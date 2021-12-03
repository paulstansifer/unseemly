use crate::{
    ast::*,
    ast_walk::{
        walk, Clo, LazyWalkReses,
        WalkRule::{self, *},
    },
    core_forms::find_core_form,
    form::{Both, Form},
    name::*,
    ty::TyErr,
    util::assoc::Assoc,
    walk_mode::WalkMode,
};
use std::{cell::RefCell, collections::HashMap, rc::Rc};

// Let me write down an example subtyping hierarchy, to stop myself from getting confused.
//          ⊤ (any type/dynamic type/"dunno"/∀X.X)
// ╱              |                       |          ╲
// Num          ∀X Y.(X⇒Y)               Nat⇒Int     ∀X Y.(X,Y)
// |           ╱         ╲              ╱     ╲         ╲
// Int     ∀Y.(Bool⇒Y)  ∀X.(X⇒Bool)  Int⇒Int  Nat⇒Nat  ∀X.(X, Bool)
// |           ╲         ╱              ╲     ╱           |
// Nat           Bool⇒Bool               Int⇒Nat      (Nat,Bool)
// ╲               |                      |            ╱
//   ⊥ (uninhabited type/panic/"can't happen"/enum{})
//
// How do we see if S is a subtype of T?
// First, we positively walk S, turning `∀X.(X⇒X)` into `(G23⇒G23)`
// (where `G23` is a generated type name),
// producing SArbitrary
// Then, we negatively walk T, with SArbitrary as context, similarly eliminating `∀`.
// We use side-effects to see if generated type names in T can be consistently assigned
// to make everything match.
//
// Is (Int, Nat) <: ∀X. (X, X)?
// If so, we could instantiate every type variable at ⊤, eliminating all constraints!
// Eliminating ⊤ doesn't prevent (Bool⇒Bool, String⇒String) <: ∀X. (X X), via X=∀Y. Y⇒Y.
// I think that this means we need to constrain ∀-originated variables to being equal,
// not subtypes.
//
// Okay, we know that negative positions have the opposite subtyping relationship...
//
// <digression about something not currently implemented>
//
// ...weirdly, this kinda suggests that there's an alternative formulation of `∀`
// that's more concise, and might play better with our system,
// and (for better or worse) can't express certain "exotic" types.
// In this forumlation, instead of writing `∀X. …`,
// we paste `∀` in front of a negative-position variable:
// id: ∀X ⇒ X
// map: List<∀X> (X ⇒ ∀Y) ⇒ List<Y>   (need `letrec`-style binding!)
// boring_map: List<Int> (Int ⇒ ∀Y) ⇒ List<Y>    (need `∀` to distinguish binders and refs!)
// boring_map2: List<∀X> List<X> (X X ⇒ ∀Y) ⇒ List<Y>
// let_macro: "[let :::[ ;[var ⇑ v]; = ;[ expr<∀T> ]; ]::: in ;[expr<∀S> ↓ ...{v = T}...]; ]"
// -> expr<S>
//
// Okay, let's walk through this. Let's suppose that we have some type variables in scope:
// is `(A ⇒ B) ⇒ ((∀A ⇒ F) ⇒ D)` a subtype of `(∀EE ⇒ BB) ⇒ (CC ⇒ EE)`?
//
// It starts as a negative walk of the purported supertype. Destructuring succeeds.
// Add ∀ed type variables to an environment. Now `∀X` might as well be `X`.
// - is [A]`((A ⇒ F) ⇒ D)` a subtype of [EE]`(CC ⇒ EE)`? Destructuring succeeds.
// - is [A]`D` a subtype of [EE]`EE`? Set EE := `D`.
// - is [EE]`CC` a subtype of [A]`(A ⇒ F)`? Depends on `CC`.
// Assuming CC is `CC_arg ⇒ CC_ret`, we set A := CC_arg.
// - is [EE]`(EE ⇒ BB)` a subtype of [A]`(A ⇒ B)`? Destructuring succeeds.
// - is [EE]`BB` a subtype of [A]`B`? Depends on the environment.
// - is [A]`A` a subtype of [EE]`EE`? Both have already been set, so:
// - does `CC_arg` equal `D`? Depends on the environment.
//
// What if we re-order the side-effects?
// ⋮
// - is [A]`A` a subtype of [EE]`EE`? Set A := `A_and_EE` and EE := `A_and_EE`.
// (What happens when names escape the scope that defined them??)
// ⋮
// - is [A]`D` a subtype of [EE]`EE`? EE is set to `A_and_EE`, so set A_and_EE := `D`
// - is [EE]`CC` a subtype of [A]`(A ⇒ F)`? Depends on `CC`.
// Assuming CC is `CC_arg ⇒ CC_ret`, does `D` equal `CC_arg`?.
//
// Note that, if we allowed ∀ed type variables to participate in subtyping,
// these two orders would demand opposite relationships between `D` and `CC_arg`.
//
//
//
// So, we have this negative/positive distinction. Consider:
// Nat (Int => String) => (∀X ⇒ X)
// If you count how many negations each type is under,
// you get a picture of the inputs and outputs of the type at a high level.
// So, the type needs a `Nat` and a `String` and an `X`, and provides an `Int` and an `X`
// (The `Int` is doubly-negated; the function promises to provide it to the function it is passed.).
//
// What about `Nat (∀X => Nat) => X`, assuming that we have access to `transmogrify`?
// When we typecheck an invocation of it, we expect to know the exact type of its arguments,
// but that exact type might well still be `∀X ⇒ Nat`,
// meaning we have no idea what type we'll return, and no `∀`s left to explain the lack of knowledge.
//
// </digression>
//
// But let's not do that weird thing just yet.
//

// The other thing that subtyping has to deal with is `...[T >> T]...`.
//

/// Follow variable references in `env` and underdeterminednesses in `unif`
///  until we hit something that can't move further.
/// TODO #28: could this be replaced by `SynthTy`?
/// TODO: This doesn't change `env`, and none of its clients care. It should just return `Ast`.
pub fn resolve(Clo { it: t, env }: Clo<Ast>, unif: &HashMap<Name, Clo<Ast>>) -> Clo<Ast> {
    let u_f = underdetermined_form.with(|u_f| u_f.clone());

    let resolved = match t.c() {
        VariableReference(vr) => {
            match env.find(vr) {
                // HACK: leave mu-protected variables alone, instead of recurring forever
                Some(vr_ast) if vr_ast.c() == &VariableReference(*vr) => None,
                Some(different) => Some(Clo { it: different.clone(), env: env.clone() }),
                None => None,
            }
        }
        Node(form, parts, _) if form == &find_core_form("Type", "type_apply") => {
            // Expand defined type applications.
            // This is sorta similar to the type synthesis for "type_apply",
            //  but it does not recursively process the arguments (which may be underdetermined!).
            let arg_terms = parts.get_rep_leaf_or_panic(n("arg"));

            let resolved = resolve(
                Clo { it: parts.get_leaf_or_panic(&n("type_rator")).clone(), env: env.clone() },
                unif,
            );

            match resolved {
                Clo { it: vr_ast, env } if matches!(vr_ast.c(), VariableReference(_)) => {
                    let rator_vr = match vr_ast.c() {
                        VariableReference(rator_vr) => *rator_vr,
                        _ => icp!(),
                    };
                    // e.g. `X<int, Y>` underneath `mu X. ...`

                    // Rebuild a type_apply, but evaulate its arguments
                    // This kind of thing is necessary because
                    //  we wish to avoid aliasing problems at the type level.
                    // In System F, this is avoided by performing capture-avoiding substitution.
                    use crate::util::mbe::EnvMBE;

                    let mut new__tapp_parts =
                        EnvMBE::new_from_leaves(assoc_n!("type_rator" => ast!((vr rator_vr))));

                    let mut args = vec![];
                    for individual__arg_res in arg_terms {
                        args.push(EnvMBE::new_from_leaves(
                            assoc_n!("arg" => individual__arg_res.clone()),
                        ));
                    }
                    new__tapp_parts.add_anon_repeat(args);

                    let res = raw_ast!(Node(
                        find_core_form("Type", "type_apply"),
                        new__tapp_parts,
                        crate::beta::ExportBeta::Nothing
                    ));

                    if res != t {
                        Some(Clo { it: res, env: env })
                    } else {
                        None
                    }
                }
                Clo { it: defined_type, env } => {
                    match defined_type.ty_destructure(find_core_form("Type", "forall_type"), &t) {
                        Err(_) => None, // Broken "type_apply", but let it fail elsewhere
                        Ok(ref got_forall) => {
                            let params = got_forall.get_rep_leaf_or_panic(n("param"));
                            if params.len() != arg_terms.len() {
                                panic!(
                                    "Kind error: wrong number of arguments: {} vs {}",
                                    params.len(),
                                    arg_terms.len()
                                );
                            }
                            let mut actual_params = Assoc::new();
                            for (name, arg_term) in params.iter().zip(arg_terms) {
                                actual_params = actual_params.set(name.to_name(), arg_term.clone());
                            }

                            Some(Clo {
                                it: crate::alpha::substitute(
                                    crate::core_forms::strip_ee(
                                        got_forall.get_leaf_or_panic(&n("body")),
                                    ),
                                    &actual_params,
                                ),
                                env: env,
                            })
                        }
                    }
                }
            }
        }
        // TODO: This needs to be implemented (unless issue #28 obviates it)
        // Ast(Node(ref form, ref parts, _)) if form == &find_core_form("Type", "dotdotdot") => {
        // }
        Node(ref form, ref parts, _) if form == &u_f => {
            // underdetermined
            unif.get(&parts.get_leaf_or_panic(&n("id")).to_name()).cloned()
        }
        _ => None,
    };

    resolved.map(|clo: Clo<Ast>| resolve(clo, unif)).unwrap_or(Clo { it: t, env: env })
}

thread_local! {
    // Invariant: `underdetermined_form`s in the HashMap must not form a cycle.
    pub static unification: RefCell<HashMap<Name, Clo<Ast>>>
        = RefCell::new(HashMap::<Name, Clo<Ast>>::new());
    pub static underdetermined_form : Rc<Form> = Rc::new(Form {
        name: n("<underdetermined>"),
        grammar: Rc::new(form_pat!((named "id", atom))),
        type_compare: Both(
            // pre-match handle s the negative case; we need to do the positive case manually:
            cust_rc_box!(|udet_parts| {
                let id = udet_parts.get_term(n("id")).to_name();
                unification.with(|unif| {
                    let unif = unif.borrow();
                    // TODO: don't use the id in an error message; it's user-hostile:
                    let clo = unif.get(&id).ok_or(TyErr::UnboundName(id))?;
                    canonicalize(&clo.it, clo.env.clone())
                })
            }),
            NotWalked),
        synth_type:   Both(NotWalked, NotWalked),
        eval:         Both(NotWalked, NotWalked),
        quasiquote:   Both(NotWalked, NotWalked)
    })
}

custom_derive! {
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct Canonicalize {}
}
custom_derive! {
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct Subtype {}
}

// TODO #28: Canonicalization is almost the same thing as `SynthTy`.
// Try to replace it with `SynthTy` and see what happens.
impl WalkMode for Canonicalize {
    fn name() -> &'static str { "Canon" }

    type Elt = Ast;
    type Negated = Subtype;
    type AsPositive = Canonicalize;
    type AsNegative = Subtype;
    type Err = TyErr;
    type D = crate::walk_mode::Positive<Canonicalize>;
    type ExtraInfo = ();

    // Actually, always `LiteralLike`, but need to get the lifetime as long as `f`'s
    fn get_walk_rule(f: &Form) -> WalkRule<Canonicalize> { f.type_compare.pos().clone() }
    fn automatically_extend_env() -> bool { true }

    fn walk_var(n: Name, cnc: &LazyWalkReses<Canonicalize>) -> Result<Ast, TyErr> {
        match cnc.env.find(&n) {
            // If it's protected, stop:
            Some(t) if &VariableReference(n) == t.c() => Ok(t.clone()),
            Some(t) => canonicalize(t, cnc.env.clone()),
            None => Ok(ast!((vr n))), // TODO why can this happen?
        }
    }

    // Simply protect the name; don't try to unify it.
    fn underspecified(nm: Name) -> Ast { ast!((vr nm)) }
}

fn splice_ddd(
    ddd_parts: &LazyWalkReses<Subtype>,
    context_elts: Vec<Ast>,
) -> Result<Option<(Vec<Assoc<Name, Ast>>, Ast)>, <Subtype as WalkMode>::Err> {
    let ddd_form = crate::core_forms::find("Type", "dotdotdot_type");
    let tuple_form = crate::core_forms::find("Type", "tuple");
    let undet_form = underdetermined_form.with(|u_f| u_f.clone());

    if context_elts.len() == 1 {
        match context_elts[0].destructure(ddd_form.clone()) {
            None => {} // False alarm; just a normal single repetition
            Some(sub_parts) => {
                match sub_parts.get_leaf_or_panic(&n("body")).destructure(ddd_form) {
                    Some(_) => icp!("TODO: count up nestings of :::[]:::"),
                    None => return Ok(None), // :::[]::: is a subtype of :::[]:::
                }
            }
        }
    }

    let drivers: Vec<(Name, Ast)> = unification.with(|unif| {
        ddd_parts
            .get_rep_term(n("driver"))
            .iter()
            .map(|a: &Ast| {
                (
                    a.vr_to_name(),
                    resolve(Clo { it: a.clone(), env: ddd_parts.env.clone() }, &unif.borrow()).it,
                )
            })
            .collect()
    });
    let expected_len = context_elts.len();
    let mut envs_with_walked_drivers = vec![];
    envs_with_walked_drivers.resize_with(expected_len, Assoc::new);

    // Make sure tuples are the right length,
    // and force underdetermined types to *be* tuples of the right length.
    for (name, driver) in drivers {
        // TODO: Why not use `ty_destructure` here?
        if let Some(tuple_parts) = driver.destructure(tuple_form.clone()) {
            let components = tuple_parts.get_rep_leaf_or_panic(n("component"));
            if components.len() != expected_len {
                return Err(TyErr::LengthMismatch(
                    components.into_iter().map(|a| a.clone()).collect(),
                    expected_len,
                ));
            }

            for i in 0..expected_len {
                envs_with_walked_drivers[i] =
                    envs_with_walked_drivers[i].set(name, components[i].clone());
            }
        } else if let Some(undet_parts) = driver.destructure(undet_form.clone()) {
            unification.with(|unif| {
                let mut undet_components = vec![];
                undet_components
                    .resize_with(expected_len, || Subtype::underspecified(n("ddd_bit")));
                unif.borrow_mut().insert(undet_parts.get_leaf_or_panic(&n("id")).to_name(), Clo {
                    it: ast!({"Type" "tuple" :
                            "component" => (,seq undet_components.clone()) }),
                    env: ddd_parts.env.clone(),
                });
                for i in 0..expected_len {
                    envs_with_walked_drivers[i] =
                        envs_with_walked_drivers[i].set(name, undet_components[i].clone());
                }
            })
        } else {
            return Err(TyErr::UnableToDestructure(driver, n("tuple")));
        }
    }

    Ok(Some((envs_with_walked_drivers, ddd_parts.get_term(n("body")))))
}

impl WalkMode for Subtype {
    fn name() -> &'static str { "SubTy" }

    type Elt = Ast;
    type Negated = Canonicalize;
    type AsPositive = Canonicalize;
    type AsNegative = Subtype;
    type Err = TyErr;
    type D = crate::walk_mode::Negative<Subtype>;
    type ExtraInfo = ();

    fn get_walk_rule(f: &Form) -> WalkRule<Subtype> { f.type_compare.neg().clone() }
    fn automatically_extend_env() -> bool { true }

    fn underspecified(name: Name) -> Ast {
        underdetermined_form.with(|u_f| {
            let new_name = Name::gensym(&format!("{}⚁", name));

            ast!({ u_f.clone() ; "id" => (at new_name)})
        })
    }

    /// Look up the reference and keep going.
    fn walk_var(n: Name, cnc: &LazyWalkReses<Subtype>) -> Result<Assoc<Name, Ast>, TyErr> {
        let lhs: &Ast = cnc.env.find_or_panic(&n);
        if lhs.c() == &VariableReference(n) {
            // mu-protected!
            return if cnc.context_elt().c() == &VariableReference(n) {
                // mu-protected type variables have to exactly match by name:
                Ok(Assoc::new())
            } else {
                Err(TyErr::Mismatch(cnc.context_elt().clone(), lhs.clone()))
            };
        }
        walk::<Subtype>(lhs, cnc)
    }

    fn needs__splice_healing() -> bool { true }
    fn perform_splice_positive(
        _: &Form,
        _: &LazyWalkReses<Self>,
    ) -> Result<Option<(Vec<Assoc<Name, Ast>>, Ast)>, Self::Err> {
        // If this ever is non-trivial,
        //  we need to respect `extra_env` in `Positive::walk_quasi_literally` in walk_mode.rs
        Ok(None)
    }
    fn perform_splice_negative(
        f: &Form,
        parts: &LazyWalkReses<Self>,
        context_elts: &dyn Fn() -> Vec<Ast>,
    ) -> Result<Option<(Vec<Assoc<Name, Ast>>, Ast)>, Self::Err> {
        if f.name != n("dotdotdot_type") {
            return Ok(None);
        }

        splice_ddd(parts, context_elts())
    }
}

impl crate::walk_mode::NegativeWalkMode for Subtype {
    fn qlit_mismatch_error(got: Ast, expd: Ast) -> Self::Err { TyErr::Mismatch(got, expd) }

    fn needs_pre_match() -> bool { true }

    /// Push through all variable references and underdeterminednesses on both sides,
    ///  returning types that are ready to compare, or `None` if they're definitionally equal
    fn pre_match(lhs_ty: Ast, rhs_ty: Ast, env: &Assoc<Name, Ast>) -> Option<(Clo<Ast>, Clo<Ast>)> {
        let u_f = underdetermined_form.with(|u_f| u_f.clone());

        let (res_lhs, res_rhs) = unification.with(|unif| {
            // Capture the environment and resolve:
            let lhs: Clo<Ast> = resolve(Clo { it: lhs_ty, env: env.clone() }, &unif.borrow());
            let rhs: Clo<Ast> = resolve(Clo { it: rhs_ty, env: env.clone() }, &unif.borrow());

            let lhs_name = lhs.it.ty_destructure(u_f.clone(), &ast!((trivial))).map(
                // errors get swallowed ↓
                |p| p.get_leaf_or_panic(&n("id")).to_name(),
            );
            let rhs_name = rhs
                .it
                .ty_destructure(u_f.clone(), &ast!((trivial)))
                .map(|p| p.get_leaf_or_panic(&n("id")).to_name());

            match (lhs_name, rhs_name) {
                // They are the same underdetermined type; nothing to do:
                (Ok(l), Ok(r)) if l == r => None,
                // Make a determination (possibly just merging two underdetermined types):
                (Ok(l), _) => {
                    unif.borrow_mut().insert(l, rhs);
                    None
                }
                (_, Ok(r)) => {
                    unif.borrow_mut().insert(r, lhs);
                    None
                }
                // They are (potentially) different.
                _ => Some((lhs, rhs)),
            }
        })?;

        Some((res_lhs, res_rhs))
    }

    // TODO: should unbound variable references ever be walked at all? Maybe it should panic?
}

pub fn canonicalize(t: &Ast, env: Assoc<Name, Ast>) -> Result<Ast, TyErr> {
    walk::<Canonicalize>(t, &LazyWalkReses::<Canonicalize>::new_wrapper(env))
}

// `sub` must be a subtype of `sup`. (Note that `sub` becomes the context element!)
pub fn is_subtype(
    sub: &Ast,
    sup: &Ast,
    parts: &LazyWalkReses<crate::ty::SynthTy>,
) -> Result<Assoc<Name, Ast>, TyErr> {
    walk::<Subtype>(sup, &parts.switch_mode::<Subtype>().with_context(sub.clone()))
}

// `sub` must be a subtype of `sup`. (Note that `sub` becomes the context element!)
// Only use this in tests or at the top level; this discards any non-phase-0-environments!
pub fn must_subtype(
    sub: &Ast,
    sup: &Ast,
    env: Assoc<Name, Ast>,
) -> Result<Assoc<Name, Ast>, TyErr> {
    // TODO: I think we should be canonicalizing first...
    // TODO: they might need different environments?
    let lwr_env = &LazyWalkReses::<Subtype>::new_wrapper(env).with_context(sub.clone());

    walk::<Subtype>(sup, lwr_env)
}

// TODO: I think we need to route some other things (especially in macros.rs) through this...
pub fn must_equal(
    lhs: &Ast,
    rhs: &Ast,
    parts: &LazyWalkReses<crate::ty::SynthTy>,
) -> Result<(), TyErr> {
    let canon_parts = parts.switch_mode::<Canonicalize>();
    if walk::<Canonicalize>(lhs, &canon_parts) == walk::<Canonicalize>(rhs, &canon_parts) {
        Ok(())
    } else {
        Err(TyErr::Mismatch(lhs.clone(), rhs.clone()))
    }
}

#[test]
fn basic_subtyping() {
    use crate::{ty::TyErr::*, util::assoc::Assoc};

    let mt_ty_env = Assoc::new();
    let int_ty = ast!({ "Type" "Int" : });
    let nat_ty = ast!({ "Type" "Nat" : });
    let float_ty = ast!({ "Type" "Float" : });

    assert_m!(must_subtype(&int_ty, &int_ty, mt_ty_env.clone()), Ok(_));

    assert_eq!(
        must_subtype(&float_ty, &int_ty, mt_ty_env.clone()),
        Err(Mismatch(float_ty.clone(), int_ty.clone()))
    );

    let id_fn_ty = ast!({ "Type" "forall_type" :
        "param" => ["t"],
        "body" => (import [* [forall "param"]]
            { "Type" "fn" : "param" => [ (vr "t") ], "ret" => (vr "t") })});

    let int_to_int_fn_ty = ast!({ "Type" "fn" :
         "param" => [(, int_ty.clone())],
         "ret" => (, int_ty.clone())});

    assert_m!(must_subtype(&int_to_int_fn_ty, &int_to_int_fn_ty, mt_ty_env.clone()), Ok(_));

    assert_m!(must_subtype(&id_fn_ty, &id_fn_ty, mt_ty_env.clone()), Ok(_));

    // actually subtype interestingly!
    assert_m!(must_subtype(&int_to_int_fn_ty, &id_fn_ty, mt_ty_env.clone()), Ok(_));

    // TODO: this error spits out generated names to the user without context ) :
    assert_m!(must_subtype(&id_fn_ty, &int_to_int_fn_ty, mt_ty_env.clone()), Err(Mismatch(_, _)));

    let parametric_ty_env = assoc_n!(
        "some_int" => ast!( { "Type" "Int" : }),
        "convert_to_nat" => ast!({ "Type" "forall_type" :
            "param" => ["t"],
            "body" => (import [* [forall "param"]]
                { "Type" "fn" :
                    "param" => [ (vr "t") ],
                    "ret" => (, nat_ty.clone() ) })}),
        "identity" => id_fn_ty.clone(),
        "int_to_int" => int_to_int_fn_ty.clone());

    assert_m!(
        must_subtype(&ast!((vr "int_to_int")), &ast!((vr "identity")), parametric_ty_env.clone()),
        Ok(_)
    );

    assert_m!(
        must_subtype(&ast!((vr "identity")), &ast!((vr "int_to_int")), parametric_ty_env.clone()),
        Err(Mismatch(_, _))
    );

    fn incomplete_fn_ty() -> Ast {
        // A function, so we get a fresh underspecified type each time.
        ast!({ "Type" "fn" :
            "param" => [ { "Type" "Int" : } ],
            "ret" => (, Subtype::underspecified(n("<return_type>")) )})
    }

    assert_m!(must_subtype(&incomplete_fn_ty(), &int_to_int_fn_ty, mt_ty_env.clone()), Ok(_));

    assert_m!(must_subtype(&incomplete_fn_ty(), &id_fn_ty, mt_ty_env.clone()), Ok(_));

    assert_eq!(
        crate::ty::synth_type(
            &ast!({"Expr" "apply" : "rator" => (vr "identity"),
                                                        "rand" => [(vr "some_int")]}),
            parametric_ty_env.clone()
        ),
        Ok(ast!({"Type" "Int" : }))
    );

    // TODO: write a test that relies on the capture-the-environment behavior of `pre_match`
}

#[test]
fn misc_subtyping_problems() {
    let list_ty = ast!( { "Type" "forall_type" :
            "param" => ["Datum"],
            "body" => (import [* [forall "param"]] { "Type" "mu_type" :
                "param" => [(import [prot "param"] (vr "List"))],
                "body" => (import [* [prot "param"]] { "Type" "enum" :
                    "name" => [@"c" "Nil", "Cons"],
                    "component" => [@"c" [],
                        [(vr "Datum"), {"Type" "type_apply" :
                            "type_rator" => (vr "List"),
                            "arg" => [(vr "Datum")]} ]]})})});

    let int_list_ty = ast!( { "Type" "mu_type" :
            "param" => [(import [prot "param"] (vr "IntList"))],
            "body" => (import [* [prot "param"]] { "Type" "enum" :
                "name" => [@"c" "Nil", "Cons"],
                "component" => [@"c" [], [{"Type" "Int" :}, (vr "IntList") ]]})});
    let bool_list_ty = ast!( { "Type" "mu_type" :
            "param" => [(import [prot "param"] (vr "FloatList"))],
            "body" => (import [* [prot "param"]] { "Type" "enum" :
                "name" => [@"c" "Nil", "Cons"],
                "component" => [@"c" [], [{"Type" "Float" :}, (vr "FloatList") ]]})});

    let ty_env = assoc_n!(
        "IntList" => int_list_ty.clone(),
        "FloatList" => bool_list_ty.clone(),
        "List" => list_ty.clone()
    );

    // Test that canonicalization accepts `underspecified`:
    assert_m!(canonicalize(&list_ty, ty_env.clone()), Ok(_));

    // μ also has binding:
    assert_m!(must_subtype(&int_list_ty, &int_list_ty, ty_env.clone()), Ok(_));
    assert_m!(must_subtype(&int_list_ty, &bool_list_ty, ty_env.clone()), Err(_));

    // Don't walk `Atom`s!
    let basic_enum = ast!({"Type" "enum" :
        "name" => [@"arm" "Aa", "Bb"],
        "component" => [@"arm" [{"Type" "Int" :}], []]});
    assert_m!(must_subtype(&basic_enum, &basic_enum, crate::util::assoc::Assoc::new()), Ok(_));

    let basic_mu = ast!({"Type" "mu_type" :
        "param" => [(import [prot "param"] (vr "X"))],
        "body" => (import [* [prot "param"]] (vr "X"))});
    let mu_env = assoc_n!("X" => basic_mu.clone());

    // Don't diverge on `μ`!
    assert_m!(must_subtype(&basic_mu, &basic_mu, mu_env), Ok(_));

    let id_fn_ty = ast!({ "Type" "forall_type" :
        "param" => ["t"],
        "body" => (import [* [forall "param"]]
            { "Type" "fn" :
                "param" => [ (vr "t") ],
                "ret" => (vr "t") })});

    let int_ty = ast!({ "Type" "Int" : });
    let nat_ty = ast!({ "Type" "Nat" : });

    let int_to_int_fn_ty = ast!({ "Type" "fn" :
        "param" => [(, int_ty.clone())],
        "ret" => (, int_ty.clone())});

    let parametric_ty_env = assoc_n!(
        "some_int" => ast!( { "Type" "Int" : }),
        "convert_to_nat" => ast!({ "Type" "forall_type" :
            "param" => ["t"],
            "body" => (import [* [forall "param"]]
                { "Type" "fn" :
                    "param" => [ (vr "t") ],
                    "ret" => (, nat_ty.clone() ) })}),
        "identity" => id_fn_ty.clone(),
        "int_to_int" => int_to_int_fn_ty.clone());

    assert_m!(
        must_subtype(
            &ast!({"Type" "type_apply" : "type_rator" => (vr "identity"), "arg" => [{"Type" "Int" :}]}),
            &ast!({"Type" "type_apply" : "type_rator" => (vr "identity"), "arg" => [{"Type" "Int" :}]}),
            parametric_ty_env.clone()
        ),
        Ok(_)
    );

    assert_m!(
        must_subtype(
            &ast!({"Type" "type_apply" : "type_rator" => (vr "identity"), "arg" => [{"Type" "Int" :}]}),
            &ast!((vr "identity")),
            parametric_ty_env.clone()
        ),
        Ok(_)
    );

    // Some things that involve mu

    assert_m!(must_subtype(&ast!((vr "List")), &ast!((vr "List")), ty_env.clone()), Ok(_));

    assert_m!(
        must_subtype(
            &ast!({"Type" "type_apply" : "type_rator" => (vr "List"), "arg" => [{"Type" "Int" :}]}),
            &ast!({"Type" "type_apply" : "type_rator" => (vr "List"), "arg" => [{"Type" "Int" :}]}),
            ty_env.clone()
        ),
        Ok(_)
    );

    assert_m!(
        must_subtype(
            &ast!({"Type" "type_apply" :
               "type_rator" => (, ty_env.find_or_panic(&n("List")).clone()),
                "arg" => [{"Type" "Int" :}]}),
            &ast!({"Type" "type_apply" : "type_rator" => (vr "List"), "arg" => [{"Type" "Int" :}]}),
            ty_env.clone()
        ),
        Ok(_)
    );

    assert_m!(
        must_subtype(
            &ast!({"Type" "mu_type" :
            "param" => [(import [prot "param"] (vr "List"))],
            "body" =>  (import [* [prot "param"]]
                {"Type" "type_apply": "type_rator" => (vr "List"), "arg" => [{"Type" "Int" :}]})}),
            &ast!({"Type" "mu_type" :
            "param" => [(import [prot "param"] (vr "List"))],
            "body" =>  (import [* [prot "param"]]
                {"Type" "type_apply": "type_rator" => (vr "List"), "arg" => [{"Type" "Int" :}]})}),
            ty_env.clone()
        ),
        Ok(_)
    );

    assert_m!(
        must_subtype(
            // Reparameterize
            &ast!((vr "List")),
            &ast!( { "Type" "forall_type" :
            "param" => ["Datum2"],
            "body" => (import [* [forall "param"]]
                {"Type" "type_apply" : "type_rator" => (vr "List"), "arg" => [(vr "Datum2")]})}),
            ty_env.clone()
        ),
        Ok(_)
    );
}

#[test]
fn struct_subtyping() {
    // Trivial struct subtying:
    assert_m!(
        must_subtype(
            &ast!( { "Type" "struct" :
            "component_name" => [@"c" "a", "b"],
            "component" => [@"c" {"Type" "Int" :}, {"Type" "Nat" :}]}),
            &ast!( { "Type" "struct" :
            "component_name" => [@"c" "a", "b"],
            "component" => [@"c" {"Type" "Int" :}, {"Type" "Nat" :}]}),
            Assoc::new()
        ),
        Ok(_)
    );

    // Add a component:
    assert_m!(
        must_subtype(
            &ast!( { "Type" "struct" :
            "component_name" => [@"c" "a", "b"],
            "component" => [@"c" {"Type" "Int" :}, {"Type" "Nat" :}]}),
            &ast!( { "Type" "struct" :
            "component_name" => [@"c" "a", "b", "c"],
            "component" => [@"c" {"Type" "Int" :}, {"Type" "Nat" :}, {"Type" "Float" :}]}),
            Assoc::new()
        ),
        Ok(_)
    );

    // Reorder components:
    assert_m!(
        must_subtype(
            &ast!( { "Type" "struct" :
            "component_name" => [@"c" "a", "b"],
            "component" => [@"c" {"Type" "Int" :}, {"Type" "Nat" :}]}),
            &ast!( { "Type" "struct" :
            "component_name" => [@"c" "b", "a"],
            "component" => [@"c" {"Type" "Nat" :}, {"Type" "Int" :}]}),
            Assoc::new()
        ),
        Ok(_)
    );

    // Scramble:
    assert_m!(
        must_subtype(
            &ast!( { "Type" "struct" :
            "component_name" => [@"c" "a", "b"],
            "component" => [@"c" {"Type" "Int" :}, {"Type" "Nat" :}]}),
            &ast!( { "Type" "struct" :
            "component_name" => [@"c" "b", "a"],
            "component" => [@"c" {"Type" "Int" :}, {"Type" "Nat" :}]}),
            Assoc::new()
        ),
        Err(_)
    );
}

#[test]
fn subtype_different_mus() {
    // testing the Amber rule:
    // These types are non-contractive, but it doesn't matter for subtyping purposes.
    let jane_author = ast!({"Type" "mu_type" :
        "param" => [(import [prot "param"] (vr "CharlotteBrontë"))],
        "body" => (import [* [prot "param"]]
            {"Type" "fn" : "param" => [{"Type" "Float" :}], "ret" => (vr "CharlotteBrontë")})});
    let jane_psuedonym = ast!({"Type" "mu_type" :
        "param" => [(import [prot "param"] (vr "CurrerBell"))],
        "body" => (import [* [prot "param"]]
            {"Type" "fn" : "param" => [{"Type" "Float" :}], "ret" => (vr "CurrerBell")})});
    let wuthering_author = ast!({"Type" "mu_type" :
        "param" => [(import [prot "param"] (vr "EmilyBrontë"))],
        "body" => (import [* [prot "param"]]
            {"Type" "fn" : "param" => [{"Type" "Int" :}], "ret" => (vr "EmilyBrontë")})});
    let mu_env = assoc_n!(
        "CharlotteBrontë" => jane_author.clone(),
        "CurrerBell" => jane_psuedonym.clone(),
        "EmilyBrontë" => wuthering_author.clone());
    assert_m!(must_subtype(&jane_author, &jane_author, mu_env.clone()), Ok(_));

    assert_m!(must_subtype(&jane_author, &jane_psuedonym, mu_env.clone()), Ok(_));

    assert_m!(must_subtype(&jane_author, &wuthering_author, mu_env.clone()), Err(_));
}

#[test]
fn subtype_dotdotdot_type() {
    let threeple = uty!({tuple : [{Int :}; {Float :}; {Nat :}]});
    let dddple = uty!({forall_type : [T] {tuple : [{dotdotdot_type : [T] T}]}});

    assert_m!(must_subtype(&threeple, &dddple, Assoc::new()), Ok(_));

    // TODO #15: this panics in mbe.rs; it ought to error instead (might not still be true)
    // assert_m!(must_subtype(&dddple, &threeple, assoc_n!("T" => Subtype::underspecified(n("-")))),
    //     Err(_));

    assert_m!(must_subtype(&dddple, &dddple, Assoc::new()), Ok(_));

    let expr_threeple = uty!({tuple : [{type_apply : (prim Expr) [{Int :}]};
                                       {type_apply : (prim Expr) [{Float :}]};
                                       {type_apply : (prim Expr) [{Nat :}]}]});
    let expr_dddple = uty!(
        {forall_type : [T] {tuple : [{dotdotdot_type : [T] {type_apply : (prim Expr) [T]}}]}});

    assert_m!(must_subtype(&expr_threeple, &dddple, Assoc::new()), Ok(_));

    assert_m!(must_subtype(&expr_threeple, &expr_dddple, Assoc::new()), Ok(_));
}

#[test]
fn basic_resolve() {
    let u_f = underdetermined_form.with(|u_f| u_f.clone());
    let ud0 = ast!({ u_f.clone() ; "id" => "a⚁99" });

    let list_ty = ast!( { "Type" "forall_type" :
            "param" => ["Datum"],
            "body" => (import [* [forall "param"]] { "Type" "mu_type" :
                "param" => [(import [prot "param"] (vr "List"))],
                "body" => (import [* [prot "param"]] { "Type" "enum" :
                    "name" => [@"c" "Nil", "Cons"],
                    "component" => [@"c" [],
                        [(vr "Datum"),
                         {"Type" "type_apply" :
                              "type_rator" => (vr "List"), "arg" => [(,ud0.clone())]}]]})})});
    let t_env = assoc_n!("List" => list_ty.clone());

    let unif = HashMap::<Name, Clo<Ast>>::new();

    assert_eq!(
        resolve(Clo { it: ast!({"Type" "Int" :}), env: t_env.clone() }, &unif).it,
        ast!({"Type" "Int" :})
    );

    assert_eq!(
        resolve(
            Clo {
                it: ast!({"Type" "type_apply" :
        "type_rator" => (vr "List"), "arg" => [(,ud0.clone())] }),
                env: t_env.clone()
            },
            &unif
        )
        .it,
        ast!({ "Type" "mu_type" :
            "param" => [(import [prot "param"] (vr "List"))],
            "body" => (import [* [prot "param"]] { "Type" "enum" :
                "name" => [@"c" "Nil", "Cons"],
                "component" => [@"c" [],
                    [(,ud0.clone()),
                     {"Type" "type_apply" :
                          "type_rator" => (vr "List"), "arg" => [(,ud0.clone())]} ]]})})
    );
}

#[test]
fn forall_on_both_sides() {
    let list_ty = uty!({forall_type : [Datum]
        {mu_type : [List] {enum : [Nil [] ; Cons [Datum ; {type_apply : List [Datum]}] ]}}});

    let t_env = assoc_n!("List" => list_ty.clone());

    assert_m!(
        must_subtype(
            &uty!({forall_type : [T] {type_apply : List [T]}}),
            &uty!({forall_type : [S] {type_apply : List [S]}}),
            t_env.clone()
        ),
        Ok(_)
    );

    // TODO: This ... has a stack overflow?
    // assert_m!(
    // must_subtype(
    // &uty!({forall_type : [T] {type_apply : List [{type_apply : List [T]}]}}),
    // &uty!({forall_type : [S] {type_apply : List [S]}}),
    // t_env.clone()
    // ),
    // Ok(_)
    // );
}
