use ast_walk::{walk, LazyWalkReses, WalkMode, WalkRule, NegativeWalkMode};
use ast_walk::WalkRule::*;
use form::Form;
use util::assoc::Assoc;
use ast::*;
use util::mbe::EnvMBE;
use ty::{Ty, TyErr, TypeError};
use name::*;
use std::cell::{Ref,RefCell};
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use core_forms::{find_core_form, ast_to_name};

/* Let me write down an example subtyping hierarchy, to stop myself from getting confused.
    ⊤ (any type/dynamic type/"dunno"/∀X.X)
   ╱              |                       |          ╲
 Num          ∀X Y.(X⇒Y)               Nat⇒Int     ∀X Y.(X,Y)
  |           ╱         ╲              ╱     ╲         ╲
 Int     ∀Y.(Bool⇒Y)  ∀X.(X⇒Bool)  Int⇒Int  Nat⇒Nat  ∀X.(X, Bool)
  |           ╲         ╱              ╲     ╱           |
 Nat           Bool⇒Bool               Int⇒Nat      (Nat,Bool)
   ╲               |                      |            ╱
    ⊥ (uninhabited type/panic/"can't happen"/enum{})

How do we see if S is a subtype of T?
First, we positively walk S, turning `∀X.(X⇒X)` into `(G23⇒G23)`
 (where `G23` is a generated type name),
 producing SArbitrary
Then, we negatively walk T, with SArbitrary as context, similarly eliminating `∀`.
We use side-effects to see if generated type names in T can be consistently assigned
 to make everything match.

Is (Int, Nat) <: ∀X. (X, X)?
If so, we could instantiate every type variable at ⊤, eliminating all constraints!
Eliminating ⊤ doesn't prevent (Bool⇒Bool, String⇒String) <: ∀X. (X X), via X=∀Y. Y⇒Y.
I think that this means we need to constrain ∀-originated variables to being equal,
 not subtypes.

Okay, we know that negative positions have the opposite subtyping relationship...

<digression about something not currently implemented>

...weirdly, this kinda suggests that there's an alternative formulation of `∀`
 that's more concise, and might play better with our system,
 and (for better or worse) can't express certain "exotic" types:
id: ∀X ⇒ X
map: List<[∀X]< (X ⇒ ∀Y) ⇒ List<[Y]<   (need `letrec`-style binding!)
boring_map: List<[Int]< (Int ⇒ ∀Y) ⇒ List<[Y]<    (need `∀` to distinguish binders and refs!)
boring_map2: List<[∀X]< List<[X]< (X X ⇒ ∀Y) ⇒ List<[Y]<
let_macro: "[let :::[ ;[var ⇑ v]; = ;[ expr<[∀T]< ]; ]::: in ;[expr<[∀S]< ↓ ...{v = T}...]; ]"
              -> expr<[S]<

Okay, let's walk through this. Let's suppose that we have some type variables in scope:
 is `(A ⇒ B) ⇒ ((∀A ⇒ F) ⇒ D)` a subtype of `(∀EE ⇒ BB) ⇒ (CC ⇒ EE)`?

It starts as a negative walk of the purported supertype. Destructuring succeeds.
Add ∀ed type variables to an environment. Now `∀X` might as well be `X`.
 - is [A]`((A ⇒ F) ⇒ D)` a subtype of [EE]`(CC ⇒ EE)`? Destructuring succeeds.
   - is [A]`D` a subtype of [EE]`EE`? Set EE := `D`.
   - is [EE]`CC` a subtype of [A]`(A ⇒ F)`? Depends on `CC`.
       Assuming CC is `CC_arg ⇒ CC_ret`, we set A := CC_arg.
 - is [EE]`(EE ⇒ BB)` a subtype of [A]`(A ⇒ B)`? Destructuring succeeds.
   - is [EE]`BB` a subtype of [A]`B`? Depends on the environment.
   - is [A]`A` a subtype of [EE]`EE`? Both have already been set, so:
     - does `CC_arg` equal `D`? Depends on the environment.

What if we re-order the side-effects?
    ⋮
   - is [A]`A` a subtype of [EE]`EE`? Set A := `A_and_EE` and EE := `A_and_EE`.
       (What happens when names escape the scope that defined them??)
    ⋮
   - is [A]`D` a subtype of [EE]`EE`? EE is set to `A_and_EE`, so set A_and_EE := `D`
   - is [EE]`CC` a subtype of [A]`(A ⇒ F)`? Depends on `CC`.
       Assuming CC is `CC_arg ⇒ CC_ret`, does `D` equal `CC_arg`?.

Note that, if we allowed ∀ed type variables to participate in subtyping,
 these two orders would demand opposite relationships between `D` and `CC_arg`.



So, we have this negative/positive distinction. Consider:
  Nat (Int => String) => (∀X ⇒ X)
If you count how many negations each type is under,
 you get a picture of the inputs and outputs of the type at a high level.
So, the type needs a `Nat` and a `String` and an `X`, and provides an `Int` and an `X`
 (The `Int` is doubly-negated; the function promises to provide it to the function it is passed.).

What about `Nat (∀X => Nat) => X`, assuming that we have access to `transmogrify`?
When we typecheck an invocation of it, we expect to know the exact type of its arguments,
 but that exact type might well still be `∀X ⇒ Nat`,
 meaning we have no idea what type we'll return, and no `∀`s left to explain the lack of knowledge.

</digression>

But let's not do that weird thing just yet.

*/

/// Follow variable references in `env` and underdeterminednesses in `unif`
///  until we hit something that can't move further.
pub fn resolve(t: Ty, env: &Assoc<Name, Ty>, unif: &HashMap<Name, Ty>) -> Ty {
    let u_f = underdetermined_form.with(|u_f| { u_f.clone() });

    let resolved = match t {
        Ty(VariableReference(vr)) => {
            match env.find(&vr).map(Clone::clone) {
                // HACK: leave mu-protected variables alone, instead of recurring forever
                Some(Ty(VariableReference(new_vr))) if vr == new_vr => None,
                different => different
            }
        }
        Ty(Node(ref form, ref parts, _)) if form == &find_core_form("type", "type_apply") => {
            // Expand defined type applications.
            // This is sorta similar to the type synthesis for "type_apply",
            //  but it does not recursively process the arguments (which may be underdetermined!).
            let arg_terms = parts.get_rep_leaf_or_panic(&n("arg"));

            match resolve(Ty(parts.get_leaf_or_panic(&n("type_rator")).clone()), env, unif) {
                Ty(VariableReference(rator_vr)) => {
                    // e.g. `X<[int, Y]<` underneath `mu X. ...`

                    // Rebuild a type_by_name, but evaulate its arguments
                    // This kind of thing is necessary because
                    //  we wish to avoid aliasing problems at the type level.
                    // In System F, this is avoided by performing capture-avoiding substitution.
                    let mut new__tapp_parts = ::util::mbe::EnvMBE::new_from_leaves(
                        assoc_n!("type_rator" => VariableReference(rator_vr)));

                    let mut args = vec![];
                    for individual__arg_res in arg_terms {
                        args.push(::util::mbe::EnvMBE::new_from_leaves(
                            assoc_n!("arg" => individual__arg_res.clone())));
                    }
                    new__tapp_parts.add_anon_repeat(args, None);

                    let res = Ty::new(Node(find_core_form("type", "type_apply"),
                        new__tapp_parts, ::beta::ExportBeta::Nothing));

                    if res != t { Some(res) } else { None }
                }
                defined_type => {
                    match defined_type.destructure(
                            find_core_form("type", "forall_type"), &t.0) {
                        Err(_) => None, // Broken "type_apply", but let it fail elsewhere
                        Ok(ref got_forall) => {
                            let params = got_forall.get_rep_leaf_or_panic(&n("param"));
                            if params.len() != arg_terms.len() {
                                panic!("Kind error: wrong number of arguments: {} vs {}",
                                    params.len(), arg_terms.len());
                            }
                            let mut new__ty_env = Assoc::new();
                            for (name, arg_term) in params.iter().zip(arg_terms) {
                                new__ty_env = new__ty_env.set(ast_to_name(name),
                                                              arg_term.clone());
                            }
                            Some(Ty(::alpha::substitute(
                                &::core_forms::strip_ee(
                                    &got_forall.get_leaf_or_panic(&n("body"))),
                                &new__ty_env)))
                        }
                    }
                }
            }
        }
        Ty(Node(ref form, ref parts, _)) if form == &find_core_form("type", "type_by_name") =>  {
            // TODO: remove this stanza when type_by_name is gone
            let vr = ast_to_name(&parts.get_leaf_or_panic(&n("name")));
            env.find(&vr).map(Clone::clone)
        }
        Ty(Node(ref form, ref parts, _)) if form == &u_f => { // underdetermined
            unif.get(&ast_to_name(parts.get_leaf_or_panic(&n("id")))).map(Clone::clone)
        }
        _ => None
    };

    resolved.map(|new_t| resolve(new_t, env, unif)).unwrap_or(t)
}

thread_local! {
    pub static next_id: RefCell<u32> = RefCell::new(0);

    // Invariant: `underdetermined_form`s in the HashMap must not form a cycle.
    pub static unification: RefCell<HashMap<Name, Ty>>
        = RefCell::new(HashMap::new());
    pub static underdetermined_form : ::std::rc::Rc<Form> = ::std::rc::Rc::new(Form {
        name: n("underdetermined"),
        grammar: ::std::rc::Rc::new(form_pat!((named "id", aat))),
        type_compare: ::form::Both(WalkRule::NotWalked,WalkRule::NotWalked),
        synth_type:   ::form::Both(WalkRule::NotWalked,WalkRule::NotWalked),
        eval:         ::form::Both(WalkRule::NotWalked,WalkRule::NotWalked),
        quasiquote:   ::form::Both(WalkRule::NotWalked,WalkRule::NotWalked)
    })
}


custom_derive!{
    #[derive(Copy, Clone, Debug, Reifiable)]
    // Canonicalize isn't currently used explicitly, so its name is arbitrary
    pub struct Canonicalize {}
}
custom_derive!{
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct Subtype {}
}

impl WalkMode for Canonicalize {
    type Elt = Ty;
    type Negated = Subtype;
    type Err = TyErr;
    type D = ::ast_walk::Positive<Canonicalize>;

    // Actually, always `LiteralLike`, but need to get the lifetime as long as `f`'s
    fn get_walk_rule(f: &Form) -> &WalkRule<Canonicalize> { &f.type_compare.pos() }
    fn automatically_extend_env() -> bool { true }

    fn walk_var(n: Name, cnc: &LazyWalkReses<Canonicalize>) -> Result<Ty, TyErr> {
        Ok(match cnc.env.find(&n) {
            Some(t) => t.clone(),
            None => Ty(VariableReference(n)) //TODO why can this happen?
        })
    }
}

impl WalkMode for Subtype {
    type Elt = Ty;
    type Negated = Canonicalize;
    type Err = TyErr;
    type D = ::ast_walk::Negative<Subtype>;

    fn get_walk_rule(f: &Form) -> &WalkRule<Subtype> { &f.type_compare.neg() }
    fn automatically_extend_env() -> bool { true }

    fn underspecified(name: Name) -> Ty {
        ::ty_compare::next_id.with(|id| {
            ::ty_compare::underdetermined_form.with(|u_f| {
                *id.borrow_mut() += 1;
                // TODO: we need `gensym`!
                let new_name = n(format!("{}⚁{}", name, *id.borrow()).as_str());

                ty!({ u_f.clone() ; "id" => (, ::ast::Atom(new_name))})
            })
        })
    }

    /// Look up the reference and keep going.
    fn walk_var(n: Name, cnc: &LazyWalkReses<Subtype>) -> Result<Assoc<Name, Ty>, TyErr> {
        let lhs: &Ty = cnc.env.find_or_panic(&n);
        if lhs == &Ty(VariableReference(n)) { // mu-protected!
            return match cnc.context_elt() {
                // mu-protected type variables have to exactly match by name:
                &Ty(VariableReference(other_n)) if other_n == n => Ok(Assoc::new()),
                different => Err(TyErr::Mismatch(different.clone(), lhs.clone()))
            }
        }
        walk::<Subtype>(&lhs.concrete(), cnc)
    }
}


impl ::ast_walk::NegativeWalkMode for Subtype {
    fn qlit_mismatch_error(got: Ty, expd: Ty) -> Self::Err { TyErr::Mismatch(got, expd) }

    fn needs_pre_match() -> bool { true }

    /// Push through all variable references and underdeterminednesses on both sides,
    ///  returning types that are ready to compare, or `None` if they're definitionally equal
    fn pre_match(lhs: Ty, rhs: Ty, env: &Assoc<Name, Ty>) -> Option<(Ty, Ty)> {
        let u_f = underdetermined_form.with(|u_f| { u_f.clone() });

        unification.with(|unif| {
            let lhs = resolve(lhs, env, &unif.borrow()).clone();
            let rhs = resolve(rhs, env, &unif.borrow()).clone();

            // We need to capture the environment (but only for storing unification)
            let lhs = Ty(::alpha::substitute(&lhs.concrete(), &env.map(|t| t.concrete())));
            let rhs = Ty(::alpha::substitute(&rhs.concrete(), &env.map(|t| t.concrete())));

            let lhs_name = lhs.destructure(u_f.clone(), &Trivial).map( // errors get swallowed ↓
                |p| ast_to_name(p.get_leaf_or_panic(&n("id"))));
            let rhs_name = rhs.destructure(u_f.clone(), &Trivial).map(
                |p| ast_to_name(p.get_leaf_or_panic(&n("id"))));

            // print!("%%: {}\n%%: {}\n", lhs, rhs);
            // print!("in: {:?}\n", env.map(|_| "…"));

            match (lhs_name, rhs_name) {
                // They are the same underdetermined type; nothing to do:
                (Ok(l), Ok(r)) if l == r => { None }
                // Make a determination (possibly just merging two underdetermined types):
                (Ok(l), _) => { unif.borrow_mut().insert(l, rhs.clone()); None }
                (_, Ok(r)) => { unif.borrow_mut().insert(r, lhs.clone()); None }
                // They are (potentially) different:
                _ => { Some((lhs.clone(), rhs.clone())) }
            }
        })
    }

    // TODO: should unbound variable references ever be walked at all? Maybe it should panic?
}

pub fn capture_environment(t: &Ty, env: Assoc<Name, Ty>) -> Ty {
    let walk_env = &LazyWalkReses::<Canonicalize>::new_wrapper(env);
    walk::<Canonicalize>(&t.concrete(), walk_env).expect("ICE: Ill-formed type")
}

pub fn must_subtype(sub: &Ty, sup: &Ty, env: Assoc<Name, Ty>) -> Result<Assoc<Name, Ty>, TyErr> {
    // TODO: I think we should be canonicalizing first...
    // TODO: they might need different environments?
    let lwr_env = &LazyWalkReses::<Subtype>::new_wrapper(env).with_context(sub.clone());

    walk::<Subtype>(&sup.concrete(), lwr_env)
}

// TODO: I think we need to route some other things (especially in macros.rs) through this...
pub fn must_equal(lhs: &Ty, rhs: &Ty, env: Assoc<Name, Ty>) -> Result<(), TyErr> {
    let lwr_env = &LazyWalkReses::new_wrapper(env);
    if walk::<Canonicalize>(&lhs.concrete(), &lwr_env)
       == walk::<Canonicalize>(&rhs.concrete(), &lwr_env) {
        Ok(())
    } else {
        Err(TyErr::Mismatch(lhs.clone(), rhs.clone()))
    }
}

#[test]
fn basic_subtyping() {
    use ::ty::TyErr::*;
    use ::util::assoc::Assoc;

    let mt_ty_env = Assoc::new();
    let int_ty = ty!({ "type" "Int" : });
    let nat_ty = ty!({ "type" "Nat" : });
    let float_ty = ty!({ "type" "Float" : });


    assert_m!(must_subtype(&int_ty, &int_ty, mt_ty_env.clone()), Ok(_));

    assert_eq!(must_subtype(&float_ty, &int_ty, mt_ty_env.clone()),
        Err(Mismatch(float_ty.clone(), int_ty.clone())));

    let id_fn_ty = ty!({ "type" "forall_type" :
        "param" => ["t"],
        "body" => (import [* [forall "param"]]
            { "type" "fn" : "param" => [ (vr "t") ], "ret" => (vr "t") })});

    let int_to_int_fn_ty = ty!({ "type" "fn" :
         "param" => [(, int_ty.concrete())],
         "ret" => (, int_ty.concrete())});

    assert_m!(must_subtype(&int_to_int_fn_ty, &int_to_int_fn_ty, mt_ty_env.clone()),
               Ok(_));



    assert_m!(must_subtype(&id_fn_ty, &id_fn_ty, mt_ty_env.clone()),
               Ok(_));

    // actually subtype interestingly!
    assert_m!(must_subtype(&int_to_int_fn_ty, &id_fn_ty, mt_ty_env.clone()),
               Ok(_));

    // TODO: this error spits out generated names to the user without context ) :
    assert_m!(must_subtype(&id_fn_ty, &int_to_int_fn_ty, mt_ty_env.clone()),
              Err(Mismatch(_,_)));

    let parametric_ty_env = assoc_n!(
        "some_int" => ty!( { "type" "Int" : }),
        "convert_to_nat" => ty!({ "type" "forall_type" :
            "param" => ["t"],
            "body" => (import [* [forall "param"]]
                { "type" "fn" :
                    "param" => [ (vr "t") ],
                    "ret" => (, nat_ty.concrete() ) })}),
        "identity" => id_fn_ty.clone(),
        "int_to_int" => int_to_int_fn_ty.clone());


    assert_m!(must_subtype(&ty!((vr "int_to_int")), &ty!((vr "identity")),
                  parametric_ty_env.clone()),
              Ok(_));

    assert_m!(must_subtype(&ty!((vr "identity")), &ty!((vr "int_to_int")),
                  parametric_ty_env.clone()),
              Err(Mismatch(_,_)));

    fn incomplete_fn_ty() -> Ty { // A function, so we get a fresh underspecified type each time.
        use ast_walk::WalkElt;
        ty!({ "type" "fn" :
            "param" => [ { "type" "Int" : } ],
            "ret" => (, Subtype::underspecified(n("<return_type>")).concrete() )})
    }


    assert_m!(must_subtype(&incomplete_fn_ty(), &int_to_int_fn_ty, mt_ty_env.clone()),
              Ok(_));

    assert_m!(must_subtype(&incomplete_fn_ty(), &id_fn_ty, mt_ty_env.clone()),
              Ok(_));

    assert_eq!(::ty::synth_type(&ast!({"expr" "apply" : "rator" => (vr "identity"),
                                                        "rand" => [(vr "some_int")]}),
                          parametric_ty_env.clone()),
               Ok(ty!({"type" "Int" : })));

    // TODO: write a test that relies on the capture-the-environment behavior of `pre_match`
}


#[test]
fn misc_subtyping_problems() {
    let list_ty =
        ty!( { "type" "forall_type" :
            "param" => ["Datum"],
            "body" => (import [* [forall "param"]] { "type" "mu_type" :
                "param" => ["List"],
                "body" => (import [* [prot "param"]] { "type" "enum" :
                    "name" => [@"c" "Nil", "Cons"],
                    "component" => [@"c" [],
                        [(vr "Datum"), {"type" "type_apply" :
                            "type_rator" => (vr "List"),
                            "arg" => [(vr "Datum")]} ]]})})});

    let int_list_ty =
        ty!( { "type" "mu_type" :
            "param" => ["IntList"],
            "body" => (import [* [prot "param"]] { "type" "enum" :
                "name" => [@"c" "Nil", "Cons"],
                "component" => [@"c" [], [{"type" "Int" :}, (vr "IntList") ]]})});
    let bool_list_ty =
        ty!( { "type" "mu_type" :
            "param" => ["FloatList"],
            "body" => (import [* [prot "param"]] { "type" "enum" :
                "name" => [@"c" "Nil", "Cons"],
                "component" => [@"c" [], [{"type" "Float" :}, (vr "FloatList") ]]})});

    let ty_env = assoc_n!(
        "IntList" => int_list_ty.clone(),
        "FloatList" => bool_list_ty.clone(),
        "List" => list_ty.clone()
    );

    // μ also has binding:
    assert_m!(must_subtype(&int_list_ty, &int_list_ty, ty_env.clone()), Ok(_));
    assert_m!(must_subtype(&int_list_ty, &bool_list_ty, ty_env.clone()), Err(_));

    // Don't walk `Atom`s!
    let basic_enum = ty!({"type" "enum" :
        "name" => [@"arm" "Aa", "Bb"],
        "component" => [@"arm" [{"type" "Int" :}], []]});
    assert_m!(must_subtype(&basic_enum, &basic_enum, ::util::assoc::Assoc::new()),
              Ok(_));

    let basic_mu = ty!({"type" "mu_type" :
        "param" => ["X"],
        "body" => (import [* [prot "param"]] (vr "X"))});
    let mu_env = assoc_n!("X" => basic_mu.clone());


    // Don't diverge on `μ`!
    assert_m!(must_subtype(&basic_mu, &basic_mu, mu_env),
              Ok(_));

    let id_fn_ty = ty!({ "type" "forall_type" :
        "param" => ["t"],
        "body" => (import [* [forall "param"]]
            { "type" "fn" :
                "param" => [ (vr "t") ],
                "ret" => (vr "t") })});

    let int_ty = ty!({ "type" "Int" : });
    let nat_ty = ty!({ "type" "Nat" : });


    let int_to_int_fn_ty = ty!({ "type" "fn" :
        "param" => [(, int_ty.concrete())],
        "ret" => (, int_ty.concrete())});


    let parametric_ty_env = assoc_n!(
        "some_int" => ty!( { "type" "Int" : }),
        "convert_to_nat" => ty!({ "type" "forall_type" :
            "param" => ["t"],
            "body" => (import [* [forall "param"]]
                { "type" "fn" :
                    "param" => [ (vr "t") ],
                    "ret" => (, nat_ty.concrete() ) })}),
        "identity" => id_fn_ty.clone(),
        "int_to_int" => int_to_int_fn_ty.clone());

    assert_m!(must_subtype(
        &ty!({"type" "type_apply" : "type_rator" => (vr "identity"), "arg" => [{"type" "Int" :}]}),
        &ty!({"type" "type_apply" : "type_rator" => (vr "identity"), "arg" => [{"type" "Int" :}]}),
        parametric_ty_env.clone()),
    Ok(_));


    assert_m!(must_subtype(
        &ty!({"type" "type_apply" : "type_rator" => (vr "identity"), "arg" => [{"type" "Int" :}]}),
        &ty!((vr "identity")),
        parametric_ty_env.clone()),
    Ok(_));

    // Some things that involve mu

    assert_m!(must_subtype(
        &ty!((vr "List")), &ty!((vr "List")), ty_env.clone()),
    Ok(_));


    assert_m!(must_subtype(
        &ty!({"type" "type_apply" : "type_rator" => (vr "List"), "arg" => [{"type" "Int" :}]}),
        &ty!({"type" "type_apply" : "type_rator" => (vr "List"), "arg" => [{"type" "Int" :}]}),
        ty_env.clone()),
    Ok(_));

    assert_m!(must_subtype(
        &ty!({"type" "type_apply" : "type_rator" => (, ty_env.find_or_panic(&n("List")).0.clone()),
                                    "arg" => [{"type" "Int" :}]}),
        &ty!({"type" "type_apply" : "type_rator" => (vr "List"), "arg" => [{"type" "Int" :}]}),
        ty_env.clone()),
    Ok(_));


    assert_m!(must_subtype(
        &ty!({"type" "mu_type" :
            "param" => ["List"],
            "body" =>  (import [* [prot "param"]]
                {"type" "type_apply": "type_rator" => (vr "List"), "arg" => [{"type" "Int" :}]})}),
        &ty!({"type" "mu_type" :
            "param" => ["List"],
            "body" =>  (import [* [prot "param"]]
                {"type" "type_apply": "type_rator" => (vr "List"), "arg" => [{"type" "Int" :}]})}),
        ty_env.clone()),
    Ok(_));

    assert_m!(must_subtype( // Reparameterize
        &ty!((vr "List")),
        &ty!( { "type" "forall_type" :
            "param" => ["Datum2"],
            "body" => (import [* [forall "param"]]
                {"type" "type_apply" : "type_rator" => (vr "List"), "arg" => [(vr "Datum2")]})}),
        ty_env.clone()),
    Ok(_));

}

#[test]
fn subtype_different_mus() { // testing the Amber rule:
    // These types are non-contractive, but it doesn't matter for subtyping purposes.
    let jane_author = ty!({"type" "mu_type" :
        "param" => ["CharlotteBrontë"],
        "body" => (import [* [prot "param"]]
            {"type" "fn" : "param" => [{"type" "Float" :}], "ret" => (vr "CharlotteBrontë")})});
    let jane_psuedonym = ty!({"type" "mu_type" :
        "param" => ["CurrerBell"],
        "body" => (import [* [prot "param"]]
            {"type" "fn" : "param" => [{"type" "Float" :}], "ret" => (vr "CurrerBell")})});
    let wuthering_author = ty!({"type" "mu_type" :
        "param" => ["EmilyBrontë"],
        "body" => (import [* [prot "param"]]
            {"type" "fn" : "param" => [{"type" "Int" :}], "ret" => (vr "EmilyBrontë")})});
    let mu_env = assoc_n!(
        "CharlotteBrontë" => jane_author.clone(),
        "CurrerBell" => jane_psuedonym.clone(),
        "EmilyBrontë" => wuthering_author.clone());
    assert_m!(must_subtype(&jane_author, &jane_author, mu_env.clone()),
        Ok(_));

    assert_m!(must_subtype(&jane_author, &jane_psuedonym, mu_env.clone()),
        Ok(_));

    assert_m!(must_subtype(&jane_author, &wuthering_author, mu_env.clone()),
        Err(_));
}

#[test]
fn basic_resolve() {
    let u_f = underdetermined_form.with(|u_f| { u_f.clone() });
    let ud0 = ast!({ u_f.clone() ; "id" => "a⚁99" });

    let list_ty =
        ty!( { "type" "forall_type" :
            "param" => ["Datum"],
            "body" => (import [* [forall "param"]] { "type" "mu_type" :
                "param" => ["List"],
                "body" => (import [* [prot "param"]] { "type" "enum" :
                    "name" => [@"c" "Nil", "Cons"],
                    "component" => [@"c" [],
                        [(vr "Datum"),
                         {"type" "type_apply" :
                              "type_rator" => (vr "List"), "arg" => [(,ud0.clone())]}]]})})});
    let t_env = assoc_n!("List" => list_ty.clone());


    let unif = HashMap::<Name, Ty>::new();

    assert_eq!(resolve(ty!({"type" "Int" :}), &t_env, &unif), ty!({"type" "Int" :}));

    assert_eq!(resolve(ty!({"type" "type_apply" :
        "type_rator" => (vr "List"), "arg" => [(,ud0.clone())] }), &t_env, &unif),
        ty!({ "type" "mu_type" :
            "param" => ["List"],
            "body" => (import [* [prot "param"]] { "type" "enum" :
                "name" => [@"c" "Nil", "Cons"],
                "component" => [@"c" [],
                    [(,ud0.clone()),
                     {"type" "type_apply" :
                          "type_rator" => (vr "List"), "arg" => [(,ud0.clone())]} ]]})}));
}
