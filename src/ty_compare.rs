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
use core_forms::{find_core_form, ast_to_atom};

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
pub fn resolve<'a>(t: &'a Ty, env: &'a Assoc<Name, Ty>, unif: &'a HashMap<Name, Ty>) -> &'a Ty {
    let u_f = underdetermined_form.with(|u_f| { u_f.clone() });

    match t {
        &Ty(VariableReference(vr)) => { // variable reference
            env.find(&vr).map(|new_t| resolve(new_t, env, unif)).unwrap_or(t)
        }
        &Ty(Node(ref form, ref parts)) if form == &find_core_form("type", "type_by_name") =>  {
            // TODO: remove this stanza when type_by_name is gone
            let vr = ast_to_atom(&parts.get_leaf_or_panic(&n("name")));
            env.find(&vr).map(|new_t| resolve(new_t, env, unif)).unwrap_or(t)
        }
        &Ty(Node(ref form, ref parts)) if form == &u_f => { // underdetermined
            match unif.get(&ast_to_atom(parts.get_leaf_or_panic(&n("id")))) {
                Some(ref new_t) => resolve(new_t, env, unif),
                // unfortunately, since I don't want to return a mutable reference here,
                //  the client will have to re-do the above destructuring to insert into the table
                None => t
            }
        }
        _ => t
    }
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
    // Canonicalize isn't currently used, so its name is arbitrary
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

    fn get_walk_rule(f: &Form) -> &WalkRule<Canonicalize> { &f.type_compare.pos() }
    fn automatically_extend_env() -> bool { true }
}

impl WalkMode for Subtype {
    type Elt = Ty;
    type Negated = Canonicalize;
    type Err = TyErr;
    type D = ::ast_walk::Negative<Subtype>;

    fn get_walk_rule(f: &Form) -> &WalkRule<Subtype> { &f.type_compare.neg() }
    fn automatically_extend_env() -> bool { true }
}


impl ::ast_walk::NegativeWalkMode for Subtype {
    fn qlit_mismatch_error(got: Ty, expd: Ty) -> Self::Err { TyErr::Mismatch(got, expd) }

    fn needs_pre_match() -> bool { true }

    /// Push through all variable references and underdeterminednesses on both sides,
    ///  returning types that are ready to compare, or `None` if they're definitionally equal
    fn pre_match(lhs: Ty, rhs: Ty, env: &Assoc<Name, Ty>) -> Option<(Ty, Ty)> {
        let u_f = underdetermined_form.with(|u_f| { u_f.clone() });

        unification.with(|unif| {
            let lhs = resolve(&lhs, env, &unif.borrow()).clone();
            let rhs = resolve(&rhs, env, &unif.borrow()).clone();

            let lhs_name = lhs.destructure(u_f.clone()).map(
                |p| ast_to_atom(p.get_leaf_or_panic(&n("id"))));
            let rhs_name = rhs.destructure(u_f.clone()).map(
                |p| ast_to_atom(p.get_leaf_or_panic(&n("id"))));

            match (lhs_name, rhs_name) {
                // They are the same underdetermined type; nothing to do:
                (Ok(l), Ok(r)) if l == r => { None }
                // Make a determination (possibly just merging two underdetermined types):
                (Ok(l), _) => { unif.borrow_mut().insert(l, rhs.clone()); None }
                (_, Ok(r)) => { unif.borrow_mut().insert(r, lhs.clone()); None }
                // They are (potentially) different:
                _ => { Some((lhs.clone(), rhs.clone()))}
            }
        })
    }

    // TODO: should unbound variable references ever be walked at all? Maybe it should panic?
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

    fn tbn(nm: &'static str) -> Ty {
        ty!( { "type" "type_by_name" : "name" => (, ::ast::Ast::Atom(n(nm))) } )
    }

    let mt_ty_env = Assoc::new();
    let int_ty = ty!({ "type" "int" : });
    let nat_ty = ty!({ "type" "nat" : });
    let bool_ty = ty!({ "type" "bool" : });


    assert_m!(must_subtype(&int_ty, &int_ty, mt_ty_env.clone()), Ok(_));

    assert_eq!(must_subtype(&bool_ty, &int_ty, mt_ty_env.clone()),
        Err(Mismatch(bool_ty.clone(), int_ty.clone())));

    let id_fn_ty = ty!({ "type" "forall_type" :
        "param" => ["t"],
        "body" => (import [* [forall "param"]]
            { "type" "fn" :
                "param" => [ (, tbn("t").concrete()) ],
                "ret" => (, tbn("t").concrete()) })});

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
        "some_int" => ty!( { "type" "int" : }),
        "convert_to_nat" => ty!({ "type" "forall_type" :
            "param" => ["t"],
            "body" => (import [* [forall "param"]]
                { "type" "fn" :
                    "param" => [ (, tbn("t").concrete() ) ],
                    "ret" => (, nat_ty.concrete() ) })}),
        "identity" => id_fn_ty.clone(),
        "int_to_int" => int_to_int_fn_ty.clone());


    assert_m!(must_subtype(&tbn("int_to_int"), &tbn("identity"), parametric_ty_env.clone()),
              Ok(_));

    assert_m!(must_subtype(&tbn("identity"), &tbn("int_to_int"), parametric_ty_env.clone()),
              Err(Mismatch(_,_)));

    fn incomplete_fn_ty() -> Ty { // A function, so we get a fresh underspecified type each time.
        use ast_walk::WalkElt;
        ty!({ "type" "fn" :
            "param" => [ { "type" "int" : } ],
            "ret" => (, Ty::underspecified().concrete() )})
    }


    assert_m!(must_subtype(&incomplete_fn_ty(), &int_to_int_fn_ty, mt_ty_env.clone()),
              Ok(_));

    assert_m!(must_subtype(&incomplete_fn_ty(), &id_fn_ty, mt_ty_env.clone()),
              Ok(_));
}
