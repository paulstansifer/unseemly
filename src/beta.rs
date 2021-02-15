#![macro_use]

use crate::{
    alpha::Ren,
    ast::{Ast, Atom, ExtendEnv, VariableReference},
    ast_walk::{LazilyWalkedTerm, LazyWalkReses},
    name::*,
    util::{assoc::Assoc, mbe::EnvMBE},
    walk_mode::{Dir, WalkElt},
};
use std::fmt;

custom_derive! {
    /**
     `Beta`s are always tied to a particular `Form`,
    and they have names that refer to the parts of that `Form`.
    They are generally used to talk about environmental operations,
    and they are most useful for typechecking
    (the evaluation process ignores them,
        because it needs to do more complex operations
        to calculate extended environments).

    `Beta`s are trees that determine how variables shadow each other,
    if multiple variables are being handled at once.
    The leaf nodes, `Basic` and `SameAs`, indicate
    (a) where the name comes from
    (b) where to get the type annotation (`Basic`)
        or an expression producing the type (`SameAs`)
        for that name.
    The more exotic leaf nodes, `Underspecified`, `Protected`, and `BoundButNotUsable`
     do various weird things.

    I have no idea where the name "β" came from, and whether it has any connection to α-equivalence.

    There's probably a very elegant way to make `Beta` just another kind of `Ast`.
    Finding it might require some time in the math mines, though.
    */
    #[derive(PartialEq, Clone, Reifiable)]
    pub enum Beta {
        /// Both of these `Name`s refer to named terms in the current `Scope`
        ///  (or `ResEnv`, for `Ast`s).
        /// The first is the identifier to import, and the second the syntax for its type.
        Basic(Name, Name),
        /// Like `Basic`, but here the second part is another expression
        /// which should be typechecked, and whose type the new name gets.
        /// (This can be used write to `let` without requiring a type annotation.)
        SameAs(Name, Box<Ast>),
        /// Names are introduced here, but bound to `Trivial`.
        /// Needed to avoid an infinite regress where the syntax for `Scope` does a self-import
        ///  to expose the names it introduces to the (syntax for) betas that need them.
        BoundButNotUsable(Name),
        /// Name is introduced here (must be a single `Atom`),
        ///  and its meaning is figured out from usage.
        Underspecified(Name),
        /// Name is left alone (must be a single `VarRef`, and already bound)
        Protected(Name),
        /// Shadow the names from two `Beta`s.
        Shadow(Box<Beta>, Box<Beta>),
        /// Shadow the names from a `Beta`, repeated.
        /// The `Vec` should always be equal to `names_mentioned(...)` of the `Beta`.
        ShadowAll(Box<Beta>, Vec<Name>),
        /// No names
        Nothing
    }
}

pub use self::Beta::*;

impl fmt::Debug for Beta {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Nothing => write!(f, "∅"),
            Shadow(ref lhs, ref rhs) => write!(f, "({:#?} ▷ {:#?})", lhs, rhs),
            ShadowAll(ref sub_beta, ref drivers) => {
                write!(f, "( {:#?} ▷ ... by {:#?})", sub_beta, drivers)
            }
            Basic(ref name, ref ty) => write!(f, "{:#?}:{:#?}", name, ty),
            SameAs(ref name, ref ty_source) => write!(f, "{:#?}={:#?}", name, ty_source),
            BoundButNotUsable(ref name) => write!(f, "!{:#}", name),
            Underspecified(ref name) => write!(f, "∀{:#?}", name),
            Protected(ref name) => write!(f, "↫{:#?}", name),
        }
    }
}

impl Beta {
    // TODO: alpha.rs needs a version of this that o,ots the RHS of `Basic` and `SameAs`.
    //  but macro.rs needs this version.
    // (maybe it just needs `names_mentioned_and_bound`)
    pub fn names_mentioned(&self) -> Vec<Name> {
        match *self {
            Nothing => vec![],
            Shadow(ref lhs, ref rhs) => {
                lhs.names_mentioned().into_iter().chain(rhs.names_mentioned().into_iter()).collect()
            }
            ShadowAll(_, ref drivers) => drivers.clone(),
            Basic(n, v) => vec![n, v],
            SameAs(n, ref v_source) => {
                vec![n].into_iter().chain(v_source.free_vrs().into_iter()).collect()
            }
            BoundButNotUsable(n) => vec![n],
            Underspecified(n) => vec![n],
            Protected(n) => vec![n],
        }
    }

    // `Protected` doens't actually bind, so we shouldn't rename under it!
    pub fn names_mentioned_and_bound(&self) -> Vec<Name> {
        match *self {
            Nothing | Protected(_) => vec![],
            Shadow(ref lhs, ref rhs) => {
                let mut res = lhs.names_mentioned_and_bound();
                let mut r_res = rhs.names_mentioned_and_bound();
                res.append(&mut r_res);
                res
            }
            ShadowAll(ref sub, _) => sub.names_mentioned_and_bound(), // drivers is too broad!
            Basic(n, _) => vec![n],
            SameAs(n, _) => vec![n],
            BoundButNotUsable(n) => vec![n],
            Underspecified(n) => vec![n],
        }
    }

    // alpha::freshen_binders wants this to extract from complex payloads, hence `f`
    pub fn extract_from_mbe<T: Clone + std::fmt::Debug>(
        &self,
        parts: &EnvMBE<T>,
        f: &dyn Fn(&T) -> &Ren,
    ) -> Ren {
        match *self {
            Nothing => Ren::new(),
            Shadow(ref lhs, ref rhs) => {
                lhs.extract_from_mbe(parts, f).set_assoc(&rhs.extract_from_mbe(parts, f))
            }
            ShadowAll(ref sub_beta, ref drivers) => {
                let mut res = Ren::new();
                for parts in parts.march_all(drivers) {
                    // Maybe `march_all` should memoize?
                    res = res.set_assoc(&sub_beta.extract_from_mbe(&parts, f));
                }
                res
            }
            Basic(n_s, _)
            | SameAs(n_s, _)
            | BoundButNotUsable(n_s)
            | Underspecified(n_s)
            | Protected(n_s) => f(parts.get_leaf_or_panic(&n_s)).clone(),
        }
    }
}

/// Find the environment represented by `b`.
/// `SameAs` and `Basic` nodes will cause walking in `Mode`, which should be positive.
/// TODO: Unfortunately, this means that they don't work well in the subtyping walk, for instance.
pub fn env_from_beta<Mode: crate::walk_mode::WalkMode>(
    b: &Beta,
    parts: &LazyWalkReses<Mode>,
) -> Result<Assoc<Name, Mode::Elt>, Mode::Err> {
    // TODO: figure out why we *do* get called (during subtyping, apparently)
    // if !Mode::D::is_positive() { icp!("e_f_b on {:#?} in {} (negative)", b, Mode::name())}
    match *b {
        Nothing => Ok(Assoc::new()),
        Shadow(ref lhs, ref rhs) => {
            Ok(env_from_beta::<Mode>(&*lhs, parts)?
                .set_assoc(&env_from_beta::<Mode>(&*rhs, parts)?))
        }
        ShadowAll(ref sub_beta, ref drivers) => {
            let mut res = Assoc::new();
            for parts in parts.march_all(drivers) {
                res = res.set_assoc(&env_from_beta::<Mode>(&*sub_beta, &parts)?);
            }
            Ok(res)
        }
        Basic(name_source, rhs_source) => {
            if let LazilyWalkedTerm { term: Atom(ref name), .. } =
                **parts.parts.get_leaf_or_panic(&name_source)
            {
                // let LazilyWalkedTerm {term: ref rhs_stx, ..}
                //    = **parts.parts.get_leaf_or_panic(rhs_source);
                let rhs = parts.switch_to_positive().get_res(rhs_source)?;

                Ok(Assoc::new().set(*name, rhs))
            } else {
                panic!(
                    "User error: {:#?} is supposed to supply names, but is not an Atom.",
                    parts.parts.get_leaf_or_panic(&name_source).term
                )
            }
        }

        // `res_source` should be positive and `name_source` should be negative.
        // Gets the names from `name_source`, treating `res_source` as the context.
        SameAs(name_source, ref res_source) => {
            use crate::walk_mode::WalkMode;

            // TODO: isn't this unhygienic in the case of collisions between part names and
            //  names already in the environment?
            // Probably ought to just use `susbsitute` anyways.
            let mut env_for_parts = parts.env.clone();
            for n in res_source.free_vrs() {
                env_for_parts = env_for_parts.set(n, parts.switch_to_positive().get_res(n)?);
            }

            let rhs_parts = parts.switch_to_positive().with_environment(env_for_parts);
            let ctxt: Mode::Elt =
                crate::ast_walk::walk::<<Mode as WalkMode>::AsPositive>(&res_source, &rhs_parts)?;

            // Do the actual work:
            let res = parts.switch_to_negative().with_context(ctxt).get_res(name_source)?;

            // ... and then check that it's the right set of names!
            // Somewhat awkward (but not unsound!) run-time error in the case that
            //  the declared export does not match the actual result of negative type synthesis.
            // This is parallel to unbound variable name errors that we also don't protect against.
            // (This is more like FreshML/Redex than Pure FreshML/Romeo.
            //   The latter have heavyweight logic systems that really aren't worth it,
            //    because the errors in question aren't that bad to debug.)

            // For our purposes, this syntax is "real", so `quote_depth` is 0:
            let expected_res_keys = names_exported_by(parts.get_term_ref(name_source), 0);
            let mut count = 0;
            for (k, _) in res.iter_pairs() {
                if !expected_res_keys.contains(k) {
                    panic!(
                        "{} was exported (we only wanted {:#?} via {:#?})",
                        k, expected_res_keys, res_source
                    );
                    // TODO: make this an `Err`. And test it with ill-formed `Form`s
                }
                count += 1;
            }

            if count != expected_res_keys.len() {
                // TODO: Likewise:
                panic!("expected {:?} exports, got {}", expected_res_keys, count)
            }

            Ok(res)
        }

        BoundButNotUsable(name_source) => {
            // For our purposes, this syntax is "real", so `quote_depth` is 0:
            let expected_res_keys = names_exported_by(parts.get_term_ref(name_source), 0);

            let mut res = Assoc::new();
            for name in expected_res_keys {
                res = res.set(name, <Mode::Elt as WalkElt>::from_ast(&crate::ast::Trivial));
            }

            Ok(res)
        }

        Underspecified(ref name_source) => {
            if let LazilyWalkedTerm { term: Atom(ref name), .. } =
                **parts.parts.get_leaf_or_panic(name_source)
            {
                Ok(Assoc::new().set(*name, Mode::underspecified(*name)))
            } else {
                panic!(
                    "{:#?} is supposed to supply names, but is not an Atom.",
                    parts.parts.get_leaf_or_panic(name_source).term
                )
            }
        }

        Protected(ref name_source) => {
            // Since protection isn't binding, it gets variable references instead
            if let LazilyWalkedTerm { term: ExtendEnv(ref boxed_vr, _), .. } =
                **parts.parts.get_leaf_or_panic(name_source)
            {
                // HACK: rely on the fact that `walk_var`
                //  won't recursively substitute until it "hits bottom"
                // Drop the variable reference right into the environment.
                Ok(Assoc::new().set(boxed_vr.vr_to_name(), Mode::Elt::from_ast(&*boxed_vr)))
            } else {
                panic!(
                    "{:#?} is supposed to supply names, but is not an EE(VR()).",
                    parts.parts.get_leaf_or_panic(name_source).term
                )
            }
        }
    }
}

// Like `Beta`, but without type information (which gets added at the `import` stage).
// At the moment, this seems to work better...
custom_derive! {
    #[derive(PartialEq, Eq, Clone, Reifiable)]
    pub enum ExportBeta {
        /// Like `Basic`/`SameAs`/`Underspecified`/`Protected`, but without committing to a type
        Use(Name),
        Shadow(Box<ExportBeta>, Box<ExportBeta>),
        /// Shadow the names from a `ExportBeta`, repeated.
        /// The `Vec` should always be equal to `names_mentioned(...)` of the `ExportBeta`.
        ShadowAll(Box<ExportBeta>, Vec<Name>),
        /// No names
        Nothing
    }
}

impl fmt::Debug for ExportBeta {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ExportBeta::Nothing => write!(f, "∅"),
            ExportBeta::Shadow(ref lhs, ref rhs) => write!(f, "({:#?} ▷ {:#?})", lhs, rhs),
            ExportBeta::ShadowAll(ref sub_beta, ref drivers) => {
                write!(f, "( {:#?} ▷ ... by {:#?})", sub_beta, drivers)
            }
            ExportBeta::Use(ref name) => write!(f, "{:#?}", name),
        }
    }
}

impl ExportBeta {
    pub fn names_mentioned(&self) -> Vec<Name> {
        match *self {
            ExportBeta::Nothing => vec![],
            ExportBeta::Shadow(ref lhs, ref rhs) => {
                let mut res = lhs.names_mentioned();
                let mut r_res = rhs.names_mentioned();
                res.append(&mut r_res);
                res
            }
            ExportBeta::ShadowAll(_, ref drivers) => drivers.clone(),
            ExportBeta::Use(n) => vec![n],
        }
    }

    // This has an overly-specific type to match implementation details of alpha::freshen_binders.
    // Not sure if we need a generalization, though.
    pub fn extract_from_mbe<T: Clone + std::fmt::Debug>(
        &self,
        parts: &EnvMBE<T>,
        f: &dyn Fn(&T) -> &Ren,
    ) -> Ren {
        match *self {
            ExportBeta::Nothing => Ren::new(),
            ExportBeta::Shadow(ref lhs, ref rhs) => {
                lhs.extract_from_mbe(parts, f).set_assoc(&rhs.extract_from_mbe(parts, f))
            }
            ExportBeta::ShadowAll(ref sub_beta, ref drivers) => {
                let mut res = Ren::new();
                for parts in parts.march_all(drivers) {
                    // Maybe `march_all` should memoize?
                    res = res.set_assoc(&sub_beta.extract_from_mbe(&parts, f));
                }
                res
            }
            ExportBeta::Use(n_s) => f(parts.get_leaf_or_panic(&n_s)).clone(),
        }
    }
}

// Helper for `bound_from_[export_]beta`:
fn names_exported_by(ast: &Ast, quote_depth: i16) -> Vec<Name> {
    use tap::TapOps;

    match *ast {
        Ast::Atom(n) => vec![n],
        Ast::Node(_, ref sub_parts, ref export) => {
            if quote_depth <= 0 {
                bound_from_export_beta(export, sub_parts, quote_depth)
            } else {
                sub_parts.map_reduce(
                    &|a: &Ast| names_exported_by(a, quote_depth),
                    &|v1, v2| v1.clone().tap(|v1| v1.append(&mut v2.clone())),
                    vec![],
                )
            }
        }
        Ast::ExtendEnv(ref body, _) => names_exported_by(body, quote_depth),
        Ast::QuoteMore(ref body, _) => names_exported_by(body, quote_depth + 1),
        Ast::QuoteLess(ref body, _) => names_exported_by(body, quote_depth - 1),
        ref ast if quote_depth <= 0 => icp!("beta SameAs refers to an invalid AST node: {}", ast),
        _ => vec![],
    }
}

// Like just taking the (non-Protected) keys from `env_from_beta`, but faster and non-failing.
// It's a runtime error if the definition of a form causes `env_from_beta` to diverge from this.
pub fn bound_from_beta(b: &Beta, parts: &EnvMBE<crate::ast::Ast>, quote_depth: i16) -> Vec<Name> {
    match *b {
        Nothing => vec![],
        Shadow(ref lhs, ref rhs) => {
            let mut res = bound_from_beta(&*lhs, parts, quote_depth);
            let mut res_r = bound_from_beta(&*rhs, parts, quote_depth);
            res.append(&mut res_r);
            res
        }
        ShadowAll(ref sub_beta, ref drivers) => {
            let mut res = vec![];
            for sub_parts in &parts.march_all(drivers) {
                res.append(&mut bound_from_beta(&*sub_beta, sub_parts, quote_depth));
            }
            res
        }
        SameAs(ref n_s, _) | BoundButNotUsable(ref n_s) => {
            // Can be a non-atom
            names_exported_by(parts.get_leaf_or_panic(n_s), quote_depth)
        }
        Protected(ref _n_s) => vec![], // Non-binding
        Basic(ref n_s, _) | Underspecified(ref n_s) => {
            vec![parts.get_leaf_or_panic(n_s).to_name()]
        }
    }
}

// Like just taking the keys from `env_from_export_beta`, but faster and non-failing
pub fn bound_from_export_beta(
    b: &ExportBeta,
    parts: &EnvMBE<crate::ast::Ast>,
    quote_depth: i16,
) -> Vec<Name> {
    match *b {
        ExportBeta::Nothing => vec![],
        ExportBeta::Shadow(ref lhs, ref rhs) => {
            let mut res = bound_from_export_beta(&*lhs, parts, quote_depth);
            let mut res_r = bound_from_export_beta(&*rhs, parts, quote_depth);
            res.append(&mut res_r);
            res
        }
        ExportBeta::ShadowAll(ref sub_beta, ref drivers) => {
            let mut res = vec![];
            for sub_parts in &parts.march_all(drivers) {
                res.append(&mut bound_from_export_beta(&*sub_beta, sub_parts, quote_depth));
            }
            res
        }
        ExportBeta::Use(ref n_s) => {
            // Can be a non-atom
            names_exported_by(parts.get_leaf_or_panic(n_s), quote_depth)
        }
    }
}

// TODO NOW: make this return the atom-freshened node (possibly freshening recursive nodes)

// We keep a table, keyed on leaf names and actual atoms, to keep track of the freshening.
// This means that shadowing in leaf-named atom set doesn't get separated.
// (e.g. `.[a : Int  a : Int . ⋯].` freshens to `.[a🍅 : Int  a🍅 : Int . ⋯].`).
// As long as betas can't select a different shadowing direction, this isn't a problem.
pub fn freshening_from_beta(
    b: &Beta,
    parts: &EnvMBE<crate::ast::Ast>,
    memo: &mut std::collections::HashMap<(Name, Name), Name>,
) -> Assoc<Name, Ast> {
    match *b {
        Nothing => Assoc::new(),
        Shadow(ref lhs, ref rhs) => freshening_from_beta(&*lhs, parts, memo)
            .set_assoc(&freshening_from_beta(&*rhs, parts, memo)),
        ShadowAll(ref sub_beta, ref drivers) => {
            let mut res = Assoc::new();
            for parts in parts.march_all(drivers) {
                res = res.set_assoc(&freshening_from_beta(&*sub_beta, &parts, memo));
            }
            res
        }
        Protected(_n_s) => unimplemented!("Not hard, just not used yet"),
        // TODO: n_s isn't necessarily just one name in the `SameAs` case! This is an ICP for sure.
        Basic(n_s, _) | SameAs(n_s, _) | Underspecified(n_s) | BoundButNotUsable(n_s) => {
            let this_name = parts.get_leaf_or_panic(&n_s).to_name();

            Assoc::new().set(
                this_name,
                crate::ast::VariableReference(
                    *memo.entry((n_s, this_name)).or_insert_with(|| this_name.freshen()),
                ),
            )
        }
    }
}

#[test]
fn env_from_beta_basics() {
    let trivial_form = crate::core_type_forms::type_defn("unused", form_pat!((impossible)));

    let complex_ast = ast!({trivial_form;
        "a" => "aa",
        "b" => "bb",
        "c" => (vr "my_int"),
        "d" => (vr "S"),
        "e" => [@"3" "e0", "e1", "e2"],
        "f" => [@"3" (vr "S"), (vr "T"), (vr "S")],
        "g" => [@"3" (vr "my_int"), (vr "my_int"), (vr "my_int")],
        "S" => {"Type" "Nat" :} // same name as a varable in the environment
    });

    let lwr = LazyWalkReses::<crate::ty::SynthTy>::new(
        assoc_n!("my_int" => uty!({Int :}), "S" => uty!(T), "T" => uty!({Int :})),
        assoc_n!(),
        complex_ast.node_parts(),
        complex_ast.clone(),
    );

    assert_eq!(env_from_beta(&beta!([]), &lwr), Ok(assoc_n!()));

    assert_eq!(env_from_beta(&beta!(["a" : "d"]), &lwr), Ok(assoc_n!("aa" => uty!({Int :}))));

    assert_eq!(
        env_from_beta(&beta!([* ["e" : "f"]]), &lwr),
        Ok(assoc_n!("e0" => uty!({Int :}), "e1" => uty!({Int :}), "e2" => uty!({Int :})))
    );

    assert_eq!(
        env_from_beta(&beta!([*["e" = "g"]]), &lwr),
        Ok(assoc_n!("e0" => uty!({Int :}), "e1" => uty!({Int :}), "e2" => uty!({Int :})))
    );

    assert_eq!(
        env_from_beta(&beta!(["a" += {Type fn : [d] d}]), &lwr),
        Ok(assoc_n!("aa" => uty!({fn : [{Int :}] {Int :}})))
    );

    // Name collision: why isn't this failing?
    assert_eq!(
        env_from_beta(&beta!(["a" += {Type fn : [d] S}]), &lwr),
        Ok(assoc_n!("aa" => uty!({fn : [{Int :}] {Nat:}})))
    );

    assert_eq!(env_from_beta(&beta!(["a" : "S"]), &lwr), Ok(assoc_n!("aa" => uty!({Nat :}))));
}

// fn fold_beta<T>(b: Beta, over: Assoc<Name, T>,
//                    leaf: Fn(&Ast ) -> S

// TODO: Test negative quasiquotation (in a non end-to-end way):
//   '[Expr | (plus one (plus one (plus ,[lhs], ,[rhs], )))]'
// #[test]
// fn beta_with_negative_quasiquote() {
//
// }
