#![macro_use]

use std::fmt;
use name::*;
use ast_walk::{LazyWalkReses, LazilyWalkedTerm};
use util::assoc::Assoc;
use ast::{Ast,Atom,VariableReference,ExtendEnv};
use util::mbe::EnvMBE;
use walk_mode::Dir;
use alpha::Ren;


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
        or an expression producting the type (`SameAs`)
        for that name.

    I have no idea where the name "β" came from, and whether it has any connection to α-equivalence.

    There's probably a very elegant way to make `Beta` just another kind of `Ast`.
    Finding it might require some time in the math mines, though.
    */
    #[derive(PartialEq, Eq, Clone, Reifiable)]
    pub enum Beta {
        /// Both of these `Name`s refer to named terms in the current `Scope`
        ///  (or `ResEnv`, for `Ast`s).
        /// The first is the identifier to import, and the second the syntax for its type.
        Basic(Name, Name),
        /// Like `Basic`, but here the second part is another expression
        /// which should be typechecked, and whose type the new name gets.
        /// (This can be used write to `let` without requiring a type annotation.)
        SameAs(Name, Name),
        /// Name is introduced here, and its meaning is figured out from usage.
        Underspecified(Name),
        /// Name is left alone (only makes sense in `LiteralLike` regimes, where var refs are okay)
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
            Nothing => { write!(f, "∅") },
            Shadow(ref lhs, ref rhs) => { write!(f, "({:#?} ▷ {:#?})", lhs, rhs) },
            ShadowAll(ref sub_beta, ref drivers) => {
                write!(f, "( {:#?} ▷ ... by {:#?})", sub_beta, drivers)
            }
            Basic(ref name, ref ty) => { write!(f, "{:#?}:{:#?}", name, ty) }
            SameAs(ref name, ref ty_source) => {
                write!(f, "{:#?}={:#?}", name, ty_source)
            }
            Underspecified(ref name) => {
                write!(f, "∀{:#?}", name)
            }
            Protected(ref name) => {
                write!(f, "↫{:#?}", name)
            }
        }
    }
}

impl Beta {
    pub fn names_mentioned(&self) -> Vec<Name> {
        match *self {
            Nothing => { vec![] }
            Shadow(ref lhs, ref rhs) => {
                let mut res = lhs.names_mentioned();
                let mut r_res = rhs.names_mentioned();
                res.append(&mut r_res);
                res
            }
            ShadowAll(_, ref drivers) => { drivers.clone() }
            Basic(n, v) => { vec![n, v] }
            SameAs(n, v_source) => { vec![n, v_source] }
            Underspecified(n) => { vec![n] }
            Protected(n) => { vec![n] }
        }
    }

    // `Protected` doens't actually bind, so we shouldn't rename under it!
    pub fn names_mentioned_and_bound(&self) -> Vec<Name> {
        match *self {
            Nothing | Protected(_) => { vec![] }
            Shadow(ref lhs, ref rhs) => {
                let mut res = lhs.names_mentioned_and_bound();
                let mut r_res = rhs.names_mentioned_and_bound();
                res.append(&mut r_res);
                res
            }
            ShadowAll(ref sub, _) => { sub.names_mentioned_and_bound() } // drivers is too broad!
            Basic(n, v) => { vec![n, v] }
            SameAs(n, v_source) => { vec![n, v_source] }
            Underspecified(n) => { vec![n] }
        }
    }

    // alpha::freshen_binders wants this to extract from complex payloads, hence `f`
    pub fn extract_from_mbe<T: Clone + ::std::fmt::Debug>(
                &self, parts: &EnvMBE<T>, f: &Fn(&T) -> &Ren) -> Ren {
        match *self {
            Nothing => { Ren::new() }
            Shadow(ref lhs, ref rhs) => {
                lhs.extract_from_mbe(parts, f).set_assoc(&rhs.extract_from_mbe(parts, f))
            }
            ShadowAll(ref sub_beta, ref drivers) => {
                let mut res = Ren::new();
                for parts in parts.march_all(drivers) { // Maybe `march_all` should memoize?
                    res = res.set_assoc(&sub_beta.extract_from_mbe(&parts, f));
                }
                res
            }
            Basic(n_s, _) | SameAs(n_s, _) | Underspecified(n_s) | Protected(n_s)=> {
                f(parts.get_leaf_or_panic(&n_s)).clone()
            }
        }
    }


}

/// Find the environment represented by `b`.
/// `SameAs` and `Basic` nodes will cause walking in `Mode`, which should be positive.
/// TODO: Unfortunately, this means that they don't work well in the subtyping walk, for instance.
pub fn env_from_beta<Mode: ::walk_mode::WalkMode>(b: &Beta, parts: &LazyWalkReses<Mode>)
         -> Result<Assoc<Name, Mode::Elt>, Mode::Err> {
    // TODO: figure out why we *do* get called (during subtyping, apparently)
    //if !Mode::D::is_positive() { panic!("ICE: e_f_b on {:#?} in {} (negative)", b, Mode::name())}
    match *b {
        Nothing => { Ok(Assoc::new()) }
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
        Basic(name_source, ty_source) => {
            if let LazilyWalkedTerm {term: Atom(ref name), ..}
                    = **parts.parts.get_leaf_or_panic(&name_source) {
                //let LazilyWalkedTerm {term: ref ty_stx, ..}
                //    = **parts.parts.get_leaf_or_panic(ty_source);
                let ty = parts.get_res(ty_source)?;

                Ok(Assoc::new().set(*name, Mode::out_as_elt(ty.clone())))
            } else {
                panic!("User error: {:#?} is supposed to supply names, but is not an Atom.",
                    parts.parts.get_leaf_or_panic(&name_source).term)
            }
        }

        // `res_source` should be positive and `name_source` should be negative.
        // Gets the names from `name_source`, treating `res_source` as the context.
        SameAs(name_source, res_source) => {
            use walk_mode::WalkMode;

            let ctxt = parts.get_res(res_source)?;

            // Do the actual work:
            let res = Mode::Negated::out_as_env(
                parts.switch_mode::<Mode::Negated>()
                    .with_context(Mode::out_as_elt(ctxt))
                    .get_res(name_source)?);

            // ... and then check that it's the right set of names!
            // Somewhat awkward (but not unsound!) run-time error in the case that
            //  the declared export does not match the actual result of negative type synthesis.
            // This is parallel to unbound variable name errors that we also don't protect against.
            // (This is more like FreshML/Redex than Pure FreshML/Romeo.
            //   The latter have heavyweight logic systems that really aren't worth it,
            //    because the errors in question aren't that bad to debug.)

            if let Ast::Node(_, ref sub_parts, ref export) = parts.get_term(name_source) {
                // For our purposes, this syntax is "real", so `quote_depth` is 0:
                let expected_res_keys = bound_from_export_beta(export, sub_parts, 0);

                let mut count = 0;
                for (k, _) in res.iter_pairs() {
                    if !expected_res_keys.contains(k) {
                        panic!("{} was exported (we only wanted {:#?} via {:#?})",
                               k, expected_res_keys, parts.get_term(res_source));
                        // TODO: make this an `Err`. And test it with ill-formed `Form`s
                    }
                    count += 1;
                }

                if count != expected_res_keys.len() { // TODO: Likewise:
                    panic!("expected {:?} exports, got {}", expected_res_keys, count)
                }
            }

            Ok(res)
        }

        Underspecified(ref name_source) => {
            if let LazilyWalkedTerm {term: Atom(ref name), ..}
                    = **parts.parts.get_leaf_or_panic(name_source) {
                Ok(Assoc::new().set(*name, Mode::underspecified(*name)))
            } else {
                panic!("{:#?} is supposed to supply names, but is not an Atom.",
                    parts.parts.get_leaf_or_panic(name_source).term)
            }
        }

        Protected(ref name_source) => {
            // Since protection isn't binding, it gets variable references instead
            if let LazilyWalkedTerm {term: ExtendEnv(ref boxed_vr,_), ..}
                    = **parts.parts.get_leaf_or_panic(name_source) {
                use walk_mode::WalkElt;

                // HACK: rely on the fact that `walk_var`
                //  won't recursively substitute until it "hits bottom"
                // Drop the variable reference right into the environment.
                Ok(Assoc::new().set(::core_forms::vr_to_name(&*boxed_vr),
                                    Mode::Elt::from_ast(&*boxed_vr)))
            } else {
                panic!("{:#?} is supposed to supply names, but is not an EE(VR()).",
                    parts.parts.get_leaf_or_panic(name_source).term)
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
            ExportBeta::Nothing => { write!(f, "∅") },
            ExportBeta::Shadow(ref lhs, ref rhs) => { write!(f, "({:#?} ▷ {:#?})", lhs, rhs) },
            ExportBeta::ShadowAll(ref sub_beta, ref drivers) => {
                write!(f, "( {:#?} ▷ ... by {:#?})", sub_beta, drivers)
            }
            ExportBeta::Use(ref name) => { write!(f, "{:#?}", name) }
        }
    }
}

impl ExportBeta {
    pub fn names_mentioned(&self) -> Vec<Name> {
        match *self {
            ExportBeta::Nothing => { vec![] }
            ExportBeta::Shadow(ref lhs, ref rhs) => {
                let mut res = lhs.names_mentioned();
                let mut r_res = rhs.names_mentioned();
                res.append(&mut r_res);
                res
            }
            ExportBeta::ShadowAll(_, ref drivers) => { drivers.clone() }
            ExportBeta::Use(n) => { vec![n] }
        }
    }

    // This has an overly-specific type to match implementation details of alpha::freshen_binders.
    // Not sure if we need a generalization, though.
    pub fn extract_from_mbe<T: Clone + ::std::fmt::Debug>(
            &self, parts: &EnvMBE<T>, f: &Fn(&T) -> &Ren) -> Ren {
        match *self {
            ExportBeta::Nothing => { Ren::new() }
            ExportBeta::Shadow(ref lhs, ref rhs) => {
                lhs.extract_from_mbe(parts, f).set_assoc(&rhs.extract_from_mbe(parts, f))
            }
            ExportBeta::ShadowAll(ref sub_beta, ref drivers) => {
                let mut res = Ren::new();
                for parts in parts.march_all(drivers) { // Maybe `march_all` should memoize?
                    res = res.set_assoc(&sub_beta.extract_from_mbe(&parts, f));
                }
                res
            }
            ExportBeta::Use(n_s) => {
                f(parts.get_leaf_or_panic(&n_s)).clone()
            }
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
                sub_parts.map_reduce(&|a: &Ast| names_exported_by(a, quote_depth),
                                     &|v1, v2| v1.clone().tap(|v1| v1.append(&mut v2.clone())),
                                     vec![])
            }
        }
        Ast::QuoteMore(ref body, _) => names_exported_by(body, quote_depth+1),
        Ast::QuoteLess(ref body, _) => names_exported_by(body, quote_depth-1),
        ref ast if quote_depth <= 0 => {
            panic!("ICE: beta SameAs refers to an invalid AST node: {}", ast)
        }
        _ => { vec![] }
    }
}

// Like just taking the (non-Protected) keys from `env_from_beta`, but faster and non-failing.
// It's a runtime error if the definition of a form causes `env_from_beta` to diverge from this.
pub fn bound_from_beta(b: &Beta, parts: &EnvMBE<::ast::Ast>, quote_depth: i16) -> Vec<Name> {
    match *b {
        Nothing => { vec![] }
        Shadow(ref lhs, ref rhs) => {
            let mut res = bound_from_beta(&*lhs, parts, quote_depth);
            let mut res_r = bound_from_beta(&*rhs, parts, quote_depth);
            res.append(&mut res_r);
            res
        }
        ShadowAll(ref sub_beta, ref drivers) => {
            let mut res = vec![];
            for ref sub_parts in parts.march_all(drivers) {
                res.append(&mut bound_from_beta(&*sub_beta, sub_parts, quote_depth));
            }
            res
        }
        SameAs(ref n_s, _) => { // Can be a non-atom
            names_exported_by(parts.get_leaf_or_panic(n_s), quote_depth)
        }
        Protected(ref _n_s) => { vec![] } // Non-binding
        Basic(ref n_s, _) | Underspecified(ref n_s) => {
            vec![::core_forms::ast_to_name(parts.get_leaf_or_panic(n_s))]
        }
    }
}

// Like just taking the keys from `env_from_export_beta`, but faster and non-failing
pub fn bound_from_export_beta(b: &ExportBeta, parts: &EnvMBE<::ast::Ast>, quote_depth: i16)
        -> Vec<Name> {
    match *b {
        ExportBeta::Nothing => { vec![] }
        ExportBeta::Shadow(ref lhs, ref rhs) => {
            let mut res = bound_from_export_beta(&*lhs, parts, quote_depth);
            let mut res_r = bound_from_export_beta(&*rhs, parts, quote_depth);
            res.append(&mut res_r);
            res
        }
        ExportBeta::ShadowAll(ref sub_beta, ref drivers) => {
            let mut res = vec![];
            for ref sub_parts in parts.march_all(drivers) {
                res.append(&mut bound_from_export_beta(&*sub_beta, sub_parts, quote_depth));
            }
            res
        }
        ExportBeta::Use(ref n_s) => { // Can be a non-atom
            names_exported_by(parts.get_leaf_or_panic(n_s), quote_depth)
        }
    }
}


// TODO NOW: make this return the atom-freshened node (possibly freshening recursive nodes)

// We keep a table, keyed on leaf names and actual atoms, to keep track of the freshening.
// This means that shadowing in leaf-named atom set doesn't get separated.
// (e.g. `.[a : Int  a : Int . ⋯].` freshens to `.[a🍅 : Int  a🍅 : Int . ⋯].`).
// As long as betas can't select a different shadowing direction, this isn't a problem.
pub fn freshening_from_beta(b: &Beta, parts: &EnvMBE<::ast::Ast>,
                            memo: &mut ::std::collections::HashMap<(Name, Name), Name>)
         -> Assoc<Name, Ast> {
    match *b {
        Nothing => { Assoc::new() }
        Shadow(ref lhs, ref rhs) => {
            freshening_from_beta(&*lhs, parts, memo)
                .set_assoc(&freshening_from_beta(&*rhs, parts, memo))
        }
        ShadowAll(ref sub_beta, ref drivers) => {
            let mut res = Assoc::new();
            for parts in parts.march_all(drivers) {
                res = res.set_assoc(&freshening_from_beta(&*sub_beta, &parts, memo));
            }
            res
        }
        Protected(_n_s) => { unimplemented!("Not hard, just not used yet")}
        Basic(n_s, _) | SameAs(n_s, _) | Underspecified(n_s) => {
            let this_name = ::core_forms::ast_to_name(parts.get_leaf_or_panic(&n_s));

            Assoc::new().set(this_name, ::ast::VariableReference(*memo.entry((n_s, this_name))
                .or_insert_with(||{ this_name.freshen() })))
        }
    }
}

//fn fold_beta<T>(b: Beta, over: Assoc<Name, T>,
//                    leaf: Fn(&Ast ) -> S

// TODO: I know we don't handle negative quasiquotation correctly:
//   '[Expr | (plus one (plus one (plus ,[Expr | lhs], ,[Expr | rhs], )))]'
// should export `lhs` and `rhs`. But how?
/*
#[test]
fn beta_with_negative_quasiquote() {

}
*/
