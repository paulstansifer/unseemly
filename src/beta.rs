#![macro_use]

use std::fmt;
use name::*;
use ast_walk::{ResEnv, LazyWalkReses, LazilyWalkedTerm, WalkMode};
use util::assoc::Assoc;
use ast::{Atom};


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
 */



custom_derive! {
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
            Shadow(ref lhs, ref rhs) => { write!(f, "({:?} ▷ {:?})", lhs, rhs) },
            ShadowAll(ref sub_beta, ref drivers) => {
                write!(f, "( {:?} ▷ ... by {:?})", sub_beta, drivers)
            }
            Basic(ref name, ref ty) => { write!(f, "{:?}:{:?}", name, ty) }
            SameAs(ref name, ref ty_source) => {
                write!(f, "{:?}={:?}", name, ty_source)
            }
            Underspecified(ref name) => {
                write!(f, "∀{:?}", name)
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

        }
    }
}

// Mode is expected to be positive
pub fn env_from_beta<Mode: WalkMode>(b: &Beta, parts: &LazyWalkReses<Mode>)
         -> Result<Assoc<Name, Mode::Elt>, Mode::Err> {
    match *b {
        Nothing => { Ok(Assoc::new()) }
        Shadow(ref lhs, ref rhs) => {
            Ok(try!(env_from_beta::<Mode>(&*lhs, parts))
                .set_assoc(&try!(env_from_beta::<Mode>(&*rhs, parts))))
        }
        ShadowAll(ref sub_beta, ref drivers) => {
            let mut res = Assoc::new();
            for parts in parts.march_all(drivers) {
                res = res.set_assoc(&try!(env_from_beta::<Mode>(&*sub_beta, &parts)));
            }
            Ok(res)
        }
        Basic(ref name_source, ref ty_source) => {
            if let LazilyWalkedTerm {term: Atom(ref name), ..}
                    = **parts.parts.get_leaf_or_panic(name_source) {
                //let LazilyWalkedTerm {term: ref ty_stx, ..}
                //    = **parts.parts.get_leaf_or_panic(ty_source);
                let ty = try!(parts.get_res(ty_source));

                Ok(Assoc::new().set(*name, Mode::out_as_elt(ty.clone())))
            } else {
                panic!("{:?} is supposed to supply names, but is not an Atom.",
                    parts.parts.get_leaf_or_panic(name_source).term)
            }
        }

        // TODO: I need more help understanding this
        // treats the node `name_source` mentions as a negative node, and gets names from it
        SameAs(ref name_source, ref res_source) => {
            // TODO: `env_from_beta` needs to return a Result
            let ty = try!(parts.get_res(res_source));

            Ok(Mode::Negated::out_as_env(
                try!(parts.switch_mode::<Mode::Negated>()
                    .with_context(Mode::out_as_elt(ty))
                    .get_res(name_source))))
        }

        Underspecified(ref name_source) => {
            if let LazilyWalkedTerm {term: Atom(ref name), ..}
                    = **parts.parts.get_leaf_or_panic(name_source) {
                use ast_walk::WalkElt;

                Ok(Assoc::new().set(*name, Mode::Elt::underspecified()))
            } else {
                panic!("{:?} is supposed to supply names, but is not an Atom.",
                    parts.parts.get_leaf_or_panic(name_source).term)
            }
        }
    }
}

// Like just taking the keys from `env_from_beta`, but faster and non-failing
pub fn keys_from_beta(b: &Beta, parts: &::util::mbe::EnvMBE<::ast::Ast>) -> Vec<Name> {
    match *b {
        Nothing => { vec![] }
        Shadow(ref lhs, ref rhs) => {
            let mut res = keys_from_beta(&*lhs, parts);
            let mut res_r = keys_from_beta(&*rhs, parts);
            res.append(&mut res_r);
            res
        }
        ShadowAll(ref sub_beta, ref drivers) => {
            let mut res = vec![];
            for ref sub_parts in parts.march_all(drivers) {
                res.append(&mut keys_from_beta(&*sub_beta, sub_parts));
            }
            res
        }
        Basic(ref n_s, _) | SameAs(ref n_s, _) | Underspecified(ref n_s)=> {
            vec![::core_forms::ast_to_atom(parts.get_leaf_or_panic(n_s))]
        }
    }
}

//fn fold_beta<T>(b: Beta, over: Assoc<Name, T>,
//                    leaf: Fn(&Ast ) -> S
