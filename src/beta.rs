#![macro_use]

use std::fmt;
use name::*;
use ast_walk::{ResEnv, LazyWalkReses, LazilyWalkedTerm, WalkMode};
use util::assoc::Assoc;
use ast::{Ast, Atom};


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
 The leaf nodes, `Basic` and `SameAs`
 */

#[derive(PartialEq, Eq, Clone)]
pub enum Beta<'t> {
    /// Both of these `Name`s refer to named terms in the current `Scope` (or `ResEnv`, for `Ast`s).
    /// The first is the identifier to import, and the second the syntax for its type.
    Basic(Name<'t>, Name<'t>),
    /// Like `Basic`, but here the second part is another expression 
    /// which should be typechecked, and whose type the new name gets.
    /// (This can be used write `let` without requiring a type annotation.)
    SameAs(Name<'t>, Name<'t>),
    /// Shadow the names from two `Beta`s.
    Shadow(Box<Beta<'t>>, Box<Beta<'t>>),
    /// Shadow the names from a `Beta`, repeated.
    /// The `Vec` should always be equal to `names_mentioned(...)` of the `Beta`.
    ShadowAll(Box<Beta<'t>>, Vec<Name<'t>>),
    Nothing
}

pub use self::Beta::*;

impl<'t> fmt::Debug for Beta<'t> {
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
        }
    }
}

impl<'t> Beta<'t> {
    pub fn names_mentioned(&self) -> Vec<Name<'t>> {
        match self {
            &Nothing => { vec![] }
            &Shadow(ref lhs, ref rhs) => { 
                let mut res = lhs.names_mentioned();
                let mut r_res = rhs.names_mentioned();
                res.append(&mut r_res);
                res
            }
            &ShadowAll(_, ref drivers) => { drivers.clone() }
            &Basic(ref n, ref v) => { vec![*n, *v] }
            &SameAs(ref n, ref v_source) => { vec![*n, *v_source] }
        }
    }
}

pub fn env_from_beta<'t, Mode: WalkMode<'t>>(b: &Beta<'t>, parts: &LazyWalkReses<'t, Mode>)
         -> Result<ResEnv<'t, Mode::Elt>, ()> {
    match b {
        &Nothing => { Ok(Assoc::new()) }
        &Shadow(ref lhs, ref rhs) => {
            Ok(try!(env_from_beta(&*lhs, parts))
                .set_assoc(&try!(env_from_beta(&*rhs, parts))))
        }
        &ShadowAll(ref sub_beta, ref drivers) => {
            let mut res = Assoc::new();
            for parts in parts.march_all(drivers) {
                res = res.set_assoc(&try!(env_from_beta(&*sub_beta, &parts)));
            }
            Ok(res)
        }
        &Basic(ref name_source, ref ty_source) => {
            if let LazilyWalkedTerm {term: Atom(ref name), ..} 
                    = **parts.parts.get_leaf_or_panic(name_source) {
                let LazilyWalkedTerm {term: ref ty_stx, ..}
                    = **parts.parts.get_leaf_or_panic(ty_source);
                        
                Ok(Assoc::new().set(*name, Mode::ast_to_elt((*ty_stx).clone(), parts)))        
            } else {
                panic!("{:?} is supposed to supply names, but is not an Atom.", 
                    parts.parts.get_leaf_or_panic(name_source).term)
            }
        }
        
        // treats the node `name_source` mentions as a negative node, and gets names from it
        &SameAs(ref name_source, ref res_source) => {
            // TODO: `env_from_beta` needs to return a Result
            let ty = try!(parts.get_res(res_source));
            Ok(Mode::Negative::out_to_env(
                try!(parts.switch_mode::<Mode::Negative>()
                    .with_context(Mode::out_to_elt(ty))
                    .get_res(name_source))))
        }
    }
}

//fn fold_beta<'t, T>(b: Beta<'t>, over: Assoc<Name<'t>, T>,
//                    leaf: Fn(&Ast<'t> ) -> S

