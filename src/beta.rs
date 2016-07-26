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
    Shadow(Box<Beta<'t>>, Box<Beta<'t>>),
    Nothing
}

pub use self::Beta::*;

impl<'t> fmt::Debug for Beta<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Nothing => { write!(f, "∅") },
            Shadow(ref lhs, ref rhs) => { write!(f, "({:?} ▷ {:?})", lhs, rhs) },
            Basic(ref name, ref ty) => { write!(f, "{:?}:{:?}", name, ty) }
            SameAs(ref name, ref ty_source) => { 
                write!(f, "{:?}={:?}", name, ty_source)
            }
        }
    }
}

pub fn env_from_beta<'t, Mode: WalkMode<'t>>
    (b: &Beta<'t>, parts: &LazyWalkReses<'t, Mode>)
         -> ResEnv<'t, Mode::Out> {
    match b {
        &Nothing => { Assoc::new() }
        &Shadow(ref lhs, ref rhs) => {
            env_from_beta(&*lhs, parts)
                .set_assoc(&env_from_beta(&*rhs, parts))
        }
        &Basic(ref name_source, ref ty_source) => {
            //Assoc::new().set(parts.get_term(name_source).unwrap(), )
            if let LazilyWalkedTerm {term: Atom(ref name), ..} 
                    = **parts.parts.get_leaf_or_die(name_source) {
                let LazilyWalkedTerm {term: ref ty_stx, ..}
                    = **parts.parts.get_leaf_or_die(ty_source);
                        
                Assoc::new().set(*name, Mode::ast_to_out((*ty_stx).clone()))        
            } else {
                panic!("{:?} is supposed to supply names, but is not an Atom.", 
                    parts.parts.get_leaf_or_die(name_source).term)
            }
            
        }
        &SameAs(ref _name_source, ref _ty_source) => {
            panic!("TODO! Not implemented! But should be easy!")
        }
    }
}

//fn fold_beta<'t, T>(b: Beta<'t>, over: Assoc<Name<'t>, T>,
//                    leaf: Fn(&Ast<'t> ) -> S

macro_rules! beta_connector {
    ( : ) => { Basic };
    ( = ) => { SameAs }
}

macro_rules! beta {
    ( [] ) => { Nothing };
    ( [ $name:tt $connector:tt $t:tt
        $(, $name_cdr:tt $connector_cdr:tt $t_cdr:tt )*
         ] ) => { 
        Shadow(Box::new(beta_connector!($connector)(n(expr_ify!($name)), 
                                                    n(expr_ify!($t)))),
               Box::new(beta!( [ $( $name_cdr $connector_cdr $t_cdr ),* ] )))
    }
}
