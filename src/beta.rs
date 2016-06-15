#![macro_use]

use std::fmt;
use name::*;
use ty::{TyEnv, LazyPartTypes, LazilyTypedTerm};
use util::assoc::Assoc;
use ast::{Ast, Atom};

#[derive(PartialEq, Eq, Clone)]
pub enum Beta<'t> {
    /// Both of these `Name`s refer to named terms in the current `Scope` (or `Env`, for `Ast`s).
    /// The first is the identifier to import, and the second the syntax for its type.
    Basic(Name<'t>, Name<'t>),
    /// Like `Basic`, but here the second part is another expression 
    /// which should be typechecked, and whose type the new name gets.
    /// (This can be used write `let` without requiring a type annotation.)
    SameTypeAs(Name<'t>, Name<'t>),
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
            SameTypeAs(ref name, ref ty_source) => { 
                write!(f, "{:?}={:?}", name, ty_source)
            }
        }
    }
}

pub fn env_from_beta<'t>(b: &Beta<'t>, parts: LazyPartTypes<'t>)
         -> TyEnv<'t> {
    match b {
        &Nothing => { Assoc::new() }
        &Shadow(ref lhs, ref rhs) => {
            env_from_beta(&*lhs, parts.clone())
                .set_assoc(&env_from_beta(&*rhs, parts))
        }
        &Basic(ref name_source, ref ty_source) => {
                        
            if let Some(& LazilyTypedTerm {term: Atom(ref name), ty: _} ) 
                    = parts.parts.find(name_source) {
                if let Some(& LazilyTypedTerm {term: ref ty_stx, ty: _} )
                        = parts.parts.find(ty_source) {
                    Assoc::new().set(*name, (*ty_stx).clone())
                } else {
                    panic!("Type {:?} not found in {:?}", ty_source, parts);
                }
            } else {
                panic!("Name {:?} not found in {:?}", name_source, parts);
            }
        }
        &SameTypeAs(ref _name_source, ref _ty_source) => {
            panic!("TODO! Thread typechecking information here!")
        }
    }
}

//fn fold_beta<'t, T>(b: Beta<'t>, over: Assoc<Name<'t>, T>,
//                    leaf: Fn(&Ast<'t> ) -> S

macro_rules! beta_connector {
    ( : ) => { Basic };
    ( = ) => { SameTypeAs }
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