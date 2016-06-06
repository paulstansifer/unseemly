#![macro_use]

use std::fmt;
use name::*;

#[derive(PartialEq, Eq, Clone)]
pub enum Beta<'t> {
    /// Both of these `Name`s refer to named terms in the current `Scope` (or `Env`, for `Ast`s).
    /// The first is the identifier to import, and the second is the type.
    Basic(Name<'t>, Name<'t>),
    Shadow(Box<Beta<'t>>, Box<Beta<'t>>),
    Nothing
}

use self::Beta::*;

impl<'t> fmt::Debug for Beta<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Nothing => { write!(f, "∅") },
            Shadow(ref lhs, ref rhs) => { write!(f, "({:?} ▷ {:?})", lhs, rhs) },
            Basic(ref name, ref ty) => { write!(f, "{:?}:{:?}", name, ty) }
        }
    }
}

//fn fold_beta<'t, T>(b: Beta<'t>, over: Assoc<Name<'t>, T>,
//                    leaf: Fn(&Ast<'t> ) -> S

macro_rules! beta {
    ( [ $name:tt : $t:tt
        $(, $name_cdr:tt : $t_cdr:tt )*
         ] ) => { 
        Shadow(Box::new(Basic(n(expr_ify!($name)), n(expr_ify!($t)))),
               Box::new(beta!( [ $( $name_cdr : $t_cdr ),* ] )))
    }
}