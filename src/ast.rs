#![macro_use]

use util::assoc::Assoc;
use name::*;
use beta::Beta;
use std::iter;
use std::cmp::PartialEq;
use std::fmt;
use std::rc::Rc;
use form::Form;

#[derive(Clone, PartialEq)]
pub enum Ast<'t> {
    Trivial,
    Atom(Name<'t>),
    Shape(Vec<Ast<'t>>),
    Env(Assoc<Name<'t>, Ast<'t>>),
    Node(Rc<Form<'t>>, Rc<Ast<'t>>),
    ExtendEnv(Box<Ast<'t>>, Beta<'t>)
}


/*

{ lam ; [ "rator" => ... , "rator_type" => ... ,
          "rand" => ( ... ↓ "rator" : "rator_type ] }

*/

macro_rules! ast_shape {
    ($($contents:tt)*) => { Shape(vec![ $(  ast!($contents) ),* ] )};
}


pub use self::Ast::*;


macro_rules! ast {
    ( (import $beta:tt $sub:tt) ) => {
        ExtendEnv(Box::new(ast!($sub)), beta!($beta))
    };
    ( (, $interp:expr)) => { $interp };
    ( ( $( $list:tt )* ) ) => { ast_shape!($($list)*)};
    ( [ ] ) => { Env(Assoc::new()) };
    ( [ $n:tt => $sub:tt $(, $n_cdr:tt => $sub_cdr:tt )* ] ) =>  {
        if let Env(contents) = ast!( [ $( $n_cdr => $sub_cdr ),* ] ) {
            Env(contents.set(n(expr_ify!($n)), ast!($sub)))
        } else {
            panic!("internal macro error!")
        }
    };
    ( { $form:expr; $sub:tt } ) => { Node($form, Rc::new(ast!($sub)))};
    ($e:tt) => { Atom(n(expr_ify!($e))) }
}


impl<'t> fmt::Debug for Ast<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Trivial => { write!(f, "⨉") },
            Atom(ref n) => { write!(f, "{:?}", n) },
            Shape(ref v) => {
                try!(write!(f, "["));
                let mut first = true;
                for elt in v {
                    if !first { try!(write!(f, " ")) }
                    try!(elt.fmt(f));
                    first = false;
                }
                write!(f, "]")
            },
            Env(ref assoc) => { assoc.fmt(f) },
            Node(ref form, ref body) => { 
                write!(f, "{{ ({:?}); {:?} }}", form.name, body)
            }
            ExtendEnv(ref body, ref beta) => {
                write!(f, "{:?}↓{:?}", body, beta)
            }
        }
    }
}

impl<'t> Ast<'t> {
    // TODO: this ought have MBE-style support for repetition
    // TODO: this ought to at least warn if we're losing anything other than `Shape`
    pub fn flatten_to_node(&self) -> Ast<'t> {
        
        fn flatten<'t>(a: & Ast<'t>) -> Assoc<Name<'t>, Ast<'t>> {
            match *a {
                Trivial => Assoc::new(),
                Atom(_) => Assoc::new(),
                Shape(ref v) => {
                    let mut accum = Assoc::new();
                    for sub_a in v {
                        accum = accum.set_assoc(&flatten(&sub_a))
                    }
                    accum
                },
                // TODO: think about unusual `Ast`s and how they should behave.
                Env(ref contents) => contents.clone(),
                Node(_, ref body) => flatten(body) ,
                ExtendEnv(ref body, _) => flatten(body)
            }
        }
        Env(flatten(self))
    }

}

impl<'t> iter::FromIterator<Ast<'t>> for Ast<'t> {
    fn from_iter<I: IntoIterator<Item=Ast<'t>>>(i: I) -> Self {
        Shape(i.into_iter().collect())
    }
}

