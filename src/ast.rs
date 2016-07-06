#![macro_use]

use util::assoc::Assoc;
use name::*;
use beta::Beta;
use std::iter;
use std::cmp::PartialEq;
use std::fmt;
use std::rc::Rc;
use form::Form;

use parse::FormPat;
use ast_walk::WalkRule;

#[derive(Clone, PartialEq)]
pub enum Ast<'t> {
    Trivial,
    Atom(Name<'t>),
    VariableReference(Name<'t>),
    Shape(Vec<Ast<'t>>),
    Node(Rc<Form<'t>>, Assoc<Name<'t>, Ast<'t>>),
    IncompleteNode(Assoc<Name<'t>, Ast<'t>>),
    ExtendEnv(Box<Ast<'t>>, Beta<'t>)
}

macro_rules! ast_shape {
    ($($contents:tt)*) => { Shape(vec![ $(  ast!($contents) ),* ] )};
}


pub use self::Ast::*;


macro_rules! ast {
    ( (import $beta:tt $sub:tt) ) => {
        ExtendEnv(Box::new(ast!($sub)), beta!($beta))
    };
    ( (vr $var:expr) ) => { VariableReference(n($var)) };
    ( (, $interp:expr)) => { $interp };
    ( ( $( $list:tt )* ) ) => { ast_shape!($($list)*)};
    ( { $form:expr; [ $($part_name:tt => $sub:tt ),* ] }) => {
        ast!( { $form ; $($part_name => $sub),* } )
    };
    ( { $form:expr; $($part_name:tt => $sub:tt ),* }) => {
        Node($form, assoc_n!( $( $part_name => ast!($sub) ),* ))
    };
    ($e:expr) => { Atom(n($e))}
}


impl<'t> fmt::Debug for Ast<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Trivial => { write!(f, "⨉") },
            Atom(ref n) => { write!(f, "⋅{:?}⋅", n) },
            VariableReference(ref v) => { write!(f, "{:?}", v)}
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
            Node(ref form, ref body) => { 
                write!(f, "{{ ({:?}); {:?} }}", form.name, body)
            }
            IncompleteNode(ref body) => {
                write!(f, "{{ INCOMPLETE; {:?} }}", body)                
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
    pub fn flatten(&self) -> Assoc<Name<'t>, Ast<'t>> {
        match *self {
            Trivial => Assoc::new(),
            Atom(_) => Assoc::new(),
            VariableReference(_) => Assoc::new(),
            Shape(ref v) => {
                let mut accum = Assoc::new();
                for sub_a in v {
                    accum = accum.set_assoc(&sub_a.flatten())
                }
                accum
            },
            IncompleteNode(ref env) => { env.clone() }
            Node(ref _f, ref _body) => {
                // TODO: think about what should happen when 
                //  `Scope` contains a `Scope` without an intervening `Named`
                panic!("I don't know what to do here!")
            },
            ExtendEnv(ref body, _) => body.flatten()
        }
    }
}

// This is used by combine::many, which is used by the Star parser
impl<'t> iter::FromIterator<Ast<'t>> for Ast<'t> {
    fn from_iter<I: IntoIterator<Item=Ast<'t>>>(i: I) -> Self {
        Shape(i.into_iter().collect())
    }
}

