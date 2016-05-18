#![macro_use]

use util::assoc::Assoc;
use name::*;
use std::iter;
use std::fmt;

#[derive(Clone, PartialEq, Eq)]
pub enum Ast<'t> {
    Trivial,
    Atom(Name<'t>),
    Shape(Vec<Ast<'t>>),
    Node(Assoc<Name<'t>, Ast<'t>>)
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
                    try!(elt.fmt(f));
                    if !first { try!(write!(f, " ")) }
                }
                write!(f, "]")
            },
            Node(ref assoc) => { assoc.fmt(f) }
        }
    }
}

impl<'t> Ast<'t> {
    /// TODO: this ought have MBE-style support for repetition
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
                }
                Node(ref contents) => contents.clone()
            }
        }
        Node(flatten(self))
    }

}

use self::Ast::*;

impl<'t> iter::FromIterator<Ast<'t>> for Ast<'t> {
    fn from_iter<I: IntoIterator<Item=Ast<'t>>>(i: I) -> Self {
        Shape(i.into_iter().collect())
    }
}

macro_rules! ast {
    ($($contents:tt)*) => { Shape(vec![ $(  ast_elt!($contents) ),* ] )};
}

macro_rules! ast_elt {
    ( ( $( $list:tt )* ) ) => { ast!($($list)*)};
    ( [ ] ) => { Node(Assoc::new()) } ;
    ( [ $n:expr; $sub:tt $(, $n_cdr:expr; $sub_cdr:tt )* ] ) =>  {
        if let Node(contents) = ast_elt!( [ $( $n_cdr:expr; $sub_cdr:tt ),* ] ) {
            Node(contents.set(n($n), ast_elt!($sub)))
        } else {
            panic!("internal macro error!")
        }
    };
    ($e:expr) => { Atom(n($e)) }
}
