#![macro_use]

use util::assoc::Assoc;
use name::*;
use std::iter;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ast<'t> {
    Trivial,
    Atom(Name<'t>),
    Shape(Vec<Ast<'t>>),
    Node(Assoc<Name<'t>, Ast<'t>>)
}

use self::Ast::*;

impl<'t> iter::FromIterator<Ast<'t>> for Ast<'t> {
    fn from_iter<I: IntoIterator<Item=Ast<'t>>>(i: I) -> Self {
        Shape(i.into_iter().collect())
    }
}

macro_rules! ast {
    ($($contents:tt)*) => { Shape(vec![ $(  ast_elt!($contents) ),* ] )}
}

macro_rules! ast_elt {
    ( ( $( $list:tt )* ) ) => { ast!($($list)*)};
    ($e:expr) => { Atom(n($e)) }
}
