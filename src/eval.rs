
use num::bigint::BigInt;
use util::assoc::Assoc;
use name::*;
use std::rc::Rc;
use ast::Ast;
use ast_walk::{walk, WalkMode, WalkRule, LazyWalkReses};
use form::Form;

#[derive(Debug,Clone,PartialEq)]
pub enum Value<'t> {
    Int(BigInt),
    Ident(ContainedName),
    Cons(Rc<Value<'t>>, Rc<Value<'t>>),
    Function(Rc<Closure<'t>>) // TODO: unsure if this Rc is needed
}

pub use self::Value::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Closure<'t> {
    pub body: Ast<'t>,
    pub param: Name<'t>,
    pub env: Assoc<Name<'t>, Value<'t>>
}

#[derive(Clone, Copy, Debug)]
pub struct Evaluate {}

impl<'t> WalkMode<'t> for Evaluate {
    type Out = Value<'t>;
    
    fn get_walk_rule<'f>(f: &'f Form<'t>) -> &'f WalkRule<'t, Self> {
        &f.eval
    }
}

pub fn eval_top<'t>(expr: &Ast<'t>) -> Result<Value<'t>, ()> {
    eval(expr, Assoc::new())
}

pub fn eval<'t>(expr: &Ast<'t>, env: Assoc<Name<'t>, Value<'t>>)
        -> Result<Value<'t>, ()> {
    walk(expr, Evaluate{}, env, 
         &LazyWalkReses::new(Evaluate{}, Assoc::new(), Assoc::new()))
}