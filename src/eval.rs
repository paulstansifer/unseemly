
use num::bigint::BigInt;
use util::assoc::Assoc;
use name::*;
use std::rc::Rc;
use ast::Ast;
use ast_walk::{walk, WalkMode, WalkRule, LazyWalkReses};
use form::Form;
use std;

#[derive(Debug,Clone,PartialEq)]
pub enum Value<'t> {
    Int(BigInt),
    Bool(bool),
    Ident(ContainedName),
    Cons(Rc<Value<'t>>, Rc<Value<'t>>),
    Function(Rc<Closure<'t>>), // TODO: unsure if this Rc is needed
    BuiltInFunction(BIF<'t>),
    AbstractSyntax(Name<'t>, Rc<Ast<'t>>) // likewise
}

pub use self::Value::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Closure<'t> {
    pub body: Ast<'t>,
    pub param: Name<'t>,
    pub env: Assoc<Name<'t>, Value<'t>>
}

pub struct BIF<'t>(pub Rc<(Fn(&Value<'t>) -> Value<'t>)>);

impl<'t> PartialEq for BIF<'t> {
    fn eq(&self, other: &BIF<'t>) -> bool {
        self as *const BIF<'t> == other as *const BIF<'t>
    }
}

impl<'t> Clone for BIF<'t> {
    fn clone(&self) -> BIF<'t> {
        BIF(self.0.clone())
    }
}

impl<'t> std::fmt::Debug for BIF<'t> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        formatter.write_str("[built-in function]")
    }
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