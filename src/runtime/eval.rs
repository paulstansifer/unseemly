#![macro_use]

use num::bigint::BigInt;
use util::assoc::Assoc;
use name::*;
use std::rc::Rc;
use ast::Ast;
use ast_walk::{walk, WalkMode, WalkRule, LazyWalkReses};
use form::Form;
use std;

/**
 * Values in Unseemly.
 */

#[derive(Debug,Clone,PartialEq)]
pub enum Value<'t> {
    Int(BigInt),
    Bool(bool),
    Ident(Name<'t>), // TODO: is the lifetime okay here?
    Cons(Rc<Value<'t>>, Rc<Value<'t>>), // TODO: switch to a different core sequence type
    Function(Rc<Closure<'t>>), // TODO: unsure if this Rc is needed
    BuiltInFunction(BIF<'t>),
    AbstractSyntax(Name<'t>, Rc<Ast<'t>>), // likewise. Also, I'm not sure `Name` is right...
    Struct(Assoc<Name<'t>, Value<'t>>),
    Enum(Name<'t>, Vec<Value<'t>>) // A real compiler would probably tag with numbers...
}

pub use self::Value::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Closure<'t> {
    pub body: Ast<'t>,
    pub params: Vec<Name<'t>>,
    pub env: Assoc<Name<'t>, Value<'t>>
}

pub struct BIF<'t>(pub Rc<(Fn(Vec<Value<'t>>) -> Value<'t>)>);

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
    type Elt = Value<'t>;
    
    type Negative = NegativeEvaluate;
    
    fn get_walk_rule<'f>(f: &'f Form<'t>) -> &'f WalkRule<'t, Self> {
        f.eval.pos()
    }

    // It's not possible to construct the environment of the body of a function 
    // at the point it's written down in code.
    fn automatically_extend_env() -> bool { false }
    
    fn ast_to_elt(a: Ast<'t>, parts: &LazyWalkReses<'t, Self>) -> Self::Elt { 
        walk::<Evaluate>(&a, parts).unwrap() //TODO: this should probably return a result
    }
    
    fn var_to_out(n: &Name<'t>, env: &Assoc<Name<'t>, Value<'t>>) -> Result<Value<'t>, ()> {
        ::ast_walk::var_lookup(n, env)
    }
    
    fn out_to_elt(o: Self::Out) -> Self::Elt { o }
    
    fn positive() -> bool { true }
}

#[derive(Clone, Copy, Debug)]
pub struct NegativeEvaluate{}

impl<'t> WalkMode<'t> for NegativeEvaluate {
    type Out = Assoc<Name<'t>, Value<'t>>;
    type Elt = Value<'t>;
    
    type Negative = Evaluate;
    
    fn get_walk_rule<'f>(f: &'f Form<'t>) -> &'f WalkRule<'t, Self> {
        &f.eval.neg()
    }

    // It's not possible to construct the environment of the body of a function 
    // at the point it's written down in code.
    fn automatically_extend_env() -> bool { false }
    
    fn var_to_out(n: &Name<'t>, env: &Assoc<Name<'t>, Value<'t>>) 
            -> Result<Assoc<Name<'t>, Value<'t>>, ()> {
        ::ast_walk::var_bind(n, env)
    }
    
    fn out_to_env(o: Self::Out) -> Assoc<Name<'t>, Self::Elt> { o }
    
    fn positive() -> bool { false }
}


pub fn eval_top<'t>(expr: &Ast<'t>) -> Result<Value<'t>, ()> {
    eval(expr, Assoc::new())
}

pub fn eval<'t>(expr: &Ast<'t>, env: Assoc<Name<'t>, Value<'t>>) -> Result<Value<'t>, ()> {
    walk::<Evaluate>(expr, &LazyWalkReses::new(env, ::util::mbe::EnvMBE::new()))
}

pub fn neg_eval<'t>(pat: &Ast<'t>, env: Assoc<Name<'t>, Value<'t>>)
        -> Result<Assoc<Name<'t>, Value<'t>>,()> {
    walk::<NegativeEvaluate>(pat, 
        &LazyWalkReses::<NegativeEvaluate>::new(env, ::util::mbe::EnvMBE::new()))
}

