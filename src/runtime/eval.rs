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
pub enum Value {
    Int(BigInt),
    Bool(bool),
    Ident(Name),
    Sequence(Vec<Rc<Value>>), // TODO: switch to a different core sequence type
    Function(Rc<Closure>), // TODO: unsure if this Rc is needed
    BuiltInFunction(BIF),
    AbstractSyntax(Name, Rc<Ast>), // likewise. Also, I'm not sure `Name` is right...
    Struct(Assoc<Name, Value>),
    Enum(Name, Vec<Value>) // A real compiler would probably tag with numbers...
}

pub use self::Value::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Closure {
    pub body: Ast,
    pub params: Vec<Name>,
    pub env: Assoc<Name, Value>
}

pub struct BIF(pub Rc<(Fn(Vec<Value>) -> Value)>);

impl PartialEq for BIF {
    fn eq(&self, other: &BIF) -> bool {
        self as *const BIF == other as *const BIF
    }
}

impl Clone for BIF {
    fn clone(&self) -> BIF {
        BIF(self.0.clone())
    }
}

impl std::fmt::Debug for BIF {
    fn fmt(&self, formatter: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        formatter.write_str("[built-in function]")
    }
}

custom_derive! {
    #[derive(Clone, Copy, Debug, Reifiable)]
    pub struct Evaluate {}
}

impl WalkMode for Evaluate {
    type Out = Value;
    type Elt = Value;
    
    type Negative = NegativeEvaluate;
    
    fn get_walk_rule<'f>(f: &'f Form) -> &'f WalkRule<Self> {
        f.eval.pos()
    }

    // It's not possible to construct the environment of the body of a function 
    // at the point it's written down in code.
    fn automatically_extend_env() -> bool { false }
    
    fn ast_to_elt(a: Ast, parts: &LazyWalkReses<Self>) -> Self::Elt { 
        walk::<Evaluate>(&a, parts).unwrap() //TODO: this should probably return a result
    }
    
    fn var_to_out(n: &Name, env: &Assoc<Name, Value>) -> Result<Value, ()> {
        ::ast_walk::var_lookup(n, env)
    }
    
    fn out_to_elt(o: Self::Out) -> Self::Elt { o }
    
    fn positive() -> bool { true }
}

custom_derive! {
    #[derive(Clone, Copy, Debug, Reifiable)]
    pub struct NegativeEvaluate {}
}

impl WalkMode for NegativeEvaluate {
    type Out = Assoc<Name, Value>;
    type Elt = Value;
    
    type Negative = Evaluate;
    
    fn get_walk_rule<'f>(f: &'f Form) -> &'f WalkRule<Self> {
        &f.eval.neg()
    }

    // It's not possible to construct the environment of the body of a function 
    // at the point it's written down in code.
    fn automatically_extend_env() -> bool { false }
    
    fn var_to_out(n: &Name, env: &Assoc<Name, Value>) -> Result<Assoc<Name, Value>, ()> {
        ::ast_walk::var_bind(n, env)
    }
    
    fn out_to_env(o: Self::Out) -> Assoc<Name, Self::Elt> { o }
    fn env_to_out(e: Assoc<Name, Self::Elt>) -> Self::Out { e }

    fn positive() -> bool { false }
}

custom_derive! {
    #[derive(Clone, Copy, Debug, Reifiable)]
    pub struct Quasiquote {}
}

impl WalkMode for Quasiquote {
    type Out = Value;
    type Elt = Value;
    
    type Negative = NegativeQuasiquote;
    
    fn get_walk_rule<'f>(f: &'f Form) -> &'f WalkRule<Self> {
        f.quasiquote.pos()
    }
    
    fn automatically_extend_env() -> bool { true } // but will it get the right phase?
    
    fn ast_to_elt(a: Ast, _: &LazyWalkReses<Self>) -> Self::Elt {
        Value::AbstractSyntax(n("<unknown>"), Rc::new(a))
    }
    
    fn ast_to_out(a: Ast) -> Self::Out {
        Value::AbstractSyntax(n("<unknown>"), Rc::new(a))
    }
    
    fn out_to_elt(o: Self::Out) -> Self::Elt { o }
    
    fn out_to_ast(o: Self::Out) -> Ast {
        match o {
            Value::AbstractSyntax(_, a) => (*a).clone(),
            _ => panic!("ICE: messed-up syntax")
        }
    }
    
    fn var_to_out(n: &Name, env: &Assoc<Name, Self::Elt>) -> Result<Self::Out, ()> {
        ::ast_walk::var_lookup(n, env)
    }
    
    fn positive() -> bool { true }
}

custom_derive! {
    #[derive(Clone, Copy, Debug, Reifiable)]
    pub struct NegativeQuasiquote {}
}

impl WalkMode for NegativeQuasiquote {
    type Out = Assoc<Name, Value>;
    type Elt = Value;
    
    type Negative = Quasiquote;
    
    fn get_walk_rule<'f>(f: &'f Form) -> &'f WalkRule<Self> {
        f.quasiquote.neg()
    }
    
    fn automatically_extend_env() -> bool { true } // but will it get the right phase?
    
    fn ast_to_elt(a: Ast, _: &LazyWalkReses<Self>) -> Self::Elt {
        Value::AbstractSyntax(n("<unknown>"), Rc::new(a))
    }
    
    fn var_to_out(n: &Name, env: &Assoc<Name, Self::Elt>) -> Result<Self::Out, ()> {
        ::ast_walk::var_bind(n, env)
    }
    
    fn out_to_env(o: Self::Out) -> Assoc<Name, Self::Elt> { o }
    fn env_to_out(e: Assoc<Name, Self::Elt>) -> Self::Out { e }
    
    fn positive() -> bool { false }
}

pub fn eval_top(expr: &Ast) -> Result<Value, ()> {
    eval(expr, Assoc::new())
}

pub fn eval(expr: &Ast, env: Assoc<Name, Value>) -> Result<Value, ()> {
    walk::<Evaluate>(expr, &LazyWalkReses::new_wrapper(env))
}

pub fn neg_eval(pat: &Ast, env: Assoc<Name, Value>)
        -> Result<Assoc<Name, Value>,()> {
    walk::<NegativeEvaluate>(pat, 
        &LazyWalkReses::<NegativeEvaluate>::new_wrapper(env))
}

