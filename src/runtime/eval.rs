
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
    Ident(ContainedName),
    Cons(Rc<Value<'t>>, Rc<Value<'t>>), // TODO: switch to a different core sequence type
    Function(Rc<Closure<'t>>), // TODO: unsure if this Rc is needed
    BuiltInFunction(BIF<'t>),
    AbstractSyntax(Name<'t>, Rc<Ast<'t>>), // likewise
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
    
    fn get_walk_rule<'f>(f: &'f Form<'t>) -> &'f WalkRule<'t, Self> {
        f.eval.pos()
    }

    // It's not possible to construct the environment of the body of a function 
    // at the point it's written down in code.
    fn automatically_extend_env() -> bool { false }
    
    fn var_to_out(n: &Name<'t>, env: &Assoc<Name<'t>, Value<'t>>) -> Result<Value<'t>, ()> {
        ::ast_walk::var_lookup(n, env)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct NegativeEvaluate{}

impl<'t> WalkMode<'t> for NegativeEvaluate {
    type Out = Assoc<Name<'t>, Value<'t>>;
    type Elt = Value<'t>;
    
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
}


pub fn eval_top<'t>(expr: &Ast<'t>) -> Result<Value<'t>, ()> {
    eval(expr, Assoc::new())
}

pub fn eval<'t>(expr: &Ast<'t>, env: Assoc<Name<'t>, Value<'t>>) -> Result<Value<'t>, ()> {
    walk(expr, Evaluate{}, env, 
         &LazyWalkReses::new(Evaluate{}, Assoc::new(), ::util::mbe::EnvMBE::new()))
}

pub fn neg_eval<'t>(pat: &Ast<'t>, env: Assoc<Name<'t>, Value<'t>>)
        -> Result<Assoc<Name<'t>, Value<'t>>,()> {
    walk(pat, NegativeEvaluate{}, env,
         &LazyWalkReses::new(NegativeEvaluate{}, Assoc::new(), ::util::mbe::EnvMBE::new()))
}



/** This is for parts of this compiler that can also be represented as object-level values.
 * 
 * Since this language is extensible, we need to connect the Rust code in the compiler
 *  with the Unseemly code that actually gets evaluated.
 * This is where the magic happens.
 *
 * This is also where ICEs can happen, so make sure that ::type() is consistent with ::reify().
 */

trait Reifiable {
    /// The Unseemly type that corresponds to Self.
    fn ty() -> Ast<'static>;
    
    /// What should Unseemly programmers call this type?
    fn type_name() -> Name<'static>;
    
    /// The Unseemly value that corresponds to a value.
    fn reify<'t>(&self) -> Value<'t>;
    
    /// Get a value from an Unseemly value
    fn reflect<'t>(&Value<'t>) -> Self;
}