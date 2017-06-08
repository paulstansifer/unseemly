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
    Ident(Name), // TODO: this is subsumed by AbstractSyntax, isn't it?
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

impl ::ast_walk::WalkElt<Eval> for Value {
    type Err = ();
    
    fn get_bidi_walk_rule(f: &Form) -> &::form::BiDiWR<Eval, Destructure> { &f.eval }
    
    /// The whole point of program evaluation is that the enviornment 
    ///  isn't generateable from the source tree.
    /// Does that make sense? I suspect it does not.
    fn automatically_extend_env() -> bool { false }
    
    /// We'd need to know what `nt` we're at, so the quotation form has to do this work...
    fn from_ast(_: &Ast) -> Value { panic!("ICE: tried to convert Ast to Value") }
    /// This is possible, but should be handled by the unquotation form
    fn to_ast(&self) -> Ast { panic!("ICE: shoudn't happen...")}
}

pub type Eval = ::ast_walk::PositiveWalkMode<Value, ()>;
pub type Destructure = ::ast_walk::NegativeWalkMode<Value, ()>;




impl ::ast_walk::WalkElt<QQuote> for Ast {
    type Err = ();
    
    fn get_bidi_walk_rule(f: &Form) -> &::form::BiDiWR<QQuote, QQuoteDestr> { &f.quasiquote }

    fn automatically_extend_env() -> bool { true } // This is the point of Unseemly!
    
    fn from_ast(a: &Ast) -> Ast { a.clone() }
    fn to_ast(&self) -> Ast { self.clone() }
}


pub fn eval_top(expr: &Ast) -> Result<Value, ()> {
    eval(expr, Assoc::new())
}

pub fn eval(expr: &Ast, env: Assoc<Name, Value>) -> Result<Value, ()> {
    walk::<Eval>(expr, &LazyWalkReses::new_wrapper(env))
}

pub fn neg_eval(pat: &Ast, env: Assoc<Name, Value>)
        -> Result<Assoc<Name, Value>,()> {
    walk::<Destructure>(pat, &LazyWalkReses::new_wrapper(env))
}

pub type QQuote = ::ast_walk::PositiveWalkMode<Ast, ()>;
pub type QQuoteDestr = ::ast_walk::NegativeWalkMode<Ast, ()>;
