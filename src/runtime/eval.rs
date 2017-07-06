#![macro_use]

use num::bigint::BigInt;
use util::assoc::Assoc;
use name::*;
use std::rc::Rc;
use ast::Ast;
use ast_walk::{walk, WalkMode, WalkRule, LazyWalkReses, NegativeWalkMode};
use form::Form;
use std;

/**
 * Values in Unseemly.
 */

#[derive(Debug,Clone,PartialEq)]
pub enum Value {
    Int(BigInt),
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

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match self {
            &Int(ref bi) => { write!(f, "{}", bi) }
            &Ident(n) => { write!(f, "{}", n) }
            &Sequence(ref seq) => {
                for elt in seq { try!(write!(f, "{}", &*elt)); }; Ok(())
            }
            &Function(_) => { write!(f, "[closure]") }
            &BuiltInFunction(_) => { write!(f, "[built-in function]") }
            &AbstractSyntax(n, ref ast) => { write!(f, "{}: {:?}", n, ast) }
            &Struct(ref parts) => {
                try!(write!(f, "*["));
                for (k,v) in parts.iter_pairs() {
                    try!(write!(f, "{}: {} ", k, v));
                }
                write!(f, "]*")
            }
            &Enum(n, ref parts) => {
                try!(write!(f, "+[{}", n));
                for p in parts.iter() { try!(write!(f, " {}", p)); }
                write!(f, "]+")
            }
        }
    }
}

impl std::fmt::Debug for BIF {
    fn fmt(&self, formatter: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        formatter.write_str("[built-in function]")
    }
}

impl ::ast_walk::WalkElt for Value {
    /// We'd need to know what `nt` we're at, so the quotation form has to do this work...
    fn from_ast(_: &Ast) -> Value { panic!("ICE: tried to convert Ast to Value") }
    /// This is possible, but should be handled by the unquotation form
    fn to_ast(&self) -> Ast { panic!("ICE: shoudn't happen...")}
}



custom_derive!{
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct Eval {}
}
custom_derive!{
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct Destructure {}
}

impl WalkMode for Eval {
    type Elt = Value;
    type Negated = Destructure;
    type Err = ();
    type D = ::ast_walk::Positive<Eval>;

    fn get_walk_rule(f: &Form) -> &WalkRule<Eval> { &f.eval.pos() }
    fn automatically_extend_env() -> bool { false }

    fn walk_var(n: Name, cnc: &LazyWalkReses<Eval>) -> Result<Value, ()> {
        Ok(cnc.env.find(&n).expect("Undefined var; did you use a type name as a value?").clone())
    }

    // TODO: maybe keep this from being called?
    fn underspecified(_: Name) -> Value { val!(enum "why is this here?", ) }
}

impl WalkMode for Destructure {
    type Elt = Value;
    type Negated = Eval;
    type Err = ();
    type D = ::ast_walk::Negative<Destructure>;

    /// The whole point of program evaluation is that the enviornment
    ///  isn't generateable from the source tree.
    /// Does that make sense? I suspect it does not.
    fn get_walk_rule(f: &Form) -> &WalkRule<Destructure> { &f.eval.neg() }
    fn automatically_extend_env() -> bool { false } // TODO: think about this
}

impl NegativeWalkMode for Destructure {}

impl ::ast_walk::WalkElt for Ast {
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

custom_derive!{
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct QQuote {}
}
custom_derive!{
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct QQuoteDestr {}
}

impl WalkMode for QQuote {
    type Elt = Ast;
    type Negated = QQuoteDestr;
    type Err = ();
    type D = ::ast_walk::Positive<QQuote>;

    fn get_walk_rule(f: &Form) -> &WalkRule<QQuote> { &f.quasiquote.pos() }
    fn automatically_extend_env() -> bool { true } // This is the point of Unseemly!
}

impl WalkMode for QQuoteDestr {
    type Elt = Ast;
    type Negated = QQuote;
    type Err = ();
    type D = ::ast_walk::Negative<QQuoteDestr>;

    fn get_walk_rule(f: &Form) -> &WalkRule<QQuoteDestr> { &f.quasiquote.neg() }
    fn automatically_extend_env() -> bool { true } // This is the point of Unseemly!
}

impl NegativeWalkMode for QQuoteDestr {}
