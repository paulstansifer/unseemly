#![macro_use]

use crate::{
    ast::Ast,
    ast_walk::{walk, LazyWalkReses, WalkRule},
    form::Form,
    name::*,
    util::assoc::Assoc,
    walk_mode::{NegativeWalkMode, WalkMode},
};
use num::bigint::BigInt;
use std::{self, rc::Rc};

/// Values in Unseemly.

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(BigInt),
    Sequence(Vec<Rc<Value>>), // TODO: switch to a different core sequence type
    Function(Rc<Closure>),    // TODO: unsure if this Rc is needed
    BuiltInFunction(BIF),
    AbstractSyntax(Ast),
    Struct(Assoc<Name, Value>),
    Enum(Name, Vec<Value>),
    // Hypothesis: all strings are either
    //  in a formal language (and should be stored as ASTs instead)
    //  or in a human language (and should be tokens for localization).
    // But for now, here's a plain string.
    Text(String),
    Cell(Rc<std::cell::RefCell<Value>>),
    // Reifying `Form`s causes loss of identity, so have an explicit (opaque) representation.
    // Perhaps drop reification entirely, and just use an opaque type based on `std::any::Any`?
    ParseContext(Box<crate::earley::ParseContext>),
}

pub use self::Value::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Closure {
    pub body: Ast,
    pub params: Vec<Name>,
    pub env: Assoc<Name, Value>,
}

impl Value {
    /// Turns this `Value` into a "magic" `Ast` that evaluates to it.
    /// The `Ast` will have the universal type
    pub fn prefab(self) -> Ast {
        raw_ast!(Node(
            typed_form!(
                "prefab_internal",
                (impossible), // no syntax
                cust_rc_box!(move |_| Ok(ast!(
                        // Cheat: has the universal type, but we know it's safe because <mumble>.
                        {"Type" "forall_type" :
                            "param" => ["T"],
                            "body" => (import [* [forall "param"]] (vr "T"))}))),
                cust_rc_box!(move |_| Ok(self.clone()))
            ),
            crate::util::mbe::EnvMBE::new(),
            crate::beta::ExportBeta::Nothing
        ))
    }
}

/// Creates an (ill-typed!) lambda expression that behaves like the closure.
/// Free names in `self.body` remain free.
impl Closure {
    pub fn prefab(&self) -> Ast {
        ast!({"Expr" "lambda" :
            "param" => (@"p" ,seq self.params.iter().map(|n| ast!(*n)).collect::<Vec<Ast>>()),
            "p_t" => (@"p" ,seq self.params.iter().map(|_| ast!((trivial))).collect::<Vec<Ast>>()),
            "body" => (import [* ["param" : "p_t"]] (,
                crate::alpha::substitute(&self.body,
                    &self.env.map(|v| v.clone().prefab())
                )
            ))
        })
    }
}

// Built-in function
pub struct BIF(pub Rc<(dyn Fn(Vec<Value>) -> Value)>);

pub fn apply__function_value(f: &Value, args: Vec<Value>) -> Value {
    match *f {
        BuiltInFunction(BIF(ref f)) => f(args.into_iter().collect()),
        Function(ref cl) => {
            let mut clo_env = cl.env.clone();
            if cl.params.len() != args.len() {
                panic!(
                    "[type error] Attempted to apply {} arguments to function requiring {} \
                     parameters",
                    args.len(),
                    cl.params.len()
                );
            }
            for (p, a) in cl.params.iter().zip(args.into_iter()) {
                clo_env = clo_env.set(*p, a)
            }
            eval(&cl.body, clo_env).unwrap()
        }
        _ => panic!("[type error] {:#?} is not a function", f),
    }
}

impl PartialEq for BIF {
    fn eq(&self, other: &BIF) -> bool { self as *const BIF == other as *const BIF }
}

impl Clone for BIF {
    fn clone(&self) -> BIF { BIF(self.0.clone()) }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match *self {
            Int(ref bi) => write!(f, "{}", bi),
            Sequence(ref seq) => {
                for elt in seq {
                    write!(f, "{}", &*elt)?;
                }
                Ok(())
            }
            Function(_) => write!(f, "[closure]"),
            BuiltInFunction(_) => write!(f, "[built-in function]"),
            AbstractSyntax(ref ast) => write!(f, "'[{}]'", ast),
            Struct(ref parts) => {
                write!(f, "*[")?;
                for (k, v) in parts.iter_pairs() {
                    write!(f, "{}: {} ", k, v)?;
                }
                write!(f, "]*")
            }
            Enum(n, ref parts) => {
                write!(f, "+[{}", n)?;
                for p in parts.iter() {
                    write!(f, " {}", p)?;
                }
                write!(f, "]+")
            }
            Text(ref st) => write!(f, "{}", st),
            Cell(ref cell) => write!(f, "{}", cell.borrow()),
            ParseContext(_) => write!(f, "[a language]"),
        }
    }
}

impl std::fmt::Debug for BIF {
    fn fmt(&self, formatter: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        formatter.write_str("[built-in function]")
    }
}

impl crate::walk_mode::WalkElt for Value {
    fn from_ast(a: &Ast) -> Value { AbstractSyntax(a.clone()) }
    fn to_ast(&self) -> Ast {
        match *self {
            AbstractSyntax(ref a) => a.clone(),
            _ => icp!("[type error] {} is not syntax", self),
        }
    }
}

custom_derive! {
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct Eval {}
}
custom_derive! {
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct Destructure {}
}

impl WalkMode for Eval {
    fn name() -> &'static str { "Evalu" }

    type Elt = Value;
    type Negated = Destructure;
    type AsPositive = Eval;
    type AsNegative = Destructure;
    type Err = ();
    type D = crate::walk_mode::Positive<Eval>;
    type ExtraInfo = ();

    fn get_walk_rule(f: &Form) -> WalkRule<Eval> {
        // Macro invocations use `eval`, to avoid having a whole extra field in `Form`:
        if f.name == n("macro_invocation") {
            icp!("unexpanded macro!")
        }
        f.eval.pos().clone()
    }
    fn automatically_extend_env() -> bool { true }

    fn walk_var(n: Name, cnc: &LazyWalkReses<Eval>) -> Result<Value, ()> {
        match cnc.env.find(&n) {
            Some(v) => Ok(v.clone()),
            None => panic!("Undefined var `{}` in {}", n, cnc.env),
        }
    }

    // TODO: maybe keep this from being called?
    fn underspecified(_: Name) -> Value { val!(enum "why is this here?", ) }
}

impl WalkMode for Destructure {
    fn name() -> &'static str { "Destr" }

    type Elt = Value;
    type Negated = Eval;
    type AsPositive = Eval;
    type AsNegative = Destructure;
    type Err = ();
    type D = crate::walk_mode::Negative<Destructure>;
    type ExtraInfo = ();

    /// The whole point of program evaluation is that the enviornment
    ///  isn't generateable from the source tree.
    /// Does that make sense? I suspect it does not.
    fn get_walk_rule(f: &Form) -> WalkRule<Destructure> { f.eval.neg().clone() }
    fn automatically_extend_env() -> bool { true } // TODO: think about this
}

impl NegativeWalkMode for Destructure {
    fn needs_pre_match() -> bool { false } // Values don't have binding (in this mode!)
}

impl crate::walk_mode::WalkElt for Ast {
    fn from_ast(a: &Ast) -> Ast { a.clone() }
    fn to_ast(&self) -> Ast { self.clone() }
}

pub fn eval_top(expr: &Ast) -> Result<Value, ()> { eval(expr, Assoc::new()) }

pub fn eval(expr: &Ast, env: Assoc<Name, Value>) -> Result<Value, ()> {
    walk::<Eval>(expr, &LazyWalkReses::new_wrapper(env))
}

pub fn neg_eval(pat: &Ast, env: Assoc<Name, Value>) -> Result<Assoc<Name, Value>, ()> {
    walk::<Destructure>(pat, &LazyWalkReses::new_wrapper(env))
}

custom_derive! {
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct QQuote {}
}
custom_derive! {
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct QQuoteDestr {}
}

impl WalkMode for QQuote {
    fn name() -> &'static str { "QQuote" }

    // Why not `Ast`? Because QQuote and Eval need to share environments.
    type Elt = Value;
    type Negated = QQuoteDestr;
    type AsPositive = QQuote;
    type AsNegative = QQuoteDestr;
    type Err = ();
    type D = crate::walk_mode::Positive<QQuote>;
    type ExtraInfo = ();

    fn walk_var(n: Name, _: &LazyWalkReses<Self>) -> Result<Value, ()> { Ok(val!(ast (vr n))) }
    fn walk_atom(n: Name, _: &LazyWalkReses<Self>) -> Result<Value, ()> { Ok(val!(ast (at n))) }
    // TODO #26: Just special-case "unquote" and "dotdotdot"
    fn get_walk_rule(f: &Form) -> WalkRule<QQuote> { f.quasiquote.pos().clone() }
    fn automatically_extend_env() -> bool { false }
}

impl WalkMode for QQuoteDestr {
    fn name() -> &'static str { "QQDes" }

    type Elt = Value;
    type Negated = QQuote;
    type AsPositive = QQuote;
    type AsNegative = QQuoteDestr;
    type Err = ();
    type D = crate::walk_mode::Negative<QQuoteDestr>;
    type ExtraInfo = ();

    fn walk_var(n: Name, cnc: &LazyWalkReses<Self>) -> Result<Assoc<Name, Value>, ()> {
        let val = val!(ast (vr n));
        if cnc.context_elt() == &val {
            Ok(Assoc::<Name, Value>::new())
        } else {
            Err(Self::qlit_mismatch_error(val, cnc.context_elt().clone()))
        }
    }
    fn walk_atom(n: Name, cnc: &LazyWalkReses<Self>) -> Result<Assoc<Name, Value>, ()> {
        let val = val!(ast (at n));
        if cnc.context_elt() == &val {
            Ok(Assoc::<Name, Value>::new())
        } else {
            Err(Self::qlit_mismatch_error(val, cnc.context_elt().clone()))
        }
    }
    // TODO #26: Just special-case "unquote"
    fn get_walk_rule(f: &Form) -> WalkRule<QQuoteDestr> { f.quasiquote.neg().clone() }
    fn automatically_extend_env() -> bool { false }
}

impl NegativeWalkMode for QQuoteDestr {
    fn needs_pre_match() -> bool { true } // Quoted syntax does have binding!
}

// `env` is a trap! We want a shifted `LazyWalkReses`!
// pub fn qquote(expr: &Ast, env: Assoc<Name, Value>) -> Result<Value, ()> {
//     walk::<QQuote>(expr, &LazyWalkReses::new_wrapper(env))
// }
//
// pub fn qquote_destr(pat: &Ast, env: Assoc<Name, Value>)
//         -> Result<Assoc<Name, Value>,()> {
//     walk::<QQuoteDestr>(pat, &LazyWalkReses::new_wrapper(env))
// }
