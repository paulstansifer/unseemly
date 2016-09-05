
use ast::Ast;
use ast::Ast::*;
use runtime::eval::{Value, BIF, eval};
use runtime::eval::Value::*;
use parse::SynEnv;
use core_forms::{find_form, make_core_syn_env};
use util::assoc::Assoc;
use name::*;
use std::rc::Rc;
use std::ops::{Add,Sub,Mul};


use num::{BigInt};

#[derive(Debug,Clone,PartialEq)]
pub struct TypedValue<'t> {
    pub ty: Ast<'t>,
    pub val: Value<'t>
}

pub fn erase_types<'t>(tv: TypedValue<'t>) -> Value<'t> { tv.val }


macro_rules! mk_type {
    ( $se:expr, [ ( $( $param:tt ),* )  -> $ret_t:tt ] ) => {
        ast!( { find_form($se, "type", "fn") ; 
                  "param" => [ $((, mk_type!($se, $param) )),*],
                  "ret" => (, mk_type!($se, $ret_t))
        })
    };
    ( $se:expr, $n:tt ) => { ast!($n) };
}

/* Define a typed function */
macro_rules! tf {
    ( $se:expr, [ ( $($param_t:tt),* ) -> $ret_t:tt ] , 
       ( $($param_p:pat),* ) => $body:expr) => {
        TypedValue {
            ty: mk_type!($se, [ ( $($param_t),* ) -> $ret_t ] ),
            val: core_fn!( $($param_p),* => $body)
        }
    }
}

macro_rules! bind_patterns {
    ( $iter:expr; () => $body:expr ) => { $body };
    ( $iter:expr; ($p_car:pat, $($p_cdr:pat,)* ) => $body:expr ) => {
        match $iter.next() {
            Some($p_car) => {
                bind_patterns!($iter; ($( $p_cdr, )*) => $body)
            }
            None => { panic!("ICE: too few arguments"); }
            Some(ref other) => { panic!("Type ICE in argument: {:?}", other); }
        } 
    }
}

macro_rules! core_fn {
    ( $($p:pat),* => $body:expr ) => {
        BuiltInFunction(BIF(Rc::new(
            move | args | { 
                let mut argi = args.into_iter();
                bind_patterns!(argi; ($( $p, )*) => $body )
            }
        )))
    }
}


pub fn core_typed_values<'t>(se: &SynEnv<'t>) -> Assoc<Name<'t>, TypedValue<'t>> {
    assoc_n!(
        "plus" =>
        tf!(se, [( "integer", "integer" ) -> "integer"],
                 ( Int(a), Int(b) ) => { Int( a.clone() + b ) }),
        "minus" =>
        tf!(se, [( "integer", "integer" ) -> "integer"],
                 ( Int(a), Int(b) ) => { Int( a.clone() - b ) }),
        "times" =>
        tf!(se, [( "integer", "integer" ) -> "integer"],
                 ( Int(a), Int(b) ) => { Int( a.clone() * b ) }),
        "zero?" =>
        tf!(se, [( "integer" ) -> "bool"],
                 ( Int(a) ) => { Bool(a == BigInt::from(0))} )
    )
}


#[test]
fn basic_core_value_evaluation() {
    let cse = make_core_syn_env();
    let cte = core_typed_values(&cse);
    let ce = cte.map(&erase_types);
    
    let env = ce.set(n("one"), Int(BigInt::from(1)));
    
    assert_eq!(eval(
        &ast!({ find_form(&cse, "expr", "apply") ;
            "rator" => (vr "plus"),
            "rand" => [ (vr "one"), (vr "one") ]
        }),
        env),
        Ok(Int(BigInt::from(2))));
}