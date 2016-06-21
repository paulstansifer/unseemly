
use ast::Ast;
use ast::Ast::*;
use eval::{Value, BIF};
use eval::Value::*;
use parse::SynEnv;
use core_forms::find_form;
use util::assoc::Assoc;
use name::*;
use std::rc::Rc;
use std::ops::{Add,Sub,Mul};


use num::BigInt;
use num::Zero;

pub struct TypedValue<'t> {
    pub ty: Ast<'t>,
    pub val: Value<'t>
}


macro_rules! mk_type {
    ( $se:expr, [ () -> $ret_t:tt] ) => { ast!($ret_t) };
    ( $se:expr, [ ( $param_car:tt $(, $param_cdr:tt)* )  -> $ret_t:tt ] ) => {
        ast!( { find_form($se, "type", "fn") ; 
            [
                "param" => (, mk_type!($se, $param_car) ),
                "ret" => (, mk_type!($se, [( $($param_cdr),* ) -> $ret_t] ))
            ]
        })
    };
    ( $se:expr, $n:tt ) => { ast!($n) };
}

macro_rules! tf {
    ( $se:expr, [ ( $($param_t:tt),* ) -> $ret_t:tt ] , 
       ( $($param_p:pat),* ) => $body:expr) => {
        TypedValue {
            ty: mk_type!($se, [ ( $($param_t),* ) -> $ret_t ] ),
            val: n_arg_fn!( ( $($param_p),* ) => $body)
        }
    }
}


macro_rules! one_arg_fn {
    ( $p:pat, $body:expr ) => {
        BuiltInFunction(BIF(Rc::new(
            /* this clone should be removable if we ever stop currying */
            move | v | {match v.clone() {$p => { $body }, _ => { panic!("Type ICE") }}})))
    }
}

macro_rules! n_arg_fn {
    ( ( ) => $body:expr ) => { $body };
    ( ( $p_car:pat $(, $p_cdr:pat)* ) => $body:expr) => {
        one_arg_fn!( $p_car, n_arg_fn!( ( $($p_cdr),* ) => $body))
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
                 ( Int(a) ) => { Bool(a.is_zero())} )
    )
}