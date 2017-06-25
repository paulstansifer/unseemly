use ast::Ast;
use ty::Ty;
use runtime::eval::{Value, BIF, eval};
use runtime::eval::Value::*;
use util::assoc::Assoc;
use name::*;
use std::rc::Rc;


use num::{BigInt};

#[derive(Debug,Clone,PartialEq)]
pub struct TypedValue {
    pub ty: Ast,
    pub val: Value
}

pub fn erase_type(tv: &TypedValue) -> Value { tv.val.clone() }
pub fn erase_value(tv: &TypedValue) -> Ty { Ty::new(tv.ty.clone()) }


pub fn core_typed_values() -> Assoc<Name, TypedValue> {
    assoc_n!(
        "plus" =>
        tf!([( "int", "int" ) -> "int"],
             ( Int(a), Int(b) ) => { Int( a.clone() + b ) }),
        "minus" =>
        tf!([( "int", "int" ) -> "int"],
             ( Int(a), Int(b) ) => { Int( a.clone() - b ) }),
        "times" =>
        tf!([( "int", "int" ) -> "int"],
             ( Int(a), Int(b) ) => { Int( a.clone() * b ) }),
        "zero?" =>
        tf!([( "int" ) -> "bool"],
             ( Int(a) ) => { Bool(a == BigInt::from(0))} ),
        "zero" => tf!( "int", val!(i 0) ),
        "one" => tf!( "int", val!(i 1) ),
        "two" => tf!( "int", val!(i 2) ),
        "three" => tf!( "int", val!(i 3) ),
        "four" => tf!( "int", val!(i 4) ),
        "five" => tf!( "int", val!(i 5) ),
        "six" => tf!( "int", val!(i 6) ),
        "seven" => tf!( "int", val!(i 7) ),
        "eight" => tf!( "int", val!(i 8) ),
        "nine" => tf!( "int", val!(i 9) ),
        "ten" => tf!( "int", val!(i 10) ),
        "false" => tf!( "bool", val!(b false)),
        "true" => tf!( "bool", val!(b true))
    )
}

pub fn core_values() -> Assoc<Name, Value> {
    core_typed_values().map(&erase_type)
}

pub fn core_types() -> Assoc<Name, Ty> {
    core_typed_values().map(&erase_value)
}


#[test]
fn basic_core_value_evaluation() {
    use core_forms::find_core_form;

    let cte = core_typed_values();
    let ce = cte.map(&erase_type);

    assert_eq!(eval(
        &ast!({ find_core_form( "expr", "apply") ;
            "rator" => (vr "plus"),
            "rand" => [ (vr "one"), (vr "one") ]
        }),
        ce),
        Ok(Int(BigInt::from(2))));
}
