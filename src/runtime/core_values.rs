
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
pub fn erase_value(tv: &TypedValue) -> Ty { Ty(tv.ty.clone()) }


pub fn core_typed_values() -> Assoc<Name, TypedValue> {
    assoc_n!(
        "plus" =>
        tf!([( "integer", "integer" ) -> "integer"],
             ( Int(a), Int(b) ) => { Int( a.clone() + b ) }),
        "minus" =>
        tf!([( "integer", "integer" ) -> "integer"],
             ( Int(a), Int(b) ) => { Int( a.clone() - b ) }),
        "times" =>
        tf!([( "integer", "integer" ) -> "integer"],
             ( Int(a), Int(b) ) => { Int( a.clone() * b ) }),
        "zero?" =>
        tf!([( "integer" ) -> "bool"],
             ( Int(a) ) => { Bool(a == BigInt::from(0))} ),
        "zero" => tf!( "integer", val!(i 0) ),
        "one" => tf!( "integer", val!(i 1) )
        
    )
}

pub fn core_values() -> Assoc<Name, Value> {
    core_typed_values().map(&erase_type)
}

pub fn core_types() -> Assoc<Name, Ty> {
    core_typed_values().map(&erase_value).set_assoc(
        // TODO: This is needed for `type_by_name`s to turn into ... plain names
        &assoc_n!(
            "integer" => ty!("integer"),
            "bool" => ty!("bool")
        )
    )
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
