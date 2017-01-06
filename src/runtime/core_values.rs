
use ast::Ast;
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

pub fn erase_types(tv: &TypedValue) -> Value { tv.val.clone() }



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
             ( Int(a) ) => { Bool(a == BigInt::from(0))} )
    )
}


#[test]
fn basic_core_value_evaluation() {
    use core_forms::find_core_form;
    
    let cte = core_typed_values();
    let ce = cte.map(&erase_types);
    
    let env = ce.set(n("one"), Int(BigInt::from(1)));
    
    assert_eq!(eval(
        &ast!({ find_core_form( "expr", "apply") ;
            "rator" => (vr "plus"),
            "rand" => [ (vr "one"), (vr "one") ]
        }),
        env),
        Ok(Int(BigInt::from(2))));
}
