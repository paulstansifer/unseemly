
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
