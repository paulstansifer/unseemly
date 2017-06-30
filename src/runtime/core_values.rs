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
    let a_to_b = ast!({"type" "fn" : "param" => [(vr "a")], "ret" => (vr "b")});
    let a_to_b_thunk = ast!({"type" "fn" : "param" => [], "ret" => (, a_to_b.clone() )});

    assoc_n!(
        "fix" =>
        tyf!( { "type" "forall_type" :
            "param" => ["a", "b"],
            "body" => (import [* [forall "param"]] { "type" "fn" :
                "param" => [ { "type" "fn" :
                    "param" => [(, a_to_b_thunk.clone())], "ret" => (, a_to_b.clone())} ],
                "ret" => (, a_to_b.clone()) })},
            // TODO: built-in functions, even though none of them work, shouldn't crash
            ( Function(cl) ) => {
                let new_env = cl.env.set(cl.params[0],
                    // reconstruct the invocation that caused this:
                    Function(Rc::new(::runtime::eval::Closure {
                        body: ast!({"expr" "apply" :
                            "rator" => (vr "fix"),
                            "rand" => [(vr "orig_arg")]}),
                        params: vec![],
                        env: assoc_n!("orig_arg" => Function(cl.clone()),
                                      // TODO: `core_values` does the `map` every time...
                                      "fix" => core_values().find_or_panic(&n("fix")).clone())})));
                eval(&cl.body, new_env).unwrap() // TODO: should be able to return `Result`
            }
        ),
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
        tyf!( {"type" "fn" : "param" => [ {"type" "int" :}], "ret" => (vr "bool") },
              ( Int(a) ) => { val!(b   a == BigInt::from(0))}),
        "equal?" =>
        tyf!( {"type" "fn" : "param" => [ {"type" "int" :}, {"type" "int" :} ],
                             "ret" => (vr "bool")},
              ( Int(a), Int(b) ) => { val!(b a == b)} ),
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
        "false" => TypedValue { ty: ast!((vr "bool")), val: val!(b false)},
        "true" => TypedValue { ty: ast!((vr "bool")), val: val!(b true)}
    )
}

pub fn core_values() -> Assoc<Name, Value> {
    core_typed_values().map(&erase_type)
}

pub fn core_types() -> Assoc<Name, Ty> {
    core_typed_values().map(&erase_value).set(
        n("bool"), ty!(
            {"type" "enum" : "name" => [@"c" "True", "False"], "component" => [@"c" [], []]}))
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

#[test]
fn fixpoint_evaluation() {

    // Note that I'm cheating by leaving off the lambda imports because lambda evaluation
    //  doesn't take advantage of the betas in the first place.
    assert_eq!(eval(
        &ast!( {"expr" "apply" : "rator" =>
        { "expr" "apply" :
            "rator" => (vr "fix"),
            "rand" => [{ "expr" "lambda" :
                 "param" => [ "again" ],
                 "p_t" => [ /* TODO */ (vr "TODO")  ],
                 "body" => { "expr" "lambda" :
                     "param" => [ "n" ],
                     "p_t" => [ { "type" "int" : } ],
                     "body" => { "expr" "match" :
                         "scrutinee" => { "expr" "apply" : "rator" => (vr "zero?"),
                                                           "rand" => [(vr "n")] },
                         "p" => [@"c" {"pat" "enum_pat" : "component" => [], "name" => "True"  },
                                      {"pat" "enum_pat" : "component" => [], "name" => "False" }],
                         "arm" =>
                             [@"c"
                              (import ["p" = "scrutinee"] (vr "one")),
                              (import ["p" = "scrutinee"] { "expr" "apply" :
                                   "rator" => (vr "times"),
                                   "rand" =>
                                       [(vr "n"),
                                        { "expr" "apply" :
                                            "rator" => { "expr" "apply" :
                                                "rator" => (vr "again"), "rand" => []},
                                            "rand" => [{ "expr" "apply" :
                                                 "rator" => (vr "minus"),
                                                 "rand" => [(vr "n"), (vr "one")]}]}]})]}}}]},
        "rand" => [(vr "five")]}),
        core_values()),
        Ok(val!(i 120)));
}
