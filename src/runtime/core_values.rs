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
        "fix" =>
        tyf!( { "Type" "forall_type" :
            "param" => ["F"], // has to be a function, but we don't know its arity
            "body" => (import [* [forall "param"]] { "Type" "fn" :
                "param" => [ { "Type" "fn" :
                    "param" => [{"Type" "fn" : "param" => [], "ret" => (vr "F") }],
                    "ret" => (vr "F")} ],
                "ret" => (vr "F") })},
            // TODO: built-in functions, even though none of them make sense here, shouldn't crash
            ( Function(cl) ) => {
                let new_env = cl.env.set(cl.params[0],
                    // reconstruct the invocation that caused this:
                    Function(Rc::new(::runtime::eval::Closure {
                        body: ast!({"Expr" "apply" :
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
        tf!([( "Int", "Int" ) -> "Int"],
             ( Int(a), Int(b) ) => { Int( a.clone() + b ) }),
        "minus" =>
        tf!([( "Int", "Int" ) -> "Int"],
             ( Int(a), Int(b) ) => { Int( a.clone() - b ) }),
        "times" =>
        tf!([( "Int", "Int" ) -> "Int"],
             ( Int(a), Int(b) ) => { Int( a.clone() * b ) }),
        "zero?" =>
        tyf!( {"Type" "fn" : "param" => [ {"Type" "Int" :}], "ret" => (vr "Bool") },
              ( Int(a) ) => { val!(b   a == BigInt::from(0))}),
        "equal?" =>
        tyf!( {"Type" "fn" : "param" => [ {"Type" "Int" :}, {"Type" "Int" :} ],
                             "ret" => (vr "Bool")},
              ( Int(a), Int(b) ) => { val!(b a == b)} ),
        "zero" => tf!( "Int", val!(i 0) ),
        "one" => tf!( "Int", val!(i 1) ),
        "two" => tf!( "Int", val!(i 2) ),
        "three" => tf!( "Int", val!(i 3) ),
        "four" => tf!( "Int", val!(i 4) ),
        "five" => tf!( "Int", val!(i 5) ),
        "six" => tf!( "Int", val!(i 6) ),
        "seven" => tf!( "Int", val!(i 7) ),
        "eight" => tf!( "Int", val!(i 8) ),
        "nine" => tf!( "Int", val!(i 9) ),
        "ten" => tf!( "Int", val!(i 10) ),
        "false" => TypedValue { ty: ast!((vr "Bool")), val: val!(b false)},
        "true" => TypedValue { ty: ast!((vr "Bool")), val: val!(b true)}
    )
}

pub fn core_values() -> Assoc<Name, Value> {
    core_typed_values().map(&erase_type)
}

pub fn core_types() -> Assoc<Name, Ty> {
    use ::core_type_forms::get__abstract_parametric_type;
    core_typed_values().map(&erase_value)
        .set(n("Bool"), ty!(
            {"Type" "enum" : "name" => [@"c" "True", "False"], "component" => [@"c" [], []]}))
        // These need to be in the environment, not just atomic types
        //  because we sometimes look them up internally in the compiler
        //   in the environment,
        //  not just as programmers, looking them up by syntax, where this whole thing is a wash.
        .set(n("Pat"), ty!({get__abstract_parametric_type() ; "name" => "Pat" }))
        .set(n("Type"), ty!({get__abstract_parametric_type() ; "name" => "Type" }))
        .set(n("Expr"), ty!({get__abstract_parametric_type() ; "name" => "Expr" }))
}


#[test]
fn basic_core_value_evaluation() {
    use core_forms::find_core_form;

    let cte = core_typed_values();
    let ce = cte.map(&erase_type);

    assert_eq!(eval(
        &ast!({ find_core_form( "Expr", "apply") ;
            "rator" => (vr "plus"),
            "rand" => [ (vr "one"), (vr "one") ]
        }),
        ce),
        Ok(Int(BigInt::from(2))));
}

#[test]
fn fixpoint_evaluation() {
    assert_eq!(eval(
        &ast!( {"Expr" "apply" : "rator" =>
        { "Expr" "apply" :
            "rator" => (vr "fix"),
            "rand" => [{ "Expr" "lambda" :
                 "param" => [@"p" "again" ],
                 "p_t" => [@"p" /* TODO */ (vr "TODO")  ],
                 "body" => (import [* ["param" : "p_t"]]
                 { "Expr" "lambda" :
                     "param" => [@"p" "n" ],
                     "p_t" => [@"p" { "Type" "Int" : } ],
                     "body" => (import [* ["param" : "p_t"]]
                     { "Expr" "match" :
                         "scrutinee" => { "Expr" "apply" : "rator" => (vr "zero?"),
                                                           "rand" => [(vr "n")] },
                         "p" => [@"c" {"Pat" "enum_pat" : "component" => [], "name" => "True"  },
                                      {"Pat" "enum_pat" : "component" => [], "name" => "False" }],
                         "arm" =>
                             [@"c"
                              (import ["p" = "scrutinee"] (vr "one")),
                              (import ["p" = "scrutinee"] { "Expr" "apply" :
                                   "rator" => (vr "times"),
                                   "rand" =>
                                       [(vr "n"),
                                        { "Expr" "apply" :
                                            "rator" => { "Expr" "apply" :
                                                "rator" => (vr "again"), "rand" => []},
                                            "rand" => [{ "Expr" "apply" :
                                                 "rator" => (vr "minus"),
                                                 "rand" => [(vr "n"), (vr "one")]}]}]})]})})}]},
        "rand" => [(vr "five")]}),
        core_values()),
        Ok(val!(i 120)));
}
