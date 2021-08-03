use crate::{
    ast::Ast,
    core_type_forms::get__primitive_type,
    name::*,
    runtime::eval::{
        apply__function_value, eval,
        Value::{self, *},
        BIF,
    },
    util::assoc::Assoc,
};
use std::rc::Rc;

use num::{BigInt, ToPrimitive};

#[derive(Debug, Clone, PartialEq)]
pub struct TypedValue {
    pub ty: Ast,
    pub val: Value,
}

pub fn erase_type(tv: &TypedValue) -> Value { tv.val.clone() }
pub fn erase_value(tv: &TypedValue) -> Ast { tv.ty.clone() }

pub fn sequence_operations() -> Assoc<Name, TypedValue> {
    assoc_n!(
        "no_integers" => TypedValue {
            ty: ast!({ "Type" "type_apply" :
                    "type_rator" => (vr "Sequence"), "arg" => [{"Type" "Int" :}]}),
            val: val!(seq)},
        "index" =>
            tyf!( { "Type" "forall_type" :
                "param" => ["T"],
                "body" => (import [* [forall "param"]] { "Type" "fn" :
                    "param" => [
                        { "Type" "type_apply" :
                            "type_rator" => (vr "Sequence"),
                            "arg" => [(vr "T")]},
                        { "Type" "Int" : }
                        ],
                    "ret" => (vr "T")})},
                ( Sequence(seq), Int(idx)) => (*seq[idx.to_usize().unwrap()]).clone()),
        "len" =>
            tyf!( { "Type" "forall_type" :
                "param" => ["T"],
                "body" => (import [* [forall "param"]] { "Type" "fn" :
                    "param" => [
                        { "Type" "type_apply" :
                            "type_rator" => (vr "Sequence"),
                            "arg" => [(vr "T")]}
                        ],
                    "ret" => { "Type" "Int" : }})},
                ( Sequence(seq) ) => val!(i seq.len())),
        "push" =>
            tyf!( { "Type" "forall_type" :
            "param" => ["T"],
            "body" => (import [* [forall "param"]] { "Type" "fn" :
                "param" => [
                    { "Type" "type_apply" :
                        "type_rator" => (vr "Sequence"),
                        "arg" => [(vr "T")]},
                    (vr "T")
                    ],
                "ret" => { "Type" "type_apply" :
                    "type_rator" => (vr "Sequence"),
                    "arg" => [(vr "T")]}})},
            ( Sequence(seq), elt) => {
                let mut result = seq.clone(); result.push(Rc::new(elt)); Sequence(result)}),
        "map" =>
            tyf!( { "Type" "forall_type" :
                "param" => ["T", "U"],
                "body" => (import [* [forall "param"]] { "Type" "fn" :
                    "param" => [
                        { "Type" "type_apply" :
                            "type_rator" => (vr "Sequence"),
                            "arg" => [(vr "T")]},
                        { "Type" "fn" : "param" => [(vr "T")], "ret" => (vr "U") }
                        ],
                    "ret" =>
                        { "Type" "type_apply" :
                            "type_rator" => (vr "Sequence"),
                            "arg" => [(vr "U")]} })},
                ( Sequence(seq), f) => {
                    Sequence(seq.into_iter().map(
                        |elt| Rc::new(apply__function_value(&f, vec![elt]))).collect())
                })
    )
}

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
                    Function(Rc::new(crate::runtime::eval::Closure {
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
             ( Int(a), Int(b) ) => Int( a + b ) ),
        "minus" =>
        tf!([( "Int", "Int" ) -> "Int"],
             ( Int(a), Int(b) ) => Int( a - b ) ),
        "times" =>
        tf!([( "Int", "Int" ) -> "Int"],
             ( Int(a), Int(b) ) => Int( a * b )),
        "zero?" =>
        tyf!( {"Type" "fn" : "param" => [ {"Type" "Int" :}], "ret" => (vr "Bool") },
              ( Int(a) ) => val!(b   a == BigInt::from(0))),
        "equal?" =>
        tyf!( {"Type" "fn" : "param" => [ {"Type" "Int" :}, {"Type" "Int" :} ],
                             "ret" => (vr "Bool")},
              ( Int(a), Int(b) ) => val!(b a == b) ),
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
    .set_assoc(&sequence_operations())
}

pub fn core_values() -> Assoc<Name, Value> { core_typed_values().map(&erase_type) }

// Helper for building an environment by reifying a bunch of Rust types
macro_rules! reified_ty_env {
    ( $($t:ty),* ) => {
        Assoc::new() $( .set(<$t>::ty_name(), <$t>::ty()))*
    };
}

pub fn core_types() -> Assoc<Name, Ast> {
    use crate::runtime::reify::{Irr, Reifiable};
    core_typed_values()
        .map(&erase_value)
        .set(
            n("Bool"),
            ast!({"Type" "enum" : "name" => [@"c" "True", "False"], "component" => [@"c" [], []]}),
        )
        // These need to be in the environment, not just atomic types
        //  because we sometimes look them up internally in the compiler
        //   in the environment,
        //  not just as programmers, looking them up by syntax, where this whole thing is a wash.
        .set(n("Pat"), get__primitive_type(n("Pat")))
        .set(n("Type"), get__primitive_type(n("Type")))
        .set(n("Expr"), get__primitive_type(n("Expr")))
        .set(n("Sequence"), get__primitive_type(n("Sequence")))
        .set_assoc(&reified_ty_env!(
            Option<Irr>, u8, usize,
            crate::util::assoc::Assoc<Irr, Irr>,
            crate::util::mbe::EnvMBE<Irr>,
            Name, crate::ast::Ast, crate::beta::Beta, crate::beta::ExportBeta,
            crate::grammar::FormPat, crate::grammar::SyntaxExtension, crate::grammar::Scanner,
            crate::form::Form, crate::form::EitherPN<Irr, Irr>, crate::ast_walk::WalkRule<Irr>,
            crate::runtime::eval::QQuote, crate::runtime::eval::QQuoteDestr,
            crate::runtime::eval::Eval, crate::runtime::eval::Destructure,
            crate::ty::SynthTy, crate::ty::UnpackTy,
            crate::ty_compare::Canonicalize, crate::ty_compare::Subtype
            ))
}

pub fn get_core_envs() -> crate::earley::CodeEnvs {
    (
        crate::ast_walk::LazyWalkReses::new_wrapper(core_types()),
        crate::ast_walk::LazyWalkReses::new_wrapper(core_values()),
    )
}

#[test]
fn basic_core_value_evaluation() {
    use crate::core_forms::find_core_form;

    let cte = core_typed_values();
    let ce = cte.map(&erase_type);

    assert_eq!(
        eval(
            &ast!({ find_core_form( "Expr", "apply") ;
                "rator" => (vr "plus"),
                "rand" => [ (vr "one"), (vr "one") ]
            }),
            ce
        ),
        Ok(Int(BigInt::from(2)))
    );
}

#[test]
fn fixpoint_evaluation() {
    assert_eq!(
        eval(
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
            core_values()
        ),
        Ok(val!(i 120))
    );
}

#[test]
fn type_sequence_primitives() {
    let mut prelude = core_types();
    use crate::ty::synth_type;

    assert_eq!(synth_type(&u!({apply : len [no_integers]}), prelude.clone()), Ok(uty!({Int :})));

    assert_eq!(
        synth_type(&u!({apply : push [{apply : push [no_integers ; one]} ; two]}), prelude.clone()),
        synth_type(&uty!({type_apply : Sequence [{Int :}]}), prelude.clone())
    );

    prelude = prelude.set(
        n("one_two"),
        synth_type(&uty!({type_apply : Sequence [{Int :}]}), prelude.clone()).unwrap(),
    );

    assert_eq!(
        synth_type(&u!({apply : index [one_two ; one]}), prelude.clone()),
        Ok(uty!({Int :}))
    );

    assert_eq!(
        synth_type(
            &u!({apply : map [one_two ; (, Ast::VariableReference(n("zero?"))) ]}),
            prelude.clone()
        ),
        synth_type(&uty!({type_apply : Sequence [Bool]}), prelude.clone())
    );
}

#[test]
fn eval_sequence_primitives() {
    let mut prelude = core_values();

    assert_eq!(eval(&u!({apply : len [no_integers]}), prelude.clone()), Ok(val!(i 0)));

    assert_eq!(
        eval(&u!({apply : push [{apply : push [no_integers ; one]} ; two]}), prelude.clone()),
        Ok(val!(seq (i 1) (i 2)))
    );

    prelude = prelude.set(n("one_two"), val!(seq (i 1) (i 2)));

    assert_eq!(eval(&u!({apply : index [one_two ; one]}), prelude.clone()), Ok(val!(i 2)));

    assert_eq!(
        eval(
            &u!({apply : map [one_two ; (, Ast::VariableReference(n("zero?"))) ]}),
            prelude.clone()
        ),
        Ok(val!(seq (b false) (b false)))
    );
}
