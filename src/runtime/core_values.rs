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
pub fn string_operations() -> Assoc<Name, TypedValue> {
    assoc_n!(
    "string_to_sequence" => tyf! {
        {"Type" "fn" :
            "param" => [{"Type" "String" :}],
            "ret" => { "Type" "type_apply" :
                "type_rator" => (vr "Sequence"), "arg" => [{"Type" "Int" :}]}
        },
        (Text(s)) =>
            Sequence(s.chars().map(|c: char| Rc::new(Int(BigInt::from(c as u32)))).collect())
    },
    "ident_to_string" => tyf! {
        {"Type" "fn" :
            "param" => [{"Type" "Ident" :}],
            "ret" => {"Type" "String" :}
        },
        (AbstractSyntax(Ast::Atom(name))) => Text(name.orig_sp())},
    "concat" => tyf! {
        {"Type" "fn" :
            "param" => [{"Type" "String" :}, {"Type" "String" :}],
            "ret" => {"Type" "String" :}
        },
        (Text(lhs), Text(rhs)) => Text(format!("{}{}", lhs, rhs))},
    "replace" => tyf! {
        {"Type" "fn" :
            "param" => [{"Type" "String" :}, {"Type" "String" :}, {"Type" "String" :}],
            "ret" => {"Type" "String" :}
        },
        (Text(body), Text(old), Text(new)) => Text(body.replace(&old, &new))},
    "join" => tyf! {
        {"Type" "fn" :
            "param" => [{"Type" "type_apply" : "type_rator" => (vr "Sequence"),
                                               "arg" => [{"Type" "String" :}]},
                        {"Type" "String" :}],
            "ret" => {"Type" "String" :}
        },
        (Sequence(seq), Text(joiner)) => {
            let mut buf = String::new();
            let mut first = true;
            for elt in seq {
                if !first {
                    buf.push_str(&joiner);
                }
                first = false;
                if let Text(ref str_elt) = *elt {
                    buf.push_str(str_elt);
                }
            }
            Text(buf)
        }},
    "read_file" => tyf! {
        {"Type" "fn" :
            "param" => [{"Type" "String" :}],
            "ret" => {"Type" "String" :}
        },
        (Text(filename)) => {
            let mut contents = String::new();

            use std::io::Read;
            std::fs::File::open(std::path::Path::new(&filename))
                .expect("Error opening file")
                .read_to_string(&mut contents)
                .expect("Error reading file");
            Text(contents)
        }},
    "write_file" => tyf! {
        {"Type" "fn" :
            "param" => [{"Type" "String" :}, {"Type" "String" :}],
            "ret" => (vr "Unit")
        },
        (Text(filename), Text(contents)) => {
            std::fs::write(filename, contents).expect("Error writing file");
            Sequence(vec![])
        }},
    "os_command" => tyf! {
        {"Type" "fn" :
            "param" => [
                {"Type" "String" :},
                {"Type" "type_apply" :
                    "type_rator" => (vr "Sequence"),
                    "arg" => [{"Type" "String" :}]
            }],
            "ret" => {"Type" "String" :}
        },
        (Text(command_name), Sequence(args)) => {
            Text(std::str::from_utf8(&std::process::Command::new(&command_name)
                .args(args.iter().map(|arg| match &**arg { Text(str_arg) => str_arg, _ => icp!()}))
                .output()
                .expect("process failure")
                .stdout).unwrap().to_string())
        }
    })
}
pub fn sequence_operations() -> Assoc<Name, TypedValue> {
    assoc_n!(
    "range" => tyf!( {"Type" "fn" :
        "param" => [{"Type" "Int" :}, {"Type" "Int" :}],
        "ret" => {"Type" "type_apply" :
            "type_rator" => (vr "Sequence"),
            "arg" => [{"Type" "Int" :}]}},
        (Int(start), Int(end)) => Sequence((start.to_i32().unwrap()..end.to_i32().unwrap()).map(
            |i| Rc::new(Int(BigInt::from(i)))).collect())
    ),
    "empty" => TypedValue {
        ty: ast!({"Type" "forall_type" :
            "param" => ["T"],
            "body" => (import [* [forall "param"]] { "Type" "type_apply" :
                "type_rator" => (vr "Sequence"), "arg" => [(vr "T")]})}),
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
                    |elt| Rc::new(apply__function_value(&f, vec![(*elt).clone()]))).collect())
            }),
    "foldl" =>
        tyf!( { "Type" "forall_type" :
            "param" => ["T", "U"],
            "body" => (import [* [forall "param"]] { "Type" "fn" :
                "param" => [
                    { "Type" "type_apply" :
                        "type_rator" => (vr "Sequence"),
                        "arg" => [(vr "T")]},
                    (vr "U"),
                    { "Type" "fn" : "param" => [(vr "U"), (vr "T")], "ret" => (vr "U") }
                    ],
                "ret" => (vr "U") })},
            ( Sequence(seq), init, f) => {
                seq.into_iter().fold(init, |running, elt| {
                    apply__function_value(&f, vec![running, (*elt).clone()])
                })
            })
    )
}
pub fn cell_operations() -> Assoc<Name, TypedValue> {
    assoc_n!(
        "new_cell" =>
        tyf!( { "Type" "forall_type" :
            "param" => ["T"],
            "body" => (import [* [forall "param"]] { "Type" "fn" :
                "param" => [(vr "T")],
                "ret" =>
                    { "Type" "type_apply" : "type_rator" => (vr "Cell"), "arg" => [(vr "T")]}})},
            ( val ) => {
                Cell(Rc::new(std::cell::RefCell::new(val)))
            }
        ),
        "assign" =>
        tyf!( { "Type" "forall_type" :
            "param" => ["T"],
            "body" => (import [* [forall "param"]] { "Type" "fn" :
                "param" => [
                    { "Type" "type_apply" :
                        "type_rator" => (vr "Cell"),
                        "arg" => [(vr "T")]},
                    (vr "T")
                    ],
                "ret" => (vr "Unit")})},
            ( Cell(cell), val ) => {
                cell.replace(val);
                Sequence(vec![])
            }
        ),
        "value" =>
        tyf!( { "Type" "forall_type" :
            "param" => ["T"],
            "body" => (import [* [forall "param"]] { "Type" "fn" :
                "param" => [
                    { "Type" "type_apply" :
                        "type_rator" => (vr "Cell"),
                        "arg" => [(vr "T")]}
                    ],
                "ret" => (vr "T")})},
            ( Cell(cell) ) => {
                (*cell.borrow()).clone()
            }
        )
    )
}

thread_local! {
    pub static static_core_values: Assoc<Name, TypedValue> = make_core_typed_values();
}

pub fn core_typed_values() -> Assoc<Name, TypedValue> { static_core_values.with(|cv| cv.clone()) }

fn make_core_typed_values() -> Assoc<Name, TypedValue> {
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
        // From a value, produces an expression that evalutes to it.
        // Not quite the same as Racket prefab structures.
        "prefab" =>
        tyf!( { "Type" "forall_type" :
            "param" => ["T"],
            "body" => (import [* [forall "param"]] {"Type" "fn" :
                "param" => [(vr "T")],
                "ret" => {"Type" "type_apply" :
                    "type_rator" => (vr "Expr"),
                    "arg" => [(vr "T")]}})},
            ( val ) => {
                AbstractSyntax(Ast::Node(typed_form!("prefab_internal",
                    (impossible), // no syntax
                    cust_rc_box!(move |_| Ok(ast!(
                        // Cheat: has the universal type, but we know it's safe because <mumble>.
                        {"Type" "forall_type" :
                            "param" => ["T"],
                            "body" => (import [* [forall "param"]] (vr "T"))})) ),
                    cust_rc_box!(move |_| Ok(val.clone()) )
                ), crate::util::mbe::EnvMBE::new(), crate::beta::ExportBeta::Nothing))
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
    .set_assoc(&string_operations())
    .set_assoc(&cell_operations())
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
            ast!({"Type" "enum" : "name" => [@"c" "True", "False"], "component" => [@"c" [], []]}))
        .set(
            n("Unit"),
            ast!({"Type" "tuple" : "component" => []}))
        // These need to be in the environment, not just atomic types
        //  because we sometimes look them up internally in the compiler
        //   in the environment,
        //  not just as programmers, looking them up by syntax, where this whole thing is a wash.
        .set(n("Pat"), get__primitive_type(n("Pat")))
        .set(n("Type"), get__primitive_type(n("Type")))
        .set(n("Expr"), get__primitive_type(n("Expr")))
        .set(n("Sequence"), get__primitive_type(n("Sequence")))
        .set(n("Cell"), get__primitive_type(n("Cell")))
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
fn type_sequence_operations() {
    let mut prelude = core_types();
    use crate::ty::synth_type;

    assert_eq!(synth_type(&u!({apply : len [empty]}), prelude.clone()), Ok(uty!({Int :})));

    assert_eq!(
        synth_type(&u!({apply : push [{apply : push [empty ; one]} ; two]}), prelude.clone()),
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

    assert_eq!(
        synth_type(&u!({apply : foldl [one_two ; zero ; plus ]}), prelude.clone()),
        Ok(uty!({Int :}))
    );
}

#[test]
fn eval_sequence_operations() {
    let mut prelude = core_values();

    assert_eq!(eval(&u!({apply : len [empty]}), prelude.clone()), Ok(val!(i 0)));

    assert_eq!(
        eval(&u!({apply : push [{apply : push [empty ; one]} ; two]}), prelude.clone()),
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

    assert_eq!(eval(&u!({apply : foldl [one_two ; zero ; plus ]}), prelude.clone()), Ok(val!(i 3)));
}

#[test]
fn eval_string_operations() {
    let mut prelude = core_values();

    prelude = prelude.set(n("first"), val!(s "Frederick"));
    prelude = prelude.set(n("last"), val!(s "Douglass"));

    assert_eq!(
        eval(&u!({apply : concat [first; last]}), prelude.clone()),
        Ok(val!(s "FrederickDouglass"))
    );

    prelude = prelude.set(n("names"), val!(seq (s "Frederick") (s "Douglass")));
    prelude = prelude.set(n("space"), val!(s " "));

    assert_eq!(
        eval(&u!({apply : join [names; space]}), prelude.clone()),
        Ok(val!(s "Frederick Douglass"))
    );
}

#[test]
fn eval_cell_operations() {
    let prelude = core_values().set(n("c"), val!(cell (i 5)));

    assert_eq!(
        eval(
            &u!(
            {block :
                [(~ {apply : assign [c ; {apply : plus [one ; {apply : value [c]}]}]})]
                {apply : value [c]}
            }),
            prelude.clone()
        ),
        Ok(val!(i 6))
    );
}
