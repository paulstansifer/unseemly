use crate::{
    ast::Ast,
    core_forms, eval_unseemly_program_top, expand, grammar,
    name::{n, Name},
    runtime::{core_values, eval, eval::Value},
    ty, type_unseemly_program_top,
    util::assoc::Assoc,
};
use std::cell::RefCell;

// HACK: the non-test code in here is copied from `cli.rs`.

thread_local! {
    pub static ty_env : RefCell<Assoc<Name, Ast>> = RefCell::new(core_values::core_types());
    pub static val_env : RefCell<Assoc<Name, Value>> = RefCell::new(core_values::core_values());
}

fn type_unseemly_program(program: &str) -> Result<Ast, String> {
    let ast = grammar::parse(
        &core_forms::outermost_form(),
        core_forms::outermost__parse_context(),
        program,
    )
    .map_err(|e| e.msg)?;

    ty_env.with(|tys| ty::synth_type(&ast, tys.borrow().clone()).map_err(|e| format!("{}", e)))
}

fn eval_unseemly_program(program: &str) -> Result<Value, String> {
    let ast: Ast = grammar::parse(
        &core_forms::outermost_form(),
        core_forms::outermost__parse_context(),
        program,
    )
    .map_err(|e| e.msg)?;

    let _type = ty_env
        .with(|tys| ty::synth_type(&ast, tys.borrow().clone()).map_err(|e| format!("{}", e)))?;

    let core_ast = expand::expand(&ast).map_err(|_| "error".to_owned())?;

    val_env.with(|vals| eval::eval(&core_ast, vals.borrow().clone()).map_err(|_| "???".to_string()))
}

fn assign_variable(name: &str, expr: &str) -> Result<Value, String> {
    let res = eval_unseemly_program(expr);

    if let Ok(ref v) = res {
        let ty = type_unseemly_program(expr).unwrap();
        ty_env.with(|tys| {
            val_env.with(|vals| {
                let new_tys = tys.borrow().set(n(name), ty);
                let new_vals = vals.borrow().set(n(name), v.clone());
                *tys.borrow_mut() = new_tys;
                *vals.borrow_mut() = new_vals;
            })
        })
    }
    res
}

fn assign_t_var(name: &str, t: &str) -> Result<Ast, String> {
    let ast = grammar::parse(
        &grammar::FormPat::Call(n("Type")),
        core_forms::outermost__parse_context(),
        t,
    )
    .map_err(|e| e.msg)?;

    let res =
        ty_env.with(|tys| ty::synth_type(&ast, tys.borrow().clone()).map_err(|e| format!("{}", e)));

    if let Ok(ref t) = res {
        ty_env.with(|tys| {
            let new_tys = tys.borrow().set(n(name), t.clone());
            *tys.borrow_mut() = new_tys;
        })
    }

    res
}

fn ignore__this_function() {
    // Suppress unused variable warnings for functions only used in tests.
    let _ = eval_unseemly_program_top;
    let _ = type_unseemly_program_top;
}

// Many of these tests should be converted to `u!`-based tests.
// In a lot of cases, the fact htat `u!` doesn't support syntax quotation is an obstacle.
// TODO: cut the knot and bake syntax {,un}quotation support to `u!`.

#[test]
fn end_to_end_int_list_tools() {
    assert_m!(assign_t_var("IntList", "mu_type IntList . { +[Nil]+ +[Cons Int IntList]+ }"), Ok(_));

    assert_m!(assign_t_var("IntListUF", "{ +[Nil]+ +[Cons Int IntList]+ }"), Ok(_));

    assert_m!(
        assign_variable("mt_ilist", "fold +[Nil]+ : { +[Nil]+ +[Cons Int IntList]+ } : IntList"),
        Ok(_)
    );

    assert_m!(
        assign_variable("ilist_3", "fold +[Cons three mt_ilist]+ : IntListUF : IntList"),
        Ok(_)
    );

    assert_m!(
        assign_variable("ilist_23", "fold +[Cons two ilist_3]+ : IntListUF : IntList"),
        Ok(_)
    );

    assert_m!(
        assign_variable("ilist_123", "fold +[Cons one ilist_23]+ : IntListUF : IntList"),
        Ok(_)
    );

    assert_m!(
        assign_variable(
            "sum_int_list",
            "(fix .[again : [-> [IntList -> Int]] .
             .[ lst : IntList .
                 match unfold lst {
                     +[Nil]+ => zero +[Cons hd tl]+ => (plus hd ((again) tl))} ]. ]. )"
        ),
        Ok(_)
    );

    assert_eq!(eval_unseemly_program("(sum_int_list ilist_123)"), Ok(val!(i 6)));

    assert_m!(
        assign_variable(
            "int_list_len",
            "(fix .[again : [-> [IntList -> Int]] .
             .[ lst : IntList .
                 match unfold lst {
                     +[Nil]+ => zero +[Cons hd tl]+ => (plus one ((again) tl))} ]. ].)"
        ),
        Ok(_)
    );

    assert_eq!(eval_unseemly_program("(int_list_len ilist_123)"), Ok(val!(i 3)));
}

#[test]
fn end_to_end_list_tools() {
    assert_m!(
        assign_t_var("List", "forall T . mu_type List . { +[Nil]+ +[Cons T List<T> ]+ }"),
        Ok(_)
    );

    assert_m!(assign_t_var("ListUF", "forall T . { +[Nil]+ +[Cons T List<T> ]+ }"), Ok(_));

    assert_m!(
        assign_variable(
            "mt_list",
            "fold +[Nil]+ : { +[Nil]+ +[Cons Int List<Int> ]+ } : List < Int > "
        ),
        Ok(_)
    );

    assert_m!(
        assign_variable("list_3", "fold +[Cons three mt_list]+ : ListUF<Int> : List<Int>"),
        Ok(_)
    );

    assert_m!(
        assign_variable("list_23", "fold +[Cons two list_3]+ : ListUF<Int> : List<Int>"),
        Ok(_)
    );

    assert_m!(
        assign_variable("list_123", "fold +[Cons one list_23]+ : ListUF<Int> : List<Int>"),
        Ok(_)
    );

    assert_m!(
        assign_variable(
            "list_len",
            "forall S . (fix .[again : [-> [List<S> -> Int]] .
            .[ lst : List<S> .
                match unfold lst {
                    +[Nil]+ => zero
                    +[Cons hd tl]+ => (plus one ((again) tl))} ]. ].)"
        ),
        Ok(_)
    );

    assert_eq!(eval_unseemly_program("(list_len list_123)"), Ok(val!(i 3)));

    assert_m!(
        assign_variable(
            "map",
            "forall T S . (fix  .[again : [-> [List<T>  [T -> S] -> List<S> ]] .
            .[ lst : List<T>   f : [T -> S] .
                match unfold lst {
                    +[Nil]+ => fold +[Nil]+ : ListUF<S> : List<S>
                    +[Cons hd tl]+ =>
                      fold +[Cons (f hd) ((again) tl f)]+ : ListUF<S> : List<S> } ]. ].)"
        ),
        Ok(_)
    );
    // TODO: what should even happen if you have `forall` not on the "outside"?
    // It should probably be an error to have a value typed with an underdetermined type.

    // TODO: it's way too much of a pain to define each different expected result list.
    assert_m!(eval_unseemly_program("(map list_123 .[x : Int . (plus x one)]. )"), Ok(_));

    assert_m!(eval_unseemly_program("(map list_123 .[x : Int . (equal? x two)]. )"), Ok(_));
}

#[test]
fn subtyping_direction() {
    // Let's check to make sure that "supertype" and "subtype" never got mixed up:

    assert_m!(assign_variable("ident", "forall T . .[ a : T . a ]."), Ok(_));

    assert_eq!(eval_unseemly_program("(ident five)"), Ok(val!(i 5)));

    assert_m!(eval_unseemly_program("( .[ a : [Int -> Int] . a]. ident)"), Ok(_));

    assert_m!(eval_unseemly_program("( .[ a : forall T . [T -> T] . a]. .[a : Int . a].)"), Err(_));

    assert_m!(eval_unseemly_program(".[ a : *[]* . a]."), Ok(_));

    assert_m!(
        eval_unseemly_program("( .[ a : *[normal : Int extra : Int]* . a]. *[normal : one]*)"),
        Err(_)
    );

    assert_m!(
        eval_unseemly_program("( .[ a : *[normal : Int]* . a]. *[normal : one extra : five]*)"),
        Ok(_)
    );
}

#[test]
fn end_to_end_quotation_advanced() {
    assert_eq!(
        eval_unseemly_program(
            "(.[five_e : Expr < Int >.
                '[Expr | (plus five ,[five_e],) ]' ].
                '[Expr | five]')"
        ),
        eval_unseemly_program("'[Expr | (plus five five) ]'")
    );

    // Pass the wrong type (not really a test of quotation)
    assert_m!(
        type_unseemly_program_top(
            "(.[five_e : Expr<Int> .
                '[Expr | (plus five ,[five_e],) ]' ].
                '[Expr | true]')"
        ),
        Err(_)
    );

    // Interpolate the wrong type
    assert_m!(
        type_unseemly_program_top(
            "(.[five_e : Expr<Bool> .
                '[Expr | (plus five ,[five_e],) ]' ].
                '[Expr | true]')"
        ),
        Err(_)
    );

    // Interpolate the wrong type (no application needed to find the error)
    assert_m!(
        type_unseemly_program_top(".[five_e : Expr<Bool> . '[Expr | (plus five ,[five_e],) ]' ]."),
        Err(_)
    );

    assert_m!(
        eval_unseemly_program(
            "forall T . .[type : Type<T>   rhs : Expr<T>
                . '[Expr | (.[x : ,[Type<T> | type], . eight].  ,[rhs], )]' ]."
        ),
        Ok(_)
    );

    assert_m!(eval_unseemly_program("'[Pat<Nat> | x]'"), Ok(_));

    // Actually import a pattern of quoted syntax:
    assert_eq!(
        eval_unseemly_program(
            "match '[Expr | (plus one two) ]' {
                 '[Expr<Int> | (plus ,[Expr<Int> | e], two) ]' => e }"
        ),
        eval_unseemly_program("'[Expr| one]'")
    );

    // Thanks to `prefab_type`, we can do implicitly-typed `let`
    //  expanding to explicitly-typed lambda!
    // See `trad_let.unseemly` for details.
    assert_m!(
        assign_variable(
            "let",
            "forall T S . .[binder : Pat<T>
                        type : Type<T>
                        rhs : Expr<T>
                        body : Expr<S> .
             '[ Expr | (.[x : ,[type],
                     . match x { ,[Pat<T> | binder], => ,[body], } ].
                 ,[rhs],)]' ]."
        ),
        Ok(_)
    );

    without_freshening! {
        assert_eq!(
            eval_unseemly_program(
                "(let  '[Pat<Int> | y]'
                       '[Type<Int> | Int]'
                       '[Expr<Int> | eight]'
                       '[Expr<Int> | five]')"),
            eval_unseemly_program("'[Expr<Int> | (.[x : Int . match x {y => five}].  eight)]'"));
    }

    //  // We need tuple literals before we can test this:
    //  assert_m!(assign_variable("let-multi",
    //      "forall T . .[ binder : **[ :::[T >> Ident<T> ]::: ]**
    //                     type : **[ :::[T >> Type<T> ]::: ]**
    //                     rhs : **[ :::[T >> Expr<T> ]::: ]**
    //                     body : Expr<S> .
    //          '[Expr | (.[ ...[, binder , >> ,[Ident | binder],]...
    //                       : ...[, type , >> ,[Type | type], ]... .
    //                    ,[body], ].
    //                      ...[, Expr , | ,[rhs], ]... ) ]'
    //                       "),
    //       Ok(_));

    //  without_freshening! {
    //      assert_eq!(
    //          eval_unseemly_program(
    //              "(let-multi  '[Ident<Int> | y]'
    //                     '[Type<Int> | Int]'
    //                     '[Expr<Int> | eight]'
    //                     '[Expr<Int> | five]')"),
    //          eval_unseemly_program("'[Expr<Int> | (.[x : Int . match x {y => five}].  eight)]'"));
    //  }
}

#[test]
fn simple_end_to_end_eval() {
    assert_eq!(eval_unseemly_program_top("(zero? zero)"), Ok(val!(b true)));

    assert_eq!(eval_unseemly_program_top("(plus one one)"), Ok(val!(i 2)));

    assert_eq!(
        eval_unseemly_program_top("(.[x : Int  y : Int . (plus x y)]. one one)"),
        Ok(val!(i 2))
    );

    assert_eq!(
        eval_unseemly_program_top(
            "((fix .[ again : [ -> [ Int -> Int ]] .
            .[ n : Int .
                match (zero? n) {
                    +[True]+ => one
                    +[False]+ => (times n ((again) (minus n one))) } ]. ].) five)"
        ),
        Ok(val!(i 120))
    );
}

#[test]
fn end_to_end_quotation_basic() {
    assert_m!(eval_unseemly_program_top("'[Expr | .[ x : Int . x ]. ]'"), Ok(_));

    assert_m!(eval_unseemly_program_top("'[Expr | (plus five five) ]'"), Ok(_));

    assert_m!(eval_unseemly_program_top("'[Expr | '[Expr | (plus five five) ]' ]'"), Ok(_));

    //≫ .[s : Expr<Int> . '[Expr | ( ,[Expr | s], '[Expr | ,[Expr | s], ]')]' ].
}

#[test]
fn language_building() {
    assert_eq!(
        eval_unseemly_program_top(
            r"extend_syntax
                DefaultSeparator ::= /((?:\s|#[^\n]*)*)/ ;
            in
                # Now we have comments! (just not after the last token)
            five"
        ),
        Ok(val!(i 5))
    );

    let bound_wrong_prog = "extend_syntax
            Expr ::=also forall T S . '{
                [
                    lit ,{ DefaultToken }, = 'let'
                    [
                        pat := ( ,{ Pat<S> }, )
                        lit ,{ DefaultToken }, = '='
                        value := ( ,{ Expr<S> }, )
                        lit ,{ DefaultToken }, = ';'
                    ] *
                    lit ,{ DefaultToken }, = 'in'
                    body := ( ,{ Expr<T> }, <-- ...[pat = value]... )
                ]
            }' let_macro -> .{
                '[Expr |
                    match ...[,value, >> ,[value], ]...
                        { ...[,pat, >> ,[pat],]... => ,[body], } ]'
            }. ;
        in
        let x = eight ;
            y = times ;
        in (plus x y)";
    let bound_wrong_ast = grammar::parse(
        &core_forms::outermost_form(),
        core_forms::outermost__parse_context(),
        bound_wrong_prog,
    )
    .unwrap();

    assert_m!(
        ty::synth_type(&bound_wrong_ast, crate::runtime::core_values::core_types()),
        ty_err_p!(Mismatch(x, y)) => {
            assert_eq!(x, uty!({Int :}));
            assert_eq!(y, uty!({fn : [{Int :}; {Int :}] {Int :}}));
        }
    );

    let inner_expr_wrong_prog = "extend_syntax
            Expr ::=also forall T S . '{
                [
                    lit ,{ DefaultToken }, = 'let'
                    [
                        pat := ( ,{ Pat<S> }, )
                        lit ,{ DefaultToken }, = '='
                        value := ( ,{ Expr<S> }, )
                        lit ,{ DefaultToken }, = ';'
                    ] *
                    lit ,{ DefaultToken }, = 'in'
                    body := ( ,{ Expr< T > }, <-- ...[pat = value]... )
                ]
            }' let_macro -> .{
                '[Expr |
                    match ...[,value, >> ,[value], ]...
                        { ...[,pat, >> ,[pat],]... => ,[body], } ]'
            }. ;
        in
        let x = eight ;
            y = four ;
        in (plus x times)";
    let inner_expr_wrong_ast = grammar::parse(
        &core_forms::outermost_form(),
        core_forms::outermost__parse_context(),
        inner_expr_wrong_prog,
    )
    .unwrap();

    assert_m!(
        ty::synth_type(&inner_expr_wrong_ast, crate::runtime::core_values::core_types()),
        ty_err_p!(Mismatch(x, times)) => {
            assert_eq!(x, uty!({Int :}));
            assert_eq!(times, uty!({fn : [{Int :}; {Int :}] {Int :}}));
        }
    );

    // TODO: leaving out the `**[ ]**` results in an ICP; it should be a static error.

    let let_macro_prog = "extend_syntax
            Expr ::=also forall T S . '{
                [
                    lit ,{ DefaultToken }, = 'let'
                    [
                        pat := ( ,{ Pat<S> }, )
                        lit ,{ DefaultToken }, = '='
                        value := ( ,{ Expr<S> }, )
                        lit ,{ DefaultToken }, = ';'
                    ] *
                    lit ,{ DefaultToken }, = 'in'
                    body := ( ,{ Expr<T> }, <-- ...[pat = value]... )
                ]
            }' let_macro -> .{
                '[Expr |
                    match **[...[,value, >> ,[value], ]... ]**
                        { **[...[,pat, >> ,[pat],]... ]** => ,[body], } ]'
            }. ;
        in
        let x = eight ;
            y = four ;
        in (plus y (plus x y))";
    assert_eq!(eval_unseemly_program_top(let_macro_prog), Ok(val!(i 16)));
}

#[test]
fn for_loop__macro() {
    // For whatever reason, this program uncovered a bunch of bugs.
    assert_eq!(
        eval_unseemly_program_top(
            r"
        extend_syntax
            Expr ::=also
                forall T S . '{ [
                    lit ,{ DefaultToken }, = 'let'
                    [
                        pat := ( ,{ Pat<S> }, )
                        lit ,{ DefaultToken }, = '='
                        val := ( ,{ Expr<S> }, )
                        lit ,{ DefaultToken }, = ';'
                    ] *
                    lit ,{ DefaultToken }, = 'in'
                    body := ( ,{ Expr<T> }, <-- ...[pat = val]... )
                ] }' let_macro -> .{
                    '[Expr |
                        match **[...[,val, >> ,[val], ]... ]**
                            { **[...[,pat, >> ,[pat],]... ]** => ,[body], } ]'
                }. ;
        in
        extend_syntax
            Expr ::=also forall T . '{ [
                lit ,{ DefaultToken }, = 'for'
                pat := ( ,{ Pat<T> }, )
                lit ,{ DefaultToken }, = 'in'
                seq := ( ,{ Expr<Sequence<T>> }, )
                body := ( ,{ Expr<Unit> }, <-- pat : T )
            ] }' for_loop -> .{
                '[Expr |
                    (foldl ,[seq],
                        **[]**
                        .[unit : Unit  arg : ,[prefab_type T], .
                            let ,[pat], = arg ; in ,[body],
                        ]. )
                ]'
            }. ;
        in
        let foo = seven ; in
        for x in (range one three) (print (anything_to_string x))"
        ),
        Ok(val!(seq))
    );

}