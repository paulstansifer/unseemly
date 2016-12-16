// This virtual machine kills cyber-fascists.

#![allow(dead_code, non_upper_case_globals)]

/*
 * Core forms!
 * 
 * This is the definition of Unseemly, the bizarre boiled-down programming language.
 *
 * Unseemly programs have expressions and types (and probably kinds, too).
 * 
 * The type theory for this is largely swiped from the "Types and Programming Languages" by Pierce.
 * I've agressively copied the formally-elegant but non-ergonomic theory 
 *  whenever I think that the ergonomic way of doing things is just syntax sugar over it.
 * After all, syntax sugar is the point of Unseemly!
 *
 */


use name::*;
use parse::{SynEnv, FormPat};
use parse::FormPat::*;
use form::{Form, simple_form};
use util::assoc::Assoc;
use ast::*;
use std::rc::Rc;
use ty::*;
use runtime::eval::*;
use beta::*;
use ast_walk::WalkRule::*;
use num::bigint::ToBigInt;

fn ast_to_atom<'t>(ast: &Ast<'t>) -> Name<'t> {
    match ast { &Atom(n) => n, _ => { panic!("internal error!") } }
}

macro_rules! cust_rc_box {
    ($contents:expr) => { Custom(Rc::new(Box::new($contents))) }
}

fn type_defn<'t>(form_name: &'t str, p: FormPat<'t>) -> Rc<Form<'t>> {
    Rc::new(Form {
        name: n(form_name),
        grammar: p,
        relative_phase: Assoc::new(),
        // How do kinds fit into this? Recall that `eval` must produce a `Value`, so 
        // `synth_type` has to produce a type even though we are "evaluating" to a type
        synth_type: ::form::Positive(LiteralLike),
        eval: ::form::Positive(NotWalked) 
    })
}

/* Note that both types and terms are represented as Ast<'t> */

/// This is the Unseemly language.
pub fn make_core_syn_env<'t>() -> SynEnv<'t> {
        /* Regarding the value/type/kind hierarchy, Benjamin Pierce generously assures us that 
        "For programming languages ... three levels have proved sufficient." */
    
    /* kinds */
    let _type_kind = simple_form("type", form_pat!((lit "*")));
    let _higher_kind = simple_form("higher", form_pat!(
        (delim "k[", "[", /*]]*/ 
            [ (star (named "param", (call "kind"))), (lit "->"), (named "res", (call "kind"))])));
    
    
    /* types */
    let fn_type =
        type_defn("fn", 
            /* Friggin' Atom bracket matching doesn't ignore strings or comments. */
            form_pat!((delim "[", "[", /*]]*/
                [ (star (named "param", (call "type"))), (lit "->"), 
                  (named "ret", (call "type") ) ])));
                  
    let enum_type = 
        type_defn("enum", form_pat!([(lit "enum"),
            (delim "{", "{", /*}}*/ (star [(named "name", aat), 
                (delim "(", "(", /*))*/ [(star (named "component", (call "type")))])]))]));
                
    let struct_type =
        type_defn("struct", form_pat!(
            [(lit "struct"),
             (delim "{", "{", /*}}*/ (star [(named "component_name", aat), (lit ":"), 
                                            (named "component", (call "type"))]))]));
    
    let forall_type = 
        type_defn("forall_type", form_pat!(
            [(lit "forall_type"), (star (named "param", aat)), (lit "."), 
                // // This isn't part of the grammar from the user's point of view!
                // // We just need the type kind for the RHS of the beta, 
                // //  since the parameters are always plain types.
                // // (but is this even right? Is it an enviornment of types specifically, or 
                // //  whatever-is-one-level-up-from-the-LHS)
                // (named "type_kind_stx", (anyways "*")),
                
                // It seems like there ought to be an import of "param" here,
                //  but the binding has to be done manually. 
                // Maybe there's something we can add to `beta` for this case...
                (delim "forall[", "[", /*]]*/ (named "body", (call "type")))]));
    
    /* This behaves slightly differently than the `mu` from Pierce's book,
     *  because we need to support mutual recursion.
     * In particular, it relies on having a binding for `param` in the environment!
     * The only thing that `mu` actually does is suppress substitution,
     *  to prevent the attempted generation of an infinite type.
     */
    let mu_type = typed_form!("mu_type",
            [(lit "mu_type"), (star (named "param", aat)), (lit "."), 
             (named "body", (call "type"))],
        cust_rc_box!(move |mu_parts| {
            // This probably ought to eventually be a feature of betas...
            let without_param = mu_parts.with_environment(mu_parts.env.unset(
                &ast_to_atom(&mu_parts.get_term(&n("param")))));
                            
            // Like LiteralLike, but with the above environment-mucking
            Ok(ast!({ mu_parts.this_form.clone() ; 
                "param" => (, mu_parts.get_term(&n("param"))),
                "body" => (, try!(without_param.get_res(&n("body"))))}))
         }),
         NotWalked);
         
    
    // Like a variable reference (but `LiteralLike` typing prevents us from doing that)
    let type_by_name = typed_form!("type_by_name", (named "name", aat),
        cust_rc_box!(move |tbn_part| {
            let name = tbn_part.get_term(&n("name"));
            match tbn_part.env.find(&ast_to_atom(&name)) {
                None => // This is fine; e.g. we might be at the `X` in `forall X. List<[X]<`.
                    Ok(ast!({ tbn_part.this_form ; "name" => (, name) })),
                Some(ty) => Ok(ty.clone())
            }
        }),
        NotWalked);

    /* This seems to be necessary to get separate `Rc`s into the closures. */
    let fn_type_0 = fn_type.clone();
    let fn_type_1 = fn_type.clone();
    let enum_type_0 = enum_type.clone();
    let enum_type_1 = enum_type.clone();
    let struct_type_0 = struct_type.clone();
    let struct_type_1 = struct_type.clone();
    let forall_type_0 = forall_type.clone();
    let mu_type_0 = mu_type.clone();
    let mu_type_1 = mu_type.clone();
    
   /* [Type theory alert!]
    * Pierce's notion of type application is an expression, not a type; 
    *  you just take an expression whose type is a `forall`, and then give it some arguments.
    * Instead, we will just make the type system unify `forall` types with more specific types.
    * But sometimes the user wants to write a more specific type, and they use this.
    *
    * This is, at the type level, like function application.
    * We restrict the LHS to being a name, because that's "normal". Should we?
    */    
    let type_apply = typed_form!("type_apply",
        // The technical term for `<[...]<` is "fish X-ray"
        [(lit "tbn"), (named "type_name", aat), 
         (delim "<[", "[", /*]]*/ (star [(named "arg", (call "type")), (lit ",")]))],
        cust_rc_box!(move |tapp_parts| {
            let arg_res = try!(tapp_parts.get_rep_res(&n("arg")));
            match tapp_parts.env.find(&ast_to_atom(&tapp_parts.get_term(&n("type_name")))) {
                None => { // e.g. `X<[int, Y]<` underneath `mu X. ...`
                    // Rebuild a type_by_name, but evaulate its arguments
                    // This kind of this is necessary because 
                    //  we wish to avoid aliasing problems at the type level.
                    // In System F, this is avoided by capture-avoiding substitution.
                    let mut new__tapp_parts = ::util::mbe::EnvMBE::new_from_leaves(
                        assoc_n!("type_name" => tapp_parts.get_term(&n("type_name"))));

                    let mut args = vec![];
                    for individual__arg_res in arg_res {
                        args.push(::util::mbe::EnvMBE::new_from_leaves(
                            assoc_n!("arg" => individual__arg_res)));
                    }
                    new__tapp_parts.add_anon_repeat(args);
                    
                    Ok(Node(tapp_parts.this_form, new__tapp_parts))
                }
                Some(defined_type) => {
                    // This might ought to be done by a specialized `beta`...
                    expect_node!( (*defined_type ; forall_type_0.clone())
                        forall_type__parts;
                        {
                            let params = forall_type__parts.get_rep_leaf_or_panic(&n("param"));
                            if params.len() != arg_res.len() {
                                panic!("Kind error: wrong number of arguments");
                            }
                            let mut new__ty_env = tapp_parts.env.clone();
                            for (name, actual_type) in params.iter().zip(arg_res) {
                                new__ty_env 
                                    = new__ty_env.set(ast_to_atom(name), actual_type);
                            }
                            
                            synth_type(&forall_type__parts.get_leaf_or_panic(&n("body")), 
                                       new__ty_env)
                        })
                }
            }
        }),
        NotWalked);
        
    // Unseemly expressions
    let main_expr_forms = forms_to_form_pat![
        typed_form!("lambda",
            /* syntax */ /* TODO: add comma separators to the syntax! */
            (delim ".[", "[", /*]]*/ [
                               (star [(named "param", aat), (lit ":"), 
                                      (named "p_t", (call "type"))]), (lit "."),
                (named "body",
                    (import [* ["param" : "p_t"]], (call "expr")))]),
            /* type */
            cust_rc_box!( move | part_types | {
                let lambda_type : Ast<'t> = 
                    ast!({ fn_type_1.clone() ;
                         "param" => [* part_types =>("param") part_types :
                                       (, try!(part_types.get_res(&n("p_t"))))],
                         "ret" => (, try!(part_types.get_res(&n("body"))))});
                Ok(lambda_type)}),
            /* evaluation */
            cust_rc_box!( move | part_values | {
                Ok(Function(Rc::new(Closure {
                    body: part_values.get_term(&n("body")),
                    params: 
                    part_values.get_rep_term(&n("param")).iter().map(ast_to_atom).collect(),
                    env: part_values.env
                })))
            })),
        
        typed_form!("apply", /* function application*/
            [(named "rator", (call "expr")), 
             (star (named "rand", (call "expr")))],
            cust_rc_box!(move | part_types |
                expect_node!( (try!(part_types.get_res(&n("rator"))) ; 
                               fn_type_0)
                    env;
                    {
                        for (input, expected) in env.get_rep_leaf_or_panic(&n("param")).iter().zip(
                            &try!(part_types.get_rep_res(&n("rand")))
                        ) {
                            // TODO: proper type comparison
                            if input != &expected { return Err(()); }
                        }
                    
                        Ok(env.get_leaf_or_panic(&n("ret")).clone())
                    }
                )),
            cust_rc_box!( move | part_values | {
                match try!(part_values.get_res(&n("rator"))) {
                    Function(clos) => {
                        // Evaluate arguments into a fake LazyWalkReses,
                        //  making a dummy form that has the actual arguments and the body together
                        let mut params = vec![];
                        for (p, t) in clos.params.iter().zip(
                                part_values.get_rep_term(&n("rand"))) {
                            let new_arg_parts = ::util::mbe::EnvMBE::new_from_leaves(
                                assoc_n!("param" => Atom(*p), "p_t" => t));
                            params.push(new_arg_parts);
                            //new_env_parts.add_leaf(*p, t);
                        }
                        
                        // All these colons suggest that maybe there's 
                        // some other interface that should exist.
                        
                        let new_env_parts = ::util::mbe::EnvMBE::new_from_anon_repeat(params);
                        
                        ::ast_walk::walk::<::runtime::eval::Evaluate>(&clos.body,
                            &::ast_walk::LazyWalkReses::new(
                                clos.env.clone(), new_env_parts, part_values.this_form))
                    },
                    BuiltInFunction(::runtime::eval::BIF(f)) => {
                        Ok(f(try!(part_values.get_rep_res(&n("rand")))))
                    }
                    other => { 
                        panic!("Type soundness bug: attempted to invoke {:?} 
                        as if it were a function", other)
                    }
                }
            })),
        typed_form!("match",
            [(lit "match"), (named "scrutinee", (call "expr")),
             (delim "{", "{", 
                 (star [(named "p", (call "pat")), (lit "=>"),
                        (named "arm", (import ["p" = "scrutinee"], (call "expr")))]))],
            /* Typesynth: */
            cust_rc_box!(move | part_types | {
                let mut res = None;
                for arm_part_types in part_types.march_parts(&vec![n("arm")]) {
                    let arm_res = try!(arm_part_types.get_res(&n("arm")));

                    match res {
                        None => { res = Some(arm_res) }
                        Some(ref old_res) => {
                            if old_res != &arm_res {
                                panic!("Type error: arm mismatch: {:?} vs. {:?}", old_res, arm_res)
                            }
                        }
                    }
                }
                
                Ok(res.expect("Type error: no arms!"))                
            }),
            /* Evaluation: */
            cust_rc_box!( move | part_values | {
                for arm_values in part_values.march_all(&vec![n("arm")]) {
                    match arm_values.get_res(&n("arm")) {
                        Ok(res) => { return Ok(res); }
                        Err(()) => { /* try the next one */ }
                    }
                }
                panic!("No arms matched! This ought to be a type error, but isn't.");
            })
        ),
        /* Note that we inconveniently require the user to specify the type.
           "real" languages infer the type from the (required-to-be-unique)
           component name. */
        typed_form!("enum_expr",
            [(named "name", aat), 
             (delim "(", "(", /*))*/ [(star (named "component", (call "pat")))]),
             (lit ":"), (named "t", (call "type"))],
            /* Typesynth: */
            cust_rc_box!( move | part_types | {
                let res = try!(part_types.get_res(&n("t")));
                expect_node!( (res ; enum_type_1)
                    enum_type_parts; 
                    {
                        for enum_type_part in enum_type_parts.march_all(&vec![n("name")]) {
                            if &part_types.get_term(&n("name")) 
                                    != enum_type_part.get_leaf_or_panic(&n("name")) {
                                continue; // not the right arm
                            }
                            
                            let component_types : Vec<Ast<'t>> = 
                                enum_type_part.get_rep_leaf_or_panic(&n("component"))
                                    .iter().map(|a| (*a).clone()).collect();
                                    
                            for (t, expected_t) in try!(part_types.get_rep_res(&n("component")))
                                .iter().zip(component_types) {
                                if t != &expected_t {
                                    panic!("Expected type: {:?}, got: {:?}", expected_t, t)
                                }
                            }
                            
                            return Ok(res.clone());
                        }
                        panic!("{:?} is not a valid arm for the type {:?}", 
                            part_types.get_term(&n("name")), res)
                    }        
                )            
            }),
            /* Evaluate: */
            cust_rc_box!( move | part_values | {
                Ok(Enum(ast_to_atom(&part_values.get_term(&n("name"))),
                    try!(part_values.get_rep_res(&n("component")))))
            })),
        typed_form!("struct_expr",
            (delim "{", "{", /*}}*/ 
                (star [(named "component_name", aat), (lit ":"), 
                       (named "component", (call "expr"))])),
            cust_rc_box!( move | part_types | {
                Ok(ast!({ struct_type_1.clone() ;
                    "component_name" => (@"c" ,seq part_types.get_rep_term(&n("component_name"))),
                    "component" => (@"c" ,seq try!(part_types.get_rep_res(&n("component"))))
                }))
            }),
            cust_rc_box!( move | part_values | {
                let mut res = Assoc::new();
                
                for component_parts in part_values.march_parts(&vec![n("component")]) {
                    res = res.set(ast_to_atom(&component_parts.get_term(&n("component_name"))),
                                  try!(component_parts.get_res(&n("component"))));
                }
                
                Ok(Struct(res))
            })),

        /* e.g.
         * let_type
         *   pair = mu lhs rhs. {l: lhs, r: rhs}
         *   point = pair <[int, int]<
         * in ...
         */
        typed_form!("let_type",
            [(lit "let_type"),
             (named "type_kind_stx", (anyways "*")),
             (import [* ["type_name" = "type_def"]], // put `pair` and `point` in type env
                 (star [(named "type_name", aat), (lit "="), (named "type_def", (call "type"))])),
             (lit "in"),
             (named "body", (import [* ["type_name" = "type_def"]], (call "expr")))],
            Body(n("body")),
            Body(n("body"))),
            
        /* e.g. where List = ∀ X. μ List. enum { Nil(), Cons(X, List<[X]<) }
         * '[x : List <[X]<  . match (unfold x) ... ]'
         * (unfold is needed because `match` wants an `enum`, not a `μ`)
         * Exposes the inside of a μ type by performing one level of substitution.
         */
        typed_form!("unfold",
            [(lit "unfold"), (named "body", (call "expr"))],
            cust_rc_box!( move |unfold_parts| {
                // TODO: this "evaluates" types twice; once in `get_res` and once in `synth_type`
                // It shouldn't be necessary, and it's probably quadratic.
                // Maybe this points to a weakness in the LiteralLike approach to traversing types?
                let mu_typed = try!(unfold_parts.get_res(&n("body")));

                expect_node!( (mu_typed.clone() ; mu_type_0) 
                    mu_parts;
                    {
                        synth_type(
                            mu_parts.get_leaf_or_panic(&n("body")), 
                            unfold_parts.env.set(
                                ast_to_atom(mu_parts.get_leaf_or_panic(&n("param"))),
                                // Maybe this ought to be a lookup of `param` in `ty_env`?
                                // Is there ever a difference?
                                mu_typed))
                    })
            }),
            Body(n("body"))),
        
        /* e.g. where List = ∀ X. μ List. enum { Nil(), Cons(X, List<[X]<) }
         * '[x : List <[X]<  ...]' fold Nil() : List<[X]<
         */
        typed_form!("fold",
            [(lit "fold"), (named "body", (call "expr")), (lit ":"), (named "t", (call "type"))],
            cust_rc_box!( move |fold_parts| {
                let goal_type = try!(fold_parts.get_res(&n("t")));
                // TODO: I can't figure out how to pull this out into a function 
                //  to invoke both here and above, since `mu_type_0` needs cloning...
                let folded_goal = expect_node!( (goal_type.clone() ; mu_type_1) 
                    mu_parts;
                    {
                        try!(synth_type(
                            mu_parts.get_leaf_or_panic(&n("body")), 
                            fold_parts.env.set(
                                ast_to_atom(mu_parts.get_leaf_or_panic(&n("param"))),
                                // Maybe this ought to be a lookup of `param` in `ty_env`?
                                // Is there ever a difference?
                                goal_type.clone())))
                    });

                // TODO: do proper type comparison
                if folded_goal != try!(fold_parts.get_res(&n("body"))) {
                    panic!("Type error: {:?} ≠ {:?}\n", folded_goal, try!(fold_parts.get_res(&n("body"))));
                }
                Ok(goal_type)
            }),
            Body(n("body")))
            
            /*
        // We have isorecursive types: the user has to explicitly `unfold_type`
        //   to "get past" type_by_name.
        // In the environment from the above `let_type`, if `p` has type `pair <[int, int]<`:  
        //  .[x : {l: int, r: int} .  ??? ]. p
        // ...is ill-typed, but
        //  .[x : {l: int, r: int} .  ??? ]. (unfold_type p)
        // ...is well-typed.
        typed_form!("unfold_type",
            [(delim "(", "(", /*))*/ [ (lit "unfold_type"), (named "body", (call "type"))])],
            cust_rc_box!( move | unfld_ty_parts | {
                // We are being applied to a type like
                //  `pair <[int, int]<`
                // expect, in our environment, to find something like
                //  `pair <[lhs, rhs]< = {l: lhs, r: rhs}`
                // 
                
                expect_node!( (try!(unfld_ty_parts.get_res(&n("body"))) ; type_by_name_0)
                    _env; {
                        // e.g. `pair <[lhs, rhs]< `
                        /*
                        let mut res : Ast<'t> = unfld_ty_parts.env.find_or_panic(
                            &ast_to_atom(env.get_leaf_or_panic(&n("type_name")))).clone();
                        for(p, t) in unfld_ty_parts.get_term(&n("arg"))*/
                        //Ok(res)
                        panic!("");
                    }
               
           )
           }
           ),
           Body(n("body")) 
    
    
        )
*/

        // The first use for syntax quotes will be in macro definitions.
        // But we will someday need them as expressions.                    
    ];
    
    let main_pat_forms = forms_to_form_pat![
        negative_typed_form!("enum_pat",
            [(named "name", aat), 
             (delim "(", "(", /*))*/ [(star (named "component", (call "pat")))])],
            /* (Negatively) Typecheck: */
            cust_rc_box!( move | part_types |
                expect_node!( (*part_types.context_elt() ; enum_type_0)
                    enum_type_parts;
                    {
                        for enum_type_part in enum_type_parts.march_all(&vec![n("name")]) {
                        
                            if &part_types.get_term(&n("name")) 
                                    != enum_type_part.get_leaf_or_panic(&n("name")) {
                                continue; // not the right arm
                            }
                        
                            let component_types : Vec<Ast<'t>> = 
                                enum_type_part.get_rep_leaf_or_panic(&n("component"))
                                    .iter().map(|a| (*a).clone()).collect();
                           
                            let mut res = Assoc::new();
                            for sub_res in &try!(part_types
                                    .get_rep_res_with(&n("component"), component_types)) {
                                res = res.set_assoc(sub_res);
                            }
                        
                            return Ok(res);
                        }
                        panic!("Type error: enum branch not found");
                }
            )),
            /* (Negatively) Evaluate: */
            cust_rc_box!( move | part_values | {
                match part_values.context_elt() /* : Value<'t> */ {
                    &Enum(ref name, ref elts) => {
                        // "Try another branch"
                        if name != &ast_to_atom(&part_values.get_term(&n("name"))) {
                            return Err(()); 
                        }
                        
                        let mut res = Assoc::new();
                        for sub_res in &try!(part_values.get_rep_res_with(&n("component"), 
                                                                          elts.clone())) {
                            res = res.set_assoc(sub_res);
                        }
                        
                        Ok(res)
                    }
                    _ => panic!("Type ICE: non-enum")
                }            
            })),
        negative_typed_form!("struct_pat",
            [(delim "{", "{", /*}}*/ 
                 (star [(named "component_name", aat), (lit ":"), 
                        (named "component", (call "pat"))]))],
            /* (Negatively) typesynth: */
            cust_rc_box!( move | part_types | 
                expect_node!( (*part_types.context_elt() ; struct_type_0)
                    struct_type_parts;
                    {
                        let mut res = Assoc::new();
                        for component_ctx in part_types.march_parts(&vec![n("component")]) {
                            let mut component_found = false;
                            for struct_type_part 
                                    in struct_type_parts.march_all(&vec![n("component")]) {
                                if &component_ctx.get_term(&n("component_name"))
                                    != struct_type_part.get_leaf_or_panic(&n("component_name")) {
                                    continue;
                                }
                                component_found = true;
                                res = res.set_assoc(
                                    &try!(component_ctx
                                        .with_context(
                                            struct_type_part.get_leaf_or_panic(&n("component"))
                                                .clone())
                                        .get_res(&n("component"))));
                                break;
                            }
                            if !component_found {
                                panic!("Type error: {:?} isn't a field of {:?}", 
                                    component_ctx.get_term(&n("component_name")),
                                    part_types.context_elt());
                            }
                        }
                        Ok(res)
                    })),
            cust_rc_box!( move | part_values | {
                match part_values.context_elt() {
                    &Struct(ref contents) => {
                        let mut res = Assoc::new();
                        
                        for component_ctx in part_values.march_parts(&vec![n("component")]) {
                            res = res.set_assoc(
                                &try!(component_ctx
                                    .with_context(contents.find_or_panic(
                                        &ast_to_atom(
                                            &component_ctx.get_term(&n("component_name"))))
                                            .clone())
                                    .get_res(&n("component"))));
                        }
                        
                        Ok(res)
                    }
                    _ => panic!("Type ICE: non-struct")
                }
            }))];

    assoc_n!(
        "pat" => Biased(Box::new(main_pat_forms), Box::new(VarRef)),
        "expr" => Biased(Box::new(main_expr_forms), Box::new(VarRef)),
        "type" => Biased(Box::new(forms_to_form_pat![
            fn_type.clone(),
            type_defn("ident", form_pat!((lit "ident"))),
            type_defn("int", form_pat!((lit "int"))),
            type_defn("nat", form_pat!((lit "nat"))),
            type_defn("float", form_pat!((lit "float"))),
            type_defn("bool", form_pat!((lit "bool"))),
            enum_type.clone(),
            struct_type.clone(),
            forall_type.clone(),
            mu_type.clone(),
            type_apply.clone(),
            type_by_name.clone()
            ]), Box::new(VarRef))
    )
}






/**
 * Mostly for testing purposes, this looks up forms by name.
 * In the "real world", programmers look up forms by syntax, using a parser. 
 */
pub fn find_form<'t>(se: &SynEnv<'t>, nt: &str, form_name: &str)
         -> Rc<Form<'t>> {             

    fn find_form_rec<'t>(f: &FormPat<'t>, form_name: &str) -> Option<Rc<Form<'t>>> {
        match f {
            &Scope(ref f) => {
                if f.name.is(form_name) {
                    Some(f.clone())
                } else {
                    None
                }
            }
            &Alt(ref vf) => {
                for f in vf {
                    let res = find_form_rec(f, form_name);
                    if res.is_some() { return res; }
                }
                None
            }
            &Biased(ref lhs, ref rhs) => {
                let l_res = find_form_rec(lhs, form_name);
                if l_res.is_some() { l_res } else { find_form_rec(rhs, form_name) }
            }
            _ => { None }
        }        
    }
    let pat = se.find_or_panic(&n(nt));
    
    find_form_rec(pat, form_name)
        .expect(format!("{:?} not found in {:?}", form_name, pat).as_str())
}

thread_local! {
    pub static core_forms: SynEnv<'static> = make_core_syn_env();
}

pub fn find_core_form(nt: &str, name: &str) -> Rc<Form<'static>> {
    core_forms.with(|cf| find_form(cf, nt, name))
}



/* TODO: this test is broken by identifiers-as-a-valid-type. Why? All other possible parses
         should override identifiers.
#[test]
fn form_grammar() {
    let cse = make_core_syn_env();
    assert_eq!(parse(&form_pat!((call "type")),
                     cse.clone(),
                     &tokens!([""; "ident" "->" "ident"])),
               Ok(ast!({ find_form(&cse, "type", "fn"); 
                   ["ret" => {find_form(&cse, "type", "ident") ; []},
                    "param" => [{find_form(&cse, "type", "ident") ; []}]]})));
    
}*/


#[test]
fn form_expect_node() {
    let ast = ast!({ find_core_form("expr", "apply"); 
        ["rand" => [(vr "f")], "rator" => (vr "x")]});
    let _ : Result<(), ()> = expect_node!( 
        ( ast ; find_core_form("expr", "apply")) env; //expect_f = "rand", expect_x = "rator";
        {
            assert_eq!(env.get_rep_leaf_or_panic(&n("rand")), vec![&ast!((vr "f"))]);
            assert_eq!(env.get_leaf_or_panic(&n("rator")), &ast!((vr "x")));
            Ok(())
        });
}

#[test]
fn form_type() {
    let simple_ty_env = assoc_n!(
        "x" => ast!({ find_core_form("type", "int") ; }),
        "b" => ast!({ find_core_form("type", "bool") ; }));
    
    let lam = find_core_form("expr", "lambda");
    let fun = find_core_form("type", "fn");

    
    assert_eq!(synth_type(&ast!( (vr "x") ), simple_ty_env.clone()),
               Ok(ast!( { find_core_form("type", "int") ; })));
    
    assert_eq!(synth_type(&ast!( 
        { lam.clone() ;
            "param" => [@"p" "y"], 
            "p_t" => [@"p" { find_core_form("type", "nat") ; }],
            "body" => (import [* [ "param" : "p_t" ]] (vr "x"))}),
        simple_ty_env.clone()),
        Ok(ast!({ fun.clone() ; 
            "param" => [{ find_core_form("type", "nat") ; }], 
            "ret" => { find_core_form("type", "int") ; }})));
}

#[test]
fn form_eval() {
    let cse = make_core_syn_env();
    
    let simple_env = assoc_n!("x" => Int(18.to_bigint().unwrap()),
                              "w" => Int(99.to_bigint().unwrap()),
                              "b" => Bool(false));    
    
    let lam = find_form(&cse, "expr", "lambda");
    let app = find_form(&cse, "expr", "apply");

    
    assert_eq!(eval(&ast!((vr "x")), simple_env.clone()),
               Ok(Int(18.to_bigint().unwrap())));
    
    // (λy.w) x
    assert_eq!(eval(&ast!( 
        { app.clone() ;
            [
             "rator" => 
                { lam.clone() ;
                    "param" => [@"p" "y"], 
                    "p_t" => [@"p" "integer"],
                    "body" => (import [* [ "param" : "p_t" ]]  (vr "w"))},
             "rand" => [(vr "x")]
            ]}),
        simple_env.clone()),
        Ok(Int(99.to_bigint().unwrap())));
    
    // (λy.y) x
    assert_eq!(eval(&ast!(
        { app.clone() ;
            [
             "rator" => 
                { lam.clone() ;
                    "param" => [@"p" "y"], 
                    "p_t" => [@"p" "integer"],
                    "body" => (import [* [ "param" : "p_t" ]]  (vr "y"))},
             "rand" => [(vr "x")]
            ]}),
        simple_env.clone()),
        Ok(Int(18.to_bigint().unwrap())));
    
}

#[test]
fn alg_type() {
    let cse = make_core_syn_env();
    
    let mt_ty_env = Assoc::new();
    let simple_ty_env = assoc_n!(
        "x" => ast!("integer"), "b" => ast!("bool"), "f" => ast!("float"));

    /* Typecheck enum pattern */
    let enum_p = find_form(&cse, "pat", "enum_pat");
    let enum_t = find_form(&cse, "type", "enum");
    
    let my_enum = ast!({ enum_t.clone() ;
        "name" => [@"c" "Adams", "Jefferson", "Burr"],
        "component" => [@"c" ["integer"], ["integer", "bool"], ["float", "float"]]
    });
        
    assert_eq!(neg_synth_type(&ast!(
        { enum_p.clone() ; 
            "name" => "Jefferson",
            "component" => [(vr "abc"), (vr "def")]
        }),
        mt_ty_env.set(negative_ret_val, my_enum.clone())),
        Ok(Assoc::new().set(n("abc"), ast!("integer")).set(n("def"), ast!("bool"))));
    
    /* Typecheck enum expression */
    let enum_e = find_form(&cse, "expr", "enum_expr");
    
    assert_eq!(synth_type(&ast!(
        { enum_e.clone() ;
            "name" => "Jefferson",
            "component" => [(vr "x"), (vr "b")],
            "t" => (, my_enum.clone())
        }),
        simple_ty_env.clone()),
        Ok(my_enum));
        
        
    /* Typecheck struct pattern */    
    
    let struct_p = find_form(&cse, "pat", "struct_pat");
    let struct_t = find_form(&cse, "type", "struct");
    
    let my_struct = ast!({ struct_t.clone() ;
        "component_name" => [@"c" "x", "y"],
        "component" => [@"c" "integer", "float"]
    });
    
    assert_eq!(neg_synth_type(&ast!(
            { struct_p.clone() ;
                "component_name" => [@"c" "y", "x"],
                "component" => [@"c" (vr "yy"), (vr "xx")]
            }),
            mt_ty_env.set(negative_ret_val, my_struct.clone())),
        Ok(assoc_n!("yy" => ast!("float"), "xx" => ast!("integer"))));
        
    /* Typecheck struct expression */ 
    let struct_e = find_form(&cse, "expr", "struct_expr");
    
    // TODO: currently {x: integer, y: float} ≠ {y: float, x: integer}
    // Implement proper type equality!
    assert_eq!(synth_type(&ast!(
            { struct_e.clone() ;
                "component_name" => [@"c" "x", "y"],
                "component" => [@"c" (vr "x"), (vr "f")]
            }),
            simple_ty_env.clone()),
        Ok(my_struct));
    
    /* Simple match... */
    
    let mtch = find_form(&cse, "expr", "match");
    
    assert_eq!(synth_type(&ast!({ mtch.clone() ;
                "scrutinee" => (vr "f"),
                "p" => [@"arm" (vr "my_new_name"), (vr "unreachable")],
                "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "my_new_name")), 
                                 (import ["p" = "scrutinee"] (vr "f"))]
            }),
            simple_ty_env.clone()),
        Ok(ast!("float")));
    
        
    // TODO: use this test when type errors aren't panics
        /*
    assert_eq!(synth_type(&ast!({ mtch.clone() ;
                "scrutinee" => (vr "b"),
                "p" => [@"arm" (vr "my_new_name"), (vr "unreachable")],
                "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "my_new_name")), 
                                 (import ["p" = "scrutinee"] (vr "f"))]
            }),
            simple_ty_env.clone()),
        Err(())); */

    
}

#[test]
fn alg_eval() {
    let cse = make_core_syn_env();
    
    let mt_env = Assoc::new();
    let simple_env = assoc_n!("x" => val!(i 18), "w" => val!(i 99), "b" => val!(b false));
    
    /* Evaluate enum pattern */
    let enum_p = find_form(&cse, "pat", "enum_pat");
    
    assert_eq!(neg_eval(&ast!(
        { enum_p.clone() ; 
            "name" => "choice1",
            "component" => [(vr "abc"), (vr "def")]
        }),
        mt_env.set(negative_ret_val, val!(enum "choice1", (i 9006), (b true)))),
        Ok(assoc_n!("abc" => val!(i 9006), "def" => val!(b true))));
            
    assert_eq!(neg_eval(&ast!(
        { enum_p.clone() ; 
            "name" => "choice1",
            "component" => [(vr "abc"), (vr "def")]
        }),
        mt_env.set(negative_ret_val, val!(enum "choice0", (i 12321)))),
        Err(()));

    /* Evaluate enum expression */

    let enum_t = find_form(&cse, "type", "enum");
    
    let my_enum = ast!({ enum_t.clone() ;
        "name" => [@"c" "choice0", "choice1", "choice2"],
        "component" => [@"c" ["integer"], ["integer", "bool"], ["float", "float"]]
    });

    let enum_e = find_form(&cse, "expr", "enum_expr");
    
    assert_eq!(eval(&ast!(
        { enum_e.clone() ;
            "name" => "choice1",
            "component" => [(vr "x"), (vr "b")],
            "t" => (, my_enum.clone())
        }),
        simple_env.clone()),
        Ok(val!(enum "choice1", (i 18), (b false))));
        
    /* Evaluate struct pattern */
    
    let struct_p = find_form(&cse, "pat", "struct_pat");
    assert_eq!(neg_eval(&ast!(
        { struct_p.clone() ;
            "component_name" => [@"c" "x", "y"],
            "component" => [@"c" (vr "xx"), (vr "yy")]
        }),
        mt_env.set(negative_ret_val,
                   Struct(assoc_n!("x" => val!(i 0), "y" => val!(b true))))),
        Ok(assoc_n!("xx" => val!(i 0), "yy" => val!(b true))));
    
    /* Evaluate match */
    
    let mtch = find_form(&cse, "expr", "match");
    
    assert_eq!(eval(&ast!({ mtch.clone() ;
                "scrutinee" => (vr "x"),
                "p" => [@"arm" (vr "my_new_name"), (vr "unreachable")],
                "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "my_new_name")), 
                                 (import ["p" = "scrutinee"] (vr "x"))]
        }),
        simple_env.clone()),
        Ok(val!(i 18)));
    
}
#[test]
fn parametric_types() {
    let ident_ty = ast!( { find_core_form("type", "ident") ; });
    let nat_ty = ast!( { find_core_form("type", "nat") ; });
    
    fn tbn(nm: &'static str) -> Ast<'static> {
        ast!( { find_core_form("type", "type_by_name") ; "name" => (, ::ast::Ast::Atom(n(nm))) } )
    }

    let mt_ty_env = Assoc::new();    
    let para_ty_env = assoc_n!(
        "unary" => ast!({ find_core_form("type", "forall_type") ;
            "param" => ["t"],
            "body" => { find_core_form("type", "fn") ;
                "param" => [ (, nat_ty.clone()) ],
                "ret" => (, tbn("t")) }}),
        "binary" => ast!({ find_core_form("type", "forall_type") ;
            "param" => ["t", "u"],
            "body" => { find_core_form("type", "fn") ;
                "param" => [ (, tbn("t")), (, tbn("u")) ],
                "ret" => (, nat_ty.clone()) }}));

    // If `unary` is undefined, `unary <[ ident ]<` can't be simplified.
    assert_eq!(synth_type(
        &ast!( { find_core_form("type", "type_apply") ;
            "type_name" => "unary",
            "arg" => [ (, ident_ty.clone()) ]}),
        mt_ty_env.clone()),
        Ok(ast!({ find_core_form("type", "type_apply") ;
            "type_name" => "unary",
            "arg" => [ (, ident_ty.clone()) ]})));

    // If `unary` is undefined, `unary <[ [nat -> nat] ]<` can't be simplified.
    assert_eq!(synth_type(
        &ast!( { find_core_form("type", "type_apply") ;
            "type_name" => "unary",
            "arg" => [ { find_core_form("type", "fn") ; 
                "param" => [(, nat_ty.clone())], "ret" => (, nat_ty.clone())} ]}),
        mt_ty_env.clone()),
        Ok(ast!({ find_core_form("type", "type_apply") ;
            "type_name" => "unary",
            "arg" => [ { find_core_form("type", "fn") ; 
                "param" => [(, nat_ty.clone())], "ret" => (, nat_ty.clone())} ]})));
                
    // Expand the definition of `unary`.
    assert_eq!(synth_type(
        &ast!( { find_core_form("type", "type_apply") ;
            "type_name" => "unary",
            "arg" => [ (, ident_ty.clone()) ]}),
        para_ty_env),
        Ok(ast!({ find_core_form("type", "fn") ;
            "param" => [(, nat_ty)],
            "ret" => (, ident_ty.clone())})));
    
}

#[test]
fn recursive_types() {
    fn tbn(nm: &'static str) -> Ast<'static> {
        ast!( { find_core_form("type", "type_by_name") ; "name" => (, ::ast::Ast::Atom(n(nm))) } )
    }
    
    let int_list_ty = ast!( { find_core_form("type", "mu_type") ; 
        "param" => "int_list",
        "body" => { find_core_form("type", "enum") ; 
            "name" => [@"c" "Nil", "Cons"],
            "component" => [@"c" [], ["integer", (, tbn("int_list"))]]}});
            
    let ty_env = assoc_n!(
        "int_list" => int_list_ty.clone(),  // this is a type definition...
        "il_direct" => int_list_ty.clone()  // ...and this is a value with a type
        // TODO: ... distinguish between these in the environment! Is the difference ... kind?

        // We should never have `tbn`s in the environment unless "protected" by a μ.
        // TODO: enforce that:
        //"il_named" => tbn("int_list")
    );
    
    // folding an unfolded thing should give us back the same thing
    assert_eq!(synth_type(
        &ast!( { find_core_form("expr", "fold") ;
            "body" => { find_core_form("expr", "unfold") ; 
                "body" => (vr "il_direct") },
            "t" => (, int_list_ty.clone())}),
        ty_env.clone()),
        Ok(int_list_ty.clone()));
    
    // Unfold a type and then match it
    assert_eq!(synth_type(
        &ast!( { find_core_form("expr", "match") ; 
            "scrutinee" => { find_core_form("expr", "unfold") ; "body" => (vr "il_direct") },
            "p" => [@"arm" { find_core_form("pat", "enum_pat") ;
                "name" => "Cons",
                "component" => [(vr "car"), (vr "cdr")],
                "t" => (, tbn("int_list"))            
            }],
            "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "car"))]
        }),
        ty_env.clone()),
        Ok(ast!("integer"))
    );
    /*
    // When type errors aren't panics, uncomment this (test that missing an unfold fails)
    assert_eq!(synth_type(
        &ast!( { find_core_form("expr", "match") ; 
            "scrutinee" =>  (vr "il_direct") ,
            "p" => [@"arm" { find_core_form("pat", "enum_pat") ;
                "name" => "Cons",
                "component" => [(vr "car"), (vr "cdr")],
                "t" => (, tbn("int_list"))            
            }],
            "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "car"))]
        }),
        ty_env.clone()),
        Err(...)
    );*/
}