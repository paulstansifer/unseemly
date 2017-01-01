/*
 * The type theory for Unseemly 
 *  is largely swiped from the "Types and Programming Languages" by Pierce.
 * I've agressively copied the formally-elegant but non-ergonomic theory 
 *  whenever I think that the ergonomic way of doing things is just syntax sugar over it.
 * After all, syntax sugar is the point of Unseemly!
 * 
 * I didn't think that I could survive making a system out of + and × types, though,
 *  so there are `struct`s and `enum`s.
 */
 
use std::rc::Rc;
use parse::{SynEnv, FormPat};
use form::{Form, simple_form};
use parse::FormPat::*;
use ast_walk::WalkRule::*;
use name::*;
use core_forms::ast_to_atom;
use ty::{Ty, synth_type};
use ast::*;

fn type_defn<'t>(form_name: &'t str, p: FormPat<'t>) -> Rc<Form<'t>> {
    Rc::new(Form {
        name: n(form_name),
        grammar: p,
        relative_phase: ::util::assoc::Assoc::new(),
        // How do kinds fit into this? Recall that `eval` must produce a `Value`, so 
        // `synth_type` has to produce a type even though we are "evaluating" to a type
        synth_type: ::form::Positive(LiteralLike),
        eval: ::form::Positive(NotWalked) 
    })
}

pub fn make_core_syn_env_types<'t>() -> SynEnv<'t> {
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
            Ok(ty!({ mu_parts.this_form.clone() ; 
                "param" => (, mu_parts.get_term(&n("param"))),
                "body" => (, try!(without_param.get_res(&n("body"))).0 )}))
         }),
         NotWalked);
         
    
    // Like a variable reference (but `LiteralLike` typing prevents us from doing that)
    let type_by_name = typed_form!("type_by_name", (named "name", aat),
        cust_rc_box!(move |tbn_part| {
            let name = tbn_part.get_term(&n("name"));
            match tbn_part.env.find(&ast_to_atom(&name)) {
                None => // This is fine; e.g. we might be at the `X` in `forall X. List<[X]<`.
                    Ok(ty!({ tbn_part.this_form ; "name" => (, name) })),
                Some(ty) => Ok(ty.clone())
            }
        }),
        NotWalked);

    let forall_type_0 = forall_type.clone();
    
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
                            assoc_n!("arg" => individual__arg_res.0)));
                    }
                    new__tapp_parts.add_anon_repeat(args);
                    
                    Ok(Ty(Node(tapp_parts.this_form, new__tapp_parts)))
                }
                Some(defined_type) => {
                    // This might ought to be done by a specialized `beta`...
                    expect_node!( (defined_type.0 ; forall_type_0.clone())
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
        
    assoc_n!("type" => /*Biased(Box::new(*/forms_to_form_pat![
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
        ]/*), Box::new(VarRef))*/)
} 

#[test]
fn parametric_types() {
    let ident_ty = ty!( { "type" "ident" : });
    let nat_ty = ty!( { "type" "nat" : });
    
    fn tbn(nm: &'static str) -> Ty<'static> {
        ty!( { "type" "type_by_name" : "name" => (, ::ast::Ast::Atom(n(nm))) } )
    }

    let mt_ty_env = ::util::assoc::Assoc::new();    
    let para_ty_env = assoc_n!(
        "unary" => ty!({ "type" "forall_type" :
            "param" => ["t"],
            "body" => { "type" "fn" :
                "param" => [ (, nat_ty.0.clone()) ],
                "ret" => (, tbn("t").0) }}),
        "binary" => ty!({ "type" "forall_type" :
            "param" => ["t", "u"],
            "body" => { "type" "fn" :
                "param" => [ (, tbn("t").0), (, tbn("u").0) ],
                "ret" => (, nat_ty.0.clone()) }}));

    // If `unary` is undefined, `unary <[ ident ]<` can't be simplified.
    assert_eq!(synth_type(
        &ast!( { "type" "type_apply" :
            "type_name" => "unary",
            "arg" => [ (, ident_ty.0.clone()) ]}),
        mt_ty_env.clone()),
        Ok(ty!({ "type" "type_apply" :
            "type_name" => "unary",
            "arg" => [ (, ident_ty.0.clone()) ]})));

    // If `unary` is undefined, `unary <[ [nat -> nat] ]<` can't be simplified.
    assert_eq!(synth_type(
        &ast!( { "type" "type_apply" :
            "type_name" => "unary",
            "arg" => [ { "type" "fn" :
                "param" => [(, nat_ty.0.clone())], "ret" => (, nat_ty.0.clone())} ]}),
        mt_ty_env.clone()),
        Ok(ty!({ "type" "type_apply" :
            "type_name" => "unary",
            "arg" => [ { "type" "fn" :
                "param" => [(, nat_ty.0.clone())], "ret" => (, nat_ty.0.clone())} ]})));
                
    // Expand the definition of `unary`.
    assert_eq!(synth_type(
        &ast!( { "type" "type_apply" :
            "type_name" => "unary",
            "arg" => [ (, ident_ty.0.clone()) ]}),
        para_ty_env),
        Ok(ty!({ "type" "fn" :
            "param" => [(, nat_ty.0)],
            "ret" => (, ident_ty.0.clone())})));
}