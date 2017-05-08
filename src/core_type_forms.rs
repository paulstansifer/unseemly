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
 
 /*
There are two similar things we should distinguish!
(1) syntax for types, as written by the user in an `Ast`
(2) types themselves, the result of type synthesis, often stored in `Ty`
     (which is just a thin wrapper around `Ast`).

These things are almost identical, 
 which is why postive synth_type is usually implemented with `LiteralLike`.
 
We should also distinguish
(3) ___, (normally also called "types"). The ___ of an expression is a type, 
     and the ___ of a type is a kind.


It is at this point that I am reminded of a passage from GEB:

 Now in set theory, which deals with abstractions that we don't use all the time, a 
 stratification like the theory of types seems acceptable, even if a little strange-but when it 
 comes to language, an all-pervading part of life, such stratification appears absurd. We 
 don't think of ourselves as jumping up and down a hierarchy of languages when we speak 
 about various things. A rather matter-of-fact sentence such as, "In this book, I criticize 
 the theory of types" would be doubly forbidden in the system we are discussing. Firstly, it 
 mentions "this book", which should only be mentionable in a metabook-and secondly, it mentions
 me-a person whom I should not be allowed to speak of at all! This example points out how silly
 the theory of types seems, when you import it into a familiar context. The remedy it adopts for
 paradoxes-total banishment of self-reference in any form-is a real case of overkill, branding
 many perfectly good constructions as meaningless. The adjective "meaningless", by the way,
 would have to apply to all discussions of the theory of linguistic types (such as that of this
 very paragraph) for they clearly could not occur on any of the levels-neither object language, 
 nor metalanguage, nor metametalanguage, etc. So the very act of discussing the theory 
 would be the most blatant possible violation of it!
 
   — Douglas Hofstadter, Godel, Escher, Bach: and Eternal Golden Braid

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

/*
 NOT SURE IF THIS IS A HACK ALERT
 
 Type synth on expressions/patterns is a positive/negative walk with `Elt`=`Ty` which 
  emulates normal typechecking.
 Type synth on types is a positive (mostly `LiteralLike`) walk that turns type syntax into types.
 ...but there's also a negative type synth on types, used to determine if the type in question
  can specialize down to the `context_elt`.
  
 It feels funny, but "are these two types compatible?" is a question we ask during type synthesis,
  and the negative side of type syntax is the right place for it.
 But it still feels like a hack. 
 In particular, I feel like this comment is bascially incomprehensible
 */


//TODO: I think we need to extend `Form` with `synth_kind`...
fn type_defn(form_name: &str, p: FormPat) -> Rc<Form> {
    Rc::new(Form {
        name: n(form_name),
        grammar: Rc::new(p),
        relative_phase: ::util::assoc::Assoc::new(),
        synth_type: ::form::Both(LiteralLike, LiteralLike),
        quasiquote: ::form::Both(LiteralLike, LiteralLike),
        eval: ::form::Positive(NotWalked) 
    })
}

/* Let me write down an example subtyping hierarchy, to stop myself from getting confused.
    ⊤ (any type/dynamic type/"dunno")
   ╱              |                      ╲
 Num          ∀X.∀Y.(X→Y)              Nat→Int
  |           ╱         ╲              ╱     ╲
 Int     ∀Y.(Bool→Y)  ∀X.(X→Bool)  Int→Int  Nat→Nat
  |           ╲         ╱              ╲     ╱
 Nat           Bool→Bool              Int→Nat
   ╲               |                     ╱
    ⊥ (uninhabited type/panic/"can't happen")

*/


pub fn make_core_syn_env_types() -> SynEnv {
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
                (delim "forall[", "[", /*]]*/ 
                    (named "body", (import [forall "param"], (call "type"))))]));
    
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
                "body" => (, try!(without_param.get_res(&n("body"))).concrete() )}))
         }),
         NotWalked);
    
    // This only makes sense inside a concrete syntax type or during typechecking.
    // For example, the type of the `let` macro is (where `dotdotdot_type` is `...[]...`):
    // ∀ ...{T}... . ∀ S . 
    //    '[let ...[ ,[ var ⇑ v ], = ,[ expr<[T]< ], ]... 
    //            in ,[ expr<[S]< ↓ ...{v = T}...], ]' 
    //        -> expr<[S]<
    // TODO: add named repeats. Add type-level numbers!
    let dotdotdot_type = type_defn("dotdotdot", 
        form_pat!((delim "...[", "[", /*]]*/ (named "body", (call "type")))));
    
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
                            assoc_n!("arg" => individual__arg_res.concrete())));
                    }
                    new__tapp_parts.add_anon_repeat(args, None);
                    
                    Ok(Ty::new(Node(tapp_parts.this_form, new__tapp_parts)))
                }
                Some(defined_type) => {
                    // This might ought to be done by a specialized `beta`...
                    expect_ty_node!( (defined_type ; forall_type_0.clone())
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
        
    assoc_n!("type" => Rc::new(Biased(Rc::new(forms_to_form_pat![
        fn_type.clone(),
        type_defn("ident", form_pat!((lit "ident"))),
        type_defn("int", form_pat!((lit "int"))),
        type_defn("nat", form_pat!((lit "nat"))),
        type_defn("float", form_pat!((lit "float"))),
        type_defn("bool", form_pat!((lit "bool"))),
        enum_type.clone(),
        struct_type.clone(),
        forall_type.clone(),
        dotdotdot_type.clone(),
        mu_type.clone(),
        type_apply.clone()
        ]), Rc::new(form_pat!((scope type_by_name.clone()))))))
} 

#[test]
fn parametric_types() {
    let ident_ty = ty!( { "type" "ident" : });
    let nat_ty = ty!( { "type" "nat" : });
    
    fn tbn(nm: &'static str) -> Ty {
        ty!( { "type" "type_by_name" : "name" => (, ::ast::Ast::Atom(n(nm))) } )
    }

    let mt_ty_env = ::util::assoc::Assoc::new();    
    let para_ty_env = assoc_n!(
        "unary" => ty!({ "type" "forall_type" :
            "param" => ["t"],
            "body" => { "type" "fn" :
                "param" => [ (, nat_ty.concrete()) ],
                "ret" => (, tbn("t").concrete() ) }}),
        "binary" => ty!({ "type" "forall_type" :
            "param" => ["t", "u"],
            "body" => { "type" "fn" :
                "param" => [ (, tbn("t").concrete() ), (, tbn("u").concrete() ) ],
                "ret" => (, nat_ty.concrete()) }}));

    // If `unary` is undefined, `unary <[ ident ]<` can't be simplified.
    assert_eq!(synth_type(
        &ast!( { "type" "type_apply" :
            "type_name" => "unary",
            "arg" => [ (, ident_ty.concrete()) ]}),
        mt_ty_env.clone()),
        Ok(ty!({ "type" "type_apply" :
            "type_name" => "unary",
            "arg" => [ (, ident_ty.concrete()) ]})));

    // If `unary` is undefined, `unary <[ [nat -> nat] ]<` can't be simplified.
    assert_eq!(synth_type(
        &ast!( { "type" "type_apply" :
            "type_name" => "unary",
            "arg" => [ { "type" "fn" :
                "param" => [(, nat_ty.concrete())], "ret" => (, nat_ty.concrete())} ]}),
        mt_ty_env.clone()),
        Ok(ty!({ "type" "type_apply" :
            "type_name" => "unary",
            "arg" => [ { "type" "fn" :
                "param" => [(, nat_ty.concrete())], "ret" => (, nat_ty.concrete())} ]})));
                
    // Expand the definition of `unary`.
    assert_eq!(synth_type(
        &ast!( { "type" "type_apply" :
            "type_name" => "unary",
            "arg" => [ (, ident_ty.concrete()) ]}),
        para_ty_env),
        Ok(ty!({ "type" "fn" :
            "param" => [(, nat_ty.concrete() )],
            "ret" => (, ident_ty.concrete())})));
}