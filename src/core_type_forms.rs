// The type theory for Unseemly
//  is largely swiped from the "Types and Programming Languages" by Pierce.
// I've agressively copied the formally-elegant but non-ergonomic theory
//  whenever I think that the ergonomic way of doing things is just syntax sugar over it.
// After all, syntax sugar is the point of Unseemly!
//
// However, I expect that the core types of a typed macro language will are
//  part of the user interface (for example, they'd appear in generated module documentation).
// Therefore, I used `enum` and `struct` instead of × and +.

// There are two similar things we should distinguish!
// (1) syntax for types, as written by the user in an `Ast`
// (2) types themselves, the result of type synthesis, often stored in `Ty`
//      (which is just a thin wrapper around `Ast`).
//
// These things are almost identical,
//  which is why postive synth_type is usually implemented with `LiteralLike`.
// Performing `SynthTy` translates from (1) to (2). Mainly, it resolves type variable references.
//
// We should also distinguish
// (3) ___, (normally also called "types"). The ___ of an expression is a type,
//      and the ___ of a type is a kind.
//
//
// It is at this point that I am reminded of a passage:
//
// Now in set theory, which deals with abstractions that we don't use all the time, a
// stratification like the theory of types seems acceptable, even if a little strange-but when it
// comes to language, an all-pervading part of life, such stratification appears absurd. We
// don't think of ourselves as jumping up and down a hierarchy of languages when we speak
// about various things. A rather matter-of-fact sentence such as, "In this book, I criticize
// the theory of types" would be doubly forbidden in the system we are discussing. Firstly, it
// mentions "this book", which should only be mentionable in a metabook-and secondly, it mentions
// me-a person whom I should not be allowed to speak of at all! This example points out how silly
// the theory of types seems, when you import it into a familiar context. The remedy it adopts for
// paradoxes-total banishment of self-reference in any form-is a real case of overkill, branding
// many perfectly good constructions as meaningless. The adjective "meaningless", by the way,
// would have to apply to all discussions of the theory of linguistic types (such as that of this
// very paragraph) for they clearly could not occur on any of the levels-neither object language,
// nor metalanguage, nor metametalanguage, etc. So the very act of discussing the theory
// would be the most blatant possible violation of it!
//
// — Douglas Hofstadter, Gödel, Escher, Bach: an Eternal Golden Braid

use crate::{
    ast::*,
    ast_walk::{
        walk,
        WalkRule::{self, *},
    },
    core_forms::{ast_to_name, vr_to_name},
    form::{simple_form, BiDiWR, Both, Form, Positive},
    grammar::{
        FormPat::{self, *},
        SynEnv,
    },
    name::*,
    ty::{synth_type, SynthTy, Ty, TyErr},
    ty_compare::{Canonicalize, Subtype},
    util::assoc::Assoc,
    walk_mode::{NegativeWalkMode, WalkMode},
};
use std::rc::Rc;

// TODO #3: I think we need to extend `Form` with `synth_kind`...
pub fn type_defn(form_name: &str, p: FormPat) -> Rc<Form> {
    Rc::new(Form {
        name: n(form_name),
        grammar: Rc::new(p),
        type_compare: Both(LiteralLike, LiteralLike),
        synth_type: Positive(LiteralLike),
        quasiquote: Both(LiteralLike, LiteralLike),
        eval: Positive(NotWalked),
    })
}

fn type_defn_complex(
    form_name: &str,
    p: FormPat,
    sy: WalkRule<SynthTy>,
    tc: BiDiWR<Canonicalize, Subtype>,
) -> Rc<Form>
{
    Rc::new(Form {
        name: n(form_name),
        grammar: Rc::new(p),
        type_compare: tc,
        synth_type: Positive(sy),
        quasiquote: Both(LiteralLike, LiteralLike),
        eval: Positive(NotWalked),
    })
}

thread_local! {
    // Not needed by the user.
    // An internal type to keep the compiler from trying to dig into the `Expr` in `Expr<X>`.
    pub static primitive_type : Rc<Form> = Rc::new(Form {
        name: n("primitive_type"),
        grammar: Rc::new(form_pat!([(named "name", atom)])),
        type_compare: Both(LiteralLike, LiteralLike),
        synth_type: Positive(LiteralLike),
        quasiquote: Both(LiteralLike, LiteralLike),
        eval: Positive(NotWalked)
    })
}

pub fn get__primitive_type(called: Name) -> Ty {
    ty!({primitive_type.with(|p_t| p_t.clone()) ; "name" => (, Atom(called))})
}

fn is_primitive(form: &Rc<Form>) -> bool { form == &primitive_type.with(|p_t| p_t.clone()) }

pub fn make_core_syn_env_types() -> SynEnv {
    // Regarding the value/type/kind hierarchy, Benjamin Pierce generously assures us that
    // "For programming languages ... three levels have proved sufficient."

    // kinds
    let _type_kind = simple_form("Type", form_pat!((lit "*")));
    let _higher_kind = simple_form(
        "higher",
        form_pat!(
        (delim "k[", "[",
            [ (star (named "param", (call "kind"))), (lit "->"), (named "res", (call "kind"))])),
    );

    // types
    let fn_type = type_defn_complex(
        "fn",
        form_pat!((delim "[", "[",
                [ (star (named "param", (call "Type"))), (lit "->"),
                  (named "ret", (call "Type") ) ])),
        LiteralLike, // synth is normal
        Both(
            LiteralLike,
            cust_rc_box!(move |fn_parts| {
                let actual = fn_parts.context_elt().concrete();
                let actual_parts =
                    Subtype::context_match(&fn_parts.this_ast, &actual, fn_parts.env.clone())?;

                let expd_params = fn_parts.get_rep_term(n("param"));
                let actl_params = actual_parts.get_rep_leaf_or_panic(n("param"));
                if expd_params.len() != actl_params.len() {
                    return Err(TyErr::LengthMismatch(
                        actl_params.iter().map(|&a| Ty(a.clone())).collect(),
                        expd_params.len(),
                    ));
                }
                for (p_expected, p_got) in expd_params.iter().zip(actl_params.iter()) {
                    // Parameters have reversed subtyping:
                    let _: Assoc<Name, Ty> = walk::<Subtype>(
                        *p_got,
                        &fn_parts.with_context(Ty::new(p_expected.clone())),
                    )?;
                }

                walk::<Subtype>(
                    &fn_parts.get_term(n("ret")),
                    &fn_parts
                        .with_context(Ty::new(actual_parts.get_leaf_or_panic(&n("ret")).clone())),
                )
            }),
        ),
    );

    let enum_type = type_defn(
        "enum",
        form_pat!(
            (delim "{", "{", (star
                (delim "+[", "[",
                    [(named "name", atom),(star (named "component", (call "Type")))])))),
    );

    let struct_type = type_defn_complex(
        "struct",
        form_pat!(
             (delim "*[", "[", (star [(named "component_name", atom), (lit ":"),
                                     (named "component", (call "Type"))]))),
        LiteralLike, // synth is normal
        Both(
            LiteralLike,
            cust_rc_box!(move |struct_parts| {
                let actual_struct_parts = Subtype::context_match(
                    &struct_parts.this_ast,
                    &struct_parts.context_elt().concrete(),
                    struct_parts.env.clone(),
                )?;

                for (got_name, got_ty) in actual_struct_parts
                    .get_rep_leaf_or_panic(n("component_name"))
                    .iter()
                    .zip(actual_struct_parts.get_rep_leaf_or_panic(n("component")))
                {
                    let mut found = false;
                    for (exp_name, exp_ty) in struct_parts
                        .get_rep_term(n("component_name"))
                        .iter()
                        .zip(struct_parts.get_rep_term(n("component")))
                    {
                        if ast_to_name(got_name) != ast_to_name(exp_name) {
                            continue;
                        }
                        found = true;
                        let _ = walk::<Subtype>(
                            &got_ty,
                            &struct_parts.with_context(Ty(exp_ty.clone())),
                        )?;
                    }
                    if !found {
                        return Err(TyErr::NonexistentStructField(
                            ast_to_name(&got_name),
                            struct_parts.context_elt().clone(),
                        ));
                    }
                }

                Ok(assoc_n!())
            }),
        ),
    );

    let tuple_type = type_defn_complex(
        "tuple",
        form_pat!((delim "**[", "[", (star (named "component", (call "Type"))))),
        LiteralLike,
        Both(LiteralLike, LiteralLike),
    );

    let forall_type = type_defn_complex(
        "forall_type",
        form_pat!([(lit "forall"), (star (named "param", atom)), (lit "."),
                       (named "body", (import [* [forall "param"]], (call "Type")))]),
        LiteralLike, // synth is normal
        Both(
            LiteralLike,
            cust_rc_box!(move |forall_parts| {
                match Subtype::context_match(
                    &forall_parts.this_ast,
                    &forall_parts.context_elt().concrete(),
                    forall_parts.env.clone(),
                ) {
                    // ∀ X. ⋯ <: ∀ Y. ⋯ ? (so force X=Y)
                    Ok(actual_forall_parts) => {
                        let actl_inner_body = actual_forall_parts.get_leaf_or_panic(&n("body"));

                        walk::<Subtype>(
                            &forall_parts.get_term(n("body")),
                            &forall_parts.with_context(Ty::new(actl_inner_body.clone())),
                        )
                    }
                    // ∀ X. ⋯ <: ⋯ ?  (so try to specialize X)
                    Err(_) => {
                        // `import [forall "param"]` handles the specialization,
                        //  and we leave the context element alone
                        walk::<Subtype>(&forall_parts.get_term(n("body")), &forall_parts)
                    }
                }
            }),
        ),
    );

    // This behaves slightly differently than the `mu` from Pierce's book,
    //  because we need to support mutual recursion.
    // In particular, it relies on having a binding for `param` in the environment!
    // The only thing that `mu` actually does is suppress substitution,
    //  to prevent the attempted generation of an infinite type.
    let mu_type = type_defn_complex(
        "mu_type",
        form_pat!([(lit "mu_type"), (star (named "param", (import [prot "param"], varref))),
             (lit "."), (named "body", (import [* [prot "param"]], (call "Type")))]),
        LiteralLike,
        Both(
            LiteralLike,
            cust_rc_box!(move |mu_parts| {
                let rhs_mu_parts = Subtype::context_match(
                    &mu_parts.this_ast,
                    &mu_parts.context_elt().concrete(),
                    mu_parts.env.clone(),
                )?;

                let rhs_body = rhs_mu_parts.get_leaf_or_panic(&n("body"));

                let r_params = rhs_mu_parts.get_rep_leaf_or_panic(n("param"));
                let l_params = mu_parts.get_rep_term(n("param"));
                if r_params.len() != l_params.len() {
                    return Err(TyErr::LengthMismatch(
                        r_params.iter().map(|a| Ty((*a).clone())).collect(),
                        l_params.len(),
                    ));
                }
                // Apply the Amber rule; assume the `mu`ed names are subtypes to subtype the bodies
                let mut amber_environment = mu_parts.env.clone();
                for (&ee_r, ee_l) in r_params.iter().zip(l_params.iter()) {
                    let (p_r, p_l) = if let (ExtendEnv(r, _), ExtendEnv(l, _)) = (ee_r, ee_l) {
                        (&**r, &**l)
                    } else {
                        icp!("ill-formed mu_type")
                    };
                    if p_r == p_l // short-circuit if the names are the same...
                        || mu_parts.env.find(&vr_to_name(&*p_r)) // ...or Amber assumed so already
                             == Some(&Ty(p_l.clone()))
                    {
                        continue;
                    }

                    amber_environment = amber_environment.set(vr_to_name(p_r), Ty(p_l.clone()));
                }

                walk::<Subtype>(
                    &mu_parts.get_term(n("body")),
                    &mu_parts
                        .with_environment(amber_environment)
                        .with_context(Ty::new(rhs_body.clone())),
                )
            }),
        ),
    );

    // TODO: add named repeats. Add type-level numbers!
    // TODO: We probably need kinds, to say that `T` is a tuple
    // TODO: we'll need dotdotdot inside betas, also, huh?
    let dotdotdot_type = type_defn(
        "dotdotdot_type",
        form_pat!((delim ":::[", "[", [(star (named "driver", varref)), (lit ">>"),
                                        (named "body", (call "Type"))])),
    );

    let forall_type_0 = forall_type.clone();

    // [Type theory alert!]
    // Pierce's notion of type application is an expression, not a type;
    //  you just take an expression whose type is a `forall`, and then give it some arguments.
    // Instead, we will just make the type system unify `forall` types with more specific types.
    // But sometimes the user wants to write a more specific type, and they use this.
    //
    // This is, at the type level, like function application.
    // We restrict the LHS to being a name, because that's "normal". Should we?
    let type_apply = type_defn_complex(
        "type_apply",
        // TODO: invoking `scan` directly to ad-hoc tokenize ... isn't ideal.
        form_pat!([(named "type_rator", (call "Type")),
                   (call "DefaultSeparator"), (scan r"(<)"),
                   (star (named "arg", (call "Type"))),
                   (call "DefaultSeparator"), (scan r"(>)")]),
        // TODO: shouldn't it be "args"?
        cust_rc_box!(move |tapp_parts| {
            use crate::util::mbe::EnvMBE;
            let arg_res = tapp_parts.get_rep_res(n("arg"))?;
            let rator_res = tapp_parts.get_res(n("type_rator"))?;
            match rator_res.0 {
                VariableReference(rator_vr) => {
                    // e.g. `X<int, Y>` underneath `mu X. ...`

                    // Rebuild a type_apply, but evaulate its arguments
                    // This kind of thing is necessary because
                    //  we wish to avoid aliasing problems at the type level.
                    // In System F, this is avoided by performing capture-avoiding substitution.
                    let mut new__tapp_parts = EnvMBE::new_from_leaves(
                        assoc_n!("type_rator" => VariableReference(rator_vr)),
                    );

                    let mut args = vec![];
                    for individual__arg_res in arg_res {
                        args.push(EnvMBE::new_from_leaves(
                            assoc_n!("arg" => individual__arg_res.concrete()),
                        ));
                    }
                    new__tapp_parts.add_anon_repeat(args, None);

                    if let Node(ref f, _, ref exp) = tapp_parts.this_ast {
                        Ok(Ty::new(Node(/* forall */ f.clone(), new__tapp_parts, exp.clone())))
                    } else {
                        icp!()
                    }
                }
                Node(ref got_f, ref lhs_parts, ref exports) if is_primitive(got_f) => {
                    // Like the above; don't descend into `Expr`
                    let mut new__tapp_parts = EnvMBE::new_from_leaves(assoc_n!("type_rator" =>
                            Node(got_f.clone(), lhs_parts.clone(), exports.clone())));
                    let mut args = vec![];
                    for individual__arg_res in arg_res {
                        args.push(EnvMBE::new_from_leaves(
                            assoc_n!("arg" => individual__arg_res.concrete()),
                        ));
                    }
                    new__tapp_parts.add_anon_repeat(args, None);

                    if let Node(ref f, _, ref exp) = tapp_parts.this_ast {
                        Ok(Ty::new(Node(/* forall */ f.clone(), new__tapp_parts, exp.clone())))
                    } else {
                        icp!()
                    }
                }
                Node(ref got_f, ref forall_type__parts, _) if got_f == &forall_type_0 => {
                    // This might ought to be done by a specialized `beta`...
                    let params = forall_type__parts.get_rep_leaf_or_panic(n("param"));
                    if params.len() != arg_res.len() {
                        panic!("[kind error] wrong number of arguments");
                    }
                    let mut new__ty_env = tapp_parts.env.clone();
                    for (name, actual_type) in params.iter().zip(arg_res) {
                        new__ty_env = new__ty_env.set(ast_to_name(name), actual_type);
                    }

                    // This bypasses the binding in the type, which is what we want:
                    synth_type(
                        crate::core_forms::strip_ee(
                            forall_type__parts.get_leaf_or_panic(&n("body")),
                        ),
                        new__ty_env,
                    )
                }

                _ => {
                    panic!("[kind error] {} is not a forall.", rator_res);
                }
            }
        }),
        Both(LiteralLike, LiteralLike),
    );

    assoc_n!("Type" => Rc::new(Biased(Rc::new(forms_to_form_pat![
        fn_type.clone(),
        // TODO: these should turn into `primitive_type`s in the core type environment.
        // First, we need a really simple core type environment for testing,
        //  and then to change all the `uty!({Type Int :})`s into `uty!(Int)`s
        //  (and `ast!({"Type" "Int" :})`s into `ast!((vr "Int"))`).
        type_defn("Ident", form_pat!((name_lit "Ident"))),
        type_defn("Int", form_pat!((name_lit "Int"))),
        type_defn("Nat", form_pat!((name_lit "Nat"))),
        type_defn("Float", form_pat!((name_lit "Float"))),
        enum_type.clone(),
        struct_type.clone(),
        tuple_type.clone(),
        forall_type.clone(),
        dotdotdot_type.clone(),
        mu_type.clone(),
        type_apply.clone()
        ]), Rc::new(VarRef(Rc::new(Call(n("DefaultAtom"))))))))
}

// TODO #4: this should be extensible for when the syntax environment is extended...
//  or just automatically have one type per NT. Probably the latter.
pub fn nt_to_type(nt: Name) -> Ty {
    if nt == n("Type") || nt == n("Pat") || nt == n("Expr") {
        get__primitive_type(nt)
    } else {
        icp!("unknown NT {}", nt)
    }
}

// TODO #4: make this extensible, too! When the user creates a new NT,
//  do they need to specify the direction?
pub fn nt_is_positive(nt: Name) -> bool {
    if nt == n("Type") || nt == n("Expr") || nt == n("DefaultReference") {
        true
    } else if nt == n("Pat") || nt == n("Ident") || nt == n("DefaultAtom") {
        // TODO: Remove "Ident" entirely.
        // HACK: "Ident" and "DefaultAtom" are just not walked; this should probably be three-armed
        false
    } else {
        icp!("unknown NT {}", nt)
    }
}

pub fn less_quoted_ty(t: &Ty, nt: Option<Name>, loc: &Ast) -> Result<Ty, crate::ty::TypeError> {
    // suppose that this is an expr, and `body` has the type `Expr<String>`:
    expect_ty_node!( (t ; crate::core_forms::find_core_form("Type", "type_apply") ; loc)
        tapp_parts;
        {
            if let Some(nt) = nt { // Check it if you got it
                ty_exp!(
                    &Ty::new(tapp_parts.get_leaf_or_panic(&n("type_rator")).clone()),
                    &get__primitive_type(nt),
                    loc
                );
            }

            let args = tapp_parts.get_rep_leaf_or_panic(n("arg"));
            if args.len() != 1 {
                ty_err!(LengthMismatch(args.iter().map(|t| Ty::new((*t).clone())).collect(), 1)
                        at loc);
            }

            // ...returns `String` in that case
            Ok(Ty(args[0].clone()))
        }
    )
}

pub fn more_quoted_ty(t: &Ty, nt: Name) -> Ty {
    ty!({"Type" "type_apply" :
        "type_rator" => (, get__primitive_type(nt).concrete()),
        "arg" => [(, t.concrete())]})
}

#[test]
fn parametric_types() {
    // Are plain parametric types valid?
    without_freshening! { // (so we don't have to compute alpha-equivalence)
     assert_eq!(
         synth_type(&ast!({"Type" "forall_type" : "param" => ["t"],
                           "body" => (import [* [forall "param"]] (vr "t"))}),
                    Assoc::new()),
        Ok(ty!({"Type" "forall_type" : "param" => ["t"],
                "body" => (import [* [forall "param"]] (vr "t"))})));
    }

    let ident_ty = ty!( { "Type" "Ident" : });
    let nat_ty = ty!( { "Type" "Nat" : });

    let para_ty_env = assoc_n!(
        "unary" => ty!({ "Type" "forall_type" :
            "param" => ["t"],
            "body" => (import [* [forall "param"]] { "Type" "fn" :
                "param" => [ (, nat_ty.concrete()) ],
                "ret" => (vr "t") })}),
        "binary" => ty!({ "Type" "forall_type" :
            "param" => ["t", "u"],
            "body" => (import [* [forall "param"]] { "Type" "fn" :
                "param" => [ (vr "t"), (vr "u") ],
                "ret" => (, nat_ty.concrete()) })}));
    let mued_ty_env = assoc_n!("unary" => ty!((vr "unary")), "binary" => ty!((vr "binary")));

    // If `unary` is `mu`ed, `unary< ident >` can't be simplified.
    assert_eq!(
        synth_type(
            &ast!( { "Type" "type_apply" :
            "type_rator" => (vr "unary"),
            "arg" => [ (, ident_ty.concrete()) ]}),
            mued_ty_env.clone()
        ),
        Ok(ty!({ "Type" "type_apply" :
            "type_rator" => (vr "unary"),
            "arg" => [ (, ident_ty.concrete()) ]}))
    );

    // If `unary` is `mu`ed, `unary< [nat -> nat] >` can't be simplified.
    assert_eq!(
        synth_type(
            &ast!( { "Type" "type_apply" :
            "type_rator" => (vr "unary"),
            "arg" => [ { "Type" "fn" :
                "param" => [(, nat_ty.concrete())], "ret" => (, nat_ty.concrete())} ]}),
            mued_ty_env.clone()
        ),
        Ok(ty!({ "Type" "type_apply" :
            "type_rator" => (vr "unary"),
            "arg" => [ { "Type" "fn" :
                "param" => [(, nat_ty.concrete())], "ret" => (, nat_ty.concrete())} ]}))
    );

    // Expand the definition of `unary`.
    assert_eq!(
        synth_type(
            &ast!( { "Type" "type_apply" :
            "type_rator" => (vr "unary"),
            "arg" => [ (, ident_ty.concrete()) ]}),
            para_ty_env
        ),
        Ok(ty!({ "Type" "fn" :
            "param" => [(, nat_ty.concrete() )],
            "ret" => (, ident_ty.concrete())}))
    );
}
