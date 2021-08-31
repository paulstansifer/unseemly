use crate::{
    ast::{Ast, AstContents, AstContents::*},
    grammar::{
        FormPat::{self, *},
        SynEnv,
    },
    name::*,
    util::mbe::EnvMBE,
};

fn node_names_mentioned(pat: &FormPat) -> Vec<Name> {
    match *pat {
        Named(n, ref body) => {
            let mut res = node_names_mentioned(&*body);
            res.push(n);
            res
        }
        Scope(_, _) => vec![],
        Pick(_, _) => vec![],
        Star(ref body)
        | Plus(ref body)
        | NameImport(ref body, _)
        | NameImportPhaseless(ref body, _)
        | VarRef(ref body)
        | Literal(ref body, _)
        | QuoteDeepen(ref body, _)
        | QuoteEscape(ref body, _)
        | Common(ref body)
        | Reserved(ref body, _) => node_names_mentioned(&*body),
        Seq(ref sub_pats) | Alt(ref sub_pats) => {
            let mut res = vec![];
            for pat in sub_pats {
                res.append(&mut node_names_mentioned(pat));
            }
            res
        }
        Biased(ref lhs, ref rhs) => {
            let mut res = node_names_mentioned(&*lhs);
            res.append(&mut node_names_mentioned(&*rhs));
            res
        }
        Anyways(_) | Impossible | Scan(_, _) | Call(_) | SynImport(_, _, _) => vec![],
    }
}

pub fn unparse_mbe(pat: &FormPat, actl: &AstContents, context: &EnvMBE<Ast>, s: &SynEnv) -> String {
    // HACK: handle underdetermined forms
    let undet = crate::ty_compare::underdetermined_form.with(|u| u.clone());
    match actl {
        Node(form, body, _) if form == &undet => {
            return crate::ty_compare::unification.with(|unif| {
                let var = body.get_leaf_or_panic(&n("id")).to_name();
                let looked_up = unif.borrow().get(&var).cloned();
                match looked_up {
                    // Apparently the environment is recursive; `{}`ing it stack-overflows
                    Some(ref clo) => {
                        format!("{} in some environment", clo.it /* , {:#?} clo.env */)
                    }
                    None => format!("¿{}?", var),
                }
            });
        }
        _ => {}
    }

    // TODO: this really ought to notice when `actl` is ill-formed for `pat`.
    match (pat, actl) {
        (&Named(name, ref body), _) => {
            // TODO: why does the `unwrap_or` case happen once after each variable is printed?
            unparse_mbe(&*body, context.get_leaf(name).unwrap_or(&ast!((at ""))).c(), context, s)
        }
        (&Call(sub_form), _) => unparse_mbe(s.find_or_panic(&sub_form), actl, context, s),
        (&Anyways(_), _) | (&Impossible, _) => "".to_string(),
        (&Literal(_, n), _) => n.print(),
        (&Scan(_, _), &Atom(n)) => n.print(),
        (&Scan(_, _), _) => "".to_string(), // HACK for `Alt`
        (&VarRef(ref sub_form), &VariableReference(n)) => {
            unparse_mbe(&*sub_form, &Atom(n), context, s)
        }
        (&VarRef(_), _) => "".to_string(), // HACK for `Alt`
        (&Seq(ref sub_pats), _) => {
            let mut prev_empty = true;
            let mut res = String::new();
            for sub_pat in sub_pats {
                let sub_res = unparse_mbe(&*sub_pat, actl, context, s);
                if !prev_empty && sub_res != "" {
                    res.push(' ');
                }
                prev_empty = sub_res == "";
                res.push_str(&sub_res);
            }
            res
        }
        (&Alt(ref sub_pats), _) => {
            let mut any_scopes = false;
            for sub_pat in sub_pats {
                if let Scope(_, _) = &**sub_pat {
                    any_scopes = true;
                    continue;
                }

                let sub_res = unparse_mbe(&*sub_pat, actl, context, s);
                if sub_res != "" {
                    return sub_res;
                } // HACK: should use `Option`
            }
            // HACK: certain forms don't live in the syntax environment,
            //  but "belong" under an `Alt`, so just assume forms know their grammar:
            if any_scopes {
                if let &Node(ref form_actual, ref body, _) = actl {
                    return unparse_mbe(&*form_actual.grammar, actl, body, s);
                }
            }

            return "".to_string(); // Not sure if it's an error, or really just empty
        }
        (&Biased(ref lhs, ref rhs), _) => {
            format!("{}{}", unparse_mbe(lhs, actl, context, s), unparse_mbe(rhs, actl, context, s))
        }
        (&Star(ref sub_pat), _) | (&Plus(ref sub_pat), _) => {
            let mut first = true;
            let mut res = String::new();
            for marched_ctxt in context.march_all(&node_names_mentioned(&*sub_pat)) {
                if !first {
                    res.push(' ');
                }
                first = false;
                res.push_str(&unparse_mbe(&*sub_pat, actl, &marched_ctxt, s));
            }
            res
        }
        (&Scope(ref form, _), &Node(ref form_actual, ref body, _)) => {
            if form == form_actual {
                unparse_mbe(&*form.grammar, actl, body, s)
            } else {
                "".to_string() // HACK for `Alt`
            }
        }
        (&Scope(_, _), _) => "".to_string(), // Non-match
        (&Pick(ref body, _), _) | (&Common(ref body), _) => unparse_mbe(&*body, actl, context, s),
        (&NameImport(ref body, _), &ExtendEnv(ref actl_body, _)) => {
            unparse_mbe(&*body, actl_body.c(), context, s)
        }
        (&NameImport(_, _), _) => format!("[Missing import]→{:#?}←", actl),
        (&NameImportPhaseless(ref body, _), &ExtendEnvPhaseless(ref actl_body, _)) => {
            unparse_mbe(&*body, actl_body.c(), context, s)
        }
        (&NameImportPhaseless(_, _), _) => format!("[Missing import]±→{:#?}←±", actl),
        (&QuoteDeepen(ref body, _), &QuoteMore(ref actl_body, _)) => {
            unparse_mbe(&*body, actl_body.c(), context, s)
        }
        (&QuoteDeepen(_, _), _) => format!("[Missing qm]{:#?}", actl),
        (&QuoteEscape(ref body, _), &QuoteLess(ref actl_body, _)) => {
            unparse_mbe(&*body, actl_body.c(), context, s)
        }
        (&QuoteEscape(_, _), _) => format!("[Missing ql]{:#?}", actl),
        (&SynImport(ref _lhs_grammar, ref _rhs, _), &Node(_, ref actl_body, _)) => {
            // TODO: I think we need to store the LHS or the new SynEnv to make this pretty.
            format!("?syntax import? {}", actl_body)
        }
        (&SynImport(_, _, _), _) => "".to_string(),
        (&Reserved(ref body, _), _) => unparse_mbe(body, actl, context, s),
    }
}
