use name::*;
use grammar::{FormPat, SynEnv};
use grammar::FormPat::*;
use ast::Ast;
use ast::Ast::*;
use util::mbe::EnvMBE;

fn node_names_mentioned(pat: &FormPat) -> Vec<Name> {
    match *pat {
        Named(n, ref body) => {
            let mut res = node_names_mentioned(&*body);
            res.push(n);
            res
        }
        Scope(_,_) => { vec![] }
        Delimited(_,_, ref body) | Star(ref body) | Plus(ref body) | ComputeSyntax(_, ref body)
        | NameImport(ref body, _) | QuoteDeepen(ref body, _) | QuoteEscape(ref body, _)=> {
            node_names_mentioned(&*body)
        }
        Seq(ref sub_pats) | Alt(ref sub_pats) => {
            let mut res = vec![];
            for pat in sub_pats { res.append(&mut node_names_mentioned(pat)); }
            res
        }
        Biased(ref lhs, ref rhs) => {
            let mut res = node_names_mentioned(&*lhs);
            res.append(&mut node_names_mentioned(&*rhs));
            res
        }
        Anyways(_) | Impossible | Literal(_) | AnyToken | AnyAtomicToken | VarRef | Call(_)
        | SynImport(_,_,_) => { vec![] }
    }
}

pub fn unparse_mbe(pat: &FormPat, actl: &Ast, context: &EnvMBE<Ast>, s: &SynEnv) -> String {

    //HACK: handle underdetermined forms
    let undet = ::ty_compare::underdetermined_form.with(|u| u.clone());
    match *actl {
        Node(ref form, ref body, _) if form == &undet => {
            return ::ty_compare::unification.with(|unif| {
                let var = ::core_forms::ast_to_name(body.get_leaf_or_panic(&n("id")));
                let looked_up = unif.borrow().get(&var).cloned();
                match looked_up {
                    // Apparently the environment is recursive; `{}`ing it stack-overflows
                    Some(ref clo) => format!("{} in some environment", clo.it /*, {:#?} clo.env*/),
                    None => format!("¿{}?", var)
                }
            });
        }
        _ => {}
    }

    // TODO: this really ought to notice when `actl` is ill-formed for `pat`.
    match (pat, actl) {
        (&Named(name, ref body), _) => {
            unparse_mbe(&*body, context.get_leaf(name).unwrap_or(&Atom(n("<->"))), context, s)
        }
            //=> unparse_mbe(&*body, context.get_leaf(name).unwrap_or(&Atom(n("<MISSING>"))), context, s),
        (&Call(sub_form), _) => unparse_mbe(s.find_or_panic(&sub_form), actl, context, s),
        (&Anyways(_), _) | (&Impossible, _) => "".to_string(),
        (&Literal(n), _) => n.print(),
        (&AnyToken, &Atom(n)) => n.print(),
        (&AnyToken, _) => panic!("TODO: pretty print arbitrary token trees"),
        (&AnyAtomicToken, &Atom(n)) => n.print(),
        (&AnyAtomicToken, _) => "".to_string(), // HACK for `Alt`
        (&VarRef, &VariableReference(n)) => n.print(),
        (&VarRef, _) => "".to_string(), // HACK for `Alt`
        (&Delimited(opener, delim, ref body), _) => {
            let mut closer = opener.print();
            closer.pop();
            format!("{}{}{}{}",
                opener.print(), unparse_mbe(&*body, actl, context, s), delim.close(), closer)
        }
        (&Seq(ref sub_pats), _) => {
            let mut prev_empty = true;
            let mut res = String::new();
            for sub_pat in sub_pats {
                let sub_res = unparse_mbe(&*sub_pat, actl, context, s);
                if !prev_empty && sub_res != "" { res.push(' '); }
                prev_empty = sub_res == "";
                res.push_str(&sub_res);
            }
            res
        }
        (&Alt(ref sub_pats), _) => {
            let mut any_scopes = false;
            for sub_pat in sub_pats {
                if let Scope(_, _) = &**sub_pat { any_scopes = true; continue; }

                let sub_res = unparse_mbe(&*sub_pat, actl, context, s);
                if sub_res != "" { return sub_res } // HACK: should use `Option`
            }
            // HACK: certain forms don't live in the syntax environment,
            //  but "belong" under an `Alt`, so just assume forms know their grammar:
            if any_scopes {
                match actl {
                    &Node(ref form_actual, ref body, _) => {
                        return unparse_mbe(&*form_actual.grammar, actl, body, s);
                    }
                    _ => { }
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
                if !first { res.push(' '); }
                first = false;
                res.push_str(&unparse_mbe(&*sub_pat, actl, &marched_ctxt, s));
            }
            res
        }
        (&ComputeSyntax(_, _), _) => format!("?compute syntax? {:#?} ?cs?", actl),
        (&Scope(ref form, _), &Node(ref form_actual, ref body, _)) => {
            if form == form_actual {
                unparse_mbe(&*form.grammar, actl, body, s)
            } else {
                "".to_string() // HACK for `Alt`
            }
        }
        (&Scope(_,_), _) => "".to_string(), // Non-match
        (&NameImport(ref body, _), &ExtendEnv(ref actl_body, _)) => {
            unparse_mbe(&*body, &*actl_body, context, s)
        }
        (&NameImport(_, _), _) => { format!("[Missing import]→{:#?}←", actl) }
        (&QuoteDeepen(ref body, _), &QuoteMore(ref actl_body, _)) => {
            unparse_mbe(&*body, &*actl_body, context, s)
        }
        (&QuoteDeepen(_, _), _) => { format!("[Missing qm]{:#?}", actl)}
        (&QuoteEscape(ref body, _), &QuoteLess(ref actl_body, _)) => {
            unparse_mbe(&*body, &*actl_body, context, s)
        }
        (&QuoteEscape(_, _), _) => { format!("[Missing ql]{:#?}", actl)}
        (&SynImport(ref _fp, ref _n, ref _se), &Node(_, ref _body, _)) => {
            // TODO: I think we need to store the LHS in the AST somehow for this to work.
/*            (*se.0)(se, )
            format!("{} {}",
                unparse_mbe(fp, ????, context, s))
                unparse_mbe(pat: &FormPat, actl: &Ast, context: &EnvMBE<Ast>, s: &SynEnv)*/
                format!("?synax import? {:#?} ?si?", actl)
        }
        (&SynImport(_,_,_), _) => { "".to_string() }
    }
}

//pub fn unparse_mbe(pat: &FormPat, actl: &Ast, context: &EnvMBE<Ast>, s: &SynEnv) -> String {
