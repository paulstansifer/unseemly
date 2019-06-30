// Alpha-equivalence utilities.
// Based on https://repository.library.northeastern.edu/files/neu:cj82mb52h

// `freshen` gets a value ready for destructuring.
// `freshen_rec` gets a value and its pattern ready for destructuring.

use ast::Ast::{self, *};
use name::*;
use util::{assoc::Assoc, mbe::EnvMBE};

// A renaming that only affects names at the "current" quotation level
#[derive(Clone, Debug, PartialEq)]
pub struct Ren {
    env: Assoc<Name, Ast>,
    q_lev: i16,
}

impl Ren {
    pub fn find(&self, n: Name) -> Option<&Ast> {
        if self.q_lev == 0 {
            self.env.find(&n)
        } else {
            None
        }
    }
    pub fn unset(self, n: Name) -> Ren {
        if self.q_lev == 0 {
            Ren { env: self.env.unset(&n), q_lev: self.q_lev }
        } else {
            self
        }
    }
    pub fn set_assoc(self, other: &Ren) -> Ren {
        if self.q_lev == other.q_lev {
            Ren { env: self.env.set_assoc(&other.env), q_lev: self.q_lev }
        } else {
            self
        }
    }
    pub fn q_more(&self, by: u8) -> Ren {
        Ren { env: self.env.clone(), q_lev: self.q_lev + i16::from(by) }
    }
    pub fn q_less(&self, by: u8) -> Ren {
        Ren { env: self.env.clone(), q_lev: self.q_lev - i16::from(by) }
    }
    pub fn new() -> Ren {
        Ren { env: Assoc::new(), q_lev: 0 }
    }
    pub fn single(n: Name, a: Ast) -> Ren {
        Ren { env: Assoc::new().set(n, a), q_lev: 0 }
    }
}

impl From<Assoc<Name, Ast>> for Ren {
    fn from(a: Assoc<Name, Ast>) -> Ren {
        Ren { env: a, q_lev: 0 }
    }
}

fn substitute_rec(node: &Ast, cur_node_contents: &EnvMBE<Ast>, env: &Ren) -> Ast {
    match *node {
        Node(ref f, ref new_parts, ref export) => {
            // let new_cnc = parts.clone();
            Node(
                f.clone(),
                new_parts.marched_map(&mut |_, marched_parts: &EnvMBE<Ast>, part: &Ast| {
                    substitute_rec(part, marched_parts, env)
                }),
                export.clone(),
            )
        }
        VariableReference(n) => env.find(n).unwrap_or(&node.clone()).clone(),
        ExtendEnv(ref body, ref beta) => {
            let mut new_env = env.clone();
            for bound_name in ::beta::bound_from_beta(beta, cur_node_contents, 0) {
                new_env = new_env.unset(bound_name);
            }

            ExtendEnv(Box::new(substitute_rec(body, cur_node_contents, &new_env)), beta.clone())
        }
        QuoteMore(ref body, pos) => {
            QuoteMore(Box::new(substitute_rec(body, cur_node_contents, &env.q_more(1))), pos)
        }
        QuoteLess(ref body, depth) => {
            QuoteLess(Box::new(substitute_rec(body, cur_node_contents, &env.q_less(depth))), depth)
        }
        _ => node.clone(),
    }
}

/// Substitute `VariableReference`s in `node`, according to `env`.
/// TODO: don't use this to "capture the environment"; it doesn't work in the presence of recursion
/// Instead, we should introduce a "constant" to Beta.
/// TODO: because of mu's use of `VariableReference`s in a place where other `Ast`s are forbidden,
///  it seems like this has limited use.
/// TODO: this isn't capture-avoiding (and shouldn't be, when called by `freshen_rec`)
/// It's safe to use when the RHS of the environment is just fresh names.
pub fn substitute(node: &Ast, env: &Assoc<Name, Ast>) -> Ast {
    substitute_rec(node, &EnvMBE::new(), &Ren::from(env.clone()))
}

/// Like `beta::names_mentioned`, but for all the imports in `parts`
fn mentioned_in_import(parts: &EnvMBE<Ast>) -> Vec<Name> {
    fn process_ast(a: &Ast, v: &mut Vec<Name>) {
        match *a {
            Node(_, _, _) => {} // new scope
            ExtendEnv(ref body, ref beta) => {
                let mut beta_mentions = beta.names_mentioned_and_bound();
                v.append(&mut beta_mentions);
                process_ast(&*body, v);
            }
            // TODO: does it make sense to mention a name underneath a quotation?
            QuoteMore(ref body, _) | QuoteLess(ref body, _) => process_ast(body, v),
            Trivial | Atom(_) | VariableReference(_) => {} // no beta
            Shape(_) | IncompleteNode(_) => panic!("ICE: shouldn't be needed"),
        }
    }

    let mut res = vec![];
    parts.map(&mut |a| process_ast(a, &mut res));
    res
}

fn freshen_rec(node: &Ast, renamings: &EnvMBE<(Ast, Ren)>, env: Ren) -> Ast {
    //  `env` is used to update the references to those atoms to match
    match *node {
        Node(_, _, _) => substitute_rec(node, &EnvMBE::new(), &env),
        VariableReference(n) => env.find(n).unwrap_or(&node.clone()).clone(),
        ExtendEnv(ref body, ref beta) => {
            let new_env = env.set_assoc(&beta.extract_from_mbe(renamings, &|x: &(_, Ren)| &x.1));

            ExtendEnv(Box::new(freshen_rec(body, renamings, new_env)), beta.clone())
        }
        QuoteMore(ref body, pos) => {
            QuoteMore(Box::new(freshen_rec(body, renamings, env.q_more(1))), pos)
        }
        QuoteLess(ref body, depth) => {
            QuoteLess(Box::new(freshen_rec(body, renamings, env.q_less(depth))), depth)
        }
        Atom(_) | Trivial | IncompleteNode(_) | Shape(_) => node.clone(),
    }
}

thread_local! {
    pub static freshening_enabled: ::std::cell::RefCell<bool> = ::std::cell::RefCell::new(true);
}

pub fn freshen(a: &Ast) -> Ast {
    // TODO: I think this shouldn't take a reference for performance
    if freshening_enabled.with(|f| *f.borrow()) {
        match a {
            &Node(ref f, ref p, ref export) => {
                // Every part that gets mentioned inside this node...
                let mentioned = mentioned_in_import(p);
                // ...needs to have its binders freshend:
                let fresh_ast_and_rens = freshen_binders_inside_node(p, &mentioned);

                Node(
                    f.clone(),
                    fresh_ast_and_rens.marched_map(
                        &mut |_, marched: &EnvMBE<(Ast, Ren)>, &(ref part, _)| {
                            freshen_rec(part, marched, Ren::new())
                        },
                    ),
                    export.clone(),
                )
            }
            non_node => non_node.clone(),
        }
    } else {
        a.clone()
    }
}
// TODO: verify that this handles internal `ExtendEnv`s right
pub fn freshen_with(lhs: &Ast, rhs: &Ast) -> (Ast, Ast) {
    if freshening_enabled.with(|f| *f.borrow()) {
        match (lhs, rhs) {
            (&Node(ref f, ref p_lhs, ref export), &Node(ref f_rhs, ref p_rhs, ref export_rhs)) => {
                if f != f_rhs || export != export_rhs {
                    return (lhs.clone(), rhs.clone());
                }
                // Every part that gets mentioned inside this node...
                let mentioned = mentioned_in_import(p_lhs);
                //  (if it matters which `p_{l,r}hs` we used, the match below will be `None`)
                // ...needs to have its binders freshend:
                match freshen_binders_inside_node_with(p_lhs, p_rhs, &mentioned) {
                    Some(fresh_ast_and_rens) => {
                        let new_p_lhs = fresh_ast_and_rens.marched_map(
                            &mut |_,
                                  marched: &EnvMBE<(Ast, Ren, Ast, Ren)>,
                                  &(ref parts, _, _, _)| {
                                freshen_rec(
                                    parts,
                                    &marched.map(&mut |q| (q.0.clone(), q.1.clone())),
                                    Ren::new(),
                                )
                            },
                        );
                        let new_p_rhs = fresh_ast_and_rens.marched_map(
                            &mut |_,
                                  marched: &EnvMBE<(Ast, Ren, Ast, Ren)>,
                                  &(_, _, ref parts, _)| {
                                freshen_rec(
                                    parts,
                                    &marched.map(&mut |q| (q.2.clone(), q.3.clone())),
                                    Ren::new(),
                                )
                            },
                        );
                        (
                            Node(f.clone(), new_p_lhs, export.clone()),
                            Node(f.clone(), new_p_rhs, export.clone()),
                        )
                    }
                    None => (lhs.clone(), rhs.clone()), // No destructuring will be performed!
                }
            }
            _ => (lhs.clone(), rhs.clone()), // No binding
        }
    } else {
        (lhs.clone(), rhs.clone()) // Freshening is disabled
    }
}

pub fn freshen_binders_inside_node(parts: &EnvMBE<Ast>, mentioned: &[Name]) -> EnvMBE<(Ast, Ren)> {
    parts.named_map(&mut |n: &Name, a: &Ast| {
        if mentioned.contains(n) {
            freshen_binders(a)
        } else {
            (a.clone(), Ren::new())
        }
    })
}

pub fn freshen_binders_inside_node_with(
    p_lhs: &EnvMBE<Ast>,
    p_rhs: &EnvMBE<Ast>,
    men: &[Name],
) -> Option<EnvMBE<(Ast, Ren, Ast, Ren)>>
{
    if !p_lhs.can_map_with(p_rhs) {
        return None;
    }
    p_lhs
        .named_map_with(p_rhs, &|n: &Name, a_lhs: &Ast, a_rhs: &Ast| {
            if men.contains(n) {
                freshen_binders_with(a_lhs, a_rhs).ok_or(())
            } else {
                Ok((a_lhs.clone(), Ren::new(), a_rhs.clone(), Ren::new()))
            }
        })
        .lift_result()
        .ok()
}

/// Returns an `Ast` like `a`, but with fresh `Atom`s
///  and a map to change references in the same manner
pub fn freshen_binders(a: &Ast) -> (Ast, Ren) {
    match *a {
        Trivial | VariableReference(_) => (a.clone(), Ren::new()),
        Atom(old_name) => {
            let new_name = old_name.freshen();
            (Atom(new_name), Ren::single(old_name, VariableReference(new_name)))
        }
        Node(ref f, ref parts, ref export) => {
            if export == &::beta::ExportBeta::Nothing {
                return (a.clone(), Ren::new()); // short-circuit (should this at least warn?)
            }
            let exported = export.names_mentioned(); // Unmentioned atoms shouldn't be touched

            let fresh_pairs = freshen_binders_inside_node(parts, &exported);
            let fresh_ast = fresh_pairs.map(&mut |&(ref a, _): &(Ast, _)| a.clone());
            let renaming = export.extract_from_mbe(&fresh_pairs, &|&(_, ref r): &(_, Ren)| &r);

            (Node(f.clone(), fresh_ast, export.clone()), renaming)
        }
        IncompleteNode(_) | Shape(_) => panic!("ICE: didn't think this was needed"),
        QuoteMore(ref body, pos) => {
            let (a, r) = freshen_binders(body);
            (QuoteMore(Box::new(a), pos), r.q_less(1))
        }
        QuoteLess(ref body, depth) => {
            let (a, r) = freshen_binders(body);
            (QuoteLess(Box::new(a), depth), r.q_more(depth))
        }
        ExtendEnv(ref sub, ref beta) => {
            // We're only looking at `Atom`s, so this is transparent
            let (new_sub, subst) = freshen_binders(&*sub);
            (ExtendEnv(Box::new(new_sub), beta.clone()), subst)
        }
    }
}

/// Like `freshen_binders`, but to unite two `Ast`s with identical structure (else returns `None`).
pub fn freshen_binders_with(lhs: &Ast, rhs: &Ast) -> Option<(Ast, Ren, Ast, Ren)> {
    match (lhs, rhs) {
        (&Trivial, &Trivial) | (&VariableReference(_), &VariableReference(_)) => {
            Some((lhs.clone(), Ren::new(), rhs.clone(), Ren::new()))
        }
        (&Atom(old_name_lhs), &Atom(old_name_rhs)) => {
            let new_name = old_name_lhs.freshen();
            Some((
                Atom(new_name),
                Ren::single(old_name_lhs, VariableReference(new_name)),
                Atom(new_name),
                Ren::single(old_name_rhs, VariableReference(new_name)),
            ))
        }
        // TODO: Handle matching `'[let (a,b) = ⋯]'` against the pattern `'[let ,[p], = ⋯]'` !!
        (
            &Node(ref f, ref parts_lhs, ref export),
            &Node(ref f_rhs, ref parts_rhs, ref export_rhs),
        ) => {
            if f != f_rhs || export != export_rhs {
                return None;
            }

            if export == &::beta::ExportBeta::Nothing {
                // short-circuit:
                return Some((lhs.clone(), Ren::new(), rhs.clone(), Ren::new()));
            }
            let exported = export.names_mentioned(); // Unmentioned atoms shouldn't be touched

            match freshen_binders_inside_node_with(parts_lhs, parts_rhs, &exported) {
                Some(fresh_pairs) => {
                    let fresh_ast_lhs = fresh_pairs.map(&mut |&(ref a, _, _, _)| a.clone());
                    let fresh_ast_rhs = fresh_pairs.map(&mut |&(_, _, ref a, _)| a.clone());
                    let ren_lhs = export.extract_from_mbe(&fresh_pairs, &|t: &(_, Ren, _, _)| &t.1);
                    let ren_rhs = export.extract_from_mbe(&fresh_pairs, &|t: &(_, _, _, Ren)| &t.3);
                    Some((
                        Node(f.clone(), fresh_ast_lhs, export.clone()),
                        ren_lhs,
                        Node(f.clone(), fresh_ast_rhs, export.clone()),
                        ren_rhs,
                    ))
                }
                None => None,
            }
        }
        (&QuoteMore(ref body_lhs, pos), &QuoteMore(ref body_rhs, pos_rhs)) if pos == pos_rhs => {
            match freshen_binders_with(&*body_lhs, &*body_rhs) {
                Some((n_lhs, ren_lhs, n_rhs, ren_rhs)) => Some((
                    QuoteMore(Box::new(n_lhs), pos),
                    ren_lhs.q_less(1),
                    QuoteMore(Box::new(n_rhs), pos),
                    ren_rhs.q_less(1),
                )),
                None => None,
            }
        }
        (&QuoteLess(ref body_lhs, depth), &QuoteLess(ref body_rhs, depth_rhs))
            if depth == depth_rhs =>
        {
            match freshen_binders_with(&*body_lhs, &*body_rhs) {
                Some((n_lhs, ren_lhs, n_rhs, ren_rhs)) => Some((
                    QuoteLess(Box::new(n_lhs), depth),
                    ren_lhs.q_more(depth),
                    QuoteLess(Box::new(n_rhs), depth),
                    ren_rhs.q_more(depth),
                )),
                None => None,
            }
        }
        (&IncompleteNode(_), _) | (&Shape(_), _) => panic!("ICE: didn't think this was needed"),
        (&ExtendEnv(ref sub_lhs, ref beta), &ExtendEnv(ref sub_rhs, ref beta_rhs)) => {
            if beta != beta_rhs {
                return None;
            }
            // We're only looking at `Atom`s, so this is transparent
            match freshen_binders_with(&*sub_lhs, &*sub_rhs) {
                Some((n_lhs, ren_lhs, n_rhs, ren_rhs)) => Some((
                    ExtendEnv(Box::new(n_lhs), beta.clone()),
                    ren_lhs,
                    ExtendEnv(Box::new(n_rhs), beta.clone()),
                    ren_rhs,
                )),
                None => None,
            }
        }
        _ => None, // Match failure
    }
}

#[test]
fn basic_substitution() {
    ::name::enable_fake_freshness(true);

    assert_eq!(
        substitute(
            &ast!({"Expr" "apply" : "rator" => (vr "a"), "rand" => [(vr "b"), (vr "c")]}),
            &assoc_n!("x" => ast!((vr "y")), "buchanan" => ast!((vr "lincoln")))
        ),
        ast!({"Expr" "apply" : "rator" => (vr "a"), "rand" => [(vr "b"), (vr "c")]})
    );

    assert_eq!(
        substitute(
            &ast!({"Expr" "apply" : "rator" => (vr "buchanan"),
                                    "rand" => [(vr "buchanan"), (vr "c")]}),
            &assoc_n!("x" => ast!((vr "y")), "buchanan" => ast!((vr "lincoln")))
        ),
        ast!({"Expr" "apply" : "rator" => (vr "lincoln"), "rand" => [(vr "lincoln"), (vr "c")]})
    );

    assert_eq!(
        substitute(
            &ast!({"Expr" "lambda" :
                "param" => ["b", "x"],
                "body" => (import [* ["param" : "[ignored]"]]
                    {"Expr" "apply" : "rator" => (vr "f"),
                                      "rand" => [(vr "a"), (vr "b"), (vr "c")]})}),
            &assoc_n!("a" => ast!((vr "A")), "b" => ast!((vr "B")), "c" => ast!((vr "C")))
        ),
        ast!({"Expr" "lambda" :
            "param" => ["b", "x"],
            "body" => (import [* ["param" : "[ignored]"]]
                {"Expr" "apply" : "rator" => (vr "f"),
                                  "rand" => [(vr "A"), (vr "b"), (vr "C")]})})
    );
}

#[test]
fn basic_binder_freshening() {
    ::name::enable_fake_freshness(true);

    assert_eq!(freshen_binders(&ast!((vr "a"))), (ast!((vr "a")), Ren::new()));

    assert_eq!(
        freshen_binders(&ast!("a")),
        (ast!("a🍅"), Ren::from(assoc_n!("a" => ast!((vr "a🍅")))))
    );

    assert_eq!(
        freshen_binders(&ast!({ "Pat" "enum_pat" => [* ["component"]] :
            "name" => "[ignored]", "component" => ["a", "b"] })),
        (
            ast!({ "Pat" "enum_pat" => [* ["component"]] :
            "name" => "[ignored]", "component" => ["a🍅", "b🍅"] }),
            Ren::from(assoc_n!("a" => ast!((vr "a🍅")), "b" => ast!((vr "b🍅"))))
        )
    );
}

#[test]
fn basic_freshening() {
    ::name::enable_fake_freshness(true);

    assert_eq!(
        freshen(&ast!({"Expr" "lambda" :
                "param" => ["a", "b"],
                "body" => (import [* ["param" : "[ignored]"]]
                    {"Expr" "apply" : "rator" => (vr "f"),
                                      "rand" => [(vr "a"), (vr "b"), (vr "c"), (vr "d")]})})),
        ast!({"Expr" "lambda" :
            "param" => ["a🍅", "b🍅"],
            "body" => (import [* ["param" : "[ignored]"]]
                {"Expr" "apply" : "rator" => (vr "f"),
                                  "rand" => [(vr "a🍅"), (vr "b🍅"), (vr "c"), (vr "d")]})})
    );

    assert_eq!(
        freshen(&ast!({"Expr" "match" :
            "scrutinee" => (vr "x"),
            "p" => [@"arm" "a", "b"],
            "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "a")),
                             (import ["p" = "scrutinee"] (vr "x"))]
        })),
        ast!({"Expr" "match" :
            "scrutinee" => (vr "x"),
            "p" => [@"arm" "a🍅", "b🍅"],
            "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "a🍅")),
                             (import ["p" = "scrutinee"] (vr "x"))]})
    );

    // Test that importing non-atoms works
    assert_eq!(
        freshen(&ast!({"Expr" "match" :
            "scrutinee" => (vr "x"),
            "p" => [@"arm" { "Pat" "enum_pat" => [* ["component"]] :
                "name" => "[ignored]", "component" => ["a"]
            }],
            "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "a"))]
        })),
        ast!({"Expr" "match" :
            "scrutinee" => (vr "x"),
            "p" => [@"arm" { "Pat" "enum_pat" => [* ["component"]] :
                "name" => "[ignored]", "component" => ["a🍅"]
            }],
            "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "a🍅"))]})
    );

    // TODO: test more!
}

#[test]
fn basic_freshening_with() {
    ::name::enable_fake_freshness(true);

    assert_eq!(
        freshen_with(&ast!({"Type" "Int" :}), &ast!({"Type" "Float" :})),
        (ast!({"Type" "Int" :}), ast!({"Type" "Float" :}))
    );

    assert_eq!(
        freshen_with(
            &ast!({"Expr" "lambda" :
                "param" => ["a", "b"],
                "body" => (import [* ["param" : "[ignored]"]]
                    {"Expr" "apply" : "rator" => (vr "f"),
                                      "rand" => [(vr "a"), (vr "b"), (vr "c"), (vr "d")]})}),
            &ast!({"Expr" "lambda" :
                "param" => ["j", "k"],
                "body" => (import [* ["param" : "[ignored]"]]
                    {"Expr" "apply" : "rator" => (vr "f"),
                                      "rand" => [(vr "j"), (vr "k"), (vr "x"), (vr "x")]})})
        ),
        (
            ast!({"Expr" "lambda" :
             "param" => ["a🍅", "b🍅"],
             "body" => (import [* ["param" : "[ignored]"]]
                 {"Expr" "apply" : "rator" => (vr "f"),
                                   "rand" => [(vr "a🍅"), (vr "b🍅"), (vr "c"), (vr "d")]})}),
            ast!({"Expr" "lambda" :
             "param" => ["a🍅", "b🍅"],
             "body" => (import [* ["param" : "[ignored]"]]
                 {"Expr" "apply" : "rator" => (vr "f"),
                                   "rand" => [(vr "a🍅"), (vr "b🍅"), (vr "x"), (vr "x")]})})
        )
    );

    assert_eq!(
        freshen_with(
            &ast!({"Expr" "match" :
                "scrutinee" => (vr "x"),
                "p" => [@"arm" { "Pat" "enum_pat" => [* ["component"]] :
                    "name" => "[ignored]", "component" => ["a"]
                }],
                "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "a"))]
            }),
            &ast!({"Expr" "match" :
                "scrutinee" => (vr "x"),
                "p" => [@"arm" { "Pat" "enum_pat" => [* ["component"]] :
                    "name" => "[ignored]", "component" => ["x"]
                }],
                "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "x"))]
            })
        ),
        (
            ast!({"Expr" "match" :
             "scrutinee" => (vr "x"),
             "p" => [@"arm" { "Pat" "enum_pat" => [* ["component"]] :
                 "name" => "[ignored]", "component" => ["a🍅"]
             }],
             "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "a🍅"))]}),
            ast!({"Expr" "match" :
              "scrutinee" => (vr "x"),
              "p" => [@"arm" { "Pat" "enum_pat" => [* ["component"]] :
                  "name" => "[ignored]", "component" => ["a🍅"]
              }],
              "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "a🍅"))]})
        )
    );

    // Terms that don't match are unaffected
    assert_eq!(
        freshen_with(
            &ast!({"Expr" "lambda" :
                  "param" => ["a", "b"],
                  "body" => (import [* ["param" : "[ignored]"]]
                      {"Expr" "apply" : "rator" => (vr "f"),
                                        "rand" => [(vr "a"), (vr "b"), (vr "c"), (vr "d")]})}),
            &ast!({"Expr" "lambda" :
                  "param" => ["abc"],
                  "body" => (import [* ["param" : "[ignored]"]]
                      {"Expr" "apply" : "rator" => (vr "f"),
                                        "rand" => [(vr "a"), (vr "b"), (vr "x"), (vr "x")]})})
        ),
        (
            ast!({"Expr" "lambda" :
              "param" => ["a", "b"],
              "body" => (import [* ["param" : "[ignored]"]]
                  {"Expr" "apply" : "rator" => (vr "f"),
                                    "rand" => [(vr "a"), (vr "b"), (vr "c"), (vr "d")]})}),
            ast!({"Expr" "lambda" :
              "param" => ["abc"],
              "body" => (import [* ["param" : "[ignored]"]]
                  {"Expr" "apply" : "rator" => (vr "f"),
                                    "rand" => [(vr "a"), (vr "b"), (vr "x"), (vr "x")]})})
        )
    );
}

#[test]
fn mu_substitution() {
    let trivial_mu = ast!( { "Type" "mu_type" : "param" => [(import [prot "param"] (vr "T"))],
                              "body" => (import [* [prot "param"]] (vr "T")) });
    assert_eq!(freshen(&trivial_mu), trivial_mu);

    assert_eq!(
        substitute(&trivial_mu, &assoc_n!("T" => ast!((vr "S")))),
        ast!( { "Type" "mu_type" : "param" => [(import [prot "param"] (vr "S"))],
                                   "body" => (import [* [prot "param"]] (vr "S")) })
    )
}

#[test]
fn alpha_quote_more_or_less() {
    ::name::enable_fake_freshness(true);

    assert_eq!(
        freshen(&ast!({"Expr" "lambda" :
                "param" => ["a", "b"],
                "body" => (import [* ["param" : "[ignored]"]]
                    (++ true {"Expr" "apply" : "rator" => (vr "f"),
                                               "rand" => [(vr "a"), (vr "b")]}))})),
        ast!({"Expr" "lambda" :
            "param" => ["a🍅", "b🍅"],
            "body" => (import [* ["param" : "[ignored]"]]
                (++ true {"Expr" "apply" : "rator" => (vr "f"),
                                           "rand" => [(vr "a"), (vr "b")]}))})
    );

    assert_eq!(
        freshen(&ast!({"Expr" "lambda" :
                "param" => ["a", "b"],
                "body" => (import [* ["param" : "[ignored]"]]
                    (++ true (-- 1 {"Expr" "apply" : "rator" => (vr "f"),
                                                     "rand" => [(vr "a"), (vr "b")]})))})),
        ast!({"Expr" "lambda" :
            "param" => ["a🍅", "b🍅"],
            "body" => (import [* ["param" : "[ignored]"]]
                (++ true (-- 1 {"Expr" "apply" : "rator" => (vr "f"),
                                                 "rand" => [(vr "a🍅"), (vr "b🍅")]})))})
    );
}
