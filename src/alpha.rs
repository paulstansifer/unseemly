// Alpha-equivalence utilities.
// Based on https://repository.library.northeastern.edu/files/neu:cj82mb52h

// `freshen` gets a value ready for destructuring.
// `freshen_rec` gets a value and its pattern ready for destructuring.

use name::*;
use util::mbe::EnvMBE;
use ast::Ast;
use ast::Ast::*;
use util::assoc::Assoc;
use std::collections::HashMap;

// Renaming:
type Ren = Assoc<Name, Ast>;


// TODO: this isn't capture-avoiding (and shouldn't be, when called by `freshen_rec`)
fn substitute_rec(node: &Ast, cur_node_contents: &EnvMBE<Ast>, env: &Ren) -> Ast {
    match *node {
        Node(ref f, ref new_parts, ref export) => {
            //let new_cnc = parts.clone();
            Node(f.clone(),
                 new_parts.marched_map(
                     &mut |_, marched_parts: &EnvMBE<Ast>, part: &Ast|
                         substitute_rec(part, marched_parts, env)),
                 export.clone())
        }
        VariableReference(n) => {
            env.find(&n).unwrap_or(&node.clone()).clone()
        }
        ExtendEnv(ref body, ref beta) => {
            let mut new_env = env.clone();
            for bound_name in ::beta::keys_from_beta(beta, cur_node_contents) {
                new_env = new_env.unset(&bound_name);
            }
            ExtendEnv(Box::new(substitute_rec(body, cur_node_contents, &new_env)), beta.clone())
        }
        _ => node.clone()
    }
}

/// Substitute `VariableReference`s in `node`, according to `env`.
pub fn substitute(node: &Ast, env: &Ren) -> Ast {
    substitute_rec(node, &EnvMBE::new(), env)
}

/// Like `beta::names_mentioned`, but for all the imports in `parts`
fn mentioned_in_import(parts: &EnvMBE<Ast>) -> Vec<Name> {
    fn process_ast(a: &Ast, v: &mut Vec<Name>) {
        match *a {
            Node(_,_,_) => {} // new scope
            ExtendEnv(ref body, ref beta) => {
                let mut beta_mentions = beta.names_mentioned_and_bound();
                v.append(&mut beta_mentions);
                process_ast(&*body, v);
            }
            Trivial | Atom(_) | VariableReference(_) => {} // no beta
            Shape(_) | IncompleteNode(_) => { panic!("ICE: shouldn't be needed") }
        }
    }

    let mut res = vec![];
    parts.map(&mut |a| { process_ast(a, &mut res) });
    res
}

fn freshen_rec(node: &Ast, renamings: &EnvMBE<(Ast, Ren)>, env: &Ren) -> Ast {
    //  `env` is used to update the references to those atoms to match
    match *node {
        Node(_, _, _) => { substitute(node, env) }
        VariableReference(n) => {
            env.find(&n).unwrap_or(&node.clone()).clone()
        }
        ExtendEnv(ref body, ref beta) => {
            let new_env = env.set_assoc(&beta.extract_from_mbe(renamings, &|x| &x.1));

            ExtendEnv(Box::new(
                freshen_rec(body, renamings, &new_env)), beta.clone())
        }
        Atom(_) | Trivial | IncompleteNode(_) | Shape(_) => node.clone()
    }
}

thread_local! {
    pub static freshening_enabled: ::std::cell::RefCell<bool> = ::std::cell::RefCell::new(true);
    pub static next_id: ::std::cell::RefCell<u32> = ::std::cell::RefCell::new(0);
}

pub fn freshen(a: &Ast) -> Ast { // TODO: I think this shouldn't take a reference for performance
    if freshening_enabled.with(|f| *f.borrow()) {
        match a {
            &Node(ref f, ref p, ref export) => {
                // Every part that gets mentioned inside this node...
                let mentioned = mentioned_in_import(p);
                // ...needs to have its binders freshend:
                let fresh_ast_and_rens = freshen_binders_inside_node(p, &mentioned);

                Node(f.clone(),
                    fresh_ast_and_rens.marched_map(
                        &mut |_, marched: &EnvMBE<(Ast, Ren)>, &(ref part, _)|
                            freshen_rec(part, marched, &Assoc::new())),
                            export.clone())
            }
            non_node => non_node.clone()
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
                if f != f_rhs || export != export_rhs { return (lhs.clone(), rhs.clone()); }
                // Every part that gets mentioned inside this node...
                let mentioned = mentioned_in_import(p_lhs);
                //  (if it matters which `p_{l,r}hs` we used, the match below will be `None`)
                // ...needs to have its binders freshend:
                match freshen_binders_inside_node_with(p_lhs, p_rhs, &mentioned) {
                    Some(fresh_ast_and_rens) => {
                        let new_p_lhs = fresh_ast_and_rens.marched_map(
                            &mut |_, marched: &EnvMBE<(Ast, Ren, Ast, Ren)>, &(ref parts, _, _, _)|
                                freshen_rec(parts,
                                            &marched.map(&mut |q| (q.0.clone(), q.1.clone())),
                                            &Assoc::new()));
                        let new_p_rhs = fresh_ast_and_rens.marched_map(
                            &mut |_, marched: &EnvMBE<(Ast, Ren, Ast, Ren)>, &(_, _, ref parts, _)|
                                freshen_rec(parts,
                                            &marched.map(&mut |q| (q.2.clone(), q.3.clone())),
                                            &Assoc::new()));
                        (Node(f.clone(), new_p_lhs, export.clone()),
                         Node(f.clone(), new_p_rhs, export.clone()))

                    }
                    None => (lhs.clone(), rhs.clone()) // No destructuring will be performed!
                }
            }
            _ => (lhs.clone(), rhs.clone()) // No binding
        }
    } else {
        (lhs.clone(), rhs.clone()) // Freshening is disabled
    }
}


pub fn freshen_binders_inside_node(parts: &EnvMBE<Ast>, mentioned: &Vec<Name>)
        -> EnvMBE<(Ast, Ren)> {
    parts.named_map(
        &mut |n: &Name, a: &Ast| {
            if mentioned.contains(n) { freshen_binders(a) } else { (a.clone(), Assoc::new()) }})
}

pub fn freshen_binders_inside_node_with(p_lhs: &EnvMBE<Ast>, p_rhs: &EnvMBE<Ast>, men: &Vec<Name>)
        -> Option<EnvMBE<(Ast, Ren, Ast, Ren)>> {
    if ! p_lhs.can_map_with(p_rhs) { return None; }
    p_lhs.named_map_with(
        p_rhs,
        &mut |n: &Name, a_lhs: &Ast, a_rhs: &Ast| {
            if men.contains(n) {
                freshen_binders_with(a_lhs, a_rhs).ok_or(())
            } else {
                Ok((a_lhs.clone(), Assoc::new(), a_rhs.clone(), Assoc::new()))
            }
        }).lift_result().ok()
}


/// Returns an `Ast` like `a`, but with fresh `Atom`s
///  and a map to change references in the same manner
pub fn freshen_binders(a: &Ast) -> (Ast, Ren){
    match *a {
        Trivial | VariableReference(_) => (a.clone(), Assoc::new()),
        Atom(old_name) => {
            next_id.with(|n_i| {
                let new_name = n(&format!("{}🍅{}", old_name, *n_i.borrow()));
                *n_i.borrow_mut() += 1;
                (Atom(new_name), Assoc::new().set(old_name, VariableReference(new_name)))
            })
        }
        Node(ref f, ref parts, ref export) => {
            if export == &::beta::ExportBeta::Nothing {
                return (a.clone(), Assoc::new()); // short-circuit (should this at least warn?)
            }
            let exported = export.names_mentioned(); // Unmentioned atoms shouldn't be touched

            let fresh_pairs = freshen_binders_inside_node(parts, &exported);
            let fresh_ast = fresh_pairs.map(&mut |&(ref a, _) : &(Ast, _)| a.clone());
            let renaming = export.extract_from_mbe(&fresh_pairs, &|x| &x.1);

            (Node(f.clone(), fresh_ast, export.clone()), renaming)
        }
        IncompleteNode(_) | Shape(_) => { panic!("ICE: didn't think this was needed") }
        ExtendEnv(ref sub, ref beta) => { // We're only looking at `Atom`s, so this is transparent
            let (new_sub, subst) = freshen_binders(&*sub);
            (ExtendEnv(Box::new(new_sub), beta.clone()), subst)
        }
    }
}

/// Like `freshen_binders`, but to unite two `Ast`s with identical structure (else returns `None`).
pub fn freshen_binders_with(lhs: &Ast, rhs: &Ast) -> Option<(Ast, Ren, Ast, Ren)>{
    match (lhs, rhs) {
        (&Trivial, &Trivial) | (&VariableReference(_), &VariableReference(_)) => {
            Some((lhs.clone(), Assoc::new(), rhs.clone(), Assoc::new()))
        },
        (&Atom(old_name_lhs), &Atom(old_name_rhs)) => {
            next_id.with(|n_i| {
                let new_name = n(&format!("{}🍅{}", old_name_lhs, *n_i.borrow()));
                *n_i.borrow_mut() += 1;
                Some((Atom(new_name), Assoc::new().set(old_name_lhs, VariableReference(new_name)),
                      Atom(new_name), Assoc::new().set(old_name_rhs, VariableReference(new_name))))
            })
        }
        // TODO: Handle matching `'[let (a,b) = ⋯]'` against the pattern `'[let ,[p], = ⋯]'` !!
        (&Node(ref f, ref parts_lhs, ref export),
         &Node(ref f_rhs, ref parts_rhs, ref export_rhs)) => {
            if f != f_rhs || export != export_rhs { return None }

            if export == &::beta::ExportBeta::Nothing { // short-circuit:
                return Some((lhs.clone(), Assoc::new(), rhs.clone(), Assoc::new()));
            }
            let exported = export.names_mentioned(); // Unmentioned atoms shouldn't be touched

            match freshen_binders_inside_node_with(parts_lhs, parts_rhs, &exported) {
                Some(fresh_pairs) => {
                    let fresh_ast_lhs = fresh_pairs.map(&mut |&(ref a, _, _, _)| a.clone());
                    let fresh_ast_rhs = fresh_pairs.map(&mut |&(_, _, ref a, _)| a.clone());
                    let ren_lhs = export.extract_from_mbe(&fresh_pairs, &|t| &t.1);
                    let ren_rhs = export.extract_from_mbe(&fresh_pairs, &|t| &t.3);
                    Some((Node(f.clone(), fresh_ast_lhs, export.clone()), ren_lhs,
                          Node(f.clone(), fresh_ast_rhs, export.clone()), ren_rhs))
                }
                None => { None }
            }
        }
        (&IncompleteNode(_), _) | (&Shape(_), _) => { panic!("ICE: didn't think this was needed") }
        (&ExtendEnv(ref sub_lhs, ref beta), &ExtendEnv(ref sub_rhs, ref beta_rhs)) => {
            if beta != beta_rhs { return None; }
            // We're only looking at `Atom`s, so this is transparent
            match freshen_binders_with(&*sub_lhs, &*sub_rhs) {
                Some((n_lhs, ren_lhs, n_rhs, ren_rhs)) => {
                    Some((ExtendEnv(Box::new(n_lhs), beta.clone()), ren_lhs,
                          ExtendEnv(Box::new(n_rhs), beta.clone()), ren_rhs))
                }
                None => None
            }
        }
        _ => None // Match failure
    }
}


#[test]
fn basic_substitution() {
    assert_eq!(substitute(
            &ast!({"expr" "apply" : "rator" => (vr "a"), "rand" => [(vr "b"), (vr "c")]}),
            &assoc_n!("x" => ast!((vr "y")), "buchanan" => ast!((vr "lincoln")))),
        ast!({"expr" "apply" : "rator" => (vr "a"), "rand" => [(vr "b"), (vr "c")]}));

    assert_eq!(substitute(
            &ast!({"expr" "apply" : "rator" => (vr "buchanan"),
                                    "rand" => [(vr "buchanan"), (vr "c")]}),
            &assoc_n!("x" => ast!((vr "y")), "buchanan" => ast!((vr "lincoln")))),
        ast!({"expr" "apply" : "rator" => (vr "lincoln"), "rand" => [(vr "lincoln"), (vr "c")]}));


    assert_eq!(substitute(
            &ast!({"expr" "lambda" :
                "param" => ["b", "x"],
                "body" => (import [* ["param" : "[ignored]"]]
                    {"expr" "apply" : "rator" => (vr "f"),
                                      "rand" => [(vr "a"), (vr "b"), (vr "c")]})}),
            &assoc_n!("a" => ast!((vr "A")), "b" => ast!((vr "B")), "c" => ast!((vr "C")))),
        ast!({"expr" "lambda" :
            "param" => ["b", "x"],
            "body" => (import [* ["param" : "[ignored]"]]
                {"expr" "apply" : "rator" => (vr "f"),
                                  "rand" => [(vr "A"), (vr "b"), (vr "C")]})}));
}

#[test]
fn basic_binder_freshening() {
    next_id.with(|n_i| { *n_i.borrow_mut() = 0 }); // Make freshening determinisitic

    assert_eq!(freshen_binders(&ast!((vr "a"))), (ast!((vr "a")), assoc_n!()));

    assert_eq!(freshen_binders(&ast!("a")), (ast!("a🍅0"), assoc_n!("a" => ast!((vr "a🍅0")))));

    assert_eq!(freshen_binders(
        &ast!({ "pat" "enum_pat" => [* ["component"]] :
            "name" => "[ignored]", "component" => ["a", "b"] })),
        (ast!({ "pat" "enum_pat" => [* ["component"]] :
            "name" => "[ignored]", "component" => ["a🍅1", "b🍅2"] }),
        assoc_n!("a" => ast!((vr "a🍅1")), "b" => ast!((vr "b🍅2")))));
}


#[test]
fn basic_freshening() {
    next_id.with(|n_i| { *n_i.borrow_mut() = 0 }); // Make freshening determinisitic

    assert_eq!(
        freshen(
            &ast!({"expr" "lambda" :
                "param" => ["a", "b"],
                "body" => (import [* ["param" : "[ignored]"]]
                    {"expr" "apply" : "rator" => (vr "f"),
                                      "rand" => [(vr "a"), (vr "b"), (vr "c"), (vr "d")]})})),
        ast!({"expr" "lambda" :
            "param" => ["a🍅0", "b🍅1"],
            "body" => (import [* ["param" : "[ignored]"]]
                {"expr" "apply" : "rator" => (vr "f"),
                                  "rand" => [(vr "a🍅0"), (vr "b🍅1"), (vr "c"), (vr "d")]})}));

    next_id.with(|n_i| { *n_i.borrow_mut() = 0 }); // Make freshening determinisitic

    assert_eq!(
        freshen(
            &ast!({"expr" "match" :
                "scrutinee" => (vr "x"),
                "p" => [@"arm" "a", "b"],
                "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "a")),
                                 (import ["p" = "scrutinee"] (vr "x"))]
            })),
        ast!({"expr" "match" :
            "scrutinee" => (vr "x"),
            "p" => [@"arm" "a🍅0", "b🍅1"],
            "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "a🍅0")),
                             (import ["p" = "scrutinee"] (vr "x"))]}));

    next_id.with(|n_i| { *n_i.borrow_mut() = 0 }); // Make freshening determinisitic

    // Test that importing non-atoms works
    assert_eq!(
        freshen(
            &ast!({"expr" "match" :
                "scrutinee" => (vr "x"),
                "p" => [@"arm" { "pat" "enum_pat" => [* ["component"]] :
                    "name" => "[ignored]", "component" => ["a"]
                }],
                "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "a"))]
            })),
        ast!({"expr" "match" :
            "scrutinee" => (vr "x"),
            "p" => [@"arm" { "pat" "enum_pat" => [* ["component"]] :
                "name" => "[ignored]", "component" => ["a🍅0"]
            }],
            "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "a🍅0"))]}));

    //TODO: test more!
}

#[test]
fn basic_freshening_with() {
    next_id.with(|n_i| { *n_i.borrow_mut() = 0 }); // Make freshening determinisitic

    assert_eq!(
        freshen_with(&ast!({"type" "Int" :}), &ast!({"type" "Float" :})),
        (ast!({"type" "Int" :}), ast!({"type" "Float" :})));

    next_id.with(|n_i| { *n_i.borrow_mut() = 0 }); // Make freshening determinisitic

    assert_eq!(
        freshen_with(
            &ast!({"expr" "lambda" :
                "param" => ["a", "b"],
                "body" => (import [* ["param" : "[ignored]"]]
                    {"expr" "apply" : "rator" => (vr "f"),
                                      "rand" => [(vr "a"), (vr "b"), (vr "c"), (vr "d")]})}),
            &ast!({"expr" "lambda" :
                "param" => ["aaa", "bbb"],
                "body" => (import [* ["param" : "[ignored]"]]
                    {"expr" "apply" : "rator" => (vr "f"),
                                      "rand" => [(vr "aaa"), (vr "bbb"), (vr "x"), (vr "x")]})})),

        (ast!({"expr" "lambda" :
             "param" => ["a🍅0", "b🍅1"],
             "body" => (import [* ["param" : "[ignored]"]]
                 {"expr" "apply" : "rator" => (vr "f"),
                                   "rand" => [(vr "a🍅0"), (vr "b🍅1"), (vr "c"), (vr "d")]})}),
         ast!({"expr" "lambda" :
             "param" => ["a🍅0", "b🍅1"],
             "body" => (import [* ["param" : "[ignored]"]]
                 {"expr" "apply" : "rator" => (vr "f"),
                                   "rand" => [(vr "a🍅0"), (vr "b🍅1"), (vr "x"), (vr "x")]})})));

    next_id.with(|n_i| { *n_i.borrow_mut() = 0 }); // Make freshening determinisitic

    assert_eq!(
        freshen_with(
            &ast!({"expr" "match" :
                "scrutinee" => (vr "x"),
                "p" => [@"arm" { "pat" "enum_pat" => [* ["component"]] :
                    "name" => "[ignored]", "component" => ["a"]
                }],
                "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "a"))]
            }),
            &ast!({"expr" "match" :
                "scrutinee" => (vr "x"),
                "p" => [@"arm" { "pat" "enum_pat" => [* ["component"]] :
                    "name" => "[ignored]", "component" => ["aaa"]
                }],
                "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "aaa"))]
            })),
        (ast!({"expr" "match" :
             "scrutinee" => (vr "x"),
             "p" => [@"arm" { "pat" "enum_pat" => [* ["component"]] :
                 "name" => "[ignored]", "component" => ["a🍅0"]
             }],
             "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "a🍅0"))]}),
         ast!({"expr" "match" :
              "scrutinee" => (vr "x"),
              "p" => [@"arm" { "pat" "enum_pat" => [* ["component"]] :
                  "name" => "[ignored]", "component" => ["a🍅0"]
              }],
              "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "a🍅0"))]})));

      next_id.with(|n_i| { *n_i.borrow_mut() = 0 }); // Make freshening determinisitic

      // Terms that don't match are unaffected
      assert_eq!(
          freshen_with(
              &ast!({"expr" "lambda" :
                  "param" => ["a", "b"],
                  "body" => (import [* ["param" : "[ignored]"]]
                      {"expr" "apply" : "rator" => (vr "f"),
                                        "rand" => [(vr "a"), (vr "b"), (vr "c"), (vr "d")]})}),
              &ast!({"expr" "lambda" :
                  "param" => ["abc"],
                  "body" => (import [* ["param" : "[ignored]"]]
                      {"expr" "apply" : "rator" => (vr "f"),
                                        "rand" => [(vr "a"), (vr "b"), (vr "x"), (vr "x")]})})),
          (ast!({"expr" "lambda" :
              "param" => ["a", "b"],
              "body" => (import [* ["param" : "[ignored]"]]
                  {"expr" "apply" : "rator" => (vr "f"),
                                    "rand" => [(vr "a"), (vr "b"), (vr "c"), (vr "d")]})}),
           ast!({"expr" "lambda" :
              "param" => ["abc"],
              "body" => (import [* ["param" : "[ignored]"]]
                  {"expr" "apply" : "rator" => (vr "f"),
                                    "rand" => [(vr "a"), (vr "b"), (vr "x"), (vr "x")]})})));
}
