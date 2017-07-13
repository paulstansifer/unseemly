// Alpha-equivalence utilities.
// Based on https://repository.library.northeastern.edu/files/neu:cj82mb52h

use name::*;
use util::mbe::EnvMBE;
use ast::Ast;
use ast::Ast::*;
use util::assoc::Assoc;
use std::collections::HashMap;


// TODO: at walk time, we must calculate the set of imported names
//  and enforce that the environment change matches.


// TODO: this isn't capture-avoiding
fn substitute_rec(node: &Ast, cur_node_contents: &EnvMBE<Ast>, env: &Assoc<Name, Ast>) -> Ast {
    print!("{:?} ({:?}) with {:?}\n", node, cur_node_contents, env);
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
pub fn substitute(node: &Ast, env: &Assoc<Name, Ast>) -> Ast {
    substitute_rec(node, &EnvMBE::new(), env)
}

/// Like `beta::names_mentioned`, but for all the imports in `parts`
fn mentioned_in_import(parts: &EnvMBE<Ast>) -> Vec<Name> {
    fn process_ast(a: &Ast, v: &mut Vec<Name>) {
        match *a {
            Node(_,_,_) => {} // new scope
            ExtendEnv(ref body, ref beta) => {
                let mut beta_mentions = beta.names_mentioned();
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

fn freshen_rec(node: &Ast, renamings: &EnvMBE<(Ast, Assoc<Name,Ast>)>, env: &Assoc<Name, Ast>) -> Ast {
    print!("FR: {:?}\nat: {:?}\n", node, renamings);
    //  `env` is used to update the references to those atoms to match
    match *node {
        Node(_, _, _) => {
            print!("subst...\n");
            substitute(node, env) }
        VariableReference(n) => {
            print!("→{:?}\n", env.find(&n));
            env.find(&n).unwrap_or(&node.clone()).clone()
        }
        ExtendEnv(ref body, ref beta) => {
            let new_env = env.set_assoc(&beta.extract_from_mbe(renamings));
            print!("EE: {:?} {:?}\n", body, new_env);

            ExtendEnv(Box::new(
                freshen_rec(body, renamings, &new_env)), beta.clone())
        }
        Atom(_) | Trivial | IncompleteNode(_) | Shape(_) => node.clone()
    }
}

thread_local! {
    pub static next_id: ::std::cell::RefCell<u32> = ::std::cell::RefCell::new(0);
}

// broken out for testing purposes
fn freshen_with_map(a: &Ast) -> Ast {
    match a {
        &Node(ref f, ref p, ref export) => {
            // Every part that gets mentioned inside this node...
            let mentioned = mentioned_in_import(p);
            // ...needs to have its binders freshend:
            let fresh_ast_and_rens = freshen_binders_inside_node(p, &mentioned);
            print!("faar: {:?}\n", fresh_ast_and_rens);

            Node(f.clone(),
                 fresh_ast_and_rens.marched_map(
                     &mut |_, marched: &EnvMBE<(Ast, Assoc<Name, Ast>)>, &(ref part, _)|
                         freshen_rec(part, marched, &Assoc::new())),
                 export.clone())
        }
        non_node => non_node.clone()
    }
}

pub fn freshen(a: &Ast) -> Ast {
    //freshen_with_map(a, &mut HashMap::new())
    a.clone()
}

pub fn freshen_binders_inside_node(parts: &EnvMBE<Ast>, mentioned: &Vec<Name>)
        -> EnvMBE<(Ast, Assoc<Name, Ast>)> {
    parts.named_map(
        &mut |n: &Name, a: &Ast| {
            if mentioned.contains(n) { freshen_binders(a) } else { (a.clone(), Assoc::new()) }})
}


pub fn freshen_binders(a: &Ast) -> (Ast, Assoc<Name, Ast>){
    match *a {
        Trivial | VariableReference(_) => (a.clone(), Assoc::new()),
        Atom(old_name) => {
            next_id.with(|n_i| {
                let new_name = n(&format!("🍅{}{}", old_name, *n_i.borrow()));
                *n_i.borrow_mut() += 1;
                (Atom(new_name), Assoc::new().set(old_name, VariableReference(new_name)))
            })
        }
        Node(ref f, ref parts, ref export) => {
            print!("FB:n {:?}\n", a);
            if export == &::beta::ExportBeta::Nothing {
                return (a.clone(), Assoc::new()); // short-circuit (should this at least warn?)
            }
            let exported = export.names_mentioned(); // Unmentioned atoms shouldn't be touched

            let fresh_pairs = freshen_binders_inside_node(parts, &exported);
            let fresh_ast = fresh_pairs.map(&mut |&(ref a, _) : &(Ast, _)| a.clone());
            let renaming = export.extract_from_mbe(&fresh_pairs);

            (Node(f.clone(), fresh_ast, export.clone()), renaming)
        }
        IncompleteNode(_) | Shape(_) => { panic!("ICE: didn't think this was needed") }
        ExtendEnv(ref sub, ref beta) => { // We're only looking at `Atom`s, so this is transparent
            let (new_sub, subst) = freshen_binders(&*sub);
            (ExtendEnv(Box::new(new_sub), beta.clone()), subst)
        }
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
                    {"expr" "apply" : "??" => [(vr "a"), (vr "b"), (vr "c")]})}),
            &assoc_n!("a" => ast!((vr "A")), "b" => ast!((vr "B")), "c" => ast!((vr "C")))),
        ast!({"expr" "lambda" :
            "param" => ["b", "x"],
            "body" => (import [* ["param" : "[ignored]"]]
                {"expr" "apply" : "??" => [(vr "A"), (vr "b"), (vr "C")]})}));
}

#[test]
fn basic_binder_freshening() {
    next_id.with(|n_i| { *n_i.borrow_mut() = 0 }); // Make freshening determinisitic

    assert_eq!(freshen_binders(&ast!((vr "a"))), (ast!((vr "a")), assoc_n!()));

    assert_eq!(freshen_binders(&ast!("a")), (ast!("🍅a0"), assoc_n!("a" => ast!((vr "🍅a0")))));

    // I just can't figure out how to add export syntax to `ast!`
    assert_eq!(freshen_binders(
        &::ast::Node(::core_forms::find_core_form("pat", "enum_pat"),
            mbe!("name" => "[ignored]", "component" => ["a", "b"]),
            ebeta!([* ["component"]]))),
        (::ast::Node(::core_forms::find_core_form("pat", "enum_pat"),
            mbe!("name" => "[ignored]", "component" => ["🍅a1", "🍅b2"]),
            ebeta!([* ["component"]])),
        assoc_n!("a" => ast!((vr "🍅a1")), "b" => ast!((vr "🍅b2")))));
}


#[test]
fn basic_freshening() {
    next_id.with(|n_i| { *n_i.borrow_mut() = 0 }); // Make freshening determinisitic

    assert_eq!(
        freshen_with_map(
            &ast!({"expr" "lambda" :
                "param" => ["a", "b"],
                "body" => (import [* ["param" : "[ignored]"]]
                    {"expr" "apply" : "??" => [(vr "a"), (vr "b"), (vr "c"), (vr "d")]})})),
        ast!({"expr" "lambda" :
            "param" => ["🍅a0", "🍅b1"],
            "body" => (import [* ["param" : "[ignored]"]]
                {"expr" "apply" : "??" => [(vr "🍅a0"), (vr "🍅b1"), (vr "c"), (vr "d")]})}));

    next_id.with(|n_i| { *n_i.borrow_mut() = 0 }); // Make freshening determinisitic

    assert_eq!(
        freshen_with_map(
            &ast!({"expr" "match" :
                "scrutinee" => (vr "x"),
                "p" => [@"arm" "a", "b"],
                "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "a")),
                                 (import ["p" = "scrutinee"] (vr "x"))]
            })),
        ast!({"expr" "match" :
            "scrutinee" => (vr "x"),
            "p" => [@"arm" "🍅a0", "🍅b1"],
            "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "🍅a0")),
                             (import ["p" = "scrutinee"] (vr "x"))]}));

    next_id.with(|n_i| { *n_i.borrow_mut() = 0 }); // Make freshening determinisitic

    // TODO: For this to work, negative terms need to bottom out at `Atom`s,
    //  not `VariableReference`s!!
    // Test that importing non-atoms works
    assert_eq!(
        freshen_with_map(
            &ast!({"expr" "match" :
                "scrutinee" => (vr "x"),
                "p" => [@"arm" /*{"pat" "enum_pat" : "name" => "asdf", "component" => ["a"]}*/
                (, ::ast::Node(::core_forms::find_core_form("pat", "enum_pat"),
                    mbe!("name" => "[ignored]", "component" => ["a"]),
                    ebeta!([* ["component"]])))
                ],
                "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "a"))]
            })),
        ast!({"expr" "match" :
            "scrutinee" => (vr "x"),
            "p" => [@"arm" /* {"pat" "enum_pat" : "name" => "asdf", "component" => ["🍅a0"]} */
            (, ::ast::Node(::core_forms::find_core_form("pat", "enum_pat"),
                mbe!("name" => "[ignored]", "component" => ["🍅a0"]),
                ebeta!([* ["component"]])))
            ],
            "arm" => [@"arm" (import ["p" = "scrutinee"] (vr "🍅a0"))]}));

    //TODO: test more!

}
