// Alpha-equivalence utilities.
// Based on https://repository.library.northeastern.edu/files/neu:cj82mb52h
//  ...however, freshening is simplified because we don't have "export"s
//   (the ability for `Node`s to be treated as a binder).
//  The fact that we have MBE makes exports less important;
//   one can create complex strucutres inside a single `Node`.

use name::*;
use util::mbe::EnvMBE;
use ast::Ast;
use ast::Ast::*;
use util::assoc::Assoc;
use std::collections::HashMap;


// TODO: this isn't capture-avoiding
fn substitute_rec(node: &Ast, cur_node_contents: &EnvMBE<Ast>, env: &Assoc<Name, Ast>) -> Ast {
    match *node {
        Node(ref f, ref new_parts) => {
            //let new_cnc = parts.clone();
            Node(f.clone(), new_parts.map(&mut |part: &Ast| substitute_rec(part, new_parts, env)))
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

pub fn substitute(node: &Ast, env: &Assoc<Name, Ast>) -> Ast {
    substitute_rec(node, &EnvMBE::new(), env)
}

fn freshen_rec(node: &Ast, cur_node_contents: &EnvMBE<Ast>, cur_leaf: Name,
               atom_memo: &mut HashMap<(Name, Name), Name>, env: &Assoc<Name, Ast>) -> Ast {
    // `atom_memo` is used to freshen the atoms;
    //  `env` is used to update the references to those atoms to match
    match *node {
        Node(_, _) => {
             substitute(node, env) }
        VariableReference(n) => {
            env.find(&n).unwrap_or(&node.clone()).clone()
        }
        ExtendEnv(ref body, ref beta) => {
            let new_env = env.set_assoc(
                &::beta::freshening_from_beta(beta, cur_node_contents, atom_memo));

            ExtendEnv(Box::new(
                freshen_rec(body, cur_node_contents, cur_leaf, atom_memo, &new_env)), beta.clone())
        }
        Atom(old_name) => {
            Atom(*atom_memo.get(&(cur_leaf, old_name)).unwrap_or(&old_name))
        }
        _ => node.clone()
    }
}

// broken out for testing purposes
fn freshen_with_map(a: Ast, mut atom_memo: &mut HashMap<(Name, Name), Name>) -> Ast {
    match a {
        Node(f, new_p) => {
            Node(f.clone(),
                 new_p.map_with_leaf_names(
                     &mut |ln: &Name, part: &Ast|
                         freshen_rec(part, &new_p, *ln, &mut atom_memo, &Assoc::new())))
        }
        non_node => non_node
    }
}

pub fn freshen(a: Ast) -> Ast {
    freshen_with_map(a, &mut HashMap::new())
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
fn basic_freshening() {
    // HACK: We pre-seed the `atom_memo` to get a determinisitic freshening
    let mut memo = HashMap::new();
    memo.insert((n("param"), n("a")), n("A"));
    memo.insert((n("param"), n("b")), n("B"));


    assert_eq!(
        freshen_with_map(
            ast!({"expr" "lambda" :
                "param" => ["a", "b"],
                "body" => (import [* ["param" : "[ignored]"]]
                    {"expr" "apply" : "??" => [(vr "a"), (vr "b"), (vr "c"), (vr "d")]})}),
            &mut memo),
        ast!({"expr" "lambda" :
            "param" => ["A", "B"],
            "body" => (import [* ["param" : "[ignored]"]]
                {"expr" "apply" : "??" => [(vr "A"), (vr "B"), (vr "c"), (vr "d")]})}));
                
    //TODO: test more!

}
