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

/*
fn freshen(node: &Ast, cur_node_contents: &EnvMBE<Ast>,
        node_memo: &mut HashMap<Name, Name>, env: &Assoc<Name, Ast>) -> Ast {
    match *node {
        Node(ref f, ref new_parts) => {
            //let new_cnc = parts.clone();
            Node(f.clone(),
                 new_parts.map(&mut |part: &Ast| freshen(part, new_parts, node_memo, env)))
        }
        VariableReference(n) => {
            env.find(&n).unwrap_or(&node.clone()).clone()
        }
        ExtendEnv(ref body, ref beta) => {
            let mut new_env = env.clone();

            for bound_name in ::beta::keys_from_beta(beta, cur_node_contents) {
                new_env = new_env.unset(&bound_name);
            }
            ExtendEnv(Box::new(freshen(body, cur_node_contents, node_memo, &new_env)), beta.clone())
        }
        Atom()
        _ => node.clone()
    }
}
*/


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
                    {"expr" "apply" : "rator" => [(vr "a"), (vr "b"), (vr "c")]})}),
            &assoc_n!("a" => ast!((vr "A")), "b" => ast!((vr "B")), "c" => ast!((vr "C")))),
        ast!({"expr" "lambda" :
            "param" => ["b", "x"],
            "body" => (import [* ["param" : "[ignored]"]]
                {"expr" "apply" : "rator" => [(vr "A"), (vr "b"), (vr "C")]})}));
}
