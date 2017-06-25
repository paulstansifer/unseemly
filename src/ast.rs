/*!
 * This abstract syntax tree is *really* abstract.
 * By necessity, it's not tied to any specific language.
 * "Normal" language forms all correspond to `Node`, and their meaning comes from their `Form`.
 */

#![macro_use]

use util::mbe::EnvMBE;
use name::*;
use beta::Beta;
use std::iter;
use std::fmt;
use std::rc::Rc;
use form::Form;
use ast;

custom_derive! {
    #[derive(Clone, PartialEq, Reifiable)]
    pub enum Ast {
        Trivial,
        /// TODO: Are we going to have a proper reference/binder dichotomy, or something weird?
        Atom(Name),
        VariableReference(Name),
        Shape(Vec<Ast>),

        /// A meaningful chunk of syntax, governed by a form, containing an environment
        Node(Rc<Form>, EnvMBE<Ast>),

        /// For parsing purposes.
        IncompleteNode(EnvMBE<Ast>),

        /// Variable binding
        ExtendEnv(Box<Ast>, Beta)
    }
}

pub use self::Ast::*;

impl fmt::Debug for Ast {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Trivial => { write!(f, "⨉") },
            Atom(ref n) => { write!(f, "∘{:?}∘", n) },
            VariableReference(ref v) => { write!(f, "{:?}", v) }
            Shape(ref v) => {
                try!(write!(f, "("));
                let mut first = true;
                for elt in v {
                    if !first { try!(write!(f, " ")) }
                    try!(elt.fmt(f));
                    first = false;
                }
                write!(f, ")")
            },
            Node(ref form, ref body) => {
                write!(f, "{{ ({}); {:?} }}", form.name.sp(), body)
            }
            IncompleteNode(ref body) => {
                write!(f, "{{ INCOMPLETE; {:?} }}", body)
            }
            ExtendEnv(ref body, ref beta) => {
                write!(f, "{:?}↓{:?}", body, beta)
            }
        }
    }
}


impl Ast {
    // TODO: this ought to at least warn if we're losing anything other than `Shape`
    pub fn flatten(&self) -> EnvMBE<Ast> {
        match *self {
            Trivial => EnvMBE::new(),
            Atom(_) => EnvMBE::new(),
            VariableReference(_) => EnvMBE::new(),
            Shape(ref v) => {
                let mut accum = EnvMBE::new();
                for sub_a in v {
                    accum = accum.combine_overriding(&sub_a.flatten())
                }
                accum
            },
            IncompleteNode(ref env) => { env.clone() }
            Node(ref _f, ref _body) => {
                // TODO: think about what should happen when
                //  `Scope` contains a `Scope` without an intervening `Named`
                panic!("I don't know what to do here!")
            },
            ExtendEnv(ref body, _) => body.flatten()
        }
    }
}

// This is used by combine::many, which is used by the Star parser
impl iter::FromIterator<Ast> for Ast {
    fn from_iter<I: IntoIterator<Item=Ast>>(i: I) -> Self {
        IncompleteNode(
            EnvMBE::new_from_anon_repeat(
                i.into_iter().map(|a| a.flatten()).collect()))
    }
}


use std::iter::FromIterator;



/*
 * This is also sort of a test of MBE, since we need `Ast`s to make them with the macros
 *
 * Suppose we have the following series of `Ast`s:
 * [b = 8] [a = [1 2], b = 8] [a = [3 4 5], b = 8]
 *
 * We should turn them into the following `Ast`
 * [a = [[] [1 2] [3 4 5]], b = [8 8 8]]
 */
#[test]
fn combine_from_kleene_star() {
    let parse_parts = vec![ast!({ - "b" => "8.0"}),
                           ast!({ - "a" => ["1", "2"], "b" => "8.1"}),
                           ast!({ - "a" => ["1", "2", "3"], "b" => "8.2"})];
    let parsed = Ast::from_iter(parse_parts);

    let mut expected_mbe =
        mbe!("a" => [@"triple" [], ["1", "2"], ["1", "2", "3"]],
             "b" => [@"triple" "8.0", "8.1", "8.2"]);
    expected_mbe.anonimize_repeat(n("triple"));

    assert_eq!(parsed, IncompleteNode(expected_mbe));
}


#[test]
fn star_construction() {
    let env = mbe!( "a" => ["1", "2"]);

    assert_eq!(
        ast!( { - "x" => [* env =>("a") env : (, env.get_leaf_or_panic(&n("a")).clone())]} ),
        ast!( { - "x" => ["1", "2"] }));



    let env = mbe!( "a" => [@"duo" "1", "2"], "b" => [@"duo" "11", "22"]);

    assert_eq!(
        ast!( { - "x" => [* env =>("a", "b") env :
                            ((, env.get_leaf_or_panic(&n("b")).clone())
                             (, env.get_leaf_or_panic(&n("a")).clone()))]} ),
        ast!( { - "x" => [("11" "1"), ("22" "2")] }));

}

#[test]
fn mbe_r_and_r_roundtrip() {
    use runtime::reify::Reifiable;
    let mbe1 = mbe!( "a" => [@"duo" "1", "2"], "b" => [@"duo" "11", "22"]);
    assert_eq!(mbe1, EnvMBE::<Ast>::reflect(&mbe1.reify()));
}
