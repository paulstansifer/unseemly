#![macro_use]

use util::assoc::Assoc;
use util::mbe::EnvMBE;
use name::*;
use beta::Beta;
use std::iter;
use std::cmp::PartialEq;
use std::fmt;
use std::rc::Rc;
use form::Form;

use parse::FormPat;
use ast_walk::WalkRule;

#[derive(Clone, PartialEq)]
pub enum Ast<'t> {
    Trivial,
    Atom(Name<'t>),
    VariableReference(Name<'t>),
    Shape(Vec<Ast<'t>>),
    
    /// A meaningful chunk of syntax, governed by a form, containing an environment
    Node(Rc<Form<'t>>, EnvMBE<'t, Ast<'t>>),
    IncompleteNode(EnvMBE<'t, Ast<'t>>),
    
    /// Variable binding
    ExtendEnv(Box<Ast<'t>>, Beta<'t>)
}

macro_rules! ast_shape {
    ($($contents:tt)*) => { Shape(vec![ $(  ast!($contents) ),* ] )};
}


pub use self::Ast::*;


macro_rules! ast {
    ( (import $beta:tt $sub:tt) ) => {
        ExtendEnv(Box::new(ast!($sub)), beta!($beta))
    };
    ( (vr $var:expr) ) => { VariableReference(n($var)) };
    ( (, $interp:expr)) => { $interp };
    ( ( $( $list:tt )* ) ) => { ast_shape!($($list)*)};
    ( { - $($mbe_arg:tt)* } ) => {
        IncompleteNode(mbe!( $($mbe_arg)* ))
    };
    ( { $form:expr; [ $($mbe_arg:tt)* ] }) => {
        ast!( { $form ; $($mbe_arg)* } )
    };
    ( { $form:expr; $($mbe_arg:tt)* }) => {
        Node($form, mbe!( $($mbe_arg)* ))
    };
    ($e:expr) => { Atom(n($e))}
}


impl<'t> fmt::Debug for Ast<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Trivial => { write!(f, "⨉") },
            Atom(ref n) => { write!(f, "∘{:?}∘", n) },
            VariableReference(ref v) => { write!(f, "{:?}", v)}
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
                write!(f, "{{ ({:?}); {:?} }}", form.name, body)
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




impl<'t> Ast<'t> {
    // TODO: this ought to at least warn if we're losing anything other than `Shape`
    pub fn flatten(&self) -> EnvMBE<'t, Ast<'t>> {
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
impl<'t> iter::FromIterator<Ast<'t>> for Ast<'t> {
    fn from_iter<I: IntoIterator<Item=Ast<'t>>>(i: I) -> Self {
        IncompleteNode(
            EnvMBE::new_from_anon_repeat(
                i.into_iter().map(|a| a.flatten()).collect()))
    }
}


use std::iter::FromIterator;



/* These macros generate `EnvMBE<Ast>`s, not arbitrary `EnvMBE`s, 
    which is a little un-abstract, but is the main usage. */



/*
 * Wait a second, I'm writing in Rust right now! I'll use an MBE macro to implement an MBE literal! 
 */
macro_rules! mbe_one_name {
    ($k:tt => [@ $n:tt $($elt:tt),*]) => {
        ::util::mbe::EnvMBE::new_from_named_repeat(
            n(expr_ify!($n)),
            vec![ $( mbe_one_name!($k => $elt) ),* ]
        )
    };
    
    ($k:tt => [$($elt:tt),*]) => {
        ::util::mbe::EnvMBE::new_from_anon_repeat(
            vec![ $( mbe_one_name!($k => $elt) ),* ])
    };
    
    // For parsing reasons, we only accept expressions that are TTs.
    // It's hard to generalize the `mbe!` interface so that it accepts exprs 
    // or `[]`-surrounded trees of them.
    ($k:tt => $leaf:tt) => {
        ::util::mbe::EnvMBE::new_from_leaves(assoc_n!($k => ast!($leaf)))
    }
}


// Eventually, this ought to support more complex structures
macro_rules! mbe {
    ( $( $lhs:tt => $rhs:tt ),* ) => {{
        let single_name_mbes = vec![ $( mbe_one_name!($lhs => $rhs) ),*];
        let mut res = ::util::mbe::EnvMBE::new();
        for m in &single_name_mbes {
            res = res.merge(m);
        }
        res
    }}
}



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
fn test_combine_from_kleene_star() {
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
