#![macro_use]

// For testing purposes, we want to generate valid Asts without a full-fledged parser.
// `ast!` is clunky and makes it *super* easy to leave off `QuoteMore`, `QuoteLess`, and `ExtendEnv`
// We'll assume that the form itself is known and that we can drop all the literals on the ground.
// The result is a terse way to make valid ASTs.

use ast::Ast::{self, *};
use grammar::FormPat;
use name::*;
use std::iter::{Iterator, Peekable};
use util::mbe::EnvMBE;

// First, transforms from `[a b c; d e f; g h i]` to `[g h i] {[a b c] [d e f]}`
//   to get around a Rust macro parsing restriction,
//  then makes a REP flimsy shape for it.
macro_rules! u_rep {
    ([; $( $ts:tt )*]   $acc_cur:tt { $( $acc_rest:tt )* }) => {
        u_rep!( [ $( $ts )* ] [] {  $( $acc_rest )*  $acc_cur })
    };
    ([$t:tt $( $ts:tt )*]  [ $( $acc_cur:tt )* ] { $( $acc_rest:tt )* }) => {
        u_rep!( [ $( $ts )* ] [$($acc_cur)* $t] { $( $acc_rest )* })
    };
    ([]  [ $( $acc_cur:tt )* ] { $( [ $( $acc_rest:tt )* ] )* }) => {
        ::ast::Shape(vec![
            ::ast::Atom(n("REP")),
            $( u!( $($acc_rest)* ), )*
            u!( $($acc_cur)* )
        ])
    };
}

macro_rules! u {
    ($atom:ident) => {
        // Default to this, because `Call` will use whatever it's given, without a grammar:
        ::ast::VariableReference(n(stringify!($atom)))
    };
    ( [ $( $ts:tt )*  ] ) => {
        u_rep!( [$($ts)*] [] {} )
    };
    ( { $form:ident : $( $ts:tt )*} ) => {
        {
            let f = ::core_forms::find_core_form("Expr", stringify!($form));
            ::ast::Node(f.clone(),
                ::macros::flimsy_syntax::parse_flimsy_mbe(&u!( (~ $($ts)* ) ), &f.grammar)
                    .unwrap_or_else(::util::mbe::EnvMBE::new),
                ::beta::ExportBeta::Nothing)
        }
    };
    ( { $nt:ident $form:ident : $( $ts:tt )*} ) => {
        {
            let f = ::core_forms::find_core_form(stringify!($nt), stringify!($form));
            ::ast::Node(f.clone(),
                ::macros::flimsy_syntax::parse_flimsy_mbe(&u!( (~ $($ts)* ) ), &f.grammar)
                    .unwrap_or_else(::util::mbe::EnvMBE::new),
                ::beta::ExportBeta::Nothing)
        }
    };
    // The need for explicit exports is unfortunate;
    //  that information is part of `Scope`, not `Form` (maybe we should change that?)
    ( { $nt:ident $form:ident => $ebeta:tt : $( $ts:tt )*} ) => {
        {
            let f = ::core_forms::find_core_form(stringify!($nt), stringify!($form));
            ::ast::Node(f.clone(),
                ::macros::flimsy_syntax::parse_flimsy_mbe(&u!( (~ $($ts)* ) ), &f.grammar)
                    .unwrap_or_else(::util::mbe::EnvMBE::new),
                ebeta!($ebeta))
        }
    };
    ({ $( $anything:tt )* }) => {
        panic!("Needed a : in u!");
    };
    // Currently, nested `Seq`s need to correspond to nested `SEQ`s, so this creates one explicitly:
    ((~ $($ts:tt)*)) => {
        ::ast::Shape(vec![
            ::ast::Atom(n("SEQ")),
            $( u!( $ts ) ),*
        ])
    };
    ((at $t:tt)) => {
        ::ast::Atom(n(stringify!($t)))
    };
    ((, $interpolate:expr)) => {
        $interpolate
    };
    // Two or more token trees (avoid infinite regress)
    ( $t_first:tt $t_second:tt $( $t:tt )* ) => {
        ::ast::Shape(vec![
            ::ast::Atom(n("SEQ")),
            u!( $t_first ), u!( $t_second ), $( u!( $t ) ),*
        ])
    };
}

macro_rules! uty {
    ($( $ts:tt )*) => {
        Ty(u!( $($ts)* ))
    };
}

fn parse_flimsy_seq<'a, I>(flimsy_seq: &mut Peekable<I>, grammar: &FormPat) -> EnvMBE<Ast>
where I: Iterator<Item = &'a Ast> {
    use grammar::FormPat::*;

    match grammar {
        Seq(ref grammar_parts) => {
            let mut result = EnvMBE::new();

            for grammar_part in grammar_parts {
                result = result.combine_overriding(&parse_flimsy_seq(flimsy_seq, grammar_part));
            }
            result
        }
        _ => {
            let flimsy = *match flimsy_seq.peek() {
                None => return EnvMBE::new(), // Or is this an error?
                Some(f) => f,
            };
            match parse_flimsy_mbe(flimsy, grammar) {
                None => EnvMBE::new(),
                Some(res) => {
                    let _ = flimsy_seq.next();
                    res
                }
            }
        }
    }
}

pub fn parse_flimsy_mbe(flimsy: &Ast, grammar: &FormPat) -> Option<EnvMBE<Ast>> {
    use grammar::FormPat::*;

    match grammar {
        Literal(_, _) => None,
        Seq(_) => match flimsy {
            Shape(flimsy_parts) => {
                if flimsy_parts[0] != Atom(n("SEQ")) {
                    panic!("Needed a SEQ, got {}", flimsy)
                }
                let mut fpi = flimsy_parts[1..].iter().peekable();

                Some(parse_flimsy_seq(&mut fpi, grammar))
            }
            _ => panic!("Needed a SEQ shape, got {}", flimsy),
        },
        Star(ref body) | Plus(ref body) => match flimsy {
            Shape(flimsy_parts) => {
                if flimsy_parts[0] != Atom(n("REP")) {
                    panic!("Need a REP")
                }

                let mut reps = vec![];
                for flimsy_part in flimsy_parts[1..].iter() {
                    reps.push(parse_flimsy_mbe(flimsy_part, &*body).unwrap());
                }
                Some(EnvMBE::new_from_anon_repeat(reps))
            }
            _ => panic!("Needed a REP shape"),
        },
        Named(name, ref body) => Some(EnvMBE::new_from_leaves(
            ::util::assoc::Assoc::new().set(*name, parse_flimsy_ast(flimsy, &*body)),
        )),
        _ => unimplemented!(),
    }
}

fn parse_flimsy_ast(flimsy: &Ast, grammar: &FormPat) -> Ast {
    use grammar::FormPat::*;

    match grammar {
        Anyways(ref a) => a.clone(),
        Impossible => unimplemented!(),
        Literal(_, _) => Trivial,
        VarRef(_) => match flimsy {
            VariableReference(a) => VariableReference(*a),
            non_atom => panic!("Needed an atom, got {}", non_atom),
        },
        NameImport(body, beta) => {
            ExtendEnv(Box::new(parse_flimsy_ast(flimsy, &*body)), beta.clone())
        }
        QuoteDeepen(body, pos) => QuoteMore(Box::new(parse_flimsy_ast(flimsy, &*body)), *pos),
        QuoteEscape(body, depth) => QuoteLess(Box::new(parse_flimsy_ast(flimsy, &*body)), *depth),

        // Lookup is faked by the flimsy macros, so we don't need to do anything:
        SynImport(body, _, _) => parse_flimsy_ast(flimsy, &*body),
        Call(name) => {
            // HACK: don't descend into `Call(n("DefaultName"))
            if *name == n("DefaultName") {
                match flimsy {
                    VariableReference(a) => Atom(*a),
                    non_atom => panic!("Needed an atom, got {}", non_atom),
                }
            } else {
                flimsy.clone()
            }
        }
        _ => unimplemented!(),
    }
}
