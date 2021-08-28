#![macro_use]

// For testing purposes, we want to generate valid `Ast`s,
//  but `ast!` is clunky and makes it *super* easy to leave off `Quote*` and `ExtendEnv`
//  and actually running the parser is a big dependency (and requires huge string literals).
//  so we introduce a `u!` macro that looks up forms but infers the internal structure.

// It's weird to be relying on the grammar while ignoring parts of it, hence "flimsy",
//  but errors are much more likely to be compile-time than inscrutable test problems.

// It's not unsafe to use `u!` for runtime operations, but there's a runtime cost, so don't do it.

use crate::{
    ast::{Ast, AstContents::*},
    grammar::FormPat,
    name::*,
    util::mbe::EnvMBE,
};
use std::iter::{Iterator, Peekable};

// AstContents to Ast
macro_rules! raw_ast {
    ($ast_kind:ident) => {
        crate::ast::Ast(std::rc::Rc::new(crate::ast::LocatedAst {
            c: crate::ast::AstContents::$ast_kind,
            // TODO: would Rust file info be useful?
            file_id: 0, begin: 0, end: 0
        }))
    };
    ($ast_kind:ident ( $( $body:expr ),* ) ) => {
        crate::ast::Ast(std::rc::Rc::new(crate::ast::LocatedAst {
            c: crate::ast::AstContents::$ast_kind( $( $body ),* ),
            // TODO: would Rust file info be useful?
            file_id: 0,
            begin: 0,
            end: 0
        }))
    }
}

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
    ([] [] {}) => {
        // Empty repeat
        raw_ast!(Shape(vec![raw_ast!(Atom(n("REP")))]))
    };
    ([]  [ $( $acc_cur:tt )* ] { $( [ $( $acc_rest:tt )* ] )* }) => {
        raw_ast!(Shape(vec![
            raw_ast!(Atom(n("REP"))),
            $( u_shape_if_many!(  $($acc_rest)* ), )*
            u_shape_if_many!(  $($acc_cur)* )
        ]))
    };
}

macro_rules! u_shape_if_many {
    ($t:tt) => {
        u!($t)
    };
    () => {
        compile_error!("empty u!")
    };
    ( $($ts:tt)* ) => {
        u!((~ $($ts)* ))
    };
}

thread_local! {
    pub static default_nt: std::cell::RefCell<String> = std::cell::RefCell::new("Expr".to_owned());
}

macro_rules! u {
    ($atom:ident) => {
        // Default to this, because `Call` will use whatever it's given, without a grammar:
        raw_ast!(VariableReference(n(stringify!($atom))))
    };
    ( [ , $seq:expr ] ) => {
        {
            let mut contents: Vec<Ast> = $seq;
            contents.insert(0, raw_ast!(Atom(n("REP"))));
            raw_ast!(Shape(contents))
        }
    };
    ( [ $( $ts:tt )*  ] ) => {
        u_rep!( [$($ts)*] [] {} )
    };
    ( { $form:ident : $( $ts:tt )*} ) => {
        {
            let f = crate::macros::flimsy_syntax::default_nt.with(|def_nt| {
                crate::core_forms::find_core_form(&def_nt.borrow(), stringify!($form))
            });
            raw_ast!(Node(f.clone(),
                crate::macros::flimsy_syntax::parse_flimsy_mbe(&u!( (~ $($ts)* ) ), &f.grammar)
                    .unwrap_or_else(crate::util::mbe::EnvMBE::new),
                crate::beta::ExportBeta::Nothing))
        }
    };
    ( { $nt:ident $form:ident : $( $ts:tt )*} ) => {
        {
            let mut old_default_nt = "".to_owned();
            let f = crate::macros::flimsy_syntax::default_nt.with(|def_nt| {
                old_default_nt = def_nt.borrow().clone();
                let nt = stringify!($nt);
                *def_nt.borrow_mut() = nt.to_string();

                crate::core_forms::find_core_form(&nt, stringify!($form))
            });
            let res = raw_ast!(Node(f.clone(),
                crate::macros::flimsy_syntax::parse_flimsy_mbe(&u!( (~ $($ts)* ) ), &f.grammar)
                    .unwrap_or_else(crate::util::mbe::EnvMBE::new),
                crate::beta::ExportBeta::Nothing));
            crate::macros::flimsy_syntax::default_nt.with(|def_nt| {
                *def_nt.borrow_mut() = old_default_nt;
            });
            res
        }
    };
    // The need for explicit exports is unfortunate;
    //  that information is part of `Scope`, not `Form` (maybe we should change that?)
    ( { $form:ident => $ebeta:tt : $( $ts:tt )*} ) => {
        {
            let f = crate::macros::flimsy_syntax::default_nt.with(|def_nt| {
                crate::core_forms::find_core_form(&def_nt.borrow(), stringify!($form))
            });
            raw_ast!(Node(f.clone(),
                crate::macros::flimsy_syntax::parse_flimsy_mbe(&u!( (~ $($ts)* ) ), &f.grammar)
                    .unwrap_or_else(crate::util::mbe::EnvMBE::new),
                ebeta!($ebeta)))
        }
    };
    ( { $nt:ident $form:ident => $ebeta:tt : $( $ts:tt )*} ) => {
        {
            // code duplication from above ) :
            let mut old_default_nt = "".to_owned();
            let f = crate::macros::flimsy_syntax::default_nt.with(|def_nt| {
                old_default_nt = def_nt.borrow().clone();
                let nt = stringify!($nt);
                *def_nt.borrow_mut() = nt.to_string();

                crate::core_forms::find_core_form(&nt, stringify!($form))
            });

            let res =raw_ast!(Node(f.clone(),
                    crate::macros::flimsy_syntax::parse_flimsy_mbe(&u!( (~ $($ts)* ) ), &f.grammar)
                        .unwrap_or_else(crate::util::mbe::EnvMBE::new),
                    ebeta!($ebeta)));
            crate::macros::flimsy_syntax::default_nt.with(|def_nt| {
                *def_nt.borrow_mut() = old_default_nt;
            });
            res
        }
    };
    ( { $form:expr ; $( $ts:tt )*} ) => {
        {
            let f = $form;
            raw_ast!(Node(f.clone(),
                crate::macros::flimsy_syntax::parse_flimsy_mbe(&u!( (~ $($ts)* ) ), &f.grammar)
                    .unwrap_or_else(crate::util::mbe::EnvMBE::new),
                crate::beta::ExportBeta::Nothing))
        }
    };
    ({ $( $anything:tt )* }) => {
        compile_error!("Needed a : or ; in u!");
    };
    // Currently, nested `Seq`s need to correspond to nested `SEQ`s, so this creates one explicitly:
    ((~ $($ts:tt)*)) => {
        raw_ast!(Shape(vec![
            raw_ast!(Atom(n("SEQ"))),
            $( u!( $ts ) ),*
        ]))
    };
    ((at $t:tt)) => {
        raw_ast!(Atom(n(stringify!($t))))
    };
    ((prim $t:tt)) => {
        crate::core_type_forms::get__primitive_type(n(stringify!($t)))
    };
    ((, $interpolate:expr)) => {
        $interpolate
    };
    // Two or more token trees (avoid infinite regress by not handling the one-element case)
    ( $t_first:tt $t_second:tt $( $t:tt )* ) => {
        raw_ast!(Shape(vec![
            raw_ast!(Atom(n("SEQ"))),
            u!( $t_first ), u!( $t_second ), $( u!( $t ) ),*
        ]))
    };
}

macro_rules! uty {
    ($( $ts:tt )*) => {
        {
            let mut old_default_nt = "".to_owned();
            crate::macros::flimsy_syntax::default_nt.with(|def_nt| {
                old_default_nt = def_nt.borrow().clone();
                *def_nt.borrow_mut() = "Type".to_owned();
            });
            let res = u!( $($ts)* );

            crate::macros::flimsy_syntax::default_nt.with(|def_nt| {
                *def_nt.borrow_mut() = old_default_nt;
            });
            res
        }
    };
}

fn parse_flimsy_seq<'a, I>(flimsy_seq: &mut Peekable<I>, grammar: &FormPat) -> EnvMBE<Ast>
where I: Iterator<Item = &'a Ast> {
    use crate::grammar::FormPat::*;

    match grammar {
        Seq(ref grammar_parts) => {
            let mut result = EnvMBE::new();

            for grammar_part in grammar_parts {
                result = result.combine_overriding(&parse_flimsy_seq(flimsy_seq, grammar_part));
            }
            result
        }
        _ => {
            // `Anyways`es shouldn't consume anything (and they'll always be `Named`):
            let consuming = match grammar {
                Named(_, ref body) => match **body {
                    Anyways(_) => false,
                    // HACK: special case for core_macro_forms::macro_invocation.
                    // There has to be a less flimsy way of doing this.
                    QuoteDeepen(ref body, _) | QuoteEscape(ref body, _) => match **body {
                        Anyways(_) => false,
                        _ => true,
                    },
                    _ => true,
                },
                _ => true,
            };
            let trivial = raw_ast!(Trivial);
            let flimsy = match flimsy_seq.peek() {
                None if consuming => return EnvMBE::new(), // Or is this an error?
                None => &trivial,
                Some(f) => f,
            };
            match parse_flimsy_mbe(&flimsy, grammar) {
                None => EnvMBE::new(),
                Some(res) => {
                    if consuming {
                        let _ = flimsy_seq.next();
                    }
                    res
                }
            }
        }
    }
}

pub fn parse_flimsy_mbe(flimsy: &Ast, grammar: &FormPat) -> Option<EnvMBE<Ast>> {
    use crate::grammar::FormPat::*;

    match grammar {
        Literal(_, _) => None,
        Call(_) => None,
        Scan(_) => None,
        Seq(_) => match flimsy.c() {
            Shape(flimsy_parts) => {
                if flimsy_parts[0].c() != &Atom(n("SEQ")) {
                    panic!("Needed a SEQ, got {}", flimsy)
                }
                let mut fpi = flimsy_parts[1..].iter().peekable();

                Some(parse_flimsy_seq(&mut fpi, grammar))
            }
            _ => panic!("Needed a SEQ shape, got {}", flimsy),
        },
        Star(ref body) | Plus(ref body) => match flimsy.c() {
            Shape(flimsy_parts) => {
                if flimsy_parts[0].c() != &Atom(n("REP")) {
                    panic!("Need a REP, got {}", flimsy_parts[0])
                }

                let mut reps = vec![];
                for flimsy_part in flimsy_parts[1..].iter() {
                    reps.push(parse_flimsy_mbe(flimsy_part, &*body).unwrap());
                }
                Some(EnvMBE::new_from_anon_repeat(reps))
            }
            _ => panic!("Needed a REP shape, got {}", flimsy),
        },
        Alt(ref subs) => {
            // HACK: always pick the first branch of the `Alt`
            // (mainly affects unquotation, where it skips the type annotation)
            parse_flimsy_mbe(flimsy, &*subs[0])
        }
        Named(name, ref body) => Some(EnvMBE::new_from_leaves(
            crate::util::assoc::Assoc::new().set(*name, parse_flimsy_ast(flimsy, &*body)),
        )),
        SynImport(_, _, _) => panic!("`SynImport` can't work without a real parser"),
        NameImport(_, _) => panic!("`NameImport` should live underneath `Named`: {:?}", grammar),
        _ => unimplemented!("Can't handle {:?}", grammar),
    }
}

fn parse_flimsy_ast(flimsy: &Ast, grammar: &FormPat) -> Ast {
    use crate::grammar::FormPat::*;

    match grammar {
        Anyways(ref a) => a.clone(),
        Impossible => unimplemented!(),
        Scan(_) => flimsy.clone(),
        Literal(_, _) => raw_ast!(Trivial),
        VarRef(_) => match flimsy.c() {
            VariableReference(a) => raw_ast!(VariableReference(*a)),
            non_atom => panic!("Needed an atom, got {}", non_atom),
        },
        NameImport(body, beta) => {
            raw_ast!(ExtendEnv(parse_flimsy_ast(flimsy, &*body), beta.clone()))
        }
        NameImportPhaseless(body, beta) => {
            raw_ast!(ExtendEnvPhaseless(parse_flimsy_ast(flimsy, &*body), beta.clone()))
        }
        QuoteDeepen(body, pos) => raw_ast!(QuoteMore(parse_flimsy_ast(flimsy, &*body), *pos)),
        QuoteEscape(body, depth) => raw_ast!(QuoteLess(parse_flimsy_ast(flimsy, &*body), *depth)),

        Call(name) => {
            // HACK: don't descend into `Call(n("DefaultAtom"))
            if *name == n("DefaultAtom") || *name == n("AtomNotInPat") {
                match flimsy.c() {
                    VariableReference(a) => raw_ast!(Atom(*a)),
                    non_atom => panic!("Needed an atom, got {}", non_atom),
                }
            } else {
                flimsy.clone()
            }
        }
        _ => unimplemented!("Can't handle {:?}", grammar),
    }
}
