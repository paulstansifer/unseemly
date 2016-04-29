#![allow(dead_code,unused_imports)]

use read::{Token, TokenTree, DelimChar, Group, Simple};
use name::*;
use form::Form;
use std::collections::HashMap;
use std::boxed::Box;
use std::option::Option;
use std::iter;
use std::clone::Clone;

extern crate combine;

use self::combine::{Parser, ParseResult, ParseError};
use self::combine::primitives::{State, SliceStream, Positioner, Consumed, Error};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ast<'t> {
    Trivial,
    Atom(Name<'t>),
    Shape(Vec<Ast<'t>>),
    Node(HashMap<Name<'t>, Ast<'t>>)
}

impl<'t> iter::FromIterator<Ast<'t>> for Ast<'t> {
    fn from_iter<I: IntoIterator<Item=Ast<'t>>>(i: I) -> Self {
        Shape(i.into_iter().collect())
    }
}

macro_rules! ast {
    ($($contents:tt)*) => { Shape(vec![ $(  ast_elt!($contents) ),* ] )}
}

macro_rules! ast_elt {
    ( ( $( $list:tt )* ) ) => { ast!($($list)*)};
    ($e:expr) => { Atom(n($e)) }
}


impl<'t> Token<'t> {
    fn to_ast(&self) -> Ast<'t> {
        match *self {
            Simple(ref s) => Atom(s.clone()),
            Group(ref _s, ref _delim, ref body) => {
                Shape(body.t.iter().map(|t| t.to_ast()).collect())
            }
        }
    }
}

use self::Ast::*;


/// FormPat is a grammar for syntax forms
#[derive(Debug,Clone)]
pub enum FormPat<'t> {
    Literal(&'t str),
    AnyAtom,
    Delimited(Name<'t>, DelimChar, Box<FormPat<'t>>),
    Seq(Vec<FormPat<'t>>),
    Star(Box<FormPat<'t>>),
    Alt(Vec<FormPat<'t>>),
    NamedPat(Name<'t>),

    Scope(Box<FormPat<'t>>), // limits the region where names are meaningful.
    Named(Name<'t>, Box<FormPat<'t>>),

    //SynImport(Name, Box<FormPat<'t>>), //TODO
    NamesImport(Name<'t>, Box<FormPat<'t>>),
    NamesExport(Vec<Name<'t>>, Box<FormPat<'t>>)
}

/*
macro_rules! form {
    ($($contents:tt)*) => { Seq(vec![ $(  ast_elt!($contents) ),* ] )}
}
*/

pub type SynEnv<'t> = HashMap<Name<'t>, Box<Form<'t>>>;

struct FormPatParser<'t> {
    f: &'t FormPat<'t>,
    se: SynEnv<'t> //unsure if this is the right lifetime
}

impl<'t> Positioner for Token<'t> {
    type Position = usize;
    fn start() -> usize { 0 }
    fn update(&self, position: &mut usize) { *position += 1 as usize }
}

impl<'t> FormPatParser<'t> {
    fn parse_tokens(&mut self, ts: &'t Vec<Token<'t>>)
            -> ParseResult<Ast<'t>, SliceStream<'t, Token<'t>>> {
        self.parse_state(State::new(SliceStream::<'t, Token<'t>>(ts.as_slice())))
    }

    fn descend(&self, f: &'t FormPat<'t>) -> FormPatParser<'t> {
        FormPatParser{f: f, se: self.se.clone()}
    }
}

fn parse<'t>(f: &'t FormPat<'t>, tt: &'t TokenTree<'t>, se: SynEnv<'t>)
        -> Result<Ast<'t>, ParseError<SliceStream<'t, Token<'t>>>> {
    FormPatParser{f: &f, se: se}.parse_tokens(&tt.t).map(|res| res.0)
        .map_err(|consumed| consumed.into_inner())
}

fn parse_top<'t>(f: &'t FormPat<'t>, tt: &'t TokenTree<'t>)
        -> Result<Ast<'t>, ParseError<SliceStream<'t, Token<'t>>>> {
    FormPatParser{f: &f, se: HashMap::new()}.parse_tokens(&tt.t).map(|res| res.0)
        .map_err(|consumed| consumed.into_inner())
}


impl<'t> combine::Parser for FormPatParser<'t> {
    type Input = SliceStream<'t, Token<'t>>;
    type Output = Ast<'t>;


    fn parse_state(&mut self, inp: State<Self::Input>)
          -> ParseResult<Self::Output, Self::Input> {

        fn ast_ify<'t, I>(res : (&'t Token<'t>, I)) -> (Ast<'t>, I) {
            let (got, inp) = res;
            (got.to_ast(), inp)
        }

        match *self.f {
            Literal(exp_tok) => {
                combine::satisfy(|tok: &'t Token<'t>| {tok.is_just(exp_tok)}).parse_state(inp)
                    .map(ast_ify)
            }
            AnyAtom => { combine::any().parse_state(inp).map(ast_ify) }
            Delimited(ref exp_extra, ref exp_delim, ref f) => {
                let (tok, rest) = try!(inp.uncons());
                match *tok {
                    Group(ref extra, ref delim, ref body)
                    if (extra, delim) == (exp_extra, exp_delim) => {
                        self.descend(f).parse_tokens(&body.t)
                    },
                    // bad error message; improve:
                    _ => {
                        combine::unexpected("non-group").parse_state(rest.into_inner())
                            .map(|_| panic!(""))
                    }
                }
            }
            Seq(ref fs) => {
                let mut subs = vec![];
                let mut remaining = inp;
                for f in fs {
                    let (parsed, rest) = try!(self.descend(f).parse_state(remaining));
                    subs.push(parsed);
                    remaining = rest.into_inner();
                }
                combine::value(Shape(subs)).parse_state(remaining)
            }
            Star(ref f) => {

                combine::many(self.descend(f)).parse_state(inp)
            }
            Alt(ref fs) => {
                let parsers: Vec<_> = fs.iter().map(
                    |f| combine::try(self.descend(f))).collect();
                combine::choice(parsers).parse_state(inp)
            }
            _ => {panic!("TODO")}
        }
              /*
        let (tok, next) = try!(inp.uncons());
        match self.f {
            Literal(l_tok) => { inp.update(tok, combine::primitives::Consumed(next)) }
        }*/
    }
}

use self::FormPat::*;

#[test]
fn test_parsing() {
    assert_eq!(parse_top(&Seq(vec![AnyAtom]), &tokens!("asdf")).unwrap(), ast!("asdf"));
    assert_eq!(parse_top(&Seq(vec![AnyAtom, Literal("fork"), AnyAtom]),
               &tokens!("asdf" "fork" "asdf")).unwrap(),
               ast!("asdf" "fork" "asdf"));
    assert_eq!(parse_top(&Seq(vec![AnyAtom, Literal("fork"), AnyAtom]),
               &tokens!("asdf" "fork" "asdf")).unwrap(),
               ast!("asdf" "fork" "asdf"));
    parse_top(&Seq(vec![AnyAtom, Literal("fork"), AnyAtom]),
          &tokens!("asdf" "knife" "asdf")).unwrap_err();
    assert_eq!(parse_top(&Seq(vec![Star(Box::new(Literal("*"))), Literal("X")]),
                     &tokens!("*" "*" "*" "*" "*" "X")).unwrap(),
               ast!(("*" "*" "*" "*" "*") "X"));

}
