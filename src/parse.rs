#![allow(dead_code,unused_imports)]

use read::{Token, TokenTree, DelimChar, Group, Simple};
use name::Name;
use std::collections::HashMap;
use std::boxed::Box;
use std::option::Option;
use std::iter;

extern crate combine;

use self::combine::{Parser, ParseResult, ParseError};
use self::combine::primitives::{State, SliceStream, Positioner, Consumed, Error};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ast<'t> {
    Trivial,
    Atom(&'t str),
    Shape(Vec<Ast<'t>>),
    Node(HashMap<Name, Ast<'t>>)
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
    ($e:expr) => { Atom($e) }
}


impl<'t> Token<'t> {
    fn to_ast(&self) -> Ast<'t> {
        match *self {
            Simple(s) => Atom(s),
            Group(_s, ref _delim, ref body) => Shape(body.t.iter().map(|t| t.to_ast()).collect())
        }
    }
}

use self::Ast::*;


/// Form is a grammar for syntax forms, augmented with binding information
pub enum Form<'t> {
    Literal(&'t str),
    AnyAtom,
    Delimited(&'t str, DelimChar, Box<Form<'t>>),
    Seq(Vec<Form<'t>>),
    Star(Box<Form<'t>>),
    Alt(Vec<Form<'t>>),

    Scope(Box<Form<'t>>), // limits the region where names are meaningful. Might be superfluous once we do names right.
    Named(Name, Box<Form<'t>>),

    //SynImport(Name, Box<Form<'t>>), //TODO
    NamesImport(Name, Box<Form<'t>>),
    NamesExport(Vec<Name>, Box<Form<'t>>)
}

/*
macro_rules! form {
    ($($contents:tt)*) => { Seq(vec![ $(  ast_elt!($contents) ),* ] )}
}
*/

struct FormParser<'t> {
    f: &'t Form<'t>,
}

impl<'t> Positioner for Token<'t> {
    type Position = usize;
    fn start() -> usize { 0 }
    fn update(&self, position: &mut usize) { *position += 1 as usize }
}

impl<'t> FormParser<'t> {
    fn parse_tokens(&mut self, ts: &'t Vec<Token<'t>>)
            -> ParseResult<Ast<'t>, SliceStream<'t, Token<'t>>> {
        self.parse_state(State::new(SliceStream::<'t, Token<'t>>(ts.as_slice())))
    }
}

fn parse<'t>(f: &'t Form<'t>, tt: &'t TokenTree<'t>) -> Result<Ast<'t>, ParseError<SliceStream<'t, Token<'t>>>> {
    FormParser{f: &f}.parse_tokens(&tt.t).map(|res| res.0).map_err(|consumed| consumed.into_inner())
}

impl<'t> combine::Parser for FormParser<'t> {
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
            Delimited(exp_extra, ref exp_delim, ref f) => {
                let (tok, rest) = try!(inp.uncons());
                match *tok {
                    Group(extra, ref delim, ref body) if (extra, delim) == (exp_extra, exp_delim) => {
                        FormParser{f:&f}.parse_tokens(&body.t)
                    },
                    // bad error message; improve:
                    _ => {
                        combine::unexpected("non-group").parse_state(rest.into_inner()).map(|_| panic!(""))
                    }
                }
            }
            Seq(ref fs) => {
                let mut subs = vec![];
                let mut remaining = inp;
                for f in fs {
                    let (parsed, rest) = try!(FormParser{f:&f}.parse_state(remaining));
                    subs.push(parsed);
                    remaining = rest.into_inner();
                }
                combine::value(Shape(subs)).parse_state(remaining)
            }
            Star(ref f) => {
                combine::many(FormParser{f:&f}).parse_state(inp)
            }
            Alt(ref fs) => {
                let parsers: Vec<_> = fs.iter().map(|f| combine::try(FormParser{f:&f})).collect();
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

use self::Form::*;

#[test]
fn test_parsing() {
    assert_eq!(parse(&Seq(vec![AnyAtom]), &tokens!("asdf")).unwrap(), ast!("asdf"));
    assert_eq!(parse(&Seq(vec![AnyAtom, Literal("fork"), AnyAtom]),
               &tokens!("asdf" "fork" "asdf")).unwrap(),
               ast!("asdf" "fork" "asdf"));
    assert_eq!(parse(&Seq(vec![AnyAtom, Literal("fork"), AnyAtom]),
               &tokens!("asdf" "fork" "asdf")).unwrap(),
               ast!("asdf" "fork" "asdf"));
    parse(&Seq(vec![AnyAtom, Literal("fork"), AnyAtom]),
          &tokens!("asdf" "knife" "asdf")).unwrap_err();
    assert_eq!(parse(&Seq(vec![Star(Box::new(Literal("*"))), Literal("X")]),
                     &tokens!("*" "*" "*" "*" "*" "X")).unwrap(),
               ast!(("*" "*" "*" "*" "*") "X"));

}
