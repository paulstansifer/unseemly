#![allow(non_upper_case_globals)]
#![macro_use]

extern crate regex;

use name::*;

#[derive(Debug,PartialEq,Eq,Clone,Copy)]
pub enum DelimChar { Paren, SquareBracket, CurlyBracket }

use self::DelimChar::*;

#[derive(Debug,PartialEq,Eq)]
pub struct TokenTree<'a> {
    pub t: Vec<Token<'a>>
}

#[derive(Debug,PartialEq,Eq)]
pub enum Token<'a> {
    Simple(Name<'a>),
    Group(Name<'a>, DelimChar, TokenTree<'a>)
}

impl<'a> Token<'a> {
    pub fn is_just(&self, s: &str) -> bool {
        match self {
            &Simple(ref x) if x.is(s) => { true }
            _ => { false }
        }
    }
}

pub use self::Token::*;

// A token may start with an open delimiter, or end with a close delmiter,
// but otherwise may not contain delimiters

const nondelim : &'static str = r"[^\[\]\(\)\{\}\s]";
const open : &'static str = r"[\[\(\{]";
const close : &'static str = r"[\]\)\}]";


pub fn delim(s: &str) -> DelimChar {
    match s {
        "(" => Paren, "[" => SquareBracket, "{" => CurlyBracket,
        ")" => Paren, "]" => SquareBracket, "}" => CurlyBracket,
        _ => {panic!("not a delimiter!")}
    }
}

fn read_tokens<'a>(s: &'a str) -> TokenTree<'a> {
    lazy_static! {
        static ref token : regex::Regex =
            regex::Regex::new(format!(r"(?P<open_all>(?P<main_o>{nd}*)(?P<open>{o}))|((?P<close>{c})(?P<main_c>{nd}*))|(?P<normal>{nd}+)",
                                      o = open, c = close, nd = nondelim)
                                      .as_str()).unwrap();
    }
    let mut flat_tokens = token.captures_iter(s);

    fn read_token_tree<'a>(flat_tokens: &mut regex::FindCaptures<'a, 'a>)
            -> (TokenTree<'a>, Option<(DelimChar, &'a str)>) {
        let mut this_level : Vec<Token> = vec![];
        loop{
            match flat_tokens.next() {
                None => { return (TokenTree{ t: this_level }, None) }
                Some(c) => {
                    if let Some(normal) = c.name("normal") {
                        this_level.push(Simple(n(normal)));
                    } else if let (Some(_main), Some(o_del), Some(all))
                        = (c.name("main_o"), c.name("open"), c.name("open_all")) {
                        let (inside, _last) = read_token_tree(flat_tokens);
                        // TODO check last
                        this_level.push(Group(n(all), delim(o_del), inside));
                    } else if let (Some(main), Some(c_del)) = (c.name("main_c"), c.name("close")) {
                        return (TokenTree{ t: this_level }, Some((delim(c_del), main)));
                    } else { panic!("ICE") }

                }
            }
        }
    }

    let (tt, leftover) = read_token_tree(&mut flat_tokens);

    match leftover {
        None => tt,
        Some(l) => { panic!("leftover! {:?}", l); }
    }
}





macro_rules! tokens {
    ($($contents:tt)*) => { TokenTree{t: vec![ $(  t_elt!($contents) ),* ] }}
}

macro_rules! t_elt {
    ( [ $e:expr ;  $( $list:tt )* ] ) => { Group(n(concat!($e,"[")), SquareBracket, tokens!($($list)*))};
    ( { $e:expr ;  $( $list:tt )* } ) => { Group(n(concat!($e,"{")), CurlyBracket, tokens!($($list)*))};
    ( ( $e:expr ;  $( $list:tt )* ) ) => { Group(n(concat!($e,"(")), Paren, tokens!($($list)*))};
    ($e:expr) => { Simple(n($e)) }
}

#[test]
fn simple_reading()  {
    assert_eq!(read_tokens(""), tokens!());
    assert_eq!(read_tokens("asdf"), tokens!("asdf"));
    assert_eq!(read_tokens("a s d-f d - f && a\na    8888"),
               tokens!("a" "s" "d-f" "d" "-" "f" "&&" "a" "a" "8888"));
}
#[test]
fn nested_reading() {
    assert_eq!(read_tokens("()"), tokens!(("";)));
    assert_eq!(read_tokens("a ()"), tokens!("a" ("";)));
    assert_eq!(read_tokens("(b)"), tokens!(("";"b")));
    assert_eq!(read_tokens("f x(c)x"), tokens!("f" ("x";"c")));
    assert_eq!(read_tokens("f x[d]x"), tokens!("f" ["x";"d"]));
    assert_eq!(read_tokens("$-[()]$- x"), tokens!(["$-";("";)] "x"));
    assert_eq!(read_tokens("(#(5 6)# -[yy foo()foo aa]-)"),
               tokens!((""; ("#"; "5" "6") ["-"; "yy" ("foo";) "aa"])))
}
