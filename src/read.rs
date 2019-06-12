/*
The tokenizer ("reader", in Scheme parlance) for Unseemly.

TODO: Make tokenization lazy...
TODO #6: ...so that it's possible to switch tokenizers mid-file.
*/

extern crate regex;

use name::*;

custom_derive! {
    #[derive(Debug,PartialEq,Eq,Clone,Copy,Reifiable)]
    pub enum DelimChar { Paren, SquareBracket, CurlyBracket }
}

impl DelimChar {
    pub fn open(self) -> char {
        match self {
            Paren => '(', SquareBracket => '[', CurlyBracket => '{'
        }
    }
    pub fn close(self) -> char {
        match self {
            Paren => ')', SquareBracket => ']', CurlyBracket => '}'
        }
    }
}

use self::DelimChar::*;

#[derive(Debug,PartialEq,Eq)]
pub struct TokenTree {
    pub t: Vec<Token>
}

#[derive(Debug,PartialEq,Eq)]
pub enum Token {
    Simple(Name),
    Group(Name, DelimChar, TokenTree)
}

impl Token {
    pub fn is_just(&self, s: &str) -> bool {
        match *self {
            Simple(ref x) if x.is(s) => { true }
            _ => { false }
        }
    }
}

pub use self::Token::*;

// A token may start with an open delimiter, or end with a close delmiter,
// but otherwise may not contain delimiters

const nondelim : &str = r"[^\[\]\(\)\{\}\s]";
const open : &str = r"[\[\(\{]";
const close : &str = r"[\]\)\}]";

pub fn delim(s: &str) -> DelimChar {
    match s {
        "(" | ")" => Paren, "[" | "]" => SquareBracket, "{" | "}" => CurlyBracket,
        _ => {panic!("not a delimiter!")}
    }
}

pub fn read_tokens(s: &str) -> Result<TokenTree, String> {
    lazy_static! {
        static ref token : regex::Regex =
            regex::Regex::new(format!(r"(?P<open_all>(?P<main_o>{nd}*)(?P<open>{o}))|((?P<close>{c})(?P<main_c>{nd}*))|(?P<normal>{nd}+)",
                                      o = open, c = close, nd = nondelim)
                                      .as_str()).unwrap();
    }
    let mut flat_tokens = token.captures_iter(s);

    fn read_token_tree<'a>(flat_tokens: &mut regex::CaptureMatches<'a, 'a>)
            -> Result<(TokenTree, Option<(DelimChar, &'a str)>), String> {
        let mut this_level : Vec<Token> = vec![];
        loop{
            match flat_tokens.next() {
                None => { return Ok((TokenTree{ t: this_level }, None)) }
                Some(c) => {
                    if let Some(normal) = c.name("normal") {
                        this_level.push(Simple(n(normal.as_str())));
                    } else if let (Some(_main), Some(o_del), Some(all))
                        = (c.name("main_o"), c.name("open"), c.name("open_all")) {
                        let (inside, last) = read_token_tree(flat_tokens)?;

                        if let Some(last) = last {
                            if format!("{}{}",last.1, o_del.as_str()) == all.as_str() {
                                this_level.push(Group(n(all.as_str()),
                                                      delim(o_del.as_str()), inside));
                            } else {
                                return Err(format!(
                                    "Unmatched delimiter names: \"{}\" is closed by \"{}\". \
                                     Remember(this tokenizer is weird)Remember",
                                        all.as_str(), last.1));
                            }
                        } else {
                            return Err(format!(
                                "Unclosed delimiter at EOF: \"{}\"", o_del.as_str()));
                        }
                    } else if let (Some(main), Some(c_del)) = (c.name("main_c"), c.name("close")) {
                        return Ok((TokenTree{ t: this_level },
                                   Some((delim(c_del.as_str()), main.as_str()))));
                    } else { panic!("ICE") }

                }
            }
        }
    }

    let (tt, leftover) = read_token_tree(&mut flat_tokens)?;

    match leftover {
        None => Ok(tt),
        Some(l) => { Err(format!("Read error: leftover {:#?}", l)) }
    }
}




#[test]
fn simple_reading()  {
    assert_eq!(read_tokens(""), Ok(tokens!()));
    assert_eq!(read_tokens("asdf"), Ok(tokens!("asdf")));
    assert_eq!(read_tokens("a s d-f d - f && a\na    8888"),
               Ok(tokens!("a" "s" "d-f" "d" "-" "f" "&&" "a" "a" "8888")));
}
#[test]
fn nested_reading() {
    assert_eq!(read_tokens("()"), Ok(tokens!(("";))));
    assert_eq!(read_tokens("a ()"), Ok(tokens!("a" ("";))));
    assert_eq!(read_tokens("(b)"), Ok(tokens!(("";"b"))));
    assert_eq!(read_tokens("f x(c)x"), Ok(tokens!("f" ("x";"c"))));
    assert_eq!(read_tokens("f x[d]x"), Ok(tokens!("f" ["x";"d"])));
    assert_eq!(read_tokens("$-[()]$- x"), Ok(tokens!(["$-";("";)] "x")));
    assert_eq!(read_tokens("(#(5 6)# -[yy foo()foo aa]-)"),
               Ok(tokens!((""; ("#"; "5" "6") ["-"; "yy" ("foo";) "aa"]))))
}
