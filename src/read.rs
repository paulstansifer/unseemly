use name::*;

custom_derive! {
    #[derive(Debug,PartialEq,Eq,Clone,Copy,Reifiable)]
    pub enum DelimChar { Paren, SquareBracket, CurlyBracket }
}

impl DelimChar {
    pub fn open(self) -> char {
        match self {
            Paren => '(',
            SquareBracket => '[',
            CurlyBracket => '{',
        }
    }
    pub fn close(self) -> char {
        match self {
            Paren => ')',
            SquareBracket => ']',
            CurlyBracket => '}',
        }
    }
}

use self::DelimChar::*;

#[derive(Debug, PartialEq, Eq)]
pub struct TokenTree {
    pub t: Vec<Token>,
}

pub type Token = Name;

impl Token {
    pub fn is_just(&self, s: &str) -> bool { self.is(s) }
}

impl TokenTree {
    pub fn to_string(&self) -> String {
        let mut result = "".to_owned();
        for t in &self.t {
            result += " ";
            result += &t.orig_sp();
        }
        result
    }
}

pub fn delim(s: &str) -> DelimChar {
    match s {
        "(" | ")" => Paren,
        "[" | "]" => SquareBracket,
        "{" | "}" => CurlyBracket,
        _ => panic!("not a delimiter!"),
    }
}
