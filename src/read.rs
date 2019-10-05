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

pub fn delim(s: &str) -> DelimChar {
    match s {
        "(" | ")" => Paren,
        "[" | "]" => SquareBracket,
        "{" | "}" => CurlyBracket,
        _ => panic!("not a delimiter!"),
    }
}
