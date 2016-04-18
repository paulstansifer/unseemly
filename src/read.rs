#![allow(dead_code)]
#![allow(non_upper_case_globals)]


extern crate regex;


#[derive(Debug,PartialEq,Eq)]
enum DelimChar { Paren, SquareBracket, CurlyBracket }

use self::DelimChar::*;

#[derive(Debug,PartialEq,Eq)]
struct TokenTree<'a> {
    t: Vec<Token<'a>>
}

#[derive(Debug,PartialEq,Eq)]
enum Token<'a> {
    Simple(&'a str),
    Group(DelimChar, &'a str, TokenTree<'a>)
}

use self::Token::*;

// A token may start with an open delimiter, or end with a close delmiter,
// but otherwise may not contain delimiters

const nondelim : &'static str = r"[^\[\]\(\)\{\}\s]";
const open : &'static str = r"[\[\(\{]";
const close : &'static str = r"[\]\)\}]";


fn delim(s: &str) -> DelimChar {
    match s {
        "(" => Paren, "[" => SquareBracket, "{" => CurlyBracket,
        ")" => Paren, "]" => SquareBracket, "}" => CurlyBracket,
        _ => {panic!("not a delimiter!")}
    }
}

fn read_tokens<'a>(s: &'a str) -> TokenTree<'a> {
    lazy_static! {
        static ref token : regex::Regex =
            regex::Regex::new(format!(r"((?P<main_o>{nd}*)(?P<open>{o}))|((?P<close>{c})(?P<main_c>{nd}*))|(?P<normal>{nd}+)",
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
                    print!("Got {:?}\n", c);

                    if let Some(normal) = c.name("normal") {
                        this_level.push(Simple(normal));
                    } else if let (Some(main), Some(o_del)) = (c.name("main_o"), c.name("open")) {
                        let (inside, _last) = read_token_tree(flat_tokens);
                        // TODO check last
                        this_level.push(Group(delim(o_del), main, inside));
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





macro_rules! t {
    ($($contents:tt)*) => { TokenTree{t: vec![ $(  t_elt!($contents) ),* ] }}
}

macro_rules! t_elt {
    ( [ $e:expr ;  $( $list:tt )* ] ) => { Group(SquareBracket, $e, t!($($list)*))};
    ( { $e:expr ;  $( $list:tt )* } ) => { Group(CurlyBracket, $e, t!($($list)*))};
    ( ( $e:expr ;  $( $list:tt )* ) ) => { Group(Paren, $e, t!($($list)*))};
    ($e:expr) => { Simple($e) }
}

#[test]
fn test_simple_reading()  {
    assert_eq!(read_tokens(""), t!());
    assert_eq!(read_tokens("asdf"), t!("asdf"));
    assert_eq!(read_tokens("a s d-f d - f && a\na    8888"),
               t!("a" "s" "d-f" "d" "-" "f" "&&" "a" "a" "8888"));
}
#[test]
fn test_nested_reading() {
    assert_eq!(read_tokens("()"), t!(("";)));
    assert_eq!(read_tokens("a ()"), t!("a" ("";)));
    assert_eq!(read_tokens("(b)"), t!(("";"b")));
    assert_eq!(read_tokens("f x(c)x"), t!("f" ("x";"c")));
    assert_eq!(read_tokens("f x[d]x"), t!("f" ["x";"d"]));
    assert_eq!(read_tokens("$-[()]$- x"), t!(["$-";("";)] "x"));
    assert_eq!(read_tokens("(#(5 6)# -[yy foo()foo aa]-)"),
               t!((""; ("#"; "5" "6") ["-"; "yy" ("foo";) "aa"])))
}
