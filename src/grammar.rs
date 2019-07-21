#![macro_use]

use ast::Ast::{self, *};
use beta::{Beta, ExportBeta};
use form::{simple_form, Form};
use name::*;
use read::{DelimChar, Token, TokenTree};
use std::{boxed::Box, clone::Clone, rc::Rc};
use util::assoc::Assoc;

impl Token {
    fn to_ast(&self) -> Ast { Atom(*self) }
}

custom_derive! {
    /// `FormPat` defines a pattern in a grammar. Think EBNF, but more extended.

    /// Most kinds of grammar nodes produce an `Ast` of either `Shape` or `Env`,
    ///  but `Named` and `Scope` are special:
    ///  everything outside of a `Named` (up to a `Scope`, if any) is discarded,
    ///   and `Scope` produces a `Node`, which maps names to what they got.
    #[derive(Debug, Clone, Reifiable, PartialEq)]
    pub enum FormPat {
        /// Matches 0 tokens, produces the argument
        Anyways(Ast),
        /// Never matches
        Impossible,
        /// Matches an atom or varref, but not if it's on the list of reserved words
        Reserved(Rc<FormPat>, Vec<Name>),
        /// Matches the given name as a literal
        Literal(Name),
        /// cleanup TODO: remove, now that tokens are always atomic
        AnyToken,
        /// Matches any token, as an `Atom`. (TODO: rename)
        AnyAtomicToken,
        /// Matches any token, as a `VariableReference`
        VarRef,
        /// Matches an ordered sequence of patterns.
        Seq(Vec<Rc<FormPat>>),
        /// Matches zero or more occurrences of a pattern.
        Star(Rc<FormPat>),
        /// Matches one or more occurrences of a pattern.
        Plus(Rc<FormPat>),
        /// Matches any of the sub-pattersn.
        Alt(Vec<Rc<FormPat>>),
        /// Matches the LHS pattern, or, failing that, the RHS pattern.
        Biased(Rc<FormPat>, Rc<FormPat>),

        /// Lookup a nonterminal in the current syntactic environment.
        Call(Name),
        /// cleanup TODO: remove this; `SynImport` obsoletes this
        ComputeSyntax(Name, Rc<FormPat>),

        /// Makes a node and limits the region where names are meaningful. `Beta` defines export.
        Scope(Rc<Form>, ExportBeta),
        /// Matches a pattern and gives it a name (inside the current `Scope`)
        Named(Name, Rc<FormPat>),

        /// This is where syntax gets extensible.
        /// Parses its body in the named NT of the syntax environment computed from
        ///  the LHS and the current syntax environment.
        SynImport(Rc<FormPat>, Name, SyntaxExtension),
        /// FOOTGUN:  NameImport(Named(...), ...) is almost always wrong.
        ///  (write Named(NameImport(..., ...)) instead)
        /// TODO: make this better
        NameImport(Rc<FormPat>, Beta),
        /// Quote syntax (the boolean indicates whether it's positive or negative)
        QuoteDeepen(Rc<FormPat>, bool),
        /// Escape syntax quotation (by some number of levels)
        QuoteEscape(Rc<FormPat>, u8)
    }
}
pub struct SyntaxExtension(pub Rc<Box<(dyn Fn(SynEnv, Ast) -> SynEnv)>>);

impl FormPat {
    // Finds all `Named` nodes, and how many layers of repetition they are underneath.
    pub fn binders(&self) -> Vec<(Name, u8)> {
        use tap::TapOps;
        match *self {
            Named(n, ref body) => vec![(n, 0)].tap(|v| v.append(&mut body.binders())),
            Seq(ref bodies) | Alt(ref bodies) => {
                let mut res = vec![];
                for body in bodies {
                    res.append(&mut body.binders());
                }
                res
            }
            Scope(_, _) => vec![], // No more bindings in this scope
            Star(ref body) | Plus(ref body) => {
                body.binders().into_iter().map(|(n, depth)| (n, depth + 1)).collect()
            }
            ComputeSyntax(_, ref body)
            | SynImport(ref body, _, _)
            | NameImport(ref body, _)
            | QuoteDeepen(ref body, _)
            | QuoteEscape(ref body, _)
            | Reserved(ref body, _) => body.binders(),
            Biased(ref body_a, ref body_b) => {
                body_a.binders().tap(|v| v.append(&mut body_b.binders()))
            }
            Anyways(_) | Impossible | Literal(_) | AnyToken | AnyAtomicToken | VarRef | Call(_) => vec![],
        }
    }

    // In this grammar, what kind of thing is `n`? Outer `None` means "not found",
    // inner means "not a call".
    pub fn find_named_call(&self, n: Name) -> Option<Option<Name>> {
        match *self {
            Named(this_n, ref sub) if this_n == n => {
                // Pass though any number of `Import`s:
                let mut sub = sub;
                while let NameImport(ref new_sub, _) = **sub {
                    sub = new_sub;
                }
                match **sub {
                    Call(nt) => Some(Some(nt)),
                    AnyAtomicToken => Some(None),
                    _ => None,
                }
            }
            Named(_, _) => None, // Otherwise, skip
            Call(_) => None,
            Scope(_, _) => None, // Only look in the current scope
            Anyways(_) | Impossible | Literal(_) | AnyToken | AnyAtomicToken | VarRef => None,
            Star(ref body)
            | Plus(ref body)
            | ComputeSyntax(_, ref body)
            | SynImport(ref body, _, _)
            | NameImport(ref body, _)
            | QuoteDeepen(ref body, _)
            | QuoteEscape(ref body, _)
            | Reserved(ref body, _) => body.find_named_call(n),
            Seq(ref bodies) | Alt(ref bodies) => {
                for body in bodies {
                    let sub_fnc = body.find_named_call(n);
                    if sub_fnc.is_some() {
                        return sub_fnc;
                    }
                }
                None
            }
            Biased(ref body_a, ref body_b) => {
                body_a.find_named_call(n).or_else(|| body_b.find_named_call(n))
            }
        }
    }
}

impl Clone for SyntaxExtension {
    fn clone(&self) -> SyntaxExtension { SyntaxExtension(self.0.clone()) }
}
impl PartialEq for SyntaxExtension {
    /// pointer equality! (for testing)
    fn eq(&self, other: &SyntaxExtension) -> bool {
        self as *const SyntaxExtension == other as *const SyntaxExtension
    }
}

// This kind of struct is theoretically possible to add to the `Reifiable!` macro,
// but I don't feel like doing it right now
impl ::runtime::reify::Reifiable for SyntaxExtension {
    fn ty_name() -> Name { n("syntax_extension") }

    fn reify(&self) -> ::runtime::eval::Value {
        ::runtime::reify::reify_2ary_function(self.0.clone())
    }

    fn reflect(v: &::runtime::eval::Value) -> Self {
        SyntaxExtension(::runtime::reify::reflect_2ary_function(v.clone()))
    }
}

impl ::std::fmt::Debug for SyntaxExtension {
    fn fmt(&self, formatter: &mut ::std::fmt::Formatter) -> Result<(), ::std::fmt::Error> {
        formatter.write_str("[syntax extension]")
    }
}

pub type SynEnv = Assoc<Name, Rc<FormPat>>;

/// Currently only used for DDDs
pub fn plug_hole(outer: &Rc<FormPat>, hole: Name, inner: &Rc<FormPat>) -> Rc<FormPat> {
    match **outer {
        Call(n) => {
            if n == hole {
                inner.clone()
            } else {
                outer.clone()
            }
        }
        Anyways(_) | Impossible | Literal(_) | AnyToken | AnyAtomicToken | VarRef => outer.clone(),
        Seq(ref subs) => Rc::new(Seq(subs.iter().map(|sub| plug_hole(sub, hole, inner)).collect())),
        _ => panic!("What are you doing? What do you even think will happen?"),
    }
}

pub use earley::parse;

/// Parse `tt` with the grammar `f` in an empty syntactic environment.
/// `Call` patterns are errors.
pub fn parse_top<'fun>(
    f: &'fun FormPat,
    tt: &'fun TokenTree,
) -> Result<Ast, /* ParseError<SliceStream<'fun, Token>> */ ::earley::ParseError>
{
    parse(f, &Assoc::new(), tt)
}

use self::FormPat::*;

#[test]
fn basic_parsing() {
    assert_eq!(
        parse_top(&Seq(vec![Rc::new(AnyToken)]), &tokens!("asdf")).unwrap(),
        ast_shape!("asdf")
    );

    assert_eq!(
        parse_top(
            &Seq(vec![Rc::new(AnyToken), Rc::new(Literal(n("fork"))), Rc::new(AnyToken)]),
            &tokens!("asdf" "fork" "asdf")
        )
        .unwrap(),
        ast_shape!("asdf" "fork" "asdf")
    );

    assert_eq!(
        parse_top(
            &Seq(vec![Rc::new(AnyToken), Rc::new(Literal(n("fork"))), Rc::new(AnyToken)]),
            &tokens!("asdf" "fork" "asdf")
        )
        .unwrap(),
        ast_shape!("asdf" "fork" "asdf")
    );

    parse_top(
        &Seq(vec![Rc::new(AnyToken), Rc::new(Literal(n("fork"))), Rc::new(AnyToken)]),
        &tokens!("asdf" "knife" "asdf"),
    )
    .unwrap_err();

    assert_eq!(
        parse_top(
            &Seq(vec![
                Rc::new(Star(Rc::new(Named(n("c"), Rc::new(Literal(n("*"))))))),
                Rc::new(Literal(n("X")))
            ]),
            &tokens!("*" "*" "*" "*" "*" "X")
        )
        .unwrap(),
        ast_shape!({- "c" => ["*", "*", "*", "*", "*"] } "X")
    );
}

#[test]
fn alternation() {
    assert_eq!(parse_top(&form_pat!((alt (lit "A"), (lit "B"))), &tokens!("A")), Ok(ast!("A")));
    assert_eq!(parse_top(&form_pat!((alt (lit "A"), (lit "B"))), &tokens!("B")), Ok(ast!("B")));

    assert_eq!(
        parse_top(
            &form_pat!((alt (lit "A"), (lit "B"), [(lit "X"), (lit "B")])),
            &tokens!("X" "B")
        ),
        Ok(ast!(("X" "B")))
    );

    assert_eq!(
        parse_top(
            &form_pat!((alt [(lit "A"), (lit "X")], (lit "B"), [(lit "A"), (lit "B")])),
            &tokens!("A" "B")
        ),
        Ok(ast!(("A" "B")))
    );

    assert_eq!(
        parse_top(
            &form_pat!((alt (lit "A"), (lit "B"), [(lit "A"), (lit "B")])),
            &tokens!("A" "B")
        ),
        Ok(ast!(("A" "B")))
    );
}

#[test]
fn advanced_parsing() {
    assert_eq!(
        parse_top(
            &form_pat!([(star (named "c", (alt (lit "X"), (lit "O")))), (lit "!")]),
            &tokens!("X" "O" "O" "O" "X" "X" "!")
        )
        .unwrap(),
        ast_shape!({- "c" => ["X", "O", "O", "O", "X", "X"]} "!")
    );

    // TODO: this hits the bug where `earley.rs` doesn't like nullables in `Seq` or `Star`

    assert_eq!(
        parse_top(
            &form_pat!((star (biased [(named "c", (anyways "ttt")), (alt (lit "X"), (lit "O"))],
                                     [(named "c", (anyways "igi")), (alt (lit "O"), (lit "H"))]))),
            &tokens!("X" "O" "H" "O" "X" "H" "O")
        )
        .unwrap(),
        ast!({ - "c" => ["ttt", "ttt", "igi", "ttt", "ttt", "igi", "ttt"]})
    );

    let ttt = simple_form("tictactoe", form_pat!( [(named "c", (alt (lit "X"), (lit "O")))]));
    let igi = simple_form("igetit", form_pat!( [(named "c", (alt (lit "O"), (lit "H")))]));

    assert_eq!(
        parse_top(
            &form_pat!((star (named "outer", (biased (scope ttt.clone()), (scope igi.clone()))))),
            &tokens!("X" "O" "H" "O" "X" "H" "O")
        )
        .unwrap(),
        ast!({ - "outer" =>
            [{ttt.clone(); ["c" => "X"]}, {ttt.clone(); ["c" => "O"]},
             {igi.clone(); ["c" => "H"]}, {ttt.clone(); ["c" => "O"]},
             {ttt.clone(); ["c" => "X"]}, {igi; ["c" => "H"]},
             {ttt; ["c" => "O"]}]})
    );

    let pair_form = simple_form(
        "pair",
        form_pat!([(named "lhs", (lit "a")),
                                                   (named "rhs", (lit "b"))]),
    );
    let toks_a_b = tokens!("a" "b");
    assert_eq!(
        parse(
            &form_pat!((call "Expr")),
            &assoc_n!(
                         "other_1" => Rc::new(Scope(simple_form("o", form_pat!((lit "other"))),
                                                    ::beta::ExportBeta::Nothing)),
                         "Expr" => Rc::new(Scope(pair_form.clone(), ::beta::ExportBeta::Nothing)),
                         "other_2" =>
                             Rc::new(Scope(simple_form("o", form_pat!((lit "otherother"))),
                                           ::beta::ExportBeta::Nothing))),
            &toks_a_b
        )
        .unwrap(),
        ast!({pair_form ; ["rhs" => "b", "lhs" => "a"]})
    );
}

// TODO: We pretty much have to use Rc<> to store grammars in Earley
//  (that's fine; they're Rc<> already!).
// But then, we pretty much have to store Earley rules in Rc<> also (ick!)...
// ...and how do we test for equality on grammars and rules?
// I think we pretty much need to force memoization on the syntax extension functions...

#[test]
fn extensible_parsing() {
    fn static_synex(s: SynEnv, _: Ast) -> SynEnv {
        assoc_n!(
            "a" => Rc::new(form_pat!(
                (star (named "c", (alt (lit "AA"), [(lit "Back"), (call "o"), (lit ".")]))))),
            "b" => Rc::new(form_pat!((lit "BB")))
        )
        .set_assoc(&s)
    }

    assert_eq!(
        parse_top(&form_pat!((extend [], "b", static_synex)), &tokens!("BB")),
        Ok(ast!("BB"))
    );

    let orig = Rc::new(assoc_n!(
        "o" => Rc::new(form_pat!(
            (star (named "c",
                (alt (lit "O"), [(lit "Extend"), (extend [], "a", static_synex), (lit ".")])))))));

    assert_eq!(
        parse(
            &form_pat!((call "o")),
            &orig,
            &tokens!("O" "O" "Extend" "AA" "AA" "Back" "O" "." "AA" "." "O")
        )
        .unwrap(),
        ast!({- "c" => ["O", "O", ("Extend" {- "c" => ["AA", "AA", ("Back" {- "c" => ["O"]} "."), "AA"]} "."), "O"]})
    );

    assert_eq!(
        parse(
            &form_pat!((call "o")),
            &orig,
            &tokens!("O" "O" "Extend" "AA" "AA" "Back" "AA" "." "AA" "." "O")
        )
        .is_err(),
        true
    );

    assert_eq!(
        parse(&form_pat!((call "o")), &orig, &tokens!("O" "O" "Extend" "O" "." "O")).is_err(),
        true
    );

    let mt_syn_env = Rc::new(Assoc::new());

    fn counter_synex(_: SynEnv, a: Ast) -> SynEnv {
        let count = match a {
            IncompleteNode(mbe) => mbe,
            _ => panic!(),
        }
        .get_rep_leaf_or_panic(n("n"))
        .len();

        assoc_n!("count" => Rc::new(Literal(n(&count.to_string()))))
    }

    assert_m!(
        parse(
            &form_pat!((extend (star (named "n", (lit "X"))), "count", counter_synex)),
            &mt_syn_env,
            &tokens!("X" "X" "X" "4")
        ),
        Err(_)
    );

    assert_eq!(
        parse(
            &form_pat!((extend (star (named "n", (lit "X"))), "count", counter_synex)),
            &mt_syn_env,
            &tokens!("X" "X" "X" "X" "4")
        ),
        Ok(ast!("4"))
    );

    assert_m!(
        parse(
            &form_pat!((extend (star (named "n", (lit "X"))), "count", counter_synex)),
            &mt_syn_env,
            &tokens!("X" "X" "X" "X" "X" "4")
        ),
        Err(_)
    );
}

// #[test]
// fn test_syn_env_parsing() as{
// let mut se = Assoc::new();
// se = se.set(n("xes"), Box::new(Form { grammar: form_pat!((star (lit "X")),
// relative_phase)}))
// }
