// TODO: there's no reason for this and `earley.rs` to be different files.

#![macro_use]

use read::{Token, TokenTree, DelimChar, Group, Simple};
use name::*;
use form::{Form,simple_form};
use std::boxed::Box;
use std::clone::Clone;
use ast::Ast;
use ast::Ast::*;
use util::assoc::Assoc;
use std::rc::Rc;
use beta::{Beta, ExportBeta};

impl Token {
    fn to_ast(&self) -> Ast {
        match *self {
            Simple(ref s) => Atom(*s),
            Group(ref _s, ref _delim, ref body) => {
                Shape(body.t.iter().map(|t| t.to_ast()).collect())
            }
        }
    }
}


custom_derive! {
    /**
      `FormPat` is a grammar. Think EBNF, but more extended.

      Most kinds of grammar nodes produce an `Ast` of either `Shape` or `Env`,
       but `Named` and `Scope` are special:
       everything outside of a `Named` (up to a `Scope`, if any) is discarded,
        and `Scope` produces a `Node`, which maps names to what they got.
     */
    #[derive(Debug, Clone, Reifiable)]
    pub enum FormPat {
        /// Matches 0 tokens, produces the argument
        Anyways(Ast),
        /// Never matches
        Impossible,

        Literal(Name),
        AnyToken,
        AnyAtomicToken,
        VarRef,
        Delimited(Name, DelimChar, Rc<FormPat>),
        Seq(Vec<Rc<FormPat>>),
        Star(Rc<FormPat>),
        Plus(Rc<FormPat>),
        Alt(Vec<Rc<FormPat>>),
        Biased(Rc<FormPat>, Rc<FormPat>),

        /// Lookup a nonterminal in the current syntactic environment.
        Call(Name),
        /**
         * This is where syntax gets reflective.
         * Evaluates its body (one phase up)
         *  as a function from the current `SynEnv` to a new one,
         *  and names the result in the current scope.
         */
        ComputeSyntax(Name, Rc<FormPat>),

        /// Makes a node and limits the region where names are meaningful. `Beta` defines export.
        Scope(Rc<Form>, ExportBeta),
        Named(Name, Rc<FormPat>),

        /**
         * This is where syntax gets extensible.
         * Parses its body in the named NT of the syntax environment computed from
         *  the LHS and the current syntax environment.
         * TODO: I think this obviates `ComputeSyntax`
         */
        SynImport(Rc<FormPat>, Name, SyntaxExtension),
        /**
         * FOOTGUN:  NameImport(Named(...), ...) is almost always wrong.
         * (write Named(NameImport(..., ...)) instead)
         * TODO: make this better
         */
        NameImport(Rc<FormPat>, Beta),
        QuoteDeepen(Rc<FormPat>),
        QuoteEscape(Rc<FormPat>, u8)
    }
}
pub struct SyntaxExtension(pub Rc<Box<(Fn(SynEnv, Ast) -> SynEnv)>>);


impl Clone for SyntaxExtension {
    fn clone(&self) -> SyntaxExtension {
        SyntaxExtension(self.0.clone())
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


pub use ::earley::parse;

/** Parse `tt` with the grammar `f` in an empty syntactic environment.
 `Call` patterns are errors. */
pub fn parse_top<'fun>(f: &'fun FormPat, tt: &'fun TokenTree)
        -> Result<Ast, /*ParseError<SliceStream<'fun, Token>>*/ ::earley::ParseError> {

    parse(f, &Assoc::new(), tt)
}


use self::FormPat::*;

#[test]
fn basic_parsing() {
    assert_eq!(parse_top(&Seq(vec![Rc::new(AnyToken)]), &tokens!("asdf")).unwrap(), ast_shape!("asdf"));

    assert_eq!(parse_top(&Seq(vec![Rc::new(AnyToken), Rc::new(Literal(n("fork"))), Rc::new(AnyToken)]),
               &tokens!("asdf" "fork" "asdf")).unwrap(),
               ast_shape!("asdf" "fork" "asdf"));

    assert_eq!(parse_top(&Seq(vec![Rc::new(AnyToken), Rc::new(Literal(n("fork"))), Rc::new(AnyToken)]),
               &tokens!("asdf" "fork" "asdf")).unwrap(),
               ast_shape!("asdf" "fork" "asdf"));

    parse_top(&Seq(vec![Rc::new(AnyToken), Rc::new(Literal(n("fork"))), Rc::new(AnyToken)]),
          &tokens!("asdf" "knife" "asdf")).unwrap_err();

    assert_eq!(parse_top(&Seq(vec![Rc::new(Star(Rc::new(Named(n("c"), Rc::new(Literal(n("*"))))))),
                                   Rc::new(Literal(n("X")))]),
                     &tokens!("*" "*" "*" "*" "*" "X")).unwrap(),
               ast_shape!({- "c" => ["*", "*", "*", "*", "*"] } "X"));
}

#[test]
fn alternation() {
    assert_eq!(parse_top(&form_pat!((alt (lit "A"), (lit "B"))), &tokens!("A")),
               Ok(ast!("A")));
    assert_eq!(parse_top(&form_pat!((alt (lit "A"), (lit "B"))), &tokens!("B")),
               Ok(ast!("B")));

    assert_eq!(parse_top(
        &form_pat!((alt (lit "A"), (lit "B"), [(lit "X"), (lit "B")])),
            &tokens!("X" "B")),
                Ok(ast!(("X" "B"))));

    assert_eq!(parse_top(
        &form_pat!((alt [(lit "A"), (lit "X")], (lit "B"), [(lit "A"), (lit "B")])),
            &tokens!("A" "B")),
                Ok(ast!(("A" "B"))));

    assert_eq!(parse_top(
        &form_pat!((alt (lit "A"), (lit "B"), [(lit "A"), (lit "B")])),
            &tokens!("A" "B")),
               Ok(ast!(("A" "B"))));


}

#[test]
fn advanced_parsing() {
    assert_eq!(parse_top(&form_pat!([(star (named "c", (alt (lit "X"), (lit "O")))), (lit "!")]),
                         &tokens!("X" "O" "O" "O" "X" "X" "!")).unwrap(),
               ast_shape!({- "c" => ["X", "O", "O", "O", "X", "X"]} "!"));

    // TODO: this hits the bug where `earley.rs` doesn't like nullables in `Seq` or `Star`

    assert_eq!(parse_top(
            &form_pat!((star (biased [(named "c", (anyways "ttt")), (alt (lit "X"), (lit "O"))],
                                     [(named "c", (anyways "igi")), (alt (lit "O"), (lit "H"))]))),
            &tokens!("X" "O" "H" "O" "X" "H" "O")).unwrap(),
        ast!({ - "c" => ["ttt", "ttt", "igi", "ttt", "ttt", "igi", "ttt"]}));


    let ttt = simple_form("tictactoe",
        form_pat!( [(named "c", (alt (lit "X"), (lit "O")))]));
    let igi = simple_form("igetit",
        form_pat!( [(named "c", (alt (lit "O"), (lit "H")))]));

    assert_eq!(parse_top(
            &form_pat!((star (named "outer", (biased (scope ttt.clone()), (scope igi.clone()))))),
            &tokens!("X" "O" "H" "O" "X" "H" "O")).unwrap(),
        ast!({ - "outer" =>
            [{ttt.clone(); ["c" => "X"]}, {ttt.clone(); ["c" => "O"]},
             {igi.clone(); ["c" => "H"]}, {ttt.clone(); ["c" => "O"]},
             {ttt.clone(); ["c" => "X"]}, {igi; ["c" => "H"]},
             {ttt; ["c" => "O"]}]}));

    let pair_form = simple_form("pair", form_pat!([(named "lhs", (lit "a")),
                                                   (named "rhs", (lit "b"))]));
    let toks_a_b = tokens!("a" "b");
    assert_eq!(parse(&form_pat!((call "Expr")),
                     &assoc_n!(
                         "other_1" => Rc::new(Scope(simple_form("o", form_pat!((lit "other"))),
                                                    ::beta::ExportBeta::Nothing)),
                         "Expr" => Rc::new(Scope(pair_form.clone(), ::beta::ExportBeta::Nothing)),
                         "other_2" =>
                             Rc::new(Scope(simple_form("o", form_pat!((lit "otherother"))),
                                           ::beta::ExportBeta::Nothing))),
                     &toks_a_b).unwrap(),
               ast!({pair_form ; ["rhs" => "b", "lhs" => "a"]}));
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
        ).set_assoc(&s)
    }

    assert_eq!(parse_top(&form_pat!((extend [], "b", static_synex)), &tokens!("BB")),
               Ok(ast!("BB")));


    let orig = Rc::new(assoc_n!(
        "o" => Rc::new(form_pat!(
            (star (named "c",
                (alt (lit "O"), [(lit "Extend"), (extend [], "a", static_synex), (lit ".")])))))));

    assert_eq!(
        parse(&form_pat!((call "o")), &orig,
            &tokens!("O" "O" "Extend" "AA" "AA" "Back" "O" "." "AA" "." "O")).unwrap(),
        ast!({- "c" => ["O", "O", ("Extend" {- "c" => ["AA", "AA", ("Back" {- "c" => ["O"]} "."), "AA"]} "."), "O"]}));

    assert_eq!(
        parse(&form_pat!((call "o")), &orig,
            &tokens!("O" "O" "Extend" "AA" "AA" "Back" "AA" "." "AA" "." "O")).is_err(),
        true);

    assert_eq!(
        parse(&form_pat!((call "o")), &orig,
            &tokens!("O" "O" "Extend" "O" "." "O")).is_err(),
        true);

    let mt_syn_env = Rc::new(Assoc::new());

    fn counter_synex(_: SynEnv, a: Ast) -> SynEnv {
        let count = match a { IncompleteNode(mbe) => mbe, _ => panic!() }
            .get_rep_leaf_or_panic(&n("n")).len();

        assoc_n!("count" => Rc::new(Literal(n(&count.to_string()))))
    }

    assert_m!(
        parse(&form_pat!((extend (star (named "n", (lit "X"))), "count", counter_synex)),
            &mt_syn_env, &tokens!("X" "X" "X" "4")),
        Err(_));

    assert_eq!(
        parse(&form_pat!((extend (star (named "n", (lit "X"))), "count", counter_synex)),
            &mt_syn_env, &tokens!("X" "X" "X" "X" "4")),
        Ok(ast!("4")));

    assert_m!(
        parse(&form_pat!((extend (star (named "n", (lit "X"))), "count", counter_synex)),
            &mt_syn_env, &tokens!("X" "X" "X" "X" "X" "4")),
        Err(_));



}


/*
#[test]
fn test_syn_env_parsing() as{
    let mut se = Assoc::new();
    se = se.set(n("xes"), Box::new(Form { grammar: form_pat!((star (lit "X")),
                                          relative_phase)}))
}*/
