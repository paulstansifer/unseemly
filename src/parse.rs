#![macro_use]

use read::{Token, TokenTree, DelimChar, Group, Simple};
use name::*;
use form::{Form, simple_form};
use std::boxed::Box;
use std::clone::Clone;
use ast::Ast;
use ast::Ast::*;
use util::assoc::Assoc;
use util::mbe::EnvMBE;
use std::rc::Rc;
use std::marker::PhantomData;
use beta::Beta;
use std;

extern crate combine;

use self::combine::{Parser, ParseResult, ParseError};
use self::combine::primitives::{State, SliceStream, Positioner};
use self::combine::combinator::ParserExt;


impl<'t> Token {
    fn to_ast(&self) -> Ast<'t> {
        match *self {
            Simple(ref s) => Atom(s.clone()),
            Group(ref _s, ref _delim, ref body) => {
                Shape(body.t.iter().map(|t| t.to_ast()).collect())
            }
        }
    }
}


custom_derive! {
    /**
      FormPat is a grammar for syntax forms.

      Most kinds of grammar nodes produce an `Ast` of either `Shape` or `Env`,
       but `Named` and `Scope` are special:
       everything outside of a `Named` (up to a `Scope`, if any) is discarded,
        and `Scope` produces a `Node`, which maps names to what they got.
     */
    #[derive(Debug, Clone, Reifiable(lifetime))]
    pub enum FormPat<'t> {
        /// Matches 0 tokens, produces the argument
        Anyways(Ast<'t>),
        /// Never matches
        Impossible,

        Literal(Name),
        AnyToken,
        AnyAtomicToken,
        VarRef,
        Delimited(Name, DelimChar, Box<FormPat<'t>>),
        Seq(Vec<FormPat<'t>>),
        Star(Box<FormPat<'t>>),
        Alt(Vec<FormPat<'t>>),
        Biased(Box<FormPat<'t>>, Box<FormPat<'t>>),

        // TODO: there should be an explicit `FormNode` pattern that wraps the result in a 
        // Node indicating the `Form`. (Some `Form`s might only exist for parsing,
        // and don't want to be on the `Ast`.) Also, `SynEnv` can go back to containing
        // a single `FormPat`, so we can use `Biased` if necessary.

        /**
         * Lookup a nonterminal in the current syntactic environment.
         */ 
        Call(Name),
        /** 
         * This is where syntax gets reflective.
         * Evaluates its body (one phase up)
         *  as a function from the current `SynEnv` to a new one, 
         *  and names the result in the current scope. 
         */
        ComputeSyntax(Name, Box<FormPat<'t>>),

        /** Makes a node and limits the region where names are meaningful. */
        Scope(Rc<Form<'t>>), 
        Named(Name, Box<FormPat<'t>>),

        /**
         * This is where syntax gets extensible.
         * Parses its body in the named syntactic environment.
         * TODO: do we need both this and `ComputeSyntax`?
         */
        SynImport(Name, SyntaxExtension<'t>),
        /**
         * FOOTGUN:  NameImport(Named(...), ...) is almost always wrong.
         * (write Named(NameImport(..., ...)) instead) 
         * TODO: make this better
         */
        NameImport(Box<FormPat<'t>>, Beta),
        //NameExport(Beta, Box<FormPat<'t>>) // This might want to go on some existing pattern
    }
}
pub struct SyntaxExtension<'t>(pub Rc<Box<(Fn(SynEnv<'t>) -> SynEnv<'t>) + 't>>);

impl<'t> Clone for SyntaxExtension<'t> {
    fn clone(&self) -> SyntaxExtension<'t> {
        SyntaxExtension(self.0.clone())
    }
}

// This kind of struct is theoretically possible to add to the `Reifiable!` macro,
// but I don't feel like doing it right now
impl<'t> ::runtime::reify::Reifiable<'t> for SyntaxExtension<'t> {
    fn ty_name() -> Name { n("syntax_extension") } 
    
    fn reify(&self) -> ::runtime::eval::Value<'t> { 
        ::runtime::reify::reify_1ary_function(self.0.clone())
    }
    
    fn reflect(v: &::runtime::eval::Value<'t>) -> Self {
        SyntaxExtension(::runtime::reify::reflect_1ary_function(v.clone()))
    }
}

impl<'t> std::fmt::Debug for SyntaxExtension<'t> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        formatter.write_str("[syntax extension]")
    }
}

pub type SynEnv<'t> = Assoc<Name, FormPat<'t>>;

struct FormPatParser<'form, 'tokens: 'form, 't: 'tokens> {
    f: &'form FormPat<'t>,
    se: SynEnv<'t>,
    token_phantom: PhantomData<&'tokens usize>
}

impl<'t> Positioner for Token {
    type Position = usize;
    fn start() -> usize { 0 }
    fn update(&self, position: &mut usize) { *position += 1 as usize }
}

impl<'form, 'tokens, 't: 'form> FormPatParser<'form, 'tokens, 't> {
    fn parse_tokens(&'form mut self, ts: &'tokens Vec<Token>)
            -> ParseResult<Ast<'t>, SliceStream<'tokens, Token>> {
        
        self.parse_state(State::new(SliceStream::<'tokens, Token>(ts.as_slice())))
    }

    fn descend<'subform>(&self, f: &'subform FormPat<'t>)
            -> FormPatParser<'subform, 'tokens, 't> {
        FormPatParser{f: f, se: self.se.clone(), token_phantom: PhantomData}
    }
    
    fn extend<'subform>(&self, f: &'subform FormPat<'t>, se: SynEnv<'t>)
            -> FormPatParser<'subform, 'tokens, 't> {
        FormPatParser{f: f, se: se, token_phantom: PhantomData}
    }

}

/** Parse `tt` with the grammar `f` in the environment `se`.
  The environment is used for lookup when `Call` patterns are reached. */
pub fn parse<'fun, 't: 'fun>(f: &'fun FormPat<'t>, se: SynEnv<'t>, tt: &'fun TokenTree)
        -> Result<Ast<'t>, ParseError<SliceStream<'fun, Token>>> {
    let (res, consumed) = 
        try!(FormPatParser{f: f, se: se, token_phantom: PhantomData}.parse_tokens(&tt.t)
            .map_err(|consumed| consumed.into_inner()));
    // TODO: this seems to lead to bad error messages 
    //  (Essentially, asking the user why they didn't end the file
    //    right after the last thing that did parse correctly)
    let (_, _) = try!(combine::eof().parse_state(consumed.into_inner())
        .map_err(|consumed| consumed.into_inner()));
    Ok(res)
}


/** Parse `tt` with the grammar `f` in an empty syntactic environment.
 `Call` patterns are errors. */
pub fn parse_top<'fun, 't>(f: &'fun FormPat<'t>, tt: &'fun TokenTree)
        -> Result<Ast<'t>, ParseError<SliceStream<'fun, Token>>> {
        
    parse(f, Assoc::new(), tt)
}

impl<'form, 'tokens, 't> combine::Parser for FormPatParser<'form, 'tokens, 't> {
    type Input = SliceStream<'tokens, Token>;
    type Output = Ast<'t>;
    
    fn parse_state<'f>(self: &'f mut FormPatParser<'form, 'tokens, 't>, inp: State<Self::Input>)
          -> ParseResult<Self::Output, Self::Input> {

        fn ast_ify<'t, I>(res : (&Token, I)) -> (Ast<'t>, I) {
            let (got, inp) = res;
            (got.to_ast(), inp)
        }

        match self.f {
            &Anyways(ref ast) => {
                combine::value(ast.clone()).parse_lazy(inp)
            }
            &Impossible => {
                combine::unexpected("impossible").parse_state(inp).map(|_| panic!(""))
            }
            &Literal(exp_tok) => {
                combine::satisfy(|tok: &'tokens Token| {tok == &Simple(exp_tok)})
                    .parse_state(inp).map(ast_ify)
            }
            &AnyToken => { combine::any().parse_state(inp).map(ast_ify) }
            &AnyAtomicToken => {
                combine::satisfy(|tok: &'tokens Token| { 
                    match *tok { Simple(_) => true, _ => false } }).parse_state(inp).map(ast_ify)
            }
            &VarRef => {
                match inp.uncons() {
                    Ok((&Simple(t), rest)) => { Ok((VariableReference(t), rest)) }
                    Ok((&Group(_,_,_), rest)) => { 
                        combine::unexpected("group").parse_state(rest.into_inner())
                            .map(|_| panic!(""))
                    }
                    Err(e) => { Err(e) }
                }
            }
            &Delimited(ref exp_extra, ref exp_delim, ref f) => {
                let (tok, rest) = try!(inp.uncons());
                match *tok {
                    Group(ref extra, ref delim, ref body)
                    if (extra, delim) == (&exp_extra, &exp_delim) => {
                        self.descend(f).parse_tokens(&body.t)
                    },
                    // bad error message; improve:
                    _ => {
                        combine::unexpected("non-group").parse_state(rest.into_inner())
                            .map(|_| panic!(""))
                    }
                }
            }
            &Seq(ref fs) => {
                let mut subs = vec![];
                let mut remaining = inp;
                for f in fs {
                    let (parsed, rest) = try!(self.descend(&f).parse_state(remaining));
                    subs.push(parsed);
                    remaining = rest.into_inner();
                }
                combine::value(Shape(subs)).parse_state(remaining)
            }
            &Star(ref f) => {
                combine::many(self.descend(f)).parse_state(inp)
            }
            &Alt(ref fs) => {
                let parsers: Vec<_> = fs.iter().map(
                    |f| combine::try(self.descend(&f))).collect();
                combine::choice(parsers).parse_state(inp)
            }
            &Biased(ref lhs, ref rhs) => {
                combine::try(self.descend(lhs)).or(self.descend(rhs)).parse_state(inp)
            }
            &Call(ref n) => {
                let deeper_pat : &'f FormPat = self.se.find(&n).unwrap();
                self.descend(deeper_pat).parse_state(inp)

/*                
                // Try all the forms at this nonterminal, and record which one we got
                // with the `Node` AST component. 
                let deeper_forms : &'f Vec<Rc<Form>> = self.se.find(&n).unwrap();
                let parsers : Vec<_> = deeper_forms.iter().map(
                    |f| combine::try(self.descend(&f.grammar)).map(
                            move |parse_res| Node(f.clone(), Rc::new(parse_res))))
                    .collect();
                combine::choice(parsers).parse_state(inp)
                */
            }
            
            &ComputeSyntax(ref _name, ref _f) => {
                panic!("TODO")
            }
        
            &Named(ref name, ref f) => {
                self.descend(f).parse_state(inp).map(|parse_res| 
                    (IncompleteNode(EnvMBE::new_from_leaves(
                        Assoc::new().set(*name, parse_res.0))),
                     parse_res.1))
            }
            &Scope(ref form) => {
                self.descend(&form.grammar).parse_state(inp).map(|parse_res|
                    (Node(form.clone(), parse_res.0.flatten()),
                     parse_res.1))
            }

            &NameImport(ref f, ref beta) => {
                self.descend(f).parse_state(inp).map(|parse_res|
                    (ExtendEnv(Box::new(parse_res.0), beta.clone()), parse_res.1))
            }
            
            &SynImport(ref name, ref f) => {
                let new_se = f.0(self.se.clone());
                self.extend(new_se.find_or_panic(&name), new_se.clone()).parse_state(inp)
            }
        }
    }
}

use self::FormPat::*;

#[test]
fn basic_parsing() {    
    assert_eq!(parse_top(&Seq(vec![AnyToken]), &tokens!("asdf")).unwrap(), ast_shape!("asdf"));
    
    assert_eq!(parse_top(&Seq(vec![AnyToken, Literal(n("fork")), AnyToken]),
               &tokens!("asdf" "fork" "asdf")).unwrap(),
               ast_shape!("asdf" "fork" "asdf"));
               
    assert_eq!(parse_top(&Seq(vec![AnyToken, Literal(n("fork")), AnyToken]),
               &tokens!("asdf" "fork" "asdf")).unwrap(),
               ast_shape!("asdf" "fork" "asdf"));
               
    parse_top(&Seq(vec![AnyToken, Literal(n("fork")), AnyToken]),
          &tokens!("asdf" "knife" "asdf")).unwrap_err();
          
    assert_eq!(parse_top(&Seq(vec![Star(Box::new(Named(n("c"), Box::new(Literal(n("*")))))),
                                   Literal(n("X"))]),
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
    /* //TODO: I'm not sure I can fix this with a combinator parser.
    assert_eq!(parse_top(
        &form_pat!((alt (lit "A"), (lit "B"), [(lit "A"), (lit "B")])),
            &tokens!("A" "B")), 
               Ok(ast!(("A" "B"))));
    */

}

#[test]
fn advanced_parsing() {    
    assert_eq!(parse_top(&form_pat!([(star (named "c", (alt (lit "X"), (lit "O")))), (lit "!")]),
                         &tokens!("X" "O" "O" "O" "X" "X" "!")).unwrap(),
               ast_shape!({- "c" => ["X", "O", "O", "O", "X", "X"]} "!"));

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
    assert_eq!(parse(&form_pat!((call "expr")),
                     assoc_n!(
                         "other_1" => Scope(simple_form("o", form_pat!((lit "other")))),
                         "expr" => Scope(pair_form.clone()),
                         "other_2" => Scope(simple_form("o", form_pat!((lit "otherother"))))),
                     &toks_a_b).unwrap(),
               ast!({pair_form ; ["rhs" => "b", "lhs" => "a"]}));
}

#[test]
fn extensible_parsing() {
    
    fn synex<'t>(s: SynEnv<'t>) -> SynEnv<'t> {
        assoc_n!(
            "a" => form_pat!((star (named "c", (alt (lit "AA"), [(lit "Back"), (call "o"), (lit ".")])))),
            "b" => form_pat!((lit "BB"))
        ).set_assoc(&s)
    }
    
    assert_eq!(parse_top(&form_pat!((extend "b", synex)), &tokens!("BB")).unwrap(),
               ast!("BB"));
               
               
    let orig = assoc_n!(
        "o" => form_pat!((star (named "c", (alt (lit "O"), [(lit "Extend"), (extend "a", synex), (lit ".")]))))
    );
    
    assert_eq!(
        parse(&form_pat!((call "o")), orig.clone(),
            &tokens!("O" "O" "Extend" "AA" "AA" "Back" "O" "." "AA" "." "O")).unwrap(),
        ast!({- "c" => ["O", "O", ("Extend" {- "c" => ["AA", "AA", ("Back" {- "c" => ["O"]} "."), "AA"]} "."), "O"]}));

    assert_eq!(
        parse(&form_pat!((call "o")), orig.clone(),
            &tokens!("O" "O" "Extend" "AA" "AA" "Back" "AA" "." "AA" "." "O")).is_err(),
        true);

    assert_eq!(
        parse(&form_pat!((call "o")), orig,
            &tokens!("O" "O" "Extend" "O" "." "O")).is_err(),
        true);


}
/*
#[test]
fn test_syn_env_parsing() as{
    let mut se = Assoc::new();
    se = se.set(n("xes"), Box::new(Form { grammar: form_pat!((star (lit "X")),
                                          relative_phase)}))
}*/