#![macro_use]

use crate::{
    ast::Ast,
    beta::{Beta, ExportBeta},
    form::Form,
    name::*,
    runtime::{eval::Value, reify},
    util::assoc::Assoc,
};
use std::{boxed::Box, clone::Clone, rc::Rc};

custom_derive! {
    /// `FormPat` defines a pattern in a grammar. Think EBNF, but more extended.

    /// Most kinds of grammar nodes produce an `Ast` of either `Shape` or `Env`,
    ///  but `Named` and `Scope` are special:
    ///  everything outside of a `Named` (up to a `Scope`, if any) is discarded,
    ///   and `Scope` produces a `Node`, which maps names to what they got.
    #[derive(Debug, Clone, Reifiable, PartialEq)]
    pub enum FormPat {
        /// Matches 0 tokens, produces the `Ast`
        Anyways(Ast),
        /// Never matches
        Impossible,

        /// Matches actual text!
        /// The regex must have a single capturing group.
        /// The optional string is a TextMate syntax category.
        Scan(Scanner, Option<String>),

        /// Marks this rule as too commonly-used to be informative;
        ///  prevents display of this rule in parse errors,
        Common(Rc<FormPat>),

        /// Matches an atom or varref, but not if it's on the list of reserved words
        Reserved(Rc<FormPat>, Vec<Name>),
        /// Matches if the sub-pattern equals the given name
        Literal(Rc<FormPat>, Name),

        /// Matches an atom, turns it into a `VariableReference`
        VarRef(Rc<FormPat>),

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
        /// This is where syntax gets extensible.
        /// Parses its body in the syntax environment computed from
        ///  the LHS and the current syntax environment.
        SynImport(Rc<FormPat>, Rc<FormPat>, SyntaxExtension),

        /// Makes a node and limits the region where names are meaningful. `Beta` defines export.
        Scope(Rc<Form>, ExportBeta),
        /// Matches a pattern and gives it a name (inside the current `Scope`)
        Named(Name, Rc<FormPat>),
        /// Like a `Scope`, but just returns whatever has the given name
        Pick(Rc<FormPat>, Name),

        /// FOOTGUN:  NameImport(Named(...), ...) is almost always wrong.
        ///  (write Named(NameImport(..., ...)) instead)
        /// TODO: make this better
        NameImport(Rc<FormPat>, Beta),
        /// Like `NameImport`, but affects all phases.
        NameImportPhaseless(Rc<FormPat>, Beta),
        /// Quote syntax (the boolean indicates whether it's positive or negative)
        QuoteDeepen(Rc<FormPat>, bool),
        /// Escape syntax quotation (by some number of levels)
        QuoteEscape(Rc<FormPat>, u8)
    }
}

impl std::fmt::Display for FormPat {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.mark_up(None))
    }
}

impl FormPat {
    pub fn mark_up(&self, pos: Option<usize>) -> String {
        match self {
            Anyways(ref ast) => {
                let contents = format!("{}", ast);
                if contents.len() > 20 {
                    format!("anyways{{⋯}}anyways")
                } else {
                    format!("anyways{{ {} }}anyways", contents)
                }
            }
            Impossible => format!("impossible"),
            Scan(ref scanner, _) => format!("/{}/", scanner.0),
            Common(ref body) => format!("common ({})", body),
            Reserved(ref body, ref names) => format!(
                "{} reserving {}",
                body,
                names.iter().map(|name| format!("'{}'", name)).collect::<Vec<_>>().join(" ")
            ),
            Literal(ref _body, name) => format!("\x1b[34m{}\x1b[0m", name),
            VarRef(ref body) => format!("vr ({})", body),
            Seq(ref elts) => {
                let mut formatted_elts = elts.iter().map(|e| format!("{}", e)).collect::<Vec<_>>();
                if let Some(pos) = pos {
                    formatted_elts.insert(pos, "•".to_string());
                }
                format!("[{}]", formatted_elts.join(" "))
            }
            Star(ref body) => format!("{} *", body),
            Plus(ref body) => format!("{} +", body),
            Alt(ref elts) => format!(
                "alt[{}]alt",
                elts.iter().map(|e| format!("{}", e)).collect::<Vec<_>>().join(" ")
            ),
            Biased(ref plan_a, ref plan_b) => format!("{} or{{{}}}or", plan_a, plan_b),
            // In macro definitions, we need a type here, but it's not present in the grammar:
            Call(ref name) => format!(",{{{}}},", name),
            SynImport(ref def, ref body, ref _synex) => match pos {
                None => format!("??syntax extension {} => {} ??", def, body),
                Some(0) => format!("??syntax extension • {} => {} ??", def, body),
                Some(1) => format!("??syntax extension {} => • {} ??", def, body),
                Some(2) => format!("??syntax extension {} => {} • ??", def, body),
                _ => icp!(),
            },

            Scope(ref form, ref ebeta) => {
                format!("'{{{}}}' ??? -> .{{??}}. => {:?}", form.grammar, ebeta)
            }
            Named(name, ref body) => format!("{} := ({})", name, body),
            Pick(ref body, name) => format!("pick {} in {}", name, body),
            NameImport(ref body, ref beta) => format!("{} <-- {:?}", body, beta),
            NameImportPhaseless(ref body, ref beta) => format!("{} <--?? {:?}", body, beta),
            QuoteDeepen(ref body, pos) => format!("??deepen?? {} {}", body, pos),
            QuoteEscape(ref body, levels) => format!("??escape?? {} {}", body, levels),
        }
    }

    // Finds all `Named` nodes, and how many layers of repetition they are underneath.
    pub fn binders(&self) -> Vec<(Name, u8)> {
        use tap::tap::Tap;
        match *self {
            Named(n, ref body) => vec![(n, 0)].tap_mut(|v| v.append(&mut body.binders())),
            Seq(ref bodies) | Alt(ref bodies) => {
                let mut res = vec![];
                for body in bodies {
                    res.append(&mut body.binders());
                }
                res
            }
            Scope(_, _) | Pick(_, _) => vec![], // No more bindings in this scope
            Star(ref body) | Plus(ref body) => {
                body.binders().into_iter().map(|(n, depth)| (n, depth + 1)).collect()
            }
            // TODO: since these belong under `Named`, I suspect they ought to return an empty Vec.
            SynImport(ref body, _, _)
            | NameImport(ref body, _)
            | NameImportPhaseless(ref body, _)
            | QuoteDeepen(ref body, _)
            | QuoteEscape(ref body, _)
            | Common(ref body)
            | Reserved(ref body, _) => body.binders(),
            Biased(ref body_a, ref body_b) => {
                body_a.binders().tap_mut(|v| v.append(&mut body_b.binders()))
            }
            Anyways(_) | Impossible | Literal(_, _) | Scan(_, _) | VarRef(_) | Call(_) => vec![],
        }
    }

    // In this grammar, what kind of thing is `n` (if it's present at all)?
    pub fn find_named_call(&self, n: Name) -> Option<Name> {
        match *self {
            Named(this_n, ref sub) if this_n == n => {
                // Pass though any number of `Import`s:
                let mut sub = sub;
                while let NameImport(ref new_sub, _) = **sub {
                    sub = new_sub;
                }
                match **sub {
                    Call(nt) => Some(nt),
                    _ => None,
                }
            }
            Named(_, _) => None, // Otherwise, skip
            Call(_) => None,
            // TODO: `Pick` should return a result.
            Scope(_, _) | Pick(_, _) => None, // Only look in the current scope
            Anyways(_) | Impossible | Scan(_, _) => None,
            Star(ref body)
            | Plus(ref body)
            | SynImport(ref body, _, _)
            | NameImport(ref body, _)
            | NameImportPhaseless(ref body, _)
            | Literal(ref body, _)
            | VarRef(ref body)
            | QuoteDeepen(ref body, _)
            | QuoteEscape(ref body, _)
            | Common(ref body)
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

    /// Map regular expressions (as strings) to their TextMate categories.
    /// This is a loose approximation of the impossible task of syntax-highlighting a `FormPat`.
    pub fn textmate_categories(&self) -> Vec<(String, String)> {
        match self {
            Scan(scanner, name) => match name {
                Some(name) => vec![(
                    format!("{}", scanner.0)
                        .strip_prefix("^")
                        .unwrap()
                        .replace(r#"\/"#, r#"/"#)
                        .to_string(),
                    name.clone(),
                )],
                None => vec![],
            },
            Reserved(body, reserved) => {
                // TODO: modify `Reserved` to allow customization
                let mut res = body.textmate_categories();
                let matcher = reserved
                    .iter()
                    .map(|word| regex::escape(&word.orig_sp()))
                    .collect::<Vec<_>>()
                    .join("|");
                res.push((matcher, "keyword".to_string()));
                res
            }
            Literal(_, lit) => {
                vec![(regex::escape(&lit.orig_sp()), "keyword.operator".to_string())]
            }
            Scope(form, _) => form.grammar.textmate_categories(),
            Anyways(_) | Impossible | Call(_) => vec![],
            Common(body)
            | VarRef(body)
            | Star(body)
            | Plus(body)
            | SynImport(_, body, _)
            | Named(_, body)
            | Pick(body, _)
            | NameImport(body, _)
            | NameImportPhaseless(body, _)
            | QuoteDeepen(body, _)
            | QuoteEscape(body, _) => body.textmate_categories(),
            Biased(lhs, rhs) => {
                let mut res = lhs.textmate_categories();
                res.append(&mut rhs.textmate_categories());
                res
            }
            Seq(bodies) | Alt(bodies) => {
                let mut res = vec![];
                for body in bodies {
                    res.append(&mut body.textmate_categories());
                }
                res
            }
        }
    }
}

#[derive(Clone)]
pub struct SyntaxExtension(
    pub Rc<Box<(dyn Fn(crate::earley::ParseContext, Ast) -> crate::earley::ParseContext)>>,
);

impl PartialEq for SyntaxExtension {
    /// pointer equality! (for testing)
    fn eq(&self, other: &SyntaxExtension) -> bool {
        self as *const SyntaxExtension == other as *const SyntaxExtension
    }
}

// This kind of struct is theoretically possible to add to the `Reifiable!` macro,
//  but is it worth the complexity?
impl reify::Reifiable for SyntaxExtension {
    fn ty_name() -> Name { n("SyntaxExtension") }

    fn reify(&self) -> Value { reify::reify_2ary_function(self.0.clone()) }

    fn reflect(v: &Value) -> Self { SyntaxExtension(reify::reflect_2ary_function(v.clone())) }
}

impl std::fmt::Debug for SyntaxExtension {
    fn fmt(&self, formatter: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        formatter.write_str("[syntax extension]")
    }
}

pub fn new_scan(regex: &str, cat: Option<String>) -> FormPat {
    Scan(Scanner(regex::Regex::new(&format!("^{}", regex)).unwrap()), cat)
}

#[derive(Clone)]
pub struct Scanner(pub regex::Regex);

impl PartialEq for Scanner {
    fn eq(&self, other: &Scanner) -> bool { self.0.as_str() == other.0.as_str() }
}

impl reify::Reifiable for Scanner {
    fn ty_name() -> Name { n("Scanner") }

    fn reify(&self) -> Value { <String as reify::Reifiable>::reify(&self.0.as_str().to_owned()) }

    fn reflect(v: &Value) -> Self {
        Scanner(regex::Regex::new(&<String as reify::Reifiable>::reflect(v)).unwrap())
    }
}

impl std::fmt::Debug for Scanner {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "[scanner {:?}]", self.0.as_str())
    }
}

pub type SynEnv = Assoc<Name, Rc<FormPat>>;

pub use crate::earley::parse;

/// Parse `tt` with the grammar `f` in an empty syntactic environment.
/// `Call` patterns are errors.
pub fn parse_top(f: &FormPat, toks: &str) -> Result<Ast, crate::earley::ParseError> {
    crate::earley::parse_in_syn_env(f, Assoc::new(), toks)
}

use self::FormPat::*;

#[test]
fn basic_parsing() {
    fn mk_lt(s: &str) -> Rc<FormPat> {
        Rc::new(Literal(Rc::new(new_scan(r"\s*(\S+)", None)), n(s)))
    }
    let atom = Rc::new(new_scan(r"\s*(\S+)", None));

    assert_eq!(parse_top(&Seq(vec![atom.clone()]), tokens_s!("asdf")).unwrap(), ast_shape!("asdf"));

    assert_eq!(
        parse_top(
            &Seq(vec![atom.clone(), mk_lt("fork"), atom.clone()]),
            tokens_s!("asdf" "fork" "asdf")
        )
        .unwrap(),
        ast_shape!("asdf" "fork" "asdf")
    );

    assert_eq!(
        parse_top(
            &Seq(vec![atom.clone(), mk_lt("fork"), atom.clone()]),
            tokens_s!("asdf" "fork" "asdf")
        )
        .unwrap(),
        ast_shape!("asdf" "fork" "asdf")
    );

    parse_top(
        &Seq(vec![atom.clone(), mk_lt("fork"), atom.clone()]),
        tokens_s!("asdf" "knife" "asdf"),
    )
    .unwrap_err();

    assert_eq!(
        parse_top(
            &Seq(vec![Rc::new(Star(Rc::new(Named(n("c"), mk_lt("*"))))), mk_lt("X")]),
            tokens_s!("*" "*" "*" "*" "*" "X")
        )
        .unwrap(),
        ast_shape!({- "c" => ["*", "*", "*", "*", "*"] } "X")
    );
}

#[test]
fn alternation() {
    assert_eq!(
        parse_top(&form_pat!((alt (lit_aat "A"), (lit_aat "B"))), tokens_s!("A")),
        Ok(ast!("A"))
    );
    assert_eq!(
        parse_top(&form_pat!((alt (lit_aat "A"), (lit_aat "B"))), tokens_s!("B")),
        Ok(ast!("B"))
    );

    assert_eq!(
        parse_top(
            &form_pat!((alt (lit_aat "A"), (lit_aat "B"), [(lit_aat "X"), (lit_aat "B")])),
            tokens_s!("X" "B")
        ),
        Ok(ast!(("X" "B")))
    );

    assert_eq!(
        parse_top(
            &form_pat!((alt [(lit_aat "A"), (lit_aat "X")], (lit_aat "B"), [(lit_aat "A"), (lit_aat "B")])),
            tokens_s!("A" "B")
        ),
        Ok(ast!(("A" "B")))
    );

    assert_eq!(
        parse_top(
            &form_pat!((alt (lit_aat "A"), (lit_aat "B"), [(lit_aat "A"), (lit_aat "B")])),
            tokens_s!("A" "B")
        ),
        Ok(ast!(("A" "B")))
    );
}

#[test]
fn advanced_parsing() {
    use crate::form::simple_form;

    assert_eq!(
        parse_top(
            &form_pat!([(star (named "c", (alt (lit_aat "X"), (lit_aat "O")))), (lit_aat "!")]),
            tokens_s!("X" "O" "O" "O" "X" "X" "!")
        )
        .unwrap(),
        ast_shape!({- "c" => ["X", "O", "O", "O", "X", "X"]} "!")
    );

    // TODO: this hits the bug where `earley.rs` doesn't like nullables in `Seq` or `Star`

    assert_eq!(
        parse_top(
            &form_pat!(
                (star (biased [(named "c", (anyways "ttt")), (alt (lit_aat "X"), (lit_aat "O"))],
                              [(named "c", (anyways "igi")), (alt (lit_aat "O"), (lit_aat "H"))]))),
            tokens_s!("X" "O" "H" "O" "X" "H" "O")
        )
        .unwrap(),
        ast!({ - "c" => ["ttt", "ttt", "igi", "ttt", "ttt", "igi", "ttt"]})
    );

    let ttt =
        simple_form("tictactoe", form_pat!( [(named "c", (alt (lit_aat "X"), (lit_aat "O")))]));
    let igi = simple_form("igetit", form_pat!( [(named "c", (alt (lit_aat "O"), (lit_aat "H")))]));

    assert_eq!(
        parse_top(
            &form_pat!((star (named "outer", (biased (scope ttt.clone()), (scope igi.clone()))))),
            tokens_s!("X" "O" "H" "O" "X" "H" "O")
        )
        .unwrap(),
        ast!({ - "outer" =>
            [{ttt.clone(); ["c" => "X"]}, {ttt.clone(); ["c" => "O"]},
             {igi.clone(); ["c" => "H"]}, {ttt.clone(); ["c" => "O"]},
             {ttt.clone(); ["c" => "X"]}, {igi; ["c" => "H"]},
             {ttt; ["c" => "O"]}]})
    );

    assert_eq!(
        parse_top(
            &form_pat!(
                (star (named "it", (pick
                    [(named "even", varref_aat), (named "odd", varref_aat)], "odd")))),
            tokens_s!("A" "B" "C" "D" "E" "F")
        )
        .unwrap(),
        ast!({- "it" => [(vr "B"), (vr "D"), (vr "F")]})
    );

    let pair_form = simple_form(
        "pair",
        form_pat!([(named "lhs", (lit_aat "a")),
                                                   (named "rhs", (lit_aat "b"))]),
    );
    let toks_a_b = tokens_s!("a" "b");
    assert_eq!(
        crate::earley::parse_in_syn_env(
            &form_pat!((call "Expr")),
            syn_env!(
                "other_1" => (scope simple_form("o", form_pat!((lit_aat "other")))),
                "Expr" => (scope pair_form.clone()),
                "other_2" => (scope simple_form("o", form_pat!((lit_aat "otherother"))))
            ),
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
    use crate::{
        ast::AstContents::IncompleteNode,
        earley::{parse_in_syn_env, ParseContext},
    };

    fn static_synex(pc: ParseContext, _: Ast) -> ParseContext {
        ParseContext {
            grammar: assoc_n!(
                "a" => Rc::new(form_pat!(
                    (star (named "c", (alt (lit_aat "AA"),
                                           [(lit_aat "Back"), (call "o"), (lit_aat "#")]))))),
                "b" => Rc::new(form_pat!((lit_aat "BB")))
            )
            .set_assoc(&pc.grammar),
            ..pc
        }
    }

    assert_eq!(
        parse_top(&form_pat!((extend_nt [], "b", static_synex)), tokens_s!("BB")),
        Ok(ast_shape!(() "BB"))
    );

    let orig = assoc_n!(
        "o" => Rc::new(form_pat!(
            (star (named "c",
                (alt (lit_aat "O"), [(lit_aat "Extend"),
                                     (extend_nt [], "a", static_synex), (lit_aat "#")]))))));

    assert_eq!(
        parse_in_syn_env(
            &form_pat!((call "o")),
            orig.clone(),
            tokens_s!("O" "O" "Extend" "AA" "AA" "Back" "O" "#" "AA" "#" "O")
        )
        .unwrap(),
        ast!({- "c" => ["O", "O", ("Extend" (() {- "c" => ["AA", "AA", ("Back" {- "c" => ["O"]} "#"), "AA"]}) "#"), "O"]})
    );

    assert_eq!(
        parse_in_syn_env(
            &form_pat!((call "o")),
            orig.clone(),
            tokens_s!("O" "O" "Extend" "AA" "AA" "Back" "AA" "#" "AA" "#" "O")
        )
        .is_err(),
        true
    );

    assert_eq!(
        parse_in_syn_env(
            &form_pat!((call "o")),
            orig.clone(),
            tokens_s!("O" "O" "Extend" "O" "#" "O")
        )
        .is_err(),
        true
    );

    fn counter_synex(_: ParseContext, a: Ast) -> ParseContext {
        let count = match a.c() {
            IncompleteNode(mbe) => mbe,
            _ => panic!(),
        }
        .get_rep_leaf_or_panic(n("n"))
        .len();

        ParseContext::new_from_grammar(
            assoc_n!("count" => Rc::new(Literal(Rc::new(new_scan(r"\s*(\S+)", None)),
                                            n(&count.to_string())))),
        )
    }

    assert_m!(
        parse_top(
            &form_pat!((extend_nt (star (named "n", (lit_aat "X"))), "count", counter_synex)),
            tokens_s!("X" "X" "X" "4")
        ),
        Err(_)
    );

    assert_eq!(
        parse_top(
            &form_pat!((extend_nt (star (named "n", (lit_aat "X"))), "count", counter_synex)),
            tokens_s!("X" "X" "X" "X" "4")
        ),
        Ok(ast_shape!({- "n" => ["X", "X", "X", "X"]} "4"))
    );

    assert_m!(
        parse_top(
            &form_pat!((extend_nt (star (named "n", (lit_aat "X"))), "count", counter_synex)),
            tokens_s!("X" "X" "X" "X" "X" "4")
        ),
        Err(_)
    );
}

// #[test]
// fn test_syn_env_parsing() as{
// let mut se = Assoc::new();
// se = se.set(n("xes"), Box::new(Form { grammar: form_pat!((star (lit_aat "X")),
// relative_phase)}))
// }
