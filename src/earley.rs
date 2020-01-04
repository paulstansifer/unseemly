#![allow(non_upper_case_globals)]

// An Earley parser!
// Partly based on advice from http://loup-vaillant.fr/tutorials/earley-parsing/.
// Partly based on https://arxiv.org/abs/1102.2003
//  (though I'll save you the trouble of reading that one:
//    it can be summed up as "Just add the current grammar to the Earley rules,
//                             and everything will work out fine.")
// Why Earley?
//  * Earley parses arbitrary CFLs, which are
//    - a category of languages I can comprehend,
//    - and closed under composition (though ambiguity can creep in)
//  * Earley has a pretty good error message story (TODO: check that this is true)
//  * Earley maxes out at O(n^3) time†, and for practical grammars tends to be linear
//       †technically, the reflective bit makes parsing NP-complete, but No One Will Do That.
//
// Also, it turns out that implementing an Earley parser goes pretty smoothly. Yay!

use crate::{
    ast::Ast,
    ast_walk::LazyWalkReses,
    grammar::{
        FormPat::{self, *},
        SynEnv,
    },
    name::*,
    util::{assoc::Assoc, mbe::EnvMBE},
};
use std::{cell::RefCell, collections::HashMap, rc::Rc};

// TODO: This UniqueId stuff is great, but we could make things faster
//  by storing array indices instead

thread_local! {
    static next_id: RefCell<u32> = RefCell::new(0);

    // TODO: instead of indexing by unique cell, we should intern `ParseContext`s
    //  for fast (and not just pointer-based) comparison.
    static all_parse_contexts: RefCell<HashMap<UniqueIdRef, ParseContext>>
        = RefCell::new(HashMap::new());

    // For parse error reporting: how far have we gotten?
    static best_token: RefCell<(usize, Rc<FormPat>, usize)>
        = RefCell::new((0, Rc::new(Impossible), 0));
}

fn get_next_id() -> UniqueId {
    next_id.with(|id| {
        let res = UniqueId(*id.borrow());
        *id.borrow_mut() += 1;
        res
    })
}

// Specifically *not* `Clone` or `Copy`
#[derive(PartialEq, Eq)]
pub struct UniqueId(u32);

impl std::fmt::Debug for UniqueId {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result { write!(f, "{}", self.0) }
}

#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub struct UniqueIdRef(u32);

impl UniqueId {
    fn get_ref(&self) -> UniqueIdRef { UniqueIdRef(self.0) }

    fn is(&self, other: UniqueIdRef) -> bool { self.0 == other.0 }
}

impl std::fmt::Debug for UniqueIdRef {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result { write!(f, "{}", self.0) }
}

// TODO: eliminate this; just use `ParseContext` everwhere
pub type CodeEnvs = (LazyWalkReses<crate::ty::SynthTy>, LazyWalkReses<crate::runtime::eval::Eval>);

pub fn empty__code_envs() -> CodeEnvs {
    (
        LazyWalkReses::<crate::ty::SynthTy>::new_empty(),
        LazyWalkReses::<crate::runtime::eval::Eval>::new_empty(),
    )
}

// TODO: We should probably refactor to use `ParseContext`
//  everywhere we currently use these two things together (particularly `earley.rs`).
custom_derive! {
    #[derive(Clone, Reifiable)]
    pub struct ParseContext {
        pub grammar: SynEnv,
        pub type_ctxt: LazyWalkReses<crate::ty::SynthTy>,
        pub eval_ctxt: LazyWalkReses<crate::runtime::eval::Eval>
    }
}

impl ParseContext {
    pub fn new(se: SynEnv, ce: CodeEnvs) -> ParseContext {
        ParseContext { grammar: se, type_ctxt: ce.0, eval_ctxt: ce.1 }
    }
    pub fn new_from_grammar(se: SynEnv) -> ParseContext {
        ParseContext {
            grammar: se,
            type_ctxt: LazyWalkReses::<crate::ty::SynthTy>::new_empty(),
            eval_ctxt: LazyWalkReses::<crate::runtime::eval::Eval>::new_empty(),
        }
    }
    pub fn with_grammar(self, se: SynEnv) -> ParseContext { ParseContext { grammar: se, ..self } }
}

// Hey, this doesn't need to be Reifiable!
pub struct Item {
    /// Where (in the token input stream) this rule tried to start matching
    start_idx: usize,
    /// What are we trying to match?
    rule: Rc<FormPat>,
    /// The location of the • in the rule. Most rules are very short
    pos: usize,
    /// The current grammar, so we can interperate `Call` rules
    grammar: SynEnv,

    /// Environments, for typing/evaluating syntax extensions
    envs: Rc<CodeEnvs>,

    // -- Just for error messages --
    /// This rule is too commonplace to be informative in a parse error
    common: bool,

    // -- Everything after this line is nonstandard, and is just here as an optimization--
    /// Identity for the purposes of `wanted_by` and `local_parse`
    id: UniqueId,

    /// Can this complete things that have asked for it?
    /// This is mostly a convenience.
    done: RefCell<bool>, // Can this complete things that have asked for it?

    /// For simple (leaf) nodes, we just store the resulting parse right away.
    /// This is a convenience so that extracting the parse tree
    ///  doesn't require trawling through the token input
    /// For non-leaf nodes, store the ID of the item that provides justification
    local_parse: RefCell<LocalParse>,

    /// Traditionally, when a rule is completed in Earley parsing,
    ///  one looks to try to find all the rules that could have asked for it.
    /// That's expensive! But keeping back-pointers instead has a timing problem:
    ///  we might create a new item with an advanced • (possibly one token ahead)
    ///   before we know everything that called for the original item.
    /// Therefore, we make sure that all items that start in the same place
    ///   with the same rule/grammar
    ///  share the same set of origins via `RefCell`.
    ///
    /// This, uh, might be an excessively cocky design.
    /// But searching item lists is *hard* when your Earley parser
    ///  has so many different kinds of rules!
    wanted_by: Rc<RefCell<Vec<UniqueIdRef>>>,
}

/// Information for parsing. It's not a parse tree, but it tells you the next step to get one.
/// (Hence "local")
#[derive(PartialEq, Debug, Clone)]
enum LocalParse {
    /// ⊤; no information yet
    NothingYet,
    JustifiedByItemPlanB(UniqueIdRef), // Looking for a better parse, though... (for `Biased`)
    JustifiedByItem(UniqueIdRef),
    ParsedAtom(Ast),
    /// ⊥; contradiction (TMI!)
    Ambiguous(Box<LocalParse>, Box<LocalParse>),
}
use self::LocalParse::*;

impl PartialOrd for LocalParse {
    /// Establish a lattice for `LocalParse`; some parses are better than others.
    /// `Biased` allows one to find a "Plan B" parse that gets overwritten by "Plan A".
    /// But there's also `NothingYet`, for ... (TODO: only leaves and just-started nodes?)
    /// ... and `Ambiguous`, when we know that there are multiple justifications for a single node
    fn partial_cmp(&self, other: &LocalParse) -> Option<std::cmp::Ordering> {
        use std::cmp::Ordering::*;
        if self == other {
            return Some(Equal);
        }
        match (self, other) {
            (&NothingYet, _) | (_, &Ambiguous(_, _)) => Some(Less),
            (&Ambiguous(_, _), _) | (_, &NothingYet) => Some(Greater),
            (&JustifiedByItemPlanB(_), &JustifiedByItem(_)) => Some(Less),
            (&JustifiedByItem(_), &JustifiedByItemPlanB(_)) => Some(Greater),
            (&JustifiedByItem(_), &JustifiedByItem(_)) => None,
            // semantically, this ought to be `None`, but that would be a hard-to-debug logic error
            _ => icp!("Attempted to compare {:#?} and {:#?}", self, other),
        }
    }
}

impl Clone for Item {
    fn clone(&self) -> Item {
        Item {
            start_idx: self.start_idx,
            rule: self.rule.clone(),
            pos: self.pos,
            grammar: self.grammar.clone(),
            envs: self.envs.clone(),
            common: self.common,
            id: get_next_id(),
            done: self.done.clone(),
            local_parse: RefCell::new(LocalParse::NothingYet),
            wanted_by: self.wanted_by.clone(),
        }
    }
}

/// Progress through the state sets
// TODO: this ought to produce an Option<ParseError>, not a bool!
fn create_chart(
    rule: Rc<FormPat>,
    grammar: SynEnv,
    envs: CodeEnvs,
    toks: &str,
) -> (UniqueId, Vec<Vec<Item>>)
{
    let toks = toks.trim(); // HACK: tokens don't consume trailing whitespace
    let mut chart: Vec<Vec<Item>> = vec![];
    chart.resize_with(toks.len() + 1, std::default::Default::default);

    let start_but_startier = get_next_id();

    let start_item = Item {
        start_idx: 0,
        rule: rule,
        pos: 0,
        grammar: grammar,
        envs: Rc::new(envs),
        common: false,
        id: get_next_id(),
        done: RefCell::new(false),
        local_parse: RefCell::new(LocalParse::NothingYet),
        wanted_by: Rc::new(RefCell::new(vec![start_but_startier.get_ref()])),
    };

    chart[0].push(start_item);

    for cur_tok in 0..toks.len() {
        walk_tt(&mut chart, &toks, cur_tok)
    }

    examine_state_set(&mut chart, &toks, toks.len()); // One last time, for nullable rules at the end

    (start_but_startier, chart)
}

/// Recognize `rule` in `grammar` (but assume no code will need to be executed)
fn recognize(rule: &FormPat, grammar: &SynEnv, toks: &str) -> bool {
    let (start_but_startier, chart) =
        create_chart(Rc::new(rule.clone()), grammar.clone(), empty__code_envs(), toks);

    chart[chart.len() - 1].iter().any(|item| {
        (*item.wanted_by.borrow()).iter().any(|idr| start_but_startier.is(*idr))
            && *item.done.borrow()
    })
}

fn walk_tt(chart: &mut Vec<Vec<Item>>, toks: &str, cur_tok: usize) {
    examine_state_set(chart, toks, cur_tok);
    // log!("\n  {:#?}\n->{:#?}\n", chart[*cur_tok], chart[*cur_tok + 1]);
}

/// Progresses a state set until it won't go any further.
/// Returns the state set for the next token.
fn examine_state_set(chart: &mut Vec<Vec<Item>>, toks: &str, cur_tok: usize) {
    // If nullable items are statically identified, I think there's an optimization
    //  where we don't re-walk old items
    while new_items_from_state_set(chart, toks, cur_tok) {} // Until a fixpoint is reached
}

fn new_items_from_state_set(chart: &mut Vec<Vec<Item>>, toks: &str, cur_tok: usize) -> bool {
    let mut effect = false;
    for idx in 0..chart[cur_tok].len() {
        for (new_item, adv) in chart[cur_tok][idx].examine(toks, cur_tok, chart) {
            effect = merge_into_state_set(new_item, &mut chart[cur_tok + adv]) || effect;
        }
    }
    effect
}

// Returns whether anything happened
fn merge_into_state_set(item: Item, items: &mut Vec<Item>) -> bool {
    for i in items.iter() {
        if i.similar(&item) {
            if i.as_good_as(&item) {
                return false; // no new information
            }
            log!("improved item: {:#?} vs. {:#?}\n", item, i);
            i.merge(&item);
            return true;
        }
    }
    log!("new item: {:#?}\n", item);
    items.push(item);

    true
}

impl std::fmt::Debug for Item {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "[({:#?}){}({:#?}.{}){}<{:#?} - {:#?}>]",
            self.id,
            self.start_idx,
            self.rule,
            self.pos,
            if *self.done.borrow() { "✓" } else { "…" },
            self.local_parse.borrow(),
            self.wanted_by.borrow()
        )
    }
}

impl Item {
    /// This is pointer equality on `rule` and `grammar` for speed.
    /// Also, it intentionally ignores `done`, `local_parse`, and `wanted_by`,
    ///  because those should be merged.
    fn similar<'f>(&'f self, other: &'f Item) -> bool {
        self.start_idx == other.start_idx
            && &*self.rule as *const FormPat == &*other.rule as *const FormPat
            && self.pos == other.pos
            && self.grammar.almost_ptr_eq(&other.grammar)
    }

    /// `false` if `other` might provide new information
    /// `true` if `other` definitely provides no new information
    /// (this is conservative regarding `wanted_by`)
    fn as_good_as<'f>(&'f self, other: &'f Item) -> bool {
        assert!(self.similar(other));
        (*self.done.borrow() == *other.done.borrow() || !*other.done.borrow()) // no more done?
        && (*other.local_parse.borrow() <= *self.local_parse.borrow() ) // no "better" parse?
        && (other.wanted_by.borrow().len() == 0 // no more wanted?
            || (other.wanted_by.borrow().iter().all(
                   |w| self.wanted_by.borrow().iter().any(|s_w| w == s_w))))
    }

    fn merge(&self, other: &Item) {
        if *other.done.borrow() {
            *self.done.borrow_mut() = true;
        }

        use std::cmp::Ordering::*;
        let comparison = other.local_parse.borrow().partial_cmp(&*self.local_parse.borrow());
        log!(
            "\n(For {}) Merging {:#?} and {:#?}... ",
            self.id.0,
            *other.local_parse.borrow(),
            *self.local_parse.borrow()
        );
        match comparison {
            Some(Greater) => {
                *self.local_parse.borrow_mut() = other.local_parse.borrow().clone();
            }
            Some(Equal) | Some(Less) => { /* no new information */ }
            None => {
                let amb = LocalParse::Ambiguous(
                    Box::new(self.local_parse.borrow().clone()),
                    Box::new(other.local_parse.borrow().clone()),
                );
                *self.local_parse.borrow_mut() = amb;
            }
        }
        log!("... into {:#?}\n", *self.local_parse.borrow());

        for other_wanted in other.wanted_by.borrow().iter() {
            let mut has = false;
            for self_wanted in self.wanted_by.borrow().iter() {
                if self_wanted == other_wanted {
                    has = true;
                    break;
                }
            }

            if !has {
                self.wanted_by.borrow_mut().push(*other_wanted)
            }
        }
    }

    // -----------------------------------------------------------
    // These methods all make a (singleton) set of items after progressing `self` somehow
    // TODO: I have a lot of "like <one of these>, but" comments around this file...
    //

    fn finish_with(&self, lp: LocalParse, toks_consumed: usize) -> Vec<(Item, usize)> {
        log!("[fin_w/ ({})]", self.id.0);
        vec![(
            Item {
                done: RefCell::new(true),
                local_parse: RefCell::new(lp),
                pos: self.pos + 1,
                ..self.clone()
            },
            toks_consumed,
        )]
    }

    fn start(&self, rule: &Rc<FormPat>, cur_idx: usize) -> Vec<(Item, usize)> {
        log!("[start ({})]", self.id.0);
        vec![(
            Item {
                start_idx: cur_idx,
                rule: rule.clone(),
                pos: 0,
                done: RefCell::new(false),
                grammar: self.grammar.clone(),
                envs: self.envs.clone(),
                common: self.common,
                local_parse: RefCell::new(LocalParse::NothingYet),
                id: get_next_id(),
                wanted_by: Rc::new(RefCell::new(vec![self.id.get_ref()])),
            },
            0,
        )]
    }

    // -----------------------------------------------------------

    /// See what new items this item justifies
    fn examine(&self, toks: &str, cur_idx: usize, chart: &[Vec<Item>]) -> Vec<(Item, usize)> {
        let mut res = if *self.done.borrow() {
            let mut waiting_satisfied = vec![];

            log!("({:#?}) done; {} items want it\n", self, (*self.wanted_by.borrow()).len());

            for &waiting_item_id in self.wanted_by.borrow().iter() {
                if let Some(waiting_item) =
                    chart[self.start_idx].iter().find(|i| i.id.is(waiting_item_id))
                {
                    // It's `None` if it's the startier item

                    let me_justif = JustifiedByItem(self.id.get_ref());

                    // We `finish_with` here for things that are waiting on other items,
                    //  in `shift_or_predict` for leaves.
                    // Except for `Seq`. TODO: why?
                    let mut more = match *waiting_item.rule {
                        Anyways(_) | Impossible | Scan(_) => {
                            icp!("{:#?} should not be waiting for anything!", waiting_item)
                        }
                        Seq(ref subs) => {
                            if (waiting_item.pos) as usize == subs.len() {
                                vec![]
                            } else {
                                // Like `waiting_item.advance`, but with a local_parse
                                vec![(
                                    Item {
                                        pos: waiting_item.pos + 1,
                                        local_parse: RefCell::new(me_justif),
                                        ..waiting_item.clone()
                                    },
                                    0,
                                )]
                            }
                        }
                        Plus(_) | Star(_) => {
                            // It'll also keep going, though!
                            waiting_item.finish_with(me_justif, 0)
                        }
                        SynImport(_, _, _) if waiting_item.pos == 0 => vec![(
                            Item {
                                pos: 1,
                                local_parse: RefCell::new(me_justif),
                                ..waiting_item.clone()
                            },
                            0,
                        )],
                        VarRef(_)
                        | Alt(_)
                        | Call(_)
                        | Scope(_, _)
                        | Pick(_, _)
                        | Named(_, _)
                        | SynImport(_, _, _)
                        | NameImport(_, _)
                        | QuoteDeepen(_, _)
                        | QuoteEscape(_, _)
                        | Common(_) => waiting_item.finish_with(me_justif, 0),
                        // Using `c_parse` instead of `local_parse` here is weird,
                        //  but probably necessary to allow `Call` under `Reserved`.
                        Reserved(_, ref name_list) => match self.c_parse(chart, cur_idx) {
                            Ok(Ast::Atom(name)) | Ok(Ast::VariableReference(name)) => {
                                if name_list.contains(&name) {
                                    vec![]
                                } else {
                                    waiting_item.finish_with(me_justif, 0)
                                }
                            }
                            _ => {
                                log!("found something unusual {:?}", other);
                                vec![]
                            }
                        },
                        Literal(_, expected) => match self.c_parse(chart, cur_idx) {
                            Ok(Ast::Atom(name)) => {
                                if name == expected {
                                    waiting_item.finish_with(me_justif, 0)
                                } else {
                                    vec![]
                                }
                            }
                            _ => {
                                log!("found something unusual {:?}", other);
                                vec![]
                            }
                        },
                        Biased(ref _plan_a, ref plan_b) => {
                            if &*self.rule as *const FormPat == &**plan_b as *const FormPat {
                                waiting_item.finish_with(JustifiedByItemPlanB(self.id.get_ref()), 0)
                            } else {
                                waiting_item.finish_with(me_justif, 0)
                            }
                        }
                    };

                    waiting_satisfied.append(&mut more);
                }
            }
            waiting_satisfied
        } else {
            vec![]
        };

        if !res.is_empty() {
            if let Call(_) = *res[0].0.rule {
                // HACK: I think that `Call` is uninformative
            } else if !self.common {
                best_token
                    .with(|bt| *bt.borrow_mut() = (cur_idx, res[0].0.rule.clone(), res[0].0.pos));
            }
        }

        res.append(&mut self.shift_or_predict(toks, cur_idx, chart));

        res
    }

    fn shift_or_predict(
        &self,
        toks: &str,
        cur_idx: usize,
        chart: &[Vec<Item>],
    ) -> Vec<(Item, usize)>
    {
        // Try to shift (bump `pos`, or set `done`) or predict (`start` a new item)
        match (self.pos, &*(self.rule.clone())) {
            // TODO: is there a better way to match in `Rc`?
            (0, &Anyways(ref a)) => self.finish_with(ParsedAtom(a.clone()), 0),
            (_, &Impossible) => vec![],
            (0, &Literal(ref sub, _)) => self.start(sub, cur_idx),
            (0, &Scan(crate::grammar::Scanner(ref regex))) => {
                let mut caps = regex.capture_locations();
                if regex.captures_read(&mut caps, &toks[cur_idx..]).is_some() {
                    match caps.get(1) {
                        Some((start, end)) => {
                            // These are byte indices!
                            self.finish_with(
                                ParsedAtom(Ast::Atom(n(&toks[cur_idx + start..cur_idx + end]))),
                                end,
                            )
                        }
                        None => self.finish_with(NothingYet, caps.get(0).unwrap().1),
                    }
                } else {
                    vec![]
                }
            }
            (0, &VarRef(ref sub)) => self.start(sub, cur_idx),
            (pos, &Seq(ref subs)) => {
                if pos < subs.len() {
                    self.start(&subs[pos as usize], cur_idx)
                } else if pos == subs.len() {
                    // a little like `.finish`, but without advancing
                    vec![(Item { done: RefCell::new(true), ..self.clone() }, 0)]
                } else {
                    vec![]
                }
            }
            (_, &Star(ref sub)) => {
                // Special case: the elegant thing would be to create `Star` pre-`done`
                let mut res = if self.pos == 0 {
                    // Like `.finish`, but without advancing
                    vec![(Item { done: RefCell::new(true), ..self.clone() }, 0)]
                } else {
                    vec![]
                };
                res.append(&mut self.start(&sub, cur_idx)); // But we can take more!
                res
            }
            (_, &Plus(ref sub)) => self.start(&sub, cur_idx),
            (0, &Alt(ref subs)) => {
                let mut res = vec![];
                for sub in subs {
                    res.append(&mut self.start(&(*sub), cur_idx));
                }
                res
            }
            // Needs special handling elsewhere!
            (0, &Biased(ref plan_a, ref plan_b)) => {
                let mut res = self.start(&plan_a, cur_idx);
                res.append(&mut self.start(&plan_b, cur_idx));
                res
            }
            (0, &Call(n)) => self.start(&self.grammar.find_or_panic(&n), cur_idx),
            (0, &Scope(ref f, _)) => {
                // form.grammar is a FormPat. Confusing!
                self.start(&f.grammar, cur_idx)
            }
            (0, &Pick(ref body, _)) => self.start(&body, cur_idx),
            (0, &SynImport(ref lhs, _, _)) => self.start(&lhs, cur_idx),
            (1, &SynImport(_, ref body, ref f)) => {
                // TODO: handle errors properly! Probably need to memoize, also!
                let partial_parse = match *self.local_parse.borrow() {
                    NothingYet | Ambiguous(_, _) => return vec![],
                    ParsedAtom(ref a) => a.clone(),
                    JustifiedByItem(_) | JustifiedByItemPlanB(_) => {
                        match self.find_wanted(chart, cur_idx).c_parse(chart, cur_idx) {
                            Ok(ast) => ast,
                            Err(_) => {
                                return vec![];
                            }
                        }
                    }
                };

                let new_ctxt = all_parse_contexts.with(|grammars| {
                    let mut mut_grammars = grammars.borrow_mut();
                    mut_grammars
                        .entry(self.id.get_ref()) // memoize
                        .or_insert_with(||
                            f.0(ParseContext::new(
                                self.grammar.clone(), (*self.envs).clone()), partial_parse))
                        .clone()
                });

                vec![(
                    Item {
                        start_idx: cur_idx,
                        rule: body.clone(),
                        pos: 0,
                        done: RefCell::new(false),
                        grammar: new_ctxt.grammar.clone(),
                        envs: Rc::new((new_ctxt.type_ctxt.clone(), new_ctxt.eval_ctxt.clone())),
                        common: false,
                        local_parse: RefCell::new(LocalParse::NothingYet),
                        id: get_next_id(),
                        wanted_by: Rc::new(RefCell::new(vec![self.id.get_ref()])),
                    },
                    0,
                )]
            }
            (0, &Named(_, ref body))
            | (0, &NameImport(ref body, _))
            | (0, &QuoteDeepen(ref body, _))
            | (0, &QuoteEscape(ref body, _))
            | (0, &Reserved(ref body, _)) => self.start(&body, cur_idx),
            (0, &Common(ref body)) => {
                let mut res = self.start(&body, cur_idx);
                res[0].0.common = true; // Only has one element
                res
            }
            // Rust rightly complains that this is unreachable; yay!
            // But how do I avoid a catch-all pattern for the pos > 0 case?
            //(0, _) =>  { icp!("unhandled FormPat") },
            _ => vec![], // end of a rule
        }
    }

    fn find_wanted<'f, 'c>(&'f self, chart: &'c [Vec<Item>], done_tok: usize) -> &'c Item {
        let mut first_found: Option<&Item> = None;
        let local_parse = self.local_parse.borrow().clone();
        let desired_id = match local_parse {
            JustifiedByItem(id) | JustifiedByItemPlanB(id) => id,
            Ambiguous(ref l, ref r) => {
                // HACK: this is quite ugly!
                let l = *l.clone();
                let r = *r.clone();
                log!("===Ambiguity===\n");
                // Show both parses...
                *self.local_parse.borrow_mut() = l;
                let l_res = self.c_parse(chart, done_tok);
                *self.local_parse.borrow_mut() = r;
                let r_res = self.c_parse(chart, done_tok);

                panic!("Ambiguity! \n{:#?}\n{:#?}\n", l_res, r_res)
            }
            _ => icp!("tried to parse unjustified item: {:#?} ", self),
        };
        log!("We are {:#?} at {}...\n", self, done_tok);

        for idx in 0..chart[done_tok].len() {
            let i = &chart[done_tok][idx];

            if i.id.is(desired_id) {
                match first_found {
                    None => {
                        first_found = Some(i);
                    }
                    Some(_) => icp!("unacknowledged ambiguity!"),
                }
            }
        }

        first_found.expect("ICP: no parse after successful recognition")
    }

    /// After the chart is built, we parse...
    fn c_parse(&self, chart: &[Vec<Item>], done_tok: usize) -> ParseResult {
        log!("Tring to parse {:#?}...\n", self);
        // assert!(*self.done.borrow()); // false during ambiguity reporting
        let res = match *self.rule {
            Anyways(ref a) => Ok(a.clone()),
            Impossible => icp!("Parser parsed the impossible!"),
            Scan(_) => match self.local_parse.borrow().clone() {
                ParsedAtom(a) => Ok(a),
                NothingYet => Ok(Ast::Trivial),
                _ => icp!(),
            },
            VarRef(_) => match self.find_wanted(chart, done_tok).c_parse(chart, done_tok)? {
                Ast::Atom(a) => Ok(Ast::VariableReference(a)),
                _ => icp!("no atom saved"),
            },
            Literal(_, _) | Alt(_) | Biased(_, _) | Call(_) | Reserved(_, _) | Common(_) => {
                self.find_wanted(chart, done_tok).c_parse(chart, done_tok)
            }
            Seq(_) | Star(_) | Plus(_) | SynImport(_, _, _) => {
                let mut step = self;
                let mut subtrees: Vec<Ast> = vec![];
                let mut pos = done_tok;
                // Walk over "previous incarnations" of `self`
                // TODO: It seems like I often have had the thought
                //  "Why not put a nullable pattern under `Star`? What could go wrong?"
                // Do something about that...
                loop {
                    log!("Trying to take a step...\n");

                    // Special case: we can't start the loop because there are 0 children
                    if let NothingYet = step.local_parse.borrow().clone() {
                        break;
                    }

                    let sub = step.find_wanted(chart, pos);
                    subtrees.push(sub.c_parse(chart, pos)?);
                    if sub.start_idx == self.start_idx && step.pos == 1 {
                        break;
                    } else {
                        pos = sub.start_idx;
                        let mut found = false;
                        for idx in 0..chart[pos].len() {
                            let i = &chart[pos][idx];
                            log!("Checking {:#?}\n", i);
                            if self.grammar.almost_ptr_eq(&i.grammar)
                                && &*self.rule as *const FormPat == &*i.rule as *const FormPat
                                && step.pos - 1 == i.pos
                            {
                                step = i;
                                found = true;
                                break;
                            }
                        }
                        if !found {
                            icp!("Can't find item previous to {:#?}", step)
                        }
                    }
                }
                subtrees.reverse();

                match *self.rule {
                    Seq(_) | SynImport(_, _, _) => Ok(Ast::Shape(subtrees)),
                    Star(_) | Plus(_) => Ok(Ast::IncompleteNode(EnvMBE::new_from_anon_repeat(
                        subtrees.into_iter().map(|a| a.flatten()).collect(),
                    ))),
                    _ => icp!("seriously, this can't happen"),
                }
            }
            Named(name, _) => {
                let sub_parsed = self.find_wanted(chart, done_tok).c_parse(chart, done_tok)?;
                Ok(Ast::IncompleteNode(EnvMBE::new_from_leaves(Assoc::single(name, sub_parsed))))
            }
            Scope(ref form, ref export) => {
                let sub_parsed = self.find_wanted(chart, done_tok).c_parse(chart, done_tok)?;
                // TODO #14: We should add zero-length repeats of missing `Named`s,
                Ok(Ast::Node(form.clone(), sub_parsed.flatten(), export.clone()))
            }
            Pick(_, name) => {
                let sub_parsed = self.find_wanted(chart, done_tok).c_parse(chart, done_tok)?;
                sub_parsed
                    .flatten()
                    .get_leaf(name)
                    .ok_or_else(|| ParseError {
                        msg: format!("Nothing named {} in {:?}", name, sub_parsed),
                    })
                    .map(std::clone::Clone::clone)
            }
            NameImport(_, ref beta) => {
                let sub_parsed = self.find_wanted(chart, done_tok).c_parse(chart, done_tok)?;
                Ok(Ast::ExtendEnv(Box::new(sub_parsed), beta.clone()))
            }
            QuoteDeepen(_, pos) => {
                let sub_parsed = self.find_wanted(chart, done_tok).c_parse(chart, done_tok)?;
                Ok(Ast::QuoteMore(Box::new(sub_parsed), pos))
            }
            QuoteEscape(_, depth) => {
                let sub_parsed = self.find_wanted(chart, done_tok).c_parse(chart, done_tok)?;
                Ok(Ast::QuoteLess(Box::new(sub_parsed), depth))
            }
        };
        log!(">>>{:#?}<<<\n", res);

        res
    }
}

type ParseResult = Result<Ast, ParseError>;

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct ParseError {
    pub msg: String,
}

pub fn parse(rule: &FormPat, grammar: &SynEnv, envs: CodeEnvs, toks: &str) -> ParseResult {
    best_token.with(|bt| *bt.borrow_mut() = (0, Rc::new(rule.clone()), 0));

    let (start_but_startier, chart) =
        create_chart(Rc::new(rule.clone()), grammar.clone(), envs, toks);
    let final_item = chart[chart.len() - 1].iter().find(|item| {
        (*item.wanted_by.borrow()).iter().any(|idr| start_but_startier.is(*idr))
            && *item.done.borrow()
    });
    log!("-------\n");
    match final_item {
        Some(i) => i.c_parse(&chart, chart.len() - 1),
        None => best_token.with(|bt| {
            let (idx, ref grammar, pos) = *bt.borrow();

            let line_begin = toks[0..idx].rfind('\n').map(|n| n + 1).unwrap_or(0);
            let line_end = toks[idx..toks.len()].find('\n').map(|n| n + idx).unwrap_or(toks.len());
            let line_number = toks[0..idx].matches('\n').count() + 1;

            Err(ParseError {
                msg: format!(
                    "Could not parse past “{}•{}” (on line {}) \nin rule {:?} at {}",
                    &toks[line_begin..idx],
                    &toks[idx..line_end],
                    line_number,
                    grammar,
                    pos
                ),
            })
        }),
    }
}

fn parse_top(rule: &FormPat, toks: &str) -> ParseResult {
    parse(rule, &Assoc::new(), empty__code_envs(), toks)
}

#[test]
fn earley_merging() {
    let one_rule = crate::grammar::new_scan("whatever");
    let another_rule = Impossible;
    let main_grammar = assoc_n!("a" => Rc::new(form_pat!((scan "irrelevant"))));
    let another_grammar = assoc_n!("a" => Rc::new(form_pat!((scan "irrelevant"))));
    let mut state_set = vec![];

    let basic_item = Item {
        start_idx: 0,
        rule: Rc::new(one_rule),
        pos: 0,
        grammar: main_grammar.clone(),
        envs: Rc::new((LazyWalkReses::new_empty(), LazyWalkReses::new_empty())),
        common: false,
        id: get_next_id(),
        done: RefCell::new(false),
        local_parse: RefCell::new(LocalParse::NothingYet),
        wanted_by: Rc::new(RefCell::new(vec![])),
    };

    assert_eq!(merge_into_state_set(basic_item.clone(), &mut state_set), true);
    assert_eq!(state_set.len(), 1);

    // exactly the same (except a different ID)
    assert_eq!(merge_into_state_set(basic_item.clone(), &mut state_set), false);
    assert_eq!(state_set.len(), 1);

    // (not done yet)
    assert_eq!(*state_set[0].done.borrow(), false);

    // improvement in doneness, mergable
    assert_eq!(
        merge_into_state_set(
            Item { done: RefCell::new(true), ..basic_item.clone() },
            &mut state_set
        ),
        true
    );
    assert_eq!(state_set.len(), 1);
    // now done!
    assert_eq!(*state_set[0].done.borrow(), true);

    // not an improvement this time!
    assert_eq!(
        merge_into_state_set(
            Item { done: RefCell::new(true), ..basic_item.clone() },
            &mut state_set
        ),
        false
    );
    assert_eq!(state_set.len(), 1);

    // not as good as
    assert_eq!(
        merge_into_state_set(
            Item { done: RefCell::new(false), ..basic_item.clone() },
            &mut state_set
        ),
        false
    );
    assert_eq!(state_set.len(), 1);
    // still done!
    assert_eq!(*state_set[0].done.borrow(), true);

    // different rule
    assert_eq!(
        merge_into_state_set(
            Item { rule: Rc::new(another_rule), ..basic_item.clone() },
            &mut state_set
        ),
        true
    );
    assert_eq!(state_set.len(), 2);

    // different grammar (pointer-wise!)
    assert_eq!(
        merge_into_state_set(
            Item { grammar: another_grammar.clone(), ..basic_item.clone() },
            &mut state_set
        ),
        true
    );
    assert_eq!(state_set.len(), 3);

    let id1 = get_next_id().get_ref();
    let id2 = get_next_id().get_ref();
    let id3 = get_next_id().get_ref();
    // log!("AGA {:#?},{:#?},{:#?},{:#?}\n",
    // (*self.done.borrow() == *other.done.borrow() || !*other.done.borrow())
    // , *self.local_parse.borrow() == *other.local_parse.borrow()
    // , *(other.local_parse).borrow() == LocalParse::NothingYet
    // , (other.wanted_by.borrow().len() == 0
    // || (other.wanted_by.borrow().iter().all(
    // |w| self.wanted_by.borrow().iter().find(|s_w| w == *s_w).is_some())))
    //
    // );
    // log!("  {:#?}=?{:#?}\n", *self.local_parse.borrow(), *other.local_parse.borrow());
    let wanted_item = |ids| Item { wanted_by: Rc::new(RefCell::new(ids)), ..basic_item.clone() };

    // test self-check (this shouldn't be interesting)
    assert_eq!(merge_into_state_set(wanted_item(vec![]), &mut state_set), false);
    assert_eq!(state_set.len(), 3);

    assert_eq!(merge_into_state_set(wanted_item(vec![id1]), &mut state_set), true);
    assert_eq!(state_set.len(), 3);

    // but another one doesn't have any effect
    assert_eq!(merge_into_state_set(wanted_item(vec![id1]), &mut state_set), false);
    assert_eq!(state_set.len(), 3);

    assert_eq!(merge_into_state_set(wanted_item(vec![id2]), &mut state_set), true);
    assert_eq!(state_set.len(), 3);

    assert_eq!(merge_into_state_set(wanted_item(vec![id1, id2]), &mut state_set), false);
    assert_eq!(state_set.len(), 3);

    assert_eq!(merge_into_state_set(wanted_item(vec![id2, id1]), &mut state_set), false);
    assert_eq!(state_set.len(), 3);

    assert_eq!(merge_into_state_set(wanted_item(vec![id2, id3]), &mut state_set), true);
    assert_eq!(state_set.len(), 3);

    // TODO: we ought to test the NothingYet - JustifiedByItem() / ParsedAtom() - Ambiguous lattice
}

#[test]
fn earley_simple_recognition() {
    let main_grammar = Assoc::new();

    let atom = Rc::new(crate::grammar::new_scan(r"\s*(\S+)"));

    // 0-length strings

    assert_eq!(recognize(&*atom, &main_grammar, tokens_s!()), false);

    assert_eq!(recognize(&Anyways(Ast::Trivial), &main_grammar, tokens_s!()), true);

    assert_eq!(recognize(&Seq(vec![]), &main_grammar, tokens_s!()), true);

    assert_eq!(recognize(&Seq(vec![atom.clone()]), &main_grammar, tokens_s!()), false);

    assert_eq!(recognize(&Star(Rc::new(Impossible)), &main_grammar, tokens_s!()), true);

    assert_eq!(recognize(&Star(atom.clone()), &main_grammar, tokens_s!()), true);

    // 1-length strings

    assert_eq!(recognize(&*atom, &main_grammar, tokens_s!("Pierre_Menard")), true);

    assert_eq!(recognize(&Impossible, &main_grammar, tokens_s!("Pierre_Menard")), false);

    assert_eq!(
        recognize(
            &Literal(atom.clone(), n("Cervantes")),
            &main_grammar,
            tokens_s!("Pierre_Menard")
        ),
        false
    );

    assert_eq!(
        recognize(&Literal(atom.clone(), n("Cervantes")), &main_grammar, tokens_s!("Cervantes")),
        true
    );

    assert_eq!(recognize(&Seq(vec![atom.clone()]), &main_grammar, tokens_s!("P.M.")), true);

    assert_eq!(recognize(&Star(atom.clone()), &main_grammar, tokens_s!("PM")), true);

    assert_eq!(
        recognize(
            &Alt(vec![Rc::new(Impossible), atom.clone()]),
            &main_grammar,
            tokens_s!("Pierre_Menard")
        ),
        true
    );

    assert_eq!(
        recognize(
            &Alt(vec![Rc::new(Impossible), Rc::new(Literal(atom.clone(), n("Cervantes")))]),
            &main_grammar,
            tokens_s!("Pierre_Menard")
        ),
        false
    );

    assert_eq!(
        recognize(
            &Biased(Rc::new(Impossible), atom.clone()),
            &main_grammar,
            tokens_s!("Pierre_Menard")
        ),
        true
    );

    assert_eq!(
        recognize(
            &Biased(atom.clone(), Rc::new(Impossible)),
            &main_grammar,
            tokens_s!("Pierre_Menard")
        ),
        true
    );

    // Nesting!

    assert_eq!(
        recognize(
            &Seq(vec![Rc::new(Seq(vec![Rc::new(Seq(vec![atom.clone()]))]))]),
            &main_grammar,
            tokens_s!("Frustrated_Novelist_No_Good_At_Describing_Hands")
        ),
        true
    );

    assert_eq!(
        recognize(
            &Alt(vec![Rc::new(Alt(vec![Rc::new(Alt(vec![atom.clone()]))]))]),
            &main_grammar,
            tokens_s!("(no_pun_intended,_by_the_way)") // What pun?
        ),
        true
    );

    assert_eq!(
        recognize(
            &Plus(Rc::new(Plus(Rc::new(Plus(atom.clone()))))),
            &main_grammar,
            tokens_s!("(except_I_might've_changed_it_otherwise)")
        ),
        true
    );

    // Fine, there are longer strings.

    assert_eq!(
        recognize(
            &Seq(vec![atom.clone(), atom.clone(), atom.clone()]),
            &main_grammar,
            tokens_s!("Author" "of_the" "Quixote")
        ),
        true
    );

    assert_eq!(
        recognize(
            &Seq(vec![atom.clone(), atom.clone(), atom.clone()]),
            &main_grammar,
            tokens_s!("Author" "of" "the" "Quixote")
        ),
        false
    );

    assert_eq!(
        recognize(
            &Seq(vec![atom.clone(), atom.clone(), atom.clone()]),
            &main_grammar,
            tokens_s!("Author_of" "the_Quixote")
        ),
        false
    );

    assert_eq!(
        recognize(
            &Plus(Rc::new(Plus(Rc::new(Plus(atom.clone()))))),
            &main_grammar,
            tokens_s!("Author" "of" "the" "Quixote")
        ),
        true
    );
}

#[test]
fn earley_env_recognition() {
    fn mk_lt(s: &str) -> Rc<FormPat> {
        Rc::new(Literal(Rc::new(crate::grammar::new_scan(r"\s*(\S+)")), n(s)))
    }
    let env = assoc_n!(
        "empty" => Rc::new(Seq(vec![])),
        "empty_indirect" => Rc::new(Call(n("empty"))),
        "impossible" => Rc::new(Impossible),
        "a" => mk_lt("a"),
        "aaa" => Rc::new(Star(mk_lt("a"))),
        "aaa_indirect" => Rc::new(Star(Rc::new(Call(n("a"))))),
        "aaaa" => Rc::new(Plus(mk_lt("a"))),
        "xxx" => Rc::new(Star(mk_lt("x"))),
        "l_rec_axxx" => Rc::new(Alt(vec![Rc::new(Seq(vec![Rc::new(Call(n("l_rec_axxx"))),
                                                          mk_lt("x")])),
                                         mk_lt("a")])),
        "l_rec_axxx_hard" => Rc::new(
            Alt(vec![Rc::new(Seq(vec![Rc::new(Call(n("l_rec_axxx_hard"))),
                                      Rc::new(Alt(vec![mk_lt("x"),
                                                       Rc::new(Call(n("impossible"))),
                                                       Rc::new(Call(n("empty_indirect")))]))])),
                                      Rc::new(Call(n("impossible"))),
                                      mk_lt("a")])),
        "r_rec_xxxa" => Rc::new(Alt(vec![Rc::new(Seq(vec![mk_lt("x"),
                                                  Rc::new(Call(n("r_rec_xxxa")))])),
                                 mk_lt("a")])),
        "l_rec_aaaa" => Rc::new(Alt(vec![Rc::new(Seq(vec![Rc::new(Call(n("l_rec_aaaa"))),
                                                          mk_lt("a")])),
                                 mk_lt("a")])),
        "r_rec_aaaa" => Rc::new(Alt(vec![Rc::new(Seq(vec![mk_lt("a"),
                                                          Rc::new(Call(n("r_rec_aaaa")))])),
                                 mk_lt("a")])));

    assert_eq!(recognize(&*mk_lt("a"), &env, tokens_s!("a")), true);
    assert_eq!(recognize(&*mk_lt("a"), &env, tokens_s!("b")), false);

    assert_eq!(recognize(&Call(n("empty")), &env, tokens_s!()), true);
    assert_eq!(recognize(&Call(n("empty")), &env, tokens_s!("not empty!")), false);

    assert_eq!(recognize(&Call(n("empty_indirect")), &env, tokens_s!()), true);
    assert_eq!(recognize(&Call(n("empty_indirect")), &env, tokens_s!("not empty!")), false);

    assert_eq!(recognize(&Call(n("aaa")), &env, tokens_s!()), true);
    assert_eq!(recognize(&Call(n("aaa")), &env, tokens_s!("a")), true);
    assert_eq!(recognize(&Call(n("aaa")), &env, tokens_s!("a" "a")), true);
    assert_eq!(recognize(&Call(n("aaa")), &env, tokens_s!("a" "a" "a")), true);
    assert_eq!(recognize(&Call(n("aaa")), &env, tokens_s!("a" "x" "a")), false);

    assert_eq!(recognize(&Call(n("aaaa")), &env, tokens_s!()), false);
    assert_eq!(recognize(&Call(n("aaaa")), &env, tokens_s!("a")), true);
    assert_eq!(recognize(&Call(n("aaaa")), &env, tokens_s!("a" "a")), true);
    assert_eq!(recognize(&Call(n("aaaa")), &env, tokens_s!("a" "a" "a")), true);
    assert_eq!(recognize(&Call(n("aaaa")), &env, tokens_s!("a" "x" "a")), false);

    assert_eq!(recognize(&Call(n("aaa_indirect")), &env, tokens_s!()), true);
    assert_eq!(recognize(&Call(n("aaa_indirect")), &env, tokens_s!("a")), true);
    assert_eq!(recognize(&Call(n("aaa_indirect")), &env, tokens_s!("a" "a")), true);
    assert_eq!(recognize(&Call(n("aaa_indirect")), &env, tokens_s!("a" "a" "a")), true);
    assert_eq!(recognize(&Call(n("aaa_indirect")), &env, tokens_s!("a" "x" "a")), false);

    for l_rec in vec!["l_rec_axxx", "l_rec_axxx_hard"] {
        assert_eq!(recognize(&Call(n(l_rec)), &env, tokens_s!("a")), true);
        assert_eq!(recognize(&Call(n(l_rec)), &env, tokens_s!("a" "x")), true);
        assert_eq!(recognize(&Call(n(l_rec)), &env, tokens_s!("a" "x" "x")), true);
        assert_eq!(recognize(&Call(n(l_rec)), &env, tokens_s!("a" "x" "x" "x")), true);
        assert_eq!(recognize(&Call(n(l_rec)), &env, tokens_s!("a" "a" "x" "x")), false);
        assert_eq!(recognize(&Call(n(l_rec)), &env, tokens_s!()), false);
        assert_eq!(recognize(&Call(n(l_rec)), &env, tokens_s!("a" "x" "a" "x")), false);
    }
}

#[test]
fn basic_parsing_e() {
    fn mk_lt(s: &str) -> Rc<FormPat> {
        Rc::new(Literal(Rc::new(crate::grammar::new_scan(r"\s*(\S+)")), n(s)))
    }

    let atom = Rc::new(crate::grammar::new_scan(r"\s*(\S+)"));

    assert_eq!(parse_top(&*atom, tokens_s!("asdf")), Ok(ast!("asdf")));

    assert_eq!(parse_top(&Anyways(ast!("asdf")), tokens_s!()), Ok(ast!("asdf")));

    assert_eq!(
        parse_top(&Biased(Rc::new(Anyways(ast!("A"))), Rc::new(Anyways(ast!("B")))), tokens_s!()),
        Ok(ast!("A"))
    );

    assert_eq!(
        parse_top(&Named(n("c"), Rc::new(Anyways(ast!("asdf")))), tokens_s!()),
        Ok(ast!({- "c" => "asdf"}))
    );

    assert_eq!(parse_top(&Seq(vec![atom.clone()]), tokens_s!("asdf")), Ok(ast_shape!("asdf")));

    assert_eq!(
        parse_top(
            &Seq(vec![atom.clone(), mk_lt("fork"), atom.clone()]),
            tokens_s!("asdf" "fork" "asdf")
        ),
        Ok(ast_shape!("asdf" "fork" "asdf"))
    );

    assert_eq!(
        parse_top(
            &Seq(vec![
                Rc::new(Seq(vec![mk_lt("aa"), mk_lt("ab")])),
                Rc::new(Seq(vec![mk_lt("ba"), mk_lt("bb")]))
            ]),
            tokens_s!("aa" "ab" "ba" "bb")
        ),
        Ok(ast_shape!(("aa" "ab") ("ba" "bb")))
    );

    assert!(!parse_top(
        &Seq(vec![atom.clone(), mk_lt("fork"), atom.clone()]),
        tokens_s!("asdf" "knife" "asdf"),
    )
    .is_ok());

    assert_eq!(
        parse_top(
            &form_pat!([(star (named "c", (alt (lit_aat "X"), (lit_aat "O")))), (lit_aat "!")]),
            tokens_s!("X" "O" "O" "O" "X" "X" "!")
        ),
        Ok(ast_shape!({- "c" => ["X", "O", "O", "O", "X", "X"]} "!"))
    );

    assert_eq!(
        parse_top(
            &Seq(vec![Rc::new(Star(Rc::new(Named(n("c"), mk_lt("*"))))), mk_lt("X")]),
            tokens_s!("*" "*" "*" "*" "*" "X")
        ),
        Ok(ast_shape!({- "c" => ["*", "*", "*", "*", "*"] } "X"))
    );

    assert_m!(
        parse_top(
            &form_pat!([(star (biased (lit_aat "a"), (lit_aat "b"))), (lit_aat "b")]),
            tokens_s!["a" "a" "b"]
        ),
        Ok(_)
    );

    assert_m!(
        parse_top(
            &form_pat!([(star (biased (lit_aat "b"), (lit_aat "a"))), (lit_aat "b")]),
            tokens_s!["a" "a" "b"]
        ),
        Ok(_)
    );

    assert_eq!(parse_top(&form_pat!([(lit_aat "b")]), tokens_s!["b"]), Ok(ast_shape!("b")));

    assert_eq!(parse_top(&form_pat!(varref_aat), tokens_s!("Spoon")), Ok(ast!((vr "Spoon"))));

    assert_eq!(
        parse_top(&form_pat!((reserved varref_aat, "Moon")), tokens_s!("Spoon")),
        Ok(ast!((vr "Spoon")))
    );

    assert_eq!(
        parse_top(
            &form_pat!((alt (lit_aat "Moon"), (reserved varref_aat, "Moon"))),
            tokens_s!("Spoon")
        ),
        Ok(ast!((vr "Spoon")))
    );

    let code_envs = (
        LazyWalkReses::<crate::ty::SynthTy>::new_empty(),
        LazyWalkReses::<crate::runtime::eval::Eval>::new_empty(),
    );

    let env = assoc_n!(
        "DefaultToken" => atom.clone()
    );

    assert_eq!(
        parse(
            &form_pat!((alt (lit_aat "Moon"), (reserved (scan r"\s*(\S+)"), "Moon"))),
            &env,
            code_envs.clone(),
            tokens_s!("Moon")
        ),
        Ok(ast!("Moon")) // Not a varref, so it's the literal instead
    );

    assert_eq!(
        // `lit` calls "DefaultToken"
        parse(&form_pat!((lit "Moon")), &env, code_envs.clone(), tokens_s!("Moon")),
        Ok(ast!("Moon"))
    );
}
