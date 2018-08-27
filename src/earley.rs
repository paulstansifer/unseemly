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

use parse::{FormPat, SynEnv};
use parse::FormPat::*;
use read::{Token, TokenTree};
use read::Token::*;
use ast::Ast;
use std::rc::Rc;
use std::cell::RefCell;
use name::*;

pub fn end_of_delim() -> Token {
    Token::Simple(n("☾end delimiter☽"))
}

// TODO: This UniqueId stuff is great, but we could make things faster
//  by storing array indices instead

thread_local! {
    static next_id: RefCell<u32> = RefCell::new(0);
    static all_grammars: RefCell<::std::collections::HashMap<UniqueIdRef, SynEnv>>
        = RefCell::new(::std::collections::HashMap::new());

    static best_token: RefCell<(usize, Name)> = RefCell::new((0, n("[nothing parsed]")));
}

fn get_next_id() -> UniqueId {
    next_id.with(|id| {
        let res = UniqueId(*id.borrow());
        *id.borrow_mut() += 1;
        res
    })
}

// Specifically *not* `Clone` or `Copy`
#[derive(PartialEq,Eq)]
pub struct UniqueId(u32);

impl ::std::fmt::Debug for UniqueId {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(PartialEq,Eq,Clone,Copy,Hash)]
pub struct UniqueIdRef(u32);

impl UniqueId {
    fn get_ref(&self) -> UniqueIdRef { UniqueIdRef(self.0) }

    fn is(&self, other: UniqueIdRef) -> bool { self.0 == other.0 }
}

impl ::std::fmt::Debug for UniqueIdRef {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

// TODO: this shouldn't be hardcoded into the parser; it should be ... how should it work?
fn reserved(nm: Name) -> bool {
    Simple(nm) == end_of_delim() || nm == n("forall") || nm == n("mu_type")
        || nm == n("Int") || nm == n("Ident") || nm == n("Float") || nm == n("match")
        || nm == n("enum") || nm == n("struct") || nm == n("fold") || nm == n("unfold")
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

    // Everything after this line is nonstandard, and is just here as an optimization


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
    ///  has so many different kings of rules!
    wanted_by: Rc<RefCell<Vec<UniqueIdRef>>>
}

/// Information for parsing. It's not a parse tree, but it tells you the next step to get one.
/// (Hence "local")
#[derive(PartialEq,Debug,Clone)]
enum LocalParse {
    /// ⊤; no information yet
    NothingYet,
    JustifiedByItemPlanB(UniqueIdRef), // Looking for a better parse, though... (for `Biased`)
    JustifiedByItem(UniqueIdRef),
    ParsedAtom(Ast),
    /// ⊥; contradiction (TMI!)
    Ambiguous(Box<LocalParse>, Box<LocalParse>)
}
use self::LocalParse::*;

impl PartialOrd for LocalParse {
    /// Establish a lattice for `LocalParse`; some parses are better than others.
    /// `Biased` allows one to find a "Plan B" parse that gets overwritten by "Plan A".
    /// But there's also `NothingYet`, for ... (TODO: only leaves and just-started nodes?)
    /// ... and `Ambiguous`, when we know that there are multiple justifications for a single node
    fn partial_cmp(&self, other: &LocalParse) -> Option<::std::cmp::Ordering> {
        use ::std::cmp::Ordering::*;
        if self == other { return Some(Equal) }
        match (self, other) {
            (&NothingYet, _) | (_, &Ambiguous(_,_)) => Some(Less),
            (&Ambiguous(_,_), _) | (_, &NothingYet) => Some(Greater),
            (&JustifiedByItemPlanB(_), &JustifiedByItem(_)) => Some(Less),
            (&JustifiedByItem(_), &JustifiedByItemPlanB(_)) => Some(Greater),
            (&JustifiedByItem(_), &JustifiedByItem(_)) => None,
            // semantically, this ought to be `None`, but that would be a hard-to-debug logic error
            _ => { panic!("Attempted to compare {:?} and {:?}", self, other) }
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
            id: get_next_id(),
            done: self.done.clone(),
            local_parse: RefCell::new(LocalParse::NothingYet),
            wanted_by: self.wanted_by.clone()
        }
    }
}

/// Progress through the state sets
// TODO: this ought to produce an Option<ParseError>, not a bool!
fn create_chart(rule: Rc<FormPat>, grammar: SynEnv, tt: &TokenTree)
        -> (UniqueId, Vec<Vec<Item>>) {
    let mut chart = vec![vec![]];
    let mut cur_tok = 0;

    let start_but_startier = get_next_id();

    let start_item =
        Item{start_idx: 0, rule: rule, pos: 0, grammar: grammar, id: get_next_id(),
             done: RefCell::new(false), local_parse: RefCell::new(LocalParse::NothingYet),
             wanted_by: Rc::new(RefCell::new(vec![start_but_startier.get_ref()]))};

    chart[0].push(start_item);
    for t in &tt.t {
        walk_tt(&mut chart, t, &mut cur_tok);
    }
    examine_state_set(&mut chart, None, cur_tok); // One last time, for nullable rules at the end

    (start_but_startier, chart)
}

fn recognize(rule: &FormPat, grammar: &SynEnv, tt: &TokenTree) -> bool {
    let (start_but_startier, chart) = create_chart(Rc::new(rule.clone()), grammar.clone(), tt);

    chart[chart.len()-1].iter().any(
        |item|
            (*item.wanted_by.borrow()).iter().any(|idr| start_but_startier.is(*idr))
            && *item.done.borrow()
    )
}

fn walk_tt(chart: &mut Vec<Vec<Item>>, t: &Token, cur_tok: &mut usize) {
    chart.push(vec![]);
    examine_state_set(chart, Some(t), *cur_tok);
    //log!("\n  {:?}\n->{:?}\n", chart[*cur_tok], chart[*cur_tok + 1]);
    *cur_tok += 1;
    match *t {
        Simple(_) => { }
        Group(_, _, ref tree) => {
            for sub_tok in &tree.t {
                walk_tt(chart, sub_tok, cur_tok);
            }
            walk_tt(chart, &end_of_delim(), cur_tok);
        }
    }
}

/// Progresses a state set until it won't go any further.
/// Returns the state set for the next token.
fn examine_state_set(chart: &mut Vec<Vec<Item>>, tok: Option<&Token>, cur_tok: usize) {
    // If nullable items are statically identified, I think there's an optimization
    //  where we don't re-walk old items
    loop {
        if ! new_items_from_state_set(chart, tok, cur_tok) { break; } // reached the fixpoint?
    }
}

fn new_items_from_state_set(chart: &mut Vec<Vec<Item>>, tok: Option<&Token>,
                                cur_tok: usize) -> bool {
    let mut effect = false;
    for idx in 0..chart[cur_tok].len() {
        for (new_item, next) in chart[cur_tok][idx].examine(tok, cur_tok, chart) {
            effect = merge_into_state_set(new_item, &mut chart[cur_tok + if next {1} else {0}])
                || effect;
        }
    }
    effect
}

// Returns whether anything happened
fn merge_into_state_set(item: Item, items: &mut Vec<Item>)
        -> bool {
    for i in items.iter() {
        if i.similar(&item) {
            if i.as_good_as(&item) { return false; /* no new information */ }
            log!("improved item: {:?} vs. {:?}\n", item, i);
            i.merge(&item);
            return true;
        }
    }
    log!("new item: {:?}\n", item);
    items.push(item);

    true
}

impl ::std::fmt::Debug for Item {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "[({:?}){}({:?}.{}){}<{:?} - {:?}>]",
               self.id, self.start_idx, self.rule, self.pos,
               if *self.done.borrow() { "✓" } else { "…" },
               self.local_parse.borrow(), self.wanted_by.borrow())
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
        if *other.done.borrow() { *self.done.borrow_mut() = true; }

        use ::std::cmp::Ordering::*;
        let comparison = other.local_parse.borrow().partial_cmp(&*self.local_parse.borrow());
        log!("\n(For {}) Merging {:?} and {:?}... ", self.id.0, *other.local_parse.borrow(),
             *self.local_parse.borrow());
        match comparison {
            Some(Greater) => {
                *self.local_parse.borrow_mut() = other.local_parse.borrow().clone();
            },
            Some(Equal) | Some(Less) => { /* no new information */ },
            None => {
                let amb = LocalParse::Ambiguous(Box::new(self.local_parse.borrow().clone()),
                                                Box::new(other.local_parse.borrow().clone()));
                *self.local_parse.borrow_mut() = amb;
            }
        }
        log!("... into {:?}\n", *self.local_parse.borrow());

        for other_wanted in other.wanted_by.borrow().iter() {
            let mut has = false;
            for self_wanted in self.wanted_by.borrow().iter() {
                if self_wanted == other_wanted {
                    has = true; break;
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

    fn advance(&self, consume_tok: bool) -> Vec<(Item, bool)> {
        log!("[adv ({})]", self.id.0);
        vec![(Item{ pos: self.pos + 1,  .. self.clone() },
              consume_tok)]
    }

    fn finish_with(&self, lp: LocalParse, consume_tok: bool) -> Vec<(Item, bool)> {
        log!("[fin_w/ ({})]", self.id.0);
        vec![(Item{ done: RefCell::new(true), local_parse: RefCell::new(lp),
                    pos: self.pos + 1,  .. self.clone() },
              consume_tok)]
    }

    fn finish(&self, consume_tok: bool) -> Vec<(Item, bool)> {
        log!("[finish ({})]", self.id.0);
        vec![(Item{ done: RefCell::new(true), local_parse: RefCell::new(LocalParse::NothingYet),
                    pos: self.pos + 1,  .. self.clone() },
              consume_tok)]
    }

    fn start(&self, rule: Rc<FormPat>, cur_idx: usize) -> Vec<(Item, bool)> {
        log!("[start ({})]", self.id.0);
        vec![(Item { start_idx: cur_idx, rule: rule, pos: 0, done: RefCell::new(false),
                     grammar: self.grammar.clone(),
                     local_parse: RefCell::new(LocalParse::NothingYet), id: get_next_id(),
                     wanted_by: Rc::new(RefCell::new(vec![self.id.get_ref()]))
              },
              false)]
    }

    // -----------------------------------------------------------


    /// See what new items this item justifies
    fn examine(&self, cur: Option<&Token>, cur_idx: usize, chart: &[Vec<Item>])
            -> Vec<(Item, bool)> {
        let mut res = if *self.done.borrow() {
            let mut waiting_satisfied = vec![];

            log!("({:?}) done; {} items want it\n", self, (*self.wanted_by.borrow()).len());

            for &waiting_item_id in self.wanted_by.borrow().iter() {
                if let Some(waiting_item) = chart[self.start_idx].iter()
                    .find(|i| i.id.is(waiting_item_id)) { // It's `None` if it's the startier item


                    let me_justif = JustifiedByItem(self.id.get_ref());

                    // We `finish_with` here for things that are waiting on other items,
                    //  in `shift_or_predict` for leaves.
                    // Except for `Seq`. TODO: why?
                    let mut more = match *waiting_item.rule {
                        Anyways(_) | Impossible | Literal(_) | AnyToken | AnyAtomicToken
                        | VarRef => {
                            panic!("{:?} should not be waiting for anything!", waiting_item)
                        }
                        Seq(ref subs) => {
                            if (waiting_item.pos) as usize == subs.len() {
                                vec![]
                            } else { // Like `waiting_item.advance`, but with a local_parse
                                vec![(Item { pos: waiting_item.pos+1,
                                             local_parse: RefCell::new(me_justif),
                                               .. waiting_item.clone() }, false)]
                            }
                        }
                        Delimited(_,_,_) => { // Like `waiting_item.advance` (etc.)
                            vec![(Item { pos: waiting_item.pos+1,
                                         local_parse: RefCell::new(me_justif),
                                           .. waiting_item.clone() }, false)]
                        }
                        Plus(_) | Star(_) => { // It'll also keep going, though!
                            waiting_item.finish_with(me_justif, false)
                        }
                        SynImport(_,_,_) if waiting_item.pos == 0 => {
                            vec![(Item { pos: 1,
                                         local_parse: RefCell::new(me_justif),
                                           .. waiting_item.clone() }, false)]
                        }
                        Alt(_) | Call(_) | ComputeSyntax(_,_)
                        | Scope(_,_) | Named(_,_) | SynImport(_,_,_) | NameImport(_,_)
                        | QuoteDeepen(_,_) | QuoteEscape(_,_) => {
                            waiting_item.finish_with(me_justif, false)
                        }
                        Biased(ref _plan_a, ref plan_b) => {
                            if &*self.rule as *const FormPat == &**plan_b as *const FormPat {
                                waiting_item.finish_with(
                                    JustifiedByItemPlanB(self.id.get_ref()), false)
                            } else {
                                waiting_item.finish_with(me_justif, false)
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
            if let Some(&Simple(n)) = cur {
                best_token.with(|bt| *bt.borrow_mut() = (cur_idx, n));
            }
        }

        res.append(&mut self.shift_or_predict(cur, cur_idx, chart));

        res
    }

    fn shift_or_predict(&self, cur: Option<&Token>, cur_idx: usize, chart: &[Vec<Item>])
            -> Vec<(Item, bool)> {
        // Try to shift (bump `pos`, or set `done`) or predict (`start` a new item)
        match (self.pos, &*(self.rule.clone())) { // TODO: is there a better way to match in `Rc`?
            (0, &Anyways(ref a)) => self.finish_with(ParsedAtom(a.clone()), false),
            (_, &Impossible) =>  vec![],
            (0, &Literal(xptd_n)) => {
                match cur {
                    Some(&Simple(n)) if xptd_n == n =>  {
                        self.finish_with(ParsedAtom(::ast::Atom(n)), true)
                    }
                    _ => vec![]
                }
            },
            // TODO: without checking for `end_of_delim()`, `(plus (plus (plus one one) one) one)`
            //  parses incorrectly (one of the `end_of_delim()`s winds up in a VarRef).
            // But this should just be an optimization...
            // Maybe it has something to do with how we handle end-of-file?
            (0, &AnyToken) => {
                match cur {
                    Some(&Simple(n)) if !reserved(n) => {
                      self.finish_with(ParsedAtom(::ast::Atom(n)), true)
                    }
                    Some(&Group(_,_,_)) => self.finish_with(ParsedAtom(::ast::Trivial), true), // TODO
                    _ => vec![]
                }
            },
            (0, &AnyAtomicToken) => {
                match cur {
                    Some(&Simple(n)) if !reserved(n) => {
                      self.finish_with(ParsedAtom(::ast::Atom(n)), true)
                    }
                    _ => vec![]
                }
            },
            (0, &VarRef) => {
                match cur {
                    Some(&Simple(n)) if !reserved(n) => {
                        self.finish_with(ParsedAtom(::ast::VariableReference(n)), true)
                    },
                    _ => vec![]
                }
            },
            // TODO: does `advance_one_token == true` just work to mean "descend here"?
            (0, &Delimited(ref xptd_n, ref xptd_delim, _)) => {
                match cur {
                    Some(&Group(ref n, ref delim, _)) if n == xptd_n && delim == xptd_delim
                        => self.advance(true),
                    _ => vec![]
                }
            },
            (1, &Delimited(_, _, ref xptd_body)) => {
                self.start(xptd_body.clone(), cur_idx)
            },
            (2, &Delimited(_,_,_)) => {
                match cur {
                    Some(t) if t == &end_of_delim() => { // like `.finish`, but keeping local_parse
                        vec![(Item{done: RefCell::new(true), pos: self.pos + 1,
                                   local_parse: RefCell::new(self.local_parse.borrow().clone()),
                                    .. self.clone()},
                              true)]},
                    _ => { vec![] }
                }
            },
            (pos, &Seq(ref subs)) => {
                if pos < subs.len() {
                    self.start(subs[pos as usize].clone(), cur_idx)
                } else if pos == subs.len() { // a little like `.finish`, but without advancing
                    vec![(Item{ done: RefCell::new(true), .. self.clone()}, false)]
                } else {
                    vec![]
                }
            },
            (_, &Star(ref sub)) => {
                // Special case: the elegant thing would be to create `Star` pre-`done`
                let mut res = if self.pos == 0 { // Like `.finish`, but without advancing
                    vec![(Item{ done: RefCell::new(true), .. self.clone()}, false)]
                } else { vec![] };
                res.append(&mut self.start(sub.clone(), cur_idx)); // But we can take more!
                res
            },
            (_, &Plus(ref sub)) => {
                self.start(sub.clone(), cur_idx)
            },
            (0, &Alt(ref subs)) => {
                let mut res = vec![];
                for sub in subs {
                    res.append(&mut self.start((*sub).clone(), cur_idx));
                }
                res
            },
            // Needs special handling elsewhere!
            (0, &Biased(ref plan_a, ref plan_b)) => {
                let mut res =   self.start(plan_a.clone(), cur_idx);
                res.append(&mut self.start(plan_b.clone(), cur_idx));
                res
            },
            (0, &Call(n)) => {
                self.start(self.grammar.find_or_panic(&n).clone(), cur_idx)
            },
            (0, &Scope(ref f, _)) => { // form.grammar is a FormPat. Confusing!
                self.start(f.grammar.clone(), cur_idx)
            },
            (0, &SynImport(ref lhs, _, _)) => {
                self.start(lhs.clone(), cur_idx)
            }
            (1, &SynImport(_, ref name, ref f)) => {
                // TODO: handle errors properly! Probably need to memoize, also!
                let partial_parse = match *self.local_parse.borrow() {
                    NothingYet | Ambiguous(_, _) => return vec![],
                    ParsedAtom(ref a) => a.clone(),
                    JustifiedByItem(_) | JustifiedByItemPlanB(_) => {
                        match self.find_wanted(chart, cur_idx).c_parse(chart, cur_idx) {
                            Ok(ast) => ast,
                            Err(_) => { return vec![]; }
                        }
                    }
                };

                let new_se = all_grammars.with(|grammars| {
                    let mut mut_grammars = grammars.borrow_mut();
                    mut_grammars.entry(self.id.get_ref()) // memoize
                        .or_insert_with(|| f.0(self.grammar.clone(), partial_parse)).clone()
                });

                vec![(Item { start_idx: cur_idx, rule: new_se.find_or_panic(name).clone(), pos: 0,
                             done: RefCell::new(false),
                             grammar: new_se, local_parse: RefCell::new(LocalParse::NothingYet),
                             id: get_next_id(),
                             wanted_by: Rc::new(RefCell::new(vec![self.id.get_ref()]))
                      },
                      false)]
            }
            (0, &ComputeSyntax(_,_)) => { panic!("TODO") },
            (0, &Named(_, ref body)) | (0, &NameImport(ref body, _))
            | (0, &QuoteDeepen(ref body, _)) | (0, &QuoteEscape(ref body, _)) => {
                self.start(body.clone(), cur_idx)
            },
            // Rust rightly complains that this is unreachable; yay!
            // But how do I avoid a catch-all pattern for the pos > 0 case?
            //(0, _) =>  { panic!("ICE: unhandled FormPat") },
            _ => { vec![] } // end of a rule
        }
    }

    fn find_wanted<'f, 'c>(&'f self, chart: &'c [Vec<Item>], done_tok: usize)
            -> &'c Item {
        let mut first_found : Option<&Item> = None;
        let local_parse = self.local_parse.borrow().clone();
        let desired_id = match local_parse {
            JustifiedByItem(id) | JustifiedByItemPlanB(id) => id,
            Ambiguous(ref l, ref r) => { // HACK: this is quite ugly!
                let l = *l.clone();
                let r = *r.clone();
                log!("===Ambiguity===\n");
                // Show both parses...
                *self.local_parse.borrow_mut() = l;
                let l_res = self.c_parse(chart, done_tok);
                *self.local_parse.borrow_mut() = r;
                let r_res = self.c_parse(chart, done_tok);


                panic!("Ambiguity! \n{:?}\n{:?}\n", l_res, r_res)
            },
            _ => panic!("ICE: tried to parse unjustified item: {:?} ", self)
        };
        log!("We are {:?} at {}...\n", self, done_tok);

        for idx in 0..chart[done_tok].len() {
            let i = &chart[done_tok][idx];

            if i.id.is(desired_id) {
                match first_found {
                    None => { first_found = Some(i); }
                    Some(_) => { panic!("ICE: unacknowledged ambiguity!") }
                }
            }
        }

        first_found.expect("ICE: no parse after successful recognition")
    }

    /// After the chart is built, we parse...
    fn c_parse(&self, chart: &[Vec<Item>], done_tok: usize) -> ParseResult {
        log!("Tring to parse {:?}...\n", self);
        // assert!(*self.done.borrow()); // false during ambiguity reporting
        let res = match *self.rule {
            Anyways(ref a) => Ok(a.clone()),
            Impossible => panic!("Impossible!"),
            Literal(_) | AnyToken | AnyAtomicToken | VarRef => {
                match self.local_parse.borrow().clone() {
                    ParsedAtom(a) => Ok(a), _ => { panic!("ICE: no simple parse saved")}
                }
            },
            Delimited(_, _, _) => {
                // HACK: the wanted item is misaligned by a token because of the close delimiter
                self.find_wanted(chart, done_tok-1).c_parse(chart, done_tok-1)
            }
            Alt(_) | Biased(_, _) | Call(_) | SynImport(_,_, _) => {
                self.find_wanted(chart, done_tok).c_parse(chart, done_tok)
            },
            Seq(_) | Star(_) | Plus(_) => {
                let mut step = self;
                let mut subtrees = vec![];
                let mut pos = done_tok;
                // Walk over "previous incarnations" of `self`
                // TODO: It seems like I often have had the thought
                //  "Why not put a nullable pattern under `Star`? What could go wrong?"
                // Do something about that...
                loop {
                    log!("Trying to take a step...\n");
                    // Special case: we can't start the loop because there are 0 children
                    if let NothingYet = step.local_parse.borrow().clone() { break; }

                    let sub = step.find_wanted(chart, pos);
                    subtrees.push(try!(sub.c_parse(chart, pos)));
                    if sub.start_idx == self.start_idx && step.pos == 1 {
                        break;
                    } else {
                        pos = sub.start_idx;
                        let mut found = false;
                        for idx in 0..chart[pos].len() {
                            let i = &chart[pos][idx];
                            log!("Checking {:?}\n", i);
                            if self.grammar.almost_ptr_eq(&i.grammar)
                                && &*self.rule as *const FormPat == &*i.rule as *const FormPat
                                && step.pos - 1 == i.pos {
                                step = i;
                                found = true;
                                break;
                            }
                        }
                        if !found { panic!("ICE: Can't find item previous to {:?}", step) }
                    }
                }
                subtrees.reverse();

                match *self.rule {
                    Seq(_) => Ok(Ast::Shape(subtrees)),
                    Star(_) | Plus(_) => Ok(Ast::IncompleteNode(
                        ::util::mbe::EnvMBE::new_from_anon_repeat(
                            subtrees.into_iter().map(|a| a.flatten()).collect()))),
                    _ => { panic!("ICE: seriously, this can't happen") }
                }
            },
            ComputeSyntax(_, _) => { panic!("TODO") },
            Named(name, _) => {
                let sub_parsed = try!(self.find_wanted(chart, done_tok).c_parse(chart, done_tok));
                Ok(Ast::IncompleteNode(::util::mbe::EnvMBE::new_from_leaves(
                    ::util::assoc::Assoc::single(name, sub_parsed))))
            },
            Scope(ref form, ref export) => {
                let sub_parsed = try!(self.find_wanted(chart, done_tok).c_parse(chart, done_tok));
                Ok(Ast::Node(form.clone(), sub_parsed.flatten(), export.clone()))
            },
            NameImport(_, ref beta) => {
                let sub_parsed = try!(self.find_wanted(chart, done_tok).c_parse(chart, done_tok));
                Ok(Ast::ExtendEnv(Box::new(sub_parsed), beta.clone()))
            }
            QuoteDeepen(_, pos) => {
                let sub_parsed = try!(self.find_wanted(chart, done_tok).c_parse(chart, done_tok));
                Ok(Ast::QuoteMore(Box::new(sub_parsed), pos))
            }
            QuoteEscape(_, depth) => {
                let sub_parsed = try!(self.find_wanted(chart, done_tok).c_parse(chart, done_tok));
                Ok(Ast::QuoteLess(Box::new(sub_parsed), depth))
            }
        };
        log!(">>>{:?}<<<\n", res);

        res
    }
}

type ParseResult = Result<Ast, ParseError>;

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct ParseError {
    pub msg: String
}

pub fn parse(rule: &FormPat, grammar: &SynEnv, tt: &TokenTree) -> ParseResult {
    let (start_but_startier, chart) = create_chart(Rc::new(rule.clone()), grammar.clone(), tt);
    let final_item = chart[chart.len()-1].iter().find(
        |item|
            (*item.wanted_by.borrow()).iter().any(|idr| start_but_startier.is(*idr))
            && *item.done.borrow());
    log!("-------\n");
    match final_item {
        Some(i) => i.c_parse(&chart, chart.len()-1),
        None => {
            best_token.with(|bt| {
                let (idx, tok) = *bt.borrow();
                Err(ParseError{ msg: format!("Parse error near position {} ({})", idx, tok) })
            })
        }
    }
}

fn parse_top(rule: &FormPat, tt: &TokenTree) -> ParseResult {
    parse(rule, &::util::assoc::Assoc::new(), tt)
}

#[test]
fn earley_merging() {
    let one_rule = AnyToken;
    let another_rule = Impossible;
    let main_grammar = assoc_n!("a" => Rc::new(form_pat!(aat)));
    let another_grammar = assoc_n!("a" => Rc::new(form_pat!(aat)));
    let mut state_set = vec![];

    let basic_item = Item{start_idx: 0, rule: Rc::new(one_rule), pos: 0,
                          grammar: main_grammar.clone(),
                          id: get_next_id(), done: RefCell::new(false),
                          local_parse: RefCell::new(LocalParse::NothingYet),
                          wanted_by: Rc::new(RefCell::new(vec![]))};

    assert_eq!(merge_into_state_set(basic_item.clone(), &mut state_set), true);
    assert_eq!(state_set.len(), 1);

    // exactly the same (except a different ID)
    assert_eq!(merge_into_state_set(basic_item.clone(), &mut state_set), false);
    assert_eq!(state_set.len(), 1);

    // (not done yet)
    assert_eq!(*state_set[0].done.borrow(), false);

    // improvement in doneness, mergable
    assert_eq!(merge_into_state_set(Item{done: RefCell::new(true), .. basic_item.clone()},
                                    &mut state_set),
               true);
    assert_eq!(state_set.len(), 1);
    // now done!
    assert_eq!(*state_set[0].done.borrow(), true);

    // not an improvement this time!
    assert_eq!(merge_into_state_set(Item{done: RefCell::new(true), .. basic_item.clone()},
                                    &mut state_set),
               false);
    assert_eq!(state_set.len(), 1);

    // not as good as
    assert_eq!(merge_into_state_set(Item{done: RefCell::new(false), .. basic_item.clone()},
                                    &mut state_set),
               false);
    assert_eq!(state_set.len(), 1);
    // still done!
    assert_eq!(*state_set[0].done.borrow(), true);

    // different rule
    assert_eq!(merge_into_state_set(Item{rule: Rc::new(another_rule), .. basic_item.clone()},
                                    &mut state_set),
               true);
    assert_eq!(state_set.len(), 2);

    // different grammar (pointer-wise!)
    assert_eq!(merge_into_state_set(Item{grammar: another_grammar.clone(), .. basic_item.clone()},
                                    &mut state_set),
               true);
    assert_eq!(state_set.len(), 3);

    let id1 = get_next_id().get_ref();
    let id2 = get_next_id().get_ref();
    let id3 = get_next_id().get_ref();
            /*
        log!("AGA {:?},{:?},{:?},{:?}\n",
        (*self.done.borrow() == *other.done.borrow() || !*other.done.borrow())
        , *self.local_parse.borrow() == *other.local_parse.borrow()
            , *(other.local_parse).borrow() == LocalParse::NothingYet
        , (other.wanted_by.borrow().len() == 0
            || (other.wanted_by.borrow().iter().all(
                   |w| self.wanted_by.borrow().iter().find(|s_w| w == *s_w).is_some())))

    );
        log!("  {:?}=?{:?}\n", *self.local_parse.borrow(), *other.local_parse.borrow());*/
    let wanted_item = |ids| {
        Item {
            wanted_by: Rc::new(RefCell::new(ids)), .. basic_item.clone()
        }
    };

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
    let main_grammar = ::util::assoc::Assoc::new();

    // 0-length strings

    assert_eq!(recognize(&AnyAtomicToken, &main_grammar, &tokens!()), false);

    assert_eq!(recognize(&Anyways(::ast::Trivial), &main_grammar, &tokens!()), true);

    assert_eq!(recognize(&Seq(vec![]), &main_grammar, &tokens!()), true);

    assert_eq!(recognize(&Seq(vec![Rc::new(AnyAtomicToken)]), &main_grammar, &tokens!()), false);

    assert_eq!(recognize(&Star(Rc::new(Impossible)), &main_grammar, &tokens!()), true);

    assert_eq!(recognize(&Star(Rc::new(AnyAtomicToken)), &main_grammar, &tokens!()), true);

    // 1-length strings

    assert_eq!(recognize(&AnyAtomicToken, &main_grammar, &tokens!("Pierre Menard")), true);

    assert_eq!(recognize(&Impossible, &main_grammar, &tokens!("Pierre Menard")), false);

    assert_eq!(recognize(&Literal(n("Cervantes")), &main_grammar, &tokens!("Pierre Menard")),
               false);

    assert_eq!(recognize(&Literal(n("Cervantes")), &main_grammar, &tokens!("Cervantes")),
               true);

    assert_eq!(recognize(&Seq(vec![Rc::new(AnyAtomicToken)]), &main_grammar, &tokens!("P.M.")),
               true);

    assert_eq!(recognize(&Star(Rc::new(AnyAtomicToken)), &main_grammar, &tokens!("PM")), true);

    assert_eq!(recognize(&Alt(vec![Rc::new(Impossible), Rc::new(AnyAtomicToken)]), &main_grammar,
                         &tokens!("Pierre Menard")), true);

    assert_eq!(recognize(&Alt(vec![Rc::new(Impossible), Rc::new(Literal(n("Cervantes")))]),
                         &main_grammar, &tokens!("Pierre Menard")), false);

    assert_eq!(recognize(&Biased(Rc::new(Impossible), Rc::new(AnyAtomicToken)), &main_grammar,
                         &tokens!("Pierre Menard")), true);

    assert_eq!(recognize(&Biased(Rc::new(AnyAtomicToken), Rc::new(Impossible)), &main_grammar,
                         &tokens!("Pierre Menard")), true);


    // Nesting!

    assert_eq!(recognize(
        &Seq(vec![Rc::new(Seq(vec![Rc::new(Seq(vec![Rc::new(AnyAtomicToken)]))]))]), &main_grammar,
        &tokens!("Frustrated Novelist No Good At Describing Hands")), true);

    assert_eq!(recognize(
        &Alt(vec![Rc::new(Alt(vec![Rc::new(Alt(vec![Rc::new(AnyAtomicToken)]))]))]), &main_grammar,
        &tokens!("(no pun intended, by the way)")), true);

    assert_eq!(recognize(&Plus(Rc::new(Plus(Rc::new(Plus(Rc::new(AnyAtomicToken)))))),
                         &main_grammar,
                         &tokens!("(except I might've changed it otherwise)")), true);


    // Fine, there are longer strings.

    assert_eq!(recognize(
        &Seq(vec![Rc::new(AnyAtomicToken), Rc::new(AnyAtomicToken), Rc::new(AnyAtomicToken)]),
        &main_grammar, &tokens!("Author" "of the" "Quixote")), true);

    assert_eq!(recognize(
        &Seq(vec![Rc::new(AnyAtomicToken), Rc::new(AnyAtomicToken), Rc::new(AnyAtomicToken)]),
        &main_grammar, &tokens!("Author" "of" "the" "Quixote")), false);

    assert_eq!(recognize(
        &Seq(vec![Rc::new(AnyAtomicToken), Rc::new(AnyAtomicToken), Rc::new(AnyAtomicToken)]),
        &main_grammar, &tokens!("Author of" "the Quixote")), false);

    assert_eq!(recognize(&Plus(Rc::new(Plus(Rc::new(Plus(Rc::new(AnyAtomicToken)))))),
                         &main_grammar,
                         &tokens!("Author" "of" "the" "Quixote")), true);

}

#[test]
fn earley_env_recognition() {
    let env = assoc_n!(
        "empty" => Rc::new(Seq(vec![])),
        "empty_indirect" => Rc::new(Call(n("empty"))),
        "impossible" => Rc::new(Impossible),
        "a" => Rc::new(Literal(n("a"))),
        "aaa" => Rc::new(Star(Rc::new(Literal(n("a"))))),
        "aaa_indirect" => Rc::new(Star(Rc::new(Call(n("a"))))),
        "aaaa" => Rc::new(Plus(Rc::new(Literal(n("a"))))),
        "xxx" => Rc::new(Star(Rc::new(Literal(n("x"))))),
        "l_rec_axxx" => Rc::new(Alt(vec![Rc::new(Seq(vec![Rc::new(Call(n("l_rec_axxx"))),
                                                  Rc::new(Literal(n("x")))])),
                                 Rc::new(Literal(n("a")))])),
        "l_rec_axxx_hard" => Rc::new(
            Alt(vec![Rc::new(Seq(vec![Rc::new(Call(n("l_rec_axxx_hard"))),
                                      Rc::new(Alt(vec![Rc::new(Literal(n("x"))),
                                                       Rc::new(Call(n("impossible"))),
                                                       Rc::new(Call(n("empty_indirect")))]))])),
                                      Rc::new(Call(n("impossible"))),
                                      Rc::new(Literal(n("a")))])),
        "r_rec_xxxa" => Rc::new(Alt(vec![Rc::new(Seq(vec![Rc::new(Literal(n("x"))),
                                                  Rc::new(Call(n("r_rec_xxxa")))])),
                                 Rc::new(Literal(n("a")))])),
        "l_rec_aaaa" => Rc::new(Alt(vec![Rc::new(Seq(vec![Rc::new(Call(n("l_rec_aaaa"))),
                                                  Rc::new(Literal(n("a")))])),
                                 Rc::new(Literal(n("a")))])),
        "r_rec_aaaa" => Rc::new(Alt(vec![Rc::new(Seq(vec![Rc::new(Literal(n("a"))),
                                                  Rc::new(Call(n("r_rec_aaaa")))])),
                                 Rc::new(Literal(n("a")))])));

    assert_eq!(recognize(&Literal(n("a")), &env, &tokens!("a")), true);
    assert_eq!(recognize(&Literal(n("a")), &env, &tokens!("b")), false);

    assert_eq!(recognize(&Call(n("empty")), &env, &tokens!()), true);
    assert_eq!(recognize(&Call(n("empty")), &env, &tokens!("not empty!")), false);

    assert_eq!(recognize(&Call(n("empty_indirect")), &env, &tokens!()), true);
    assert_eq!(recognize(&Call(n("empty_indirect")), &env, &tokens!("not empty!")), false);

    assert_eq!(recognize(&Call(n("aaa")), &env, &tokens!()), true);
    assert_eq!(recognize(&Call(n("aaa")), &env, &tokens!("a")), true);
    assert_eq!(recognize(&Call(n("aaa")), &env, &tokens!("a" "a")), true);
    assert_eq!(recognize(&Call(n("aaa")), &env, &tokens!("a" "a" "a")), true);
    assert_eq!(recognize(&Call(n("aaa")), &env, &tokens!("a" "x" "a")), false);

    assert_eq!(recognize(&Call(n("aaaa")), &env, &tokens!()), false);
    assert_eq!(recognize(&Call(n("aaaa")), &env, &tokens!("a")), true);
    assert_eq!(recognize(&Call(n("aaaa")), &env, &tokens!("a" "a")), true);
    assert_eq!(recognize(&Call(n("aaaa")), &env, &tokens!("a" "a" "a")), true);
    assert_eq!(recognize(&Call(n("aaaa")), &env, &tokens!("a" "x" "a")), false);

    assert_eq!(recognize(&Call(n("aaa_indirect")), &env, &tokens!()), true);
    assert_eq!(recognize(&Call(n("aaa_indirect")), &env, &tokens!("a")), true);
    assert_eq!(recognize(&Call(n("aaa_indirect")), &env, &tokens!("a" "a")), true);
    assert_eq!(recognize(&Call(n("aaa_indirect")), &env, &tokens!("a" "a" "a")), true);
    assert_eq!(recognize(&Call(n("aaa_indirect")), &env, &tokens!("a" "x" "a")), false);

    for l_rec in vec!["l_rec_axxx", "l_rec_axxx_hard"] {
        assert_eq!(recognize(&Call(n(l_rec)), &env, &tokens!("a")), true);
        assert_eq!(recognize(&Call(n(l_rec)), &env, &tokens!("a" "x")), true);
        assert_eq!(recognize(&Call(n(l_rec)), &env, &tokens!("a" "x" "x")), true);
        assert_eq!(recognize(&Call(n(l_rec)), &env, &tokens!("a" "x" "x" "x")), true);
        assert_eq!(recognize(&Call(n(l_rec)), &env, &tokens!("a" "a" "x" "x")), false);
        assert_eq!(recognize(&Call(n(l_rec)), &env, &tokens!()), false);
        assert_eq!(recognize(&Call(n(l_rec)), &env, &tokens!("a" "x" "a" "x")), false);
    }
}


#[test]
fn basic_parsing_e() {
    assert_eq!(parse_top(&AnyToken, &tokens!("asdf")), Ok(ast!("asdf")));

    assert_eq!(parse_top(&Anyways(ast!("asdf")), &tokens!()), Ok(ast!("asdf")));

    assert_eq!(parse_top(&Biased(Rc::new(Anyways(ast!("A"))), Rc::new(Anyways(ast!("B")))),
                         &tokens!()),
               Ok(ast!("A")));

    assert_eq!(parse_top(&Named(n("c"), Rc::new(Anyways(ast!("asdf")))), &tokens!()),
               Ok(ast!({- "c" => "asdf"})));


    assert_eq!(parse_top(&Seq(vec![Rc::new(AnyToken)]), &tokens!("asdf")), Ok(ast_shape!("asdf")));

    assert_eq!(parse_top(&Seq(vec![Rc::new(AnyToken), Rc::new(Literal(n("fork"))), Rc::new(AnyToken)]),
               &tokens!("asdf" "fork" "asdf")),
               Ok(ast_shape!("asdf" "fork" "asdf")));

    assert_eq!(parse_top(
        &Seq(vec![Rc::new(Seq(vec![Rc::new(Literal(n("aa"))), Rc::new(Literal(n("ab")))])),
                  Rc::new(Seq(vec![Rc::new(Literal(n("ba"))), Rc::new(Literal(n("bb")))]))]),
               &tokens!("aa" "ab" "ba" "bb")),
               Ok(ast_shape!(("aa" "ab") ("ba" "bb"))));

    parse_top(&Seq(vec![Rc::new(AnyToken), Rc::new(Literal(n("fork"))), Rc::new(AnyToken)]),
          &tokens!("asdf" "knife" "asdf")).unwrap_err();

    assert_eq!(parse_top(&form_pat!([(star (named "c", (alt (lit "X"), (lit "O")))), (lit "!")]),
                         &tokens!("X" "O" "O" "O" "X" "X" "!")).unwrap(),
               ast_shape!({- "c" => ["X", "O", "O", "O", "X", "X"]} "!"));


    assert_eq!(parse_top(&Seq(vec![Rc::new(Star(Rc::new(Named(n("c"), Rc::new(Literal(n("*"))))))),
                                   Rc::new(Literal(n("X")))]),
                     &tokens!("*" "*" "*" "*" "*" "X")),
               Ok(ast_shape!({- "c" => ["*", "*", "*", "*", "*"] } "X")));

    assert_m!(parse_top(&form_pat!([(star (biased (lit "a"), (lit "b"))), (lit "b")]),
                        &tokens!["a" "a" "b"]),
              Ok(_));

    assert_m!(parse_top(&form_pat!([(star (biased (lit "b"), (lit "a"))), (lit "b")]),
                        &tokens!["a" "a" "b"]),
              Ok(_));
}
