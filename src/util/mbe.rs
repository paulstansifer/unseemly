#![macro_use]

// March By Example: a user-friendly way to handle named subterms under Kleene stars,
//  expressed through a special kind of environment.
// This is intended to organize the subterms of an `Ast` node.
// Using this as the evaluation environment of a program is probably interesting,
//  but not necessarily in a good way.
//
//
// The principle, when applied to pattern-based macro definitions, is as follows:
//  Kleene stars in a macro grammar
//    (e.g. `(f=Identifier (arg=Identifier ":" arg_t=Type)*)` )
//   correspond to lists in an AST.
//  The original syntactic structure is irrelevant.
//   but there's only one name (e.g. `arg_t`) for the entire list of matched syntax.
//
// This whole thing nicely generalizes to nesting: we use variable-arity trees instead of lists,
//  resulting in an `EnvMBE` (a March By Example Enviornment)
//
// For getting information *out* of an `EnvMBE`,
//  we provide an operation ("march") that, given a set of names
//    ("driving names", presumably the names "under the `*`")
//   produces `n` environments, in which each of those names has a tree
//    that is shorter by one level.
//
// One problem: what if two of the "driving names" repeat a different numbers of times?
// Traditionally, this is a runtime error,
//  but we'd like it to be a parser error:
//   after all, it's the author of the syntax
//    who has control over how many repetions there are of each thing.
// So, we will let grammars specify when different Kleene stars
//  must repeat the same number of times.
// Violations of this rule are a parse error,
//  and it's only legal to "march" with driving names
//   that were matched (at the current level)
//    (a) under the same `*`, or
//    (b) under `*`s that must repeat the same number of times.
// On the other hand, if the user wants "cross product" behavior,
//  there's no reason that they can't get it.
// We may add a facility to take syntax matched `a`, `b`, `c`... times,
//  and produce `a × b × c` different environments.
//
//
// This is based on Macro By Example, but this implementation isn't strictly about macros,
//  which is why I changed the name!
// The original MBE paper is
//  "Macro-by-example: Deriving syntactic transformations from their specifications"
//   by Kohlbecker and Wand
//   ftp://www.cs.indiana.edu/pub/techreports/TR206.pdf
//
// Many interesting macros can be defined simply
//  by specifying a grammar and a piece of quoted syntax,
//  if the syntax transcription supports MBE.
//  (This corresponds to Scheme's `syntax-rules` and Rust's `macro-rules`.)

// Suppose we want to write code that processes MBE environments.
// Obviously, we can use `march` to pull out all the structure as necessary.
// But pattern-matching is really nice...
//  and sometimes it's nice to abstract over the number of repetitions of something.
//
// So, if you set a particular index is `ddd`, that will be repeated 0 or more times
//  in order to match the length of whatever is on the other side.

use crate::{name::*, util::assoc::Assoc};
use std::{fmt, rc::Rc};

// How on earth can one data structure need so many variations on `map`?
// There's got to be a better way!

/// `EnvMBE` is like an environment,
///  except that some of its contents are "repeats",
///   which represent _n_ different values
///    (or repeats of repeats, etc.).
/// Non-repeated values may be retrieved by `get_leaf`.
/// To access repeated values, one must `march` them,
///  which produces _n_ different environments,
///   in which the marched values are not repeated (or one layer less repeated).
/// Marching multiple repeated values at once
///  is only permitted if they were constructed to repeat the same number of times.
#[derive(Eq, Clone, Default)]
// `Clone` needs to traverse the whole `Vec` ):
pub struct EnvMBE<T: Clone> {
    /// Non-repeated values
    leaves: Assoc<Name, T>,

    /// Outer vec holds distinct repetitions
    ///  (i.e. differently-named, or entirely unnamed repetitions)
    /// Note that some of the entries may be obsolete;
    ///  deletions are marked by putting `None` in the `Assoc`s
    ///   that index into this.
    repeats: Vec<Rc<Vec<EnvMBE<T>>>>,

    /// TODO #18: this is unused; remove it.
    /// Which, if any, index is supposed to match 0 or more repetitions of something?
    /// This should always have the same length as `repeats`.
    /// If this isn't all `None`, then this MBE is presumably some kind of pattern.
    ddd_rep_idxes: Vec<Option<usize>>,

    /// Where in `repeats` to look, if we want to traverse for a particular leaf.
    /// We use `.unwrap_or(None)` when looking up into this
    ///  so we can delete by storing `None`.
    leaf_locations: Assoc<Name, Option<usize>>,

    /// The location in `repeats` that represents a specific repetition name.
    named_repeats: Assoc<Name, Option<usize>>,
}

// `custom_derive!` (or maybe `Reifiable!`) can't handle type bounds, so we need to do this manually
impl<T: Clone + crate::runtime::reify::Reifiable> crate::runtime::reify::Reifiable for EnvMBE<T> {
    fn ty_name() -> Name { n("EnvMBE") }
    fn concrete_arguments() -> Option<Vec<crate::ast::Ast>> { Some(vec![T::ty_invocation()]) }
    fn reify(&self) -> crate::runtime::eval::Value {
        crate::runtime::eval::Value::Sequence(vec![
            Rc::new(self.leaves.reify()),
            Rc::new(self.repeats.reify()),
            Rc::new(self.ddd_rep_idxes.reify()),
            Rc::new(self.leaf_locations.reify()),
            Rc::new(self.named_repeats.reify()),
        ])
    }
    fn reflect(v: &crate::runtime::eval::Value) -> Self {
        extract!((v) crate::runtime::eval::Value::Sequence = (ref parts) => {
            EnvMBE {
               leaves: <Assoc<Name, T>>::reflect(&*parts[0]),
               repeats: <Vec<Rc<Vec<EnvMBE<T>>>>>::reflect(&*parts[1]),
               ddd_rep_idxes: <Vec<Option<usize>>>::reflect(&*parts[2]),
               leaf_locations: <Assoc<Name, Option<usize>>>::reflect(&*parts[3]),
               named_repeats: <Assoc<Name, Option<usize>>>::reflect(&*parts[4])
            }
        })
    }
}

impl<T: PartialEq + Clone> PartialEq for EnvMBE<T> {
    fn eq(&self, other: &EnvMBE<T>) -> bool {
        fn assoc_eq_modulo_none<K: Eq + std::hash::Hash + Clone, V: PartialEq + Clone>(
            lhs: &Assoc<K, Option<V>>,
            rhs: &Assoc<K, Option<V>>,
        ) -> bool {
            for (k, v_maybe) in lhs.iter_pairs() {
                if let Some(ref v) = *v_maybe {
                    if let Some(&Some(ref other_v)) = rhs.find(k) {
                        if !(v == other_v) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
            }

            for (other_k, other_v_maybe) in rhs.iter_pairs() {
                if let Some(ref other_v) = *other_v_maybe {
                    if let Some(&Some(ref v)) = rhs.find(other_k) {
                        if !(v == other_v) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
            }

            true
        }

        // This ought to handle permutations of `repeats`
        // (matched with permutations of the indices in the assocs)
        // but that's hard.

        self.leaves == other.leaves
            && self.repeats == other.repeats
            && self.ddd_rep_idxes == other.ddd_rep_idxes
            && assoc_eq_modulo_none(&self.leaf_locations, &other.leaf_locations)
            && assoc_eq_modulo_none(&self.named_repeats, &other.named_repeats)
    }
}

impl<T: Clone + fmt::Debug> fmt::Debug for EnvMBE<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.leaves.empty() && self.repeats.is_empty() {
            write!(f, "mbe∅")
        } else {
            write!(f, "{{ 🍂 {:#?}, ✶", self.leaves)?;
            let mut first = true;
            for (i, rep) in self.repeats.iter().enumerate() {
                if !first {
                    write!(f, ", ")?;
                }
                first = false;

                // is it a named repeat?
                for (name, idx_maybe) in self.named_repeats.iter_pairs() {
                    if let Some(idx) = *idx_maybe {
                        if idx == i {
                            write!(f, "⋯({:#?})⋯ ", name)?;
                        }
                    }
                }
                write!(f, "{:#?}", rep)?;
            }
            write!(f, "}}")
        }
    }
}

/// TODO #18: This is unused; remove it
/// An iterator that expands a dotdotdot a certain number of times.
struct DddIter<'a, S: 'a> {
    underlying: std::slice::Iter<'a, S>,
    cur_idx: usize,
    rep_idx: usize,
    repeated: Option<&'a S>,
    extra_needed: usize,
}

impl<'a, S: Clone> DddIter<'a, S> {
    fn new(und: std::slice::Iter<'a, S>, rep_idx: usize, extra: usize) -> DddIter<'a, S> {
        DddIter {
            underlying: und,
            cur_idx: 0,
            rep_idx: rep_idx,
            repeated: None,
            extra_needed: extra,
        }
    }
}

impl<'a, S: Clone> Iterator for DddIter<'a, S> {
    type Item = &'a S;
    fn next(&mut self) -> Option<&'a S> {
        let cur_idx = self.cur_idx;
        self.cur_idx += 1;

        if cur_idx == self.rep_idx {
            self.repeated = self.underlying.next();
        }

        if cur_idx >= self.rep_idx && cur_idx < self.rep_idx + self.extra_needed {
            self.repeated
        } else {
            self.underlying.next()
        }
    }
}

impl<T: Clone> EnvMBE<T> {
    pub fn new() -> EnvMBE<T> {
        EnvMBE {
            leaves: Assoc::new(),
            repeats: vec![],
            ddd_rep_idxes: vec![],
            leaf_locations: Assoc::new(),
            named_repeats: Assoc::new(),
        }
    }

    /// Creates an `EnvMBE` without any repetition
    pub fn new_from_leaves(l: Assoc<Name, T>) -> EnvMBE<T> {
        EnvMBE {
            leaves: l,
            repeats: vec![],
            ddd_rep_idxes: vec![],
            leaf_locations: Assoc::new(),
            named_repeats: Assoc::new(),
        }
    }

    /// Creates an `EnvMBE` containing a single anonymous repeat
    pub fn new_from_anon_repeat(r: Vec<EnvMBE<T>>) -> EnvMBE<T> {
        EnvMBE::new_from_anon_repeat_ddd(r, None)
    }

    /// Creates an `EnvMBE` containing a single anonymous repeat
    pub fn new_from_anon_repeat_ddd(r: Vec<EnvMBE<T>>, ddd_idx: Option<usize>) -> EnvMBE<T> {
        let mut res = EnvMBE::new();
        res.add_anon_repeat(r, ddd_idx);
        res
    }

    /// Creates an `EnvMBE` containing a single named repeat
    pub fn new_from_named_repeat(n: Name, r: Vec<EnvMBE<T>>) -> EnvMBE<T> {
        let mut res = EnvMBE::new();
        res.add_named_repeat(n, r, None);
        res
    }

    /// Combine two `EnvMBE`s whose names (both environment names and repeat names) are disjoint,
    /// or just overwrite the contents of the previous one.
    /// This should maybe not be `pub` if we can avoid it.
    /// Note: ideally, the larger one should be on the LHS.
    pub fn combine_overriding(&self, rhs: &EnvMBE<T>) -> EnvMBE<T> {
        let adjust_rhs_by = self.repeats.len();

        let mut new_repeats = self.repeats.clone();
        new_repeats.append(&mut rhs.repeats.clone());

        let mut new__ddd_rep_idxes = self.ddd_rep_idxes.clone();
        new__ddd_rep_idxes.append(&mut rhs.ddd_rep_idxes.clone());

        EnvMBE {
            leaves: self.leaves.set_assoc(&rhs.leaves),
            repeats: new_repeats,
            ddd_rep_idxes: new__ddd_rep_idxes,
            leaf_locations: self.leaf_locations.set_assoc(
                &rhs.leaf_locations.map(|idx_opt| idx_opt.map(|idx| idx + adjust_rhs_by)),
            ),
            named_repeats: self.named_repeats.set_assoc(
                &rhs.named_repeats.map(|idx_opt| idx_opt.map(|idx| idx + adjust_rhs_by)),
            ),
        }
    }

    /// Combine two `EnvMBE`s whose leaves should be disjoint, but which can contain
    /// named repeats with the same name. This should make sense for combining the results of
    /// matching two different chunks of a patern.
    pub fn merge(&self, rhs: &EnvMBE<T>) -> EnvMBE<T> {
        let mut res = self.clone();

        let mut rhs_idx_is_named: Vec<bool> = rhs.repeats.iter().map(|_| false).collect();

        // This could be made more efficient by just reusing the `Rc`s instead of cloning the
        // arrays, but that would require reworking the interface.

        for (n, rep_idx) in rhs.named_repeats.iter_pairs() {
            if let Some(rep_idx) = *rep_idx {
                res.add_named_repeat(
                    *n,
                    (*rhs.repeats[rep_idx]).clone(),
                    rhs.ddd_rep_idxes[rep_idx],
                );
                rhs_idx_is_named[rep_idx] = true;
            }
        }

        for (idx, (rep, ddd_rep_idx)) in
            rhs.repeats.iter().zip(rhs.ddd_rep_idxes.iter()).enumerate()
        {
            if !rhs_idx_is_named[idx] {
                res.add_anon_repeat((**rep).clone(), *ddd_rep_idx);
            }
        }

        res.leaves = res.leaves.set_assoc(&rhs.leaves);

        res
    }

    /// Given `driving_names`, marches the whole set of names that can march with them.
    /// (Adding an additional name to `driving_names` will result in the same behavior,
    ///  or a panic, in the case that the new name can't be marched with the existing ones.)
    ///
    /// This takes a `Vec` of `Name` instead of just one because a particular name might
    /// not be transcribed at all here, and thus can't tell us how to repeat.
    pub fn march_all(&self, driving_names: &[Name]) -> Vec<EnvMBE<T>> {
        let mut march_loc: Option<(usize, Name)> = None;

        for &n in driving_names {
            match (march_loc, self.leaf_locations.find(&n).unwrap_or(&None)) {
                (_, &None) => {}
                (None, &Some(loc)) => march_loc = Some((loc, n)),
                (Some((old_loc, old_name)), &Some(new_loc)) => {
                    if old_loc != new_loc {
                        panic!(
                            "{:#?} and {:#?} cannot march together; they weren't matched to have \
                             the same number of repeats",
                            old_name, n
                        );
                    }
                }
            }
        }

        let march_loc = match march_loc {
            None => {
                return vec![];
            } // FOOTGUN: assume that it is repeated zero times
            Some((loc, _)) => loc,
        };

        let mut result = vec![];
        for marched_out in self.repeats[march_loc].iter() {
            // TODO: should we allow cross-product marching by keeping around unused repeats?
            // Don't lose the current leaves:
            result
                .push(EnvMBE::new_from_leaves(self.leaves.clone()).combine_overriding(marched_out));
        }

        result
    }

    /// Get a non-repeated thing in the enviornment
    pub fn get_leaf(&self, n: Name) -> Option<&T> { self.leaves.find(&n) }

    pub fn get_rep_leaf(&self, n: Name) -> Option<Vec<&T>> {
        // FOOTGUN: can't distinguish wrong leaf names from 0-repeated leaves
        // TODO: remove get_rep_leaf_or_panic, as this never returns `None`

        let mut res = vec![];
        let leaf_loc = match self.leaf_locations.find(&n) {
            Some(&Some(ll)) => ll,
            _ => {
                return Some(vec![]);
            }
        };

        for r in &*self.repeats[leaf_loc] {
            match r.get_leaf(n) {
                Some(leaf) => res.push(leaf),
                None => {
                    return Some(vec![]);
                } // `march` can leave us with dead leaf_locations
            }
        }
        Some(res)
    }

    /// Extend with a non-repeated thing
    pub fn add_leaf(&mut self, n: Name, v: T) { self.leaves = self.leaves.set(n, v); }

    pub fn add_named_repeat(&mut self, n: Name, sub: Vec<EnvMBE<T>>, sub_ddd_idx: Option<usize>) {
        if sub.is_empty() {
            return;
        } // no-op-ish, but keep the repeats clean (good for `eq`)

        match *self.named_repeats.find(&n).unwrap_or(&None) {
            None => {
                let new_index = self.repeats.len();
                self.update_leaf_locs(new_index, &sub);

                self.repeats.push(Rc::new(sub));
                self.ddd_rep_idxes.push(sub_ddd_idx);
                self.named_repeats = self.named_repeats.set(n, Some(new_index));
            }
            Some(idx) => {
                if self.repeats[idx].len() != sub.len() {
                    panic!(
                        "Named repetition {:#?} is repeated {:#?} times in one place, {:#?} times \
                         in another.",
                        n,
                        self.repeats[idx].len(),
                        sub.len()
                    )
                }

                self.update_leaf_locs(idx, &sub);

                let mut new_repeats_at_idx = vec![];
                for pairs in self.repeats[idx].iter().zip(sub.iter()) {
                    new_repeats_at_idx.push(pairs.0.combine_overriding(pairs.1));
                }
                self.repeats[idx] = Rc::new(new_repeats_at_idx);
                if self.ddd_rep_idxes[idx] != sub_ddd_idx {
                    // Maybe we should support this usecase!
                    panic!(
                        "Named repetition {:#?} has mismatched ddd rep indices {:#?} and {:#?}.",
                        n, self.ddd_rep_idxes[idx], sub_ddd_idx
                    );
                }
            }
        }
    }

    pub fn add_anon_repeat(&mut self, sub: Vec<EnvMBE<T>>, sub_ddd_idx: Option<usize>) {
        if sub.is_empty() {
            return;
        } // no-op-ish, but keep the repeats clean (good for `eq`)

        let new_index = self.repeats.len();
        self.update_leaf_locs(new_index, &sub);

        self.repeats.push(Rc::new(sub));
        self.ddd_rep_idxes.push(sub_ddd_idx);
    }

    pub fn anonimize_repeat(&mut self, n: Name) {
        // Now you can't find me!
        self.named_repeats = self.named_repeats.set(n, None);
    }

    pub fn map<NewT: Clone, F>(&self, f: &mut F) -> EnvMBE<NewT>
    where F: FnMut(&T) -> NewT {
        self.named_map(&mut |_n, elt| f(elt))
    }

    /// Map, but march the `ctxt` along with the structure of `self`
    pub fn map_marched_against<NewT: Clone, Mode: crate::walk_mode::WalkMode, F>(
        &self,
        f: &mut F,
        ctxt: &crate::ast_walk::LazyWalkReses<Mode>,
    ) -> EnvMBE<NewT>
    where
        F: FnMut(&T, &crate::ast_walk::LazyWalkReses<Mode>) -> NewT,
    {
        EnvMBE {
            leaves: self.leaves.map_borrow_f(&mut |t: &T| f(t, ctxt)),
            repeats: self
                .repeats
                .iter()
                .enumerate()
                .map(|(rpt_idx, rc_vec_mbe): (usize, &Rc<Vec<EnvMBE<T>>>)| {
                    let this_rpt_name = self.leaf_locations.find_value(&Some(rpt_idx)).unwrap();
                    let marched_ctxts = ctxt.march_all(&[*this_rpt_name]);
                    Rc::new(
                        rc_vec_mbe
                            .iter()
                            .zip(marched_ctxts)
                            .map(
                                |(mbe, marched_ctxt): (
                                    &EnvMBE<T>,
                                    crate::ast_walk::LazyWalkReses<Mode>,
                                )| {
                                    mbe.map_marched_against(f, &marched_ctxt)
                                },
                            )
                            .collect(),
                    )
                })
                .collect(),
            ddd_rep_idxes: self.ddd_rep_idxes.clone(),
            leaf_locations: self.leaf_locations.clone(),
            named_repeats: self.named_repeats.clone(),
        }
    }

    pub fn named_map<NewT: Clone, F>(&self, f: &mut F) -> EnvMBE<NewT>
    where F: FnMut(&Name, &T) -> NewT {
        EnvMBE {
            leaves: self.leaves.keyed_map_borrow_f(f),
            repeats: self
                .repeats
                .iter()
                .map(|rc_vec_mbe: &Rc<Vec<EnvMBE<T>>>| {
                    Rc::new(rc_vec_mbe.iter().map(|mbe: &EnvMBE<T>| mbe.named_map(f)).collect())
                })
                .collect(),
            ddd_rep_idxes: self.ddd_rep_idxes.clone(),
            leaf_locations: self.leaf_locations.clone(),
            named_repeats: self.named_repeats.clone(),
        }
    }

    pub fn map_reduce<NewT: Clone>(
        &self,
        f: &dyn Fn(&T) -> NewT,
        red: &dyn Fn(&NewT, &NewT) -> NewT,
        base: NewT,
    ) -> NewT {
        let reduced: NewT = self.leaves.map(f).reduce(&|_k, v, res| red(v, &res), base);

        self.repeats.iter().fold(reduced, |base: NewT, rc_vec_mbe: &Rc<Vec<EnvMBE<T>>>| {
            rc_vec_mbe.iter().fold(base, |base: NewT, mbe: &EnvMBE<T>| mbe.map_reduce(f, red, base))
        })
    }

    /// Provide the map function with the name of the current leaf,
    /// and the appropriately-marched context element
    pub fn marched_map<NewT: Clone, F>(&self, f: &mut F) -> EnvMBE<NewT>
    where F: FnMut(Name, &EnvMBE<T>, &T) -> NewT {
        self.marched_map_rec(self, f)
    }

    fn marched_map_rec<NewT: Clone, F>(&self, outer: &EnvMBE<T>, f: &mut F) -> EnvMBE<NewT>
    where F: FnMut(Name, &EnvMBE<T>, &T) -> NewT {
        let local_mbe = outer.combine_overriding(self);

        let new_leaves =
            self.leaves.keyed_map_borrow_f(&mut |n: &Name, elt: &T| f(*n, &local_mbe, elt));
        EnvMBE {
            leaves: new_leaves,
            repeats: self
                .repeats
                .iter()
                .map(|rc_vec_mbe: &Rc<Vec<EnvMBE<T>>>| {
                    Rc::new(
                        rc_vec_mbe
                            .iter()
                            .map(|marched_out: &EnvMBE<T>| marched_out.marched_map_rec(outer, f))
                            .collect(),
                    )
                })
                .collect(),
            ddd_rep_idxes: self.ddd_rep_idxes.clone(),
            leaf_locations: self.leaf_locations.clone(),
            named_repeats: self.named_repeats.clone(),
        }
    }

    /// TODO #18: this is unused; remove it
    /// Duplicate contents of the side with a DDD to line it up with the other
    // TODO: this needs to return `Option` (and so does everything `_with`)
    // TODO: for efficiency, this ought to return iterators
    fn resolve_ddd<'a, S: Clone>(
        lhs: &'a Rc<Vec<EnvMBE<T>>>,
        lhs_ddd: &'a Option<usize>,
        rhs: &'a Rc<Vec<EnvMBE<S>>>,
        rhs_ddd: &'a Option<usize>,
    ) -> Vec<(&'a EnvMBE<T>, &'a EnvMBE<S>)> {
        let len_diff = lhs.len() as i32 - (rhs.len() as i32);

        let matched: Vec<(&EnvMBE<T>, &EnvMBE<S>)> = match (lhs_ddd, rhs_ddd) {
            (&None, &None) => {
                if len_diff != 0 {
                    panic!("mismatched MBE lengths")
                }
                lhs.iter().zip(rhs.iter()).collect()
            }
            (&Some(ddd_idx), &None) => {
                if len_diff - 1 > 0 {
                    panic!("abstract MBE LHS too long")
                }
                DddIter::new(lhs.iter(), ddd_idx, -(len_diff - 1) as usize)
                    .zip(rhs.iter())
                    .collect()
            }
            (&None, &Some(ddd_idx)) => {
                if len_diff + 1 < 0 {
                    panic!("abstract MBE RHS too long")
                }
                lhs.iter().zip(DddIter::new(rhs.iter(), ddd_idx, (len_diff + 1) as usize)).collect()
            }
            (&Some(_), &Some(_)) => panic!("repetition on both sides"),
        };

        matched
    }

    // The LHS must be the side with the DDD.
    // TODO: try just using `reduced` instead of `base.clone()`
    // TODO #15: `Result` instead of panicing
    fn match_collapse_ddd<'a, S: Clone, NewT: Clone>(
        lhs: &'a Rc<Vec<EnvMBE<T>>>,
        lhs_ddd: &'a Option<usize>,
        rhs: &'a Rc<Vec<EnvMBE<S>>>,
        rhs_ddd: &'a Option<usize>,
        f: &dyn Fn(&T, &S) -> NewT,
        col: &dyn Fn(Vec<NewT>) -> NewT,
        red: &dyn Fn(NewT, NewT) -> NewT,
        base: NewT,
    ) -> NewT {
        let len_diff = lhs.len() as i32 - (rhs.len() as i32);

        // The RHS can have a DDD if it's exactly the same (subtyping only goes the one way)
        // TODO: if the user is rebuilding MBEs using `map_collapse_reduce_with`, they'll lose
        // the DDDs they should keep; how do we get that information back in? (I assume we pass
        // a bool to one of the function arguments.)
        if rhs_ddd.is_some() && lhs_ddd != rhs_ddd {
            panic!("RHS must match LHS exactly if it uses DDD")
        }

        let mut reduced = base.clone();
        // Unpack the DDD ... unless the RHS is a DDD also.
        if let (&Some(ddd_idx), false) = (lhs_ddd, rhs_ddd.is_some()) {
            if len_diff - 1 > 0 {
                panic!("abstract MBE LHS too long")
            }

            for i in 0..ddd_idx {
                reduced = red(
                    reduced,
                    lhs[i].map_collapse_reduce_with(&rhs[i], f, col, red, base.clone()),
                );
            }

            let mut ddd_rep = vec![];
            for rep in 0..((1 - len_diff) as usize) {
                ddd_rep.push(lhs[ddd_idx].map_collapse_reduce_with(
                    &rhs[ddd_idx + rep],
                    f,
                    col,
                    red,
                    base.clone(),
                ));
            }
            reduced = red(reduced, col(ddd_rep));

            for i in (ddd_idx + 1)..lhs.len() {
                let rhs_i = (i as i32 - len_diff) as usize;

                reduced = red(
                    reduced,
                    lhs[i].map_collapse_reduce_with(&rhs[rhs_i], f, col, red, base.clone()),
                );
            }
        } else {
            if len_diff != 0 {
                panic!("mismatched MBE lengths {} vs. {}", lhs.len(), rhs.len())
            }
            for i in 0..lhs.len() {
                reduced = red(
                    reduced,
                    lhs[i].map_collapse_reduce_with(&rhs[i], f, col, red, base.clone()),
                );
            }
        }
        reduced
    }

    // TODO: we should just have the relevant functions return None...
    pub fn can_map_with(&self, o: &EnvMBE<T>) -> bool {
        let mut lhs_keys = std::collections::HashSet::<Name>::new();
        for (k, _) in self.leaves.iter_pairs() {
            lhs_keys.insert(*k);
        }
        let mut rhs_keys = std::collections::HashSet::<Name>::new();
        for (k, _) in o.leaves.iter_pairs() {
            rhs_keys.insert(*k);
        }

        if lhs_keys != rhs_keys {
            return false;
        }

        for ((subs, subs_ddd), (o_subs, o_subs_ddd)) in self
            .repeats
            .iter()
            .zip(self.ddd_rep_idxes.iter())
            .zip(o.repeats.iter().zip(o.ddd_rep_idxes.iter()))
        {
            if subs_ddd != &None && o_subs_ddd != &None {
                panic!("Ill-formed; can't walk two DDDs")
            }
            if subs_ddd == &None && o_subs_ddd == &None && subs.len() != o_subs.len() {
                return false;
            }
            if subs_ddd != &None && o_subs.len() < subs.len() - 1 {
                return false;
            }
            if o_subs_ddd != &None && subs.len() < o_subs.len() - 1 {
                return false;
            }

            for (mbe, o_mbe) in Self::resolve_ddd(subs, subs_ddd, o_subs, o_subs_ddd) {
                if !mbe.can_map_with(o_mbe) {
                    return false;
                }
            }
        }

        true
    }

    pub fn map_with<S: Clone, NewT: Clone>(
        &self,
        o: &EnvMBE<S>,
        f: &dyn Fn(&T, &S) -> NewT,
    ) -> EnvMBE<NewT> {
        self.named_map_with(o, &|_name, l, r| f(l, r))
    }

    pub fn named_map_with<S: Clone, NewT: Clone>(
        &self,
        o: &EnvMBE<S>,
        f: &dyn Fn(&Name, &T, &S) -> NewT,
    ) -> EnvMBE<NewT> {
        EnvMBE {
            leaves: self.leaves.keyed_map_with(&o.leaves, f),

            // This assumes that "equivalent" repeats have the same indices... ) :
            repeats: self
                .repeats
                .iter()
                .zip(self.ddd_rep_idxes.iter())
                .zip(o.repeats.iter().zip(o.ddd_rep_idxes.iter()))
                .map(&|((rc_vec_mbe, ddd_idx), (o_rc_vec_mbe, o_ddd_idx)): (
                    (&Rc<Vec<EnvMBE<T>>>, &Option<usize>),
                    (&Rc<Vec<EnvMBE<S>>>, &Option<usize>),
                )| {
                    let mapped: Vec<_> =
                        Self::resolve_ddd(rc_vec_mbe, ddd_idx, o_rc_vec_mbe, o_ddd_idx)
                            .iter()
                            .map(|&(mbe, o_mbe): &(&EnvMBE<T>, &EnvMBE<S>)| {
                                mbe.named_map_with(o_mbe, f)
                            })
                            .collect();

                    Rc::new(mapped)
                })
                .collect(),
            ddd_rep_idxes: self.repeats.iter().map(|_| None).collect(), // remove all dotdotdots
            leaf_locations: self.leaf_locations.clone(),
            named_repeats: self.named_repeats.clone(),
        }
    }

    pub fn map_reduce_with<NewT: Clone>(
        &self,
        other: &EnvMBE<T>,
        f: &dyn Fn(&T, &T) -> NewT,
        red: &dyn Fn(&NewT, &NewT) -> NewT,
        base: NewT,
    ) -> NewT {
        // TODO #15: this panics all over the place if anything goes wrong
        let mut reduced: NewT =
            self.leaves.map_with(&other.leaves, f).reduce(&|_k, v, res| red(v, &res), base);

        let mut already_processed: Vec<bool> = self.repeats.iter().map(|_| false).collect();

        for (leaf_name, self_idx) in self.leaf_locations.iter_pairs() {
            let self_idx = match *self_idx {
                Some(si) => si,
                None => {
                    continue;
                }
            };
            if already_processed[self_idx] {
                continue;
            }
            already_processed[self_idx] = true;

            let other_idx = other.leaf_locations.find_or_panic(leaf_name).unwrap();

            let matched = Self::resolve_ddd(
                &self.repeats[self_idx],
                &self.ddd_rep_idxes[self_idx],
                &other.repeats[other_idx],
                &other.ddd_rep_idxes[other_idx],
            );

            for (self_elt, other_elt) in matched {
                reduced = self_elt.map_reduce_with(other_elt, f, &red, reduced);
            }
        }

        reduced
    }

    // TODO: test this more.
    pub fn map_collapse_reduce_with<S: Clone, NewT: Clone>(
        &self,
        other: &EnvMBE<S>,
        f: &dyn Fn(&T, &S) -> NewT,
        col: &dyn Fn(Vec<NewT>) -> NewT,
        red: &dyn Fn(NewT, NewT) -> NewT,
        base: NewT,
    ) -> NewT {
        // TODO #15: this panics all over the place if anything goes wrong
        let mut reduced: NewT =
            self.leaves.map_with(&other.leaves, f).reduce(&|_k, v, res| red(v.clone(), res), base);

        let mut already_processed: Vec<bool> = self.repeats.iter().map(|_| false).collect();

        for (leaf_name, self_idx) in self.leaf_locations.iter_pairs() {
            let self_idx = match *self_idx {
                Some(si) => si,
                None => {
                    continue;
                }
            };
            if already_processed[self_idx] {
                continue;
            }
            already_processed[self_idx] = true;

            let other_idx = other.leaf_locations.find_or_panic(leaf_name).unwrap();

            reduced = Self::match_collapse_ddd(
                &self.repeats[self_idx],
                &self.ddd_rep_idxes[self_idx],
                &other.repeats[other_idx],
                &other.ddd_rep_idxes[other_idx],
                f,
                col,
                red,
                reduced,
            );
        }

        reduced
    }

    fn update_leaf_locs(&mut self, idx: usize, sub: &[EnvMBE<T>]) {
        let mut already_placed_leaves = std::collections::HashSet::<Name>::new();
        let mut already_placed_repeats = std::collections::HashSet::<Name>::new();

        for sub_mbe in sub {
            for leaf_name in sub_mbe.leaf_locations.iter_keys().chain(sub_mbe.leaves.iter_keys()) {
                if !already_placed_leaves.contains(leaf_name) {
                    self.leaf_locations = self.leaf_locations.set(*leaf_name, Some(idx));
                    already_placed_leaves.insert(*leaf_name);
                }
            }
            for repeat_name in sub_mbe.named_repeats.iter_keys() {
                if !already_placed_repeats.contains(repeat_name) {
                    self.named_repeats = self.named_repeats.set(*repeat_name, Some(idx));
                    already_placed_repeats.insert(*repeat_name);
                }
            }
        }
    }

    // If `f` turns a leaf into a `Vec`, splice those results in
    pub fn heal_splices<E>(
        &mut self,
        f: &dyn Fn(&T) -> Result<Option<Vec<T>>, E>,
    ) -> Result<(), E> {
        for repeat in &mut self.repeats {
            let mut cur_repeat: Vec<EnvMBE<T>> = (**repeat).clone();
            let mut i = 0;
            while i < cur_repeat.len() {
                cur_repeat[i].heal_splices(f)?;

                let mut splices = vec![];
                {
                    let n_and_vals = cur_repeat[i].leaves.iter_pairs();
                    for (n, val) in n_and_vals {
                        if let Some(splice) = f(val)? {
                            splices.push((*n, splice));
                        }
                    }
                }

                if !splices.is_empty() {
                    let mut template = cur_repeat.remove(i);

                    // TODO: each of the splices better be the same length.
                    // I don't know what has to go wrong to violate that rule.
                    for rep in 0..splices[0].1.len() {
                        for splice in &splices {
                            template.add_leaf(splice.0, splice.1[rep].clone());
                        }
                        cur_repeat.insert(i + rep, template.clone())
                    }
                    i += splices[0].1.len();
                } else {
                    i += 1;
                }
            }
            *repeat = Rc::new(cur_repeat)
        }
        Ok(())
    }

    // TODO: this should return a usable error
    pub fn heal_splices__with<E, S: Clone>(
        &mut self,
        other: &EnvMBE<S>,
        f: &dyn Fn(&T, &dyn Fn() -> Vec<S>) -> Result<Option<Vec<T>>, E>,
    ) -> Result<(), E>
    where
        T: std::fmt::Debug,
    {
        for repeat in &mut self.repeats {
            // Find the same repeat in `other`:
            let mut names_needed = vec![];
            for (name, _) in self.leaf_locations.iter_pairs() {
                names_needed.push(name);
            }
            let other__rep_loc = match other.leaf_locations.find(names_needed[0]) {
                Some(Some(l)) => *l,
                _ => {
                    return Ok(()); // Should become a mismatch error elsewhere (TODO: make an `E`)
                }
            };

            let other__cur_repeat: &Vec<EnvMBE<S>> = &*other.repeats[other__rep_loc];
            let mut cur_repeat: Vec<EnvMBE<T>> = (**repeat).clone();

            // If an item splices, how wide does the other side need to be
            //  in order to make everything line up?
            let splice_length =
                (other__cur_repeat.len() + 1).checked_sub(cur_repeat.len()).unwrap();

            let mut i = 0;
            let mut other_i = 0;
            while i < cur_repeat.len() && other_i < other__cur_repeat.len() {
                cur_repeat[i].heal_splices__with(&other__cur_repeat[other_i], f)?;

                let mut splices = vec![];
                {
                    let n_and_vals = cur_repeat[i].leaves.iter_pairs();
                    for (n, val) in n_and_vals {
                        let concrete_splice__thunk = || {
                            let mut result = vec![];
                            for other_i in other__cur_repeat.iter().skip(i).take(splice_length) {
                                result.push(other_i.leaves.find_or_panic(n).clone())
                            }
                            result
                        };

                        if let Some(splice) = f(val, &concrete_splice__thunk)? {
                            splices.push((*n, splice));
                        }
                    }
                }

                if !splices.is_empty() {
                    let mut template = cur_repeat.remove(i);

                    // TODO: each of the splices better be the same length.
                    // I don't know what has to go wrong to violate that rule.
                    for rep in 0..splices[0].1.len() {
                        for splice in &splices {
                            template.add_leaf(splice.0, splice.1[rep].clone());
                        }
                        cur_repeat.insert(i + rep, template.clone())
                    }
                    i += splice_length;
                    other_i += splice_length;
                } else {
                    i += 1;
                    other_i += 1;
                }
            }
            // The lengths might not line up, but that doesn't mean matching will fail!
            // struct {a : Int b : Nat}  <:  struct {a : Int b : Nat c : Float}

            *repeat = Rc::new(cur_repeat)
        }
        Ok(())
    }
}

impl<T: Clone, E: Clone> EnvMBE<Result<T, E>> {
    // Is `lift` the right term?
    pub fn lift_result(&self) -> Result<EnvMBE<T>, E> {
        // There's probably a nice and elegant way to do this with Result::from_iter, but not today
        let mut leaves: Assoc<Name, T> = Assoc::new();
        for (k, v) in self.leaves.iter_pairs() {
            leaves = leaves.set(*k, (*v).clone()?);
        }

        let mut repeats = vec![];
        for rep in &self.repeats {
            let mut items = vec![];
            for item in &**rep {
                items.push(item.lift_result()?);
            }
            repeats.push(Rc::new(items));
        }

        Ok(EnvMBE {
            leaves: leaves,
            repeats: repeats,
            ddd_rep_idxes: self.ddd_rep_idxes.clone(),
            leaf_locations: self.leaf_locations.clone(),
            named_repeats: self.named_repeats.clone(),
        })
    }
}

impl<T: Clone + fmt::Debug> EnvMBE<T> {
    // TODO: this should just take `Name`, not `&Name`
    pub fn get_leaf_or_panic(&self, n: &Name) -> &T {
        match self.leaves.find(n) {
            Some(v) => v,
            None => panic!(" {:#?} not found in {:#?} (perhaps it is still repeated?)", n, self),
        }
    }

    pub fn get_rep_leaf_or_panic(&self, n: Name) -> Vec<&T> { self.get_rep_leaf(n).unwrap() }

    pub fn map_flatten_rep_leaf_or_panic<S>(
        &self,
        n: Name,
        depth: u8,
        m: &dyn Fn(&T) -> S,
        f: &dyn Fn(Vec<S>) -> S,
    ) -> S {
        if depth == 0 {
            return m(self.get_leaf_or_panic(&n));
        }
        let leaf_loc = match self.leaf_locations.find(&n) {
            Some(&Some(ll)) => ll,
            _ => panic!("Leaf {} not found", n),
        };

        f(self.repeats[leaf_loc]
            .iter()
            .map(|mbe| mbe.map_flatten_rep_leaf_or_panic(n, depth - 1, m, f))
            .collect())
    }
}

#[test]
fn basic_mbe() {
    let mut mbe = EnvMBE::new();
    mbe.add_leaf(n("eight"), 8 as i32);
    mbe.add_leaf(n("nine"), 9);

    assert!(mbe != EnvMBE::new());
    assert!(EnvMBE::new() != mbe);

    let teens_mbe = vec![
        EnvMBE::new_from_leaves(assoc_n!("t" => 11)),
        EnvMBE::new_from_leaves(assoc_n!("t" => 12)),
        EnvMBE::new_from_leaves(assoc_n!("t" => 13)),
    ];

    mbe.add_named_repeat(n("low_two_digits"), teens_mbe.clone(), None);

    let big_mbe = vec![
        EnvMBE::new_from_leaves(assoc_n!("y" => 9001)),
        EnvMBE::new_from_leaves(assoc_n!("y" => 9002)),
    ];

    mbe.add_anon_repeat(big_mbe, None);

    for (sub_mbe, teen) in mbe.march_all(&vec![n("t"), n("eight")]).iter().zip(vec![11, 12, 13]) {
        assert_eq!(sub_mbe.get_leaf(n("eight")), Some(&8));
        assert_eq!(sub_mbe.get_leaf(n("nine")), Some(&9));
        assert_eq!(sub_mbe.get_leaf(n("t")), Some(&teen));
        assert_eq!(sub_mbe.get_leaf(n("y")), None);

        for (sub_sub_mbe, big) in
            sub_mbe.march_all(&vec![n("y"), n("eight")]).iter().zip(vec![9001, 9002])
        {
            assert_eq!(sub_sub_mbe.get_leaf(n("eight")), Some(&8));
            assert_eq!(sub_sub_mbe.get_leaf(n("nine")), Some(&9));
            assert_eq!(sub_sub_mbe.get_leaf(n("t")), Some(&teen));
            assert_eq!(sub_sub_mbe.get_leaf(n("y")), Some(&big));
        }
    }

    let neg_teens_mbe = vec![
        EnvMBE::new_from_leaves(assoc_n!("nt" => -11)),
        EnvMBE::new_from_leaves(assoc_n!("nt" => -12)),
        EnvMBE::new_from_leaves(assoc_n!("nt" => -13)),
    ];

    mbe.add_named_repeat(n("low_two_digits"), neg_teens_mbe, None);

    for (sub_mbe, teen) in
        mbe.march_all(&vec![n("t"), n("nt"), n("eight")]).iter().zip(vec![11, 12, 13])
    {
        assert_eq!(sub_mbe.get_leaf(n("eight")), Some(&8));
        assert_eq!(sub_mbe.get_leaf(n("nine")), Some(&9));
        assert_eq!(sub_mbe.get_leaf(n("t")), Some(&teen));
        assert_eq!(sub_mbe.get_leaf(n("nt")), Some(&-teen));

        for (sub_sub_mbe, big) in
            sub_mbe.march_all(&vec![n("y"), n("eight")]).iter().zip(vec![9001, 9002])
        {
            assert_eq!(sub_sub_mbe.get_leaf(n("eight")), Some(&8));
            assert_eq!(sub_sub_mbe.get_leaf(n("nine")), Some(&9));
            assert_eq!(sub_sub_mbe.get_leaf(n("t")), Some(&teen));
            assert_eq!(sub_sub_mbe.get_leaf(n("nt")), Some(&-teen));
            assert_eq!(sub_sub_mbe.get_leaf(n("y")), Some(&big));
        }
    }

    let all_zeroes = mbe.map_with(&mbe, &|a, b| a - b);
    for sub_mbe in all_zeroes.march_all(&vec![n("t"), n("nt"), n("eight")]) {
        assert_eq!(sub_mbe.get_leaf(n("eight")), Some(&0));
        assert_eq!(sub_mbe.get_leaf(n("nine")), Some(&0));
        assert_eq!(sub_mbe.get_leaf(n("t")), Some(&0));
        assert_eq!(sub_mbe.get_leaf(n("nt")), Some(&0));

        for (sub_sub_mbe, _) in
            sub_mbe.march_all(&vec![n("y"), n("eight")]).iter().zip(vec![9001, 9002])
        {
            assert_eq!(sub_sub_mbe.get_leaf(n("eight")), Some(&0));
            assert_eq!(sub_sub_mbe.get_leaf(n("nine")), Some(&0));
            assert_eq!(sub_sub_mbe.get_leaf(n("t")), Some(&0));
            assert_eq!(sub_sub_mbe.get_leaf(n("nt")), Some(&0));
            assert_eq!(sub_sub_mbe.get_leaf(n("y")), Some(&0));
        }
    }

    assert_eq!(mbe, mbe);
    assert!(mbe != mbe.map(&mut |x| x - 1));
    assert_eq!(mbe, mbe.map(&mut |x| x - 0));
    assert!(mbe != EnvMBE::new());
    assert!(EnvMBE::new() != mbe);

    assert_eq!(mbe, mbe.map_with(&all_zeroes, &|a, b| a + b));
    assert_eq!(mbe, all_zeroes.map_with(&mbe, &|a, b| a + b));

    assert_eq!(
        mbe.map_reduce_with(
            &all_zeroes,
            &|a, b| if *a < *b { *a } else { *b },
            &|a, b| (*a + *b),
            0
        ),
        -11 + -12 + -13
    );

    assert_eq!(
        Err(()),
        mbe.clone().map(&mut |x: &i32| if *x == 12 { Err(()) } else { Ok(*x) }).lift_result()
    );
    assert_eq!(
        Ok(mbe.clone()),
        mbe.clone().map(&mut |x: &i32| if *x == 121212 { Err(()) } else { Ok(*x) }).lift_result()
    );

    let mapped_mbe = mbe.map(&mut |x: &i32| (*x, *x - 9000));

    let first_sub_mbe = &mapped_mbe.march_all(&vec![n("y")])[0];

    assert_eq!(first_sub_mbe.get_leaf(n("y")), Some(&(9001, 1)));
    assert_eq!(first_sub_mbe.get_leaf(n("eight")), Some(&(8, (8 - 9000))));
    assert_eq!(first_sub_mbe.get_leaf(n("x")), None);

    // test that phantoms from the previous level don't cause us trouble when repeats are empty

    let mut teens_with_outer = EnvMBE::new_from_anon_repeat(teens_mbe);
    teens_with_outer.add_leaf(n("outer"), 0);
    let mut nothing_with_other = EnvMBE::new_from_anon_repeat(vec![]);
    nothing_with_other.add_leaf(n("outer"), 1);

    let teens_and_nothing =
        EnvMBE::new_from_anon_repeat(vec![teens_with_outer, nothing_with_other]);

    let mut output = vec![];
    for outer in teens_and_nothing.march_all(&vec![n("outer")]) {
        for inner in outer.march_all(&vec![n("t")]) {
            output.push((
                inner.get_leaf(n("outer")).map(|x| x.clone()),
                inner.get_leaf(n("t")).map(|x| x.clone()),
            ));
        }
    }
    assert_eq!(output, vec![(Some(0), Some(11)), (Some(0), Some(12)), (Some(0), Some(13))]);
}

#[test]
fn splice_healing() {
    use crate::ast::Ast;

    let orig = mbe!(
        "rator" => (vr "add"), "rand" => [(vr "a"), (vr "b"), (vr "c"), (vr "d")]
    );
    let mut noop = orig.clone();
    noop.heal_splices::<()>(&|_| Ok(None)).unwrap();
    assert_eq!(noop, orig);

    let mut b_to_xxx = orig.clone();
    b_to_xxx
        .heal_splices::<()>(&|a| {
            if a == &ast!((vr "b")) {
                Ok(Some(vec![ast!((vr "x")), ast!((vr "xx"))]))
            } else {
                Ok(None)
            }
        })
        .unwrap();
    assert_eq!(
        b_to_xxx,
        mbe!(
            "rator" => (vr "add"), "rand" => [(vr "a"), (vr "x"), (vr "xx"), (vr "c"), (vr "d")]
        )
    );

    let steal_from_other =
        |a: &Ast, other__a_vec__thunk: &dyn Fn() -> Vec<Ast>| -> Result<Option<Vec<Ast>>, ()> {
            if a == &ast!((vr "c")) {
                Ok(Some(other__a_vec__thunk()))
            } else {
                Ok(None)
            }
        };

    let other_short = mbe!(
        "rator" => (vr "---"), "rand" => [(vr "1"), (vr "2"), (vr "3")]);

    let mut with_short = orig.clone();
    assert_eq!(with_short.heal_splices__with::<(), Ast>(&other_short, &steal_from_other), Ok(()));
    assert_eq!(with_short, mbe!("rator" => (vr "add"), "rand" => [(vr "a"), (vr "b"), (vr "d")]));

    let other_long = mbe!(
        "rator" => (vr "---"),
        "rand" => [(vr "1"), (vr "2"), (vr "3"), (vr "4"), (vr "5"), (vr "6")]);

    let mut with_long = orig.clone();
    assert_eq!(with_long.heal_splices__with::<(), Ast>(&other_long, &steal_from_other), Ok(()));
    assert_eq!(
        with_long,
        mbe!("rator" => (vr "add"),
        "rand" => [(vr "a"), (vr "b"), (vr "3"), (vr "4"), (vr "5"), (vr "d")])
    );

    // TODO: require the existence of a constructor like `E::mismatch_error()`
    // let other__too_short = mbe!(
    // "rator" => (vr "---"),
    // "rand" => [(vr "1"), (vr "2")]);
    //
    // let mut with__too_short = orig.clone();
    //
    // assert_eq!(with__too_short.heal_splices__with(&other__too_short, &steal_from_other), ???);

    // TODO: test this more!
}

#[test]
fn ddd_iter() {
    assert_eq!(DddIter::new([0, 1, 2].iter(), 0, 0).collect::<Vec<_>>(), [&1, &2]);
    assert_eq!(DddIter::new([0, 1, 2].iter(), 1, 0).collect::<Vec<_>>(), [&0, &2]);
    assert_eq!(DddIter::new([0, 1, 2].iter(), 2, 0).collect::<Vec<_>>(), [&0, &1]);

    assert_eq!(DddIter::new([0, 1, 2].iter(), 1, 1).collect::<Vec<_>>(), [&0, &1, &2]);
    assert_eq!(DddIter::new([0, 1, 2].iter(), 1, 3).collect::<Vec<_>>(), [&0, &1, &1, &1, &2]);
}

#[test]
fn mbe_ddd_map_with() {
    use crate::ast::{Ast, Atom};

    let lhs = mbe!( "a" => ["0", "1", "2", "3", "4"] );
    let rhs = mbe!( "a" => ["0" ...("1")..., "4"] );

    fn concat(l: &Ast, r: &Ast) -> Ast {
        match (l, r) {
            (&Atom(ln), &Atom(rn)) => Atom(n(format!("{}{}", ln, rn).as_str())),
            _ => panic!(),
        }
    }

    assert_eq!(lhs.map_with(&rhs, &concat), mbe!( "a" => ["00", "11", "21", "31", "44"] ));
    assert_eq!(rhs.map_with(&lhs, &concat), mbe!( "a" => ["00", "11", "12", "13", "44"] ));

    assert_eq!(lhs.map_reduce_with(&rhs, &concat, &concat, ast!("")), ast!("4431211100")); // N.B. order is arbitrary

    {
        let lhs = mbe!( "a" => [["a", "b"], ["c", "d"], ["c", "d"]]);
        let rhs = mbe!( "a" => [["a", "b"] ...(["c", "d"])...]);

        assert_eq!(
            lhs.map_with(&rhs, &concat),
            mbe!( "a" => [["aa", "bb"], ["cc", "dd"], ["cc", "dd"]])
        );
    }
    {
        let lhs = mbe!("a" => [...(["-0", "-1" ...("-")..., "-9"])...]);
        let rhs = mbe!("a" => [["p0", "p1", "p4", "p5", "p6", "p9"], ["p0", "p1", "p9"]]);

        assert_eq!(
            lhs.map_with(&rhs, &concat),
            mbe!("a" => [["-0p0", "-1p1", "-p4", "-p5", "-p6", "-9p9"], ["-0p0", "-1p1", "-9p9"]])
        );

        // Drop all but the first of each repetition:
        assert_eq!(
            lhs.map_collapse_reduce_with(
                &rhs,
                &concat,
                &|v| if v.len() > 0 { v[0].clone() } else { ast!("") },
                &|l, r| concat(&l, &r),
                ast!("")
            ),
            ast!("-0p0-1p1-p4-9p9")
        );
    }
}
