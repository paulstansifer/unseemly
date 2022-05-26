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
//    (e.g. `[f=Identifier [arg=Identifier ":" arg_t=Type]*]` )
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
            Rc::new(self.leaf_locations.reify()),
            Rc::new(self.named_repeats.reify()),
        ])
    }
    fn reflect(v: &crate::runtime::eval::Value) -> Self {
        extract!((v) crate::runtime::eval::Value::Sequence = (ref parts) => {
            EnvMBE {
               leaves: <Assoc<Name, T>>::reflect(&*parts[0]),
               repeats: <Vec<Rc<Vec<EnvMBE<T>>>>>::reflect(&*parts[1]),
               leaf_locations: <Assoc<Name, Option<usize>>>::reflect(&*parts[2]),
               named_repeats: <Assoc<Name, Option<usize>>>::reflect(&*parts[3])
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

impl<T: Clone + fmt::Display> fmt::Display for EnvMBE<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.leaves.empty() && self.repeats.is_empty() {
            write!(f, "∅")
        } else {
            write!(f, "{{MBE {}, ✶", self.leaves)?;
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
                            write!(f, "⋯({})⋯ ", name)?;
                        }
                    }
                }
                for mbe in &**rep {
                    write!(f, "{} ", mbe)?;
                }
            }
            write!(f, "}}")
        }
    }
}

impl<T: Clone> EnvMBE<T> {
    pub fn new() -> EnvMBE<T> {
        EnvMBE {
            leaves: Assoc::new(),
            repeats: vec![],
            leaf_locations: Assoc::new(),
            named_repeats: Assoc::new(),
        }
    }

    /// Creates an `EnvMBE` without any repetition
    pub fn new_from_leaves(l: Assoc<Name, T>) -> EnvMBE<T> {
        EnvMBE {
            leaves: l,
            repeats: vec![],
            leaf_locations: Assoc::new(),
            named_repeats: Assoc::new(),
        }
    }

    /// Creates an `EnvMBE` containing a single anonymous repeat
    /// (HACK: there's no way to represent a name repeating zero times this way;
    ///  use `new_from_empty_anon_repeat`)
    pub fn new_from_anon_repeat(r: Vec<EnvMBE<T>>) -> EnvMBE<T> {
        let mut res = EnvMBE::new();
        res.add_anon_repeat(r);
        res
    }

    /// Creates an `EnvMBE` containing a single named repeat
    /// (HACK: there's no way to represent a name repeating zero times this way;
    ///  use `new_from_empty_named_repeat`)
    pub fn new_from_named_repeat(n: Name, r: Vec<EnvMBE<T>>) -> EnvMBE<T> {
        let mut res = EnvMBE::new();
        res.add_named_repeat(n, r);
        res
    }

    pub fn new_from_empty_anon_repeat(ks: &[Name]) -> EnvMBE<T> {
        let mut res = EnvMBE::new();
        for k in ks {
            res.leaf_locations.mut_set(*k, Some(0));
        }
        res.repeats.push(Rc::new(vec![]));
        res
    }

    pub fn new_from_empty_named_repeat(n: Name, ks: &[Name]) -> EnvMBE<T> {
        let mut res = EnvMBE::new();
        for k in ks {
            res.leaf_locations.mut_set(*k, Some(0));
        }
        res.repeats.push(Rc::new(vec![]));
        res.named_repeats.mut_set(n, Some(0));
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

        EnvMBE {
            leaves: self.leaves.set_assoc(&rhs.leaves),
            repeats: new_repeats,
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
                if rhs.repeats[rep_idx].len() > 0 {
                    res.add_named_repeat(*n, (*rhs.repeats[rep_idx]).clone());
                } else {
                    // Maybe pull this out as `.add_empty_named_repeat`?
                    let empty_idx = if let Some(Some(rep_idx)) = res.named_repeats.find(n) {
                        if res.repeats[*rep_idx].len() != 0 {
                            panic!("Length mismatch; {} is supposed to repeat empty", n);
                        }
                        *rep_idx
                    } else {
                        let new_idx = res.repeats.len();
                        res.repeats.push(Rc::new(vec![]));
                        res.named_repeats.mut_set(*n, Some(new_idx));
                        new_idx
                    };
                    for (leaf_name, leaf_loc) in rhs.leaf_locations.iter_pairs() {
                        if leaf_loc == &Some(rep_idx) {
                            res.leaf_locations.mut_set(*leaf_name, Some(empty_idx));
                        }
                    }
                }
                rhs_idx_is_named[rep_idx] = true;
            }
        }

        for (idx, rep) in rhs.repeats.iter().enumerate() {
            if !rhs_idx_is_named[idx] {
                if rep.len() > 0 {
                    res.add_anon_repeat((**rep).clone());
                } else {
                    // Maybe pull this out as `.addempty__anon_repeat`?
                    let empty_idx = res.repeats.len();
                    res.repeats.push(Rc::new(vec![]));
                    for (leaf_name, leaf_loc) in rhs.leaf_locations.iter_pairs() {
                        if leaf_loc == &Some(idx) {
                            res.leaf_locations.mut_set(*leaf_name, Some(empty_idx));
                        }
                    }
                }
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

    pub fn add_named_repeat(&mut self, n: Name, sub: Vec<EnvMBE<T>>) {
        if sub.is_empty() {
            return;
        } // no-op-ish, but keep the repeats clean (good for `eq`)

        match *self.named_repeats.find(&n).unwrap_or(&None) {
            None => {
                let new_index = self.repeats.len();
                self.update_leaf_locs(new_index, &sub);

                self.repeats.push(Rc::new(sub));
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
            }
        }
    }

    pub fn add_anon_repeat(&mut self, sub: Vec<EnvMBE<T>>) {
        if sub.is_empty() {
            return;
        } // no-op-ish, but keep the repeats clean (good for `eq`)

        let new_index = self.repeats.len();
        self.update_leaf_locs(new_index, &sub);

        self.repeats.push(Rc::new(sub));
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
                    let marched_ctxts = match self.leaf_locations.find_value(&Some(rpt_idx)) {
                        Some(this_rpt_name) => ctxt.march_all(&[*this_rpt_name]),
                        None => {
                            // This repeat has no leaves.
                            let mut res = vec![];
                            res.resize(rc_vec_mbe.len(), ctxt.clone());
                            res
                        }
                    };

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
            leaf_locations: self.leaf_locations.clone(),
            named_repeats: self.named_repeats.clone(),
        }
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

        if self.repeats.len() != o.repeats.len() {
            return false;
        }
        for (subs, o_subs) in self.repeats.iter().zip(o.repeats.iter()) {
            if subs.len() != o_subs.len() {
                return false;
            }
            for (mbe, o_mbe) in subs.iter().zip(o_subs.iter()) {
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
                .zip(o.repeats.iter())
                .map(&|(rc_vec_mbe, o_rc_vec_mbe): (&Rc<Vec<EnvMBE<T>>>, &Rc<Vec<EnvMBE<S>>>)| {
                    Rc::new(
                        rc_vec_mbe
                            .iter()
                            .zip(o_rc_vec_mbe.iter())
                            .map(|(mbe, o_mbe)| mbe.named_map_with(o_mbe, f))
                            .collect(),
                    )
                })
                .collect(),
            leaf_locations: self.leaf_locations.clone(),
            named_repeats: self.named_repeats.clone(),
        }
    }

    pub fn map_reduce_with<S: Clone, NewT: Clone>(
        &self,
        other: &EnvMBE<S>,
        f: &dyn Fn(&T, &S) -> NewT,
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

            for (self_elt, other_elt) in
                self.repeats[self_idx].iter().zip(other.repeats[other_idx].iter())
            {
                reduced = self_elt.map_reduce_with(other_elt, f, &red, reduced);
            }
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
            None => panic!(
                " {} not found in {} (perhaps it is still repeated?)",
                n,
                self.leaves.map(|_| "…")
            ),
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

    mbe.add_named_repeat(n("low_two_digits"), teens_mbe.clone());

    let big_mbe = vec![
        EnvMBE::new_from_leaves(assoc_n!("y" => 9001)),
        EnvMBE::new_from_leaves(assoc_n!("y" => 9002)),
    ];

    mbe.add_anon_repeat(big_mbe);

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

    mbe.add_named_repeat(n("low_two_digits"), neg_teens_mbe);

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
        mbe.map_reduce_with(&all_zeroes, &|a, b| if *a < *b { *a } else { *b }, &|a, b| a + b, 0),
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
fn empty_mbe() {
    let no_foos: EnvMBE<crate::ast::Ast> = mbe!("foo" => []);

    let no_asts: Vec<&crate::ast::Ast> = vec![];
    assert_eq!(no_foos.get_rep_leaf_or_panic(n("foo")), no_asts);
}
