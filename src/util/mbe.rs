/*
March By Example: a user-friendly way to handle named subterms under Kleene stars,
 expressed through a special kind of environment.
This is intended to organize the subterms of an `Ast` node.
Using this as the evaluation environment of a program is probably interesting,
 but not necessarily in a good way.


The principle is this: 
 Kleene stars in a (macro) grammar 
   (e.g. `(f=Identifier (arg=Identifier ":" arg_t=Type)*)` )
  correspond to lists in an AST.
 The original syntactic structure is irrelevant.
  but there's only one name (e.g. `arg_t`) for the entire list of matched syntax.
  
 But that's okay:
  We will let the user put Kleene stars inside syntax quotation (macro transcription).
  The named pieces of syntax under the Kleene star control the number of repetitions:
   if each identifier either repeats `n` times or wasn't matched under a `*` at all,
    the star repeats `n` times, with the repeated syntax "marching in lockstep",
    and the non-`*`ed syntax duplicated
    
This whole thing nicely generalizes to nesting: we use variable-arity trees instead of lists. 

This also generalizes to not need transcription:
 we will store an environment mapping names to variable-arity trees,
  and provide an operation ("march") that, given a set of names
    ("driving names", presumably the names "under the `*`")
   produces `n` environments, in which each of those names has a tree 
    that is shorter by one level.

One problem: what if two of the "driving names" repeat a different numbers of times?
Traditionally, this is a runtime error,
 but we'd like it to be a parser error: 
  after all, it's the author of the syntax  
   who has control over how many repetions there are of each thing.
So, we will let grammars specify when different Kleene stars
 must repeat the same number of times.
Violations of this rule are a parse error,
 and it's only legal to "march" with driving names
  that were matched (at the current level)
   (a) under the same `*`, or
   (b) under `*`s that must repeat the same number of times.
On the other hand, if the user wants "cross product" behavior,
 there's no reason that they can't get it.
We may add a facility to take syntax matched `a`, `b`, `c`... times,
 and produce `a × b × c` different environments.
   
   
This is based on Macro By Example, but this implementation isn't strictly about macros,
 which is why I changed the name!
The original MBE paper is 
 "Macro-by-example: Deriving syntactic transformations from their specifications"
  by Kohlbecker and Wand
  ftp://www.cs.indiana.edu/pub/techreports/TR206.pdf

Many interesting macros can be defined simply 
 by specifying a grammar and a piece of quoted syntax,
 if the syntax transcription supports MBE.
 (This corresponds to Scheme's `syntax-rules` and Rust's `macro-rules`.)
*/

use util::assoc::Assoc;
use name::*;
use std::rc::Rc;

/**
 `EnvMBE` is like an environment, 
  except that some of its contents are "repeats", 
   which represent _n_ different values 
   (or repeats of repeats, etc.).
 Non-repeated values may be retrieved by `get_leaf`.
 To access repeated values, one must `march` them, 
  which produces _n_ different environments,
   in which the marched values are not repeated (or one layer less repeated).
 Marching multiple repeated values at once
  is only permitted if they were constructed to repeat the same number of times.
 
*/
pub struct EnvMBE<'t, T> {
    /// Non-repeated values
    leaves: Assoc<Name<'t>, T>,
    
    /// Outer vec holds distinct repetitions 
    ///  (i.e. differently-named, or entirely unnamed repetitions)
    /// Note that some of the entries may be obsolete; 
    ///  deletions are marked by putting `None` in the `Assoc`s 
    ///   that index into this.
    repeats: Vec<Rc<Vec<EnvMBE<'t,T>>>>,
    
    /// Where in `repeats` to look, if we want to traverse for a particular leaf.
    /// We use `.unwrap_or(None)` when looking up into this 
    ///  so we can delete by storing `None`.

    leaf_locations: Assoc<Name<'t>, Option<usize>>,
    
    /// The location in `repeats` that represents a specific repetition name.
    named_repeats: Assoc<Name<'t>, Option<usize>>,
}



impl<'t, T: Clone> EnvMBE<'t, T> {
    pub fn new() -> EnvMBE<'t, T> {
        EnvMBE {
            leaves: Assoc::new(),
            repeats: vec![],
            leaf_locations: Assoc::new(),
            named_repeats: Assoc::new()
        }
    }
    
    pub fn new_from_leaves(l: Assoc<Name<'t>, T>) -> EnvMBE<'t, T> {
        EnvMBE {
            leaves: l,
            repeats: vec![],
            leaf_locations: Assoc::new(),
            named_repeats: Assoc::new()
        }
    }
    
    /// Note: ideally, the larger one should be on the LHS.
    pub fn combine_overriding(&self, rhs: &EnvMBE<'t,T>) -> EnvMBE<'t, T> {
        let adjust_rhs_by = self.repeats.len();
        
        let mut new_repeats = self.repeats.clone();
        new_repeats.append(&mut rhs.repeats.clone());
        
        EnvMBE {
            leaves: self.leaves.set_assoc(&rhs.leaves),
            repeats: new_repeats,
            leaf_locations: self.leaf_locations.set_assoc(
                &rhs.leaf_locations.map(&|idx_opt| idx_opt.map(|idx| idx+adjust_rhs_by))),
            named_repeats: self.named_repeats.set_assoc(
                &rhs.named_repeats.map(&|idx_opt| idx_opt.map(|idx| idx+adjust_rhs_by)))
        }
        
    }
    
    /// Given `driving_names`, marches the whole set of names that can march with them.
    /// (Adding an additional name to `driving_names` will result in the same behavior,
    ///  or a panic, in the case that the new name can't be marched with the existing ones.)
    pub fn march_all(&self, driving_names: Vec<Name<'t>>) -> Vec<EnvMBE<T>> {
        let mut first_march : Option<(usize, Name<'t>)> = None;
        
        for &n in &driving_names {
            match (first_march, self.leaf_locations.find(&n).unwrap_or(&None)) {
                 (_, &None) => {}
                 (None, &Some(loc)) => { first_march = Some((loc, n)) }
                 (Some((old_loc, old_name)), &Some(new_loc)) => {
                     if old_loc != new_loc {
                         panic!("{:?} and {:?} cannot march together; they weren't matched to have the same number of repeats",
                                old_name, n);
                     }
                 }
            }
        }
        
        let march_loc = match first_march {
            None => { panic!("None of {:?} are repeated.", driving_names) }
            Some((loc, _)) => loc
        };
        
        let mut result = vec![];
        for marched_out in self.repeats[march_loc].iter() {
            result.push(self.combine_overriding(marched_out));
        }
        
        result
    }
    
    pub fn get_leaf(&self, n: &Name<'t>) -> Option<&T> {
        self.leaves.find(n)
    }
    
    pub fn add_leaf(&mut self, n: Name<'t>, v: T) {
        self.leaves = self.leaves.set(n, v);
    }
    
    fn update_leaf_locs(&mut self, idx: usize, sub: &Vec<EnvMBE<'t, T>>) {
        let mut already_placed_leaves = ::std::collections::HashSet::<Name<'t>>::new();
        let mut already_placed_repeats = ::std::collections::HashSet::<Name<'t>>::new();

        for sub_mbe in sub {
            for &leaf_name in sub_mbe.leaf_locations.iter_keys()
                    .chain(sub_mbe.leaves.iter_keys()) {
                if !already_placed_leaves.contains(&leaf_name) {
                    self.leaf_locations = self.leaf_locations.set(leaf_name, Some(idx));
                    already_placed_leaves.insert(leaf_name);
                } 
            }
            for &repeat_name in sub_mbe.named_repeats.iter_keys() {
                if !already_placed_repeats.contains(&repeat_name) {
                    self.named_repeats = self.named_repeats.set(repeat_name, Some(idx));
                    already_placed_repeats.insert(repeat_name);
                }
            }
        }
    }
    
    pub fn add_named_repeat(&mut self, n: Name<'t>, sub: Vec<EnvMBE<'t, T>>) {
        match self.named_repeats.find(&n).unwrap_or(&None) {
            &None => {
                let new_index = self.repeats.len();
                self.update_leaf_locs(new_index, &sub);

                self.repeats.push(Rc::new(sub));
                self.named_repeats = self.named_repeats.set(n, Some(new_index));
            }
            &Some(idx) => {
                if self.repeats[idx].len() != sub.len() {
                    panic!("Named repetition {:?} is repeated {:?} times in one place, {:?} times in another.",
                        n, self.repeats[idx].len(), sub.len())
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
    
    pub fn add_anon_repeat(&mut self, sub: Vec<EnvMBE<'t, T>>) {
        let new_index = self.repeats.len();
        self.update_leaf_locs(new_index, &sub);
        
        self.repeats.push(Rc::new(sub));
    }
    
    
    pub fn map<NewT>(&self, f: &Fn(T) -> NewT) -> EnvMBE<'t, NewT> {
        EnvMBE {
            leaves: self.leaves.map(f),
            repeats: self.repeats.iter().map(
                |rc_vec_mbe| Rc::new(rc_vec_mbe.iter().map(
                    |mbe| mbe.map(f)
                ).collect())).collect(),
            leaf_locations: self.leaf_locations.clone(),
            named_repeats: self.named_repeats.clone()
        }
    }
}


#[test]

fn test_mbe() {
    let mut mbe = EnvMBE::new();
    mbe.add_leaf(n("eight"), 8 as i32);
    mbe.add_leaf(n("nine"), 9);
    
    
    let teens_mbe = vec![
        EnvMBE::new_from_leaves(assoc_n!("t" => 11)),
        EnvMBE::new_from_leaves(assoc_n!("t" => 12)),
        EnvMBE::new_from_leaves(assoc_n!("t" => 13))
    ];

    mbe.add_named_repeat(n("low_two_digits"), teens_mbe);

    let big_mbe = vec![
        EnvMBE::new_from_leaves(assoc_n!("y" => 9001)),
        EnvMBE::new_from_leaves(assoc_n!("y" => 9002))
    ];
    
    mbe.add_anon_repeat(big_mbe);

    
    for (sub_mbe, teen) in mbe.march_all(vec![n("t"), n("eight")]).iter().zip(vec![11,12,13]) {
        assert_eq!(sub_mbe.get_leaf(&n("eight")), Some(&8));
        assert_eq!(sub_mbe.get_leaf(&n("nine")), Some(&9));
        assert_eq!(sub_mbe.get_leaf(&n("t")), Some(&teen));
        assert_eq!(sub_mbe.get_leaf(&n("y")), None);
        
        for (sub_sub_mbe, big) in sub_mbe.march_all(vec![n("y"), n("eight")]).iter().zip(vec![9001, 9002]) {
            assert_eq!(sub_sub_mbe.get_leaf(&n("eight")), Some(&8));
            assert_eq!(sub_sub_mbe.get_leaf(&n("nine")), Some(&9));
            assert_eq!(sub_sub_mbe.get_leaf(&n("t")), Some(&teen));
            assert_eq!(sub_sub_mbe.get_leaf(&n("y")), Some(&big));
        }
    }
    
    let neg_teens_mbe = vec![
        EnvMBE::new_from_leaves(assoc_n!("nt" => -11)),
        EnvMBE::new_from_leaves(assoc_n!("nt" => -12)),
        EnvMBE::new_from_leaves(assoc_n!("nt" => -13))
    ];
    
    mbe.add_named_repeat(n("low_two_digits"), neg_teens_mbe);
    
    for (sub_mbe, teen) in mbe.march_all(vec![n("t"), n("nt"), n("eight")]).iter().zip(vec![11,12,13]) {
        assert_eq!(sub_mbe.get_leaf(&n("eight")), Some(&8));
        assert_eq!(sub_mbe.get_leaf(&n("nine")), Some(&9));
        assert_eq!(sub_mbe.get_leaf(&n("t")), Some(&teen));
        assert_eq!(sub_mbe.get_leaf(&n("nt")), Some(&-teen));

        for (sub_sub_mbe, big) in sub_mbe.march_all(vec![n("y"), n("eight")]).iter().zip(vec![9001, 9002]) {
            assert_eq!(sub_sub_mbe.get_leaf(&n("eight")), Some(&8));
            assert_eq!(sub_sub_mbe.get_leaf(&n("nine")), Some(&9));
            assert_eq!(sub_sub_mbe.get_leaf(&n("t")), Some(&teen));
            assert_eq!(sub_sub_mbe.get_leaf(&n("nt")), Some(&-teen));
            assert_eq!(sub_sub_mbe.get_leaf(&n("y")), Some(&big));
        }
    }
    
    let mapped_mbe = mbe.map(&|x| (x, x - 9000));
    
    let first_sub_mbe = &mapped_mbe.march_all(vec![n("y")])[0];
    
    assert_eq!(first_sub_mbe.get_leaf(&n("y")), Some(&(9001, 1)));
    assert_eq!(first_sub_mbe.get_leaf(&n("eight")), Some(&(8, 8 - 9000)));
    assert_eq!(first_sub_mbe.get_leaf(&n("x")), None); 
    
}