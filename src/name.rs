#![macro_use]

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    fmt,
    string::String,
};

/// An interned, freshenable identifier.
/// Generally, one creates names with `n()` (short for `Name::global()`);
///  two names created this way with the same spelling will be treated as the same name.
/// Hygiene comes from freshening (implemented in `alpha.rs`, invoked in `walk_mode.rs`).
/// If a name is created in an unusual way that might cause it to collide,
///  `Name::gensym()` ensures uniqueness.
/// Only names that were copied or clone from the original will compare equal.
#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub struct Name {
    id: usize,
}

pub struct Spelling {
    // No two different variables have this the same. Tomatoes may have been added:
    unique: String,
    // The original spelling that the programmer chose.
    orig: String,
}

thread_local! {
    // From `Spelling.unique` to `id`s:
    static id_map: RefCell<HashMap<String, usize>> = RefCell::new(HashMap::new());
    // From `id`s to `Spelling`s
    static spellings: RefCell<Vec<Spelling>> = RefCell::new(vec![]);

    static printables: RefCell<HashMap<usize, String>> = RefCell::new(HashMap::new());
    // The values of `printables`, for lookup purposes.
    static printables_used: RefCell<HashSet<String>> = RefCell::new(HashSet::new());

    // Should we do "naive" freshening for testing purposes?
    static fake_freshness: RefCell<bool> = RefCell::new(false);
}

impl crate::runtime::reify::Reifiable for Name {
    fn ty_name() -> Name { n("Name") }

    fn reify(&self) -> crate::runtime::eval::Value {
        crate::runtime::eval::Value::AbstractSyntax(crate::ast::Ast::Atom(*self))
    }

    fn reflect(v: &crate::runtime::eval::Value) -> Name {
        extract!((v) crate::runtime::eval::Value::AbstractSyntax = (ref ast)
                          => ast.to_name())
    }
}

impl std::cmp::PartialOrd for Name {
    fn partial_cmp(&self, other: &Name) -> Option<std::cmp::Ordering> {
        Some(self.orig_sp().cmp(&other.orig_sp()))
    }
}

impl std::cmp::Ord for Name {
    fn cmp(&self, other: &Name) -> std::cmp::Ordering { self.orig_sp().cmp(&other.orig_sp()) }
}

// These are for isolating tests of alpha-equivalence from each other.

pub fn enable_fake_freshness(ff: bool) {
    fake_freshness.with(|fake_freshness_| {
        *fake_freshness_.borrow_mut() = ff;
    })
}

// only available on nightly:
// impl !Send for Name {}

impl Name {
    /// Two names that are unequal to each other will have different "spelling"s.
    /// Tomatoes (🍅) may have been added to the end to ensure uniqueness.
    pub fn sp(self) -> String { spellings.with(|us| us.borrow()[self.id].unique.clone()) }
    /// The "original spelling" of a name; the string that was used to define it. These may collide.
    pub fn orig_sp(self) -> String { spellings.with(|us| us.borrow()[self.id].orig.clone()) }

    /// This extracts the "original" `Name`, prior to any freshening.
    /// This is probably not ever the *right* thing to do, but may be needed as a workaround.
    pub fn unhygienic_orig(self) -> Name {
        spellings.with(|us| Name::new(&us.borrow()[self.id].orig, false))
    }

    /// Printable names are unique, like names from `sp()`, but generated lazily.
    /// So, if the compiler freshens some name a bunch of times, producing a tomato-filled mess,
    /// but only prints one version of the name, it gets to print an unadorned name.
    /// If absolutely necessary to avoid collision, carrots (🥕) are added to the end.
    pub fn print(self) -> String {
        printables.with(|printables_| {
            printables_used.with(|printables_used_| {
                printables_
                    .borrow_mut()
                    .entry(self.id)
                    .or_insert_with(|| {
                        let mut print_version = self.orig_sp();
                        while printables_used_.borrow().contains(&print_version) {
                            // Graffiti seen at Berkley: "EⒶT YOUR VEGETABLES 🥕"
                            print_version = format!("{}🥕", print_version);
                        }
                        printables_used_.borrow_mut().insert(print_version.clone());
                        print_version.clone()
                    })
                    .clone()
            })
        })
    }

    pub fn global(s: &str) -> Name { Name::new(s, false) }
    pub fn gensym(s: &str) -> Name { Name::new(s, true) }
    pub fn freshen(self) -> Name { Name::new(&self.orig_sp(), true) }

    fn new(orig_spelling: &str, freshen: bool) -> Name {
        let fake_freshness_ = fake_freshness.with(|ff| *ff.borrow());

        id_map.with(|id_map_| {
            let mut unique_spelling = orig_spelling.to_owned();
            // Find a fresh version by adding tomatoes, if requested:
            while freshen && id_map_.borrow().contains_key(&unique_spelling) {
                unique_spelling = format!("{}🍅", unique_spelling);
            }

            if freshen && fake_freshness_ {
                // Forget doing it right; only add exactly one tomato:
                unique_spelling = format!("{}🍅", orig_spelling);
            }

            let claim_id = || {
                spellings.with(|spellings_| {
                    let new_id = spellings_.borrow().len();
                    spellings_.borrow_mut().push(Spelling {
                        unique: unique_spelling.clone(),
                        orig: orig_spelling.to_owned(),
                    });
                    new_id
                })
            };

            // If we're faking freshness, make the freshened name findable. Otherwise...
            let id = if freshen && !fake_freshness_ {
                claim_id() // ...don't put it in the table
            } else {
                *id_map_.borrow_mut().entry(unique_spelling.clone()).or_insert_with(claim_id)
            };

            Name { id: id }
        })
    }
    pub fn is(self, s: &str) -> bool { self.sp() == s }

    pub fn is_name(self, n: Name) -> bool { self.sp() == n.sp() }
}

// TODO: move to `ast_walk`
// TODO: using `lazy_static!` (with or without gensym) makes some tests fail. Why?
/// Special name for negative `ast_walk`ing
pub fn negative_ret_val() -> Name { Name::global("⋄") }

impl fmt::Debug for Name {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "«{}»", self.sp()) }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{}", self.print()) }
}

pub fn n(s: &str) -> Name { Name::global(s) }

#[test]
fn name_interning() {
    // This test fails under tarpaulin; why? It must be related to `thread_local!` somehow...
    let a = n("a");
    assert_eq!(a, a);
    assert_eq!(a, n("a"));
    assert_ne!(a, a.freshen());
    assert_eq!(a, a.freshen().unhygienic_orig());

    assert_ne!(a, n("x🍅"));
    assert_ne!(a.freshen(), a.freshen());

    assert_ne!(n("a"), n("y"));

    enable_fake_freshness(true);

    let x = n("x");
    assert_eq!(x, x);
    assert_eq!(x, n("x"));
    assert_ne!(x, x.freshen());

    // ... but now we the freshened version of `x` is accessible (and doesn't avoid existing names)
    assert_eq!(x.freshen(), n("x🍅"));
    assert_eq!(x.freshen(), x.freshen());

    // Printable versions are first-come, first-served
    assert_eq!(a.freshen().print(), "a");
    assert_eq!(a.print(), "a🥕");
}
