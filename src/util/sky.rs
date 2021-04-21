use crate::{
    name::{n, Name},
    util::{
        assoc::Assoc,
        asterism::{AsterMarchable, Asterism, AsterismSlice},
    },
};
use std::iter::Iterator;

type Sky<T> = Assoc<Name, Asterism<T>>;
/// `SkySlice` isn't a slice itself,
///  so we can't pull the same trick we pulled with `AsterismSlice`.
/// (Maybe rename it, then?)
type SkySlice<'a, T> = Assoc<Name, AsterismSlice<'a, T>>;

impl<'a, T> SkySlice<'a, T>
where T: Clone
{
    fn get(&self, n: Name) -> AsterismSlice<'a, T> { self.find_or_panic(&n).clone() }

    fn combine_overriding(&self, rhs: &Self) -> Assoc<Name, AsterismSlice<'a, T>> {
        self.set_assoc(rhs)
    }

    #[deprecated]
    // In `EnvMBE`, this respected named repeats.
    fn merge(&self, rhs: &Self) -> Assoc<Name, AsterismSlice<'a, T>> { self.set_assoc(rhs) }

    /// Each of `driving_names` must be a repetition of the same length.
    /// Produces an iterator with the same length,
    ///  yielding `SkySlice`s in which the driven names have that repetition removed.
    fn march(&self, driving_names: &[Name]) -> Box<dyn Iterator<Item = SkySlice<'a, T>> + 'a> {
        let marchers: Vec<(Name, std::vec::IntoIter<AsterismSlice<'a, T>>)> =
            driving_names.iter().map(|n| (*n, self.get(*n).march())).collect();

        // Require the lengths to be the same
        for (n, marcher) in &marchers[1..] {
            if marcher.len() != marchers[0].1.len() {
                icp!(
                    "Lengths don't match in march names: {} ({}) != {} ({})",
                    marcher.len(),
                    n,
                    marchers[0].1.len(),
                    marchers[0].0
                );
            }
        }

        // By default, names refer to the same Asterims (just sliced)
        let mut res: Box<dyn Iterator<Item = SkySlice<'a, T>> + 'a> =
            Box::new(std::iter::repeat(self.clone()));

        // For the driving names, override with the current step of the march
        for (name, marched) in marchers {
            res = Box::new(res.zip(marched.into_iter()).map(
                move |(base, marched): (SkySlice<T>, AsterismSlice<T>)| base.set(name, marched),
            ));
        }

        res
    }

    #[deprecated(note = "use `march` instead")]
    // The `_all` is no longer meaningful. This does a bunch of unnecessary cloning.
    fn march_all(&self, driving_names: &[Name]) -> Vec<Sky<T>> {
        self.march(driving_names).map(|s| s.to_sky()).collect()
    }

    #[deprecated(note = "do we need this?")]
    fn get_leaf<'b>(&'b self, n: Name) -> Option<&'a T> {
        match self.find(&n) {
            None => None,
            Some(aster) => Some(aster.as_leaf()),
        }
    }

    fn leaf<'b>(&'b self, n: Name) -> &'a T
    where 'a: 'b {
        self.get(n).as_leaf()
    }

    #[deprecated(note = "use `leaf` instead")]
    fn get_leaf_or_panic(&self, n: Name) -> &T { self.get(n).as_leaf() }

    #[deprecated(note = "use `depth_1` instead")]
    fn get_rep_leaf(&self, n: Name) -> Option<Vec<&T>> {
        self.find(&n).map(|asterism| asterism.as_depth_1().collect::<Vec<&T>>())
    }

    #[deprecated(note = "use `depth_1` instead")]
    fn get_rep_leaf_or_panic(&'a self, n: Name) -> Vec<&'a T> {
        self.get(n).as_depth_1().collect::<Vec<&T>>()
    }

    fn depth_1<'b>(&'b self, n: Name) -> Box<dyn std::iter::Iterator<Item = &'a T> + 'a> {
        self.get(n).as_depth_1()
    }

    // fn map_flatten_rep_leaf_or_panic<S>(&self, n: Name, depth: u8, m: &dyn Fn(&T) -> S, f: &dyn Fn(Vec<S>) -> S) -> S {
    //    unimplemented!()
    // }
}

impl<T: Clone> SkySlice<'_, T> {
    pub fn to_sky(&self) -> Sky<T> {
        self.map_borrow_f(&mut |a: &AsterismSlice<T>| a.to_asterism())
    }
}

impl<T: Clone> Sky<T> {
    // `l` could be a reference, but do we ever want that?
    pub fn new_from_leaves(l: Assoc<Name, T>) -> Self { l.map(|l| Asterism::from_leaf(l.clone())) }

    #[deprecated]
    pub fn new_from_named_repeat(_n: Name, r: Vec<Self>) -> Self { Self::new_from_anon_repeat(r) }

    pub fn new_from_anon_repeat(mut r: Vec<Self>) -> Self {
        if r.len() == 0 {
            return Sky::new();
        }
        let mut res = Assoc::<Name, Asterism<T>>::new();
        if r.len() > 0 {
            let keys: Vec<Name> = r[0].iter_keys().map(|k| *k).collect();
            for k in keys {
                let per_name_asterisms: Vec<Asterism<T>> =
                    r.iter_mut().map(|sky| sky.remove_or_panic(&k)).collect();
                res = res.set(k, Asterism::join(per_name_asterisms));
            }
        }
        res
    }

    pub fn leaf(&self, n: Name) -> &T { self.find_or_panic(&n).as_leaf() }

    pub fn depth_1<'b>(&'b self, n: Name) -> Box<dyn std::iter::Iterator<Item = &'b T> + 'b> {
        self.find_or_panic(&n).as_depth_1()
    }

    pub fn to_sky_slices<'b>(&'b self) -> SkySlice<'b, T> {
        self.map_borrow_f(&mut |a: &Asterism<T>| a.as_slice())
    }

    pub fn march<'b>(
        &'b self,
        driving_names: &'b [Name],
    ) -> Box<dyn Iterator<Item = SkySlice<'b, T>> + 'b> {
        self.to_sky_slices().march(driving_names)
    }
}

// TODO: move these to macros.rs (and fully-qualify their names)
macro_rules! asterism {
    ([$( $sub:tt ),*]) => {
        Asterism::join(vec![
            $( asterism!($sub) ),*
        ])
    };
    ($leaf:expr) => { Asterism::from_leaf($leaf) };
}

macro_rules! sky {
    ( $($n:tt => $rhs:tt),* ) => {
        assoc_n!( $( (stringify!($n)) => asterism!($rhs) ),* )
    };
}

#[test]
fn sky_basics() {
    let abc: Sky<usize> = sky!(
        a => [[1, 2], [3], []],
        b => 9,
        c => [4, 5, 6],
        d => [7, 8]
    );

    assert_eq!(abc.leaf(n("b")), &9);
    assert_eq!(abc.depth_1(n("c")).collect::<Vec<_>>(), vec![&4, &5, &6]);

    let mut cur_c = 4;
    for abccc in abc.march(&[n("c")]) {
        assert_eq!(abccc.leaf(n("b")), &9);
        assert_eq!(abccc.leaf(n("c")), &cur_c);
        cur_c += 1;
        assert_eq!(abccc.depth_1(n("d")).collect::<Vec<_>>(), vec![&7, &8]);
    }
}
