use std::{fmt, iter::Iterator};

// An `Asterism` is a tree with an arbirary arity at each node,
//  but all leaves are at the same depth.
// This structure arises from parsing under Kleene stars; each star correspons to a level of nodes.

// [                                              ] <- 2 children
// [                                        ][    ] <- 3, 1 children
// [                          ][][          ][    ] <- 5, 0, 1, 2 children
// [    ][ ][    ][    ][     ]  [          ][ ][ ] <- 2, 1, 2, 2, 2, 4, 1, 1 children
//  a  b  c  d  e  f  g  h  i     j  k  l  m  n  o

// * * # a b # c # d e # f g # h i * * # j k l m * * # n # o
//     ----| --| ----| ----| ----| |   --------|     --| --| <- these are `PackedNodes`es
//   ----------------------------| | ----------|   --------| <- everything below is a `Node`
// --------------------------------------------| ----------| <-             ⋮

#[derive(Debug, PartialEq, Eq, Clone)]
/// This is only `pub` for technical reasons; it doesn't need to be exposed to other modules.
///
/// `Node`s and `PackedNodes`es appear at the beginning of a slice to guide marching.
/// If you see `[PackedNodes, …]`, you know you're at depth 1 and [1..] is your leaves.
/// Otherwise, `[Node(n), <n entries>, Node(m), <m entries>, …]` is the shape of the current level.
pub enum LeafOrNode<T> {
    Leaf(T),
    /// A depth-1 node: *each* subtree is a single `Leaf`
    PackedNodes,
    /// A depth >1 node: *this* subtree is `usize` entires long
    Node(usize),
}

#[derive(PartialEq, Eq, Clone)]
pub struct Asterism<T>(Vec<LeafOrNode<T>>);
#[derive(PartialEq, Eq)]
pub struct AsterismSlice<'a, T>(&'a [LeafOrNode<T>]);

// `AsterismSlice` is a reference-like type, so it's always `Clone` and `Copy`, even if `T` isn't:
impl<'a, T> Copy for AsterismSlice<'a, T> {}
impl<'a, T> Clone for AsterismSlice<'a, T> {
    fn clone(&self) -> AsterismSlice<'a, T> { *self }
}

/// This trait is for reference-like views of `Asterism`.
pub trait AsterMarchable<'a, T: 'a>: Sized + Clone + Copy {
    fn as_slice(self) -> AsterismSlice<'a, T>;

    /// Only used for implementation of other methods;
    ///  adding another layer of trait seems like too much trouble to hide this.
    fn inner(self) -> &'a [LeafOrNode<T>];

    /// Returns an iterator of `AsterMarchable<T>`s
    fn march(self) -> std::vec::IntoIter<AsterismSlice<'a, T>> {
        let mut subs = vec![];
        if self.inner().len() == 0 {
            return subs.into_iter();
        }

        // A `PackedNodes` means the rest of the slice is our children (all leaves):
        let depth_1: bool = match self.inner()[0] {
            LeafOrNode::PackedNodes => true,
            _ => false,
        };
        let mut i = if depth_1 { 1 } else { 0 }; // Skip the `PackedNodes`

        while i < self.inner().len() {
            let span = match self.inner()[i] {
                LeafOrNode::Leaf(_) => {
                    if !depth_1 {
                        icp!("Unexpected Leaf")
                    }
                    1
                }
                LeafOrNode::PackedNodes => icp!("Unexpected PackedNodes"),
                LeafOrNode::Node(span) => {
                    if depth_1 {
                        icp!("Unexpected Node")
                    }
                    i += 1;
                    span
                }
            };
            subs.push(AsterismSlice(&self.inner()[i..i + span]));

            i += span;
        }

        subs.into_iter()
    }

    fn collect(self) -> Vec<AsterismSlice<'a, T>> {
        let mut res = vec![];
        for sub in self.march() {
            res.push(sub);
        }
        res
    }

    fn is_leaf(self) -> bool {
        let inner = self.as_slice().0;
        if inner.len() == 0 {
            return false;
        }
        match inner[0] {
            LeafOrNode::Leaf(_) => true,
            _ => false,
        }
    }

    fn as_leaf(self) -> &'a T {
        let inner = self.as_slice().0;
        if inner.len() != 1 {
            icp!("not a leaf, length is {}", inner.len())
        }
        match inner[0] {
            LeafOrNode::Leaf(ref l) => l,
            _ => icp!("malformed Asterism"),
        }
    }

    fn as_depth_1(self) -> Box<dyn Iterator<Item = &'a T> + 'a> {
        if self.as_slice().0.len() == 0 {
            // The "official" representation of an empty depth-1 node is a sequence with 1 `PN`.
            // ...but `Asterism::join(vec![])` doesn't know whether it's depth-1 or not!
            // So we also support an empty vector.
            // TODO: is there a better way?
            return Box::new(std::iter::empty());
        }
        match self.as_slice().0[0] {
            LeafOrNode::PackedNodes => {}
            _ => icp!("Not depth-1"),
        }
        Box::new(self.as_slice().0[1..].iter().map(|lon| match lon {
            LeafOrNode::Leaf(ref l) => l,
            _ => icp!("Not depth-1"),
        }))
    }
}

impl<'a, T> AsterMarchable<'a, T> for AsterismSlice<'a, T> {
    fn as_slice(self) -> AsterismSlice<'a, T> { self }
    fn inner(self) -> &'a [LeafOrNode<T>] { self.0 }
}

impl<'a, T> AsterMarchable<'a, T> for &'a Asterism<T> {
    fn as_slice(self) -> AsterismSlice<'a, T> { AsterismSlice(&self.0[..]) }
    fn inner(self) -> &'a [LeafOrNode<T>] { &self.0[..] }
}

impl<T> Asterism<T> {
    pub fn join(subs: Vec<Asterism<T>>) -> Asterism<T> {
        let mut res = vec![];
        if subs.len() == 0 {
            return Asterism(vec![LeafOrNode::Node(0)]);
        }
        if subs[0].0.len() != 0 {
            match subs[0].0[0] {
                LeafOrNode::Leaf(_) => {
                    let mut res = vec![LeafOrNode::PackedNodes];
                    for mut leaf_asterism in subs {
                        if !leaf_asterism.is_leaf() {
                            icp!("Not a valid leaf");
                        }
                        res.push(leaf_asterism.0.remove(0));
                    }
                    return Asterism(res);
                }
                _ => {}
            }
        }

        for mut aster in subs {
            res.push(LeafOrNode::Node(aster.0.len()));
            res.append(&mut aster.0);
        }
        Asterism(res)
    }

    pub fn from_leaf(leaf: T) -> Asterism<T> { Asterism(vec![LeafOrNode::Leaf(leaf)]) }

    pub fn from_depth_1(leaves: Vec<T>) -> Asterism<T> {
        let mut res = vec![LeafOrNode::PackedNodes];
        for leaf in leaves {
            res.push(LeafOrNode::Leaf(leaf))
        }

        Asterism(res)
    }
}

impl<'a, T: Clone> AsterismSlice<'a, T> {
    pub fn to_asterism(self) -> Asterism<T> { Asterism(self.0.to_vec()) }
}

impl<T: fmt::Debug> fmt::Debug for AsterismSlice<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.is_leaf() {
            write!(f, "{:?}", self.as_leaf())
        } else {
            write!(f, "[")?;
            let mut first = true;
            for ref sub in self.march() {
                if !first {
                    write!(f, " ")?;
                }
                write!(f, "{:?}", sub)?;
                first = false;
            }
            write!(f, "]")
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Asterism<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.as_slice().fmt(f) }
}

impl<T: fmt::Display> fmt::Display for AsterismSlice<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.is_leaf() {
            write!(f, "{}", self.as_leaf())
        } else {
            write!(f, "[")?;
            let mut first = true;
            for ref sub in self.march() {
                if !first {
                    write!(f, " ")?;
                }
                write!(f, "{}", sub)?;
                first = false;
            }
            write!(f, "]")
        }
    }
}

impl<T: fmt::Display> fmt::Display for Asterism<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.as_slice().fmt(f) }
}

impl<T: fmt::Debug> Asterism<T> {
    /// For internal debugging only
    fn show(&self) {
        for elt in &self.0 {
            match elt {
                LeafOrNode::Node(n) => print!("N{} ", n),
                LeafOrNode::PackedNodes => print!("PN "),
                LeafOrNode::Leaf(l) => print!("L{:?} ", l),
            }
        }
    }
}

#[test]
fn asterism_basics() {
    let abc = Asterism::from_depth_1(vec!["a", "b", "c"]);

    assert_eq!(abc.as_slice().as_depth_1().collect::<Vec<_>>(), vec![&"a", &"b", &"c"]);

    let (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o) =
        (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14);

    let a_through_i = Asterism::join(vec![
        Asterism::from_depth_1(vec![a, b]),
        Asterism::from_depth_1(vec![c]),
        Asterism::from_depth_1(vec![d, e]),
        Asterism::from_depth_1(vec![f, g]),
        Asterism::from_depth_1(vec![h, i]),
    ]);

    let a_through_m = Asterism::join(vec![
        a_through_i,
        Asterism::join(vec![]), // Empty `Asterism`s can be deeper than they look
        Asterism::join(vec![Asterism::from_depth_1(vec![j, k, l, m])]),
    ]);

    let a_through_o = Asterism::join(vec![
        a_through_m,
        Asterism::join(vec![Asterism::join(vec![
            Asterism::from_depth_1(vec![n]),
            Asterism::from_depth_1(vec![o]),
        ])]),
    ]);

    assert_eq!(
        format!("{}", a_through_o),
        "[[[[0 1] [2] [3 4] [5 6] [7 8]] [[]] [[9 10 11 12]]] [[[13] [14]]]]"
    );

    let mut expected_d1 = 0;
    let mut expected_m = 0;
    for m in a_through_o.march() {
        for mm in m.march() {
            for mmm in mm.march() {
                for mmmm in mmm.as_depth_1() {
                    assert_eq!(*mmmm, expected_d1);
                    expected_d1 += 1;
                }
                for mmmm in mmm.march() {
                    assert_eq!(*mmmm.as_leaf(), expected_m);
                    expected_m += 1;
                }
            }
        }
    }
    assert_eq!(15, expected_d1);
    assert_eq!(15, expected_m);

    let d1 = Asterism::from_depth_1(vec![vec![1, 3], vec![2, 3]]);

    for v in d1.as_depth_1() {
        assert_eq!(v.len(), 2)
    }
}
