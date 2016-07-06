use std::rc::Rc;
use std::clone::Clone;

use std::fmt;


// TODO: we can get rid of a lot of these `pub`s by making `Assoc` iterable

// Potential optimization: replace a run of ten nodes with a `HashMap`.
// Recursively replace runs of those, too...

#[derive(PartialEq, Eq)]
pub struct Assoc<K: PartialEq, V> {
    pub n: Option<Rc<AssocNode<K, V>>>
}

impl<K : PartialEq + Clone, V: Clone> Clone for Assoc<K, V> {
    fn clone(&self) -> Assoc<K, V> {
        self.map(&|rc| rc)
    }
}



#[derive(PartialEq, Eq, Clone)]
pub struct AssocNode<K : PartialEq, V> {
    pub k: K,
    pub v: V,
    pub next: Assoc<K,V>
}

impl<K : PartialEq, V> Assoc<K, V> {
    pub fn find<'assoc, 'f>(&'assoc self, target: &'f K) -> Option<&'assoc V> {
        match self.n {
            None => None,
            Some(ref node) => {
                if (*node).k == *target {
                    Some(&node.v)
                } else {
                    (*node).next.find(target)
                }
            }
        }
    }
    
    pub fn set(&self, k: K, v: V) -> Assoc<K, V> {
        Assoc{
            n: Some(Rc::new(AssocNode {
                k: k, v: v, next: Assoc { n: self.n.clone() }
        }))}
    }
    
    pub fn new() -> Assoc<K, V> {
        Assoc{ n: None }
    }
} 

impl<K: PartialEq + fmt::Debug, V: fmt::Debug> Assoc<K, V> {
    pub fn find_or_panic<'assoc, 'f>(&'assoc self, target: &'f K) -> &'assoc V {
        match self.find(target) {
            None => {
                panic!("{:?} not found in {:?}", target, self)
            },
            Some(ref v) => v
        }
    }
}

impl<K : PartialEq + fmt::Debug, V : fmt::Debug> fmt::Debug for Assoc<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "<|"));
        let mut cur = &self.n;
        let mut first = true;
        while let &Some(ref node) = cur {
            if !first { try!(write!(f, ", ")); }
            try!(write!(f, "{:?} => {:?}", node.k, node.v));
            first = false;
            cur = &node.next.n;
        }
        write!(f, "|>")
    }
}

impl<K : PartialEq + Clone, V : Clone> Assoc<K, V> {

    pub fn set_assoc(&self, other: &Assoc<K, V>) -> Assoc<K, V> {
        match other.n {
            None => (*self).clone(),
            Some(ref node) => {
                self.set_assoc(&node.next).set(node.k.clone(), node.v.clone())
            }
        }
    }
    
    pub fn map<NewV>(&self, f: &Fn(V) -> NewV) -> Assoc<K, NewV> {
        match self.n {
            None => Assoc{ n: None },
            Some(ref node) => {
                Assoc{ 
                    n: Some(Rc::new(AssocNode {
                        k: node.k.clone(), v: f(node.v.clone()), 
                        next: node.next.map(f)
                    }))
                }
            }
        }
    }
}

#[test]
fn test_assoc() {
    let mt : Assoc<i32, i32> = Assoc::new();
    let a1 = mt.set(5,6);
    let a2 = a1.set(6,7);
    let a_override = a2.set(5,500);

    assert_eq!(mt.find(&5), None);
    assert_eq!(a1.find(&6), None);
    assert_eq!(a2.find(&999), None);
    assert_eq!(a_override.find(&999), None);
    assert_eq!(a1.find(&5), Some(&6));
    assert_eq!(a2.find(&5), Some(&6));
    assert_eq!(a2.find(&6), Some(&7));
    assert_eq!(a2.find(&5), Some(&6));
    assert_eq!(a_override.find(&5), Some(&500));
    assert_eq!(a_override.find(&6), Some(&7));
}
