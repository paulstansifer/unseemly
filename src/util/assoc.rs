use std::rc::Rc;
use std::clone::Clone;


#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Assoc<K: PartialEq, V> {
    n: Option<Rc<AssocNode<K, V>>>
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct AssocNode<K : PartialEq, V> {
    k: K,
    v: V,
    next: Assoc<K,V>
}

impl<K : PartialEq, V>  Assoc<K, V> {
    fn find(&self, target: &K) -> Option<&V> {
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

    fn set(&self, k: K, v: V) -> Assoc<K, V> {
        Assoc{
            n: Some(Rc::new(AssocNode {
                k: k, v: v, next: Assoc { n: self.n.clone() }
        }))}
    }

    fn new() -> Assoc<K, V> {
        Assoc{ n: None }
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
