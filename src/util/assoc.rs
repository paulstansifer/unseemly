use std::rc::Rc;
use std::clone::Clone;

type Assoc<K, V> = Option<Rc<AssocNode<K, V>>>;

#[derive(Debug)]
struct AssocNode<K : PartialEq, V> {
    k: K,
    v: V,
    next: Assoc<K,V>
}

trait AssocFind<K: PartialEq, V> {
    fn find(&self, &K) -> Option<&V>;
    fn set(&self, K, V) -> Assoc<K, V>;
}

impl<K : PartialEq, V> AssocFind<K, V> for Assoc<K, V> {
    fn find(&self, target: &K) -> Option<&V> {
        match self {
            &None => None,
            &Some(ref node) => {
                if (*node).k == *target {
                    Some(&node.v)
                } else {
                    (*node).next.find(target)
                }
            }
        }
    }

    fn set(&self, k: K, v: V) -> Assoc<K, V> {
        Some(Rc::new(AssocNode {
            k: k, v: v, next: self.clone()
        }))
    }
}

#[test]
fn test_assoc() {
    let mt : Assoc<i32, i32> = None;
    let a1 = mt.set(5,6);
    let a2 = a1.set(6,7);
    let a_override = a2.set(5,500);
    let a_override2 = a2.set(5,500);

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
