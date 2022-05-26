use crate::runtime::reify::Reifiable;
use std::{clone::Clone, fmt, hash::Hash, rc::Rc};

extern crate im_rc;

use self::im_rc::HashMap;

thread_local! {
    static next_id: std::cell::RefCell<u32> = std::cell::RefCell::new(0);
}

fn get_next_id() -> u32 {
    next_id.with(|id| {
        let res = *id.borrow();
        *id.borrow_mut() += 1;
        res
    })
}

/// A persistent key-value store. `clone`, `set`, and `find` are sub-linear.
#[derive(Clone)]
pub struct Assoc<K, V>
where K: Eq + Hash + Clone
{
    hamt: HashMap<K, V>,
    // TODO: this is a hack, needed for `almost_ptr_eq`,
    //  which in turn is only needed in `earley.rs`.
    // `earley.rs` should use interning as a replacement optimization, and `id` should be removed.
    id: u32,
}

impl<K: Eq + Hash + Clone, V: Clone + PartialEq> PartialEq for Assoc<K, V> {
    // `id` is not relevant for equality
    fn eq(&self, other: &Self) -> bool { self.hamt == other.hamt }
}

impl<K: Eq + Hash + Clone, V: Clone + Eq> Eq for Assoc<K, V> {}

impl<K: Eq + Hash + Clone, V: Clone> Default for Assoc<K, V> {
    fn default() -> Self { Self::new() }
}

impl<K: Eq + Hash + Clone + Reifiable, V: Clone + Reifiable> Reifiable for Assoc<K, V> {
    fn ty_name() -> crate::name::Name { crate::name::n("Assoc") }

    fn concrete_arguments() -> Option<Vec<crate::ast::Ast>> {
        Some(vec![K::ty_invocation(), V::ty_invocation()])
    }

    fn reify(&self) -> crate::runtime::eval::Value {
        let res: Vec<_> =
            self.hamt.iter().map(|(k, v)| Rc::new((k.clone(), v.clone()).reify())).collect();

        crate::runtime::eval::Value::Sequence(res)
    }

    fn reflect(v: &crate::runtime::eval::Value) -> Self {
        let mut res = Assoc::<K, V>::new();

        extract!((v) crate::runtime::eval::Value::Sequence = (ref parts) => {
            for part in parts {
                let (k_part, v_part) = <(K,V)>::reflect(&**part);
                res = res.set(k_part, v_part);
            }
        });
        res
    }
}

impl<K: Eq + Hash + Clone + fmt::Debug, V: Clone + fmt::Debug> fmt::Debug for Assoc<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "⟦")?;
        let mut first = true;
        for (k, v) in self.iter_pairs() {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{:#?} ⇒ {:#?}", k, v)?;
            first = false;
        }
        write!(f, "⟧")
    }
}

impl<K: Eq + Hash + Clone + fmt::Display, V: Clone + fmt::Display> fmt::Display for Assoc<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "⟦")?;
        let mut first = true;
        for (k, v) in self.iter_pairs() {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{} ⇒ {}", k, v)?;
            first = false;
        }
        write!(f, "⟧")
    }
}

// Maybe we should admit that `K` is always `Name` (=`usize`) and stop taking references to it?
// Maybe we shouldn't even parameterize over it?
impl<K: Eq + Hash + Clone, V: Clone> Assoc<K, V> {
    fn from_hamt(hamt: HashMap<K, V>) -> Self { Assoc { hamt: hamt, id: get_next_id() } }

    pub fn new() -> Self { Self::from_hamt(HashMap::new()) }

    pub fn find(&self, key: &K) -> Option<&V> { self.hamt.get(key) }

    pub fn set(&self, key: K, value: V) -> Self { Self::from_hamt(self.hamt.update(key, value)) }

    pub fn set_assoc(&self, other: &Self) -> Self {
        Self::from_hamt(other.hamt.clone().union(self.hamt.clone()))
    }

    pub fn mut_set(&mut self, key: K, value: V) { self.hamt.insert(key, value); }

    pub fn single(key: K, value: V) -> Self { Self::new().set(key, value) }

    pub fn empty(&self) -> bool { self.hamt.is_empty() }

    pub fn iter_pairs(&self) -> im_rc::hashmap::Iter<K, V> { self.hamt.iter() }

    pub fn iter_keys(&self) -> im_rc::hashmap::Keys<K, V> { self.hamt.keys() }

    pub fn iter_values(&self) -> im_rc::hashmap::Values<K, V> { self.hamt.values() }

    pub fn map<NewV: Clone, F>(&self, mut f: F) -> Assoc<K, NewV>
    where F: FnMut(&V) -> NewV {
        self.map_borrow_f(&mut f)
    }

    pub fn map_borrow_f<'assoc, NewV: Clone, F>(&'assoc self, f: &mut F) -> Assoc<K, NewV>
    where F: FnMut(&'assoc V) -> NewV {
        Assoc::<K, NewV>::from_hamt(self.hamt.iter().map(|(k, ref v)| (k.clone(), f(v))).collect())
    }
    pub fn keyed_map_borrow_f<NewV: Clone, F>(&self, f: &mut F) -> Assoc<K, NewV>
    where F: FnMut(&K, &V) -> NewV {
        Assoc::<K, NewV>::from_hamt(
            self.hamt.iter().map(|(k, ref v)| (k.clone(), f(k, v))).collect(),
        )
    }

    pub fn map_with<OtherV: Clone, NewV: Clone>(
        &self,
        other: &Assoc<K, OtherV>,
        f: &dyn Fn(&V, &OtherV) -> NewV,
    ) -> Assoc<K, NewV> {
        Assoc::<K, NewV>::from_hamt(
            self.hamt
                .clone()
                .intersection_with_key(other.hamt.clone(), |_, ref v_l, ref v_r| f(v_l, v_r)),
        )
    }

    pub fn keyed_map_with<OtherV: Clone, NewV: Clone>(
        &self,
        other: &Assoc<K, OtherV>,
        f: &dyn Fn(&K, &V, &OtherV) -> NewV,
    ) -> Assoc<K, NewV> {
        Assoc::<K, NewV>::from_hamt(
            self.hamt
                .clone()
                .intersection_with_key(other.hamt.clone(), |ref k, ref v_l, ref v_r| {
                    f(k, v_l, v_r)
                }),
        )
    }

    pub fn find_value<'assoc, 'f>(&'assoc self, target: &'f V) -> Option<&'assoc K>
    where V: PartialEq {
        self.hamt.iter().find(|(_, v)| v == &target).map(|(k, _)| k)
    }

    pub fn find_or_panic<'assoc, 'f>(&'assoc self, target: &'f K) -> &'assoc V
    where K: fmt::Display {
        self.find(target).unwrap_or_else(|| icp!("'{}' not found in {}", target, self.map(|_| "…")))
    }

    pub fn remove<'assoc, 'f>(&'assoc mut self, target: &'f K) -> Option<V> {
        self.hamt.remove(target)
    }

    pub fn remove_or_panic<'assoc, 'f>(&'assoc mut self, target: &'f K) -> V
    where K: fmt::Display {
        self.hamt
            .remove(target)
            .unwrap_or_else(|| icp!("{} not found in {}", target, self.map(|_| "…")))
    }

    // Generates a version of `self` that lacks the entries that have identical values in `other`
    pub fn cut_common(&self, other: &Assoc<K, V>) -> Assoc<K, V>
    where V: PartialEq {
        let mut hamt = self.hamt.clone();
        hamt.retain(|k, v| other.find(k) != Some(v));
        Self::from_hamt(hamt)
    }

    pub fn unset(&self, k: &K) -> Assoc<K, V> { Self::from_hamt(self.hamt.without(k)) }

    pub fn reduce<Out>(&self, red: &dyn Fn(&K, &V, Out) -> Out, base: Out) -> Out {
        self.hamt.iter().fold(base, |base, (k, v)| red(k, v, base))
    }
}

impl<K: Eq + Hash + Clone, V: Clone> Assoc<K, V> {
    pub fn almost_ptr_eq(&self, other: &Assoc<K, V>) -> bool {
        self.id == other.id // Only true if they are clones of each other
    }
}

impl<K: Eq + Hash + Clone, V: Clone, E: Clone> Assoc<K, Result<V, E>> {
    pub fn lift_result(self) -> Result<Assoc<K, V>, E> {
        let mut oks = vec![];
        for (k, res_v) in self.hamt.into_iter() {
            oks.push((k, res_v?))
        }
        Ok(Assoc::<K, V>::from_hamt(HashMap::from(oks)))
    }
}

#[test]
fn basic_assoc() {
    let mt: Assoc<i32, i32> = Assoc::new();
    let a1 = mt.set(5, 6);
    let a2 = a1.set(6, 7);
    let a_override = a2.set(5, 500);

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

    assert_eq!(a_override.unset(&5).find(&5), None);
    assert_eq!(a_override.unset(&6).find(&6), None);

    assert_eq!(a_override.unset(&6).find(&5), Some(&500));
    assert_eq!(a_override.unset(&5).find(&6), Some(&7));

    assert_eq!(a_override.unset(&-111).find(&5), Some(&500));
}

#[test]
fn assoc_equality() {
    let mt: Assoc<i32, i32> = Assoc::new();
    let a1 = mt.set(5, 6);
    let a2 = a1.set(6, 7);
    let a_override = a2.set(5, 500);

    let a2_opposite = mt.set(6, 7).set(5, 6);
    let a_override_direct = mt.set(5, 500).set(6, 7);

    assert_eq!(mt, Assoc::new());
    assert_eq!(a1, a1);
    assert!(a1 != mt);
    assert!(mt != a1);
    assert_eq!(a2, a2);
    assert_eq!(a2, a2_opposite);
    assert_eq!(a_override, a_override_direct);
    assert!(a2 != a_override);

    let a1_again = mt.set(5, 6);

    // Nothing shared: no-op
    assert_eq!(mt.cut_common(&mt), mt);
    assert_eq!(a1.cut_common(&mt), a1);
    assert_eq!(mt.cut_common(&a1), mt);

    // Everything shared: empty result
    assert_eq!(a1_again.cut_common(&a1), mt);
    assert_eq!(a_override_direct.cut_common(&a_override), mt);
    assert_eq!(a_override.cut_common(&a_override_direct), mt);
    assert_eq!(a1.cut_common(&a1), mt);
    assert_eq!(a2.cut_common(&a2), mt);

    // Partial share:
    assert_eq!(a2.cut_common(&a1), mt.set(6, 7));
    assert_eq!(a_override.cut_common(&a2), mt.set(5, 500));

    assert!(mt.almost_ptr_eq(&mt));
    assert!(a2.almost_ptr_eq(&a2));
    assert!(a_override_direct.almost_ptr_eq(&a_override_direct));
    assert!(!a2.almost_ptr_eq(&a2_opposite));
    // assert!(mt.almost_ptr_eq(&Assoc::new()));
}

#[test]
fn assoc_r_and_r_roundtrip() {
    use num::BigInt;
    let mt: Assoc<BigInt, BigInt> = Assoc::new();
    let a1 = mt.set(BigInt::from(5), BigInt::from(6));
    let a2 = a1.set(BigInt::from(6), BigInt::from(7));

    assert_eq!(mt, Assoc::<BigInt, BigInt>::reflect(&mt.reify()));
    assert_eq!(a2, Assoc::<BigInt, BigInt>::reflect(&a2.reify()));
}

#[test]
fn assoc_map() {
    let a1 = assoc_n!("x" => 1, "y" => 2, "z" => 3);
    assert_eq!(a1.map(|a| a + 1), assoc_n!("x" => 2, "y" => 3, "z" => 4));

    let a2 = assoc_n!("y" => -2, "z" => -3, "x" => -1);
    assert_eq!(a1.map_with(&a2, &|a, b| a + b), assoc_n!("x" => 0, "y" => 0, "z" => 0));
}

#[test]
fn assoc_reduce() {
    let a1 = assoc_n!("x" => 1, "y" => 2, "z" => 3);
    assert_eq!(a1.reduce(&|_key, a, b| a + b, 0), 6);

    let a1 = assoc_n!("x" => 1, "y" => 2, "z" => 3);
    assert_eq!(a1.reduce(&|key, a, b| if key.is("y") { b } else { a + b }, 0), 4);
}
