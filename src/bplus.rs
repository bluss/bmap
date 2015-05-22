use arrayvec::ArrayVec;
use std::mem;
use std::ptr;
use std::default::Default;
use std::borrow::Borrow;

use std::ops::{
    Index,
};

const MAX_ORDER: usize = 6;

#[derive(Debug)]
struct Entry<K, V> {
    keys: ArrayVec<[K; MAX_ORDER - 1]>,
    values: ArrayVec<[V; MAX_ORDER - 1]>,
    children: ArrayVec<[Box<Entry<K, V>>; MAX_ORDER]>,
}

use std::iter::Enumerate;
#[inline]
pub fn enumerate<I: IntoIterator>(iter: I) -> Enumerate<I::IntoIter> {
    iter.into_iter().enumerate()
}

impl<K, V> Entry<K, V>
    where K: Ord
{
    fn new() -> Self {
        Entry {
            keys: ArrayVec::new(),
            values: ArrayVec::new(),
            children: ArrayVec::new(),
        }
    }

    fn max_order() -> usize { 6 }
    fn median_key_index() -> usize { (Self::max_order() - 1) / 2 }

    fn is_leaf(&self) -> bool { self.children.len() == 0 }
    //fn order(&self) -> usize { self.children.len() }
    fn full(&self) -> bool { self.keys.len() == self.keys.capacity() }

    // split a node and return the median key and new child
    fn split(&mut self) -> (K, V, Box<Entry<K, V>>) {
        debug_assert!(self.full());

        // new right side tree
        let mut right = Box::new(Entry::new());

        /* Split keys and children between `left` and `right` */
        // [ 0 1 2 3 ] -> [ 0 1 ] (2) [ 3 ]
        // keys: [ 0 1 2 3 ] ->  [ 0 1 ] (2) [ 3 ]
        // children: [ 0 1 2 3 4 ] -> [ 0 1 2 ] [ 3 4 ]
        right.keys.extend(self.keys.drain(1 + Self::median_key_index()..));
        right.values.extend(self.values.drain(1 + Self::median_key_index()..));
        let median_key = self.keys.remove(Self::median_key_index()).unwrap();
        let median_value = self.values.remove(Self::median_key_index()).unwrap();
        if !self.is_leaf() {
            right.children.extend(self.children.drain(1 + Self::median_key_index()..));
        }
        (median_key, median_value, right)
    }

    fn find<Q: ?Sized>(&self, key: &Q) -> (bool, usize)
        where K: Borrow<Q>,
              Q: Ord,
    {
        // find lower bound
        let mut i = 0;
        for k in &self.keys {
            if k.borrow() >= key {
                if k.borrow() == key {
                    return (true, i);
                }
                break;
            }
            i += 1;
        }
        (false, i)
    }

    fn find_key(&self, key: &K) -> bool {
        let (has, lower_bound) = self.find(key);
        if has {
            return true;
        }
        if self.is_leaf() {
            false
        } else {
            self.children[lower_bound].find_key(key)
        } 
    }

    fn find_value<Q: ?Sized>(&self, key: &Q) -> Option<&V>
        where K: Borrow<Q>,
              Q: Ord,
    {
        let (has, lower_bound) = self.find(key);
        if has {
            return Some(&self.values[lower_bound]);
        }
        if self.is_leaf() {
            None
        } else {
            self.children[lower_bound].find_value(key)
        } 
    }

    fn find_value_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
        where K: Borrow<Q>,
              Q: Ord,
    {
        let (has, lower_bound) = self.find(key);
        if has {
            return Some(&mut self.values[lower_bound]);
        }
        if self.is_leaf() {
            None
        } else {
            self.children[lower_bound].find_value_mut(key)
        } 
    }

    fn insert(&mut self, key: K, value: V, child: Option<Box<Entry<K, V>>>) {
        let (has, pos) = self.find(&key);
        debug_assert!(!has);
        debug_assert!(!self.full());
        self.keys.insert(pos, key);
        self.values.insert(pos, value);
        match child {
            Some(child_) => {
                self.children.insert(pos + 1, child_);
            }
            None => {}
        }
    }

    /// in order visit of the btree
    fn visit_inorder(&self, level: usize, f: &mut FnMut(usize, &K)) {
        let mut keys = self.keys.iter();
        let mut children = self.children.iter();
        if self.is_leaf() {
            for key in keys {
                f(level, key);
            }
        } else {
            for child in children {
                child.visit_inorder(level + 1, f);
                match keys.next() {
                    Some(key) => f(level, key),
                    None => {}
                }
            }
        }
    }


}

#[derive(Debug)]
pub struct Bplus<K, V> {
    length: usize,
    root: Box<Entry<K, V>>,
}

use self::Task::*;
enum Task<K, V> {
    Split(K, V, K, V, Box<Entry<K, V>>),
    //Insert(K),
    DoneExists,
    DoneInserted,
}


impl<K, V> Bplus<K, V>
    where K: Ord
{
    pub fn new() -> Self {
        Bplus {
            length: 0,
            root: Box::new(Entry::new()),
        }
    }

    pub fn len(&self) -> usize { self.length }

    pub fn contains(&self, key: &K) -> bool { self.root.find_key(key) }

    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V>
        where K: Borrow<Q>,
              Q: Ord,
    {
        self.root.find_value(key)
    }

    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
        where K: Borrow<Q>,
              Q: Ord,
    {
        self.root.find_value_mut(key)
    }

    /// Insert **key**
    pub fn insert_default(&mut self, mut key: K)
        where V: Default
    {
        self.insert(key, V::default())
    }

    /// Insert **key**
    pub fn insert(&mut self, mut key: K, mut value: V) {

        /* Top-down insertion:
         * Search downwards to find a leaf where we can insert the key.
         * Don't step into any full node without splitting it, and pushing
         * its median key into the parent. */

        fn insert_key<K, V>(iter: &mut Box<Entry<K, V>>, mut key: K, mut value: V) -> Task<K, V>
            where K: Ord
        {
            loop {
                if iter.full() {
                    let (median_key, mval, right_child) = iter.split();
                    //println!("Got median: {:?}, child: {:?}", median_key, right_child);
                    return Split(key, value, median_key, mval, right_child)
                }

                let (has_key, lower_bound) = iter.find(&key);
                if has_key {
                    return DoneExists;
                }
                if iter.is_leaf() {
                    iter.insert(key, value, None);
                    return DoneInserted;
                }

                match insert_key(&mut iter.children[lower_bound], key, value) {
                    Split(old_k, old_v, median_k, median_v, right_child) => {
                        iter.insert(median_k, median_v, Some(right_child));
                        key = old_k;
                        value = old_v;
                    }
                    other => return other,
                }
            }
        }

        loop {
            let iter = &mut self.root;
            match insert_key(iter, key, value) {
                Split(old_k, old_v, median_k, median_v, right_child) => {
                    // root will have
                    // left side: old root
                    // right side: right_child
                    let mut root = Box::new(Entry::new());
                    mem::swap(&mut root, iter);
                    iter.children.push(root);
                    iter.insert(median_k, median_v, Some(right_child));
                    key = old_k;
                    value = old_v;
                }
                DoneExists => break,
                DoneInserted => { self.length += 1; break }
            }
        }
    }
}

impl<'a, K, V, Q: ?Sized> Index<&'a Q> for Bplus<K, V>
    where K: Ord + Borrow<Q>,
          Q: Ord,
{
    type Output = V;
    fn index(&self, index: &'a Q) -> &V {
        self.get(index).expect("Key error in Bplus")
    }
}


#[test]
fn test_new() {
    let mut bp = Bplus::new();
    for x in vec![0, 2, 4, 6, 8, 10, 3, 1, 7, 5, 11, 13] {
        bp.insert(x, ());
        /*
        println!("{:?}", bp);
        bp.root.visit_inorder(0, &mut |indent, key| {
            for _ in 0..indent {
                print!("  ");
            }
            println!("{:?}", key);
        });
        */
    }

    let mut bp = Bplus::new();
    for x in (0..20) {
        bp.insert(x, x);
        /*
        println!("{:?}", bp);
        bp.root.visit_inorder(0, &mut |indent, key| {
            for _ in 0..indent {
                print!("  ");
            }
            println!("{:?}", key);
        });
        */
    }
}

#[test]
fn test_insert() {
    let mut bp = Bplus::new();
    bp.insert(0, ());
    assert!(bp.contains(&0));
    for x in 1..100 {
        bp.insert(x, ());
    }
    for x in 0..100 {
        assert!(bp.contains(&x));
    }
}

#[macro_export]
/// Create a **Bplus** from a list of key-value pairs
///
/// ## Example
///
/// ```
/// #[macro_use]
/// extern crate bplus;
/// # fn main() {
///
/// let foo = bmap!{
///     "a" => 1,
///     "b" => 2,
/// };
/// assert_eq!(foo["a"], 1);
/// assert_eq!(foo["b"], 2);
/// assert_eq!(foo.get("c"), None);
/// # }
/// ```
macro_rules! bmap {
    // trailing comma case
    ($($key:expr => $value:expr,)+) => (bmap!($($key => $value),+));
    
    ( $($key:expr => $value:expr),* ) => {
        {
            let mut _map = $crate::Bplus::new();
            $(
                _map.insert($key, $value);
            )*
            _map
        }
    };
}

#[test]
fn test_insert_mutate() {
    let mut m = bmap!{
        "a" => 1,
        "b" => 1,
        "c" => 1,
    };
    assert_eq!(m["a"], 1);
    assert_eq!(m["c"], 1);
    *m.get_mut("a").unwrap() = 3;
    assert_eq!(m["a"], 3);
}


#[test]
fn test_generic() {
    let mut bp = Bplus::new();
    for word in "a short treatise on rusts and other fungi".split_whitespace() {
        bp.insert(word, word)
    }
    assert!(bp.contains(&"rusts"));
    assert!(bp.contains(&"fungi"));
}

