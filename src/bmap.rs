use arrayvec::ArrayVec;
use std::mem;
use std::ptr::null_mut;
use std::default::Default;
use std::borrow::Borrow;
use std::fmt::Debug;

use std::ops::{
    Index,
};

const MAX_ORDER: usize = 12;

#[derive(Debug)]
struct Entry<K, V> {
    keys: ArrayVec<[K; MAX_ORDER - 1]>,
    values: ArrayVec<[V; MAX_ORDER - 1]>,
    children: ArrayVec<[Box<Entry<K, V>>; MAX_ORDER]>,
    parent: *mut Entry<K, V>,
}

impl<K, V> Entry<K, V>
    where K: Ord
{
    fn new() -> Self {
        Entry {
            keys: ArrayVec::new(),
            values: ArrayVec::new(),
            children: ArrayVec::new(),
            parent: null_mut(),
        }
    }

    fn max_order() -> usize { MAX_ORDER }
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
        // keys:      [ b d f ]    ->  [ b ] d [ f ]
        // children: [ a c e g ]   -> [ a c ] [ e g ]
        // keys:      [ 1 3 5 7 ]  ->  [ 1 3 ] 5 [ 7 ]
        // children: [ 0 2 4 6 8 ] -> [ 0 2 4 ] [ 6 8 ]
        right.keys.extend(self.keys.drain(1 + Self::median_key_index()..));
        right.values.extend(self.values.drain(1 + Self::median_key_index()..));
        let median_key = self.keys.pop().unwrap();
        let median_value = self.values.pop().unwrap();
        if !self.is_leaf() {
            right.children.extend(self.children.drain(1 + Self::median_key_index()..));
            let right_parent: *mut _ = &mut *right;
            for child in &mut right.children {
                child.parent = right_parent;
            }
        }
        (median_key, median_value, right)
    }

    /// Return (is_equal, best_position)
    fn find<Q: ?Sized>(&self, key: &Q) -> (bool, usize)
        where K: Borrow<Q>,
              Q: Ord,
    {
        // FIXME: When .max_order() is large, use binary search
        // find lower bound:
        // index where keys[i] < key for all i < index
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

    fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
        where K: Borrow<Q>,
              Q: Ord,
    {
        let (has, lower_bound) = self.find(key);
        if has {
            true
        } else if self.is_leaf() {
            false
        } else {
            self.children[lower_bound].contains_key(key)
        } 
    }

    fn find_value<Q: ?Sized>(&self, key: &Q) -> Option<&V>
        where K: Borrow<Q>,
              Q: Ord,
    {
        let (has, lower_bound) = self.find(key);
        if has {
            Some(self.value_at(lower_bound))
        } else if self.is_leaf() {
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
            Some(self.value_at_mut(lower_bound))
        } else if self.is_leaf() {
            None
        } else {
            self.children[lower_bound].find_value_mut(key)
        } 
    }

    fn value_at(&self, index: usize) -> &V {
        &self.values[index]
    }

    fn value_at_mut(&mut self, index: usize) -> &mut V {
        &mut self.values[index]
    }

    fn insert(&mut self, key: K, value: V, child: Option<Box<Entry<K, V>>>) {
        let (has, pos) = self.find(&key);
        debug_assert!(!has);
        self.insert_at(pos, key, value, child);
    }

    fn insert_at(&mut self, pos: usize, key: K, value: V,
                 child: Option<Box<Entry<K, V>>>) {
        debug_assert!(!self.full());
        self.keys.insert(pos, key);
        self.values.insert(pos, value);
        if let Some(child_) = child {
            self.children.insert(pos + 1, child_);
        }
    }

    fn insert_in_root(&mut self, key: K, value: V,
                      left: Box<Entry<K, V>>, right: Box<Entry<K, V>>)
    {
        debug_assert!(self.keys.len() == 0);
        debug_assert!(self.values.len() == 0);
        debug_assert!(self.children.len() == 0);
        self.keys.push(key);
        self.values.push(value);
        self.children.push(left);
        self.children.push(right);
    }

    fn update(&mut self, key: &K, value: V) -> V {
        let (has, pos) = self.find(key);
        debug_assert!(has);
        let existing = mem::replace(self.value_at_mut(pos), value);
        existing
    }

    /// in order visit of the btree
    fn _visit_inorder(&self, level: usize, f: &mut FnMut(usize, &K))
        where K: Debug, V: Debug,
    {
        let mut keys = self.keys.iter();
        let children = self.children.iter();
        if self.is_leaf() {
            if !self.parent.is_null() {
                unsafe {
                println!("Parent points to: {:?}", (*self.parent).keys);
                }
            }
            for key in keys {
                f(level, key);
            }
        } else {
            for child in children {
                child._visit_inorder(level + 1, f);
                match keys.next() {
                    Some(key) => f(level, key),
                    None => {}
                }
            }
        }
    }


}

#[derive(Debug)]
pub struct Bmap<K, V> {
    length: usize,
    root: Box<Entry<K, V>>,
}

use self::Insert::*;
enum Insert<K, V> {
    Split((K, V), K, V, Box<Entry<K, V>>),
    Updated(V),
    Inserted,
}

impl<K, V> Bmap<K, V>
    where K: Ord
{
    pub fn new() -> Self {
        Bmap {
            length: 0,
            root: Box::new(Entry::new()),
        }
    }

    pub fn len(&self) -> usize { self.length }

    pub fn contains<Q: ?Sized>(&self, key: &Q) -> bool
        where K: Borrow<Q>,
              Q: Ord,
    {
        self.root.contains_key(key)
    }

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
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        /* Top-down insertion:
         * Search downwards to find a leaf where we can insert the key.
         * Don't step into any full node without splitting it, and pushing
         * its median key into the parent. */

        fn insert_key<K, V>(entry: &mut Box<Entry<K, V>>, mut kv: (K, V)) -> Insert<K, V>
            where K: Ord
        {
            loop {
                if entry.full() {
                    let (median_k, median_v, right_child) = entry.split();
                    return Split(kv, median_k, median_v, right_child)
                }

                let (has_key, best_pos) = entry.find(&kv.0);
                if has_key {
                    return Updated(entry.update(&kv.0, kv.1));
                } else if entry.is_leaf() {
                    entry.insert_at(best_pos, kv.0, kv.1, None);
                    return Inserted;
                }

                match insert_key(&mut entry.children[best_pos], kv) {
                    Split(kv_, median_k, median_v, mut right_child) => {
                        right_child.parent = &mut **entry;
                        entry.insert(median_k, median_v, Some(right_child));
                        kv = kv_;
                    }
                    other => return other,
                }
            }
        }

        let mut kv = (key, value);
        loop {
            let root = &mut self.root;
            match insert_key(root, kv) {
                Split(kv_, median_k, median_v, mut right_child) => {
                    // Root was split, replace it with a new empty node,
                    // left side: old root
                    // right side: right_child
                    let mut left_child = mem::replace(root, Box::new(Entry::new()));
                    root.parent = null_mut();
                    left_child.parent = &mut **root;
                    right_child.parent = &mut **root;
                    root.insert_in_root(median_k, median_v,
                                        left_child, right_child);
                    kv = kv_;
                }
                Updated(v) => { return Some(v) }
                Inserted => { self.length += 1; return None }
            }
        }
    }

    pub fn iter(&self) -> Iter<K, V> {
        new_iter(self)
    }
}

impl<'a, K, V, Q: ?Sized> Index<&'a Q> for Bmap<K, V>
    where K: Ord + Borrow<Q>,
          Q: Ord,
{
    type Output = V;
    fn index(&self, index: &'a Q) -> &V {
        self.get(index).expect("Key error in Bmap")
    }
}

impl<K: Ord, V> Default for Bmap<K, V> {
    fn default() -> Self { Bmap::new() }
}

pub struct Iter<'a, K: 'a + Ord, V: 'a> {
    entry: &'a Entry<K, V>,
    index: usize,
}

fn new_iter<K: Ord, V>(map: &Bmap<K, V>) -> Iter<K, V> {
    // find and focus the lower bound
    let mut entry = &map.root;
    while !entry.is_leaf() {
        entry = &entry.children[0];
    }
    Iter {
        entry: entry,
        index: 0,
    }
}

impl<'a, K: Ord, V> Iter<'a, K, V> {
    unsafe fn parent_of(entry: &Entry<K, V>) -> Option<&Entry<K, V>> {
        if entry.parent.is_null() {
            None
        } else {
            Some(&*entry.parent)
        }
    }
}

impl<'a, K: Ord, V> Iterator for Iter<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        let mut entry = self.entry;
        debug_assert!(entry.is_leaf());
        let index = self.index;
        if index < entry.keys.len() {
            self.index += 1;
            return Some(&entry.keys[index]);
        } else {
            let last_key = entry.keys.last().unwrap();
            loop {
                entry = match unsafe { Iter::parent_of(entry) } {
                    None => break,
                    Some(parent) => parent,
                };
                let (eq, lower_bound) = entry.find(last_key);
                debug_assert!(!eq);
                if lower_bound == entry.keys.len() {
                    continue; // continue popping upwards
                }
                let next_key = Some(&entry.keys[lower_bound]);
                // dig down to successor
                self.index = 0;
                entry = &entry.children[lower_bound + 1];
                while !entry.is_leaf() {
                    entry = &entry.children[0];
                }
                self.entry = entry;
                return next_key;
            }
        }
        None
    }
}

#[test]
fn test_new() {
    let mut bp = Bmap::new();
    for x in vec![0, 2, 4, 6, 8, 10, 3, 1, 7, 5, 11, 13] {
        bp.insert(x, ());
    }

    /*
    bp.root._visit_inorder(0, &mut |indent, key| {
        for _ in 0..indent {
            print!("  ");
        }
        println!("{:?}", key);
    });
    */
    for elt in bp.iter() {
        println!("Iter: {:?}", elt);
    }
    println!("{:?}", bp);

    let mut bp = Bmap::new();
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
    let mut bp = Bmap::new();
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
/// Create a **Bmap** from a list of key-value pairs
///
/// ## Example
///
/// ```
/// #[macro_use]
/// extern crate bmap;
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
            let mut _map = $crate::Bmap::new();
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
    let old = m.insert("a", 2);
    assert_eq!(old, Some(1));
    *m.get_mut("a").unwrap() = 3;
    assert_eq!(m["a"], 3);
}

#[test]
fn test_lookup_borrow() {
    let m = bmap!{
        vec![1, 2] => 0,
        vec![1, 3] => 1,
        vec![2, 2] => 2,
        vec![2, 3] => 3,
    };
    assert_eq!(m[&[1, 2][..]], 0);
    assert_eq!(m[&[2, 2][..]], 2);
}


#[test]
fn test_generic() {
    let mut bp = Bmap::new();
    for word in "a short treatise on rusts and other fungi".split_whitespace() {
        bp.insert(word, word);
    }
    assert!(bp.contains(&"rusts"));
    assert!(bp.contains(&"fungi"));
}

