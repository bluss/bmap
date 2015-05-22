use arrayvec::ArrayVec;
use std::mem;
use std::ptr;

const MAX_ORDER: usize = 6;
pub type K = u8;

#[derive(Debug)]
struct Entry<K> {
    keys: ArrayVec<[K; MAX_ORDER - 1]>,
    children: ArrayVec<[Box<Entry<K>>; MAX_ORDER]>,
}

use std::iter::Enumerate;
#[inline]
pub fn enumerate<I: IntoIterator>(iter: I) -> Enumerate<I::IntoIter> {
    iter.into_iter().enumerate()
}

impl<K> Entry<K>
    where K: Ord
{
    fn new() -> Self {
        Entry {
            keys: ArrayVec::new(),
            children: ArrayVec::new(),
        }
    }

    fn max_order() -> usize { 6 }
    fn median_key_index() -> usize { (Self::max_order() - 1) / 2 }

    fn is_leaf(&self) -> bool { self.children.len() == 0 }
    //fn order(&self) -> usize { self.children.len() }
    fn full(&self) -> bool { self.keys.len() == self.keys.capacity() }

    // split a node and return the median key and new child
    fn split(&mut self) -> (K, Box<Entry<K>>) {
        debug_assert!(self.full());

        // new right side tree
        let mut right = Box::new(Entry::new());

        /* Split keys and children between `left` and `right` */
        // [ 0 1 2 3 ] -> [ 0 1 ] (2) [ 3 ]
        // keys: [ 0 1 2 3 ] ->  [ 0 1 ] (2) [ 3 ]
        // children: [ 0 1 2 3 4 ] -> [ 0 1 2 ] [ 3 4 ]
        right.keys.extend(self.keys.drain(1 + Self::median_key_index()..));
        let median_key = self.keys.remove(Self::median_key_index()).unwrap();
        if !self.is_leaf() {
            right.children.extend(self.children.drain(1 + Self::median_key_index()..));
        }
        (median_key, right)
    }

    fn find(&self, key: &K) -> (bool, usize) {
        // find lower bound
        let mut i = 0;
        for k in &self.keys {
            if k >= key {
                if k == key {
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

    fn insert(&mut self, key: K, child: Option<Box<Entry<K>>>) {
        let (has, pos) = self.find(&key);
        debug_assert!(!has);
        debug_assert!(!self.full());
        self.keys.insert(pos, key);
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
pub struct Bplus<K> {
    length: usize,
    root: Box<Entry<K>>,
}

use self::Task::*;
enum Task<K> {
    Split(K, K, Box<Entry<K>>),
    //Insert(K),
    DoneExists,
    DoneInserted,
}


impl<K> Bplus<K>
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

    /// Insert **key**
    pub fn insert(&mut self, mut key: K) {

        /* Top-down insertion:
         * Search downwards to find a leaf where we can insert the key.
         * Don't step into any full node without splitting it, and pushing
         * its median key into the parent. */

        fn insert_key<K>(iter: &mut Box<Entry<K>>, mut key: K) -> Task<K>
            where K: Ord
        {
            loop {
                if iter.full() {
                    let (median_key, right_child) = iter.split();
                    //println!("Got median: {:?}, child: {:?}", median_key, right_child);
                    return Split(key, median_key, right_child)
                }

                let (has_key, lower_bound) = iter.find(&key);
                if has_key {
                    return DoneExists;
                }
                if iter.is_leaf() {
                    iter.insert(key, None);
                    return DoneInserted;
                }

                match insert_key(&mut iter.children[lower_bound], key) {
                    Split(old_key, median_key, right_child) => {
                        iter.insert(median_key, Some(right_child));
                        key = old_key;
                    }
                    other => return other,
                }
            }
        }

        loop {
            let iter = &mut self.root;
            match insert_key(iter, key) {
                Split(old_key, median_key, right_child) => {
                    // root will have
                    // left side: old root
                    // right side: right_child
                    let mut root = Box::new(Entry::new());
                    mem::swap(&mut root, iter);
                    iter.children.push(root);
                    iter.insert(median_key, Some(right_child));
                    key = old_key;
                }
                DoneExists => break,
                DoneInserted => { self.length += 1; break }
            }
        }
    }
}


#[test]
fn test_new() {
    let mut bp = Bplus::new();
    /*
    println!("{:?}", bp);
    bp.insert(0);
    println!("{:?}", bp);
    bp.insert(3);
    println!("{:?}", bp);
    bp.insert(1);
    println!("{:?}", bp);
    */
    for x in vec![0, 2, 4, 6, 8, 10, 3, 1, 7, 5, 11, 13] {
        bp.insert(x);
        println!("{:?}", bp);
        bp.root.visit_inorder(0, &mut |indent, key| {
            for _ in 0..indent {
                print!("  ");
            }
            println!("{:?}", key);
        });
    }

    let mut bp = Bplus::new();
    for x in (0..20) {
        bp.insert(x);
        println!("{:?}", bp);
        bp.root.visit_inorder(0, &mut |indent, key| {
            for _ in 0..indent {
                print!("  ");
            }
            println!("{:?}", key);
        });
    }
}

#[test]
fn test_insert() {
    let mut bp = Bplus::new();
    bp.insert(0);
    assert!(bp.contains(&0));
    for x in 1..100 {
        bp.insert(x);
    }
    for x in 0..100 {
        assert!(bp.contains(&x));
    }
}

