use arrayvec::ArrayVec;
use std::mem;
use std::ptr;

const MAX_ORDER: usize = 6;
pub type K = u8;

#[derive(Debug)]
struct Entry {
    keys: ArrayVec<[K; MAX_ORDER - 1]>,
    children: ArrayVec<[Box<Entry>; MAX_ORDER]>,
}

use std::iter::Enumerate;
#[inline]
pub fn enumerate<I: IntoIterator>(iter: I) -> Enumerate<I::IntoIter> {
    iter.into_iter().enumerate()
}

impl Entry {
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
    fn split(&mut self) -> (K, Box<Entry>) {
        debug_assert!(self.full());

        // new right side tree
        let mut right = Box::new(Entry::new());

        /* Split keys and children between `left` and `right` */
        // [ 0 1 2 3 ] -> [ 0 1 ] (2) [ 3 ]
        // keys: [ 0 1 2 3 ] ->  [ 0 1 ] (2) [ 3 ]
        // children: [ 0 1 2 3 4 ] -> [ 0 1 2 ] [ 3 4 ]
        right.keys.extend(self.keys.drain(1 + Self::median_key_index()..));
        let median_key = self.keys.remove(Self::median_key_index()).unwrap();
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

    fn insert(&mut self, key: K, child: Option<Box<Entry>>) {
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

}

#[derive(Debug)]
pub struct Bplus {
    length: usize,
    root: Box<Entry>,
}

use self::Task::*;
enum Task {
    Split(K, Box<Entry>),
    //Insert(K),
    DoneExists,
    DoneInserted,
}


impl Bplus {
    pub fn new() -> Self {
        Bplus {
            length: 0,
            root: Box::new(Entry::new()),
        }
    }

    pub fn insert(&mut self, key: K) {

        fn insert_key(iter: &mut Box<Entry>, key: K) -> Task {
            loop {
                if iter.full() {
                    let (median_key, right_child) = iter.split();
                    println!("Got median: {:?}, child: {:?}", median_key, right_child);
                    return Split(median_key, right_child)
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
                    Split(key, right_child) => {
                        iter.insert(key, Some(right_child));
                    }
                    other => return other,
                }
            }
            //parent = Some(iter);
            //iter = &mut {iter}.children[lower_bound];

        }

        loop {
            let iter = &mut self.root;
            match insert_key(iter, key) {
                Split(key, right_child) => {
                    let mut root = Box::new(Entry::new());
                    mem::swap(&mut root, iter);
                    iter.children.push(root);
                    iter.insert(key, Some(right_child));
                        
                    // root will have
                    // left side: old root
                    // right side: right_child
                    //
                    //mem::swap(&mut root, &mut self.root);
                    //root.insert(median_key, Some(child));
                    //let mut root = mem::replace(&mut self.root
                    //root.insert(
                }
                other => return,
            }
        }

        return;

        /* Top-down insertion:
         * Search downwards to find a leaf where we can insert the key.
         * Don't step into any full node without splitting it, and pushing
         * its median key into the parent. */
        //let mut parent = None;
        let mut parent = None::<&mut Entry>;
        let mut iter = &mut *self.root;
        loop {
            if iter.full() {
                let (median_key, right_child) = iter.split();
                println!("Got median: {:?}, child: {:?}", median_key, right_child);
                match parent.take() {
                    Some(par) => {
                        iter = par;
                        iter.insert(median_key, Some(right_child));
                    }
                    None => {
                        /* Split the root, update the it */
                        let mut root = Box::new(Entry::new());
                        // root will have
                        // left side: old root
                        // right side: right_child
                        //
                        //mem::swap(&mut root, &mut self.root);
                        //root.insert(median_key, Some(child));
                        //let mut root = mem::replace(&mut self.root
                        //root.insert(
                    }
                }
            }
            let (has_key, lower_bound) = iter.find(&key);
            if has_key {
                return
            }
            if iter.is_leaf() {
                break;
            }

            //parent = Some(iter);
            iter = &mut {iter}.children[lower_bound];

            break;

        }
        self.length += 1;
        iter.insert(key, None);
    }

}


#[test]
fn test_new() {
    let mut bp = Bplus::new();
    println!("{:?}", bp);
    bp.insert(0);
    println!("{:?}", bp);
    bp.insert(3);
    println!("{:?}", bp);
    bp.insert(1);
    println!("{:?}", bp);
    for x in 3..20 {
        bp.insert(x);
        println!("{:?}", bp);
    }
}

