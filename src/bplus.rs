use arrayvec::ArrayVec;

type Entries = ArrayVec<[Entry; 6]>;

const ORDER: usize = 7;
pub type K = u8;

#[derive(Debug)]
struct Entry {
    keys: ArrayVec<[K; ORDER - 1]>,
    children: ArrayVec<[Box<Entry>; ORDER]>,
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

    fn is_leaf(&self) -> bool { self.children.len() == 0 }
    //fn order(&self) -> usize { self.children.len() }
    fn full(&self) -> bool { self.keys.len() == self.keys.capacity() }

    // split a node and return the median key and new child
    fn split(&mut self) -> (K, Box<Entry>) {
        debug_assert!(self.full());
        panic!()
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

    fn insert(&mut self, key: K) {
        let (has, pos) = self.find(&key);
        debug_assert!(!has);
        debug_assert!(!self.full());
        self.keys.insert(pos, key);
    }

}

#[derive(Debug)]
pub struct Bplus {
    length: usize,
    root: Entry,
}


impl Bplus {
    pub fn new() -> Self {
        Bplus {
            length: 0,
            root: Entry::new(),
        }
    }

    pub fn insert(&mut self, key: K) {
        /* Top-down insertion:
         * Search downwards to find a leaf where we can insert the key.
         * Don't step into any full node without splitting it, and pushing
         * its median key into the parent. */
        //let mut parent = None;
        let mut parent = None::<()>;
        let mut iter = &mut self.root;
        loop {
            if iter.full() {
                let (median_key, child) = iter.split();
                match parent {
                    Some(par) => {
                    }
                    None => {}
                }
            }
            let (has_key, lower_bound) = iter.find(&key);
            if has_key {
                return
            }
            if iter.is_leaf() {
                break;
            }

            iter = &mut {iter}.children[lower_bound];

            break;

        }
        iter.insert(key);
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
}

