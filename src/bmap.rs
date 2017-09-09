// bmap - B-Tree map
// Copyright (C) 2015 Ulrik Sverdrup
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

//! **Bmap\<K, V\>** is an associative array implemented with a B-Tree.
//!
//!
//!

use arrayvec::ArrayVec;
use std::mem;
use std::ptr::null_mut;
use std::default::Default;
use std::borrow::Borrow;
use odds;

#[cfg(test)]
extern crate rand;
#[cfg(test)]
use rand::{Rng, ChaChaRng, SeedableRng};

extern crate itertools as it;
use self::it::ZipSlices;

#[cfg(test)]
use odds::fix;

use odds::ptr_eq;

use std::ops::{
    Index,
    IndexMut,
};

// B=6, and MAX_ORDER = 2 * B in Btreemap

const MAX_ORDER: usize = 12;

#[derive(Debug)]
struct Entry<K, V> {
    keys: ArrayVec<[K; MAX_ORDER - 1]>,
    values: ArrayVec<[V; MAX_ORDER - 1]>,
    children: ArrayVec<[Box<Entry<K, V>>; MAX_ORDER]>,
    parent: *mut Entry<K, V>,
    position: usize,
}

/// Correctly clones recursively. The top entry will have a null parent.
impl<K, V> Clone for Box<Entry<K, V>>
    where K: Clone, V: Clone,
{
    fn clone(&self) -> Self {
        let mut entry = Box::new(Entry {
            keys: self.keys.clone(),
            values: self.values.clone(),
            children: self.children.clone(),
            parent: null_mut(),
            position: self.position,
        });

        let parent_ptr = &mut *entry as *mut _;
        for child in &mut entry.children {
            child.parent = parent_ptr;
        }
        entry
    }
}

impl<K, V> Default for Entry<K, V> {
    #[inline]
    fn default() -> Self {
        Entry {
            keys: ArrayVec::new(),
            values: ArrayVec::new(),
            children: ArrayVec::new(),
            parent: null_mut(),
            position: 0,
        }
    }
}

impl<K, V> Entry<K, V> {
    fn max_order() -> usize { MAX_ORDER }
    fn min_order() -> usize { Self::max_order() / 2 }
    fn median_key_index() -> usize { (Self::max_order() - 1) / 2 }
    fn this_max_order(&self) -> usize { Self::max_order() }
    fn this_min_order(&self) -> usize { Self::min_order() }

    fn order(&self) -> usize { self.keys.len() + 1 }

    fn is_leaf(&self) -> bool { self.children.len() == 0 }
    //fn order(&self) -> usize { self.children.len() }
    fn full(&self) -> bool { self.keys.len() == self.keys.capacity() }

    // split a node and return the median key and new child
    fn split(&mut self) -> (K, V, Box<Entry<K, V>>) {
        debug_assert!(self.full());

        // new right side tree
        let mut right = <Box<Entry<_, _>>>::default();

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
            let right_parent: *mut _ = &mut *right;
            for (index, mut child) in self.children
                                        .drain(1 + Self::median_key_index()..)
                                        .enumerate()
            {
                child.parent = right_parent;
                child.position = index;
                right.children.push(child);
            }
        }
        (median_key, median_value, right)
    }

    /// Return (is_equal, best_position)
    fn find<Q: ?Sized>(&self, key: &Q) -> (bool, usize)
        where K: Ord + Borrow<Q>,
              Q: Ord,
    {
        // FIXME: Find out a good cutoff for binary search
        if Self::max_order() >= 128 {
            return match self.keys.binary_search_by(|k| k.borrow().cmp(key)) {
                Ok(ix) => (true, ix),
                Err(ix) => (false, ix),
            };
        }
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

    /// Return (is_equal, best_position)
    ///
    /// Begin search from end of key vector
    fn find_rev<Q: ?Sized>(&self, key: &Q) -> (bool, usize)
        where K: Ord + Borrow<Q>,
              Q: Ord,
    {
        if Self::max_order() >= 128 {
            return self.find(key)
        }
        // find lower bound:
        // index where keys[i] < key for all i < index
        let mut i = self.keys.len();
        for k in self.keys.iter().rev() {
            if k.borrow() <= key {
                if k.borrow() == key {
                    return (true, i - 1);
                }
                break;
            }
            i -= 1;
        }
        (false, i)
    }

    fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
        where K: Ord + Borrow<Q>,
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
        where K: Ord + Borrow<Q>,
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
        where K: Ord + Borrow<Q>,
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

    fn find_key_value_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<(&K, &mut V)>
        where K: Ord + Borrow<Q>,
              Q: Ord,
    {
        let (has, lower_bound) = self.find(key);
        if has {
            Some((&self.keys[lower_bound], &mut self.values[lower_bound]))
        } else if self.is_leaf() {
            None
        } else {
            self.children[lower_bound].find_key_value_mut(key)
        }
    }

    fn value_at(&self, index: usize) -> &V {
        &self.values[index]
    }

    fn value_at_mut(&mut self, index: usize) -> &mut V {
        &mut self.values[index]
    }

    fn insert(&mut self, key: K, value: V, child: Option<Box<Entry<K, V>>>)
        where K: Ord
    {
        let (has, pos) = self.find(&key);
        debug_assert!(!has);
        self.insert_at(pos, key, value, child);
    }

    fn insert_at(&mut self, pos: usize, key: K, value: V,
                 child: Option<Box<Entry<K, V>>>)
        where K: Ord
    {
        debug_assert!(!self.full());
        let _ = self.keys.try_insert(pos, key);
        let _ = self.values.try_insert(pos, value);
        if let Some(mut child_) = child {
            child_.parent = self;
            child_.position = pos + 1;
            let _ = self.children.try_insert(pos + 1, child_);
            for child in &mut self.children[pos + 2..] {
                child.position += 1;
            }
        }
    }

    fn insert_in_root(&mut self, key: K, value: V,
                      mut left: Box<Entry<K, V>>, mut right: Box<Entry<K, V>>)
        where K: Ord
    {
        debug_assert!(self.keys.len() == 0);
        debug_assert!(self.values.len() == 0);
        debug_assert!(self.children.len() == 0);
        let _ = self.keys.try_push(key);
        let _ = self.values.try_push(value);
        left.position = 0;
        left.parent = self;
        let _ = self.children.try_push(left);
        right.position = 1;
        right.parent = self;
        let _ = self.children.try_push(right);
    }

    fn update(&mut self, key: &K, value: V) -> V
        where K: Ord
    {
        let (has, pos) = self.find(key);
        debug_assert!(has);
        let existing = mem::replace(self.value_at_mut(pos), value);
        existing
    }

    fn remove_at(&mut self, pos: usize) -> (K, V) {
        debug_assert!(self.is_leaf());
        let key = self.keys.remove(pos);
        let value = self.values.remove(pos);
        (key, value)
    }

    #[inline]
    unsafe fn parent(&self) -> Option<&Self> {
        if self.parent.is_null() {
            None
        } else {
            Some(&*self.parent)
        }
    }

    // -----------
    // DELETION
    // -----------

    fn remove_first(&mut self) -> (K, V, Option<Box<Entry<K, V>>>) {
        debug_assert!(self.order() > Self::min_order());
        let rkey = self.keys.remove(0);
        let rval = self.values.remove(0);
        let child = self.children.pop_at(0);
        for other in &mut self.children {
            other.position -= 1;
        }
        (rkey, rval, child)
    }

    fn remove_last(&mut self) -> (K, V, Option<Box<Entry<K, V>>>) {
        debug_assert!(self.order() > Self::min_order());
        let key = self.keys.pop().unwrap();
        let val = self.values.pop().unwrap();
        let child = self.children.pop();
        (key, val, child)
    }

    fn insert_first(&mut self, key: K, value: V, child: Option<Box<Entry<K, V>>>) {
        debug_assert!(!self.full());
        let _ = self.keys.try_insert(0, key);
        let _ = self.values.try_insert(0, value);
        if let Some(mut child) = child {
            for other in &mut self.children {
                other.position += 1;
            }
            child.parent = self;
            child.position = 0;
            let _ = self.children.try_insert(0, child);
        }
    }

    fn insert_last(&mut self, key: K, value: V, child: Option<Box<Entry<K, V>>>) {
        debug_assert!(!self.full());
        let order = self.order();
        self.keys.push(key);
        self.values.push(value);
        if let Some(mut child) = child {
            child.parent = self;
            child.position = order;
            self.children.push(child);
        }
    }

    fn rotate_right_to_left(&mut self, pos: usize) {
        /* rotate key and child from right to left
         *       pos                pos
         *       v                  v
         *    [..B..]            [..C..]
         *     /   \     to       /   \
         *   [A]   [C D]      [A B]   [D]   **/
        let (mut key, mut val, child) = self.children[pos + 1].remove_first();

        // replace parent key
        mem::swap(&mut self.keys[pos], &mut key);
        mem::swap(&mut self.values[pos], &mut val);
        self.children[pos].insert_last(key, val, child);
    }

    fn rotate_left_to_right(&mut self, pos: usize) {
        /* rotate key and child from left to right
         *       pos               pos
         *       v                 v
         *   [...C..]          [...B..]
         *      / \     to        / \
         * [A B]   [D]         [A]   [C D]       **/
        let (mut key, mut val, child) = self.children[pos].remove_last();

        // replace parent key
        mem::swap(&mut self.keys[pos], &mut key);
        mem::swap(&mut self.values[pos], &mut val);
        self.children[pos + 1].insert_first(key, val, child);
    }

    /// Return **true** if **self** was emptied
    fn merge_siblings(self: &mut Entry<K, V>, pos: usize) -> bool {
        // FIXME: We might kill the parent
        let pkey = self.keys.remove(pos);
        let pval = self.values.remove(pos);
        let right_child = *self.children.remove(pos + 1);
        //assert!(self.keys.len() > 0);
        let removed_root = self.keys.len() == 0;
        for child in &mut self.children[pos + 1..] {
            child.position -= 1;
        }
        {
            let left_child = &mut self.children[pos];
            let (keys, values, children) = match right_child {
                Entry { keys, values, children, .. } =>
                    (keys, values, children)
            };
            let len = left_child.order();
            left_child.keys.push(pkey);
            left_child.keys.extend(keys);
            left_child.values.push(pval);
            left_child.values.extend(values);
            let parent_ptr: *mut Entry<_, _> = &mut **left_child;
            left_child.children.extend(
                children.into_iter()
                    .map(|mut child| {
                        child.position += len;
                        child.parent = parent_ptr;
                        child
                    }));
        }
        if removed_root {
            // this is the new root
            let mut left_child = self.children.pop().unwrap();
            left_child.parent = self.parent;
            left_child.position = self.position;
            mem::replace(self, *left_child);
            let parent_ptr = self as *mut _;
            for child in &mut self.children {
                child.parent = parent_ptr;
            }
        }
        removed_root
    }

}

/// **Bmap\<K, V\>** is an associative array implemented with a B-Tree.
///
/// Key-value pairs are ordered by the key in ascending order.
#[derive(Clone)] // OK because Entry's clone is sane
#[derive(Debug)]
pub struct Bmap<K, V> {
    length: usize,
    root: Box<Entry<K, V>>,
}

use self::Insert::{Split, Updated, Inserted};
enum Insert<K, V> {
    Split((K, V), K, V, Box<Entry<K, V>>),
    Updated(V),
    Inserted,
}

impl<K, V> Bmap<K, V>
    where K: Ord
{
    /// Create a new **Bmap**.
    pub fn new() -> Self {
        Bmap {
            length: 0,
            root: Box::default(),
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

    /// Experimental get twice method
    pub fn get_twice_mut<Q: ?Sized>(&mut self, k: &Q, m: &Q)
        -> Option<(&K, &mut V, &K, &mut V)>
        where K: Borrow<Q>,
              Q: Ord,
    {
        if k == m {
            return None
        }

        // Allow two mutable indexes here -- they are nonoverlapping
        unsafe {
            let self_mut = self as *mut Self;
            match ((*self_mut).root.find_key_value_mut(k),
                   (*self_mut).root.find_key_value_mut(m)) {
                (Some((a, b)), Some((c, d))) => Some((a, b, c, d)),
                _ => None
            }
        }
    }

    /// Insert **key**, **value**.
    ///
    /// Return previous **value** for the key, or **None**.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        /* Top-down insertion:
         * Search downwards to find a leaf where we can insert the key.
         * Don't step into any full node without splitting it, and pushing
         * its median key into the parent. */

        fn insert_key<K, V>(entry: &mut Entry<K, V>, mut kv: (K, V)) -> Insert<K, V>
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
                    Split(kv_, median_k, median_v, right_child) => {
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
                Split(kv_, median_k, median_v, right_child) => {
                    // Root was split, replace it with a new empty node,
                    // left side: old root
                    // right side: right_child
                    let left_child = mem::replace(root, Box::default());
                    root.insert_in_root(median_k, median_v,
                                        left_child, right_child);
                    kv = kv_;
                }
                Updated(v) => { return Some(v) }
                Inserted => { self.length += 1; return None }
            }
        }
    }

    fn remove_key<Q: ?Sized>(mut entry: &mut Entry<K, V>, key: &Q) -> Option<(K, V)>
        where K: Borrow<Q>,
              Q: Ord,
    {
        /* Deletion
         *
         * - Only delete from a leaf
         *
         * - Three fixup strategies:
         *
         *   A. rotating in the max element of the lower sibling
         *   B. rotating in the least element of the higher sibling
         *   C. merging with sibling and a parent element
         *
         *   These are used either if
         *
         *   a. Key to delete is not in a leaf
         *   b. Node we are about to enter is min order
         *
         * - A last case occurs: Key to delete is not in a leaf,
         *   and both children are max order.
         *
         *   Swap key with its predecessor, and delete its position instead.
         *   Predecessor is always in a leaf, always last in the node!
         *
         */
        loop {
            let (has_key, mut pos) = entry.find(key);
            if has_key {
                if entry.is_leaf() {
                    return Some(entry.remove_at(pos));
                }
                // we need to move the k-v so we can delete them
                let (lo, ro) = {
                    let left = &entry.children[pos];
                    let right = &entry.children[pos + 1];
                    (left.order(), right.order())
                };
                if lo == entry.this_min_order() && lo == ro {
                    // Key to delete is parent to two min-size children.
                    // Push down key to merged children.
                    if entry.merge_siblings(pos) {
                        continue;
                    }
                } else if ro > entry.this_min_order() && lo != entry.this_max_order() {
                    entry.rotate_right_to_left(pos);
                } else if ro != entry.this_max_order() {
                    entry.rotate_left_to_right(pos);
                    pos += 1;
                } else {
                    // Strategy: Swap with predecessor, always in a leaf
                    //
                    let (pred_key, pred_value);
                    {
                        // FIXME: Need real delete traversal to keep invariants
                        let mut iter = &mut entry.children[pos];
                        let rm = Self::remove_key(iter, key);
                        debug_assert!(rm.is_none());
                        while !iter.is_leaf() {
                            iter = {iter}.children.last_mut().unwrap();
                        }
                        pred_key = iter.keys.pop().unwrap();
                        pred_value = iter.values.pop().unwrap();
                    }
                    let key = mem::replace(&mut entry.keys[pos], pred_key);
                    let value = mem::replace(&mut entry.values[pos], pred_value);
                    return Some((key, value));
                }

            } else if entry.is_leaf() {
                return None
            } else if entry.children[pos].order() == entry.this_min_order() {
                if pos > 0 && entry.children[pos - 1].order() > entry.this_min_order() {
                    entry.rotate_left_to_right(pos - 1);
                } else if pos + 1 < entry.children.len()
                    && entry.children[pos + 1].order() > entry.this_min_order() {
                    entry.rotate_right_to_left(pos);
                } else {
                    if pos > 0 { pos -= 1 }
                    if entry.merge_siblings(pos) {
                        continue;
                    }
                }
            }

            debug_assert!(!entry.is_leaf());
            entry = &mut {entry}.children[pos];
            debug_assert!(entry.order() >= entry.this_min_order());
        }
    }

    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
        where K: Borrow<Q>,
              Q: Ord,
    {
        self.remove_key_value(key).map(|(_, v)| v)
    }

    pub fn remove_key_value<Q: ?Sized>(&mut self, key: &Q) -> Option<(K, V)>
        where K: Borrow<Q>,
              Q: Ord,
    {
        let value = Self::remove_key(&mut self.root, key);
        if value.is_some() {
            self.length -= 1;
        }
        value
    }

    /// Iterate the Bmap in order.
    ///
    /// Iterator element type is **(&K, &V)**.
    pub fn iter(&self) -> Iter<K, V> {
        // find and focus the lower bound
        let mut entry = &self.root;
        while !entry.is_leaf() {
            entry = &entry.children[0];
        }
        Iter {
            entry: entry,
            keyiter: ZipSlices::new(&entry.keys, &entry.values),
        }
    }

    /// Iterate in order from the key **k** (inclusive).
    ///
    /// Iterator element type is **(&K, &V)**.
    pub fn iter_from<Q>(&self, k: &Q) -> Iter<K, V>
        where K: Borrow<Q>,
              Q: Ord,
    {
        // find and focus the greatest lower bound
        let mut entry = &self.root;
        loop {
            let (has, i) = entry.find(k);
            if entry.is_leaf() {
                return Iter {
                    entry: entry,
                    keyiter: ZipSlices::new(&entry.keys[i..], &entry.values[i..]),
                }
            } else if has {
                entry = &entry.children[i];
                // FIXME: descending to leaf here is unnecessary,
                // just to satisfy always-stop-in-leaf invariant in Iter
                /* descend to leaf */
                while !entry.is_leaf() {
                    entry = &entry.children.last().unwrap();
                }
                return Iter {
                    entry: entry,
                    keyiter: ZipSlices::new(&[], &[]),
                }
            } else {
                entry = &entry.children[i];
            }
        }
    }

    /// Iterate in order from the key **k** to the key **l** (both inclusive).
    ///
    /// Iterator element type is **(&K, &V)**.
    pub fn range<'a, Q>(&'a self, k: &Q, l: &'a Q) -> Range<'a, K, V, Q>
        where K: Borrow<Q>,
              Q: Ord,
    {
        // find and focus the greatest lower bound
        let mut entry = &self.root;
        loop {
            let (has, i) = entry.find(k);
            if entry.is_leaf() {
                let (has_end, j) = entry.find(l);
                if has_end {
                    return Range {
                        entry: entry,
                        keyiter: ZipSlices::new(&entry.keys[i..j + 1],
                                                &entry.values[i..j + 1]),
                        last: true,
                        end: l,
                    }
                } else {
                    // `j` may be == keys.len() here or shorter.
                    return Range {
                        entry: entry,
                        keyiter: ZipSlices::new(&entry.keys[i..j],
                                                &entry.values[i..j]),
                        last: false,
                        end: l,
                    }
                }
            } else if has {
                entry = &entry.children[i];
                // FIXME: descending to leaf here is unnecessary,
                // just to satisfy always-stop-in-leaf invariant in Iter
                /* descend to leaf */
                while !entry.is_leaf() {
                    entry = &entry.children.last().unwrap();
                }
                return Range {
                    entry: entry,
                    keyiter: ZipSlices::new(&[], &[]),
                    last: false,
                    end: l,
                }
            } else {
                entry = &entry.children[i];
            }
        }
    }

}

impl<'a, K, V, Q: ?Sized> Index<&'a Q> for Bmap<K, V>
    where K: Ord + Borrow<Q>,
          Q: Ord,
{
    type Output = V;
    fn index(&self, index: &'a Q) -> &V {
        self.get(index).expect("Bmap: Key error")
    }
}

impl<'a, K, V, Q: ?Sized> IndexMut<&'a Q> for Bmap<K, V>
    where K: Ord + Borrow<Q>,
          Q: Ord,
{
    fn index_mut(&mut self, index: &'a Q) -> &mut V {
        self.get_mut(index).expect("Bmap: Key error")
    }
}

impl<K: Ord, V> Default for Bmap<K, V> {
    fn default() -> Self { Bmap::new() }
}

impl<'a, K: Ord, V> IntoIterator for &'a Bmap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Iter<'a, K, V> { self.iter() }
}

impl<K: Ord, V> Extend<(K, V)> for Bmap<K, V> {
    fn extend<T: IntoIterator<Item=(K, V)>>(&mut self, iter: T) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<'a, K, V> Extend<(&'a K, &'a V)> for Bmap<K, V>
    where K: 'a + Ord + Clone,
          V: 'a + Clone,
{
    fn extend<T: IntoIterator<Item=(&'a K, &'a V)>>(&mut self, iter: T) {
        for (k, v) in iter {
            self.insert(k.clone(), v.clone());
        }
    }
}

/// Default iterator for **Bmap**.
pub struct Iter<'a, K: 'a, V: 'a> {
    entry: &'a Entry<K, V>,
    keyiter: ZipSlices<&'a [K], &'a [V]>,
}

impl<'a, K, V> Clone for Iter<'a, K, V> {
    fn clone(&self) -> Self {
        Iter {
            entry: self.entry,
            keyiter: self.keyiter.clone(),
        }
    }
}

// The iterator has some nice invariants.
// The currently focused entry is always a leaf, and its iterators
// are always present.

impl<'a, K: Ord, V> Iter<'a, K, V> {
    fn next_switch_node(&mut self) -> Option<<Self as Iterator>::Item> {
        let mut entry = self.entry;
        loop {
            let child = entry;
            let i = child.position;
            entry = match unsafe { entry.parent() } {
                None => break,
                Some(parent) => parent,
            };
            debug_assert!(i <= entry.keys.len());
            debug_assert!(ptr_eq(child, &*entry.children[i]));
            if i == entry.keys.len() {
                continue;
            }
            let next_key;
            let next_value;
            // Unchecked indexing improves iteration runtime by minuscle 2%.
            unsafe {
                next_key = odds::get_unchecked(&*entry.keys, i);
                next_value = odds::get_unchecked(&*entry.values, i);

                // dig down to successor
                entry = &odds::get_unchecked(&*entry.children, i + 1);
                while let Some(entry_) = entry.children.get(0) {
                    entry = entry_;
                }
            }
            self.keyiter = ZipSlices::new(&entry.keys, &entry.values);
            self.entry = entry;
            return Some((next_key, next_value));
        }
        None
    }
}

impl<'a, K: Ord, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        debug_assert!(self.entry.is_leaf());
        if let elt @ Some(..) = self.keyiter.next() {
            elt
        } else {
            self.next_switch_node()
        }
    }
}

/// Key range iterator.
pub struct Range<'a, K: 'a, V: 'a, Q: 'a> {
    entry: &'a Entry<K, V>,
    keyiter: ZipSlices<&'a [K], &'a [V]>,
    last: bool,
    end: &'a Q,
}

impl<'a, K, V, Q> Clone for Range<'a, K, V, Q> {
    fn clone(&self) -> Self {
        Range {
            entry: self.entry,
            keyiter: self.keyiter.clone(),
            last: self.last,
            end: self.end,
        }
    }
}

impl<'a, K, V, Q> Range<'a, K, V, Q>
    where K: Borrow<Q> + Ord,
          Q: Ord,
{
    fn next_switch_node(&mut self) -> Option<<Self as Iterator>::Item> {
        let mut entry = self.entry;
        loop {
            if self.last {
                // FIXME: We might not need this bool
                return None
            }
            let child = entry;
            let i = child.position;
            entry = match unsafe { entry.parent() } {
                None => break,
                Some(parent) => parent,
            };
            debug_assert!(i <= entry.keys.len());
            debug_assert!(ptr_eq(child, &*entry.children[i]));
            if i == entry.keys.len() {
                continue;
            }
            let next_key;
            let next_value;
            // Unchecked indexing improves iteration runtime by minuscle 2%.
            unsafe {
                next_key = odds::get_unchecked(&*entry.keys, i);
                next_value = odds::get_unchecked(&*entry.values, i);

                // dig down to successor
                entry = &odds::get_unchecked(&*entry.children, i + 1);
                while let Some(entry_) = entry.children.get(0) {
                    entry = entry_;
                }
            }
            if next_key.borrow() > self.end {
                return None
            }
            unsafe {
                // check if we have reached the end key:
                // Search from the back of the key array -- decreases iteration runtime by 32 %
                // Used to search from the front
                let (has_end, j) = entry.find_rev(self.end);
                // Unchecked slicing decreases iteration runtime by minuscle 1%.
                if has_end {
                    // setup termination
                    self.last = true;
                    self.keyiter = ZipSlices::new(
                        odds::slice_unchecked(&entry.keys, 0, j + 1),
                        odds::slice_unchecked(&entry.values, 0, j + 1))
                } else {
                    // `j` may be == keys.len() or shorter. If shorter, we are done.
                    self.last = j != entry.keys.len();
                    self.keyiter = ZipSlices::new(
                        odds::slice_unchecked(&entry.keys, 0, j),
                        odds::slice_unchecked(&entry.values, 0, j));
                }
            }
            self.entry = entry;
            return Some((next_key, next_value));
        }
        None
    }
}

impl<'a, K, V, Q> Iterator for Range<'a, K, V, Q>
    where K: Borrow<Q> + Ord,
          Q: Ord,
{
    type Item = (&'a K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        debug_assert!(self.entry.is_leaf());
        if let elt @ Some(..) = self.keyiter.next() {
            elt
        } else {
            self.next_switch_node()
        }
    }
}



#[test]
fn test_new() {
    let mut bp = Bmap::new();
    for x in vec![0, 2, 4, 6, 8, 10, 3, 1, 7, 5, 11, 13] {
        bp.insert(x, ());
    }

    for elt in bp.iter() {
        println!("Iter: {:?}", elt);
    }
    assert_eq!(bp.iter().count(), bp.len());
    println!("{:?}", bp);

    let mut bp = Bmap::new();
    for x in 0..20 {
        bp.insert(x, x);
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

#[cfg(test)]
#[test]
fn test_fuzz() {
    let mut rng: ChaChaRng = rand::random();

    const N: usize = 149;
    const NTEST: usize = 10;
    for _ in 0..NTEST {
        let mut keys: Vec<_> = (0..N).collect();
        rng.shuffle(&mut keys);

        let mut m = Bmap::new();
        for &key in &keys {
            m.insert(key, ());
        }

        for &key in &keys {
            assert!(m.contains(&key));
        }

        keys.sort();
        assert_eq!(m.iter().count(), keys.len());
        for (key, (map_key, _)) in keys.iter().zip(m.iter()) {
            assert_eq!(key, map_key);
        }
    }
}

//#[cfg(test)]
#[test]
fn test_fuzz_remove() {
    let input_seed = None;

    let seed = match input_seed {
        Some(inner) => inner,
        None => {
            let mut seed_ = [0_u32; 4];
            for s in &mut seed_ {
                *s = rand::random();
            }
            seed_
        }
    };
    println!("Seed: {:?}", seed);
    let mut rng = ChaChaRng::from_seed(&seed);

    const MAX: usize = 50; // max test size
    const NTEST: usize = 10000;
    type Key = u8;
    for test_index in 0..NTEST {
        let testsz = 10 + MAX * (10 * test_index) / NTEST / 10;
        let size = rng.gen_range(0, testsz);
        let mut keys: Vec<_> = rng.gen_iter::<Key>().take(size).collect();

        let mut m = Bmap::new();
        for &key in &keys {
            m.insert(key, ());
        }

        // check that all keys are present
        for &key in &keys {
            assert!(m.contains(&key));
        }
        keys.sort();
        keys.dedup();
        assert_eq!(m.iter().count(), keys.len());
        for (key, (map_key, _)) in keys.iter().zip(m.iter()) {
            assert_eq!(key, map_key);
        }

        let rm_size = rng.gen_range(0, MAX);
        let mut removals: Vec<_> = rng.gen_iter::<Key>().take(rm_size).collect();
        removals.sort();
        removals.dedup();
        rng.shuffle(&mut removals);
        //println!("Keys: {:?}", keys);
        //println!("Removals: {:?}", removals);
        //println!("Tree BEFORE Removals: {:#?}", m);

        // containment check
        for &rkey in &removals {
            assert_eq!(m.contains(&rkey), keys.contains(&rkey));
        }

        // remove check
        // keys is deduplicated here
        let mut n_present = 0;
        for &rkey in &removals {
            let removed = m.remove(&rkey);
            let is_present = keys.contains(&rkey);
            if is_present {
                n_present += 1;
            }
            if removed.is_some() != is_present {
                println!("Failed to remove key: {}", rkey);
                println!("Tree: {:#?}", m);
            }
            assert_eq!(removed.is_some(), is_present);
        }

        // check all parent links
        assert!(fix(&*m.root, |f, entry| {
            entry.children.iter().all(|c| ptr_eq(c.parent, entry) && f.call(&**c))
        }));

        //println!("After remove: {:#?}", m);
        assert_eq!(m.iter().count(), m.len());
        assert_eq!(m.len(), keys.len() - n_present);
    }
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
    assert_eq!(m.get_mut("a"), Some(&mut 2));
    m["a"] = 3;
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
    assert!(bp.contains("rusts"));
    assert!(bp.contains("fungi"));
}

#[test]
fn test_remove() {
    let mut bp = bmap!{
        1 => 1,
        2 => 2,
        3 => 3,
    };
    println!("{:#?}", bp);
    assert_eq!(bp.remove(&1), Some(1));
    assert_eq!(bp.remove(&0), None);
    assert_eq!(bp.len(), 2);
    assert_eq!(bp.remove(&2), Some(2));
    assert_eq!(bp.remove(&3), Some(3));
    assert_eq!(bp.len(), 0);
    println!("{:#?}", bp);


    // test remove from a non-leaf

    // Rotate case
    let mut bp = bmap!();
    for x in 0..MAX_ORDER {
        bp.insert(x, x);
    }
    println!("{:#?}", bp);

    let root_key = bp.root.keys[0];
    assert!(!bp.root.is_leaf());
    let removed = bp.remove(&root_key);
    println!("{:#?}", bp);
    assert_eq!(removed, Some(root_key));

    // Merge case
    let mut bp = bmap!();
    for x in 0..2 * MAX_ORDER {
        bp.insert(x, x);
    }
    println!("{:#?}", bp);

    let root_key = bp.root.keys[0];
    assert!(!bp.root.is_leaf());
    let removed = bp.remove(&root_key);
    println!("{:#?}", bp);
    assert_eq!(removed, Some(root_key));

    // Both children full case
    let max_keys = MAX_ORDER - 1;
    let mut bp = bmap!();

    let mid = max_keys + 1;
    bp.insert(mid, mid);

    for (index, x) in (0..mid).rev().enumerate() {
        let index = 2 * index + 1;
        bp.insert(x, x);
        bp.insert(x + index, x + index);
    }

    println!("{:#?}", bp);

    let root_key = bp.root.keys[0];
    assert!(!bp.root.is_leaf());
    let removed = bp.remove(&root_key);
    //println!("{:#?}", bp);
    assert_eq!(removed, Some(root_key));
}


#[cfg(test)]
fn create_random_tree<R, S>(max_size: usize) -> Bmap<R, S>
    where R: rand::Rand + Ord, S: rand::Rand
{
    let mut rng: ChaChaRng = rand::random();

    let size = rng.gen_range(0, max_size);
    let keys: Vec<_> = rng.gen_iter::<R>().take(size).collect();
    let values: Vec<_> = rng.gen_iter::<S>().take(size).collect();

    let mut m = Bmap::new();
    for (k, v) in keys.into_iter().zip(values) {
        m.insert(k, v);
    }
    m
}

#[test]
fn test_clone() {
    let t1 = create_random_tree::<i32, i32>(512);
    let t2 = t1.clone();

    it::assert_equal(t1.iter(), t2.iter());
}

#[test]
fn test_iter_from() {
    let sz = 128;
    let n = 10;
    for _ in 0.. n {
        let t1 = create_random_tree::<u8, ()>(sz);
        for key in 0..256 {
            let key8 = key as u8;
            it::assert_equal(t1.iter_from(&key8), t1.iter().filter(|&(&k, _)| k >= key8));
        }
    }
}


#[test]
fn test_iter_range() {
    fn tup_get_0<T, U>(t: (T, U)) -> T { t.0 }
    let sz = 128;
    let n = 10;
    for _ in 0.. n {
        let t1 = create_random_tree::<u8, ()>(sz);
        for key1 in 0..256 {
            for key2 in key1..256 {
                let key1_8 = key1 as u8;
                let key2_8 = key2 as u8;
                assert!(it::equal(t1.range(&key1_8, &key2_8),
                          t1.iter().filter(|&(&k, _)| k >= key1_8 && k <= key2_8)),
                        "failed: equal for Range from={}, to={}, \niter1={:?}\ntree={:?}",
                        key1, key2, t1.range(&key1_8, &key2_8).map(tup_get_0).collect::<Vec<_>>(),
                        t1);
            }
        }
    }
}

