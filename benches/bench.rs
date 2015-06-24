// Copyright 2013-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(test, collections_bound, btree_range)]
extern crate bmap;
extern crate rand;
extern crate test;


#[macro_export]
macro_rules! map_insert_remove_rand_bench {
    ($name: ident, $n: expr, $map: ident) => (
        #[bench]
        pub fn $name(b: &mut ::test::Bencher) {
            use rand::{thread_rng, Rng};
            use test::black_box;

            let n: usize = $n;
            let mut map = $map::new();
            // setup
            let mut rng = thread_rng();

            for _ in 0..n {
                let i = rng.gen::<usize>() % n;
                map.insert(i, i);
            }

            // measure
            b.iter(|| {
                let k = rng.gen::<usize>() % n;
                map.insert(k, k);
                map.remove(&k);
            });
            black_box(map);
        }
    )
}

#[macro_export]
macro_rules! map_insert_seq_bench {
    ($name: ident, $n: expr, $map: ident) => (
        #[bench]
        pub fn $name(b: &mut ::test::Bencher) {
            use test::black_box;

            let mut map = $map::new();
            let n: usize = $n;
            // setup
            for i in 0..n {
                map.insert(i * 2, i * 2);
            }

            // measure
            let mut i = 1;
            b.iter(|| {
                map.insert(i, i);
                map.remove(&i);
                i = (i + 2) % n;
            });
            black_box(map);
        }
    )
}

macro_rules! map_insert_seq2_bench {
    ($name: ident, $n: expr, $map: ident) => (
        #[bench]
        pub fn $name(b: &mut ::test::Bencher) {
            use test::black_box;

            let mut map = $map::new();
            let n: usize = $n;

            // measure
            b.iter(|| {
                for i in 0..n {
                    map.insert(i, i);
                }
            });
            black_box(map);
        }
    )
}


macro_rules! map_find_rand_bench {
    ($name: ident, $n: expr, $map: ident) => (
        #[bench]
        pub fn $name(b: &mut ::test::Bencher) {
            use std::iter::Iterator;
            use rand::{thread_rng, Rng};
            use std::vec::Vec;
            use test::black_box;

            let mut map = $map::new();
            let n: usize = $n;

            // setup
            let mut rng = thread_rng();
            let mut keys: Vec<_> = (0..n).map(|_| rng.gen::<usize>() % n).collect();

            for &k in &keys {
                map.insert(k, k);
            }

            rng.shuffle(&mut keys);

            // measure
            let mut i = 0;
            b.iter(|| {
                let t = map.get(&keys[i]);
                i = (i + 1) % n;
                black_box(t);
            })
        }
    )
}

#[macro_export]
macro_rules! map_find_seq_bench {
    ($name: ident, $n: expr, $map: ident) => (
        #[bench]
        pub fn $name(b: &mut ::test::Bencher) {
            use test::black_box;

            let mut map = $map::new();
            let n: usize = $n;

            // setup
            for i in 0..n {
                map.insert(i, i);
            }

            // measure
            let mut i = 0;
            b.iter(|| {
                let x = map.get(&i);
                i = (i + 1) % n;
                black_box(x);
            })
        }
    )
}

macro_rules! map_insert_rand_bench {
    ($name: ident, $n: expr, $map: ident) => (
        #[bench]
        pub fn $name(b: &mut ::test::Bencher) {
            use std::iter::Iterator;
            use rand::{thread_rng, Rng};
            use std::vec::Vec;
            use test::black_box;

            let mut map = $map::new();
            let n: usize = $n;

            // setup
            let mut rng = thread_rng();
            let mut keys: Vec<_> = (0..n).map(|_| rng.gen::<usize>() % n).collect();

            rng.shuffle(&mut keys);

            // measure
            b.iter(|| {
                map = $map::new();
                for &k in &keys {
                    let k = black_box(k);
                    map.insert(k, k);
                }
            })
        }
    )
}

use bmap::Bmap;
use std::collections::BTreeMap;
use std::collections::Bound;

use rand::{thread_rng, Rng};
use test::Bencher;
use test::black_box;


map_insert_remove_rand_bench!{insert_remove_rand_100_btree,    100,    BTreeMap}
map_insert_remove_rand_bench!{insert_remove_rand_10_000_btree, 10_000, BTreeMap}
map_insert_remove_rand_bench!{insert_remove_rand_100_bmap,    100,    Bmap}
map_insert_remove_rand_bench!{insert_remove_rand_10_000_bmap, 10_000, Bmap}

map_insert_seq_bench!{insert_seq_100,    100,    BTreeMap}
map_insert_seq_bench!{insert_seq_10_000, 10_000, BTreeMap}
map_insert_seq_bench!{insert_seq_100_bmap,    100,    Bmap}
map_insert_seq_bench!{insert_seq_10_000_bmap, 10_000, Bmap}

map_insert_rand_bench!{insert_rand_100,    100,    BTreeMap}
map_insert_rand_bench!{insert_rand_10_000, 10_000, BTreeMap}
map_insert_rand_bench!{insert_rand_100_bmap,    100,    Bmap}
map_insert_rand_bench!{insert_rand_10_000_bmap, 10_000, Bmap}

map_insert_seq2_bench!{insert_seq2_100,    100,    BTreeMap}
map_insert_seq2_bench!{insert_seq2_10_000, 10_000, BTreeMap}
map_insert_seq2_bench!{insert_seq2_100_bmap,    100,    Bmap}
map_insert_seq2_bench!{insert_seq2_10_000_bmap, 10_000, Bmap}

map_find_rand_bench!{find_rand_100,    100,    BTreeMap}
map_find_rand_bench!{find_rand_100_bmap,    100,    Bmap}
map_find_rand_bench!{find_rand_10_000, 10_000, BTreeMap}
map_find_rand_bench!{find_rand_10_000_bmap, 10_000, Bmap}

map_find_seq_bench!{find_seq_100,    100,    BTreeMap}
map_find_seq_bench!{find_seq_100_bmap,    100,    Bmap}
map_find_seq_bench!{find_seq_10_000, 10_000, BTreeMap}
map_find_seq_bench!{find_seq_10_000_bmap, 10_000, Bmap}

fn bench_iter(b: &mut Bencher, size: i32) {
    let mut map = BTreeMap::<i32, i32>::new();
    let mut rng = thread_rng();

    for _ in 0..size {
        map.insert(rng.gen(), rng.gen());
    }

    b.iter(|| {
        for entry in &map {
            black_box(entry);
        }
    });
}

fn bench_iter_range_btree(b: &mut Bencher, size: i32) {
    let mut map = BTreeMap::<i32, i32>::new();
    let mut rng = thread_rng();

    for _ in 0..size {
        map.insert(rng.gen(), rng.gen());
    }

    b.iter(|| {
        for entry in map.range(Bound::Included(&i32::min_value()), Bound::Included(&i32::max_value())) {
            black_box(entry);
        }
    });
}

fn bench_iter_bmap(b: &mut Bencher, size: i32) {
    let mut map = Bmap::<i32, i32>::new();
    let mut rng = thread_rng();

    for _ in 0..size {
        map.insert(rng.gen(), rng.gen());
    }

    b.iter(|| {
        for entry in map.iter() {
            black_box(entry);
        }
    });
}

fn bench_iter_range_bmap(b: &mut Bencher, size: i32) {
    let mut map = Bmap::<i32, i32>::new();
    let mut rng = thread_rng();

    for _ in 0..size {
        map.insert(rng.gen(), rng.gen());
    }

    b.iter(|| {
        for entry in map.range(&i32::min_value(), &i32::max_value()) {
            black_box(entry);
        }
    });
}

#[bench]
pub fn iter_20_btree(b: &mut Bencher) {
    bench_iter(b, 20);
}

#[bench]
pub fn iter_1000_btree(b: &mut Bencher) {
    bench_iter(b, 1000);
}

#[bench]
pub fn iter_range_1000_btree(b: &mut Bencher) {
    bench_iter_range_btree(b, 1000);
}

#[bench]
pub fn iter_100_000_btree(b: &mut Bencher) {
    bench_iter(b, 100000);
}

#[bench]
pub fn iter_20_bmap(b: &mut Bencher) {
    bench_iter_bmap(b, 20);
}

#[bench]
pub fn iter_1000_bmap(b: &mut Bencher) {
    bench_iter_bmap(b, 1000);
}

#[bench]
pub fn iter_range_1000_bmap(b: &mut Bencher) {
    bench_iter_range_bmap(b, 1000);
}

#[bench]
pub fn iter_100_000_bmap(b: &mut Bencher) {
    bench_iter_bmap(b, 100000);
}
