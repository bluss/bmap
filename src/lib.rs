//!
//!
//!
//!
//! ## License
//!
//! This program is free software: you can redistribute it and/or modify
//! it under the terms of GPL-3.

extern crate arrayvec;
#[cfg(test)]
extern crate rand;
extern crate itertools;

#[cfg(test)]
extern crate odds;

extern crate unchecked_index;

#[macro_use]
mod macros;
pub mod bmap;

pub use bmap::Bmap;
