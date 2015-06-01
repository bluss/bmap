extern crate arrayvec;
#[cfg(test)]
extern crate rand;
#[cfg(test)]
extern crate odds;

#[macro_use]
mod macros;
pub mod bmap;
mod unreachable;

pub use bmap::Bmap;

#[test]
fn it_works() {
}
