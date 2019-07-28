#![feature(test)]
extern crate test;

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

pub mod set;
mod tree;

#[cfg(test)]
mod bench;
