#![feature(iterator_try_collect)]
#![feature(get_mut_unchecked)]
#![feature(test)]

#[macro_use]
extern crate pest_derive;
extern crate test;

pub mod parser;
pub mod types;
