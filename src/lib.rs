#![cfg_attr(not(test), no_std)]

extern crate alloc;

mod entry;
pub mod tree;
pub(crate) mod u24;
mod util;
pub(crate) mod value;

pub(crate) use entry::Entry;
pub use tree::Tree;
pub(crate) use u24::U24;
pub use value::Value;

#[derive(Debug, Clone)]
pub enum Error {
    NodeFull,
    InvalidData,
    /// This Tree was either created with `new`, or it has outgrown its original buffer.
    /// To get back the bytes, `finish_vec` should be called.
    TreeAllocated,
}

type Result<T> = core::result::Result<T, Error>;

#[cfg(test)]
mod tests;
