#![allow(clippy::module_inception)]

mod pq_rc;

#[cfg(not(test))]
mod pq_rc_cell;

#[cfg(test)]
pub mod pq_rc_cell;

#[cfg(test)]
mod tests;

pub use pq_rc::*;
