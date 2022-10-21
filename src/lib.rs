#![feature(new_uninit, map_first_last, nonzero_min_max, ptr_as_uninit)]
#![deny(unsafe_op_in_unsafe_fn)]

mod char_list;
mod pq_rc;

pub use crate::char_list::*;
