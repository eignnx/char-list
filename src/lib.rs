#![feature(new_uninit, map_first_last, nonzero_min_max, ptr_as_uninit, pattern)]
#![deny(unsafe_op_in_unsafe_fn)]

//! # CharList
//! An efficient string type with the same API as a linked-list of characters.
//!
//! ## DISCLAIMER: `unsafe`
//! This crate is a work in progress. Specifically ***Not all uses of `unsafe` have been validated!*** Please don't use this for anything serious yet.
//!
//! Safety audits are welcome and appreciated! I'm still quite new to writing `unsafe` code.
//!
//! ## Internal Representation
//! This crate relies on [`front-vec`]("https://crates.io/crates/front-vec") to store arrays of bytes which allow for effiecient prepending (pushing characters onto the front of the array).
//!
//! ### `CharList == PqRc<FrontString>`
//! This crate implements a type called `PqRc` (soon to be moved to its own crate) which stands for "Priority Queue Reference Counted". It's a shared pointer type like `Rc`, but while `Rc<T>` points to a `RcBox<T>` with approximately this layout:
//!
//! ```ignore
//! struct Rc<T> {
//!     ptr: *mut RcBox<T>,
//! }
//!
//! struct RcBox<T> {
//!     strong: Cell<usize>,
//!     weak: Cell<usize>,
//!     value: T,
//! }
//! ```
//!
//! a `PqRc` points to a `PqRcCell` which looks approximately like this:
//!
//! ```ignore
//! struct PqRc<T, Priority> {
//!     priority: Priority,
//!     ptr: *mut PqRcCell<T, Priority>,
//! }
//!
//! struct PqRcCell<T, Priority> {
//!     priorities: PriorityQueue<(Priority, Count)>,
//!     value: T,
//! }
//! ```
//!
//! ### What?
//!
//! The cool thing about this setup is that if a `T` is shared among a bunch of `PqRc`s, only those with the **highest priority** are allowed to mutate the inner `T` value. And they can only\* mutate it in ways that other `PqRc`'s of lower priority won't notice.
//!
//! \* (Ok, at this point we make developers pinky-swear 🤞 they'll follow those rules, and they gotta wrap their use in an `unsafe` block. Maybe there's a better way to do this in the future though 🤔)
//!
//! ### Memory Diagram
//!
//! Consider this code:
//!
//! ```ignore
//! let empty = CharList::new();
//! let yz = empty.cons('z').cons('y');
//! let wxyz_1 = yz.cons('x').cons('w');
//! let wxyz_2 = wxyz_1.clone();
//! ```
//!
//! These values would be represented in memory like this:
//!
//! ![Box and pointer diagram showing 4 `CharList`s and 1 `PqRcCell` which owns the `FrontString` "wxyz" which also has 4 bytes of free space ahead of it.](assets/char_list_ex_1.svg)
//!
//! #### Let's `cons`!
//!
//! ```ignore
//! let vwxyz = wxyz_1.cons('v');
//! ```
//!
//! If we `cons` a character onto the front of the string via the variable `wxyz_1`, it's perfectly safe to call the underlying `FrontString`'s `push_char_front` method (mutably!). This is because `wxyz_1` has the highest **priority**. (In the case of `CharList`s, priority is defined as the **length** of the substring.)
//!
//! Notice that by pushing a character onto the front, `wxyz_1` doesn't affect **any other `CharList`'s view** of the underlying `FrontString`.
//!
//! Here's what memory looks like now:
//!
//! ![asdf](assets/char_list_ex_2.svg)
//!
//! #### Dropping
//!
//! Ok now what happens if we `drop` the longest three strings?
//!
//! ```ignore
//! drop(vwxyz);
//! drop(wxyz_1);
//! drop(wxyz_2);
//! ```
//!
//! ![asdf](assets/char_list_ex_3.svg)
//!
//! Notice that the internal `FrontString`'s `len` went down to 2. This means we can reuse the memory that used to be held by the longer strings!
//!
//! #### Cons-ing onto `empty`
//!
//! Here's a problem though. What if we want to `cons` the character `'a'` onto the front of `empty`?
//!
//! ```ignore
//! let a = empty.cons('a');
//! ```
//!
//! Well, if we overwrite the `'z'` that currently sits there, we'd be modifying `yz`'s view of the string. That's no good, so we gotta **clone** the `FrontString` and mutate the copy.
//!
//! ![adsf](assets/char_list_ex_4.svg)

mod char_list;
mod pq_rc;

pub use crate::char_list::*;
