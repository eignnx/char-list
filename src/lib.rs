#![feature(new_uninit, nonzero_min_max, ptr_as_uninit, pattern)]
#![deny(unsafe_op_in_unsafe_fn)]

//!
// Important: note the blank line of documentation on each side of the image lookup table.
// The "image lookup table" can be placed anywhere, but we place it here together with the
// warning if the `doc-images` feature is not enabled.
#![cfg_attr(feature = "doc-images",
    cfg_attr(all(),
    doc = ::embed_doc_image::embed_image!("ex1", "images/char_list_ex_1.svg"),
    doc = ::embed_doc_image::embed_image!("ex2", "images/char_list_ex_2.svg"),
    doc = ::embed_doc_image::embed_image!("ex3", "images/char_list_ex_3.svg"),
    doc = ::embed_doc_image::embed_image!("ex4", "images/char_list_ex_4.svg"),
))]
#![cfg_attr(
    not(feature = "doc-images"),
    doc = "**Doc images not enabled**. Compile with feature `doc-images` and Rust version >= 1.54 \
           to enable."
)]
//!
//! A persistent string type with the same API as a linked-list of characters.
//!
//! ## DISCLAIMER: `unsafe`
//! This crate is a work in progress. Specifically ***Not all uses of `unsafe` have been validated!*** Please don't use this for anything serious yet.
//!
//! Safety audits are welcome and appreciated! I'm still quite new to writing `unsafe` code.
//!
//! Also, this crate depends on [`front-vec`](https://crates.io/crates/front-vec) which is also badly in need of auditing.
//!
//! ## Internal Representation
//! This crate relies on [`front_vec::FrontString`](https://docs.rs/front-vec/latest/front_vec/struct.FrontString.html) to store arrays of bytes which allow for efficient prepending (pushing characters onto the front of the array).
//!
//! Each `FrontString` is owned by a `PqRcCell` (internal to this crate, soon to be it's own crate) which is sorta like a cross between a `RefCell` and a `RcBox` (the thing an `Rc` pointer points to).
//!
//! A `CharList` is just a pointer + length (though it's not a slice) which refers to a specific slice of a `PqRcCell`-managed `FrontString`.
//!
//! The `PqRcCell` ensures that out of all `CharList`s which refer to it's `FrontString`, only those with the **longest length** are allowed to mutate the inner `FrontString` value. And they can only\* mutate it in ways that other `CharList`s won't notice.
//!
//! \* (Ok, at this point we make developers pinky-swear 🤞 they'll follow those rules, and they gotta wrap their use in an `unsafe` block. Maybe there's a better way to do this in the future though 🤔)
//!
//! That was a lotta words, let's look at an example with memory diagrams.
//!
//! ### Memory Diagram
//!
//! #### Note: Simplified Diagrams
//! Every time the word `len` or `refs` appears in these diagrams, in the code it corresponds to either `priority` or `priorities`. The internal representation of a `CharList` is actually just a `PqRc` (Priority Queue Reference Counted) pointer which abstracts over its priority. For `CharList`s, priority is the same as string length.
//!
//! #### Example
//! Consider this code:
//!
//! ```
//! # use char_list::CharList;
//! use assert2::assert; // For nicer assertions.
//! let icon = CharList::from("icon");
//! let nomicon = icon.cons_str("nom");
//! let rustonomicon = nomicon.cons_str("rusto");
//! let rustonomicon2 = rustonomicon.clone();
//!
//! assert!(icon == "icon");
//! assert!(nomicon == "nomicon");
//! assert!(rustonomicon == "rustonomicon");
//! assert!(rustonomicon == rustonomicon2);
//! ```
//!
//! These values would be represented in memory like this:
//!
//! ![did it work?][ex1]
//!
//! (The arrows with dashed lines represent the *implied* beginnings of `CharList` slices, i.e. `icon` implicitly "refers to" the last four bytes in the buffer.)
//!
//! Notice that all `cons_str` and `clone` operations are immutable, i.e. they create new `CharList`s instead of mutating the original.
//!
//! #### One More `cons`
//!
//! ```
//! # use char_list::CharList;
//! # use assert2::assert;
//! # let icon = CharList::from("icon");
//! # let nomicon = icon.cons_str("nom");
//! # let rustonomicon = nomicon.cons_str("rusto");
//! # let rustonomicon2 = rustonomicon.clone();
//! #
//! # assert!(icon == "icon");
//! # assert!(nomicon == "nomicon");
//! # assert!(rustonomicon == "rustonomicon");
//! # assert!(rustonomicon == rustonomicon2);
//! #
//! let the_book = rustonomicon.cons_str("the ");
//! assert!(the_book == "the rustonomicon");
//! ```
//!
//! Here's what memory looks like now:
//!
//! ![did it work?][ex2]
//!
//! Because `rustonomicon` has the longest length in the `refs` table, it's perfectly safe to call the underlying `FrontString`'s `push_char_front` method (mutably!).
//!
//! Notice that by pushing a character onto the front, `rustonomicon` doesn't affect **any other `CharList`'s view** of the underlying `FrontString`.
//!
//! #### Dropping
//!
//! Ok now what happens if we `drop` the longest three `CharList`s?
//!
//! ```
//! # use char_list::CharList;
//! # use assert2::assert;
//! # let icon = CharList::from("icon");
//! # let nomicon = icon.cons_str("nom");
//! # let rustonomicon = nomicon.cons_str("rusto");
//! # let rustonomicon2 = rustonomicon.clone();
//! #
//! # assert!(icon == "icon");
//! # assert!(nomicon == "nomicon");
//! # assert!(rustonomicon == "rustonomicon");
//! # assert!(rustonomicon == rustonomicon2);
//! #
//! # let the_book = rustonomicon.cons_str("the ");
//! # assert!(the_book == "the rustonomicon");
//! #
//! drop(rustonomicon);
//! drop(the_book);
//! drop(rustonomicon2);
//! ```
//!
//! ![did it work?][ex3]
//!
//! Notice that the internal `FrontString`'s `len` went down to 7. This means we can reuse the memory that used to be held by the longer strings!
//!
//! #### Tricky `cons`
//!
//! Here's a problem though. What if we want to `cons` the character `'b'` onto the front of `icon`?
//!
//! ```
//! # use char_list::CharList;
//! # use assert2::assert;
//! # let icon = CharList::from("icon");
//! # let nomicon = icon.cons_str("nom");
//! # let rustonomicon = nomicon.cons_str("rusto");
//! # let rustonomicon2 = rustonomicon.clone();
//! #
//! # assert!(icon == "icon");
//! # assert!(nomicon == "nomicon");
//! # assert!(rustonomicon == "rustonomicon");
//! # assert!(rustonomicon == rustonomicon2);
//! #
//! # let the_book = rustonomicon.cons_str("the ");
//! # assert!(the_book == "the rustonomicon");
//! #
//! # drop(rustonomicon);
//! # drop(the_book);
//! # drop(rustonomicon2);
//! #
//! let janelle_monae = icon.cons('b');
//! assert!(janelle_monae == "bicon");
//! ```
//!
//! Well, if we overwrite the `'m'` that currently sits in front of "icon", we'd be modifying `nomicon`'s view of the string. That's no good, so we gotta **clone** `icon`'s view of the `FrontString` and mutate the copy.
//!
//! ![did it work?][ex4]
//!

mod char_list;
mod pq_rc;

pub use crate::char_list::*;
