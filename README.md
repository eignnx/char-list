# char-list
A persistent string type with the same API as a linked-list of characters.

## Contents
### `FiniteCharList`
The `FiniteCharList` type is probably what you want to use. It behaves just like a linked list of characters but with better (TODO: verify) performance.

### `CharList<Tail>`
The `CharList<Tail>` type allows customization of the data structure by allowing a custom tail. I'm using this to emulate Prolog's open-ended lists where the tail of the list may be an uninstantiated Prolog variable.

A `FiniteCharList` is just a type alias for `CharList<()>`.

Generic `CharList`s have much fewer abilities provided by this crate because the nature of the tail is unknown. For instance, `CharList<Tail>` does *not* implement `AsRef<str>` or even `PartialEq`!

The intention is that you will wrap a `CharList<YourTail>` in a newtype and implement those traits if it makes sense for your problem space. For example, I (plan to) use a `CharList<ast::Expression>` which *will* implement `PartialEq` because I want syntactic equality.

## Docs
See the [docs](https://docs.rs/char-list/latest/char_list/) for memory-layout ***diagrams*** and explanations of how it all works.

## DISCLAIMER: `unsafe`
This crate is a work in progress. Specifically ***Not all uses of `unsafe` have been validated!*** Please don't use this for anything serious yet.

Safety audits are welcome and appreciated! I'm still quite new to writing `unsafe` code.

Also, this crate depends on [`front-vec`](https://crates.io/crates/front-vec) which is also badly in need of auditing.

## Example

```rust
use assert2::assert; // For nicer assertions.
let icon = FiniteCharList::from("icon");
let nomicon = icon.cons_str("nom");
let rustonomicon = nomicon.cons_str("rusto");

// Cloning requires
//     1) copying two words, and
//     2) performing one BTreeMap lookup.
let rustonomicon2 = rustonomicon.clone();

assert!(icon == "icon");
assert!(nomicon == "nomicon");
assert!(rustonomicon == "rustonomicon");
assert!(rustonomicon == rustonomicon2);

// No new allocations required (if underlying buffer capacity allows).
// Mutably prepends the `&str` to the buffer without shifting memory.
let the_book = rustonomicon.cons_str("the ");
assert!(the_book == "the rustonomicon");

// Drop to mutably resize underlying buffer and 
drop(rustonomicon);
drop(the_book);
drop(rustonomicon2);

let janelle_monae = icon.cons('b'); // Duplication required now.
assert!(janelle_monae == "bicon");
```
