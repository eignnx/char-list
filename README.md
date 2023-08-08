# char-list
A persistent string type with the same API as a linked-list of characters.

## Docs
See the [docs](https://docs.rs/char-list/latest/char_list/) for memory-layout ***diagrams*** and explanations of how it all works.

## DISCLAIMER: `unsafe`
This crate is a work in progress. Specifically ***Not all uses of `unsafe` have been validated!*** Please don't use this for anything serious yet.

Safety audits are welcome and appreciated! I'm still quite new to writing `unsafe` code.

Also, this crate depends on [`front-vec`](https://crates.io/crates/front-vec) which is also badly in need of auditing.

## Example

```rust
use assert2::assert; // For nicer assertions.
let icon = CharList::from("icon");
let nomicon = icon.cons_str("nom");
let rustonomicon = nomicon.cons_str("rusto");
let rustonomicon2 = rustonomicon.clone(); // Cloning only copys two words.

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
