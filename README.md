# char-list
A persistent string type with the same API as a linked-list of characters.

## Docs
See the [docs](https://docs.rs/char-list/latest/char_list/) for memory-layout ***diagrams*** and explanations of how it all works.

## DISCLAIMER: `unsafe`
This crate is a work in progress. Specifically ***Not all uses of `unsafe` have been validated!*** Please don't use this for anything serious yet.

Safety audits are welcome and appreciated! I'm still quite new to writing `unsafe` code.

Also, this crate depends on [`front-vec`](https://crates.io/crates/front-vec) which is also badly in need of auditing.