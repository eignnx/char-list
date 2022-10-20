use std::collections::BinaryHeap;

use front_vec::FrontString;

use crate::multi::Multi;

type Len = usize;

pub struct CharBuf {
    priorities: BinaryHeap<Multi<Len>>,
    string: FrontString,
}

impl CharBuf {
    pub fn with_capacity(capacity: usize) -> CharBuf {
        todo!()
    }
}
