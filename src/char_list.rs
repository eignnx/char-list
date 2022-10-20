use std::rc::Rc;

use crate::char_buf::CharBuf;

pub struct CharList {
    len: usize,
    data: Rc<CharBuf>,
}

impl CharList {
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            len: 0,
            data: Rc::new(CharBuf::with_capacity(capacity)),
            // data: Rc::new(FrontString::with_capacity(capacity)),
        }
    }

    pub fn cons(&self, ch: char) -> Self {
        todo!()
    }

    pub fn car_cdr(&self) -> (char, Self) {
        todo!()
    }
}
