use super::{CharList, CharListTail};

pub struct Bytes<Tail: CharListTail> {
    pub char_list: CharList<Tail>,
    // # Note
    // I want to track the offset in the current segment with a `usize`. I
    // realize that I could create a new `CharList` after each `next` call, but
    // that requires:
    //     1. Dereferencing the `PqRc` to get the `PqRcCell`, and
    //     2. Indexing into (at least 1 dereference) the `PqRcCell`'s `BTreeMap`
    //        to update indices.
    // I think it'd be faster to just keep an extra index.
    pub offset_in_segment: usize,
}

impl<Tail: CharListTail> Iterator for Bytes<Tail> {
    type Item = u8;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self
                .char_list
                .segment_as_bytes()
                .get(self.offset_in_segment)
            {
                Some(&byte) => {
                    self.offset_in_segment += 1;
                    return Some(byte);
                }
                None => {
                    self.char_list = self.char_list.tail().next_char_list()?;
                    self.offset_in_segment = 0;
                    continue;
                }
            }
        }
    }
}

impl<Tail: CharListTail> ExactSizeIterator for Bytes<Tail> {
    fn len(&self) -> usize {
        self.char_list.len() - self.offset_in_segment
    }
}
