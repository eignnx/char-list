use crate::{CharList, CharListTail};

impl<Tail: CharListTail> CharList<Tail> {
    pub fn partial_segments(&self) -> SegmentWalker<Tail> {
        SegmentWalker { cl: Some(self) }
    }
}

pub struct SegmentWalker<'a, Tail: CharListTail> {
    cl: Option<&'a CharList<Tail>>,
}

impl<'a, Tail: CharListTail> Iterator for SegmentWalker<'a, Tail> {
    type Item = &'a CharList<Tail>;

    fn next(&mut self) -> Option<Self::Item> {
        let old = self.cl?;
        let nxt = self.cl?.tail().next_char_list().ok()?;
        self.cl = nxt;
        Some(old)
    }
}
