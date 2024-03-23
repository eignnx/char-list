use crate::{CharList, CharListTail};

impl<Tail: CharListTail> CharList<Tail> {
    pub fn partial_segments(&self) -> SegmentWalker<Tail> {
        SegmentWalker {
            cl: Some(self),
            err: None,
        }
    }
}

pub struct SegmentWalker<'a, Tail: CharListTail> {
    cl: Option<&'a CharList<Tail>>,
    err: Option<Tail::Err>,
}

impl<'a, Tail: CharListTail> SegmentWalker<'a, Tail> {
    /// To be used after the iterator has been consumed. Checks to see if the
    /// final tail in the `CharList` gave an error (for instance "tail variable
    /// was not sufficiently instantiated").
    pub fn final_err(&self) -> &Option<Tail::Err> {
        &self.err
    }
}

impl<'a, Tail: CharListTail> Iterator for SegmentWalker<'a, Tail> {
    type Item = &'a CharList<Tail>;

    fn next(&mut self) -> Option<Self::Item> {
        let old = self.cl?;
        let nxt = match self.cl?.tail().next_char_list() {
            Ok(opt_seg) => opt_seg,
            Err(e) => {
                self.err = Some(e);
                None
            }
        };
        self.cl = nxt;
        Some(old)
    }
}
