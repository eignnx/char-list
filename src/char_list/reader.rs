use std::io::Read;

use super::{CharList, CharListTail};

pub struct CharListReader<Tail: CharListTail> {
    pub char_list: Option<CharList<Tail>>,
}

impl<Tail: CharListTail> Read for CharListReader<Tail> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let Some(char_list) = &self.char_list else {
            return Ok(0);
        };

        let slice_in_segment = char_list.segment_as_bytes();
        let src = slice_in_segment.as_ptr();
        let dst = buf.as_mut_ptr();
        let bytes_to_copy = usize::min(slice_in_segment.len(), buf.len());

        // SAFETY:
        // * Both `src` and `dst` have at least `to_copy` bytes because of the
        //   call to `usize::min` on their lengths.
        // * Both are properly aligned since they come directly from references.
        // * They do not overlap because both pointers come from `&mut`
        //   exclusive references.
        unsafe {
            std::ptr::copy_nonoverlapping(src, dst, bytes_to_copy);
        }

        self.char_list = char_list.tail().next_char_list();

        Ok(bytes_to_copy)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert2::{assert, let_assert};

    #[test]
    fn read_no_tail() {
        let cl = CharList::<()>::from("asdf");
        let mut buf = String::new();
        let mut r = cl.reader();
        let_assert!(Ok(_) = r.read_to_string(&mut buf));
        assert!(buf == "asdf");
    }
}
