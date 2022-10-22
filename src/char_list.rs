use front_vec::FrontString;

use crate::pq_rc::PqRc;

type Len = usize;

pub struct CharList {
    data: PqRc<FrontString, Len>,
}

impl CharList {
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    pub fn len(&self) -> usize {
        PqRc::priority(&self.data)
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            data: PqRc::new(FrontString::with_capacity(capacity), 0),
        }
    }

    pub fn cons(&self, ch: char) -> Self {
        Self {
            data: unsafe {
                PqRc::mutate_or_clone(
                    &self.data,
                    |string_mut| {
                        string_mut.push_char_front(ch);
                        ch.len_utf8()
                    },
                    |_string_ref| {
                        let mut new_string = FrontString::from(self.as_ref());
                        new_string.push_char_front(ch);
                        (ch.len_utf8(), new_string)
                    },
                )
            },
        }
    }

    pub fn car_cdr(&self) -> (char, Self) {
        todo!()
    }
}

impl AsRef<str> for CharList {
    fn as_ref(&self) -> &str {
        &self.data[self.data.len() - self.len()..]
    }
}
