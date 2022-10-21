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
        self.data.priority()
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            data: PqRc::new(FrontString::with_capacity(capacity), 0),
        }
    }

    pub fn cons(&self, ch: char) -> Self {
        unsafe {
            Self {
                data: self.data.mutate_or_clone(
                    |string_mut| {
                        string_mut.push_char_front(ch);
                        ch.len_utf8()
                    },
                    |_string_ref| {
                        let mut new_string = FrontString::from(self.as_ref());
                        new_string.push_char_front(ch);
                        (ch.len_utf8(), new_string)
                    },
                ),
            }
        }
        // match unsafe { self.data.try_as_mut() } {
        //     Some(inner_mut) => {
        //         inner_mut.push_char_front(ch);

        //         Self {
        //             data: {
        //                 let new_len = self.len() + ch.len_utf8();
        //                 self.data.clone_with_new_priority(new_len)
        //             },
        //         }
        //     }
        //     None => {
        //         let mut cloned_front_string = FrontString::from(self.as_ref());
        //         cloned_front_string.push_char_front(ch);
        //         let new_len = self.len() + ch.len_utf8();
        //         Self {
        //             data: PqRc::new(cloned_front_string, new_len),
        //         }
        //     }
        // }
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
