use std::fmt;

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

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            data: PqRc::new(FrontString::with_capacity(capacity), 0),
        }
    }

    pub fn cons(&self, ch: char) -> Self {
        let mut buf = [0u8; 4];
        self.push_str_front(ch.encode_utf8(&mut buf))
    }

    pub fn push_str_front(&self, s: impl AsRef<str>) -> Self {
        let s = s.as_ref();
        Self {
            data: unsafe {
                PqRc::mutate_or_clone(
                    &self.data,
                    |string_mut| {
                        string_mut.push_str_front(s);
                        s.len()
                    },
                    |_string_ref| {
                        let mut new_string = FrontString::from(self.as_ref());
                        new_string.push_str_front(s);
                        (s.len(), new_string)
                    },
                )
            },
        }
    }

    pub fn car_cdr(&self) -> Option<(char, Self)> {
        if self.is_empty() {
            return None;
        }

        let ch = self
            .as_ref()
            .chars()
            .next()
            .expect("guard at top of fn ensures non-empty string");

        let pq_rc = PqRc::clone_with_priority(&self.data, self.len() - ch.len_utf8());
        let cl = Self { data: pq_rc };

        Some((ch, cl))
    }
}

impl Drop for CharList {
    fn drop(&mut self) {
        if let Some(front_string) = unsafe { PqRc::try_as_mut(&self.data) } {
            if PqRc::uniquely_highest_priority(&self.data) {
                if let Some(next_highest) = PqRc::second_highest_priority(&self.data) {
                    let mut to_pop = self.len() - next_highest;
                    while to_pop != 0 {
                        let ch = front_string
                            .pop_char_front()
                            .expect("non-empty since we're in `if let Some` case");
                        to_pop -= ch.len_utf8();
                    }
                }
            }
        }
    }
}

impl AsRef<str> for CharList {
    fn as_ref(&self) -> &str {
        &self.data[self.data.len() - self.len()..]
    }
}

impl From<&str> for CharList {
    fn from(s: &str) -> Self {
        Self {
            data: PqRc::new_from(s, s.as_bytes().len()),
        }
    }
}

// TODO: Is there an EFFICIENT way to impl From<String> for FrontString?
// See this issue: https://github.com/eignnx/char-list/issues/1
impl From<String> for CharList {
    fn from(string: String) -> Self {
        let slice: &str = string.as_ref();
        slice.into()
    }
}

impl fmt::Debug for CharList {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let slice: &str = self.as_ref();
        write!(f, "{slice:?}")
    }
}

impl fmt::Display for CharList {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let slice: &str = self.as_ref();
        write!(f, "{slice}")
    }
}

impl<S> PartialEq<S> for CharList
where
    S: AsRef<str>,
{
    fn eq(&self, other: &S) -> bool {
        self.as_ref() == other.as_ref()
    }
}

impl Eq for CharList {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pq_rc::PqRc;
    use assert2::{assert, let_assert};

    fn underlying(cl: &CharList) -> &FrontString {
        PqRc::inner(&cl.data)
    }

    #[test]
    fn mem_test_cdr_down() {
        let s3 = CharList::from("abc");

        assert!(underlying(&s3).len() == 3);

        let_assert!(Some((a, s2)) = s3.car_cdr());
        assert!(a == 'a');
        assert!(s2 == "bc");

        assert!(underlying(&s3).len() == 3);

        let_assert!(Some((b, s1)) = s2.car_cdr());
        assert!(b == 'b');
        assert!(s1 == "c");

        drop(s3);
        assert!(underlying(&s1).len() == 2);

        let_assert!(Some((c, s0)) = s1.car_cdr());
        assert!(c == 'c');
        assert!(s0.is_empty());
        assert!(s0 == "");

        assert!(s0.car_cdr() == None);

        drop(s2);
        drop(s1);
        assert!(underlying(&s0).len() == 0);
    }

    #[test]
    fn mem_test_cons_up() {
        let empty = CharList::new();
        assert!(empty.is_empty());
        assert!(underlying(&empty) == &"");

        let icon = empty.push_str_front("icon");
        assert!(icon == "icon");
        assert!(underlying(&empty) == &"icon");

        let nomicon = icon.push_str_front("nom");
        assert!(nomicon == "nomicon");
        assert!(underlying(&empty) == &"nomicon");

        let rustonomicon = nomicon.push_str_front("rusto");
        assert!(rustonomicon == "rustonomicon");
        assert!(underlying(&empty) == &"rustonomicon");

        let nominomicon = nomicon.push_str_front("nomi");
        assert!(nominomicon == "nominomicon");
        assert!(underlying(&empty) == &"rustonomicon");
        assert!(underlying(&nominomicon) == &"nominomicon");
    }
}
