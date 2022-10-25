use std::{
    borrow::Borrow,
    fmt,
    hash::Hash,
    ops::{Add, AddAssign},
    str::pattern::Pattern,
    string::FromUtf8Error,
};

use front_vec::FrontString;

use crate::pq_rc::PqRc;

type Len = usize;

pub struct CharList {
    data: PqRc<FrontString, Len>,
}

impl CharList {
    /// Creates an empty `CharList`.
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Returns the length of `self`.
    ///
    /// This length is in bytes, not [`char`]s or graphemes. In other words,
    /// it might not be what a human considers the length of the string.
    ///
    /// [`char`]: prim@char
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use char_list::CharList;
    /// # use assert2::assert;
    /// let foo = CharList::from("foo");
    /// assert!(foo.len() == 3);
    ///
    /// let fancy_foo = CharList::from("ƒoo"); // fancy f!
    /// assert!(fancy_foo.len() == 4);
    /// assert!(fancy_foo.chars().count() == 3);
    /// ```
    pub fn len(&self) -> usize {
        PqRc::priority(&self.data)
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn chars(&self) -> std::str::Chars {
        self.as_str().chars()
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            data: PqRc::new(FrontString::with_capacity(capacity), 0),
        }
    }

    /// Creates a new [`CharList`] which is a copy of `self`, but with the
    /// given character added onto the front.
    ///
    /// # Example
    ///
    /// ```
    /// # use char_list::CharList;
    /// # use assert2::assert;
    /// let lick = CharList::from("lick");
    /// let slick = lick.cons('s');
    /// assert!(slick == "slick");
    /// ```
    pub fn cons(&self, ch: char) -> Self {
        let mut buf = [0u8; 4];
        self.cons_str(ch.encode_utf8(&mut buf))
    }

    /// Creates a new [`CharList`] which is a copy of `self`, but with the
    /// contents of the given [`&str`] added onto the front.
    ///
    /// # Example
    ///
    /// ```
    /// # use char_list::CharList;
    /// # use assert2::assert;
    /// let tonic = CharList::from("tonic");
    /// let uh_oh = tonic.cons_str("cata");
    /// assert!(uh_oh == "catatonic");
    /// ```
    pub fn cons_str(&self, s: impl AsRef<str>) -> Self {
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

    /// Returns a pair containing the first character of `self` and a
    /// [`CharList`] made up of everything after the first character of `self`.
    ///
    /// Returns [`None`] if `self` is empty.
    ///
    /// # Example
    ///
    /// ```
    /// # use char_list::CharList;
    /// # use assert2::assert;
    /// let (g, oats) = CharList::from("goats").car_cdr().unwrap();
    /// assert!((g, oats) == ('g', CharList::from("oats")));
    ///
    /// let empty = CharList::new();
    /// assert!(empty.car_cdr() == None);
    /// ```
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

    /// Extracts a string slice which references `self`'s entire view of the
    /// underlying text.
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }

    pub fn from_utf8(vec: Vec<u8>) -> Result<Self, FromUtf8Error> {
        String::from_utf8(vec).map(Self::from)
    }

    pub fn from_utf8_lossy(bytes: &[u8]) -> Self {
        String::from_utf8_lossy(bytes).into_owned().into()
    }

    /// # Safety
    /// See [`str::from_utf8_unchecked`](std::str::from_utf8_unchecked) for
    /// safety requirements.
    pub unsafe fn from_utf8_unchecked(bytes: &[u8]) -> Self {
        // SAFETY: Defer to caller.
        let s = unsafe { std::str::from_utf8_unchecked(bytes) };
        Self::from(s)
    }

    /// Returns an optional `CharList` representing `self` if `prefix` had been
    /// removed from the front.
    ///
    /// ```
    /// # use char_list::CharList;
    /// # use assert2::assert;
    /// let creepy_book = CharList::from("necronomicon");
    /// let informational_book = creepy_book.without_prefix("necro");
    /// assert!(informational_book == Some(CharList::from("nomicon")));
    /// ```
    pub fn without_prefix<'a, P>(&'a self, prefix: P) -> Option<Self>
    where
        P: Pattern<'a>,
    {
        self.as_str().strip_prefix(prefix).map(|sub| Self {
            data: PqRc::clone_with_priority(&self.data, sub.len()),
        })
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

impl<S> PartialOrd<S> for CharList
where
    S: AsRef<str>,
{
    fn partial_cmp(&self, other: &S) -> Option<std::cmp::Ordering> {
        self.as_ref().partial_cmp(other.as_ref())
    }
}

impl Ord for CharList {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_ref().cmp(other.as_ref())
    }
}

impl Hash for CharList {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_ref().hash(state);
    }
}

impl Default for CharList {
    fn default() -> Self {
        Self::new()
    }
}

impl FromIterator<char> for CharList {
    /// Given an iterator over the `&str` `"abc"`, the `CharList` `"abc"`
    /// will be created.
    fn from_iter<I: IntoIterator<Item = char>>(iter: I) -> Self {
        let string = String::from_iter(iter);
        Self::from(string)
    }
}

impl Add<CharList> for CharList {
    type Output = CharList;
    fn add(self, rhs: CharList) -> Self::Output {
        rhs.cons_str(self.as_ref())
    }
}

impl AddAssign<CharList> for String {
    fn add_assign(&mut self, rhs: CharList) {
        self.push_str(rhs.as_ref())
    }
}

impl Borrow<str> for CharList {
    fn borrow(&self) -> &str {
        self.as_ref()
    }
}

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

        let icon = empty.cons_str("icon");
        assert!(icon == "icon");
        assert!(underlying(&empty) == &"icon");

        let nomicon = icon.cons_str("nom");
        assert!(nomicon == "nomicon");
        assert!(underlying(&empty) == &"nomicon");

        let rustonomicon = nomicon.cons_str("rusto");
        assert!(rustonomicon == "rustonomicon");
        assert!(underlying(&empty) == &"rustonomicon");

        let nominomicon = nomicon.cons_str("nomi");
        assert!(nominomicon == "nominomicon");
        assert!(underlying(&empty) == &"rustonomicon");
        assert!(underlying(&nominomicon) == &"nominomicon");
    }
}
