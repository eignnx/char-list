pub mod finite;
pub mod seg_walker;
#[cfg(test)]
mod tests;
mod trait_impls;

use std::{
    fmt,
    io::{self, Read},
    str::Utf8Error,
    string::FromUtf8Error,
};

use front_vec::FrontString;
use tracing::instrument;

use crate::pq_rc::PqRc;

type Len = usize;

/// An efficient string type with the same API as a linked-list of characters.
///
/// # Notable Methods
/// 1. [`cons`](crate::CharList::cons) which immutably prepends a character
///    ([`cons_str`](crate::CharList::cons_str) is also available), and
/// 2. [`car_cdr`](crate::CharList::car_cdr) which immutably splits `self`
///    into its first character and everything except the first character.
///
/// # Note: `CharList: !Deref<Target=str>`
/// This type specifically does **not** implement `Deref<Target=str>`. It cannot
/// because it's too generic, and might have a tail with more text. For a
/// version that does implement this trait, see [`FiniteCharList`].
pub struct CharList<Tail: CharListTail = finite::NoTail> {
    data: PqRc<StringRepr<Tail>, Len>,
}

/// Helper struct. Allows users of `CharList` to (optionally) store extra data
/// in the allocated `PqRcCell`.
#[derive(Clone)]
struct StringRepr<Tail: CharListTail> {
    front_string: FrontString,
    tail: Tail,
}

pub trait CharListTail: Clone + Default {
    type Err: fmt::Debug + fmt::Display;

    /// Returns `Ok(Some(..))` if there is a next `CharList`. If there's no next
    /// `CharList`, returns `Ok(None)`. If an answer can't be given, returns
    /// `Err(..)`.
    fn next_char_list(&self) -> Result<Option<&CharList<Self>>, Self::Err>;

    fn len(&self) -> Result<usize, Self::Err>;

    fn is_empty(&self) -> Result<bool, Self::Err> {
        Ok(self.len()? == 0)
    }
}

impl<Tail: CharListTail> CharList<Tail> {
    /// Creates an empty `CharList`.
    ///
    /// # Example
    ///
    /// ```
    /// # use char_list::CharList;
    /// # use assert2::assert;
    /// let empty = CharList::new();
    /// assert!(empty.len() == 0);
    /// ```
    pub fn new() -> Self {
        Self::with_capacity_and_tail(0, Default::default())
    }

    /// Creates a `CharList` whose backing [`FrontString`](front_string::FrontString)
    /// begins with the capacity specified.
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_tail(capacity, Default::default())
    }

    pub fn from_utf8(vec: Vec<u8>) -> Result<Self, FromUtf8Error> {
        let s = String::from_utf8(vec)?;
        Ok(Self::from_string_and_tail(s, Default::default()))
    }

    pub fn from_utf8_lossy(bytes: &[u8]) -> Self {
        let s: String = String::from_utf8_lossy(bytes).into();
        Self::from_string_and_tail(s, Default::default())
    }

    pub fn new_with_tail(tail: Tail) -> Self {
        Self::with_capacity_and_tail(0, tail)
    }

    /// Creates a `CharList` whose backing [`FrontString`](front_string::FrontString)
    /// begins with the capacity specified.
    #[instrument(skip(tail))]
    pub fn with_capacity_and_tail(capacity: usize, tail: Tail) -> Self {
        Self {
            data: PqRc::new(
                StringRepr {
                    front_string: FrontString::with_capacity(capacity),
                    tail,
                },
                0,
            ),
        }
    }

    /// For a `CharList<Tail>`, returns a reference to the inner `Tail` value.
    pub fn tail(&self) -> &Tail {
        &self.data.tail
    }

    /// Returns a string slice of this segment's portion of the string. Ignores
    /// any tail that may be present.
    ///
    /// Note: for `CharList<()>` (`()` is the default type parameter for
    /// `CharList`) this is the same as [`as_str`](CharList::as_str).
    pub fn segment_as_str(&self) -> &str {
        // Memory Diagram:
        //
        // |<--------backing_string().capacity()----------->|
        // [?????UNINIT????|***NOT MINE***|******SELF*******]
        //                 |--seg_start-->|<-segment_len()->|
        //                 |<----------slice.len()--------->|
        let slice: &str = self.backing_string().as_ref();
        let seg_start = slice.len() - self.segment_len();
        &slice[seg_start..]
    }

    /// Returns a byte slice of this segment's portion of the string. Ignores
    /// any tail that may be present.
    ///
    /// Note: for `CharList<()>` (`()` is the default type parameter for
    /// `CharList`) this is the same as [`as_bytes`](CharList::as_bytes).
    pub fn segment_as_bytes(&self) -> &[u8] {
        self.segment_as_str().as_bytes()
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
    /// assert!(foo.len() == Ok(3));
    ///
    /// let fancy_foo = CharList::from("ƒoo"); // fancy f!
    /// assert!(fancy_foo.len() == Ok(4));
    /// assert!(fancy_foo.chars().count() == 3);
    /// ```
    #[instrument(ret, skip(self), fields(repr = %self))]
    pub fn len(&self) -> Result<usize, Tail::Err> {
        Ok(self.segment_len() + self.tail().len()?)
    }

    /// Returns as much of the length of the string as is possible to know right
    /// now.
    pub fn partial_len(&self) -> usize {
        self.partial_segments().map(|seg| seg.segment_len()).sum()
    }

    /// Returns the length of this segment, ignoring any tail.
    ///
    /// # Example
    /// If the underlying buffers looked like this:
    ///
    /// ```ignore
    /// [?, ?, ?, 'a', 'b', 'c'] --> [?, ?, 'd', 'e', 'f']
    /// ```
    /// Then a `CharList` representing the string "cdef" would have a
    /// `segment_len` of one (1). A `CharList` for "abcdef" would have
    /// `segment_len` three (3).
    #[instrument(ret, skip(self))]
    pub fn segment_len(&self) -> usize {
        PqRc::priority(&self.data)
    }

    pub fn is_empty(&self) -> Result<bool, Tail::Err> {
        if self.segment_len() != 0 {
            return Ok(false);
        }

        let Some(tail) = self.tail().next_char_list()? else {
            return Ok(true);
        };

        tail.len().map(|l| l == 0)
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
    #[instrument]
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
    #[instrument(ret, fields(s = s.as_ref()))]
    pub fn cons_str(&self, s: impl AsRef<str>) -> Self {
        let s = s.as_ref();
        Self {
            data: unsafe {
                PqRc::mutate_or_clone_raising_prio(
                    &self.data,
                    |repr_mut| {
                        repr_mut.front_string.push_str_front(s);
                        s.len()
                    },
                    |_string_ref| {
                        let mut new_string = FrontString::from(self.segment_as_str());
                        new_string.push_str_front(s);
                        let repr = StringRepr {
                            front_string: new_string,
                            tail: self.tail().clone(),
                        };
                        (s.len(), repr)
                    },
                )
            },
        }
    }

    pub fn cons_char_list(&self, prefix: &Self) -> Self {
        let prefix_len = prefix.partial_len();

        let pqrc = unsafe {
            PqRc::mutate_or_clone_raising_prio(
                &self.data,
                |repr_mut| {
                    for seg in prefix.partial_segments() {
                        repr_mut
                            .front_string
                            .prepend_from_bytes_iter(seg.segment_as_bytes().iter().copied());
                    }
                    prefix_len
                },
                |_repr_ref| {
                    let mut new_string = FrontString::from(self.segment_as_str());

                    for seg in prefix.partial_segments() {
                        new_string.prepend_from_bytes_iter(seg.segment_as_bytes().iter().copied());
                    }

                    let repr = StringRepr {
                        front_string: new_string,
                        tail: self.tail().clone(),
                    };

                    (prefix_len, repr)
                },
            )
        };

        Self { data: pqrc }
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
    /// ```
    ///
    /// ```
    /// # use char_list::CharList;
    /// # use assert2::assert;
    /// let empty = CharList::new();
    /// assert!(empty.car_cdr() == None);
    /// ```
    #[track_caller]
    pub fn car_cdr(&self) -> Result<Option<(char, Self)>, Tail::Err> {
        let Some(first_char) = self.segment_as_str().chars().next() else {
            return Ok(None);
        };
        let new_len = self.segment_len() - first_char.len_utf8();
        let cdr = Self {
            data: PqRc::clone_with_priority(&self.data, new_len),
        };
        Ok(Some((first_char, cdr)))
    }

    /// # Safety
    /// See [`str::from_utf8_unchecked`](std::str::from_utf8_unchecked) for
    /// safety requirements.
    pub unsafe fn from_utf8_unchecked(bytes: &[u8]) -> Self {
        // SAFETY: Defer to caller.
        let s = unsafe { std::str::from_utf8_unchecked(bytes) };
        let s = s.to_owned();
        Self::from_string_and_tail(s, Default::default())
    }

    /// Get an immutable reference to the backing [`FrontString`](front_vec::FrontString).
    pub fn backing_string(&self) -> &FrontString {
        &PqRc::inner(&self.data).front_string
    }

    #[instrument(skip(s, tail))]
    pub fn from_string_and_tail(s: impl Into<String>, tail: Tail) -> Self {
        let front_string: FrontString = FrontString::from(s.into());
        tracing::Span::current().record("s", front_string.to_string());
        let priority = front_string.len();
        Self {
            data: PqRc::new(StringRepr { front_string, tail }, priority),
        }
    }

    pub fn from_utf8_and_tail(bytes: &[u8], tail: Tail) -> Result<Self, Utf8Error> {
        let s = std::str::from_utf8(bytes)?;
        Ok(Self::from_string_and_tail(s, tail))
    }

    pub fn from_utf8_lossy_and_tail(bytes: &[u8], tail: Tail) -> Self {
        Self::from_string_and_tail(String::from_utf8_lossy(bytes).into_owned(), tail)
    }

    pub fn from_io_readable(readable: &mut impl Read) -> io::Result<Self> {
        // TODO: optimize
        let mut buf = String::new();
        let _ = readable.read_to_string(&mut buf)?;
        Ok(Self::from(buf))
    }

    pub fn prepend_from_bytes_iter(
        &self,
        it: impl ExactSizeIterator<Item = u8>,
    ) -> Result<Self, FromUtf8Error> {
        let v = it.collect::<Vec<_>>();
        let s = String::from_utf8(v)?;
        Ok(self.cons_str(s))
    }

    /// Returns a `CharList` with the same data as `self` but with an
    /// underlying `FrontString` buffer whose capacity is
    /// `additional_bytes + self.segment_len()`.
    ///
    /// If this `CharList` has highest priority, the underlying `FrontString`'s
    /// `reserve_front` method will be called. Otherwise, the `FrontString` will
    /// be cloned, it's `reserve_front` method called, and a new `CharList`
    /// returned.
    #[must_use = "`CharList::reserving` returns a new `CharList`, it doesn't mutate the current one in place."]
    #[allow(dead_code)]
    fn reserving(&self, additional_bytes: usize) -> Self {
        let pqrc = unsafe {
            PqRc::mutate_or_clone_raising_prio(
                &self.data,
                |mut_s| {
                    mut_s.front_string.reserve_front(additional_bytes);
                    0
                },
                |ref_s| {
                    let mut s = ref_s.clone();
                    s.front_string.reserve_front(additional_bytes);
                    (0, s)
                },
            )
        };
        Self { data: pqrc }
    }
}
