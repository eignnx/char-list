mod seg_walker;
#[cfg(test)]
mod tests;

use std::{
    convert::Infallible,
    fmt,
    hash::Hash,
    io::{self, Read},
    ops::Add,
    str::{pattern::Pattern, Utf8Error},
    string::FromUtf8Error,
};

use front_vec::FrontString;
use tracing::{error, instrument, trace};

use crate::pq_rc::PqRc;

type Len = usize;
pub type NoTail = ();

/// An efficient string type with the same API as a linked-list of characters.
///
/// # Notable Methods
/// 1. [`cons`](crate::CharList::cons) which immutably prepends a character
///    ([`cons_str`](crate::CharList::cons_str) is also available), and
/// 2. [`car_cdr`](crate::CharList::car_cdr) which immutably splits `self`
///    into its first character and everything except the first character.
///
/// # Note: `CharList: !Deref<Target=str>`
/// This type specifically does **not** implement `Deref<Target=str>`.
pub struct CharList<Tail: CharListTail = NoTail> {
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

impl CharListTail for NoTail {
    type Err = Infallible;

    fn next_char_list(&self) -> Result<Option<&CharList<Self>>, Infallible> {
        Ok(None)
    }

    fn len(&self) -> Result<usize, Self::Err> {
        Ok(0)
    }
}

impl CharList<NoTail> {
    /// Extracts a string slice which references `self`'s entire view of the
    /// underlying text.
    ///
    /// Same as [`<CharList as AsRef<str>>::as_ref`](char_list::CharList::as_ref).
    pub fn as_str(&self) -> &str {
        self.segment_as_str()
    }

    /// Extracts a byte slice which references `self`'s entire view of the
    /// underlying text.
    ///
    /// Same as [`<CharList as AsRef<[u8]>>::as_ref`](char_list::CharList::as_ref).
    pub fn as_bytes(&self) -> &[u8] {
        self.segment_as_bytes()
    }

    /// Separates `self` into a prefix (described by the `Pattern` `prefix`) and
    /// a suffix made of the remainder of the string.
    ///
    /// The `Pattern` `prefix` could be:
    /// * a `&str` giving an exact prefix to match,
    /// * a `char` giving an exact character prefix to match,
    /// * a predicate of type `FnMut(char) -> bool` which returns true for all
    ///   characters in the prefix.
    ///
    /// Notice that this function returns a pair containing two *different*
    /// string types: a `&str` for the found prefix, and a `CharList` for the
    /// suffix. The assumption is that the prefix (and the `CharList` which
    /// holds onto that section of the string) will be dropped before the suffix
    /// is dropped. This means, if possible, don't immediately create a new
    /// `CharList` from the prefix as this will allocate a *copy* of the text
    /// referenced by the prefix.
    ///
    /// ```
    /// # use char_list::CharList;
    /// # use assert2::assert;
    /// let creepy_book = CharList::from("necronomicon");
    /// let pair = creepy_book.split_after_prefix("necro");
    /// assert!(pair == ("necro", CharList::from("nomicon")));
    /// ```
    ///
    /// ```
    /// # use char_list::CharList;
    /// # use assert2::assert;
    /// let words = CharList::from("hello world");
    /// let (hello, rest) = words.split_after_prefix(char::is_alphabetic);
    /// assert!(hello == "hello");
    /// assert!(rest == " world");
    /// ```
    ///
    /// ```
    /// # use char_list::CharList;
    /// # use assert2::assert;
    /// let numbers = CharList::from("1253 39271 4542");
    /// let (first_word, rest) = numbers.split_after_prefix(char::is_alphabetic);
    /// assert!(first_word.is_empty());
    /// assert!(rest == numbers);
    /// ```
    pub fn split_after_prefix<'a>(&'a self, prefix: impl Pattern<'a>) -> (&'a str, Self) {
        let seg_remainder = self.as_str().trim_start_matches(prefix);
        self.split_at(self.len().expect("infallible") - seg_remainder.len())
    }

    /// Just like [`split_after_prefix`](char_list::CharList::split_after_prefix)
    /// except it will never return an empty prefix, instead returning `None` in
    /// that case.
    pub fn split_after_nonempty_prefix<'a>(
        &'a self,
        prefix: impl Pattern<'a>,
    ) -> Option<(&'a str, Self)> {
        use std::ops::Not;
        let (prefix, suffix) = self.split_after_prefix(prefix);
        prefix.is_empty().not().then_some((prefix, suffix))
    }

    /// For the argument `idx`, returns the pair `(prefix, suffix)` where
    /// `prefix` ends just before byte-index `idx`, and `suffix` begins at
    /// byte-index `idx`.
    ///
    /// The `String` created from `format!("{prefix}{suffix}")` will always be
    /// equal to `self`.
    ///
    /// Guarunteed not to allocate a new underlying `FrontString`.
    ///
    /// # Panics
    /// A panic will occur if:
    /// * `start_idx` is greater than `self.len()`, or
    /// * `start_idx` indexes to an invalid `char` boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// # use char_list::CharList;
    /// # use assert2::assert;
    /// let rustonomicon = CharList::from("rustonomicon");
    /// let ptr_before = rustonomicon.backing_string().as_ptr();
    ///
    /// let idx = "rusto".len();
    /// let (rusto, nomicon) = rustonomicon.split_at(idx);
    /// assert!(rusto == "rusto" && nomicon == "nomicon");
    ///
    /// // The underlying buffer has NOT been reallocated!
    /// let ptr_after = nomicon.backing_string().as_ptr();
    /// assert!(ptr_before == ptr_after);
    /// ```
    ///
    /// ```
    /// # use char_list::CharList;
    /// # use assert2::assert;
    /// let word = CharList::from("word");
    /// let (empty, suffix) = word.split_at(0);
    /// assert!(empty.is_empty());
    /// assert!(suffix == word);
    /// ```
    ///
    /// ```should_panic
    /// # use char_list::CharList;
    /// # use assert2::assert;
    /// let word = CharList::from("kitty");
    /// let _ = word.split_at(1000); // Panic!
    /// ```
    ///
    /// ```should_panic
    /// # use char_list::CharList;
    /// # use assert2::assert;
    /// let pride_bytes: Vec<u8> = [
    ///     0xF0, 0x9F, 0x8F, 0xB3, // 1st char: 🏳
    ///     //          ^^^^ We're gonna try to begin the suffix here 😈
    ///     0xEF, 0xB8, 0x8F,       // 2nd char: ◌️
    ///     0xE2, 0x80, 0x8D,       // 3rd char: <Zero Width Joiner>
    ///     0xF0, 0x9F, 0x8C, 0x88, // 4th char: 🌈
    /// ].to_vec();
    ///
    /// let pride = CharList::from_utf8(pride_bytes).expect("bytes are valid utf8");
    /// assert!(pride == "🏳️‍🌈");
    ///
    /// let _ = pride.split_at(2); // Panic!
    /// ```
    #[track_caller]
    pub fn split_at(&self, split_index: usize) -> (&str, CharList) {
        if split_index > self.len().expect("infallible") {
            panic!("given range begins beyond end of the `CharList`");
        }

        if !self.as_str().is_char_boundary(split_index) {
            panic!("given range does not begin on a valid char boundary");
        }

        let prefix = &self.as_str()[..split_index];

        let suffix = Self {
            data: PqRc::clone_with_priority(
                &self.data,
                self.len().expect("infallible") - split_index,
            ),
        };

        (prefix, suffix)
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

impl<Tail: CharListTail> Drop for CharList<Tail> {
    fn drop(&mut self) {
        // SAFETY:
        // Does not mutate the inner value in a way that is visible to any other
        // `PqRc` because: the length of the underlying `FrontString` is
        // truncated to the length of the next longest (if any) `CharList` which
        // shares ownership of the `FrontString`.
        unsafe {
            PqRc::with_inner_lowering_prio(&self.data, |inner| {
                let Some(repr) = inner else {
                    return;
                };
                let Some(next_highest) = PqRc::next_highest_priority(&self.data) else {
                    return;
                };
                repr.front_string.truncate(next_highest);
            })
        }
    }
}

impl<Tail: CharListTail> Clone for CharList<Tail> {
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
        }
    }
}

impl<Tail: CharListTail> From<&str> for CharList<Tail> {
    fn from(s: &str) -> Self {
        Self::from_string_and_tail(String::from(s), Default::default())
    }
}

// TODO: Is there an EFFICIENT way to impl From<String> for FrontString?
// See this issue: https://github.com/eignnx/char-list/issues/1
impl<Tail: CharListTail> From<String> for CharList<Tail> {
    fn from(string: String) -> Self {
        let slice: &str = string.as_ref();
        slice.into()
    }
}

impl<Tail: CharListTail> fmt::Debug for CharList<Tail> {
    #[instrument(skip(self, f))]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut cl = Some(self);
        write!(f, "\"")?;
        while let Some(current) = cl {
            trace!("current.segment_as_str() == {:?}", current.segment_as_str());
            write!(f, "{}", current.segment_as_str())?;
            cl = match current.tail().next_char_list() {
                Ok(next) => next,
                Err(err) => {
                    error!("Can't Debug::fmt(CharList) because of error: {err:?}");
                    return write!(f, "{{{err:?}}}\"");
                }
            };
        }
        write!(f, "\"")
    }
}

impl<Tail: CharListTail> fmt::Display for CharList<Tail> {
    #[instrument(skip(self, f))]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut cl = Some(self);
        write!(f, "{}", self.segment_as_str())?;
        while let Some(tail) = cl {
            write!(f, "{}", tail.segment_as_str())?;
            cl = match self.tail().next_char_list() {
                Ok(next) => next,
                Err(err) => {
                    error!("Can't Display::fmt(CharList) because of error: {err:?}");
                    return write!(f, "{err}");
                }
            };
        }
        Ok(())
    }
}

impl<S, Tail> PartialEq<S> for CharList<Tail>
where
    S: AsRef<str>,
    Tail: CharListTail,
{
    #[instrument(fields(self = ?self, other = other.as_ref()))]
    fn eq(&self, other: &S) -> bool {
        let mut other = other.as_ref();
        let mut cl_opt = Some(self);
        while let Some(cl) = cl_opt {
            let seg_len = cl.segment_len();
            trace!(
                "current_seg(cl) ~= {:?}, other[..seg_len] ~= {:?}",
                cl.segment_as_str(),
                &other[..other.len().min(seg_len)]
            );
            if seg_len > other.len() || cl.segment_as_str() != &other[..seg_len] {
                return false;
            }
            other = &other[seg_len..];
            cl_opt = match cl.tail().next_char_list() {
                Ok(next) => next,
                Err(err) => {
                    error!("Can't PartialOrd::cmp due to error: {err:?}");
                    panic!("Can't PartialOrd::cmp due to error: {err:?}");
                }
            };
        }
        true
    }
}

// impl<Tail> PartialEq<CharList<Tail>> for CharList<Tail>
// where
//     Tail: CharListTail,
// {
//     /// For non-panicking version, use `partial_cmp`.
//     fn eq(&self, other: &CharList<Tail>) -> bool {
//         self.partial_cmp(other).unwrap().is_eq()
//     }
// }

/// In general, a `CharList` does not have reflexive equality.
///
/// # Example
///
/// In Prolog, a partial string looks like this:
///
/// ```prolog
/// -? Partial = [a, b, c | Tail].
/// ```
///
/// If later `Tail` is instantiated, then we have two times at which `Partial`
/// is not ***symbolically*** equal to itself i.e.
///
/// ```prolog
/// ?- [a, b, c | Tail] \== [a, b, c, d, e, f].
/// ```
// impl Eq for CharList<NoTail> {}

// impl<Tail> PartialOrd for CharList<Tail>
// where
//     Tail: CharListTail,
// {
//     #[instrument(skip(self, other))]
//     fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
//         use std::cmp::Ordering::*;

//         let mut it1 = self.chars();
//         let mut it2 = other.chars();

//         loop {
//             return match (it1.next(), it2.next()) {
//                 (None, None) => Some(Equal),

//                 (None, Some(Ok(_))) => Some(Less),
//                 (Some(Ok(_)), None) => Some(Greater),
//                 (Some(Ok(c1)), Some(Ok(c2))) => match c1.cmp(&c2) {
//                     Equal => continue,
//                     ord => Some(ord),
//                 },

//                 // If an error occurred in getting the tail, comparison is not
//                 // possible.
//                 (Some(Err(e)), _) | (_, Some(Err(e))) => {
//                     error!("Can't PartialOrd::cmp due to error: {e:?}");
//                     None
//                 }
//             };
//         }
//     }
// }

impl<S, Tail> PartialOrd<S> for CharList<Tail>
where
    S: AsRef<str>,
    Tail: CharListTail,
{
    fn partial_cmp(&self, other: &S) -> Option<std::cmp::Ordering> {
        let s = self.to_string(); // TODO: don't alloc a String.
        s.as_str().partial_cmp(other.as_ref())
    }
}

impl<Tail> Hash for CharList<Tail>
where
    Tail: CharListTail,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let mut cl_opt = Some(self);
        while let Some(cl) = cl_opt {
            cl.segment_as_str().hash(state);
            cl_opt = match cl.data.tail.next_char_list() {
                Ok(next) => next,
                Err(err) => {
                    error!("Can't PartialOrd::cmp due to error: {err:?}");
                    panic!("Can't PartialOrd::cmp due to error: {err:?}");
                }
            };
        }
    }
}

impl<Tail: CharListTail> Default for CharList<Tail> {
    fn default() -> Self {
        Self::new()
    }
}

impl<Tail: CharListTail> FromIterator<char> for CharList<Tail> {
    /// Given an iterator over the `&str` `"abc"`, the `CharList` `"abc"`
    /// will be created.
    fn from_iter<I: IntoIterator<Item = char>>(iter: I) -> Self {
        let string = String::from_iter(iter);
        Self::from(string)
    }
}

// TODO: Can this be generalized from CharList<NoTail> to CharList<Tail>?
impl Add<CharList<NoTail>> for CharList<NoTail> {
    type Output = CharList<()>;
    fn add(self, rhs: CharList<()>) -> Self::Output {
        rhs.cons_str(self.as_str())
    }
}
