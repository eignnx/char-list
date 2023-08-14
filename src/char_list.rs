use std::{
    borrow::Borrow,
    fmt,
    hash::Hash,
    ops::{Add, AddAssign},
    str::{pattern::Pattern, Utf8Error},
    string::FromUtf8Error,
};

use front_vec::FrontString;

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
/// This type specifically does **not** implement `Deref<Target=str>`. If you
/// need a `&str`, use the [`as_str`](crate::CharList::as_str) method or `as_ref`.
///
/// Essentially, I don't want users to realize they need to call `cons` but
/// only have a `&str`. Then the only way to proceed is to call `CharList::from`
/// and allocate a **new** backing string.
///
/// This restriction may be relaxed in the future (let me know if you have a good
/// argument for allowing this, I'm flexible 🙂).
pub struct CharList<Tail: Clone + Default = ()> {
    data: PqRc<StringRepr<Tail>, Len>,
}

/// Helper struct. Allows users of `CharList` to (optionally) store extra data
/// in the allocated `PqRcCell`.
struct StringRepr<Tail: Clone> {
    front_string: FrontString,
    tail: Tail,
}

impl<Tail: Clone + Default> CharList<Tail> {
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
    pub fn new_with_tail(tail: Tail) -> Self {
        Self::with_capacity_and_tail(0, tail)
    }

    /// Creates a `CharList` whose backing [`FrontString`](front_string::FrontString)
    /// begins with the capacity specified.
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

    /// Extracts a string slice which references `self`'s entire view of the
    /// underlying text.
    ///
    /// Same as [`<CharList as AsRef<str>>::as_ref`](char_list::CharList::as_ref).
    pub fn as_str(&self) -> &str {
        let entire_slice: &str = self.backing_string().as_ref();
        &entire_slice[entire_slice.len() - self.len()..]
    }

    /// Extracts a byte slice which references `self`'s entire view of the
    /// underlying text.
    ///
    /// Same as [`<CharList as AsRef<[u8]>>::as_ref`](char_list::CharList::as_ref).
    pub fn as_bytes(&self) -> &[u8] {
        self.as_str().as_bytes()
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
                PqRc::mutate_or_clone_raising_prio(
                    &self.data,
                    |repr_mut| {
                        repr_mut.front_string.push_str_front(s);
                        s.len()
                    },
                    |_string_ref| {
                        let mut new_string = FrontString::from(self.as_str());
                        new_string.push_str_front(s);
                        let repr = StringRepr {
                            front_string: new_string,
                            tail: self.data.tail.clone(),
                        };
                        (s.len(), repr)
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
    /// ```
    ///
    /// ```
    /// # use char_list::CharList;
    /// # use assert2::assert;
    /// let empty = CharList::new();
    /// assert!(empty.car_cdr() == None);
    /// ```
    #[track_caller]
    pub fn car_cdr(&self) -> Option<(char, Self)> {
        let first_char = self.as_str().chars().next()?;
        let new_len = self.len() - first_char.len_utf8();
        let cdr = Self {
            data: PqRc::clone_with_priority(&self.data, new_len),
        };
        Some((first_char, cdr))
    }

    /// Returns an iterator over the characters in `self`.
    pub fn chars(&self) -> std::str::Chars {
        self.as_str().chars()
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
    #[deprecated(since = "0.1.0", note = "use `CharList::split_prefix_suffix` instead")]
    pub fn without_prefix<'a, P>(&'a self, prefix: P) -> Option<Self>
    where
        P: Pattern<'a>,
    {
        self.as_str().strip_prefix(prefix).map(|sub| Self {
            data: PqRc::clone_with_priority(&self.data, sub.len()),
        })
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
        let remainder = self.as_str().trim_start_matches(prefix);
        self.split_at(self.len() - remainder.len())
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
    pub fn split_at(&self, split_index: usize) -> (&str, CharList<Tail>) {
        if split_index > self.len() {
            panic!("given range begins beyond end of the `CharList`");
        }

        if !self.as_str().is_char_boundary(split_index) {
            panic!("given range does not begin on a valid char boundary");
        }

        let prefix = &self.as_str()[..split_index];

        let suffix = Self {
            data: PqRc::clone_with_priority(&self.data, self.len() - split_index),
        };

        (prefix, suffix)
    }

    /// Get an immutable reference to the backing [`FrontString`](front_vec::FrontString).
    pub fn backing_string(&self) -> &FrontString {
        &PqRc::inner(&self.data).front_string
    }

    pub fn from_string_and_tail(s: impl Into<String>, tail: Tail) -> Self {
        let front_string: FrontString = FrontString::from(s.into());
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

    // TODO: implement this method
    // /// Returns a mutable slice which referencing the portion of the
    // /// `CharList`'s view of the underlying `FrontString` which `self` is
    // /// able to safely mutate. If no such slice exists (i.e. `self` is not
    // /// the longest view into the underlying `FrontString`) this method
    // /// returns an ***empty slice***.
    // pub fn mutable_portion(&mut self) -> &mut str {
    //     let mut_string = unsafe { PqRc::try_as_mut(&self.data)? };
    //     let mut_entire_slice: &mut str = mut_string.as_mut(); // TODO: impl `AsMut` for `FrontString`
    //     let from = todo!();
    //     let till = todo!();
    //     Some(&mut mut_entire_slice[from..till])
    // }
}

impl<Tail: Clone + Default> Drop for CharList<Tail> {
    fn drop(&mut self) {
        // SAFETY:
        // Does not mutate the inner value in a way that is visible to any other
        // `PqRc` because: the length of the underlying `FrontString` is
        // truncated to the length of the next longest (if any) `CharList` which
        // shares ownership of the `FrontString`.
        unsafe {
            PqRc::with_inner_lowering_prio(&self.data, |inner| match inner {
                None => (),
                Some(repr) => {
                    let Some(next_highest) = PqRc::next_highest_priority(&self.data) else {
                        return;
                    };
                    debug_assert!(next_highest <= self.len());
                    repr.front_string.truncate(next_highest);
                }
            })
        }
    }
}

impl<Tail: Clone + Default> Clone for CharList<Tail> {
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
        }
    }
}

impl<Tail: Clone + Default> From<&str> for CharList<Tail> {
    fn from(s: &str) -> Self {
        Self::from_string_and_tail(String::from(s), Default::default())
    }
}

// TODO: Is there an EFFICIENT way to impl From<String> for FrontString?
// See this issue: https://github.com/eignnx/char-list/issues/1
impl<Tail: Clone + Default> From<String> for CharList<Tail> {
    fn from(string: String) -> Self {
        let slice: &str = string.as_ref();
        slice.into()
    }
}

impl<Tail: Clone + Default> fmt::Debug for CharList<Tail> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let slice: &str = self.as_str();
        write!(f, "{slice:?}")
    }
}

impl<Tail: Clone + Default> fmt::Display for CharList<Tail> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let slice: &str = self.as_str();
        write!(f, "{slice}")
    }
}

impl<S, Tail> PartialEq<S> for CharList<Tail>
where
    S: AsRef<str>,
    Tail: Clone + Default + PartialEq, // TODO: Relax `PartialEq` requirement?
{
    fn eq(&self, other: &S) -> bool {
        self.as_str() == other.as_ref()
    }
}

impl<Tail: Clone + Default + Eq> Eq for CharList<Tail> {}

impl<S, Tail> PartialOrd<S> for CharList<Tail>
where
    S: AsRef<str>,
    Tail: Clone + Default + PartialOrd, // TODO: Relax `PartialOrd` requirement?
{
    fn partial_cmp(&self, other: &S) -> Option<std::cmp::Ordering> {
        self.as_str().partial_cmp(other.as_ref())
    }
}

impl<Tail> Ord for CharList<Tail>
where
    Tail: Clone + Default + Ord, // TODO: Relax `Ord` requirement?
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl<Tail> Hash for CharList<Tail>
where
    Tail: Clone + Default + Hash, // TODO: Relax `Hash` requirement?
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl<Tail: Clone + Default> Default for CharList<Tail> {
    fn default() -> Self {
        Self::new()
    }
}

impl<Tail: Clone + Default> FromIterator<char> for CharList<Tail> {
    /// Given an iterator over the `&str` `"abc"`, the `CharList` `"abc"`
    /// will be created.
    fn from_iter<I: IntoIterator<Item = char>>(iter: I) -> Self {
        let string = String::from_iter(iter);
        Self::from(string)
    }
}

// TODO: Can this be generalized from CharList<()> to CharList<Tail>?
impl Add<CharList<()>> for CharList<()> {
    type Output = CharList<()>;
    fn add(self, rhs: CharList<()>) -> Self::Output {
        rhs.cons_str(self.as_str())
    }
}

// TODO: Can this be generalized from CharList<()> to CharList<Tail>?
impl AddAssign<CharList<()>> for String {
    fn add_assign(&mut self, rhs: CharList<()>) {
        self.push_str(rhs.as_str())
    }
}

impl<Tail: Clone + Default> AsRef<str> for CharList<Tail> {
    /// For a more specific version of this method (when types can't be
    /// inferred) see [`CharList::as_str`](char_list::CharList::as_str).
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<Tail: Clone + Default> AsRef<[u8]> for CharList<Tail> {
    /// For a more specific version of this method (when types can't be
    /// inferred) see [`CharList::as_bytes`](char_list::CharList::as_bytes).
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

/// Note: Borrow can be implemented for `CharList` because for all `CharList`s
/// `x` and `y`:
/// 1. `x == y` implies `x.borrow() == y.borrow()`,
/// 2. `x.cmp(y) == x.borrow().cmp(y.borrow())`, and
/// 3. `hash(x) == hash(y)` implies `hash(x.borrow()) == hash(y.borrow())`.
impl<Tail: Clone + Default> Borrow<str> for CharList<Tail> {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

#[cfg(test)]
mod tests;
