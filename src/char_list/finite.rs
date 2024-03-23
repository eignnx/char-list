use std::{convert::Infallible, ops::Add, str::pattern::Pattern};

use crate::pq_rc::PqRc;

use super::{CharList, CharListTail};

pub type NoTail = ();

/// The full [`CharList`] type takes a type parameter which represents the tail
/// of the list. For a `FiniteCharList`, the tail is [`NoTail`] -- an alias to
/// `()`.
///
/// See documentation on [`CharList`] for explanation of why you might want a
/// non-finite version of this type.
pub type FiniteCharList = CharList<NoTail>;

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
    /// # use char_list::FiniteCharList;
    /// # use assert2::assert;
    /// let creepy_book = FiniteCharList::from("necronomicon");
    /// let pair = creepy_book.split_after_prefix("necro");
    /// assert!(pair == ("necro", FiniteCharList::from("nomicon")));
    /// ```
    ///
    /// ```
    /// # use char_list::FiniteCharList;
    /// # use assert2::assert;
    /// let words = FiniteCharList::from("hello world");
    /// let (hello, rest) = words.split_after_prefix(char::is_alphabetic);
    /// assert!(hello == "hello");
    /// assert!(rest == " world");
    /// ```
    ///
    /// ```
    /// # use char_list::FiniteCharList;
    /// # use assert2::assert;
    /// let numbers = FiniteCharList::from("1253 39271 4542");
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
    /// # use char_list::FiniteCharList;
    /// # use assert2::assert;
    /// let rustonomicon = FiniteCharList::from("rustonomicon");
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
    /// # use char_list::FiniteCharList;
    /// # use assert2::assert;
    /// let word = FiniteCharList::from("word");
    /// let (empty, suffix) = word.split_at(0);
    /// assert!(empty.is_empty());
    /// assert!(suffix == word);
    /// ```
    ///
    /// ```should_panic
    /// # use char_list::FiniteCharList;
    /// # use assert2::assert;
    /// let word = FiniteCharList::from("kitty");
    /// let _ = word.split_at(1000); // Panic!
    /// ```
    ///
    /// ```should_panic
    /// # use char_list::FiniteCharList;
    /// # use assert2::assert;
    /// let pride_bytes: Vec<u8> = [
    ///     0xF0, 0x9F, 0x8F, 0xB3, // 1st char: 🏳
    ///     //          ^^^^ We're gonna try to begin the suffix here 😈
    ///     0xEF, 0xB8, 0x8F,       // 2nd char: ◌️
    ///     0xE2, 0x80, 0x8D,       // 3rd char: <Zero Width Joiner>
    ///     0xF0, 0x9F, 0x8C, 0x88, // 4th char: 🌈
    /// ].to_vec();
    ///
    /// let pride = FiniteCharList::from_utf8(pride_bytes).expect("bytes are valid utf8");
    /// assert!(pride == "🏳️‍🌈");
    ///
    /// let _ = pride.split_at(2); // Panic!
    /// ```
    #[track_caller]
    pub fn split_at(&self, split_index: usize) -> (&str, Self) {
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

// TODO: Can this be generalized from CharList<NoTail> to CharList<Tail>?
impl Add<CharList<NoTail>> for CharList<NoTail> {
    type Output = CharList<NoTail>;
    fn add(self, rhs: CharList<()>) -> Self::Output {
        rhs.cons_str(self.as_str())
    }
}

impl PartialEq for FiniteCharList {
    fn eq(&self, other: &Self) -> bool {
        self.as_str() == other.as_str()
    }
}

impl Eq for FiniteCharList {}
