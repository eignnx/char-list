use std::{fmt, hash::Hash};

use tracing::{error, instrument, trace};

use crate::pq_rc::PqRc;

use super::{CharList, CharListTail};

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
