use std::{cell::OnceCell, fmt, rc::Rc};

use front_vec::FrontString;
use tracing::{instrument, trace};

use crate::{bytes::Bytes, char_list::CharList, CharListTail};

type LinkedTail = Rc<OnceCell<Option<LinkedCharList>>>;

#[derive(Default, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LinkedCharList {
    segment: CharList<LinkedTail>,
}

impl fmt::Debug for LinkedCharList {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"")?;
        write!(f, "{}", self.segment_as_str())?;
        let mut seg = self.segment.clone();
        for _ in 0..10 {
            match seg.tail().get() {
                Some(Some(tail)) => {
                    write!(f, "{}", tail.segment_as_str())?;
                    seg = tail.segment.clone();
                }
                None => write!(f, "[.. _Tail]\"")?,
                Some(None) => {
                    write!(f, "\"")?;
                    break;
                }
            }
        }
        Ok(())
    }
}

impl LinkedCharList {
    pub fn partial_from(s: impl Into<String>) -> Self {
        let segment = CharList::from(s.into());
        Self { segment }
    }

    #[instrument(skip(self), ret)]
    pub fn len(&self) -> Option<usize> {
        let mut segment = Some(self.segment.clone());
        let mut len = 0;
        while let Some(seg) = segment {
            trace!("accumulated len == {len}");
            len += seg.segment_len();
            segment = match seg.tail().get() {
                Some(next) => next.clone().map(|lcl| lcl.segment),
                None => return None,
            };
        }
        trace!("accumulated len == {len}");
        Some(len)
    }

    pub fn chars(&self) -> impl Iterator<Item = char> + '_ {
        self.segment.chars()
    }

    pub fn bytes(&self) -> Bytes<LinkedTail> {
        self.segment.bytes()
    }

    pub fn tail(&self) -> &LinkedTail {
        self.segment.tail()
    }

    pub fn cons_char_list(&self, prefix: &LinkedCharList) -> LinkedCharList {
        Self {
            segment: self.segment.cons_char_list(&prefix.segment),
        }
    }

    pub fn segment_len(&self) -> usize {
        self.segment.segment_len()
    }

    pub fn segment_as_str(&self) -> &str {
        self.segment.segment_as_str()
    }

    pub fn segment_as_bytes(&self) -> &[u8] {
        self.segment.segment_as_bytes()
    }

    pub fn backing_string(&self) -> &FrontString {
        self.segment.backing_string()
    }
}

impl CharListTail for LinkedTail {
    #[track_caller]
    #[instrument(ret)]
    fn len(&self) -> usize {
        match self.get() {
            Some(Some(tail)) => tail.len().unwrap(),
            _ => panic!("No correct length for LinkedCharList with uninstantiated tail"),
        }
    }

    fn chars(&self) -> Box<dyn Iterator<Item = char> + '_> {
        match self.get() {
            Some(Some(tail)) => Box::new(tail.chars()),
            Some(None) => Box::new(std::iter::empty()),
            None => Box::new(std::iter::once_with(|| {
                panic!("Cannot get chars from an uninstantiated tail")
            })),
        }
    }

    fn bytes(&self) -> Box<dyn ExactSizeIterator<Item = u8> + '_> {
        match self.get() {
            Some(Some(tail)) => Box::new(tail.bytes()),
            Some(None) => Box::new(std::iter::empty()),
            None => Box::new(std::iter::once_with(|| {
                panic!("Cannot get bytes from an uninstantiated tail")
            })),
        }
    }

    fn next_char_list(&self) -> Option<CharList<Self>> {
        self.get()?.clone().map(|s| s.segment)
    }
}

impl From<CharList<LinkedTail>> for LinkedCharList {
    fn from(segment: CharList<LinkedTail>) -> Self {
        Self { segment }
    }
}

impl From<&str> for LinkedCharList {
    /// Returns a "closed" or "non-partial" `LinkedCharList`. It's tail is nil.
    fn from(s: &str) -> Self {
        Self::from(CharList::from_string_and_tail(
            s,
            OnceCell::from(None).into(),
        ))
    }
}

impl<S: AsRef<str>> PartialEq<S> for LinkedCharList {
    #[instrument(ret, fields(self = ?self, other = ?other.as_ref()))]
    fn eq(&self, other: &S) -> bool {
        self.segment == other.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert2::assert;

    #[test]
    fn simple_closed() {
        let s = LinkedCharList::from("asdf");
        assert!(s.tail().get() == Some(&None));
        assert!(s == "asdf");
    }

    #[test]
    fn simple_open() {
        let s = LinkedCharList::partial_from("123");
        assert!(s.tail().get() == None);
        s.tail().set(Some(LinkedCharList::from("456"))).unwrap();
        assert!(s == "123456");
    }

    #[test]
    fn segment_as_str() {
        let world: LinkedCharList = "world!".into();
        let hello_world = LinkedCharList {
            segment: CharList::from_string_and_tail(
                "Hello, ",
                Rc::new(OnceCell::from(Some(world.clone()))),
            ),
        };
        assert!(hello_world == "Hello, world!");
        assert!(hello_world.segment_len() == "Hello, ".len());
        assert!(hello_world.backing_string().clone() == "Hello, ");
        assert!(
            hello_world
                .tail()
                .next_char_list()
                .unwrap()
                .backing_string()
                .clone()
                == "world!"
        );
        assert!(hello_world.len().unwrap() == "Hello, world!".len());
        assert!(hello_world.segment_as_str() == "Hello, ");
    }

    #[test]
    fn linked_open() {
        let abc = LinkedCharList::partial_from("Abc");
        let def = LinkedCharList::partial_from("Def");
        let hij = LinkedCharList::partial_from("Hij");
        let klm = LinkedCharList::from("Klm");

        abc.tail().set(Some(def.clone())).unwrap();
        def.tail().set(Some(hij.clone())).unwrap();
        hij.tail().set(Some(klm.clone())).unwrap();
        assert!(abc == "AbcDefHijKlm");
    }
}
