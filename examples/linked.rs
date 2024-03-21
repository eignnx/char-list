use std::{cell::OnceCell, fmt, rc::Rc};

use front_vec::FrontString;
use tracing::{instrument, trace};

use char_list::{CharList, CharListTail};

#[derive(Debug, Default, Clone)]
pub struct LinkedTail(Rc<OnceCell<Option<LinkedCharList>>>);

impl LinkedTail {
    pub fn get(&self) -> Result<&Option<LinkedCharList>, InstantiationError> {
        self.0.get().ok_or(InstantiationError)
    }

    pub fn set(
        &self,
        tail: impl Into<Option<LinkedCharList>>,
    ) -> Result<(), Option<LinkedCharList>> {
        self.0.set(tail.into())
    }
}

#[derive(Default, Clone)]
pub struct LinkedCharList {
    segment: CharList<LinkedTail>,
}

impl fmt::Debug for LinkedCharList {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"")?;
        write!(f, "{}", self.segment_as_str())?;

        let mut walker = self.segment.partial_segments();

        for seg in &mut walker {
            write!(f, "{}", seg.segment_as_str())?;
        }

        match walker.final_err() {
            Some(InstantiationError) => write!(f, "[.. _Tail]\"")?,
            None => write!(f, "\"")?,
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
    pub fn len(&self) -> Result<usize, InstantiationError> {
        let mut len = 0;
        let mut walker = self.segment.partial_segments();
        for seg in &mut walker {
            trace!("accumulated len == {len}");
            len += seg.segment_len();
        }
        if let Some(e) = walker.final_err() {
            return Err(e.clone());
        }
        trace!("accumulated len == {len}");
        Ok(len)
    }

    pub fn is_empty(&self) -> Result<bool, InstantiationError> {
        Ok(self.len()? == 0)
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

#[derive(Debug, Clone, Default, PartialEq)]
pub struct InstantiationError;

impl fmt::Display for InstantiationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Instantiation error: Tail is not sufficiently instantiated"
        )
    }
}

impl CharListTail for LinkedTail {
    type Err = InstantiationError;

    #[track_caller]
    #[instrument(ret)]
    fn len(&self) -> Result<usize, Self::Err> {
        match self.0.get() {
            Some(Some(tail)) => tail.len(),
            _ => Err(InstantiationError),
        }
    }

    fn next_char_list(&self) -> Result<Option<&CharList<Self>>, Self::Err> {
        let Some(ground) = self.0.get() else {
            return Ok(None);
        };
        Ok(ground.as_ref().map(|s| &s.segment))
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
            LinkedTail(OnceCell::from(None).into()),
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
        assert!(s.tail().get().unwrap().is_none());
        assert!(s == "asdf");
    }

    #[test]
    fn simple_open() {
        let s = LinkedCharList::partial_from("123");
        assert!(s.tail().get().is_err()); // Instantiation error.
        s.tail().set(LinkedCharList::from("456")).unwrap();
        assert!(s == "123456");
    }

    #[test]
    fn segment_as_str() {
        let world: LinkedCharList = "world!".into();
        let hello_world = LinkedCharList {
            segment: CharList::from_string_and_tail(
                "Hello, ",
                LinkedTail(Rc::new(OnceCell::from(Some(world.clone())))),
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

        abc.tail().set(def.clone()).unwrap();
        def.tail().set(hij.clone()).unwrap();
        hij.tail().set(klm.clone()).unwrap();
        assert!(abc == "AbcDefHijKlm");
    }
}

fn main() {}
