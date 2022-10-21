use std::{collections::BTreeMap, num::NonZeroUsize, ops::Deref};

type Count = NonZeroUsize;

pub struct PqRcCell<T: ?Sized, Priority: Ord> {
    priorities: BTreeMap<Priority, Count>,
    value: T,
}

impl<T, Priority: Ord + Copy> PqRcCell<T, Priority> {
    pub fn new(value: T, prio: Priority) -> Self {
        let mut priorities = BTreeMap::new();
        priorities.insert(prio, NonZeroUsize::new(1).unwrap());
        Self { priorities, value }
    }

    pub fn has_only_one_ref(&self) -> bool {
        self.priorities.len() == 1 && {
            let (_, &count) = self.priorities.last_key_value().unwrap();
            let count: usize = count.into();
            count == 1
        }
    }

    pub fn get_max_priority_count(&self) -> (&Priority, &Count) {
        self.priorities.last_key_value().unwrap()
    }

    pub fn try_inner_mut(&mut self, prio: Priority) -> Option<&mut T> {
        let (&max_prio, _) = self.get_max_priority_count();
        (prio == max_prio).then(|| &mut self.value)
    }

    pub fn incr_count(&mut self, prio: Priority) {
        self.priorities
            .entry(prio)
            .and_modify(|count| *count = count.checked_add(1).unwrap())
            .or_insert(NonZeroUsize::MIN);
    }

    pub fn decr_count(&mut self, prio: Priority) {
        let count = self
            .priorities
            .get_mut(&prio)
            .expect("priority needs to be in the map");

        match usize::from(*count) {
            0 => unreachable!(),
            1 => {
                // Remove it from the tree.
                self.priorities.remove(&prio);
            }
            n => {
                // SAFETY: `n` is greater than 1, so `n-1` is non-zero.
                *count = unsafe { NonZeroUsize::new_unchecked(n - 1) };
            }
        }
    }
}

impl<T, Priority: Ord + Copy> Deref for PqRcCell<T, Priority> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}
