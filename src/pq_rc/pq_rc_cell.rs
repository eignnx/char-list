use std::{collections::BTreeMap, num::NonZeroUsize, ops::Deref};

#[cfg(test)]
pub mod new_counts {
    use std::{
        collections::HashMap,
        sync::Mutex,
        thread::{self, ThreadId},
    };

    lazy_static::lazy_static! {
        /// Counts calls to `PqRcCell::new` for testing purposes.
        static ref NEW_COUNTS: Mutex<HashMap<ThreadId, usize>> = Default::default();
    }

    pub fn reset_new_count() {
        let tid = thread::current().id();
        NEW_COUNTS.lock().unwrap().insert(tid, 0);
    }

    pub fn new_count() -> usize {
        let tid = thread::current().id();
        *NEW_COUNTS.lock().unwrap().entry(tid).or_default()
    }

    pub fn inc_new_count() {
        let tid = thread::current().id();
        let mut guard = NEW_COUNTS.lock().unwrap();
        let count = guard.entry(tid).or_default();
        *count += 1;
    }
}

type Count = NonZeroUsize;

pub struct PqRcCell<T: ?Sized, Priority: Ord> {
    priorities: BTreeMap<Priority, Count>,
    value: T,
}

impl<T, Priority: Ord + Copy> PqRcCell<T, Priority> {
    pub fn new(value: T, prio: Priority) -> Self {
        let mut priorities = BTreeMap::new();
        priorities.insert(prio, NonZeroUsize::new(1).unwrap());

        #[cfg(test)]
        new_counts::inc_new_count();

        Self { priorities, value }
    }

    pub fn max_priority_and_count(this: &Self) -> (&Priority, &Count) {
        this.priorities
            .last_key_value()
            .expect("priorities cannot be empty if `this` exists")
    }

    pub fn max_priority(this: &Self) -> Priority {
        let (&max_proi, _) = Self::max_priority_and_count(this);
        max_proi
    }

    pub fn try_inner_mut(this: &mut Self, prio: Priority) -> Option<&mut T> {
        (prio == Self::max_priority(this)).then(|| &mut this.value)
    }

    pub fn incr_count(&mut self, prio: Priority) {
        self.priorities
            .entry(prio)
            .and_modify(|count| *count = count.checked_add(1).unwrap())
            .or_insert(NonZeroUsize::MIN);
    }

    pub fn decr_count(&mut self, prio: Priority) {
        let count_res = self.priorities.get_mut(&prio);
        let count = if cfg!(test) {
            count_res.unwrap_or_else(|| {
                #[cfg(test)]
                maybe_debug::dbg!("priority `{prio:?}` is not in the map!");
                panic!("cannot unwrap value because given priority is not registered.")
            })
        } else {
            count_res.unwrap()
        };

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

    pub fn ref_count(this: &Self) -> usize {
        this.priorities
            .iter()
            .map(|(_, &count)| usize::from(count))
            .sum()
    }

    pub fn second_highest_priority(this: &PqRcCell<T, Priority>) -> Option<Priority> {
        let snd_idx = 1;
        this.priorities
            .iter()
            .nth_back(snd_idx)
            .map(|(&prio, _)| prio)
    }

    pub fn inner(this: &Self) -> &T {
        &this.value
    }
}

impl<T, Priority: Ord + Copy> Deref for PqRcCell<T, Priority> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}
