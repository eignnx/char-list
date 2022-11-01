use std::{
    cell::{RefCell, UnsafeCell},
    collections::BTreeMap,
    num::NonZeroUsize,
    ops::Deref,
};

#[cfg(test)]
use maybe_debug::maybe_debug;

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
        static ref DROP_COUNTS: Mutex<HashMap<ThreadId, usize>> = Default::default();
    }

    pub fn reset_counts() {
        let tid = thread::current().id();
        NEW_COUNTS.lock().unwrap().insert(tid, 0);
        DROP_COUNTS.lock().unwrap().insert(tid, 0);
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

    pub fn drop_count() -> usize {
        let tid = thread::current().id();
        *DROP_COUNTS.lock().unwrap().entry(tid).or_default()
    }

    pub fn inc_drop_count() {
        let tid = thread::current().id();
        let mut guard = DROP_COUNTS.lock().unwrap();
        let count = guard.entry(tid).or_default();
        *count += 1;
    }

    pub fn current_live_allocs() -> usize {
        new_count() - drop_count()
    }
}

type Count = NonZeroUsize;

pub struct PqRcCell<T: ?Sized, Priority: Ord> {
    priorities: RefCell<BTreeMap<Priority, Count>>,
    value: UnsafeCell<T>,
}

impl<T, Priority: Ord + Copy> PqRcCell<T, Priority> {
    pub fn new(value: T, prio: Priority) -> Self {
        let mut priorities = BTreeMap::new();
        priorities.insert(prio, NonZeroUsize::new(1).unwrap());

        let priorities = RefCell::new(priorities);
        let value = UnsafeCell::new(value);

        #[cfg(test)]
        new_counts::inc_new_count();

        Self { priorities, value }
    }

    pub fn inner(this: &Self) -> &T {
        let ptr = this.value.get() as *const T;
        // SAFETY: If we have a shared immutable reference to `this`, it's ok
        // to turn that into a shared immutable reference to `value`.
        // The `unwrap_unchecked` is ok because `this` and `this.value` are
        // assumed to not be null.

        // SAFETY:
        // * The pointer is properly aligned because:
        //   - it comes from an underlying `&T` which was aligned upon
        //     initialization.
        // * It is "dereferenceable" in the sense defined in
        //   [the module documentation](std::ptr) i.e.:
        //   - ". . . the memory range of the given size starting at the pointer
        //     must all be within the bounds of a single allocated object. Note
        //     that in Rust, every (stack-allocated) variable is considered a
        //     separate allocated object." This use is safe because:
        //     + the pointer points to a single object initialized in the
        //       `PqRcCell` constructor.
        // * The pointer points to an initialized instance of T because:
        //   - the pointer points to a object initialized in the
        //     `PqRcCell` constructor.
        // * You must enforce Rust's aliasing rules, since the returned lifetime
        //   `'a` is arbitrarily chosen and does not necessarily reflect the
        //   actual lifetime of the data. In particular, while this reference
        //   exists, the memory the pointer points to must not get mutated
        //   (except inside `UnsafeCell`).
        //   This applies even if the result of this method is unused!
        //     - This is ok because the value **is** inside of an `UnsafeCell`.
        unsafe { ptr.as_ref().unwrap_unchecked() }
    }

    pub fn max_priority_and_count(this: &Self) -> (Priority, Count) {
        debug_assert!(this.priorities.borrow().len() > 0);
        this.priorities
            .borrow()
            .last_key_value()
            .map(|(p, c)| (*p, *c))
            .expect("priorities cannot be empty if `this` exists")
    }

    pub fn max_priority(this: &Self) -> Priority {
        let (max_proi, _) = Self::max_priority_and_count(this);
        max_proi
    }

    pub fn uniquely_highest_priority(this: &Self, prio: Priority) -> bool {
        let (max_prio, count) = PqRcCell::max_priority_and_count(this);
        prio == max_prio && count == NonZeroUsize::MIN
    }

    pub fn try_inner_mut(this: &mut Self, prio: Priority) -> Option<&mut T> {
        Self::uniquely_highest_priority(this, prio).then(|| {
            let value_ptr = this.value.get();
            // SAFETY:
            // * The access is unique (no active references, mutable or not)
            //   because:
            //     - `this` is itself uniquely borrowed via `&mut`.
            // * The pointer is properly aligned because:
            //     - it's a pointer to a field of a properly aligned reference
            //       to a struct.
            // * It is "dereferenceable" in the sense defined in `mod std::ptr`
            //   documentation because:
            //     - TODO[safety argument omitted]
            // * The pointer points to an initialized instance of T because:
            //     - `this` is assumed to have been properly initialized, along
            //       with all its fields.
            // * Rust's aliasing rules are enforced, since the returned lifetime
            //   `'a` is arbitrarily chosen and does not necessarily reflect the
            //   actual lifetime of the data. In particular, while this
            //   reference exists, the memory the pointer points to is not
            //   accessed (read or written) through any other pointer:
            //     - TODO[safety argument omitted]
            unsafe { value_ptr.as_mut().unwrap_unchecked() }
        })
    }

    pub fn incr_count(&self, prio: Priority) {
        self.priorities
            .borrow_mut()
            .entry(prio)
            .and_modify(|count| *count = count.checked_add(1).unwrap())
            .or_insert(NonZeroUsize::MIN);
    }

    pub fn decr_count(&self, prio: Priority) {
        let mut priorities = self.priorities.borrow_mut();
        let count_res = priorities.get_mut(&prio);
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
                priorities.remove(&prio);
            }
            n => {
                // SAFETY: `n` is greater than 1, so `n-1` is non-zero.
                *count = unsafe { NonZeroUsize::new_unchecked(n - 1) };
            }
        }
    }

    pub fn ref_count(this: &Self) -> usize {
        this.priorities
            .borrow()
            .iter()
            .map(|(_, &count)| usize::from(count))
            .sum()
    }

    pub fn second_highest_priority(this: &PqRcCell<T, Priority>) -> Option<Priority> {
        #[cfg(test)]
        {
            print!("{{");
            for x in this.priorities.borrow().iter().rev() {
                print!("{:?}, ", maybe_debug(&x));
            }
            println!("}}");
        }

        let snd_idx = 1;
        this.priorities
            .borrow()
            .iter()
            .nth_back(snd_idx)
            .map(|(&prio, _)| prio)
    }
}

impl<T, Priority: Ord + Copy> Deref for PqRcCell<T, Priority> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        Self::inner(self)
    }
}
