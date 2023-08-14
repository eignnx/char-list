use std::{
    alloc::Layout,
    cell::{RefCell, UnsafeCell},
    collections::BTreeMap,
    num::NonZeroUsize,
    ops::Deref,
};

#[cfg(test)]
#[allow(unused)]
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

    pub fn total_new_count() -> usize {
        let tid = thread::current().id();
        *NEW_COUNTS.lock().unwrap().entry(tid).or_default()
    }

    pub fn incr_total_new_count() {
        let tid = thread::current().id();
        let mut guard = NEW_COUNTS.lock().unwrap();
        let count = guard.entry(tid).or_default();
        *count += 1;
    }

    pub fn total_drop_count() -> usize {
        let tid = thread::current().id();
        *DROP_COUNTS.lock().unwrap().entry(tid).or_default()
    }

    pub fn incr_total_drop_count() {
        let tid = thread::current().id();
        let mut guard = DROP_COUNTS.lock().unwrap();
        let count = guard.entry(tid).or_default();
        *count += 1;
    }

    pub fn current_live_allocs() -> usize {
        total_new_count() - total_drop_count()
    }
}

type Count = NonZeroUsize;

pub struct PqRcCell<T: ?Sized, Priority: Ord> {
    priorities: RefCell<BTreeMap<Priority, Count>>,
    value: UnsafeCell<T>,
}

impl<T, Priority: Ord + Copy> PqRcCell<T, Priority> {
    pub const LAYOUT: Layout = Layout::new::<PqRcCell<T, Priority>>();

    /// What does this function ***do***?
    /// - It allocates a new `BTreeMap`
    /// - It inserts a `(usize, NonZeroUsize)` pair into the map.
    /// - Places the `BTreeMap` in a `RefCell`. (no-op?)
    /// - Places `value` in an `UnsafeCell`. (no-op?)
    pub fn new(value: T, prio: Priority) -> Self {
        let mut priorities = BTreeMap::new();
        priorities.insert(prio, NonZeroUsize::new(1).unwrap());

        let priorities = RefCell::new(priorities);
        let value = UnsafeCell::new(value);

        #[cfg(test)]
        new_counts::incr_total_new_count();

        Self { priorities, value }
    }

    pub fn inner<'a>(this: &'a Self) -> &'a T {
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
        unsafe { ptr.as_ref::<'a>().unwrap_unchecked() }
    }

    pub fn max_priority_and_count(this: &Self) -> (Priority, Count) {
        debug_assert!(this.priorities.borrow().len() > 0);
        this.priorities
            .borrow()
            .last_key_value()
            .map(|(p, c)| (*p, *c))
            .expect("priorities cannot be empty if `this` exists")
    }

    /// Returns `true` if `this` has a higher priority than any other `PqRcCell`.
    /// See also [`PqRcCell::highest_priority`].
    pub fn has_uniquely_highest_priority(this: &Self, prio: Priority) -> bool {
        let (max_prio, count) = PqRcCell::max_priority_and_count(this);
        prio == max_prio && count.get() == 1
    }

    /// Returns `true` if `this` has the highest priority. Note: Another `PqRcCell` may *also*
    /// have this highest priority (ex: the longest `CharList` got cloned).
    /// See also [`PqRcCell::uniquely_highest_priority`].
    pub fn has_highest_priority(this: &Self, prio: Priority) -> bool {
        let (max_prio, _) = PqRcCell::max_priority_and_count(this);
        prio == max_prio
    }

    /// Performs a mutating action on the inner `T` value.
    ///
    /// Use this when you will be **raising or keeping the same** the priority
    /// of the referring `PqRc`. This is a less strict than
    /// [`Self::with_inner_lowering_prio`] which requires unique highest
    /// priority.
    ///
    /// # Safety
    ///
    /// * `action` may not mutate `this.value` in any way that is visible to other `PqRc`s.
    pub fn with_inner_raising_prio<'a, F, O>(this: &'a Self, prio: Priority, mut action: F) -> O
    where
        F: FnMut(Option<&'a mut T>) -> O,
    {
        if Self::has_highest_priority(this, prio) {
            // SAFETY:
            // > `action` may not mutate `this.value` in any way that is visible to other `PqRc`s.
            // This is responsibility is placed on the caller of this function.
            unsafe { Self::mutate_inner(this, |inner| action(Some(inner))) }
        } else {
            action(None)
        }
    }

    /// If `this` has the highest priority (and no one else does), then give `action` a mutable
    /// reference to the inner `T` value. Otherwise, pass `None` to the action to let it do
    /// something else.
    ///
    /// # Safety
    ///
    /// * `action` may not mutate `this.value` in any way that is visible to other `PqRc`s.
    pub fn with_inner_lowering_prio<'a, F, O>(this: &'a Self, prio: Priority, mut action: F) -> O
    where
        F: FnMut(Option<&'a mut T>) -> O,
    {
        if Self::has_uniquely_highest_priority(this, prio) {
            // SAFETY:
            // > `action` may not mutate `this.value` in any way that is visible to other `PqRc`s.
            // This is responsibility is placed on the caller of this function.
            unsafe { Self::mutate_inner(this, |inner| action(Some(inner))) }
        } else {
            action(None)
        }
    }

    /// Performs a mutable action on the inner value.
    ///
    /// # Safety
    ///
    /// * `action` may not mutate `this.value` in any way that is visible to other `PqRc`s.
    unsafe fn mutate_inner<'a, F, O>(this: &'a Self, mut action: F) -> O
    where
        F: FnMut(&'a mut T) -> O,
    {
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
        let inner_mut = unsafe { this.value.get().as_mut().unwrap() };

        // Perform the mutating action on the inner value.
        action(inner_mut)
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
        let count = count_res.unwrap_or_else(|| {
            #[cfg(test)]
            maybe_debug::dbg!("priority `{prio:?}` is not in the map!");
            panic!("cannot unwrap value because given priority is not registered.")
        });

        match count.get() {
            0 => unreachable!("NonZeroUSize::get() does not return 0."),
            1 => {
                // Remove it from the tree.
                priorities.remove(&prio);
            }
            n => {
                debug_assert!(n > 1);
                // SAFETY: `n` is greater than 1 because match didn't take either of the
                // first two branches, so `n - 1` is non-zero.
                *count = unsafe { NonZeroUsize::new_unchecked(n - 1) };
            }
        }
    }

    /// Returns the total number of `PqRc`s that refer to this `PqRcCell`.
    pub fn ref_count(this: &Self) -> usize {
        this.priorities
            .borrow()
            .iter()
            .map(|(_, &count)| usize::from(count))
            .sum()
    }

    /// If the priorities' counts were expanded and sorted in descending order, i.e.
    ///
    /// |Priority|
    /// |--------|
    /// |   12   |
    /// |   12   |
    /// |   12   |
    /// |    5   |
    /// |    3   |
    ///
    /// This function returns the second element of that sequence (`12`).
    ///
    /// So it *does not* return the second highest priority (which would be 5 in this
    /// example), it returns the priority that the "second in line" has.
    pub fn next_highest_priority(this: &PqRcCell<T, Priority>) -> Option<Priority> {
        let guard = this.priorities.borrow();
        let mut it = guard.iter().rev();
        let (&highest_prio, &highest_prio_count) = it.next()?;
        if highest_prio_count.get() > 1 {
            return Some(highest_prio);
        }
        let (&snd_highest_prio, _) = it.next()?;
        Some(snd_highest_prio)
    }
}

impl<T, Priority: Ord + Copy> Deref for PqRcCell<T, Priority> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        Self::inner(self)
    }
}
