use core::fmt;
use std::{
    alloc::Layout,
    marker::PhantomData,
    num::NonZeroUsize,
    ops::{Add, Deref},
    ptr::NonNull,
};

use super::pq_rc_cell::{self, PqRcCell};

/// Priority-Queue Reference Counted pointer type.
/// Allows mutable access to the owned value if `self` has the highest priority.
pub struct PqRc<T, Priority: Ord + Copy> {
    prio: Priority,
    ptr: NonNull<PqRcCell<T, Priority>>,
    _t_marker: PhantomData<T>,
    _p_marker: PhantomData<Priority>,
}

impl<T, Priority> PqRc<T, Priority>
where
    Priority: Ord + Copy + Add<Output = Priority>,
{
    fn alloc_ptr() -> NonNull<PqRcCell<T, Priority>> {
        let layout = Layout::new::<PqRcCell<T, Priority>>();
        let ptr = unsafe { std::alloc::alloc(layout) };
        let ptr = ptr as *mut PqRcCell<T, Priority>;
        match NonNull::new(ptr) {
            Some(ptr) => ptr,
            None => std::alloc::handle_alloc_error(layout),
        }
    }

    pub fn new(value: T, priority: Priority) -> Self {
        let cell = PqRcCell::new(value, priority);
        // SAFETY: `cell` knows about the `PqRc` that we're about to create since
        // the `new` function registers a new referee.
        unsafe { Self::from_cell_and_prio(cell, priority) }
    }

    pub fn new_from(value: impl Into<T>, priority: Priority) -> Self {
        Self::new(value.into(), priority)
    }

    /// # Safety
    /// * `cell` must account for the `PqRc` that will be created by this function.
    unsafe fn from_cell_and_prio(cell: PqRcCell<T, Priority>, prio: Priority) -> Self {
        let ptr = Self::alloc_ptr();

        unsafe {
            ptr.as_uninit_mut().write(cell);
        }

        Self {
            prio,
            ptr,
            _t_marker: Default::default(),
            _p_marker: Default::default(),
        }
    }

    /// # Safety
    /// * `ptr` must point to an existing `PqRcCell`.
    unsafe fn from_prio_and_ptr(prio: Priority, mut ptr: NonNull<PqRcCell<T, Priority>>) -> Self {
        unsafe {
            // Because `ptr` refers to an existing `PqRcCell` and we're creating
            // a new `PqRc`, we **gotta** increment the count!
            ptr.as_mut().incr_count(prio);
        }

        Self {
            prio,
            ptr,
            _t_marker: Default::default(),
            _p_marker: Default::default(),
        }
    }

    pub fn priority(this: &Self) -> Priority {
        this.prio
    }

    /// Returns true if `this` is the only `PqRc` that has max priority.
    pub fn uniquely_highest_priority(this: &PqRc<T, Priority>) -> bool {
        let cell = Self::cell_ref(this);
        let (&max_prio, &count) = PqRcCell::max_priority_and_count(cell);
        Self::priority(this) == max_prio && count == NonZeroUsize::MIN
    }

    #[allow(dead_code)]
    pub fn ref_count(this: &Self) -> usize {
        PqRcCell::ref_count(this.cell_ref())
    }

    fn cell_ref(&self) -> &PqRcCell<T, Priority> {
        unsafe { self.ptr.as_ref() }
    }

    /// If `self` has the highest priority relative to all other `PqRc`s that
    /// share the inner value, returns a mutable reference to the inner value.
    /// Otherwise returns `None`.
    ///
    /// # Safety
    /// With the returned `&mut`, you **must not** mutate the inner value in a
    /// way that is visible to any other `PqRc`.
    pub unsafe fn try_as_mut(this: &Self) -> Option<&mut T> {
        let cell_ref_mut = unsafe { this.ptr.as_ptr().as_mut().unwrap_unchecked() };
        PqRcCell::try_inner_mut(cell_ref_mut, this.prio)
    }

    /// A new `PqRc` `x` is returned from this function where `x`'s priority is
    /// the priority of `self` **plus** the priority returned by the closure
    /// that gets called.
    ///
    /// # Arguments
    /// * `new_prio_mut` accepts a **mutable** reference to the inner value, and
    /// should return a priority difference.
    /// * `new_prio_ref` accepts an **immutable** reference to the inner value,
    /// and should return a priority difference *AND* a new `T` value.
    ///
    /// # Safety
    /// With the provided `&mut`, you **must not** mutate the inner value in a
    /// way that is visible to any other `PqRc` (except the new one just created).
    pub unsafe fn mutate_or_clone<'a>(
        this: &'a Self,
        new_prio_mut: impl Fn(&'a mut T) -> Priority,
        new_prio_ref: impl Fn(&'a T) -> (Priority, T),
    ) -> Self {
        // SAFETY: `inner_ref` will be mutated according to `new_prio_mut`, whose
        // requirements are listed in this function's safety section, and are the
        // same as those required by `try_as_mut`.
        match unsafe { Self::try_as_mut(this) } {
            Some(inner_ref) => {
                let new_prio = new_prio_mut(inner_ref);
                // SAFETY: `this.ptr` points to a valid `PqRcCell` because `this`
                // is assumed to be valid at start of this function.
                unsafe { Self::from_prio_and_ptr(this.prio + new_prio, this.ptr) }
            }
            None => {
                let (new_prio, new_value) = new_prio_ref(this.deref());
                Self::new(new_value, this.prio + new_prio)
            }
        }
    }

    /// Create a new pointer to the shared inner `T` but with a new priority.
    pub fn clone_with_priority(this: &Self, new_prio: Priority) -> PqRc<T, Priority> {
        let mut new = Self {
            prio: new_prio,
            ptr: this.ptr,
            _t_marker: Default::default(),
            _p_marker: Default::default(),
        };

        let cell = unsafe { new.ptr.as_mut() };
        cell.incr_count(new.prio);

        new
    }

    pub fn second_highest_priority(this: &PqRc<T, Priority>) -> Option<Priority> {
        let cell = this.cell_ref();
        PqRcCell::second_highest_priority(cell)
    }

    pub fn inner(this: &Self) -> &T {
        PqRcCell::inner(this.cell_ref())
    }
}

impl<T, Priority> Clone for PqRc<T, Priority>
where
    Priority: Ord + Copy + Add<Output = Priority>,
{
    fn clone(&self) -> Self {
        PqRc::clone_with_priority(self, self.prio)
    }
}

impl<T, Priority: Ord + Copy> Drop for PqRc<T, Priority> {
    fn drop(&mut self) {
        let cell = unsafe { self.ptr.as_mut() };
        cell.decr_count(self.prio);
        if PqRcCell::ref_count(cell) == 0 {
            #[cfg(test)]
            pq_rc_cell::new_counts::inc_drop_count();
            unsafe { std::ptr::drop_in_place(cell as *mut _) }
        }
    }
}

impl<T, Priority> Deref for PqRc<T, Priority>
where
    Priority: Ord + Copy + Add<Output = Priority>,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.cell_ref().deref()
    }
}

impl<U, T, Priority> PartialEq<U> for PqRc<T, Priority>
where
    Priority: Ord + Copy + Add<Output = Priority>,
    T: PartialEq<U>,
{
    fn eq(&self, other: &U) -> bool {
        self.cell_ref().deref().eq(other)
    }
}

impl<T, Priority> fmt::Debug for PqRc<T, Priority>
where
    Priority: Ord + Copy + Add<Output = Priority>,
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

impl<T, Priority> fmt::Display for PqRc<T, Priority>
where
    Priority: Ord + Copy + Add<Output = Priority>,
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}
