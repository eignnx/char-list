use core::fmt;
use std::{
    alloc::Layout,
    marker::PhantomData,
    ops::{Add, Deref, Sub},
    ptr::NonNull,
};

use super::pq_rc_cell::PqRcCell;

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
    Priority: Ord + Copy + Add<Output = Priority> + Sub<Output = Priority>,
{
    fn alloc_ptr() -> NonNull<PqRcCell<T, Priority>> {
        let layout = Layout::new::<PqRcCell<T, Priority>>();
        // SAFETY:
        // > This function is unsafe because undefined behavior can result if
        // > the caller does not ensure that layout has non-zero size.
        // The size of a `PqRcCell` is at least the size of a `BTreeMap`, which
        // is non-zero.
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

    #[allow(unused)]
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

    #[allow(dead_code)]
    pub fn ref_count(this: &Self) -> usize {
        PqRcCell::ref_count(this.cell_ref())
    }

    fn cell_ref(&self) -> &PqRcCell<T, Priority> {
        unsafe { self.ptr.as_ref() }
    }

    /// # Safety
    /// TODO[document safety invariants]
    pub unsafe fn with_inner_raising_prio<'a, F, O>(this: &'a Self, action: F) -> O
    where
        F: FnMut(Option<&'a mut T>) -> O,
    {
        // TODO[safety argument omitted]
        let cell_ref_mut = unsafe { this.ptr.as_ptr().as_mut().unwrap_unchecked() };
        PqRcCell::with_inner_raising_prio(cell_ref_mut, this.prio, action)
    }

    /// SAFETY: TODO[document safety invariants]
    pub unsafe fn with_inner_lowering_prio<'a, F, O>(this: &'a Self, action: F) -> O
    where
        F: FnMut(Option<&'a mut T>) -> O,
    {
        // TODO[safety argument omitted]
        let cell_ref_mut = unsafe { this.ptr.as_ptr().as_mut().unwrap_unchecked() };
        PqRcCell::with_inner_lowering_prio(cell_ref_mut, this.prio, action)
    }

    /// A new `PqRc` `x` is returned from this function where `x`'s priority is
    /// the priority of `self` **plus** the priority returned by the closure
    /// that gets called.
    ///
    /// # Arguments
    /// * `new_prio_mut` accepts a **mutable** reference to the inner value, and
    /// should return a priority difference (increase).
    /// * `new_prio_ref` accepts an **immutable** reference to the inner value,
    /// and should return a priority difference (increase) *AND* a new `T` value.
    ///
    /// # Safety
    /// With the provided `&mut`, you **must not** mutate the inner value in a
    /// way that is visible to any other `PqRc` (except the new one just created).
    pub unsafe fn mutate_or_clone_raising_prio<'a>(
        this: &'a Self,
        new_prio_mut: impl Fn(&'a mut T) -> Priority,
        new_prio_ref: impl Fn(&'a T) -> (Priority, T),
    ) -> Self {
        // SAFETY: TODO
        // OLD ----v
        // `inner_ref` will be mutated according to `new_prio_mut`, whose
        // requirements are listed in this function's safety section, and are the
        // same as those required by `try_as_mut`.
        unsafe {
            Self::with_inner_raising_prio(this, |inner| {
                match inner {
                    Some(inner_ref) => {
                        let new_prio = new_prio_mut(inner_ref);
                        // SAFETY: `this.ptr` points to a valid `PqRcCell` because `this`
                        // is assumed to be valid at start of this function.
                        Self::from_prio_and_ptr(this.prio + new_prio, this.ptr)
                    }
                    None => {
                        let (new_prio, new_value) = new_prio_ref(this.deref());
                        Self::new(new_value, this.prio + new_prio)
                    }
                }
            })
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

        // SAFETY:
        //
        // > The pointer must be properly aligned.
        // `PqRcCell`s are not created with unaligned `ptr` fields, and `ptr` is
        // never shifted so it isn't becoming unaligned ever.
        //
        // > It must be "dereferenceable" in the sense defined in [the module documentation].
        // TODO[safety argument omitted]
        //
        // > The pointer must point to an initialized instance of `T`.
        // `*this` is assumed to contain an initialized instance of a `PqRcCell`.
        //
        // > You must enforce Rust's aliasing rules, since the returned lifetime `'a` is
        // > arbitrarily chosen and does not necessarily reflect the actual lifetime of the data.
        // > In particular, while this reference exists, the memory the pointer points to must
        // > not get accessed (read or written) through any other pointer.
        // We get the `&mut`, call `incr_count` with it, and then immediately release it.
        //
        // > This applies even if the result of this method is unused!
        // > (The part about being initialized is not yet fully decided, but until
        // > it is, the only safe approach is to ensure that they are indeed initialized.)
        // The result *is* used, so this doesn't apply.
        let cell = unsafe { new.ptr.as_mut() };
        cell.incr_count(new.prio);

        new
    }

    pub fn second_highest_priority(this: &PqRc<T, Priority>) -> Option<Priority> {
        PqRcCell::next_highest_priority(this.cell_ref())
    }

    pub fn inner(this: &Self) -> &T {
        PqRcCell::inner(this.cell_ref())
    }
}

impl<T, Priority> Clone for PqRc<T, Priority>
where
    Priority: Ord + Copy + Add<Output = Priority> + Sub<Output = Priority>,
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
            {
                use crate::pq_rc::pq_rc_cell;
                pq_rc_cell::new_counts::incr_total_drop_count();
            }
            // TODO[safety argument omitted]
            unsafe { std::ptr::drop_in_place(cell as *mut _) }
        }
    }
}

impl<T, Priority> Deref for PqRc<T, Priority>
where
    Priority: Ord + Copy + Add<Output = Priority> + Sub<Output = Priority>,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.cell_ref().deref()
    }
}

impl<U, T, Priority> PartialEq<U> for PqRc<T, Priority>
where
    Priority: Ord + Copy + Add<Output = Priority> + Sub<Output = Priority>,
    T: PartialEq<U>,
{
    fn eq(&self, other: &U) -> bool {
        self.cell_ref().deref().eq(other)
    }
}

impl<T, Priority> fmt::Debug for PqRc<T, Priority>
where
    Priority: Ord + Copy + Add<Output = Priority> + Sub<Output = Priority>,
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PqRc::inner(self).fmt(f)
    }
}

impl<T, Priority> fmt::Display for PqRc<T, Priority>
where
    Priority: Ord + Copy + Add<Output = Priority> + Sub<Output = Priority>,
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PqRc::inner(self).fmt(f)
    }
}
