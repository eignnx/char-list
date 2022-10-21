use std::{alloc::Layout, marker::PhantomData, ops::Deref, ptr::NonNull};

use super::pq_rc_cell::PqRcCell;

/// Priority-Queue Reference Counted pointer type.
/// Allows mutable access to the owned value if `self` has the highest priority.
pub struct PqRc<T, Priority: Ord + Copy> {
    prio: Priority,
    ptr: NonNull<PqRcCell<T, Priority>>,
    _t_marker: PhantomData<T>,
    _p_marker: PhantomData<Priority>,
}

impl<T, Priority: Ord + Copy> PqRc<T, Priority> {
    pub fn new(t: T, prio: Priority) -> Self {
        let layout = Layout::new::<PqRcCell<T, Priority>>();
        let ptr = unsafe { std::alloc::alloc(layout) };
        let ptr = ptr as *mut PqRcCell<T, Priority>;

        if ptr.is_null() {
            std::alloc::handle_alloc_error(layout);
        }

        let ptr = unsafe {
            ptr.as_uninit_mut()
                .unwrap_unchecked()
                .write(PqRcCell::new(t, prio))
        };

        let ptr = NonNull::from(ptr);

        Self {
            prio,
            ptr,
            _t_marker: Default::default(),
            _p_marker: Default::default(),
        }
    }

    pub fn priority(&self) -> Priority {
        self.prio
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
    pub unsafe fn try_as_mut(&self) -> Option<&mut T> {
        let cell_ref_mut = unsafe { self.ptr.as_ptr().as_mut().unwrap_unchecked() };
        cell_ref_mut.try_inner_mut(self.prio)
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
        &'a self,
        new_prio_mut: impl Fn(&'a mut T) -> Priority,
        new_prio_ref: impl Fn(&'a T) -> (Priority, T),
    ) -> Self {
        match unsafe { self.try_as_mut() } {
            Some(inner_ref) => {
                let new_prio = new_prio_mut(inner_ref);
                Self {
                    prio: new_prio,
                    ptr: self.ptr,
                    _t_marker: Default::default(),
                    _p_marker: Default::default(),
                }
            }
            None => {
                let (new_prio, new_value) = new_prio_ref(self.deref());
                Self::new(new_value, new_prio)
            }
        }
    }
}

impl<T, Priority: Ord + Copy> Clone for PqRc<T, Priority> {
    fn clone(&self) -> Self {
        let mut new = Self {
            prio: self.prio,
            ptr: self.ptr,
            _t_marker: Default::default(),
            _p_marker: Default::default(),
        };

        let cell = unsafe { new.ptr.as_mut() };
        cell.incr_count(self.prio);

        new
    }
}

impl<T, Priority: Ord + Copy> Drop for PqRc<T, Priority> {
    fn drop(&mut self) {
        let cell = unsafe { self.ptr.as_mut() };
        if cell.has_only_one_ref() {
            unsafe { std::ptr::drop_in_place(cell as *mut _) }
        } else {
            cell.decr_count(self.prio);
        }
    }
}

impl<T, Priority: Ord + Copy> Deref for PqRc<T, Priority> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.cell_ref().deref()
    }
}
