use core::mem::ManuallyDrop;
use core::ops::{Deref, DerefMut};

/// A wrapper for dropping values while interrupts are disabled.
pub struct InterruptDropper<T> {
    inner: ManuallyDrop<T>,
}

impl<T> From<T> for InterruptDropper<T> {
    #[inline]
    fn from(value: T) -> Self {
        Self {
            inner: ManuallyDrop::new(value),
        }
    }
}

impl<T> InterruptDropper<T> {
    #[inline]
    pub fn into_inner(mut this: Self) -> T {
        // SAFETY: We never use `this` after this again.
        unsafe { ManuallyDrop::take(&mut this.inner) }
    }
}

impl<T> Deref for InterruptDropper<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.inner.deref()
    }
}

impl<T> DerefMut for InterruptDropper<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner.deref_mut()
    }
}

impl<T> Drop for InterruptDropper<T> {
    #[inline]
    fn drop(&mut self) {
        let guard = interrupts::disable();
        // Drop `inner` as while we can guarentee interrupts are disabled
        // SAFETY: This is not exposed to safe code and is not called more than once
        unsafe { ManuallyDrop::drop(&mut self.inner) }
        drop(guard);
    }
}
