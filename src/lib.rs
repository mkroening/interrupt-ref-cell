//! A [`RefCell`] for sharing data with interrupt handlers or signal handlers on the same thread.
//!
//! [`InterruptRefCell`] is just like [`RefCell`], but disables interrupts during borrows.
//!
//! See [`std::cell`] for a module-level description of cells.
//!
//! # Synchronization
//!
//! This cell synchronizes the current thread _with itself_ via a [`compiler_fence`].
//!
//! A compiler fence is sufficient for sharing a `!Sync` type, such as [`RefCell`], with an interrupt handler on the same thread.
//!
//! [`compiler_fence`]: std::sync::atomic::compiler_fence
//!
//! # Caveats
//!
//! <div class="warning">Interrupts are disabled on a best-effort basis.</div>
//!
//! Holding a reference does not guarantee that interrupts are disabled.
//! Dropping shared references in the wrong order might enable interrupts prematurely.
//! Similarly, you can just enable interrupts manually while holding a reference.
//!
//! # Examples
//!
//! ```
//! use interrupt_ref_cell::{InterruptRefCell, LocalKeyExt};
//!
//! thread_local! {
//!     static X: InterruptRefCell<Vec<i32>> = InterruptRefCell::new(Vec::new());
//! }
//!
//! fn interrupt_handler() {
//!     X.with_borrow_mut(|v| v.push(1));
//! }
//! #
//! # // Setup signal handling for demo
//! #
//! # use nix::libc;
//! # use nix::sys::signal::{self, SigHandler, Signal};
//! #
//! # extern "C" fn handle_sigint(_signal: libc::c_int) {
//! #     interrupt_handler();
//! # }
//! #
//! # let handler = SigHandler::Handler(handle_sigint);
//! # unsafe { signal::signal(Signal::SIGINT, handler) }.unwrap();
//! #
//! # fn raise_interrupt() {
//! #     signal::raise(Signal::SIGINT);
//! # }
//!
//! X.with_borrow(|v| {
//!     // Raise an interrupt
//!     raise_interrupt();
//!     assert_eq!(*v, vec![]);
//! });
//!
//! // The interrupt handler runs
//!
//! X.with_borrow(|v| assert_eq!(*v, vec![1]));
//! ```

#![cfg_attr(target_os = "none", no_std)]

#[cfg(not(target_os = "none"))]
mod local_key;
use core::cell::{BorrowError, BorrowMutError, Ref, RefCell, RefMut};
use core::cmp::Ordering;
use core::ops::{Deref, DerefMut};
use core::{fmt, mem};

#[cfg(not(target_os = "none"))]
pub use local_key::LocalKeyExt;

/// A mutable memory location with dynamically checked borrow rules
///
/// See the [module-level documentation](self) for more.
pub struct InterruptRefCell<T: ?Sized> {
    inner: RefCell<T>,
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for InterruptRefCell<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("InterruptRefCell");
        match self.try_borrow() {
            Ok(borrow) => d.field("value", &borrow),
            Err(_) => d.field("value", &format_args!("<borrowed>")),
        };
        d.finish()
    }
}

impl<T> InterruptRefCell<T> {
    /// Creates a new `InterruptRefCell` containing `value`.
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::InterruptRefCell;
    ///
    /// let c = InterruptRefCell::new(5);
    /// ```
    #[inline]
    pub const fn new(value: T) -> Self {
        Self {
            inner: RefCell::new(value),
        }
    }

    /// Consumes the `InterruptRefCell`, returning the wrapped value.
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::InterruptRefCell;
    ///
    /// let c = InterruptRefCell::new(5);
    ///
    /// let five = c.into_inner();
    /// ```
    #[inline]
    pub fn into_inner(self) -> T {
        self.inner.into_inner()
    }

    /// Replaces the wrapped value with a new one, returning the old value,
    /// without deinitializing either one.
    ///
    /// This function corresponds to [`std::mem::replace`](../mem/fn.replace.html).
    ///
    /// # Panics
    ///
    /// Panics if the value is currently borrowed.
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::InterruptRefCell;
    /// let cell = InterruptRefCell::new(5);
    /// let old_value = cell.replace(6);
    /// assert_eq!(old_value, 5);
    /// assert_eq!(cell, InterruptRefCell::new(6));
    /// ```
    #[inline]
    #[track_caller]
    pub fn replace(&self, t: T) -> T {
        mem::replace(&mut *self.borrow_mut(), t)
    }

    /// Replaces the wrapped value with a new one computed from `f`, returning
    /// the old value, without deinitializing either one.
    ///
    /// # Panics
    ///
    /// Panics if the value is currently borrowed.
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::InterruptRefCell;
    /// let cell = InterruptRefCell::new(5);
    /// let old_value = cell.replace_with(|&mut old| old + 1);
    /// assert_eq!(old_value, 5);
    /// assert_eq!(cell, InterruptRefCell::new(6));
    /// ```
    #[inline]
    #[track_caller]
    pub fn replace_with<F: FnOnce(&mut T) -> T>(&self, f: F) -> T {
        let mut_borrow = &mut *self.borrow_mut();
        let replacement = f(mut_borrow);
        mem::replace(mut_borrow, replacement)
    }

    /// Swaps the wrapped value of `self` with the wrapped value of `other`,
    /// without deinitializing either one.
    ///
    /// This function corresponds to [`std::mem::swap`](../mem/fn.swap.html).
    ///
    /// # Panics
    ///
    /// Panics if the value in either `InterruptRefCell` is currently borrowed, or
    /// if `self` and `other` point to the same `InterruptRefCell`.
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::InterruptRefCell;
    /// let c = InterruptRefCell::new(5);
    /// let d = InterruptRefCell::new(6);
    /// c.swap(&d);
    /// assert_eq!(c, InterruptRefCell::new(6));
    /// assert_eq!(d, InterruptRefCell::new(5));
    /// ```
    #[inline]
    pub fn swap(&self, other: &Self) {
        mem::swap(&mut *self.borrow_mut(), &mut *other.borrow_mut())
    }
}

impl<T: ?Sized> InterruptRefCell<T> {
    /// Immutably borrows the wrapped value.
    ///
    /// The borrow lasts until the returned `InterruptRef` exits scope. Multiple
    /// immutable borrows can be taken out at the same time.
    ///
    /// # Panics
    ///
    /// Panics if the value is currently mutably borrowed. For a non-panicking variant, use
    /// [`try_borrow`](#method.try_borrow).
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::InterruptRefCell;
    ///
    /// let c = InterruptRefCell::new(5);
    ///
    /// let borrowed_five = c.borrow();
    /// let borrowed_five2 = c.borrow();
    /// ```
    ///
    /// An example of panic:
    ///
    /// ```should_panic
    /// use interrupt_ref_cell::InterruptRefCell;
    ///
    /// let c = InterruptRefCell::new(5);
    ///
    /// let m = c.borrow_mut();
    /// let b = c.borrow(); // this causes a panic
    /// ```
    #[inline]
    #[track_caller]
    pub fn borrow(&self) -> InterruptRef<'_, T> {
        self.try_borrow().expect("already mutably borrowed")
    }

    /// Immutably borrows the wrapped value, returning an error if the value is currently mutably
    /// borrowed.
    ///
    /// The borrow lasts until the returned `InterruptRef` exits scope. Multiple immutable borrows can be
    /// taken out at the same time.
    ///
    /// This is the non-panicking variant of [`borrow`](#method.borrow).
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::InterruptRefCell;
    ///
    /// let c = InterruptRefCell::new(5);
    ///
    /// {
    ///     let m = c.borrow_mut();
    ///     assert!(c.try_borrow().is_err());
    /// }
    ///
    /// {
    ///     let m = c.borrow();
    ///     assert!(c.try_borrow().is_ok());
    /// }
    /// ```
    #[inline]
    #[cfg_attr(feature = "debug_interruptrefcell", track_caller)]
    pub fn try_borrow(&self) -> Result<InterruptRef<'_, T>, BorrowError> {
        let _guard = interrupts::disable();
        self.inner
            .try_borrow()
            .map(|inner| InterruptRef { inner, _guard })
    }

    /// Mutably borrows the wrapped value.
    ///
    /// The borrow lasts until the returned `InterruptRefMut` or all `InterruptRefMut`s derived
    /// from it exit scope. The value cannot be borrowed while this borrow is
    /// active.
    ///
    /// # Panics
    ///
    /// Panics if the value is currently borrowed. For a non-panicking variant, use
    /// [`try_borrow_mut`](#method.try_borrow_mut).
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::InterruptRefCell;
    ///
    /// let c = InterruptRefCell::new("hello".to_owned());
    ///
    /// *c.borrow_mut() = "bonjour".to_owned();
    ///
    /// assert_eq!(&*c.borrow(), "bonjour");
    /// ```
    ///
    /// An example of panic:
    ///
    /// ```should_panic
    /// use interrupt_ref_cell::InterruptRefCell;
    ///
    /// let c = InterruptRefCell::new(5);
    /// let m = c.borrow();
    ///
    /// let b = c.borrow_mut(); // this causes a panic
    /// ```
    #[inline]
    #[track_caller]
    pub fn borrow_mut(&self) -> InterruptRefMut<'_, T> {
        self.try_borrow_mut().expect("already borrowed")
    }

    /// Mutably borrows the wrapped value, returning an error if the value is currently borrowed.
    ///
    /// The borrow lasts until the returned `InterruptRefMut` or all `InterruptRefMut`s derived
    /// from it exit scope. The value cannot be borrowed while this borrow is
    /// active.
    ///
    /// This is the non-panicking variant of [`borrow_mut`](#method.borrow_mut).
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::InterruptRefCell;
    ///
    /// let c = InterruptRefCell::new(5);
    ///
    /// {
    ///     let m = c.borrow();
    ///     assert!(c.try_borrow_mut().is_err());
    /// }
    ///
    /// assert!(c.try_borrow_mut().is_ok());
    /// ```
    #[inline]
    #[cfg_attr(feature = "debug_interruptrefcell", track_caller)]
    pub fn try_borrow_mut(&self) -> Result<InterruptRefMut<'_, T>, BorrowMutError> {
        let _guard = interrupts::disable();
        self.inner
            .try_borrow_mut()
            .map(|inner| InterruptRefMut { inner, _guard })
    }

    /// Returns a raw pointer to the underlying data in this cell.
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::InterruptRefCell;
    ///
    /// let c = InterruptRefCell::new(5);
    ///
    /// let ptr = c.as_ptr();
    /// ```
    #[inline]
    pub fn as_ptr(&self) -> *mut T {
        self.inner.as_ptr()
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this method borrows `InterruptRefCell` mutably, it is statically guaranteed
    /// that no borrows to the underlying data exist. The dynamic checks inherent
    /// in [`borrow_mut`] and most other methods of `InterruptRefCell` are therefore
    /// unnecessary.
    ///
    /// This method can only be called if `InterruptRefCell` can be mutably borrowed,
    /// which in general is only the case directly after the `InterruptRefCell` has
    /// been created. In these situations, skipping the aforementioned dynamic
    /// borrowing checks may yield better ergonomics and runtime-performance.
    ///
    /// In most situations where `InterruptRefCell` is used, it can't be borrowed mutably.
    /// Use [`borrow_mut`] to get mutable access to the underlying data then.
    ///
    /// [`borrow_mut`]: InterruptRefCell::borrow_mut()
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::InterruptRefCell;
    ///
    /// let mut c = InterruptRefCell::new(5);
    /// *c.get_mut() += 1;
    ///
    /// assert_eq!(c, InterruptRefCell::new(6));
    /// ```
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        self.inner.get_mut()
    }

    /// Immutably borrows the wrapped value, returning an error if the value is
    /// currently mutably borrowed.
    ///
    /// # Safety
    ///
    /// Unlike `InterruptRefCell::borrow`, this method is unsafe because it does not
    /// return a `InterruptRef`, thus leaving the borrow flag untouched. Mutably
    /// borrowing the `InterruptRefCell` while the reference returned by this method
    /// is alive is undefined behaviour.
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::InterruptRefCell;
    ///
    /// let c = InterruptRefCell::new(5);
    ///
    /// {
    ///     let m = c.borrow_mut();
    ///     assert!(unsafe { c.try_borrow_unguarded() }.is_err());
    /// }
    ///
    /// {
    ///     let m = c.borrow();
    ///     assert!(unsafe { c.try_borrow_unguarded() }.is_ok());
    /// }
    /// ```
    #[inline]
    pub unsafe fn try_borrow_unguarded(&self) -> Result<&T, BorrowError> {
        self.inner.try_borrow_unguarded()
    }
}

impl<T: Default> InterruptRefCell<T> {
    /// Takes the wrapped value, leaving `Default::default()` in its place.
    ///
    /// # Panics
    ///
    /// Panics if the value is currently borrowed.
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::InterruptRefCell;
    ///
    /// let c = InterruptRefCell::new(5);
    /// let five = c.take();
    ///
    /// assert_eq!(five, 5);
    /// assert_eq!(c.into_inner(), 0);
    /// ```
    pub fn take(&self) -> T {
        self.replace(Default::default())
    }
}

impl<T: Clone> Clone for InterruptRefCell<T> {
    /// # Panics
    ///
    /// Panics if the value is currently mutably borrowed.
    #[inline]
    #[track_caller]
    fn clone(&self) -> InterruptRefCell<T> {
        InterruptRefCell::new(self.borrow().clone())
    }

    /// # Panics
    ///
    /// Panics if `other` is currently mutably borrowed.
    #[inline]
    #[track_caller]
    fn clone_from(&mut self, other: &Self) {
        self.get_mut().clone_from(&other.borrow())
    }
}

impl<T: Default> Default for InterruptRefCell<T> {
    /// Creates a `InterruptRefCell<T>`, with the `Default` value for T.
    #[inline]
    fn default() -> InterruptRefCell<T> {
        InterruptRefCell::new(Default::default())
    }
}

impl<T: ?Sized + PartialEq> PartialEq for InterruptRefCell<T> {
    /// # Panics
    ///
    /// Panics if the value in either `InterruptRefCell` is currently mutably borrowed.
    #[inline]
    fn eq(&self, other: &InterruptRefCell<T>) -> bool {
        *self.borrow() == *other.borrow()
    }
}

impl<T: ?Sized + Eq> Eq for InterruptRefCell<T> {}

impl<T: ?Sized + PartialOrd> PartialOrd for InterruptRefCell<T> {
    /// # Panics
    ///
    /// Panics if the value in either `InterruptRefCell` is currently mutably borrowed.
    #[inline]
    fn partial_cmp(&self, other: &InterruptRefCell<T>) -> Option<Ordering> {
        self.borrow().partial_cmp(&*other.borrow())
    }

    /// # Panics
    ///
    /// Panics if the value in either `InterruptRefCell` is currently mutably borrowed.
    #[inline]
    fn lt(&self, other: &InterruptRefCell<T>) -> bool {
        *self.borrow() < *other.borrow()
    }

    /// # Panics
    ///
    /// Panics if the value in either `InterruptRefCell` is currently mutably borrowed.
    #[inline]
    fn le(&self, other: &InterruptRefCell<T>) -> bool {
        *self.borrow() <= *other.borrow()
    }

    /// # Panics
    ///
    /// Panics if the value in either `InterruptRefCell` is currently mutably borrowed.
    #[inline]
    fn gt(&self, other: &InterruptRefCell<T>) -> bool {
        *self.borrow() > *other.borrow()
    }

    /// # Panics
    ///
    /// Panics if the value in either `InterruptRefCell` is currently mutably borrowed.
    #[inline]
    fn ge(&self, other: &InterruptRefCell<T>) -> bool {
        *self.borrow() >= *other.borrow()
    }
}

impl<T: ?Sized + Ord> Ord for InterruptRefCell<T> {
    /// # Panics
    ///
    /// Panics if the value in either `InterruptRefCell` is currently mutably borrowed.
    #[inline]
    fn cmp(&self, other: &InterruptRefCell<T>) -> Ordering {
        self.borrow().cmp(&*other.borrow())
    }
}

impl<T> From<T> for InterruptRefCell<T> {
    /// Creates a new `InterruptRefCell<T>` containing the given value.
    fn from(t: T) -> InterruptRefCell<T> {
        InterruptRefCell::new(t)
    }
}

/// Wraps a borrowed reference to a value in a `InterruptRefCell` box.
/// A wrapper type for an immutably borrowed value from a `InterruptRefCell<T>`.
///
/// See the [module-level documentation](self) for more.
pub struct InterruptRef<'b, T: ?Sized + 'b> {
    inner: Ref<'b, T>,
    _guard: interrupts::Guard,
}

impl<T: ?Sized> Deref for InterruptRef<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.inner.deref()
    }
}

impl<'b, T: ?Sized> InterruptRef<'b, T> {
    /// Copies a `InterruptRef`.
    ///
    /// The `InterruptRefCell` is already immutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `InterruptRef::clone(...)`. A `Clone` implementation or a method would interfere
    /// with the widespread use of `r.borrow().clone()` to clone the contents of
    /// a `InterruptRefCell`.
    #[allow(clippy::should_implement_trait)]
    #[must_use]
    #[inline]
    pub fn clone(orig: &InterruptRef<'b, T>) -> InterruptRef<'b, T> {
        InterruptRef {
            inner: Ref::clone(&orig.inner),
            _guard: interrupts::disable(),
        }
    }

    /// Makes a new `InterruptRef` for a component of the borrowed data.
    ///
    /// The `InterruptRefCell` is already immutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as `InterruptRef::map(...)`.
    /// A method would interfere with methods of the same name on the contents
    /// of a `InterruptRefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::{InterruptRefCell, InterruptRef};
    ///
    /// let c = InterruptRefCell::new((5, 'b'));
    /// let b1: InterruptRef<'_, (u32, char)> = c.borrow();
    /// let b2: InterruptRef<'_, u32> = InterruptRef::map(b1, |t| &t.0);
    /// assert_eq!(*b2, 5)
    /// ```
    #[inline]
    pub fn map<U: ?Sized, F>(orig: InterruptRef<'b, T>, f: F) -> InterruptRef<'b, U>
    where
        F: FnOnce(&T) -> &U,
    {
        let InterruptRef { inner, _guard } = orig;
        InterruptRef {
            inner: Ref::map(inner, f),
            _guard,
        }
    }

    /// Makes a new `InterruptRef` for an optional component of the borrowed data. The
    /// original guard is returned as an `Err(..)` if the closure returns
    /// `None`.
    ///
    /// The `InterruptRefCell` is already immutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `InterruptRef::filter_map(...)`. A method would interfere with methods of the same
    /// name on the contents of a `InterruptRefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::{InterruptRefCell, InterruptRef};
    ///
    /// let c = InterruptRefCell::new(vec![1, 2, 3]);
    /// let b1: InterruptRef<'_, Vec<u32>> = c.borrow();
    /// let b2: Result<InterruptRef<'_, u32>, _> = InterruptRef::filter_map(b1, |v| v.get(1));
    /// assert_eq!(*b2.unwrap(), 2);
    /// ```
    #[allow(clippy::result_large_err)]
    #[inline]
    pub fn filter_map<U: ?Sized, F>(
        orig: InterruptRef<'b, T>,
        f: F,
    ) -> Result<InterruptRef<'b, U>, Self>
    where
        F: FnOnce(&T) -> Option<&U>,
    {
        let InterruptRef { inner, _guard } = orig;
        match Ref::filter_map(inner, f) {
            Ok(inner) => Ok(InterruptRef { inner, _guard }),
            Err(inner) => Err(InterruptRef { inner, _guard }),
        }
    }

    /// Splits a `InterruptRef` into multiple `InterruptRef`s for different components of the
    /// borrowed data.
    ///
    /// The `InterruptRefCell` is already immutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `InterruptRef::map_split(...)`. A method would interfere with methods of the same
    /// name on the contents of a `InterruptRefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::{InterruptRefCell, InterruptRef};
    ///
    /// let cell = InterruptRefCell::new([1, 2, 3, 4]);
    /// let borrow = cell.borrow();
    /// let (begin, end) = InterruptRef::map_split(borrow, |slice| slice.split_at(2));
    /// assert_eq!(*begin, [1, 2]);
    /// assert_eq!(*end, [3, 4]);
    /// ```
    #[inline]
    pub fn map_split<U: ?Sized, V: ?Sized, F>(
        orig: InterruptRef<'b, T>,
        f: F,
    ) -> (InterruptRef<'b, U>, InterruptRef<'b, V>)
    where
        F: FnOnce(&T) -> (&U, &V),
    {
        let (a, b) = Ref::map_split(orig.inner, f);
        (
            InterruptRef {
                inner: a,
                _guard: orig._guard,
            },
            InterruptRef {
                inner: b,
                _guard: interrupts::disable(),
            },
        )
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for InterruptRef<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for InterruptRef<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<'b, T: ?Sized> InterruptRefMut<'b, T> {
    /// Makes a new `InterruptRefMut` for a component of the borrowed data, e.g., an enum
    /// variant.
    ///
    /// The `InterruptRefCell` is already mutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `InterruptRefMut::map(...)`. A method would interfere with methods of the same
    /// name on the contents of a `InterruptRefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::{InterruptRefCell, InterruptRefMut};
    ///
    /// let c = InterruptRefCell::new((5, 'b'));
    /// {
    ///     let b1: InterruptRefMut<'_, (u32, char)> = c.borrow_mut();
    ///     let mut b2: InterruptRefMut<'_, u32> = InterruptRefMut::map(b1, |t| &mut t.0);
    ///     assert_eq!(*b2, 5);
    ///     *b2 = 42;
    /// }
    /// assert_eq!(*c.borrow(), (42, 'b'));
    /// ```
    #[inline]
    pub fn map<U: ?Sized, F>(orig: InterruptRefMut<'b, T>, f: F) -> InterruptRefMut<'b, U>
    where
        F: FnOnce(&mut T) -> &mut U,
    {
        let InterruptRefMut { inner, _guard } = orig;
        InterruptRefMut {
            inner: RefMut::map(inner, f),
            _guard,
        }
    }

    /// Makes a new `InterruptRefMut` for an optional component of the borrowed data. The
    /// original guard is returned as an `Err(..)` if the closure returns
    /// `None`.
    ///
    /// The `InterruptRefCell` is already mutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `InterruptRefMut::filter_map(...)`. A method would interfere with methods of the
    /// same name on the contents of a `InterruptRefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::{InterruptRefCell, InterruptRefMut};
    ///
    /// let c = InterruptRefCell::new(vec![1, 2, 3]);
    ///
    /// {
    ///     let b1: InterruptRefMut<'_, Vec<u32>> = c.borrow_mut();
    ///     let mut b2: Result<InterruptRefMut<'_, u32>, _> = InterruptRefMut::filter_map(b1, |v| v.get_mut(1));
    ///
    ///     if let Ok(mut b2) = b2 {
    ///         *b2 += 2;
    ///     }
    /// }
    ///
    /// assert_eq!(*c.borrow(), vec![1, 4, 3]);
    /// ```
    #[allow(clippy::result_large_err)]
    #[inline]
    pub fn filter_map<U: ?Sized, F>(
        orig: InterruptRefMut<'b, T>,
        f: F,
    ) -> Result<InterruptRefMut<'b, U>, Self>
    where
        F: FnOnce(&mut T) -> Option<&mut U>,
    {
        let InterruptRefMut { inner, _guard } = orig;
        match RefMut::filter_map(inner, f) {
            Ok(inner) => Ok(InterruptRefMut { inner, _guard }),
            Err(inner) => Err(InterruptRefMut { inner, _guard }),
        }
    }

    /// Splits a `InterruptRefMut` into multiple `InterruptRefMut`s for different components of the
    /// borrowed data.
    ///
    /// The underlying `InterruptRefCell` will remain mutably borrowed until both
    /// returned `InterruptRefMut`s go out of scope.
    ///
    /// The `InterruptRefCell` is already mutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `InterruptRefMut::map_split(...)`. A method would interfere with methods of the
    /// same name on the contents of a `InterruptRefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::{InterruptRefCell, InterruptRefMut};
    ///
    /// let cell = InterruptRefCell::new([1, 2, 3, 4]);
    /// let borrow = cell.borrow_mut();
    /// let (mut begin, mut end) = InterruptRefMut::map_split(borrow, |slice| slice.split_at_mut(2));
    /// assert_eq!(*begin, [1, 2]);
    /// assert_eq!(*end, [3, 4]);
    /// begin.copy_from_slice(&[4, 3]);
    /// end.copy_from_slice(&[2, 1]);
    /// ```
    #[inline]
    pub fn map_split<U: ?Sized, V: ?Sized, F>(
        orig: InterruptRefMut<'b, T>,
        f: F,
    ) -> (InterruptRefMut<'b, U>, InterruptRefMut<'b, V>)
    where
        F: FnOnce(&mut T) -> (&mut U, &mut V),
    {
        let (a, b) = RefMut::map_split(orig.inner, f);
        (
            InterruptRefMut {
                inner: a,
                _guard: orig._guard,
            },
            InterruptRefMut {
                inner: b,
                _guard: interrupts::disable(),
            },
        )
    }
}

/// A wrapper type for a mutably borrowed value from a `InterruptRefCell<T>`.
///
/// See the [module-level documentation](self) for more.
pub struct InterruptRefMut<'b, T: ?Sized + 'b> {
    inner: RefMut<'b, T>,
    _guard: interrupts::Guard,
}

impl<T: ?Sized> Deref for InterruptRefMut<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.inner.deref()
    }
}

impl<T: ?Sized> DerefMut for InterruptRefMut<'_, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner.deref_mut()
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for InterruptRefMut<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for InterruptRefMut<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}
