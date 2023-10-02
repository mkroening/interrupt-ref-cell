use std::thread::LocalKey;

use crate::InterruptRefCell;

pub trait LocalKeyExt<T> {
    /// Acquires a reference to the contained value.
    ///
    /// This will lazily initialize the value if this thread has not referenced
    /// this key yet.
    ///
    /// # Panics
    ///
    /// Panics if the value is currently mutably borrowed.
    ///
    /// Panics if the key currently has its destructor running,
    /// and it **may** panic if the destructor has previously been run for this thread.
    ///
    /// # Example
    ///
    /// ```
    /// use interrupt_ref_cell::{InterruptRefCell, LocalKeyExt};
    ///
    /// thread_local! {
    ///     static X: InterruptRefCell<Vec<i32>> = InterruptRefCell::new(Vec::new());
    /// }
    ///
    /// X.with_borrow(|v| assert!(v.is_empty()));
    /// ```
    fn with_borrow<F, R>(&'static self, f: F) -> R
    where
        F: FnOnce(&T) -> R;

    /// Acquires a mutable reference to the contained value.
    ///
    /// This will lazily initialize the value if this thread has not referenced
    /// this key yet.
    ///
    /// # Panics
    ///
    /// Panics if the value is currently borrowed.
    ///
    /// Panics if the key currently has its destructor running,
    /// and it **may** panic if the destructor has previously been run for this thread.
    ///
    /// # Example
    ///
    /// ```
    /// use interrupt_ref_cell::{InterruptRefCell, LocalKeyExt};
    ///
    /// thread_local! {
    ///     static X: InterruptRefCell<Vec<i32>> = InterruptRefCell::new(Vec::new());
    /// }
    ///
    /// X.with_borrow_mut(|v| v.push(1));
    ///
    /// X.with_borrow(|v| assert_eq!(*v, vec![1]));
    /// ```
    fn with_borrow_mut<F, R>(&'static self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R;

    /// Sets the contained value.
    ///
    /// <div class="warning">This will run the lazy initializer.</div>
    ///
    /// Unlike [`LocalKey<RefCell<T>>::set`], this method *does* run the lazy
    /// initializer of the thread local. The required API to avoid that is not
    /// not public.
    ///
    /// # Panics
    ///
    /// Panics if the value is currently borrowed.
    ///
    /// Panics if the key currently has its destructor running,
    /// and it **may** panic if the destructor has previously been run for this thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::{InterruptRefCell, LocalKeyExt};
    ///
    /// thread_local! {
    ///     static X: InterruptRefCell<Vec<i32>> = InterruptRefCell::new(Vec::new());
    /// }
    ///
    /// // Calling X.with() here would result in a panic.
    ///
    /// X.set(vec![1, 2, 3]); // But X.set() is fine, as it skips the initializer above.
    ///
    /// X.with_borrow(|v| assert_eq!(*v, vec![1, 2, 3]));
    /// ```
    fn set(&'static self, value: T);

    /// Takes the contained value, leaving `Default::default()` in its place.
    ///
    /// This will lazily initialize the value if this thread has not referenced
    /// this key yet.
    ///
    /// # Panics
    ///
    /// Panics if the value is currently borrowed.
    ///
    /// Panics if the key currently has its destructor running,
    /// and it **may** panic if the destructor has previously been run for this thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::{InterruptRefCell, LocalKeyExt};
    ///
    /// thread_local! {
    ///     static X: InterruptRefCell<Vec<i32>> = InterruptRefCell::new(Vec::new());
    /// }
    ///
    /// X.with_borrow_mut(|v| v.push(1));
    ///
    /// let a = X.take();
    ///
    /// assert_eq!(a, vec![1]);
    ///
    /// X.with_borrow(|v| assert!(v.is_empty()));
    /// ```
    fn take(&'static self) -> T
    where
        T: Default;

    /// Replaces the contained value, returning the old value.
    ///
    /// # Panics
    ///
    /// Panics if the value is currently borrowed.
    ///
    /// Panics if the key currently has its destructor running,
    /// and it **may** panic if the destructor has previously been run for this thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use interrupt_ref_cell::{InterruptRefCell, LocalKeyExt};
    ///
    /// thread_local! {
    ///     static X: InterruptRefCell<Vec<i32>> = InterruptRefCell::new(Vec::new());
    /// }
    ///
    /// let prev = X.replace(vec![1, 2, 3]);
    /// assert!(prev.is_empty());
    ///
    /// X.with_borrow(|v| assert_eq!(*v, vec![1, 2, 3]));
    /// ```
    fn replace(&'static self, value: T) -> T;
}

impl<T: 'static> LocalKeyExt<T> for LocalKey<InterruptRefCell<T>> {
    fn with_borrow<F, R>(&'static self, f: F) -> R
    where
        F: FnOnce(&T) -> R,
    {
        self.with(|cell| f(&cell.borrow()))
    }

    fn with_borrow_mut<F, R>(&'static self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        self.with(|cell| f(&mut cell.borrow_mut()))
    }

    fn set(&'static self, value: T) {
        // We'd rather use `RefCell::initialize_with`, which is private.
        self.with(|cell| {
            *cell.borrow_mut() = value;
        });
    }

    fn take(&'static self) -> T
    where
        T: Default,
    {
        self.with(|cell| cell.take())
    }

    fn replace(&'static self, value: T) -> T {
        self.with(|cell| cell.replace(value))
    }
}
