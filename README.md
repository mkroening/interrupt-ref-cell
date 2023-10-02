# interrupt-ref-cell

[![Crates.io](https://img.shields.io/crates/v/interrupt-ref-cell)](https://crates.io/crates/interrupt-ref-cell)
[![docs.rs](https://img.shields.io/docsrs/interrupt-ref-cell)](https://docs.rs/interrupt-ref-cell)
[![CI](https://github.com/mkroening/interrupt-ref-cell/actions/workflows/ci.yml/badge.svg)](https://github.com/mkroening/interrupt-ref-cell/actions/workflows/ci.yml)

A `RefCell` for sharing data with interrupt handlers or signal handlers on the same thread.

```rust
use interrupt_ref_cell::{InterruptRefCell, LocalKeyExt};
 
thread_local! {
    static X: InterruptRefCell<Vec<i32>> = InterruptRefCell::new(Vec::new());
}
 
fn interrupt_handler() {
    X.with_borrow_mut(|v| v.push(1));
}

X.with_borrow(|v| {
    // Raise an interrupt
    raise_interrupt();
    assert_eq!(*v, vec![]);
});
 
// The interrupt handler runs
 
X.with_borrow(|v| assert_eq!(*v, vec![1]));
```

For API documentation, see the [docs].

[docs]: https://docs.rs/interrupt-ref-cell

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
