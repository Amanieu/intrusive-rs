intrusive-collections
=====================

[![Build Status](https://travis-ci.org/Amanieu/intrusive-rs.svg?branch=master)](https://travis-ci.org/Amanieu/intrusive-rs) [![Coverage Status](https://coveralls.io/repos/github/Amanieu/intrusive-rs/badge.svg?branch=master)](https://coveralls.io/github/Amanieu/intrusive-rs?branch=master) [![Crates.io](https://img.shields.io/crates/v/intrusive-collections.svg)](https://crates.io/crates/intrusive-collections)

A Rust library for creating intrusive collections. Currently supports singly-linked and doubly-linked lists, as well as red-black trees.

[Documentation](https://amanieu.github.io/intrusive-rs/intrusive_collections/index.html)

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
intrusive-collections = "0.3"
```

and this to your crate root:

```rust
#[macro_use]
extern crate intrusive_collections;
```

This crate has two Cargo features:

- `nightly`: Enables nightly-only features: `const fn` constructors and `NonZero` support for `IntrusiveRef`.
- `box` (enabled by default): Enables `IntrusiveRef::{from_box,into_box}`. This requires `libstd` on stable, but only `liballoc` if the `nightly` feature is enabled. 

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
