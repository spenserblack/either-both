# `either-both`

[![Crates.io Version](https://img.shields.io/crates/v/either-both)](https://crates.io/crates/either-both)

This crate is intended to be similar to [`either`][either-crate],
but also cover the "both" variant.

This crate was inspired by wanting to implement a method similar to
`Iterator::zip` that continues until *both* zipped iterators are exhausted.

A common use case could be replacing the type `(Option<L>, Option<R>)` where
the `(None, None)` variant is impossible.

## Example

```rust
use either_both::prelude::*;

pub struct ZipToEnd<A: Iterator, B: Iterator>(A, B);

impl<A: Iterator, B: Iterator> Iterator for ZipToEnd<A, B> {
    type Item = Either<<A as Iterator>::Item, <B as Iterator>::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        let either = match (self.0.next(), self.1.next()) {
            (Some(a), Some(b)) => Both(a, b),
            (Some(a), None) => Left(a),
            (None, Some(b)) => Right(b),
            (None, None) => return None,
        };
        Some(either)
    }
}
```

[either-crate]: https://crates.io/crates/either
