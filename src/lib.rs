//! This crate is intended to be similar to [`either`][either-crate],
//! but also cover the "both" variant.
//!
//! This crate was inspired by wanting to implement a method similar to
//! [`Iterator::zip`] that continues until *both* zipped iterators are exhausted.
//!
//! # Usage
//!
//! It's recommended to use the prelude, which brings into scope `Either<L, R>`, and
//! also its variants:
//!
//! * `Left`
//! * `Right`
//! * `Both`
//!
//! ```rust
//! use either_both::prelude::*;
//!
//! // Just like how Option's and Result's variants are often used without the prefix,
//! // you can now use Left, Right, and Both without prefixing with "Either::"
//! const CHOICES: [Either<bool, u8>;3] = [Left(true), Right(1), Both(false, 0)];
//! ```
//!
//! # Example
//!
//! ```rust
//! use either_both::prelude::*;
//!
//! pub struct ZipToEnd<A: Iterator, B: Iterator>(A, B);
//!
//! impl<A: Iterator, B: Iterator> Iterator for ZipToEnd<A, B> {
//!     type Item = Either<<A as Iterator>::Item, <B as Iterator>::Item>;
//!
//!     fn next(&mut self) -> Option<Self::Item> {
//!         Either::from_options(self.0.next(), self.1.next())
//!     }
//! }
//! ```
//!
//! [either-crate]: https://crates.io/crates/either
#![cfg_attr(not(feature = "std"), no_std)]
use core::{convert::identity, iter::FusedIterator, ops::Add};

pub use Either::{Both, Left, Right};

pub mod prelude;
/// The main enum, with variants `Left`, `Right`, and `Both`.
///
/// Because `Both` represents *both* left and right variants being present, most
/// methods that act on either `Left` or `Right` will also act on `Both`. For
/// example, [`Either::left`] should only return `None` on the variant `Right`, and
/// `Some` on `Left` and `Both`. Methods that act *exclusively* on the `Left` or
/// `Right` variants will usually have "only" in the name, like [`Either::only_left`].
///
/// While most methods will have an "only" version, some will not if:
///
/// * other wording would be more descriptive. For example, rather than define `is_left`
///   and `is_only_left`, there is [`Either::is_left`] and [`Either::has_left`].
/// * it doesn't make sense to have an "only" version. For example, while there is
///   [`Either::map_left`], there isn't `map_only_left`, because it would be unknown
///   what the `Both` variant's left value should become when the left type changes.
///
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Either<L, R> {
    Left(L),
    Right(R),
    /// Both `Left` and `Right` variants, together.
    Both(L, R),
}

/// Always returns `None`, to represent when neither the left nor right value are
/// present.
///
/// Using `None` (or `Option::<Either::<L, R>>::None` for the long form) is fine.
///
/// # Example
///
/// ```rust
/// # use either_both::prelude::*;
/// let maybe_either: MaybeEither<u32, i32> = Either::from_options(None, None);
/// assert_eq!(maybe_either, neither());
/// ```
#[inline]
pub const fn neither<L, R>() -> MaybeEither<L, R> {
    None
}

/// A shortcut to represent the possibility of neither left nor right values existing
/// by wrapping the `Either<L, R>` in an `Option`.
pub type MaybeEither<L, R> = Option<Either<L, R>>;

impl<L, R> Either<L, R> {
    /// Converts two options to `Option<Either<L, R>>`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// assert!(Either::<(), ()>::from_options(None, None).is_none());
    /// let left = Either::<_, ()>::from_options(Some(1), None).unwrap();
    /// assert_eq!(left, Left(1));
    /// let right = Either::<(), _>::from_options(None, Some(1)).unwrap();
    /// assert_eq!(right, Right(1));
    /// let both = Either::from_options(Some('l'), Some('r')).unwrap();
    /// assert_eq!(both, Both('l', 'r'));
    /// ```
    pub fn from_options(left: Option<L>, right: Option<R>) -> MaybeEither<L, R> {
        let either = match (left, right) {
            (None, None) => return None,
            (Some(l), None) => Left(l),
            (None, Some(r)) => Right(r),
            (Some(l), Some(r)) => Both(l, r),
        };
        Some(either)
    }

    /// Converts `&Either<L, R>` to `Either<&L, &R>`
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let value_and_label = Both(1usize, "one");
    /// let threes: Either<usize, usize> = value_and_label
    ///     .map_left(|value| value + 2)
    ///     .map_right(|label| label.len());
    /// println!("still can print value_and_label: {value_and_label:?}");
    /// ```
    ///
    pub const fn as_ref(&self) -> Either<&L, &R> {
        match *self {
            Left(ref l) => Left(l),
            Right(ref r) => Right(r),
            Both(ref l, ref r) => Both(l, r),
        }
    }

    /// Gets the left value from either `Left` or `Both`. To exclude `Both`, use
    /// [`Either::only_left`].
    pub fn left(self) -> Option<L> {
        match self {
            Left(l) | Both(l, _) => Some(l),
            Right(_) => None,
        }
    }

    /// Gets the left value from only `Left`. To include `Both`, use [`Either::left`].
    pub fn only_left(self) -> Option<L> {
        match self {
            Left(l) => Some(l),
            _ => None,
        }
    }

    /// Gets the right value from either `Right` or `Both`. To exclude `Both`, use
    /// [`Either::only_right`].
    pub fn right(self) -> Option<R> {
        match self {
            Right(r) | Both(_, r) => Some(r),
            Left(_) => None,
        }
    }

    /// Gets the right value from only `Right`. To include `Both`, use [`Either::right`].
    pub fn only_right(self) -> Option<R> {
        match self {
            Right(r) => Some(r),
            _ => None,
        }
    }

    /// Gets both values if they exist.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let vehicles = Both(2u8, 1u8);
    /// let (cars, motorcycles) = vehicles
    ///     .both()
    ///     .expect("inventory for both cars and motorcycles to be tracked");
    /// assert_eq!(cars, 2);
    /// assert_eq!(motorcycles, 1);
    /// ```
    pub fn both(self) -> Option<(L, R)> {
        match self {
            Both(l, r) => Some((l, r)),
            _ => None,
        }
    }

    /// Tries to get a left value from either `Left` or `Both`. To exclude `Both`,
    /// use [`Either::expect_only_left`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let left: Either<_, ()> = Left(1);
    /// let one = left.expect_left("left to exist");
    /// ```
    ///
    /// ```rust,should_panic
    /// # use either_both::prelude::*;
    /// let right: Either<i32, _> = Right(());
    /// let two = right.expect_left("left to exist");
    /// ```
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let both = Both(3, ());
    /// let three = both.expect_left("left to exist");
    /// ```
    pub fn expect_left(self, message: &str) -> L {
        match self {
            Left(l) | Both(l, _) => l,
            Right(_) => panic!("{message}"),
        }
    }

    /// Tries to get a left value from `Left`. To include `Both`,
    /// use [`Either::expect_left`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let left: Either<_, ()> = Left(1);
    /// let one = left.expect_only_left("left to exist");
    /// ```
    ///
    /// ```rust,should_panic
    /// # use either_both::prelude::*;
    /// let right: Either<i32, _> = Right(());
    /// let two = right.expect_only_left("left to exist");
    /// ```
    ///
    /// ```rust,should_panic
    /// # use either_both::prelude::*;
    /// let both = Both(3, ());
    /// let three = both.expect_only_left("left to exist");
    /// ```
    pub fn expect_only_left(self, message: &str) -> L {
        if let Left(l) = self {
            l
        } else {
            panic!("{message}")
        }
    }

    /// Tries to get a right value from either `Right` or `Both`. To exclude `Both`,
    /// use [`Either::expect_only_right`].
    ///
    /// # Examples
    ///
    /// ```rust,should_panic
    /// # use either_both::prelude::*;
    /// let left: Either<_, i32> = Left(());
    /// let one = left.expect_right("left to exist");
    /// ```
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let right: Either<(), _> = Right(2);
    /// let two = right.expect_right("left to exist");
    /// ```
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let both = Both((), 3);
    /// let three = both.expect_right("left to exist");
    /// ```
    pub fn expect_right(self, message: &str) -> R {
        match self {
            Right(r) | Both(_, r) => r,
            Left(_) => panic!("{message}"),
        }
    }

    /// Tries to get a right value from `Right`. To include `Both`,
    /// use [`Either::expect_right`].
    ///
    /// # Examples
    ///
    /// ```rust,should_panic
    /// # use either_both::prelude::*;
    /// let left: Either<_, i32> = Left(());
    /// let one = left.expect_only_right("left to exist");
    /// ```
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let right: Either<(), _> = Right(2);
    /// let two = right.expect_only_right("left to exist");
    /// ```
    ///
    /// ```rust,should_panic
    /// # use either_both::prelude::*;
    /// let both = Both((), 3);
    /// let three = both.expect_only_right("left to exist");
    /// ```
    pub fn expect_only_right(self, message: &str) -> R {
        if let Right(r) = self {
            r
        } else {
            panic!("{message}")
        }
    }

    /// Tries to get both left and right values together.
    ///
    /// # Examples
    ///
    /// ```rust,should_panic
    /// # use either_both::prelude::*;
    /// let left: Either<_, i32> = Left(1);
    /// let (one, two) = left.expect_both("both to exist");
    /// ```
    ///
    /// ```rust,should_panic
    /// # use either_both::prelude::*;
    /// let right: Either<i32, _> = Right(4);
    /// let (three, four) = right.expect_both("both to exist");
    /// ```
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let both = Both(5, 6);
    /// let (five, six) = both.expect_both("both to exist");
    /// ```
    pub fn expect_both(self, message: &str) -> (L, R) {
        if let Both(l, r) = self {
            (l, r)
        } else {
            panic!("{message}")
        }
    }

    /// Tries to get a left value from either `Left` or `Both`. To exclude `Both`,
    /// use [`Either::unwrap_only_left`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let left: Either<_, ()> = Left(1);
    /// let one = left.unwrap_left();
    /// ```
    ///
    /// ```rust,should_panic
    /// # use either_both::prelude::*;
    /// let right: Either<i32, _> = Right(());
    /// let two = right.unwrap_left();
    /// ```
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let both = Both(3, ());
    /// let three = both.unwrap_left();
    /// ```
    #[inline]
    pub fn unwrap_left(self) -> L {
        self.expect_left("unwrap_left called on Right")
    }

    /// Tries to get a left value from `Left`. To include `Both`,
    /// use [`Either::unwrap_left`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let left: Either<_, ()> = Left(1);
    /// let one = left.unwrap_only_left();
    /// ```
    ///
    /// ```rust,should_panic
    /// # use either_both::prelude::*;
    /// let right: Either<i32, _> = Right(());
    /// let two = right.unwrap_only_left();
    /// ```
    ///
    /// ```rust,should_panic
    /// # use either_both::prelude::*;
    /// let both = Both(3, ());
    /// let three = both.unwrap_only_left();
    /// ```
    #[inline]
    pub fn unwrap_only_left(self) -> L {
        self.expect_only_left("unwrap_only_left called on Right or Both")
    }

    /// Tries to get a right value from either `Right` or `Both`. To exclude `Both`,
    /// use [`Either::unwrap_only_right`].
    ///
    /// # Examples
    ///
    /// ```rust,should_panic
    /// # use either_both::prelude::*;
    /// let left: Either<_, i32> = Left(());
    /// let one = left.unwrap_right();
    /// ```
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let right: Either<(), _> = Right(2);
    /// let two = right.unwrap_right();
    /// ```
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let both = Both((), 3);
    /// let three = both.unwrap_right();
    /// ```
    #[inline]
    pub fn unwrap_right(self) -> R {
        self.expect_right("unwrap_right called on Left")
    }

    /// Tries to get a right value from `Right`. To include `Both`,
    /// use [`Either::unwrap_right`].
    ///
    /// # Examples
    ///
    /// ```rust,should_panic
    /// # use either_both::prelude::*;
    /// let left: Either<_, i32> = Left(());
    /// let one = left.unwrap_only_right();
    /// ```
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let right: Either<(), _> = Right(2);
    /// let two = right.unwrap_only_right();
    /// ```
    ///
    /// ```rust,should_panic
    /// # use either_both::prelude::*;
    /// let both = Both((), 3);
    /// let three = both.unwrap_only_right();
    /// ```
    #[inline]
    pub fn unwrap_only_right(self) -> R {
        self.expect_only_right("unwrap_only_right called on Left or Both")
    }

    /// Tries to get both left and right values together.
    ///
    /// # Examples
    ///
    /// ```rust,should_panic
    /// # use either_both::prelude::*;
    /// let left: Either<_, i32> = Left(1);
    /// let (one, two) = left.unwrap_both();
    /// ```
    ///
    /// ```rust,should_panic
    /// # use either_both::prelude::*;
    /// let right: Either<i32, _> = Right(4);
    /// let (three, four) = right.unwrap_both();
    /// ```
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let both = Both(5, 6);
    /// let (five, six) = both.unwrap_both();
    /// ```
    #[inline]
    pub fn unwrap_both(self) -> (L, R) {
        self.expect_both("unwrap_both called on Left or Right")
    }

    /// Tries to get the left value, or uses a default value. To unwrap *only* the
    /// `Left` variant, and exclude `Both`, use
    /// [`Either::unwrap_only_left_or_default`].
    pub fn unwrap_left_or_default(self) -> L
    where
        L: Default,
    {
        match self {
            Left(l) | Both(l, _) => l,
            Right(_) => L::default(),
        }
    }

    /// Tries to get the left from `Left`, or uses a default value. To also use the left
    /// value from `Both`,  use [`Either::unwrap_left_or_default`].
    pub fn unwrap_only_left_or_default(self) -> L
    where
        L: Default,
    {
        match self {
            Left(l) => l,
            _ => L::default(),
        }
    }

    /// Tries to get the right value, or uses a default value. To unwrap *only* the
    /// `Right` variant, and exclude `Both`, use
    /// [`Either::unwrap_only_right_or_default`].
    pub fn unwrap_right_or_default(self) -> R
    where
        R: Default,
    {
        match self {
            Right(r) | Both(_, r) => r,
            Left(_) => R::default(),
        }
    }

    /// Tries to get the right from `Right`, or uses a default value. To also use the
    /// right value from `Both`,  use [`Either::unwrap_right_or_default`].
    pub fn unwrap_only_right_or_default(self) -> R
    where
        R: Default,
    {
        match self {
            Right(r) => r,
            _ => R::default(),
        }
    }

    /// Tries to get both the left and right values, and uses a default value for any
    /// missing value. To unwrap only `Both`, use [`Either::unwrap_only_both_or_default`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let left: Either<_, &str> = Left("left");
    /// assert_eq!(left.unwrap_both_or_default(), ("left", ""));
    /// let right: Either<&str, _> = Right("right");
    /// assert_eq!(right.unwrap_both_or_default(), ("", "right"));
    /// let both = Both("left", "right");
    /// assert_eq!(both.unwrap_both_or_default(), ("left", "right"));
    /// ```
    pub fn unwrap_both_or_default(self) -> (L, R)
    where
        L: Default,
        R: Default,
    {
        match self {
            Left(l) => (l, R::default()),
            Right(r) => (L::default(), r),
            Both(l, r) => (l, r),
        }
    }

    /// Tries to get both the left and right values. If the variant is not `Both`,
    /// the default value will be used for both `L` and `R`. To keep the existing
    /// value in a `Left` or `Right` variant, use [`Either::unwrap_both_or_default`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let left: Either<_, &str> = Left("left");
    /// assert_eq!(left.unwrap_only_both_or_default(), ("", ""));
    /// let right: Either<&str, _> = Right("right");
    /// assert_eq!(right.unwrap_only_both_or_default(), ("", ""));
    /// let both = Both("left", "right");
    /// assert_eq!(both.unwrap_only_both_or_default(), ("left", "right"));
    /// ```
    pub fn unwrap_only_both_or_default(self) -> (L, R)
    where
        L: Default,
        R: Default,
    {
        match self {
            Both(l, r) => (l, r),
            _ => Default::default(),
        }
    }

    /// Maps `Either<L, R>` to `Either<L2, R2>` by applying a function to the left
    /// and right values.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let label: Either<_, i32> = Left("one");
    /// let value: Either<&str, _> = Right(1);
    /// let item = Both("one", 1);
    ///
    /// assert_eq!(label.map(str::len, |n| n + 2), Left(3));
    /// assert_eq!(value.map(str::len, |n| n + 2), Right(3));
    /// assert_eq!(item.map(str::len, |n| n + 2), Both(3, 3));
    /// ```
    #[inline]
    pub fn map<L2, R2, LF, RF>(self, left: LF, right: RF) -> Either<L2, R2>
    where
        LF: FnOnce(L) -> L2,
        RF: FnOnce(R) -> R2,
    {
        match self {
            Left(l) => Left(left(l)),
            Right(r) => Right(right(r)),
            Both(l, r) => Both(left(l), right(r)),
        }
    }

    /// Maps `Either<L, R>` to `Either<L2, R>` by applying a function to `Left` or
    /// `Both`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let num_or_str: Either<_, &str> = Left(1usize);
    /// let b: Either<bool, &str> = num_or_str.map_left(|num| num == 1);
    /// assert_eq!(b, Left(true));
    /// ```
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let num_or_str = Both(1usize, "false");
    /// let b: Either<bool, &str> = num_or_str.map_left(|num| num == 1);
    /// assert_eq!(b, Both(true, "false"));
    /// ```
    #[inline]
    pub fn map_left<L2, F>(self, f: F) -> Either<L2, R>
    where
        F: FnOnce(L) -> L2,
    {
        self.map(f, identity)
    }

    /// Maps `Either<L, R>` to `Either<L2, R>` by applying a function to `Right` or
    /// `Both`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let num_or_str: Either<usize, _> = Right("false");
    /// let b: Either<usize, bool> = num_or_str.map_right(|s| s == "true");
    /// assert_eq!(b, Right(false));
    /// ```
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let num_or_str = Both(1usize, "false");
    /// let b: Either<usize, bool> = num_or_str.map_right(|s| s == "true");
    /// assert_eq!(b, Both(1, false));
    /// ```
    #[inline]
    pub fn map_right<R2, F>(self, f: F) -> Either<L, R2>
    where
        F: FnOnce(R) -> R2,
    {
        self.map(identity, f)
    }

    /// Calls the left function on the left value and the right function on the right value.
    /// Returns the original `Either`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let list = vec![1, 2, 3];
    /// // NOTE from_options returns an Option<Either<L, R>>
    /// let sum = Either::from_options(list.get(0), list.get(2))
    ///     .and_then(|either| {
    ///         either
    ///             .inspect(|l| println!("left = {l}"), |r| println!("right = {r}"))
    ///             .both()
    ///     })
    ///     .map(|(l, r)| l + r)
    ///     .expect("list should have indices 0 and 2");
    /// ```
    ///
    pub fn inspect<LF, RF>(self, left: LF, right: RF) -> Self
    where
        LF: FnOnce(&L),
        RF: FnOnce(&R),
    {
        match self {
            Left(ref l) => left(l),
            Right(ref r) => right(r),
            Both(ref l, ref r) => {
                left(l);
                right(r);
            }
        }
        self
    }

    /// Calls a function with a reference to the left value. Returns the original
    /// `Either`.
    ///
    /// To call the function on only the `Left` variant, use
    /// [`Either::inspect_only_left`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let list = vec![1, 2, 3];
    /// // NOTE from_options returns an Option<Either<L, R>>
    /// let first = Either::from_options(list.get(0), list.get(100))
    ///     .and_then(|either| {
    ///         either
    ///             .inspect_left(|l| println!("left = {l}"))
    ///             .left()
    ///     })
    ///     .expect("list should have index 0");
    /// ```
    #[inline]
    pub fn inspect_left<F>(self, f: F) -> Self
    where
        F: FnOnce(&L),
    {
        self.inspect(f, noop1)
    }

    /// Calls a function with a reference to the value contained in only the `Left`
    /// variant. Returns the original `Either`.
    ///
    /// To call the function on the `Left` *or* `Both` variant, use
    /// [`Either::inspect_left`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let list = vec![1, 2, 3];
    /// // NOTE from_options returns an Option<Either<L, R>>
    /// let first = Either::from_options(list.get(0), list.get(100))
    ///     .and_then(|either| {
    ///         either
    ///             .inspect_only_left(|l| println!("left = {l}"))
    ///             .only_left()
    ///     })
    ///     .expect("list should have index 0 and not index 100");
    /// ```
    pub fn inspect_only_left<F>(self, f: F) -> Self
    where
        F: FnOnce(&L),
    {
        if let Left(ref l) = self {
            f(l);
        }
        self
    }

    /// Calls a function with a reference to the right value. Returns the original
    /// `Either`.
    ///
    /// To call the function on only the `Right` variant, use
    /// [`Either::inspect_only_right`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let list = vec![1, 2, 3];
    /// // NOTE from_options returns an Option<Either<L, R>>
    /// let last = Either::from_options(list.get(0), list.get(2))
    ///     .and_then(|either| {
    ///         either
    ///             .inspect_right(|r| println!("right = {r}"))
    ///             .right()
    ///     })
    ///     .expect("list should have index 2");
    /// ```
    #[inline]
    pub fn inspect_right<F>(self, f: F) -> Self
    where
        F: FnOnce(&R),
    {
        self.inspect(noop1, f)
    }

    /// Calls a function with a reference to the value contained in only the `Right`
    /// variant. Returns the original `Either`.
    ///
    /// To call the function on the `Right` *or* `Both` variant, use
    /// [`Either::inspect_right`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let list = vec![1, 2, 3];
    /// // NOTE from_options returns an Option<Either<L, R>>
    /// let last = Either::from_options(list.get(100), list.get(2))
    ///     .and_then(|either| {
    ///         either
    ///             .inspect_only_right(|r| println!("right = {r}"))
    ///             .only_right()
    ///     })
    ///     .expect("list shouldn't have index 100 but should have index 2");
    /// ```
    pub fn inspect_only_right<F>(self, f: F) -> Self
    where
        F: FnOnce(&R),
    {
        if let Right(ref r) = self {
            f(r);
        }
        self
    }

    /// Calls a function with a reference to the left value and a reference to the
    /// right value contained in (and only in) `Both`.
    ///
    /// If you would like to inspect all possible variants, you can chain
    /// [`Either::inspect_left`] and [`Either::inspect_right`] instead.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let list = vec![1, 2, 3];
    /// // NOTE from_options returns an Option<Either<L, R>>
    /// let (first, last) = Either::from_options(list.get(0), list.get(2))
    ///     .and_then(|either| {
    ///         either
    ///             .inspect_both(|l, r| println!("left = {l}, right = {r}"))
    ///             .both()
    ///     })
    ///     .expect("list should have indices 0 and 2");
    /// ```
    pub fn inspect_both<F>(self, f: F) -> Self
    where
        F: FnOnce(&L, &R),
    {
        if let Both(ref l, ref r) = self {
            f(l, r);
        }
        self
    }

    /// If the left value doesn't exist, it is populated.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let left: Either<u32, u64> = Left(1);
    /// assert_eq!(left.fill_left(100), Left(1));
    /// let right: Either<u32, u64> = Right(2);
    /// assert_eq!(right.fill_left(100), Both(100, 2));
    /// let both: Either<u32, u64> = Both(3, 4);
    /// assert_eq!(both.fill_left(100), Both(3, 4));
    /// ```
    pub fn fill_left(self, left: L) -> Either<L, R> {
        match self {
            Left(l) => Left(l),
            Right(r) => Both(left, r),
            Both(l, r) => Both(l, r),
        }
    }

    /// If the left value doesn't exist, it is populated.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let left: Either<u32, u64> = Left(1);
    /// assert_eq!(left.fill_left_lazy(|| 100), Left(1));
    /// let right: Either<u32, u64> = Right(2);
    /// assert_eq!(right.fill_left_lazy(|| 100), Both(100, 2));
    /// let both: Either<u32, u64> = Both(3, 4);
    /// assert_eq!(both.fill_left_lazy(|| 100), Both(3, 4));
    /// ```
    pub fn fill_left_lazy<F>(self, f: F) -> Either<L, R>
    where
        F: FnOnce() -> L,
    {
        match self {
            Left(l) => Left(l),
            Right(r) => Both(f(), r),
            Both(l, r) => Both(l, r),
        }
    }

    /// If the right value doesn't exist, it is populated.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let left: Either<u32, u64> = Left(1);
    /// assert_eq!(left.fill_right(100), Both(1, 100));
    /// let right: Either<u32, u64> = Right(2);
    /// assert_eq!(right.fill_right(100), Right(2));
    /// let both: Either<u32, u64> = Both(3, 4);
    /// assert_eq!(both.fill_right(100), Both(3, 4));
    /// ```
    pub fn fill_right(self, right: R) -> Either<L, R> {
        match self {
            Left(l) => Both(l, right),
            Right(r) => Right(r),
            Both(l, r) => Both(l, r),
        }
    }

    /// If the right value doesn't exist, it is populated.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let left: Either<u32, u64> = Left(1);
    /// assert_eq!(left.fill_right_lazy(|| 100), Both(1, 100));
    /// let right: Either<u32, u64> = Right(2);
    /// assert_eq!(right.fill_right_lazy(|| 100), Right(2));
    /// let both: Either<u32, u64> = Both(3, 4);
    /// assert_eq!(both.fill_right_lazy(|| 100), Both(3, 4));
    /// ```
    pub fn fill_right_lazy<F>(self, f: F) -> Either<L, R>
    where
        F: FnOnce() -> R,
    {
        match self {
            Left(l) => Both(l, f()),
            Right(r) => Right(r),
            Both(l, r) => Both(l, r),
        }
    }

    /// Returns `true` if the variant is `Left`. To check if a left value exists (which
    /// includes `Both`) [`Either::has_left`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let left: Either<_, ()> = Left(());
    /// assert!(left.is_left());
    /// let both = Both((), ());
    /// assert!(!both.is_left());
    /// ```
    #[inline]
    pub const fn is_left(&self) -> bool {
        matches!(self, Left(_))
    }

    /// Returns `true` if the variant is `Right`. To check if a right value exists (which
    /// includes `Both`) [`Either::has_right`].
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let right: Either<(), _> = Right(());
    /// assert!(right.is_right());
    /// let both = Both((), ());
    /// assert!(!both.is_right());
    /// ```
    #[inline]
    pub const fn is_right(&self) -> bool {
        matches!(self, Right(_))
    }

    /// Returns `true` if the variant is `Both`.
    #[inline]
    pub const fn is_both(&self) -> bool {
        matches!(self, Both(_, _))
    }

    /// Returns `true` if the variant is `Left` or `Both`. To check for only `Left`,
    /// use [`Either::is_left`].
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let left: Either<_, ()> = Left(());
    /// assert!(left.has_left());
    /// let both = Both((), ());
    /// assert!(both.has_left());
    /// ```
    #[inline]
    pub const fn has_left(&self) -> bool {
        matches!(self, Left(_) | Both(_, _))
    }

    /// Returns `true` if the variant is `Right` or `Both`. To check for only `Right`,
    /// use [`Either::is_right`].
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let right: Either<(), _> = Right(());
    /// assert!(right.has_right());
    /// let both = Both((), ());
    /// assert!(both.has_right());
    /// ```
    #[inline]
    pub const fn has_right(&self) -> bool {
        matches!(self, Right(_) | Both(_, _))
    }

    /// Returns `true` if a left value exists and `f` returns `true`. If you want
    /// to return *`false`* on `Both`, use [`Either::is_left_and`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let left: Either<_, ()> = Left(1);
    /// assert!(left.has_left_and(|n| *n == 1));
    /// let both = Both(1, ());
    /// assert!(both.has_left_and(|n| *n == 1));
    /// ```
    pub fn has_left_and<F>(&self, f: F) -> bool
    where
        F: FnOnce(&L) -> bool,
    {
        match self {
            Self::Left(l) | Self::Both(l, _) => f(l),
            Self::Right(_) => false,
        }
    }

    /// Returns `true` the variant is `Left` and `f` returns `true`. If you want
    /// to allow `Both` to return `true`, use [`Either::has_left_and`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let left: Either<_, ()> = Left(1);
    /// assert!(left.is_left_and(|n| *n == 1));
    /// let both = Both(1, ());
    /// assert!(!both.is_left_and(|n| *n == 1));
    /// ```
    pub fn is_left_and<F>(&self, f: F) -> bool
    where
        F: FnOnce(&L) -> bool,
    {
        if let Left(l) = self { f(l) } else { false }
    }

    /// Returns `true` if a right value exists and `f` returns `true`. If you want
    /// to return *`false`* on `Both`, use [`Either::is_right_and`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let right: Either<(), _> = Right(1);
    /// assert!(right.has_right_and(|n| *n == 1));
    /// let both = Both((), 1);
    /// assert!(both.has_right_and(|n| *n == 1));
    /// ```
    pub fn has_right_and<F>(&self, f: F) -> bool
    where
        F: FnOnce(&R) -> bool,
    {
        match self {
            Self::Right(r) | Self::Both(_, r) => f(r),
            Self::Left(_) => false,
        }
    }

    /// Returns `true` the variant is `Right` and  `f` returns `true`. If you want
    /// to allow `Both` to return `true`, use [`Either::has_right_and`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let right: Either<(), _> = Right(1);
    /// assert!(right.is_right_and(|n| *n == 1));
    /// let both = Both((), 1);
    /// assert!(!both.is_right_and(|n| *n == 1));
    /// ```
    pub fn is_right_and<F>(&self, f: F) -> bool
    where
        F: FnOnce(&R) -> bool,
    {
        if let Right(r) = self { f(r) } else { false }
    }

    /// Returns `true` if both left and right values exist and `f` returns `true`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let both = Both(1, 2);
    /// assert!(both.is_both_and(|a, b| a + b == 3));
    /// ```
    pub fn is_both_and<F>(&self, f: F) -> bool
    where
        F: FnOnce(&L, &R) -> bool,
    {
        if let Both(l, r) = self {
            f(l, r)
        } else {
            false
        }
    }

    /// Swaps the left and right values.
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let left: Either<_, ()> = Left('l');
    /// assert_eq!(left.swap(), Right('l'));
    /// let right: Either<(), _> = Right('r');
    /// assert_eq!(right.swap(), Left('r'));
    /// let both = Both('l', 'r');
    /// assert_eq!(both.swap(), Both('r', 'l'));
    /// ```
    pub fn swap(self) -> Either<R, L> {
        match self {
            Left(l) => Right(l),
            Right(r) => Left(r),
            Both(l, r) => Both(r, l),
        }
    }

    /// Uses a function to fold the left and right values into each other.
    /// `default_left` and `default_right` are used where the left value or right
    /// value isn't available.
    ///
    /// If generating `default_left` or `default_right` is an expensive operation,
    /// consider using [`Either::fold_with`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let list = vec![1];
    ///
    /// let left = Either::from_options(list.first().copied(), list.get(1).copied())
    ///     .expect("list should have at least one element");
    /// let sum = left.fold(100, 2, |l, r| l + r);
    /// assert_eq!(sum, 1 + 2);
    /// ```
    #[inline]
    pub fn fold<T, F>(self, default_left: L, default_right: R, f: F) -> T
    where
        F: FnOnce(L, R) -> T,
    {
        self.fold_with(|| default_left, || default_right, f)
    }

    /// Uses a function to fold the left and right values into each other.
    /// `default_left` and `default_right` are used where the left value or right
    /// value isn't available.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// fn expensive_function() -> i32 {
    ///     100
    /// }
    /// let list = vec![1];
    ///
    /// let left = Either::from_options(list.first().copied(), list.get(1).copied())
    ///     .expect("list should have at least one element");
    /// let sum = left.fold_with(
    ///     expensive_function,
    ///     expensive_function,
    ///     |l, r| l + r,
    /// );
    /// assert_eq!(sum, 1 + 100);
    /// ```
    pub fn fold_with<T, F, DLF, DRF>(self, default_left: DLF, default_right: DRF, f: F) -> T
    where
        F: FnOnce(L, R) -> T,
        DLF: FnOnce() -> L,
        DRF: FnOnce() -> R,
    {
        let (left, right) = match self {
            Left(l) => (l, default_right()),
            Right(r) => (default_left(), r),
            Both(l, r) => (l, r),
        };
        f(left, right)
    }

    #[inline]
    const fn count_usize(&self) -> usize {
        if self.is_both() { 2 } else { 1 }
    }
}

impl<L, R> Either<&L, R> {
    pub fn left_copied(self) -> Either<L, R>
    where
        L: Copy,
    {
        match self {
            Left(&l) => Left(l),
            Right(r) => Right(r),
            Both(&l, r) => Both(l, r),
        }
    }

    #[inline]
    pub fn left_cloned(self) -> Either<L, R>
    where
        L: Clone,
    {
        self.map_left(|l| l.clone())
    }
}

impl<L, R> Either<L, &R> {
    pub fn right_copied(self) -> Either<L, R>
    where
        R: Copy,
    {
        match self {
            Left(l) => Left(l),
            Right(&r) => Right(r),
            Both(l, &r) => Both(l, r),
        }
    }

    #[inline]
    pub fn right_cloned(self) -> Either<L, R>
    where
        R: Clone,
    {
        self.map_right(|r| r.clone())
    }
}

impl<L, R> Either<&L, &R> {
    pub const fn copied(self) -> Either<L, R>
    where
        L: Copy,
        R: Copy,
    {
        match self {
            Left(&l) => Left(l),
            Right(&r) => Right(r),
            Both(&l, &r) => Both(l, r),
        }
    }

    #[inline]
    pub fn cloned(self) -> Either<L, R>
    where
        L: Clone,
        R: Clone,
    {
        self.map(Clone::clone, Clone::clone)
    }
}

impl<L, R> Either<&mut L, R> {
    pub fn left_copied(self) -> Either<L, R>
    where
        L: Copy,
    {
        match self {
            Left(&mut l) => Left(l),
            Right(r) => Right(r),
            Both(&mut l, r) => Both(l, r),
        }
    }

    #[inline]
    pub fn left_cloned(self) -> Either<L, R>
    where
        L: Clone,
    {
        self.map_left(|l| l.clone())
    }
}

impl<L, R> Either<L, &mut R> {
    pub fn right_copied(self) -> Either<L, R>
    where
        R: Copy,
    {
        match self {
            Left(l) => Left(l),
            Right(&mut r) => Right(r),
            Both(l, &mut r) => Both(l, r),
        }
    }

    #[inline]
    pub fn right_cloned(self) -> Either<L, R>
    where
        R: Clone,
    {
        self.map_right(|r| r.clone())
    }
}

impl<L, R> Either<&mut L, &mut R> {
    pub const fn copied(self) -> Either<L, R>
    where
        L: Copy,
        R: Copy,
    {
        match self {
            Left(&mut l) => Left(l),
            Right(&mut r) => Right(r),
            Both(&mut l, &mut r) => Both(l, r),
        }
    }

    #[inline]
    pub fn cloned(self) -> Either<L, R>
    where
        L: Clone,
        R: Clone,
    {
        self.map(|l| l.clone(), |r| r.clone())
    }
}

impl<L, R> Either<Option<L>, Option<R>> {
    /// Converts an `Either<Option<L>, Option<R>>` to an `Option<Either<L, R>>`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let nothing: Either<Option<()>, Option<()>> = Both(None, None);
    /// assert_eq!(nothing.transpose(), None);
    /// let left: Either<_, Option<char>> = Left(Some('l'));
    /// assert_eq!(left.transpose(), Some(Left('l')));
    /// let left: Either<_, Option<char>> = Both(Some('l'), None);
    /// assert_eq!(left.transpose(), Some(Left('l')));
    /// let both = Both(Some('l'), Some('r'));
    /// assert_eq!(both.transpose(), Some(Both('l', 'r')));
    /// ```
    pub fn transpose(self) -> MaybeEither<L, R> {
        match self {
            Left(None) | Right(None) | Both(None, None) => None,
            Left(Some(l)) | Both(Some(l), None) => Some(Left(l)),
            Right(Some(r)) | Both(None, Some(r)) => Some(Right(r)),
            Both(Some(l), Some(r)) => Some(Both(l, r)),
        }
    }
}

impl<L, EL, R, ER> Either<Result<L, EL>, Result<R, ER>> {
    /// Converts an `Either<Result<L, EL>, Result<R, ER>>` to an
    /// `Result<Either<L, R>, Either<EL, ER>>`.
    ///
    /// In the case of mixed results (`Both(ok, err)` or `Both(err, ok)`), `Ok` will
    /// be returned if `prefer_ok` is `true`, and `Err` will be returned if `prefer_ok`
    /// is `false`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let ok_left: Either<Result<_, ()>, Result<(), ()>> = Left(Ok(1));
    /// assert_eq!(ok_left.transpose(true), Ok(Left(1)));
    /// let ok_both: Either<Result<_, ()>, Result<_, ()>> = Both(Ok(3), Ok(4));
    /// assert_eq!(ok_both.transpose(true), Ok(Both(3, 4)));
    /// let err_left: Either<Result<(), _>, Result<(), ()>> = Left(Err('a'));
    /// assert_eq!(err_left.transpose(true), Err(Left('a')));
    /// let err_both: Either<Result<(), _>, Result<(), _>> = Both(Err('b'), Err('c'));
    /// assert_eq!(err_both.transpose(true), Err(Both('b', 'c')));
    ///
    /// // The prefer_ok argument is used to decide what to do with mixed results.
    /// let mixed_results: Either<Result<bool, _>, Result<_, ()>>
    ///     = Both(Err("error"), Ok("success"));
    /// assert_eq!(mixed_results.transpose(true), Ok(Right("success")));
    /// let mixed_results: Either<Result<bool, _>, Result<_, ()>>
    ///     = Both(Err("error"), Ok("success"));
    /// assert_eq!(mixed_results.transpose(false), Err(Left("error")));
    /// ```
    pub fn transpose(self, prefer_ok: bool) -> Result<Either<L, R>, Either<EL, ER>> {
        match self {
            Left(Ok(l)) => Ok(Left(l)),
            Left(Err(el)) => Err(Left(el)),
            Right(Ok(r)) => Ok(Right(r)),
            Right(Err(er)) => Err(Right(er)),
            Both(Ok(l), Ok(r)) => Ok(Both(l, r)),
            Both(Err(el), Err(er)) => Err(Both(el, er)),
            Both(Ok(l), Err(er)) => {
                if prefer_ok {
                    Ok(Left(l))
                } else {
                    Err(Right(er))
                }
            }
            Both(Err(el), Ok(r)) => {
                if prefer_ok {
                    Ok(Right(r))
                } else {
                    Err(Left(el))
                }
            }
        }
    }
}

impl<T> Either<T, T> {
    /// Gets the total value of the left and/or right values. If only one value exists,
    /// it is returned. If both left and right values exist, they are added together.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// use std::collections::HashMap;
    /// let mut vehicles = HashMap::from([("car", 3usize)]);
    /// let total = Either::from_options(vehicles.get("car").copied(), vehicles.get("truck").copied())
    ///     .map(|either| either.total())
    ///     .expect("vehicles should have at least one entry");
    /// assert_eq!(total, 3);
    ///
    /// vehicles.insert("truck", 2);
    /// let total = Either::from_options(vehicles.get("car").copied(), vehicles.get("truck").copied())
    ///     .map(|either| either.total())
    ///     .expect("vehicles should have at least one entry");
    /// assert_eq!(total, 3 + 2);
    /// ```
    pub fn total(self) -> T
    where
        T: Add<T, Output = T>,
    {
        match self {
            Left(l) => l,
            Right(r) => r,
            Both(l, r) => l + r,
        }
    }

    /// Creates an iterator that iterates over one or two items. In the case of `Both`,
    /// the left value will always be the first item, and the right value will be the
    /// second.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let either: Either<_, char> = Left('l');
    /// let mut iter = either.iter();
    /// assert_eq!(iter.next(), Some(&'l'));
    /// assert_eq!(iter.next(), None);
    /// ```
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let either: Either<char, _> = Right('r');
    /// let mut iter = either.iter();
    /// assert_eq!(iter.next(), Some(&'r'));
    /// assert_eq!(iter.next(), None);
    /// ```
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let either = Both('l', 'r');
    /// let mut iter = either.iter();
    /// assert_eq!(iter.next(), Some(&'l'));
    /// assert_eq!(iter.next(), Some(&'r'));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            inner: Some(self.as_ref()),
        }
    }
}

/// The iterator for [`Either`].
pub struct Iter<'a, T> {
    inner: MaybeEither<&'a T, &'a T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner {
            None => None,
            Some(Left(v)) | Some(Right(v)) => {
                self.inner = None;
                Some(v)
            }
            Some(Both(l, r)) => {
                self.inner = Some(Right(r));
                Some(l)
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.inner.as_ref().map(|e| e.count_usize()).unwrap_or(0);
        (size, Some(size))
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self.inner {
            None => None,
            Some(Left(v)) | Some(Right(v)) => {
                self.inner = None;
                Some(v)
            }
            Some(Both(l, r)) => {
                self.inner = Some(Left(l));
                Some(r)
            }
        }
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {}

impl<'a, T> FusedIterator for Iter<'a, T> {}

impl<L, R> From<(L, R)> for Either<L, R> {
    /// Converts a tuple of two values to `Both`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use either_both::prelude::*;
    /// let item = ("Dark mode", true);
    /// let label_and_value = Either::from(item);
    /// assert_eq!(label_and_value, Both("Dark mode", true));
    /// ```
    #[inline]
    fn from((left, right): (L, R)) -> Self {
        Self::Both(left, right)
    }
}

/// Takes one argument and does nothing.
#[inline]
const fn noop1<T>(_: &T) {}

#[cfg(feature = "either")]
mod either_interop;

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case(Left(()), Some(()))]
    #[case(Right(()), None)]
    #[case(Both((), ()), Some(()))]
    fn test_left(#[case] variant: Either<(), ()>, #[case] expected: Option<()>) {
        assert_eq!(variant.left(), expected);
    }

    #[rstest]
    #[case(Left(()), Some(()))]
    #[case(Right(()), None)]
    #[case(Both((), ()), None)]
    fn test_only_left(#[case] variant: Either<(), ()>, #[case] expected: Option<()>) {
        assert_eq!(variant.only_left(), expected);
    }

    #[rstest]
    #[case(Left(()), None)]
    #[case(Right(()), Some(()))]
    #[case(Both((), ()), Some(()))]
    fn test_right(#[case] variant: Either<(), ()>, #[case] expected: Option<()>) {
        assert_eq!(variant.right(), expected);
    }

    #[rstest]
    #[case(Left(()), None)]
    #[case(Right(()), Some(()))]
    #[case(Both((), ()), None)]
    fn test_only_right(#[case] variant: Either<(), ()>, #[case] expected: Option<()>) {
        assert_eq!(variant.only_right(), expected);
    }

    #[rstest]
    #[case(Left(()))]
    #[case(Both((), ()))]
    fn ok_test_unwrap_left(#[case] either: Either<(), ()>) {
        either.unwrap_left()
    }

    #[test]
    fn ok_test_unwrap_only_left() {
        let left: Either<_, ()> = Left(());
        left.unwrap_only_left()
    }

    #[rstest]
    #[case(Right(()))]
    #[case(Both((), ()))]
    fn ok_test_unwrap_right(#[case] either: Either<(), ()>) {
        either.unwrap_right()
    }

    #[test]
    fn ok_test_unwrap_only_right() {
        let right: Either<(), _> = Right(());
        right.unwrap_only_right()
    }

    #[rstest]
    #[case(Left(()))]
    #[case(Both((), ()))]
    fn ok_test_expect_left(#[case] either: Either<(), ()>) {
        either.expect_left("left value to exist")
    }

    #[test]
    fn ok_test_expect_only_left() {
        let left: Either<_, ()> = Left(());
        left.expect_only_left("only left value to exist")
    }

    #[rstest]
    #[case(Right(()))]
    #[case(Both((), ()))]
    fn ok_test_expect_right(#[case] either: Either<(), ()>) {
        either.expect_right("right value to exist")
    }

    #[test]
    fn ok_test_expect_only_right() {
        let right: Either<(), _> = Right(());
        right.expect_only_right("only right value to exist")
    }

    #[test]
    #[should_panic(expected = "unwrap_left called on Right")]
    fn panic_test_unwrap_left() {
        let right: Either<(), _> = Right(());
        right.unwrap_left()
    }

    #[rstest]
    #[case(Right(()))]
    #[case(Both((), ()))]
    #[should_panic(expected = "unwrap_only_left called on Right or Both")]
    fn panic_test_unwrap_only_left(#[case] either: Either<(), ()>) {
        either.unwrap_only_left()
    }

    #[test]
    #[should_panic(expected = "unwrap_right called on Left")]
    fn panic_test_unwrap_right() {
        let left: Either<_, ()> = Left(());
        left.unwrap_right()
    }

    #[rstest]
    #[case(Left(()))]
    #[case(Both((), ()))]
    #[should_panic(expected = "unwrap_only_right called on Left or Both")]
    fn panic_test_unwrap_only_right(#[case] either: Either<(), ()>) {
        either.unwrap_only_right()
    }

    #[test]
    #[should_panic(expected = "left value to exist")]
    fn panic_test_expect_left() {
        let right: Either<(), _> = Right(());
        right.expect_left("left value to exist")
    }

    #[rstest]
    #[case(Right(()))]
    #[case(Both((), ()))]
    #[should_panic(expected = "only left value to exist")]
    fn panic_test_expect_only_left(#[case] either: Either<(), ()>) {
        either.expect_only_left("only left value to exist")
    }

    #[test]
    #[should_panic(expected = "right value to exist")]
    fn panic_test_expect_right() {
        let left: Either<_, ()> = Left(());
        left.expect_right("right value to exist")
    }

    #[rstest]
    #[case(Left(()))]
    #[case(Both((), ()))]
    #[should_panic(expected = "only right value to exist")]
    fn panic_test_expect_only_right(#[case] either: Either<(), ()>) {
        either.expect_only_right("only right value to exist")
    }

    #[rstest]
    #[case(Left(1), Left(1))]
    #[case(Right(2), Both(100, 2))]
    #[case(Both(1, 2), Both(1, 2))]
    fn test_fill_left(#[case] either: Either<u8, u8>, #[case] expected: Either<u8, u8>) {
        assert_eq!(either.fill_left(100), expected);
    }

    #[rstest]
    #[case(Left(1), Left(1))]
    #[case(Right(2), Both(100, 2))]
    #[case(Both(1, 2), Both(1, 2))]
    fn test_fill_left_lazy(#[case] either: Either<u8, u8>, #[case] expected: Either<u8, u8>) {
        assert_eq!(either.fill_left_lazy(|| 100), expected);
    }

    #[rstest]
    #[case(Left(1), Both(1, 100))]
    #[case(Right(2), Right(2))]
    #[case(Both(1, 2), Both(1, 2))]
    fn test_fill_right(#[case] either: Either<u8, u8>, #[case] expected: Either<u8, u8>) {
        assert_eq!(either.fill_right(100), expected);
    }

    #[rstest]
    #[case(Left(1), Both(1, 100))]
    #[case(Right(2), Right(2))]
    #[case(Both(1, 2), Both(1, 2))]
    fn test_fill_right_lazy(#[case] either: Either<u8, u8>, #[case] expected: Either<u8, u8>) {
        assert_eq!(either.fill_right_lazy(|| 100), expected);
    }

    #[rstest]
    #[case(Left(()), true)]
    #[case(Right(()), false)]
    #[case(Both((), ()), false)]
    fn test_is_left(#[case] either: Either<(), ()>, #[case] expected: bool) {
        assert_eq!(either.is_left(), expected);
    }

    #[rstest]
    #[case(Left(()), false)]
    #[case(Right(()), true)]
    #[case(Both((), ()), false)]
    fn test_is_right(#[case] either: Either<(), ()>, #[case] expected: bool) {
        assert_eq!(either.is_right(), expected);
    }

    #[rstest]
    #[case(Left(()), false)]
    #[case(Right(()), false)]
    #[case(Both((), ()), true)]
    fn test_is_both(#[case] either: Either<(), ()>, #[case] expected: bool) {
        assert_eq!(either.is_both(), expected);
    }

    #[rstest]
    #[case(Left(()), true)]
    #[case(Right(()), false)]
    #[case(Both((), ()), true)]
    fn test_has_left(#[case] either: Either<(), ()>, #[case] expected: bool) {
        assert_eq!(either.has_left(), expected);
    }

    #[rstest]
    #[case(Left(()), false)]
    #[case(Right(()), true)]
    #[case(Both((), ()), true)]
    fn test_has_right(#[case] either: Either<(), ()>, #[case] expected: bool) {
        assert_eq!(either.has_right(), expected);
    }

    #[rstest]
    #[case(Left(()), true, false)]
    #[case(Right(()), false, true)]
    #[case(Both((), ()), true, true)]
    fn test_inspect(
        #[case] either: Either<(), ()>,
        #[case] should_call_left: bool,
        #[case] should_call_right: bool,
    ) {
        let mut left_called = false;
        let mut right_called = false;
        either.inspect(
            |_| {
                left_called = true;
            },
            |_| {
                right_called = true;
            },
        );
        assert_eq!(left_called, should_call_left);
        assert_eq!(right_called, should_call_right);
    }

    #[rstest]
    #[case(Left(()), true)]
    #[case(Right(()), false)]
    #[case(Both((), ()), true)]
    fn test_inspect_left(#[case] either: Either<(), ()>, #[case] should_call: bool) {
        let mut called = false;
        either.inspect_left(|_| {
            called = true;
        });
        assert_eq!(called, should_call);
    }

    #[rstest]
    #[case(Left(()), true)]
    #[case(Right(()), false)]
    #[case(Both((), ()), false)]
    fn test_inspect_only_left(#[case] either: Either<(), ()>, #[case] should_call: bool) {
        let mut called = false;
        either.inspect_only_left(|_| {
            called = true;
        });
        assert_eq!(called, should_call);
    }

    #[rstest]
    #[case(Left(()), false)]
    #[case(Right(()), true)]
    #[case(Both((), ()), true)]
    fn test_inspect_right(#[case] either: Either<(), ()>, #[case] should_call: bool) {
        let mut called = false;
        either.inspect_right(|_| {
            called = true;
        });
        assert_eq!(called, should_call);
    }

    #[rstest]
    #[case(Left(()), false)]
    #[case(Right(()), true)]
    #[case(Both((), ()), false)]
    fn test_inspect_only_right(#[case] either: Either<(), ()>, #[case] should_call: bool) {
        let mut called = false;
        either.inspect_only_right(|_| {
            called = true;
        });
        assert_eq!(called, should_call);
    }

    #[rstest]
    #[case(Left(()), false)]
    #[case(Right(()), false)]
    #[case(Both((), ()), true)]
    fn test_inspect_both(#[case] either: Either<(), ()>, #[case] should_call: bool) {
        let mut called = false;
        either.inspect_both(|_, _| {
            called = true;
        });
        assert_eq!(called, should_call);
    }
}
