use super::*;
use either::Either as Other;
impl<L, R> From<Other<L, R>> for Either<L, R> {
    /// Converts the `Either` variant from the `either` crate to this crate's `Either`.
    /// This will either produce the variant `Left` or `Right`, but never `Both`.
    ///
    /// # Example
    ///
    /// ```rust
    /// let left: either::Either<_, ()> = either::Left(());
    /// let right: either::Either<(), _> = either::Right(());
    /// assert!(matches!(left.into(), either_both::Left(_)));
    /// assert!(matches!(right.into(), either_both::Right(_)));
    /// ```
    fn from(value: Other<L, R>) -> Self {
        match value {
            Other::Left(l) => Self::Left(l),
            Other::Right(r) => Self::Right(r),
        }
    }
}

impl<L, R> From<Other<Other<L, R>, (L, R)>> for Either<L, R> {
    fn from(value: Other<Other<L, R>, (L, R)>) -> Self {
        match value {
            Other::Left(Other::Left(l)) => Self::Left(l),
            Other::Left(Other::Right(r)) => Self::Right(r),
            Other::Right((l, r)) => Self::Both(l, r),
        }
    }
}

impl<L, R> From<Other<(L, R), Other<L, R>>> for Either<L, R> {
    fn from(value: Other<(L, R), Other<L, R>>) -> Self {
        match value {
            Other::Left((l, r)) => Self::Both(l, r),
            Other::Right(Other::Left(l)) => Self::Left(l),
            Other::Right(Other::Right(r)) => Self::Right(r),
        }
    }
}

impl<L, R> From<Either<L, R>> for Other<Other<L, R>, (L, R)> {
    fn from(value: Either<L, R>) -> Self {
        match value {
            Either::Left(l) => Self::Left(Other::Left(l)),
            Either::Right(r) => Self::Left(Other::Right(r)),
            Either::Both(l, r) => Self::Right((l, r)),
        }
    }
}

impl<L, R> From<Either<L, R>> for Other<(L, R), Other<L, R>> {
    fn from(value: Either<L, R>) -> Self {
        match value {
            Either::Left(l) => Self::Right(Other::Left(l)),
            Either::Right(r) => Self::Right(Other::Right(r)),
            Either::Both(l, r) => Self::Left((l, r)),
        }
    }
}
