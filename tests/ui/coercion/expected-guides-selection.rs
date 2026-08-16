//@ check-pass
//@ edition: 2021
// This tests that the expected type for a LUB coercion can be used to guide
// trait selection within the expression itself.
use std::convert::TryFrom;

struct Simd<T>([T; 0]);

impl<T> TryFrom<&[T]> for Simd<T> {
    type Error = std::array::TryFromSliceError;

    #[inline]
    fn try_from(slice: &[T]) -> Result<Self, Self::Error> {
        // We need `[T; 0]` to guide what type `slice` is converted to.
        let _: &[T; 0] = match slice.try_into() {
            Result::Err(e) => return Result::Err(e),
            Result::Ok(val) => val,
        };
        loop {}
    }
}

fn main() {}
