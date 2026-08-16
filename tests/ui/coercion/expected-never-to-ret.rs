//@ check-pass
// This tests that the LUB type gets coerced into the expected type (in this case,
// the return type of the function).
#![feature(never_type)]

struct TryFromIntError;

impl From<!> for TryFromIntError {
    fn from(never: !) -> TryFromIntError {
        match never {}
    }
}

fn main() {}
