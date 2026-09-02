use crate::clone::TrivialClone;
use crate::ptr;

pub(super) trait SpecFill<T> {
    fn spec_fill(&mut self, value: T);
}

impl<T: Clone> SpecFill<T> for [T] {
    default fn spec_fill(&mut self, value: T) {
        if let Some((last, elems)) = self.split_last_mut() {
            for el in elems {
                el.clone_from(&value);
            }

            *last = value
        }
    }
}

impl<T: TrivialClone> SpecFill<T> for [T] {
    default fn spec_fill(&mut self, value: T) {
        for item in self.iter_mut() {
            // SAFETY: `TrivialClone` indicates that this is equivalent to
            // calling `Clone::clone`
            *item = unsafe { ptr::read(&value) };
        }
    }
}

impl<T: TrivialClone + SpecFillElem> SpecFill<T> for [T] {
    fn spec_fill(&mut self, value: T) {
        T::fill_slice(self, value);
    }
}

/// Carries the integer fill bodies, so that `SpecFill` can specialize on a
/// trait bound rather than on concrete element types.
#[rustc_specialization_trait]
trait SpecFillElem: Sized {
    fn fill_slice(slice: &mut [Self], value: Self);
}

impl SpecFillElem for u8 {
    fn fill_slice(slice: &mut [Self], value: Self) {
        // SAFETY: The pointer is derived from a reference, so it's writable.
        unsafe {
            crate::intrinsics::write_bytes(slice.as_mut_ptr(), value, slice.len());
        }
    }
}

impl SpecFillElem for i8 {
    fn fill_slice(slice: &mut [Self], value: Self) {
        // SAFETY: The pointer is derived from a reference, so it's writable.
        unsafe {
            crate::intrinsics::write_bytes(slice.as_mut_ptr(), value.cast_unsigned(), slice.len());
        }
    }
}

macro spec_fill_int {
    ($($type:ty)*) => {$(
        impl SpecFillElem for $type {
            #[inline]
            fn fill_slice(slice: &mut [Self], value: Self) {
                // We always take this fastpath in Miri for long slices as the manual `for`
                // loop can be prohibitively slow.
                if (cfg!(miri) && slice.len() > 32) || crate::intrinsics::is_val_statically_known(value) {
                    let bytes = value.to_ne_bytes();
                    if value == <$type>::from_ne_bytes([bytes[0]; size_of::<$type>()]) {
                        // SAFETY: The pointer is derived from a reference, so it's writable.
                        unsafe {
                            crate::intrinsics::write_bytes(slice.as_mut_ptr(), bytes[0], slice.len());
                        }
                        return;
                    }
                }
                for item in slice.iter_mut() {
                    *item = value;
                }
            }
        }
    )*}
}

spec_fill_int! { u16 i16 u32 i32 u64 i64 u128 i128 usize isize }
