use super::Vec;
use crate::alloc::Allocator;

// Specialization trait used for Vec::extend
pub(super) trait SpecExtend<T, I> {
    fn spec_extend(&mut self, iter: I);
}

impl<T, I, A: Allocator> SpecExtend<T, I> for Vec<T, A>
where
    I: Iterator<Item = T>,
{
    fn spec_extend(&mut self, iter: I) {
        self.extend_desugared(iter)
    }
}

impl<'a, T: 'a, I, A: Allocator> SpecExtend<&'a T, I> for Vec<T, A>
where
    I: Iterator<Item = &'a T>,
    T: Clone,
{
    fn spec_extend(&mut self, iterator: I) {
        self.spec_extend(iterator.cloned())
    }
}
