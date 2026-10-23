//@ edition: 2024
//@ check-pass

// Reduced from hashbrown-0.17.1 `RawTableInner::resize_inner`. The opaque's only declared
// outlives bound is `'a`, but in edition 2024 it also captures the anonymous `&self` lifetime,
// and nothing relates that lifetime to `'a`.
//
// So the captured `&self` lifetime is not one the underlying type could hold, and is not live:
// the immutable borrow of `*self` ends at the call, and `self.items` can be assigned while the
// returned guard is still alive. Keeping it live instead makes this fail to borrow-check, which
// is how it was caught -- it is what `std` does, and it stopped `core` from building.

#![forbid(unsafe_code)]

struct Guard<T, F> {
    val: T,
    f: F,
}

struct Table {
    items: usize,
}

impl Table {
    fn prepare<'a, A>(&self, alloc: &'a A) -> Guard<usize, impl FnMut(&mut usize) + 'a> {
        let _ = alloc;
        Guard { val: self.items, f: |_: &mut usize| {} }
    }

    fn resize<A>(&mut self, alloc: &A) {
        let mut g = self.prepare(alloc);
        self.items += 1;
        g.val += 1;
        (g.f)(&mut g.val);
    }
}

fn main() {}
