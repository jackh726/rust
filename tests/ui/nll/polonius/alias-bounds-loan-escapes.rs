// Multiple alias outlives bounds form a disjunction represented by a type test. A type test checks
// that the alias outlives a region, but does not create a localized edge for loan propagation.

//@ ignore-compare-mode-polonius (explicit revisions)
//@ edition: 2024
//@ revisions: nll polonius
//@ [nll] compile-flags: -Z polonius=off
//@ [polonius] compile-flags: -Z polonius=next
#![forbid(unsafe_code)]

fn require_static<T: 'static>(_: T) {}

// If there are two outlives bounds on an alias, then we can't simply register
// an outlives constraint. Instead, a `AnyBound` type test is registered. This
// test is a safe-code use-after-free if accepted.
mod observable_ub {
    use std::fmt::Debug;

    fn make<'a: 'b, 'b>(x: &'a u8) -> impl Debug + Copy + 'a + 'b {
        x
    }

    pub fn test() {
        let mut y = make::<'static, 'static>(&0);
        let escaped: Box<dyn Debug>;
        {
            let x = 42u8;
            y = make(&x);
            //~^ ERROR `x` does not live long enough
            escaped = Box::new(y);
        }
        println!("{escaped:?}");
    }
}

// A more minimal form of the above, but requires the alias to outlive `'static`
// rather than being used outside the inner block.
mod ordered_bounds {
    use super::require_static;

    fn make<'a: 'b, 'b>(x: &'a u8) -> impl Copy + 'a + 'b {
        x
    }

    pub fn test() {
        let mut y = make::<'static, 'static>(&0);
        {
            let x = 42u8;
            y = make(&x);
            //~^ ERROR `x` does not live long enough
            require_static(y);
        }
    }
}

// Here the alias bounds are unrelated, so the type-outlives relation necessarily uses a type test.
mod unrelated_bounds {
    use super::require_static;

    fn make<'a, 'b, 'c>(x: &'c u8) -> impl Copy + 'a + 'b
    where
        'c: 'a,
        'c: 'b,
    {
        x
    }

    pub fn test() {
        let mut y = make::<'static, 'static, 'static>(&0);
        {
            let x = 42u8;
            y = make(&x);
            //~^ ERROR `x` does not live long enough
            require_static(y);
        }
    }
}

// Any universal region has the same effect as `'static`.
mod universal_param {
    fn make<'a: 'b, 'b>(x: &'a u8) -> impl Copy + 'a + 'b {
        x
    }

    fn require<'p, T: 'p>(_: T) {}

    pub fn test<'p>(seed: &'p u8) {
        let mut y = make::<'p, 'p>(seed);
        {
            let x = 42u8;
            y = make(&x);
            //~^ ERROR `x` does not live long enough
            require::<'p, _>(y);
        }
    }
}

// The same behavior applies to projections, too.
mod projection {
    use super::require_static;

    pub trait Tr<'a: 'b, 'b> {
        type A: Copy + 'a + 'b;
        fn mk(x: &'a u8) -> Self::A;
    }

    pub fn test<T: for<'a, 'b> Tr<'a, 'b>>() {
        let mut y = <T as Tr<'static, 'static>>::mk(&0);
        {
            let x = 42u8;
            y = <T as Tr<'_, '_>>::mk(&x);
            //~^ ERROR `x` does not live long enough
            require_static(y);
        }
    }
}


// Control case with no type-outlives use. It has no type test; Alpha can accept after the old loan
// is dead even though NLL's location-insensitive constraints reject it.
mod no_bounds {
    fn make<'a: 'b, 'b>(x: &'a u8) -> impl Copy + 'a + 'b {
        x
    }

    pub fn test() {
        let mut y = make::<'static, 'static>(&0);
        {
            let x = 42u8;
            y = make(&x);
            //[nll]~^ ERROR `x` does not live long enough
        }
    }
}

fn main() {
    observable_ub::test();
}
