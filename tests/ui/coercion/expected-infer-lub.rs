//@ check-pass
// This tests that the type of the expression returened by a LUBed expression ends
// up being coercible from the `LUB` type. Here, the LUB type should be `*const ()`,
// and inferred type of `_a` should *also* be `*const ()` - but naively if we
// set the expected type *too early*, then we would end up setting it to `*mut ()`
// (since that's the type of the first arm) and then the LUB type would not coerce.

fn example() {
    let a: *mut () = loop {};
    let b: *const () = loop {};
    let _a = if true {
        a
    } else {
        b
    };
    ()
}

fn main() {}
