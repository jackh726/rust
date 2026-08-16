//@ check-pass
// This tests that the expected type for a LUB coercion can guide the coercion
// of individual coerce sites to `fn` types - and, importantly, that the all the
// closure inference is correct w.r.t. higher-ranked lifetimes.
use std::path::Path;


fn example() {
    let mounts: &[fn(&Path) -> &Path] = &[
        |p| p,
        |p| p,
    ];
}

fn main() {}
