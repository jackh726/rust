// `Captures<'a> + 'static` no longer compiles: an alias's outlives bound describes
// its hidden type, but `Captures<'a>` in the bounds is still an *interface*, and a
// lifetime in the interface can always be resurrected — see
// `interface-marker-trait-{uaf,blanket,dyn}.rs`. The replacement spelling is
// `+ 'static + use<'a>`, which says "captured, not part of the interface" and keeps
// the old behaviour (`interface-use-bound-migration.rs`).
trait Captures<'a> {}
impl<T> Captures<'_> for T {}

trait Outlives<'a>: 'a {}
impl<'a, T: 'a> Outlives<'a> for T {}

// Test that we treat `for<'a> Opaque: 'a` as `Opaque: 'static`
fn test<'o>(v: &'o Vec<i32>) -> impl Captures<'o> + for<'a> Outlives<'a> {}

fn opaque_doesnt_use_temporary() {
    let a = test(&vec![]);
    //~^ ERROR temporary value dropped while borrowed
}

fn main() {}
