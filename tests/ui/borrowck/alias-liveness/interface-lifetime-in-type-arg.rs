//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// Same hole as #160979, but the observable lifetime is hidden inside a *type*
// argument of the interface bound rather than appearing as a lifetime argument.
// Accepted by `-Zpolonius=next` before the fix, rejected by NLL.
//
// This is why the rule has to talk about generic *args* of the alias rather than
// just the lifetimes syntactically in its bounds.

struct Lifetimed<'a>(&'a ());
static LIFETIMED: Lifetimed<'static> = Lifetimed(&());

trait Produce<T> {
    fn produce(&self) -> T;
}
struct P;
impl<'a> Produce<&'a Lifetimed<'a>> for P {
    fn produce(&self) -> &'a Lifetimed<'a> {
        &LIFETIMED
    }
}

fn make<T>(_t: T) -> impl Produce<T> + 'static + use<T>
where
    P: Produce<T>,
{
    P
}

fn leak_it<T: 'static>(val: T) -> &'static T {
    Box::leak(Box::new(val))
}

fn main() {
    let p;
    {
        let local = Lifetimed(&());
        let r: &Lifetimed<'_> = &local; //~ ERROR `local` does not live long enough
        p = make(r);
    }
    let v = p.produce();
    let _leaked = leak_it(v);
}
