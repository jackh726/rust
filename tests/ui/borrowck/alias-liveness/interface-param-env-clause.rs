//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius] compile-flags: -Zpolonius=next
//@ edition: 2024

// The pruning does not have to come from the alias's own bounds: a *caller's*
// where-clause prunes through `live_args_for_outlives_clause` just as well. Accepted
// by `-Zpolonius=next` before the fix, rejected by NLL.
//
// This is why the interface args have to be unioned in *after* the param-env
// intersection, and why a declaration-site check could never be sufficient on its
// own — `for<'r> <G as Producer<'r>>::Ty: 'static` is not a declaration of `Ty`.
trait Producer<'r> {
    type Ty: Into<&'r str>;
    fn construct(r: &'r str) -> Self::Ty;
}

fn example<G>(hold: &mut Option<<G as Producer<'_>>::Ty>)
where
    G: for<'r> Producer<'r>,
    for<'r> <G as Producer<'r>>::Ty: 'static,
{
    let out;
    {
        let s = String::from("huh");
        let r: &str = &s; //~ ERROR `s` does not live long enough
        let v = G::construct(r);
        *hold = Some(v);
    }
    let _unrelated = String::from("UB!");
    out = hold.take().unwrap().into();
    println!("{}", out);
}

fn main() {}
