// An opaque type has a single hidden type, and we only keep a single hidden
// primary hidden type and each new defining use replaces the previous one.
// In the next solver, the goals equating the previous hidden type with the new
// one used `Locations::Single`, which meant that the outlives relationship
// wasn't propogated properly.

// We now equate all hidden types in borrowck with `Locations::All`, which
// ensures that the outlives relationship is propogated to all defining uses.

//@ ignore-compare-mode-polonius (explicit revisions)
//@ ignore-compare-mode-next-solver (explicit revisions)
//@ revisions: nll polonius legacy next
//@ [nll] compile-flags: -Z polonius=off
//@ [polonius] compile-flags: -Z polonius=next
//@ [legacy] compile-flags: -Z polonius=legacy
//@ [next] compile-flags: -Z next-solver -Z polonius=next

use std::fmt::Display;

fn two_uses<'a>(s: &'a String, flag: bool) -> impl Display + use<'a> {
    if flag {
        let local = String::from("dangling");
        return &local; //~ ERROR `local` does not live long enough
    }
    s
}

// Although similar to the previous, this function correctly failed to compile
// because the issues was rooted in *MIR* order, not source order: the second
// branch ended up being after the final statement, resulting in a correct
// `Locations::All`.
fn three_uses<'a>(s: &'a String, flag: u8) -> impl Display + use<'a> {
    if flag == 0 {
        let local = String::from("dangling0");
        return &local; //~ ERROR `local` does not live long enough
    }
    if flag == 1 {
        let local = String::from("dangling1");
        return &local; //~ ERROR `local` does not live long enough
    }
    s
}


// Similar to `two_uses`, but checks the opposite MIR order.
fn reversed_order<'a>(s: &'a String, flag: bool) -> impl Display + use<'a> {
    if flag {
        return s;
    }
    let local = String::from("dangling");
    &local //~ ERROR `local` does not live long enough
}

fn main() {}
