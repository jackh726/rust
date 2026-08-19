// `-Zpolonius=next` computes where a loan goes out of scope by scanning the loan's point set for
// the first point the loan is not live at. That set is a bitset, and the scan works a word at a
// time: it masks the word down to the points belonging to the block, and takes the lowest bit left.
//
// Getting that masking wrong moves the computed kill location. Too wide a mask kills the loan
// early and loses the error; too narrow a mask misses the kill and keeps the loan live past its
// scope. Neither shows up on a small body, because every point fits in the first word -- so these
// bodies are padded to push the loan and its uses across word boundaries, at a spread of offsets,
// so that some of them land on a boundary whatever the exact point numbering turns out to be.

//@ ignore-compare-mode-polonius (explicit revisions)
//@ revisions: nll polonius_next
//@ [nll] compile-flags: -Zpolonius=off
//@ [polonius_next] compile-flags: -Zpolonius=next

/// Emits one `let` per token, to pad a basic block with points.
macro_rules! pad {
    ($($n:tt)*) => { $( let _pad = $n; )* };
}

// The loan is issued after the padding, so its own point is in a high word: this is what the
// "the loan is always live where it is issued" special case has to keep working across words.
fn issued_in_a_later_word() {
    let mut v = 0u32;
    pad!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30);
    let r = &v;
    v += 1; //~ ERROR cannot assign to `v` because it is borrowed
    let _ = *r;
}

// The same, one point further along, so that if the above lands just short of a boundary this one
// lands just past it.
fn issued_in_a_later_word_plus_one() {
    let mut v = 0u32;
    pad!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31);
    let r = &v;
    v += 1; //~ ERROR cannot assign to `v` because it is borrowed
    let _ = *r;
}

fn issued_in_a_later_word_plus_two() {
    let mut v = 0u32;
    pad!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32);
    let r = &v;
    v += 1; //~ ERROR cannot assign to `v` because it is borrowed
    let _ = *r;
}

// Here the loan is issued in the first word and used in a later one, so the scan has to run over
// several words before finding the kill point.
fn live_across_words() {
    let mut v = 0u32;
    let r = &v;
    pad!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32);
    v += 1; //~ ERROR cannot assign to `v` because it is borrowed
    let _ = *r;
}

fn live_across_words_plus_one() {
    let mut v = 0u32;
    let r = &v;
    pad!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33);
    v += 1; //~ ERROR cannot assign to `v` because it is borrowed
    let _ = *r;
}

// The loan dies before the conflicting write, several words in: the error must *not* be reported.
// A mask that keeps the loan live past its last use would produce one here.
fn dead_before_the_write() {
    let mut v = 0u32;
    let r = &v;
    let _ = *r;
    pad!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32);
    v += 1;
}

fn dead_before_the_write_plus_one() {
    let mut v = 0u32;
    let r = &v;
    let _ = *r;
    pad!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33);
    v += 1;
}

// The kill point is in a *successor* block, so the walk has to carry the loan across the block
// boundary and mask the successor's own point range rather than the issuing block's.
fn killed_in_a_successor_block(cond: bool) {
    let mut v = 0u32;
    let r = &v;
    pad!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32);
    if cond {
        pad!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30);
        v += 1; //~ ERROR cannot assign to `v` because it is borrowed
    }
    let _ = *r;
}

fn main() {}
