// Like `streaming_iterator.rs`, except only the trait/impl.

// run-pass

#![feature(generic_associated_types)]

trait StreamingIterator {
    type Item<'a>;
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}

impl<I: Iterator> StreamingIterator for I {
    type Item<'a> = <I as Iterator>::Item;
    fn next(&mut self) -> Option<<I as StreamingIterator>::Item<'_>> {
        Iterator::next(self)
    }
}

fn main() {}
