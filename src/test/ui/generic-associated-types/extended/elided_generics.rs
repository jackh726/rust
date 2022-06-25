// revisions: base extended
//[base] check-fail
//[extended] check-pass

#![feature(generic_associated_types)]
#![cfg_attr(extended, feature(generic_associated_types_extended))]
#![cfg_attr(extended, allow(incomplete_features))]

trait LendingIterator {
    type Item<'a>;
}

fn foo<T: LendingIterator>(_t: T::Item) {}
//[base]~^ missing generics

fn main() {}
