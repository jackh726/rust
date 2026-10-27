//@ edition: 2024
//@ check-pass

// Minimized from ty_python_semantic::Binding::enumerate_argument_types
// regression in #161154.

#![forbid(unsafe_code)]
#![allow(dead_code)]

struct Types<'db>(&'db u8);
#[derive(Clone, Copy)]
struct Argument<'a>(&'a u8);
struct Inner<'a, 'db> {
    items: Vec<(Argument<'a>, Types<'db>)>,
}
impl<'a, 'db> Inner<'a, 'db> {
    fn iter(&self) -> impl Iterator<Item = (Argument<'a>, &Types<'db>)> + '_ {
        self.items.iter().map(|(arg, types)| (*arg, types))
    }
}
struct Outer<'a, 'db> {
    inner: &'a Inner<'a, 'db>,
}
impl<'a, 'db> Outer<'a, 'db> {
    fn iter(&self) -> impl Iterator<Item = (Argument<'a>, &Types<'db>)> + 'a {
        self.inner.iter().map(|(arg, types)| (arg, types))
    }
    fn iter_explicit(&self) -> impl Iterator<Item = (Argument<'a>, &'a Types<'db>)> + 'a {
        self.inner.iter().map(|(arg, types)| (arg, types))
    }
    fn update(&mut self) {}
    fn check(&mut self) {
        for _ in self.iter() {
            self.update()
        }
    }
    fn check_explicit(&mut self) {
        for _ in self.iter_explicit() {
            self.update()
        }
    }
}

fn main() {}
