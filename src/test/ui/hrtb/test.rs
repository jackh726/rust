// check-pass
// compile-flags: -Z verbose

trait Callback<T>: Fn(&T) {}

struct Bar<T> {
    callback: Box<dyn Callback<T>>,
}

fn main() {}
