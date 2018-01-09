// https://github.com/rust-lang/rust/issues/47253

#![feature(generators)]

pub struct Foo {
    _a: bool,
    _b: Option<String>,
}

fn main() {
    let g = ||  {
        let _f = Foo { _a: true, _b: None };
        yield ();
    };
    match Some(g) {
        None => (),
        Some(_) => (),
    }
}
