#[repr(C)]
pub enum Foo {
    A, B, C, D
}

fn main() {
    let f = unsafe { std::mem::transmute::<i32, Foo>(42) };
    match f {  //~ ERROR invalid enum discriminant value read
        Foo::A => {},
        Foo::B => {},
        Foo::C => {},
        Foo::D => {},
    }
}
