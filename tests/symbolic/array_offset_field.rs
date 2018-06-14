#[repr(C)]
struct Foo {
    pub a: u16,
    pub b: u8,
    pub c: u8,
}

impl Foo {
    pub fn new(x: u8) -> Self {
        Foo { a: x as u16, b: x, c: x }
    }
}

fn main() {
    use std::io::Read;
    let mut data = [0; 2];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    let v: &[Foo] = &[Foo::new(0),
                      Foo::new(1),
                      Foo::new(2),
                      Foo::new(3),
                      Foo::new(4),
                      Foo::new(5),
                      Foo::new(6),
                      Foo::new(7),
                      Foo::new(8),
                      Foo::new(9)];

    let d0 = data[0]; // 1
    let d1 = data[1]; // 4

    if d0 as usize + d1 as usize >= v.len() {
        return;
    }

    if v[d0 as usize].a == 1 {
        if v[d0 as usize + d1 as usize].b == 5 {
            panic!()
        }
    }
}
