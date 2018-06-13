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
                      Foo::new(9),
                      Foo::new(10)];

    let mut p = v.as_ptr();

    let d0 = data[0]; // 3
    let d1 = data[1]; // 5

    if (d0.wrapping_add(d1)) as usize >= v.len() {
        return;
    }

    p = unsafe { p.offset(d0 as isize) };

    let q = unsafe { p.offset(d1 as isize) };

    if unsafe { (*p).a } == 3 {
        if unsafe { (*q).b } == 8 {
            panic!()
        }
    }
}
