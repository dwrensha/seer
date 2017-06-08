#[derive(Copy, Clone)]
struct Foo {
    _a: u32,
    _b: bool,
    c: u64,
    _d: u8,
}

fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 2];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    let mut v: Vec<Foo> = vec![Foo {_a: 0, _b: false, c: 0, _d: 0,}; 20];

    let d0 = data[0] as usize; // 5
    let d1 = data[1] as usize; // 5

    if d0 >= v.len() {
        return;
    }

    if d1 >= v.len() {
        return;
    }

    {
        let x: &mut u64 = &mut v[d0].c;
        *x = 222;
    }

    if v[d0].c == v[d1].c {
        if d0 == 5 {
            panic!()
        }
    }
}
