fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 1];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    // Make sure there is only one possible way to hit the panic.
    if data[0] >= 127 { return }

    let mut v: Vec<u16> = Vec::new();
    for idx in 0..128 { // going up to 256 takes too long
        v.push(idx);
    }

    if v[(data[0] & 0x7f) as usize] == 73 {
        panic!()
    }
}
