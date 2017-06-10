fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 2];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    // Make sure there is only one possible way to hit the panic.
    if data[0] >= 127 { return }

    let mut v: Vec<u16> = Vec::new();
    for idx in 0..128 { // going up to 256 takes too long
        v.push(idx);
    }

    if v[(data[0] & 0x7f) as usize] != 73 { return; }

    let mut w: Vec<u16> = vec![0; 256];
    w[data[1] as usize] = 0xabcd;

    if w[158] != 0xabcd { return; }

    panic!()
}
