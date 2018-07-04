fn main() {
    use std::io::Read;
    let mut data = [0; 2];
    let mut stdin = ::std::io::stdin();
    stdin.read_exact(&mut data[..]).unwrap();

    // Make sure there is only one possible way to hit the panic.
    if data[0] >= 127 { return }

    let mut v = [0; 128];
    for idx in 0..128 { // going up to 256 takes too long
        v[idx as usize] = idx;
    }

    if v[(data[0] & 0x7f) as usize] != 73 { return; }

    let mut w = [0; 256];
    w[data[1] as usize] = 0xabcd;

    if w[158] != 0xabcd { return; }

    panic!()
}
