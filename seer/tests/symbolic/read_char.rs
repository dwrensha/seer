fn main() {
    use std::io::Read;
    let mut data = [0; 2];
    let mut stdin = ::std::io::stdin();
    stdin.read_exact(&mut data[..]).unwrap();

    let two_bytes = (data[0] as u16) + ((data[1] as u16) << 8);

    if two_bytes > 0xd7ff {
        return; // avoid surrogate code points
    }

    let c = ::std::char::from_u32(two_bytes as u32).unwrap();

    let smiley = '☺';
    assert_eq!(smiley as u32, 0x263a);

    if c == smiley {
        panic!()
    }
}
