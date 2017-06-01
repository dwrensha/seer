fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 4];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    let four_bytes =
        (data[0] as u32) +
        ((data[1] as u32) << 8) +
        ((data[2] as u32) << 16) +
        ((data[3] as u32) << 24);

    if four_bytes == 0x44332211u32 && four_bytes.swap_bytes() == 0x11223344u32 {
        panic!()
    }
}
