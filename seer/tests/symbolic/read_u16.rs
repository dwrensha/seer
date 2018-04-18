fn main() {
    use std::io::Read;
    let mut data = [0; 2];
    let mut stdin = ::std::io::stdin();
    stdin.read_exact(&mut data[..]).unwrap();

    let two_bytes = (data[0] as u16) + ((data[1] as u16) << 8);

    if two_bytes == 0xffeeu16 && two_bytes.swap_bytes() == 0xeeffu16 {
        if two_bytes << 4u8 == 0xfee0 {
            panic!()
        }
    }
}
