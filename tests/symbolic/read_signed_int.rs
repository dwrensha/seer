fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 1];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    if ((data[0] as i8) >> 1) == -64i8 { // data[0] = 0x80
        panic!()
    }
}
