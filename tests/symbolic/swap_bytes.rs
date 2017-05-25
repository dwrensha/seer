fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 2];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    let _two_bytes = (data[0] as u16) + ((data[1] as u16) << 8);
}
