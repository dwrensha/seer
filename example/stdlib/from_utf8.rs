fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 8];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    let _ = ::std::str::from_utf8(&data);
}
