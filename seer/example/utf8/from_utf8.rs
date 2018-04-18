fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 8];
    let mut stdin = ::std::io::stdin();
    stdin.read_exact(&mut data[..]).unwrap();

    match ::std::str::from_utf8(&data) {
        Ok(s) => {
            assert_eq!(s.as_bytes(), &data[..]);
        }
        Err(_) => (),
    }
}
