pub fn main() {
    use std::io::Read;

    let mut data = [0; 16];
    let mut stdin = ::std::io::stdin();
    stdin.read_exact(&mut data[..]).unwrap();

    if &data[0..4] == &[10, 11, 12, 13] {
        if &[21, 22, 23, 24] == &data[4..8] {
            if &data[0..8] == &data[8..16] {
                panic!()
            }
        }
    }
}
