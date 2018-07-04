fn main() {
    use std::io::Read;
    let mut data = [0; 1];
    let mut stdin = ::std::io::stdin();
    stdin.read_exact(&mut data[..]).unwrap();

    let b0 = data[0];
    if b0.leading_zeros() == 7 {
        panic!()
    }
}
