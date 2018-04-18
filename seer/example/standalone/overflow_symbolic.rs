fn main() {
    use std::io::{stdin, Read};
    let mut data = [0; 1];
    stdin().read_exact(&mut data[..]).unwrap();
    let i = data[0] as i8;
    let _overflowed: i8 = i - 1i8;
}
