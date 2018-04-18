fn main() {
    use std::io::Read;
    let mut data = [0; 2];
    let mut stdin = ::std::io::stdin();
    stdin.read_exact(&mut data[..]).unwrap();

    let b0 = data[0] == 18;
    if b0 as i8 == 1 {
        let b1 = data[1] != 102;
        if b1 as i8 == 0 {
            panic!()
        }
    }
}
