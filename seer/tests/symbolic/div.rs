fn main() {
    use std::io::Read;
    let mut data = [0; 2];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    let d0 = data[0]; // 57

    if d0 / 3 == 19 && d0 % 3 == 0 {

        let d1 = data[1] as i8; // 199 (== -57)
        if d1 / 4 == -14 && d1 % 4 == -1 {
            panic!()
        }
    }
}
