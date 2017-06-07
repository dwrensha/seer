fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 6];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    for idx in 0..data.len() {
        if data[idx] > 1 {
            return // force all values to be zero or one.
        }
    }

    let b0 = data[0] != 0; // 1
    let b1 = data[1] != 0; // 1

    if b0 & b1 {
        let b2 = data[2] != 0; // 0
        let b3 = data[3] != 0; // 0

        if !(b2 | b3) {

            let b4 = data[4] != 0; // 0
            let b5 = data[5] != 0; // 1

            if !b4 && (b4 ^ b5) {
                panic!()
            }
        }
    }
}
