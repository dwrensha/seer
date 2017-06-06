fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 2];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    let b = data[0] != 0;
    let bp = &b;
    if !*bp {
        let b1 = data[1] == 63;
        let bp1 = &b1;
        if *bp1 {
            panic!()
        }
    }
}
