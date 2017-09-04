fn main() {
    use std::io::Read;
    let mut data = [0; 1];
    let mut stdin = ::std::io::stdin();
    stdin.read_exact(&mut data[..]).unwrap();

    let buf = [17; 255];

    let slice = &buf[0..(data[0] as usize)];

    if slice.len() == 35 {
        panic!()
    }
}
