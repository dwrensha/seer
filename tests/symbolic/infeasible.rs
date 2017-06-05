use std::io::Read;

fn main() {
    let mut data: Vec<u8> = vec![0; 1];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    if data[0] == 27 {
        if data[0] == 129 {
            panic!()
        }
    }
}
