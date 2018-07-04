use std::io::Read;

fn main() {
    let mut data = [0];
    let mut stdin = ::std::io::stdin();
    stdin.read_exact(&mut data[..]).unwrap();

    if data[0] == 43 {
        panic!()
    }
}
