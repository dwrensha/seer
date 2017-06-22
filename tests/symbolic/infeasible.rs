use std::io::Read;

fn main() {
    let mut data = [0];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    if data[0] == 27 {
        if data[0] == 129 {
            panic!()
        }
    }
}
