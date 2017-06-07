fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 5];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    data.sort();

    let mut floor = 0;
    for d in data {
        if d < floor {
            panic!()
        }
        floor = d;
    }
}
