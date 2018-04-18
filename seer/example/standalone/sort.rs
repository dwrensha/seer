fn main() {
    use std::io::{stdin, Read};
    let mut data = [0; 5];
    stdin().read_exact(&mut data[..]).unwrap();

    data.sort();

    let mut floor = 0;
    for &d in data.iter() {
        if d < floor {
            panic!()
        }
        floor = d;
    }
}
