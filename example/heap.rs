use std::collections::BinaryHeap;

fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 11];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    let mut heap = BinaryHeap::new();
    for d in data {
        heap.push(d);
    }


    let mut ceiling = 255;
    while let Some(d) = heap.pop() {
        if d > ceiling {
            panic!()
        }
        ceiling = d;
    }
}
