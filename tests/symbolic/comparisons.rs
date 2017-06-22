fn main() {
    use std::io::Read;

    let mut data = [0; 5];
    let mut stdin = ::std::io::stdin();
    stdin.read_exact(&mut data[..]).unwrap();

    // should panic on [ 17, 18, 38, 37, 101 ];

    if data.len() >= 5 {
        if 16 < data[0] && data[0] < data[1] && data[1] <= 18 {
            if 39 > data[2] && data[2] > data[3] && data[3] >= 37 {
                let x = data[4];
                if x != 100 {
                    if !(x == 102) {
                        if x > 100 && x < 103 {
                            panic!()
                        }
                    }
                }
            }
        }
    }
}
