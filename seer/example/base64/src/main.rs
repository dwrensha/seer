extern crate base64;

fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 12];
    let mut stdin = ::std::io::stdin();
    stdin.read_exact(&mut data[..]).unwrap();

    let data_copy = data.clone();

    let encoded = ::base64::encode(&data[..]);
    if encoded.starts_with("dGhpcyBpcy") {
        panic!()
    }

/*
    match ::base64::decode(encoded.as_bytes()) {
        Ok(v) => {
            if &v[..] != &data_copy[..] {
                panic!()
            }
        }
        Err(e) => {
            panic!()
        }
    }
*/
}
