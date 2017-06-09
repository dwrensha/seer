extern crate fuzzy_pickles;

pub fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 15];
    let mut stdin = ::std::io::stdin();
    stdin.read_exact(&mut data[..]).unwrap();

    for idx in 0..data.len() {
        if data[idx] > 127 {
            return; // avoid invalid utf8 by exiting early
        }
    }

    let mut buf = String::new();
    {
        let mut buf_bytes = unsafe { buf.as_mut_vec() };
        for idx in 0..data.len() {
            buf_bytes.push(data[idx]);
        }
    }


    let _ = ::fuzzy_pickles::parse_rust_file(&buf);
}
