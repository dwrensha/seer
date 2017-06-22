fn main() {
    use std::io::Read;
    let mut data = [0; 11];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

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

    if buf.starts_with("hello") {
        if buf.as_bytes()[5..].starts_with(b" world") {
            panic!()
        }
    }
}
