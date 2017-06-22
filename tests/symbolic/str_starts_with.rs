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

    let buf = unsafe { ::std::str::from_utf8_unchecked(&data[..]) };

    if buf.starts_with("hello") {
        if buf.as_bytes()[5..].starts_with(b" world") {
            panic!()
        }
    }
}
