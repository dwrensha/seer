extern crate wtf8;

pub fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 10];
    let mut stdin = ::std::io::stdin();
    stdin.read_exact(&mut data[..]).unwrap();

    let mut u16data: Vec<u16> = Vec::new();
    for idx in 0 .. (data.len() / 2) {
        u16data.push(data[2 * idx] as u16 | ((data[2 * idx + 1] as u16) << 8));
    }
    let wtf8buf = wtf8::Wtf8Buf::from_ill_formed_utf16(&u16data);

    let mut result: Vec<u16> = Vec::new();
    for c in wtf8buf.to_ill_formed_utf16() {
        result.push(c);
    }
    assert_eq!(result, u16data);
}
