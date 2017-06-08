extern crate brotli;

pub fn main() {
    use std::io::{Cursor, Read};
    let mut data: Vec<u8> = vec![0; 64];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();
    let data = &data[..];

    let mut data_reader = Cursor::new(data);
    let mut result = Vec::with_capacity(data.len());

    let mut de = brotli::Decompressor::new(&mut data_reader, data.len());

    let _ = de.read_exact(&mut result);
}
