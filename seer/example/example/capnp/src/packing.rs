extern crate capnp;

use capnp::{message, serialize_packed};

fn try_go(mut data: &[u8]) -> ::capnp::Result<()> {
    let orig_data = data;
    let _message_reader = try!(serialize_packed::read_message(
        &mut data,
        *message::ReaderOptions::new().traversal_limit_in_words(10)));
    assert!(orig_data.len() > data.len());

    Ok(())
}

pub fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 64];

    // packed stream header
    data[0] = 16; // tag
    data[1] = 4;  // number of words in main message body

    let mut stdin = ::std::io::stdin();
    stdin.read_exact(&mut data[2..]).unwrap();

    let _ = try_go(&data[..]);
}
