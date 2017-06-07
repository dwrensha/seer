extern crate capnp;

use capnp::{serialize, message};

fn try_go(mut data: &[u8]) -> ::capnp::Result<()> {
    let orig_data = data;
    let message = try!(serialize::read_message(&mut data, Default::default()));
    assert!(orig_data.len() > data.len());
    let bytes_consumed = orig_data.len() - data.len();
    let maybe_is_canonical = message.is_canonical();
    let canonical_words = try!(message.canonicalize());

    if let Ok(true) = maybe_is_canonical {
        assert_eq!(&orig_data[8..bytes_consumed], ::capnp::Word::words_to_bytes(&canonical_words[..]));
    }

    let segments = &[&canonical_words[..]];
    let segment_array = message::SegmentArray::new(segments);
    let canonical_message = message::Reader::new(segment_array, Default::default());
    assert!(try!(canonical_message.is_canonical()));

    let canonical2_words = try!(canonical_message.canonicalize());
    assert_eq!(canonical_words, canonical2_words);
    Ok(())
}

pub fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 32];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    let _ = try_go(&data[..]);
}
