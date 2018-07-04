extern crate capnp;

use capnp::{serialize, message};
use test_capnp::test_all_types;

pub mod test_capnp;

fn traverse(v: test_all_types::Reader) -> ::capnp::Result<()> {
    v.get_int64_field();
    try!(v.get_enum_field());
    try!(v.get_data_field());
    try!(v.get_struct_field());

    let structs = try!(v.get_struct_list());
    for s in structs.iter() {
        try!(s.get_struct_field());
    }

    try!(v.get_void_list());

    let bl = try!(v.get_bool_list());
    for idx in 0..bl.len() {
        bl.get(idx);
    }

    let el = try!(v.get_enum_list());
    for idx in 0..el.len() {
        try!(el.get(idx));
    }

    let dl = try!(v.get_data_list());
    for idx in 0..dl.len() {
        try!(dl.get(idx));
    }

    try!(v.get_text_list());
    Ok(())
}

fn try_go(mut data: &[u8]) -> ::capnp::Result<()> {
    let orig_data = data;
    let message_reader = try!(serialize::read_message(
        &mut data,
        *message::ReaderOptions::new().traversal_limit_in_words(10)));
    assert!(orig_data.len() > data.len());

    let root: test_all_types::Reader = try!(message_reader.get_root());
    try!(root.total_size());
    try!(traverse(root));

/*
    let mut message = message::Builder::new_default();
    try!(message.set_root(root));
    {
        let root_builder = try!(message.get_root::<test_all_types::Builder>());
        try!(root_builder.total_size());
        try!(traverse(root_builder.as_reader()));
    }

    // init_root() will zero the previous value
    let mut new_root = message.init_root::<test_all_types::Builder>();

    try!(new_root.set_struct_field(root)); */
    Ok(())
}

pub fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 32];

    // Set the size of the message to a concrete value because seer does
    // not yet support allocation of abstract size.
    data[0] = 0;
    data[1] = 0;
    data[2] = 0;
    data[3] = 0;
    data[4] = ((data.len() / 8) - 1) as u8;
    data[5] = 0;
    data[6] = 0;
    data[7] = 0;

    let mut stdin = ::std::io::stdin();
    stdin.read_exact(&mut data[8..]).unwrap();

    let _ = try_go(&data[..]);
}
