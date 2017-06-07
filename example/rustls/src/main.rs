extern crate rustls;

use rustls::{ClientConfig, ClientSession, Session};
use std::io;
use std::sync::Arc;

fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 12];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    let data = &data[..];

    let config = Arc::new(ClientConfig::new());
    let mut client = ClientSession::new(&config, "example.com");
    let _ = client.read_tls(&mut io::Cursor::new(data));
}
