extern crate httparse;

fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 40];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    //let data = b"GET /index.html HTTP/1.1\r\nHost: example.domain\r\n\r\n";
    //println!("data.len = {}", data.len()); // = 50

    let mut headers = [httparse::EMPTY_HEADER; 16];
    {
        let mut req = httparse::Request::new(&mut headers);
        match req.parse(&data[..]) {
            Ok(n) => {
                if n.is_complete() {

                } else {

                }
            }
            Err(_) => {}
        }
    }
    if headers[0].name == "Host" {
        panic!()
    }
}
