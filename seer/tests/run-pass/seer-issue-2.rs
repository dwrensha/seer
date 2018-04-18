enum Token {
    _LeftAngle,
    _RightAngle
}

struct ParseMaster<P> {
    _failures: P,
}

struct Alternate<'pm, P: 'pm, T> {
    _master: &'pm mut ParseMaster<P>,
    _current: Option<Progress<P, T>>,
    _point: P,
}

struct TokenPoint<'a, T: 'a> {
    _offset: usize,
    _sub_offset: Option<u8>,
    _s: &'a [T],
}

impl <P> ParseMaster<P> {
    fn alternate<'pm, T>(&'pm mut self, pt: P) -> Alternate<'pm, P, T> {
        Alternate {
            _master: self,
            _current: None,
            _point: pt,
        }
    }
}

struct Progress<P, T> {
    _point: P,
    _status: Status<T>,
}

enum Status<T> {
    _Success(T),
    _Failure,
}

fn main() {
    let mut pm : ParseMaster<TokenPoint<Token>> = ParseMaster {
        _failures: TokenPoint {
            _offset: 0,
            _sub_offset: None,
            _s:&[],
        },
    };

    pm.alternate::<()>(TokenPoint {
        _offset: 0,
        _sub_offset: None,
        _s:&[],
    });

}
