#![no_std]
#![forbid(unsafe_code)]

pub struct Token {
    pub word: u16,
}

pub struct Rows {
    pub values: [[Token; 2]; 2],
}

#[inline(never)]
pub fn unpack(values: [Token; 2]) -> (Token, Token) {
    let [left, right] = values;
    (left, right)
}

#[inline(never)]
pub fn unpack_rows(rows: Rows) -> (Token, Token, Token, Token) {
    let Rows {
        values: [[a, b], [c, d]],
    } = rows;
    (a, b, c, d)
}

pub fn array_claim(a: u16, b: u16) {
    let (left, right) = unpack([Token { word: a }, Token { word: b }]);
    assert!(left.word == a && right.word == b);
}

pub fn array_wrong(a: u16, b: u16) {
    let (left, right) = unpack([Token { word: a }, Token { word: b }]);
    assert!(left.word == (a ^ 1) && right.word == b);
}

pub fn nested_claim(a: u16, b: u16, c: u16, d: u16) {
    let (x, y, z, w) = unpack_rows(Rows {
        values: [
            [Token { word: a }, Token { word: b }],
            [Token { word: c }, Token { word: d }],
        ],
    });
    assert!(x.word == a && y.word == b && z.word == c && w.word == d);
}

pub fn nested_wrong(a: u16, b: u16, c: u16, d: u16) {
    let (x, y, z, w) = unpack_rows(Rows {
        values: [
            [Token { word: a }, Token { word: b }],
            [Token { word: c }, Token { word: d }],
        ],
    });
    assert!(x.word == a && y.word == b && z.word == c && w.word == (d ^ 1));
}

// A whole covering assignment after destructuring is ordinary safe Rust. This repairs the whole
// array, rather than pretending indexed repair of a partially moved array is Rust-legal.
pub fn covering_array_repair(a: u16, b: u16, next: u16) {
    let mut values = [Token { word: a }, Token { word: b }];
    let [left, right] = values;
    assert!(left.word == a && right.word == b);
    values = [Token { word: next }, Token { word: next }];
    let [left, right] = values;
    assert!(left.word == next && right.word == next);
}

#[cfg(test)]
mod native {
    #[test]
    fn array() {
        super::array_claim(9, 17);
    }
    #[test]
    fn nested() {
        super::nested_claim(9, 17, 23, 29);
    }
    #[test]
    fn repair() {
        super::covering_array_repair(9, 17, 23);
    }
    #[test]
    fn array_wrong() {
        super::array_wrong(9, 17);
    }
    #[test]
    fn nested_wrong() {
        super::nested_wrong(9, 17, 23, 29);
    }
}
