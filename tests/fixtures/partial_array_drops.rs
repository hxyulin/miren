#![no_std]
#![forbid(unsafe_code)]
use core::cell::Cell;

struct Stamp<'a> {
    log: &'a Cell<u32>,
    digit: u32,
}
impl Drop for Stamp<'_> {
    fn drop(&mut self) {
        self.log
            .set(self.log.get().wrapping_mul(10).wrapping_add(self.digit));
    }
}
#[inline(never)]
fn partial(log: &Cell<u32>) {
    let values = [
        Stamp { log, digit: 1 },
        Stamp { log, digit: 2 },
        Stamp { log, digit: 3 },
    ];
    let [first, ..] = values;
    drop(first);
    assert!(log.get() == 1);
}
#[inline(never)]
fn nested(log: &Cell<u32>) {
    let values = [
        [Stamp { log, digit: 1 }, Stamp { log, digit: 2 }],
        [Stamp { log, digit: 3 }, Stamp { log, digit: 4 }],
    ];
    let [[first, ..], ..] = values;
    drop(first);
    assert!(log.get() == 1);
}
#[inline(never)]
fn covering(log: &Cell<u32>) {
    let mut values = [Stamp { log, digit: 1 }, Stamp { log, digit: 2 }];
    let [first, ..] = values;
    drop(first);
    values = [Stamp { log, digit: 3 }, Stamp { log, digit: 4 }];
    assert!(log.get() == 12);
    drop(values);
}
pub fn partial_claim() {
    let log = Cell::new(0);
    partial(&log);
    assert!(log.get() == 123);
}
pub fn partial_wrong() {
    let log = Cell::new(0);
    partial(&log);
    assert!(log.get() == 132);
}
pub fn nested_claim() {
    let log = Cell::new(0);
    nested(&log);
    assert!(log.get() == 1342);
}
pub fn covering_claim() {
    let log = Cell::new(0);
    covering(&log);
    assert!(log.get() == 1234);
}
pub fn iterator_claim() {
    let log = Cell::new(0);
    {
        let mut pending = [
            Stamp {
                log: &log,
                digit: 1,
            },
            Stamp {
                log: &log,
                digit: 2,
            },
            Stamp {
                log: &log,
                digit: 3,
            },
        ]
        .into_iter();
        drop(pending.next().unwrap());
        assert!(log.get() == 1);
    }
    assert!(log.get() == 123);
}
#[cfg(test)]
mod native {
    #[test]
    fn partial() {
        super::partial_claim();
    }
    #[test]
    fn nested() {
        super::nested_claim();
    }
    #[test]
    fn covering() {
        super::covering_claim();
    }
    #[test]
    fn iterator() {
        super::iterator_claim();
    }
    #[test]
    fn wrong() {
        super::partial_wrong();
    }
}

// Body-owned scalar product storage for original-type/namespace controls, not a Drop shortcut.
pub struct Plain {
    pub word: u16,
}
#[inline(never)]
pub fn owner_probe(values: [Plain; 2]) -> [Plain; 2] {
    values
}
pub fn zero_claim() {
    let log = Cell::new(0);
    let values: [Stamp<'_>; 0] = [];
    drop(values);
    assert!(log.get() == 0);
}

#[inline(never)]
fn symbolic_partial_trace(log: &Cell<u32>, a: u32, b: u32, c: u32) {
    let values = [
        Stamp { log, digit: a },
        Stamp { log, digit: b },
        Stamp { log, digit: c },
    ];
    let [first, ..] = values;
    drop(first);
    assert!(log.get() == a);
}
#[inline(never)]
fn symbolic_nested_trace(log: &Cell<u32>, a: u32, b: u32, c: u32, d: u32) {
    let values = [
        [Stamp { log, digit: a }, Stamp { log, digit: b }],
        [Stamp { log, digit: c }, Stamp { log, digit: d }],
    ];
    let [[first, ..], ..] = values;
    drop(first);
    assert!(log.get() == a);
}
#[inline(never)]
fn symbolic_covering_trace(log: &Cell<u32>, a: u32, b: u32, c: u32, d: u32) {
    let mut values = [Stamp { log, digit: a }, Stamp { log, digit: b }];
    let [first, ..] = values;
    drop(first);
    values = [Stamp { log, digit: c }, Stamp { log, digit: d }];
    assert!(log.get() == a.wrapping_mul(10).wrapping_add(b));
    drop(values);
}
fn append_digit(previous: u32, digit: u32) -> u32 {
    previous.wrapping_mul(10).wrapping_add(digit)
}
pub fn symbolic_partial(a: u32, b: u32, c: u32) {
    let log = Cell::new(0);
    symbolic_partial_trace(&log, a, b, c);
    assert!(log.get() == append_digit(append_digit(a, b), c));
}
pub fn symbolic_partial_wrong(a: u32, b: u32, c: u32) {
    let log = Cell::new(0);
    symbolic_partial_trace(&log, a, b, c);
    assert!(log.get() == append_digit(append_digit(a, c), b));
}
pub fn symbolic_nested(a: u32, b: u32, c: u32, d: u32) {
    let log = Cell::new(0);
    symbolic_nested_trace(&log, a, b, c, d);
    assert!(log.get() == append_digit(append_digit(append_digit(a, c), d), b));
}
pub fn symbolic_nested_wrong(a: u32, b: u32, c: u32, d: u32) {
    let log = Cell::new(0);
    symbolic_nested_trace(&log, a, b, c, d);
    assert!(log.get() == append_digit(append_digit(append_digit(a, d), c), b));
}
pub fn symbolic_covering(a: u32, b: u32, c: u32, d: u32) {
    let log = Cell::new(0);
    symbolic_covering_trace(&log, a, b, c, d);
    assert!(log.get() == append_digit(append_digit(append_digit(a, b), c), d));
}
pub fn symbolic_covering_wrong(a: u32, b: u32, c: u32, d: u32) {
    let log = Cell::new(0);
    symbolic_covering_trace(&log, a, b, c, d);
    assert!(log.get() == append_digit(append_digit(append_digit(a, b), d), c));
}

#[cfg(test)]
mod symbolic_native {
    #[test]
    fn positive() {
        for (a, b, c, d) in [
            (1, 2, 3, 4),
            (u32::MAX, 0, 1, u32::MAX),
            (17, 11, u32::MAX, 23),
        ] {
            super::symbolic_partial(a, b, c);
            super::symbolic_nested(a, b, c, d);
            super::symbolic_covering(a, b, c, d);
        }
    }
    #[test]
    fn partial_wrong() {
        super::symbolic_partial_wrong(1, 2, 3);
    }
    #[test]
    fn nested_wrong() {
        super::symbolic_nested_wrong(1, 2, 3, 4);
    }
    #[test]
    fn covering_wrong() {
        super::symbolic_covering_wrong(1, 2, 3, 4);
    }
}
