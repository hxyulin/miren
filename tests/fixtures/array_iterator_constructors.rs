#![no_std]
#![forbid(unsafe_code)]

pub struct Stamp(pub u16);
impl Drop for Stamp {
    fn drop(&mut self) {}
}

pub fn constructor(input: [Stamp; 2]) -> core::array::IntoIter<Stamp, 2> {
    input.into_iter()
}

pub fn constructor_move(a: Stamp, b: Stamp) -> core::array::IntoIter<Stamp, 2> {
    [a, b].into_iter()
}

pub fn constructor_wrong(flag: bool, input: [Stamp; 2]) -> core::array::IntoIter<Stamp, 2> {
    assert!(!flag);
    input.into_iter()
}

pub fn remaining_drop_unknown(input: [Stamp; 2]) {
    drop(input.into_iter());
}

pub fn next_unknown(input: [Stamp; 2]) {
    let mut iterator = input.into_iter();
    let _ = iterator.next();
}

fn pass(iterator: core::array::IntoIter<Stamp, 2>) -> core::array::IntoIter<Stamp, 2> {
    iterator
}

pub fn helper_argument_unknown(input: [Stamp; 2]) -> core::array::IntoIter<Stamp, 2> {
    pass(input.into_iter())
}
