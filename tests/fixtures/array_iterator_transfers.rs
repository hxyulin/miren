#![no_std]
#![forbid(unsafe_code)]

pub struct Stamp(pub u16);
impl Drop for Stamp {
    fn drop(&mut self) {
        self.0 = self.0.wrapping_add(1);
        assert!(matches!(self.0, 12 | 23 | 34));
    }
}

pub fn front_drop() -> core::array::IntoIter<Stamp, 2> {
    let mut iterator = [Stamp(11), Stamp(22)].into_iter();
    let value = iterator.next().unwrap();
    assert!(value.0 == 11);
    drop(value);
    iterator
}

pub fn back_drop() -> core::array::IntoIter<Stamp, 2> {
    let mut iterator = [Stamp(11), Stamp(22)].into_iter();
    let value = iterator.next_back().unwrap();
    assert!(value.0 == 22);
    drop(value);
    iterator
}

pub fn wrong_front() -> core::array::IntoIter<Stamp, 2> {
    let mut iterator = [Stamp(11), Stamp(22)].into_iter();
    let value = iterator.next().unwrap();
    assert!(value.0 == 22);
    drop(value);
    iterator
}

pub fn mixed() -> (
    Option<Stamp>, Option<Stamp>, Option<Stamp>, Option<Stamp>, Option<Stamp>,
    core::array::IntoIter<Stamp, 3>,
) {
    let mut iterator = [Stamp(11), Stamp(22), Stamp(33)].into_iter();
    let first = iterator.next();
    let last = iterator.next_back();
    let middle = iterator.next();
    let empty_front = iterator.next();
    let empty_back = iterator.next_back();
    (first, last, middle, empty_front, empty_back, iterator)
}

pub fn empty() -> core::array::IntoIter<Stamp, 0> {
    let mut iterator: core::array::IntoIter<Stamp, 0> = [].into_iter();
    assert!(iterator.next().is_none());
    assert!(iterator.next_back().is_none());
    iterator
}

pub struct Zero;
impl Drop for Zero {
    fn drop(&mut self) {
        assert!(core::mem::size_of::<Self>() == 0);
    }
}

pub fn zero_sized() -> core::array::IntoIter<Zero, 2> {
    let mut iterator = [Zero, Zero].into_iter();
    drop(iterator.next().unwrap());
    drop(iterator.next_back().unwrap());
    assert!(iterator.next().is_none());
    iterator
}

pub fn remaining_unknown() {
    let mut iterator = [Stamp(11), Stamp(22)].into_iter();
    drop(iterator.next().unwrap());
    drop(iterator);
}

pub fn mem_forget_unknown() {
    let mut iterator = [Stamp(11), Stamp(22)].into_iter();
    drop(iterator.next().unwrap());
    core::mem::forget(iterator);
}

fn resume(mut iterator: core::array::IntoIter<Stamp, 2>) -> (
    Option<Stamp>, core::array::IntoIter<Stamp, 2>,
) {
    let value = iterator.next_back();
    (value, iterator)
}

pub fn helper_transport() -> (Option<Stamp>, core::array::IntoIter<Stamp, 2>) {
    let mut iterator = [Stamp(11), Stamp(22)].into_iter();
    drop(iterator.next().unwrap());
    resume(iterator)
}
