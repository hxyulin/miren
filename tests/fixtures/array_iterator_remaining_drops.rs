#![no_std]
#![forbid(unsafe_code)]

pub struct Stamp(pub u16);
impl Drop for Stamp {
    fn drop(&mut self) {
        self.0 = self.0.wrapping_add(1);
        assert!(matches!(self.0, 12 | 23 | 34));
    }
}

pub fn full() {
    drop([Stamp(11), Stamp(22), Stamp(33)].into_iter());
}
pub fn front() {
    let mut iterator = [Stamp(11), Stamp(22), Stamp(33)].into_iter();
    drop(iterator.next().unwrap());
    drop(iterator);
}
pub fn back() {
    let mut iterator = [Stamp(11), Stamp(22), Stamp(33)].into_iter();
    drop(iterator.next_back().unwrap());
    drop(iterator);
}
pub fn mixed() {
    let mut iterator = [Stamp(11), Stamp(22), Stamp(33)].into_iter();
    drop(iterator.next().unwrap());
    drop(iterator.next_back().unwrap());
    drop(iterator);
}
pub fn exhausted() {
    let mut iterator = [Stamp(11), Stamp(22)].into_iter();
    drop(iterator.next().unwrap());
    drop(iterator.next_back().unwrap());
    assert!(iterator.next().is_none());
    drop(iterator);
}
pub fn empty() {
    drop(([] as [Stamp; 0]).into_iter());
}
pub struct Zero;
impl Drop for Zero {
    fn drop(&mut self) {
        assert!(core::mem::size_of::<Self>() == 0);
    }
}
pub fn zero() {
    let mut iterator = [Zero, Zero].into_iter();
    drop(iterator.next().unwrap());
    drop(iterator);
}
pub struct Address;
impl Drop for Address {
    fn drop(&mut self) {
        let address = self as *mut Self;
        assert!(!address.is_null());
    }
}
pub fn address_unknown() {
    drop([Address, Address].into_iter());
}
pub struct Nested(pub Stamp);
pub fn nested_unknown() {
    drop([Nested(Stamp(11))].into_iter());
}
pub fn wrong_remaining() {
    drop([Stamp(10)].into_iter());
}

pub struct Callback;
fn callback(value: &mut Callback) {
    let address = value as *mut Callback;
    assert!(!address.is_null());
}
impl Drop for Callback {
    fn drop(&mut self) {
        let callbacks: [fn(&mut Callback); 1] = [callback];
        callbacks[0](self);
    }
}
pub fn callback_unknown() {
    drop([Callback].into_iter());
}

pub struct FromFn;
impl Drop for FromFn {
    fn drop(&mut self) {
        let observations: [bool; 1] = core::array::from_fn(|_| {
            let address = self as *mut Self;
            !address.is_null()
        });
        assert!(observations[0]);
    }
}
pub fn from_fn_unknown() {
    drop([FromFn].into_iter());
}

pub struct Map;
impl Drop for Map {
    fn drop(&mut self) {
        let observations = [0_u8].map(|_| {
            let address = self as *mut Self;
            !address.is_null()
        });
        assert!(observations[0]);
    }
}
pub fn map_unknown() {
    drop([Map].into_iter());
}
