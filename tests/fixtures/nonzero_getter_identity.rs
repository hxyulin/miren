#![no_std]
#![forbid(unsafe_code)]
use core::num::{NonZeroI16, NonZeroU32, NonZeroUsize};

#[inline(never)]
fn get(_: NonZeroU32) -> u32 {
    0
}

pub fn free_getter_body_returns_zero(value: NonZeroU32) {
    assert!(get(value) == 0);
}
pub fn free_getter_is_not_the_core_getter(value: NonZeroU32) {
    assert!(get(value) == value.get());
}

mod panicking {
    use super::NonZeroU32;
    #[inline(never)]
    pub fn get(_: NonZeroU32) -> u32 {
        panic!("actual free getter body");
    }
}
pub fn free_getter_panic_runs(value: NonZeroU32) {
    let _ = panicking::get(value);
}

trait LocalGet {
    fn get(self) -> u32;
}
impl LocalGet for NonZeroU32 {
    #[inline(never)]
    fn get(self) -> u32 {
        0
    }
}
pub fn trait_getter_body_returns_zero(value: NonZeroU32) {
    assert!(LocalGet::get(value) == 0);
}
pub fn trait_getter_is_not_the_core_getter(value: NonZeroU32) {
    assert!(LocalGet::get(value) == value.get());
}
trait PanicGet {
    fn get(self) -> u32;
}
impl PanicGet for NonZeroU32 {
    #[inline(never)]
    fn get(self) -> u32 {
        panic!("actual trait getter body");
    }
}
pub fn trait_getter_panic_runs(value: NonZeroU32) {
    let _ = PanicGet::get(value);
}

pub fn genuine_unsigned_getter(value: NonZeroU32) {
    assert!(value.get() != 0);
}
pub fn genuine_signed_getter(value: NonZeroI16) {
    assert!(value.get() != 0);
}
pub fn genuine_pointer_width_getter(value: NonZeroUsize) {
    assert!(value.get() != 0);
}
pub fn wrong_genuine_getter_claim(value: NonZeroI16) {
    assert!(value.get() == 0);
}

pub struct Other(u32);
impl Other {
    #[inline(never)]
    fn get(&self) -> u32 {
        17
    }
}
pub fn unrelated_inherent_getter_runs(value: u32) {
    assert!(Other(value).get() == 17);
}

mod opaque {
    pub fn get(_: &str) -> u32 {
        0
    }
}
pub fn unrelated_string_getter_is_unknown(value: &str) {
    assert!(opaque::get(value) == 0);
}

#[cfg(test)]
extern crate std;
#[cfg(test)]
#[test]
fn native_getter_bodies() {
    for raw in [1, 17, u32::MAX] {
        let value = NonZeroU32::new(raw).unwrap();
        free_getter_body_returns_zero(value);
        trait_getter_body_returns_zero(value);
        genuine_unsigned_getter(value);
        assert!(std::panic::catch_unwind(|| free_getter_is_not_the_core_getter(value)).is_err());
        assert!(std::panic::catch_unwind(|| trait_getter_is_not_the_core_getter(value)).is_err());
        assert!(std::panic::catch_unwind(|| free_getter_panic_runs(value)).is_err());
        assert!(std::panic::catch_unwind(|| trait_getter_panic_runs(value)).is_err());
    }
    for raw in [i16::MIN, -1, 1, i16::MAX] {
        genuine_signed_getter(NonZeroI16::new(raw).unwrap());
    }
    genuine_pointer_width_getter(NonZeroUsize::new(1).unwrap());
    unrelated_inherent_getter_runs(9);
}
