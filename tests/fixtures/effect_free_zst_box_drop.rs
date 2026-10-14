#![no_std]
#![forbid(unsafe_code)]
extern crate alloc;
use alloc::boxed::Box;

#[repr(align(4096))]
pub struct Marker;
impl Drop for Marker {
    fn drop(&mut self) {}
}
#[inline(never)]
pub fn actual_tag() -> u16 {
    17
}
#[inline(never)]
pub fn selected(owner: Box<Marker>) -> u16 {
    core::mem::drop(owner);
    actual_tag()
}
pub fn implicit() {
    let _owner = Box::new(Marker);
    assert!(actual_tag() == 17);
}
pub fn explicit() {
    core::mem::drop(Box::new(Marker));
    assert!(actual_tag() == 17);
}
pub fn transfer() {
    assert!(selected(Box::new(Marker)) == 17);
}
pub fn independent() {
    let first = Box::new(Marker);
    let second = Box::new(Marker);
    core::mem::drop(first);
    core::mem::drop(second);
    assert!(actual_tag() == 17);
}
pub fn branches(choose: bool) {
    let owner = Box::new(Marker);
    if choose {
        core::mem::drop(owner);
    } else {
        let moved = owner;
        core::mem::drop(moved);
    }
    assert!(actual_tag() == 17);
}
pub fn wrong_tag() {
    assert!(selected(Box::new(Marker)) == 18);
}

pub struct Panicking;
impl Drop for Panicking {
    fn drop(&mut self) {
        panic!("actual payload destructor panic");
    }
}
pub fn panicking() {
    let _owner = Box::new(Panicking);
}
static SIDE_EFFECT: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);
pub struct Effectful;
impl Drop for Effectful {
    fn drop(&mut self) {
        SIDE_EFFECT.store(1, core::sync::atomic::Ordering::Relaxed);
    }
}
pub fn effectful() {
    let _owner = Box::new(Effectful);
}
pub struct Nested(pub Marker);
pub fn nested() {
    let _owner = Box::new(Nested(Marker));
}
pub struct Nonzero(pub u8);
impl Drop for Nonzero {
    fn drop(&mut self) {}
}
pub fn nonzero() {
    let _owner = Box::new(Nonzero(7));
}
pub struct ZeroArray(pub [Marker; 0]);
impl Drop for ZeroArray {
    fn drop(&mut self) {}
}
pub fn zero_array() {
    let _owner = Box::new(ZeroArray([]));
}
pub struct NotFreeze(pub core::cell::UnsafeCell<()>);
impl Drop for NotFreeze {
    fn drop(&mut self) {}
}
pub fn not_freeze() {
    let _owner = Box::new(NotFreeze(core::cell::UnsafeCell::new(())));
}

#[cfg(test)]
mod native {
    #[test]
    fn unchanged_claims_execute_actual_destructor_and_helper() {
        super::implicit();
        super::explicit();
        super::transfer();
        super::independent();
        super::branches(true);
        super::branches(false);
    }
}

#[repr(align(64))]
pub struct HelperMarker;
#[inline(never)]
fn actual_drop_helper(value: u16) {
    assert!(value == 17);
}
impl Drop for HelperMarker {
    #[inline(never)]
    fn drop(&mut self) {
        actual_drop_helper(17);
    }
}
pub fn helper_box() {
    core::mem::drop(Box::new(HelperMarker));
}
