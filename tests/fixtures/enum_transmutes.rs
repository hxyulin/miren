#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]
use core::intrinsics::mir::*;

#[repr(u8)]
#[derive(Clone, Copy)]
pub enum Pull { Floating = 0, Up = 1, Down = 2, Reserved = 3 }
#[repr(i8)]
#[derive(Clone, Copy)]
pub enum Signed { Negative = -7, Zero = 0, Positive = 9 }
#[repr(u16)]
#[derive(Clone, Copy)]
pub enum Sparse { Low = 3, High = 300 }
#[repr(u128)]
#[derive(Clone, Copy)]
pub enum Wide { Low = 0, High = 1 << 100 }
#[repr(isize)]
#[derive(Clone, Copy)]
pub enum PointerSized { Negative = -1, Positive = 7 }
#[repr(u8)]
#[derive(Clone, Copy)]
pub enum Singleton { Only = 7 }
#[derive(Clone, Copy)]
pub enum DefaultRepr { First, Second }
#[repr(C)]
#[derive(Clone, Copy)]
pub enum CRepr { First, Second }
#[repr(u8)]
#[derive(Clone, Copy)]
pub enum Payload { First(u8), Second(u8) }
#[repr(u8)]
pub enum Dropped { First, Second }
impl Drop for Dropped { fn drop(&mut self) {} }

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn cast<S, T>(value: S) -> T { mir! {{ RET = CastTransmute(value); Return() }} }
fn to_bits(value: Pull) -> u8 { cast(value) }
pub fn concrete() {
    assert!(to_bits(Pull::Floating) == 0);
    assert!(to_bits(Pull::Up) == 1);
    assert!(to_bits(Pull::Down) == 2);
    assert!(to_bits(Pull::Reserved) == 3);
    assert!(cast::<_, i8>(Signed::Negative) == -7);
    assert!(cast::<_, u16>(Sparse::High) == 300);
}
pub fn symbolic(value: Pull) {
    let expected = match value { Pull::Floating => 0, Pull::Up => 1, Pull::Down => 2, Pull::Reserved => 3 };
    assert!(to_bits(value) == expected);
}
pub fn sparse(value: Sparse) {
    let bits: u16 = cast(value);
    assert!(bits == 3 || bits == 300);
}
pub fn signed_sparse(value: Signed) {
    let bits: i8 = cast(value);
    assert!(bits == -7 || bits == 0 || bits == 9);
    match value { Signed::Negative => assert!(bits == -7), Signed::Zero => assert!(bits == 0),
        Signed::Positive => assert!(bits == 9) }
}
pub fn wide(value: Wide) {
    let bits: u128 = cast(value);
    assert!(bits == 0 || bits == 1 << 100);
    assert!(cast::<_, u128>(Wide::High) == 1 << 100);
}
pub fn pointer_sized(value: PointerSized) {
    let bits: isize = cast(value);
    assert!(bits == -1 || bits == 7);
}
pub fn wrong_claim() { assert!(to_bits(Pull::Up) == 2); }
pub fn excludes_negative(value: Signed) { assert!(cast::<_, i8>(value) != -7); }
pub fn excludes_positive(value: Signed) { assert!(cast::<_, i8>(value) != 9); }
pub fn excludes_sparse(value: Sparse) { assert!(cast::<_, u16>(value) != 300); }
pub fn reverse(value: u8) { let _: Pull = cast(value); }
pub fn payload(value: Payload) { let _: u16 = cast(value); }
pub fn default_repr(value: DefaultRepr) { let _: u8 = cast(value); }
pub fn c_repr(value: CRepr) { let _: u32 = cast(value); }
pub fn wrong_sign(value: Pull) { let _: i8 = cast(value); }
pub fn wrong_width(value: Pull) { let _: u16 = cast(value); }
pub fn singleton(value: Singleton) -> u8 { cast(value) }
pub fn dropped(value: Dropped) { let _: u8 = cast(value); }
pub fn bool_target(value: Pull) { let _: bool = cast(value); }

#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn positives() {
        concrete();
        for value in [Pull::Floating, Pull::Up, Pull::Down, Pull::Reserved] { symbolic(value); }
        for value in [Signed::Negative, Signed::Zero, Signed::Positive] { signed_sparse(value); }
        for value in [Sparse::Low, Sparse::High] { sparse(value); }
        for value in [Wide::Low, Wide::High] { wide(value); }
        for value in [PointerSized::Negative, PointerSized::Positive] { pointer_sized(value); }
    }
}
