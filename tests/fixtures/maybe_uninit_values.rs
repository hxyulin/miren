#![no_std]
#![feature(core_intrinsics, pattern_types, pattern_type_macro)]
#![allow(internal_features)]
use core::mem::MaybeUninit;
macro_rules! integer_roundtrip {
    ($name:ident, $integer:ty) => {
        pub fn $name(value: $integer) {
            let returned = unsafe { MaybeUninit::new(value).assume_init() };
            assert!(returned == value);
        }
    };
}
integer_roundtrip!(exact_u8, u8);
integer_roundtrip!(exact_u16, u16);
integer_roundtrip!(exact_u32, u32);
integer_roundtrip!(exact_u64, u64);
integer_roundtrip!(exact_u128, u128);
integer_roundtrip!(exact_usize, usize);
integer_roundtrip!(exact_i8, i8);
integer_roundtrip!(exact_i16, i16);
integer_roundtrip!(exact_i32, i32);
integer_roundtrip!(exact_i64, i64);
integer_roundtrip!(exact_i128, i128);
integer_roundtrip!(exact_isize, isize);

pub fn exact_bool(value: bool) {
    assert!(unsafe { MaybeUninit::new(value).assume_init() } == value);
}
pub fn exact_tuple(value: (u32, (bool, i16), ())) {
    assert!(unsafe { MaybeUninit::new(value).assume_init() } == value);
}
pub fn exact_f32(bits: u32) {
    assert!(unsafe { MaybeUninit::new(f32::from_bits(bits)).assume_init() }.to_bits() == bits);
}
pub fn exact_f64(bits: u64) {
    assert!(unsafe { MaybeUninit::new(f64::from_bits(bits)).assume_init() }.to_bits() == bits);
}
pub fn uninit_container() {
    let _ = MaybeUninit::<u32>::uninit();
}
pub fn unique_unit() {
    assert!(unsafe { MaybeUninit::<()>::uninit().assume_init() } == ());
}
pub fn unique_tuple() {
    assert!(unsafe { MaybeUninit::<((), ((), ()))>::uninit().assume_init() } == ((), ((), ())));
}
pub fn whole_assignment(value: u32) {
    let mut cell = MaybeUninit::new(value);
    if value == 0 {
        cell = MaybeUninit::new(7);
    }
    let result = unsafe { cell.assume_init() };
    if value == 0 {
        assert!(result == 7);
    } else {
        assert!(result == value);
    }
}
struct Holder {
    cell: MaybeUninit<(u32, bool)>,
}
pub fn nested_container(value: u32) {
    let holder = Holder {
        cell: MaybeUninit::new((value, true)),
    };
    let array = [holder.cell, MaybeUninit::new((9, false))];
    let result = unsafe { array[0].assume_init() };
    assert!(result == (value, true));
}
pub fn copied_wrapper(value: u32) {
    let a = MaybeUninit::new(value);
    let b = a;
    assert!(unsafe { a.assume_init() } == unsafe { b.assume_init() });
}
pub fn wrong_claim(value: u32) {
    assert!(unsafe { MaybeUninit::new(value).assume_init() } == 0);
}
pub fn mutation_claim(value: u32) {
    assert!(unsafe { MaybeUninit::new(value).assume_init() } == value);
}
pub fn uninitialized() -> u32 {
    unsafe { MaybeUninit::<u32>::uninit().assume_init() }
}
pub fn conditional_uninitialized(value: bool) -> u32 {
    let mut cell = MaybeUninit::<u32>::uninit();
    if value {
        cell = MaybeUninit::new(3);
    }
    unsafe { cell.assume_init() }
}
pub fn wrong_primitive() -> i32 {
    unsafe { core::mem::transmute(MaybeUninit::new(3u32)) }
}
#[repr(C)]
union Foreign {
    value: u32,
}
pub fn foreign_union() -> u32 {
    unsafe { Foreign { value: 3 }.value }
}
pub struct Empty;
pub fn zst_adt() -> Empty {
    unsafe { MaybeUninit::<Empty>::uninit().assume_init() }
}
pub fn pointer_payload(value: *const u32) -> *const u32 {
    unsafe { MaybeUninit::new(value).assume_init() }
}
pub fn reference_payload(value: &u32) -> &u32 {
    unsafe { MaybeUninit::new(value).assume_init() }
}
pub fn safe_write(value: u32) -> u32 {
    let mut cell = MaybeUninit::<u32>::uninit();
    *cell.write(value)
}
pub fn initialized_ref(value: u32) -> u32 {
    let cell = MaybeUninit::new(value);
    unsafe { *cell.assume_init_ref() }
}
pub fn zeroed() -> u32 {
    unsafe { MaybeUninit::<u32>::zeroed().assume_init() }
}
#[cfg(test)]
#[test]
fn native_valid() {
    for value in [0, 1, u32::MAX] {
        exact_u32(value);
        exact_tuple((value, (true, -7), ()));
        whole_assignment(value);
        nested_container(value);
        copied_wrapper(value);
        mutation_claim(value);
    }
    for value in [false, true] {
        exact_bool(value);
    }
    for bits in [0u32, 0x80000000, 0x7fc00015, u32::MAX] {
        exact_f32(bits);
    }
    for bits in [0u64, 0x8000000000000000, 0x7ff8000000000015, u64::MAX] {
        exact_f64(bits);
    }
    unique_unit();
    unique_tuple();
    uninit_container();
}

type Positive = core::pattern_type!(u32 is 1..);
pub fn root_pattern(value: Positive) -> Positive {
    unsafe { MaybeUninit::new(value).assume_init() }
}
pub fn direct_pattern() -> MaybeUninit<Positive> {
    MaybeUninit::uninit()
}
pub fn nested_pattern(value: (u32, Positive)) -> (u32, Positive) {
    unsafe { MaybeUninit::new(value).assume_init() }
}
pub fn uninhabited_guard() {
    core::intrinsics::assert_inhabited::<core::convert::Infallible>();
}
mod lookalike {
    pub fn assert_inhabited<T>() {}
}
pub fn lookalike_guard() {
    lookalike::assert_inhabited::<core::convert::Infallible>();
}
