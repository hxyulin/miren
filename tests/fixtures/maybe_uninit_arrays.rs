#![no_std]
#![feature(
    core_intrinsics,
    maybe_uninit_array_assume_init,
    pattern_types,
    pattern_type_macro
)]
#![allow(internal_features)]
use core::mem::MaybeUninit;
pub fn integers(value: [u16; 3]) {
    let result = unsafe { MaybeUninit::new(value).assume_init() };
    assert!(result == value);
}
pub fn bytes(value: [u8; 128]) {
    let result = unsafe { MaybeUninit::new(value).assume_init() };
    assert!(result == value);
}
pub fn bools(value: [bool; 3]) {
    let result = unsafe { MaybeUninit::new(value).assume_init() };
    assert!(result == value);
}
pub fn tuples(value: [(u16, bool); 3]) {
    let result = unsafe { MaybeUninit::new(value).assume_init() };
    assert!(result == value);
}
pub fn nested(value: [[i32; 2]; 3]) {
    let result = unsafe { MaybeUninit::new(value).assume_init() };
    assert!(result == value);
}
pub fn float_bits(bits: [u32; 3]) {
    let value = [
        f32::from_bits(bits[0]),
        f32::from_bits(bits[1]),
        f32::from_bits(bits[2]),
    ];
    let result = unsafe { MaybeUninit::new(value).assume_init() };
    assert!(result[0].to_bits() == bits[0]);
    assert!(result[1].to_bits() == bits[1]);
    assert!(result[2].to_bits() == bits[2]);
}
pub fn float64_bits(bits: [u64; 3]) {
    let value = [
        f64::from_bits(bits[0]),
        f64::from_bits(bits[1]),
        f64::from_bits(bits[2]),
    ];
    let result = unsafe { MaybeUninit::new(value).assume_init() };
    assert!(result[0].to_bits() == bits[0]);
    assert!(result[1].to_bits() == bits[1]);
    assert!(result[2].to_bits() == bits[2]);
}
pub fn boundary(value: [u16; 128]) {
    let result = unsafe { MaybeUninit::new(value).assume_init() };
    assert!(result[127] == value[127]);
}
pub fn node_boundary(value: [(u16, bool); 85]) {
    let result = unsafe { MaybeUninit::new(value).assume_init() };
    assert!(result[84] == value[84]);
}
pub fn node_exhaustion(value: [(u16, bool); 86]) {
    let _ = unsafe { MaybeUninit::new(value).assume_init() };
}
pub fn oversized(value: [u16; 129]) {
    let _ = unsafe { MaybeUninit::new(value).assume_init() };
}
pub fn empty_initialized() {
    let result = unsafe { MaybeUninit::new([] as [u16; 0]).assume_init() };
    assert!(result.len() == 0);
}
pub fn empty_bytes() {
    let result = unsafe { MaybeUninit::<[u8; 0]>::uninit().assume_init() };
    assert!(result.len() == 0);
}
pub fn empty_integers() {
    let result = unsafe { MaybeUninit::<[u16; 0]>::uninit().assume_init() };
    assert!(result.len() == 0);
}
pub fn unique_units() {
    let result = unsafe { MaybeUninit::<[(); 128]>::uninit().assume_init() };
    assert!(result[127] == ());
}
pub fn unique_nested() {
    let result = unsafe { MaybeUninit::<[[((), ()); 2]; 3]>::uninit().assume_init() };
    assert!(result[2][1] == ((), ()));
}
pub fn replaced(value: [u16; 3], pick: bool) {
    let mut cell = MaybeUninit::new(value);
    let copy = cell;
    if pick {
        cell = MaybeUninit::new([7, 8, 9]);
    }
    let result = unsafe { cell.assume_init() };
    let old = unsafe { copy.assume_init() };
    assert!(old == value);
    if pick {
        assert!(result == [7, 8, 9]);
    } else {
        assert!(result == value);
    }
}
pub fn helper() -> [u16; 3] {
    unsafe { MaybeUninit::new([3, 5, 7]).assume_init() }
}
pub fn mutation_claim() {
    assert!(helper() == [3, 5, 7]);
}
pub fn wrong_claim() {
    assert!(helper()[2] == 6);
}
pub fn bounds_failure(index: usize) {
    let _ = helper()[index];
}
pub fn uninitialized() -> [u16; 3] {
    unsafe { MaybeUninit::uninit().assume_init() }
}
pub fn conditional(value: bool) -> [u16; 3] {
    let mut cell = MaybeUninit::uninit();
    if value {
        cell = MaybeUninit::new([3, 5, 7]);
    }
    unsafe { cell.assume_init() }
}
pub fn wrong_type() -> [i16; 3] {
    unsafe { core::mem::transmute(MaybeUninit::new([3u16, 5, 7])) }
}
pub fn raw_elements() {
    let _ = MaybeUninit::<[*const u16; 0]>::uninit();
}
pub fn reference_elements() {
    let _ = MaybeUninit::<[&u16; 0]>::uninit();
}
#[derive(Clone, Copy)]
enum Never {}
pub fn never_elements() {
    let _ = MaybeUninit::<[Never; 0]>::uninit();
}
pub fn nonzero_elements() {
    let _ = MaybeUninit::<[core::num::NonZeroU16; 0]>::uninit();
}
struct Drops;
impl Drop for Drops {
    fn drop(&mut self) {}
}
pub fn drop_elements() {
    let _ = MaybeUninit::<[Drops; 0]>::uninit();
}
pub fn arbitrary_wrapper(value: MaybeUninit<[u16; 3]>) -> [u16; 3] {
    unsafe { value.assume_init() }
}
pub fn array_assume_init() -> [u16; 3] {
    unsafe {
        MaybeUninit::array_assume_init([
            MaybeUninit::new(3),
            MaybeUninit::new(5),
            MaybeUninit::new(7),
        ])
    }
}
pub fn wrapper_repeat() {
    let _ = [MaybeUninit::new(3u16); 3];
}
pub fn reference_result() -> u16 {
    let cell = MaybeUninit::new([3u16, 5, 7]);
    unsafe { cell.assume_init_ref()[0] }
}
pub fn zeroed() -> [u16; 3] {
    unsafe { MaybeUninit::<[u16; 3]>::zeroed().assume_init() }
}
type Positive = core::pattern_type!(u16 is 1..);
pub fn pattern_elements() {
    let _ = MaybeUninit::<[Positive; 0]>::uninit();
}
pub fn nested_pattern_elements() {
    let _ = MaybeUninit::<[[(Positive, ()); 0]; 0]>::uninit();
}
#[cfg(test)]
#[test]
fn native_valid() {
    integers([0, 3, u16::MAX]);
    bytes([17; 128]);
    bools([true, false, true]);
    tuples([(3, true), (5, false), (7, true)]);
    nested([[3, -5], [0, i32::MIN], [i32::MAX, 7]]);
    float_bits([0, 0x80000000, 0x7fc00015]);
    float64_bits([0, 0x8000000000000000, 0x7ff8000000000015]);
    boundary([3; 128]);
    node_boundary([(3, true); 85]);
    empty_initialized();
    empty_bytes();
    empty_integers();
    unique_units();
    unique_nested();
    replaced([3, 5, 7], false);
    replaced([3, 5, 7], true);
    mutation_claim();
}

pub fn zero_byte_node_exhaustion() {
    let _ = MaybeUninit::<[((), ()); 128]>::uninit();
}
type Deep0 = u16;
type Deep1 = [Deep0; 1];
type Deep2 = [Deep1; 1];
type Deep3 = [Deep2; 1];
type Deep4 = [Deep3; 1];
type Deep5 = [Deep4; 1];
type Deep6 = [Deep5; 1];
type Deep7 = [Deep6; 1];
type Deep8 = [Deep7; 1];
type Deep9 = [Deep8; 1];
type Deep10 = [Deep9; 1];
type Deep11 = [Deep10; 1];
type Deep12 = [Deep11; 1];
type Deep13 = [Deep12; 1];
type Deep14 = [Deep13; 1];
type Deep15 = [Deep14; 1];
type Deep16 = [Deep15; 1];
type Deep17 = [Deep16; 1];
pub fn depth_exhaustion() {
    let _ = MaybeUninit::<Deep17>::uninit();
}
