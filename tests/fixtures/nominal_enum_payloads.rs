#![no_std]
#![feature(pattern_types, pattern_type_macro)]
#![cfg_attr(not(test), feature(custom_mir, core_intrinsics))]
#![allow(internal_features)]

#[derive(Clone, Copy, PartialEq)]
pub struct Record {
    left: u16,
    right: u16,
    samples: [u16; 2],
}
impl Record {
    #[inline(never)]
    pub fn selected(self) -> u16 {
        self.left
    }
}
#[derive(Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum Packet {
    Empty = 3,
    Data(Record) = 7,
    Repeated(Record, Record) = 11,
}
pub fn selected(values: &[Packet], index: usize) {
    if index < values.len() {
        if let Packet::Data(record) = values[index] {
            assert!(record.selected() == record.left);
            assert!(record.samples[0] == record.samples[0]);
        }
    }
}
pub fn falsely_zero(values: &[Packet], index: usize) {
    if index < values.len() {
        if let Packet::Data(record) = values[index] { assert!(record.selected() == 0); }
    }
}
pub fn falsely_equal(values: &[Packet], index: usize) {
    if index < values.len() {
        if let Packet::Repeated(left, right) = values[index] {
            assert!(left.selected() == right.selected());
        }
    }
}
pub fn long_selected(values: &[Packet]) {
    if values.len() > 128 { selected(values, values.len() - 1); }
}
pub fn view(values: &[Packet], start: usize, index: usize) {
    if start <= values.len() && index < values.len() - start {
        if let Packet::Data(record) = values[start..][index] {
            if let Packet::Data(other) = values[start + index] {
                assert!(record.selected() == other.left);
            } else { panic!(); }
        }
    }
}
pub fn cursor(values: &[Packet], index: usize) {
    match values.iter().nth(index) {
        Some(Packet::Data(record)) => {
            if let Packet::Data(other) = values[index] {
                assert!(record.selected() == other.left);
            } else { panic!(); }
        }
        Some(_) => assert!(index < values.len()),
        None => assert!(index >= values.len()),
    }
}
pub fn borrowed_field(values: &[Packet], index: usize) -> Option<&u16> {
    if index < values.len() {
        if let Packet::Data(record) = &values[index] { return Some(&record.left); }
    }
    None
}
pub fn layout(values: &[Packet]) {
    assert!(core::mem::size_of_val(values) == values.len() * core::mem::size_of::<Packet>());
    assert!(core::mem::align_of_val(values) == core::mem::align_of::<Packet>());
}
#[derive(Clone, Copy)]
pub struct Single { value: u16 }
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum Small { Empty, Value(Single) }
pub fn scalar_payload(values: &[Small], index: usize) {
    if index < values.len() {
        if let Small::Value(record) = values[index] {
            if let Small::Value(other) = values[index] { assert!(record.value == other.value); }
        }
    }
}
#[derive(Clone, Copy)]
pub struct Pair { first: u16, second: u16 }
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum Paired { Empty, Value(Pair) }
pub fn pair_payload(values: &[Paired], index: usize) {
    if index < values.len() {
        if let Paired::Value(record) = values[index] {
            if let Paired::Value(other) = values[index] {
                assert!(record.first == other.first && record.second == other.second);
            }
        }
    }
}
#[derive(Clone, Copy)]
pub struct Generic<T: Copy, const N: usize> { value: T, samples: [u16; N] }
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum GenericPacket<T: Copy, const N: usize> { Empty, Value(Generic<T, N>) }
pub fn generic_payload(values: &[GenericPacket<u16, 2>], index: usize) {
    if index < values.len() {
        if let GenericPacket::Value(record) = values[index] {
            if let GenericPacket::Value(other) = values[index] {
                assert!(record.value == other.value && record.samples[1] == other.samples[1]);
            }
        }
    }
}
#[derive(Clone, Copy)]
#[repr(align(16))]
pub struct Marker;
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum Zero { Empty, Value(Marker, [Marker; 0]) }
pub fn zero_payload(values: &[Zero], index: usize) {
    if index < values.len() {
        if let Zero::Value(_, array) = values[index] { assert!(array.len() == 0); }
    }
}
#[derive(Clone, Copy)]
pub struct Numerical { character: char, single: f32, double: f64 }
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum Numbers { Empty, Value(Numerical) }
pub fn numerical_bits(values: &[Numbers], index: usize) {
    if index < values.len() {
        if let Numbers::Value(record) = values[index] {
            if let Numbers::Value(other) = values[index] {
                assert!(record.character == other.character);
                assert!(record.single.to_bits() == other.single.to_bits());
                assert!(record.double.to_bits() == other.double.to_bits());
            }
        }
    }
}
#[derive(Clone, Copy)]
pub struct Nested { record: Record, marker: Marker }
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum Nest { Empty, Value(Nested) }
pub fn nested(values: &[Nest], index: usize) {
    if index < values.len() {
        if let Nest::Value(record) = values[index] {
            assert!(record.record.selected() == record.record.left);
        }
    }
}
#[derive(Clone, Copy)]
pub struct FalseEquality { value: u16 }
impl PartialEq for FalseEquality {
    #[inline(never)]
    fn eq(&self, _: &Self) -> bool { false }
}
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum EqualityPacket { Empty, Value(FalseEquality) }
pub fn custom_false_equality(values: &[EqualityPacket], index: usize) {
    if index < values.len() {
        if let EqualityPacket::Value(record) = values[index] { assert!(record == record); }
    }
}
#[derive(Copy)]
pub struct PanicClone { value: u16 }
impl Clone for PanicClone {
    #[inline(never)]
    fn clone(&self) -> Self { panic!(); }
}
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum ClonePacket { Empty, Value(PanicClone) }
pub fn custom_panic_clone(values: &[ClonePacket], index: usize) {
    if index < values.len() {
        if let ClonePacket::Value(record) = values[index] { let _ = record.clone(); }
    }
}
pub fn out_of_bounds(values: &[Packet], index: usize) { let _ = values[index]; }
pub fn contains(values: &[Packet]) { let _ = values.contains(&Packet::Empty); }
pub fn equality(values: &[Packet]) { assert!(values == values); }
pub fn mutable(values: &mut [Packet]) { let _ = values.len(); }
#[derive(Clone, Copy)]
pub struct Flag { value: bool }
#[derive(Clone, Copy)]
pub enum WrappedBool { Empty, Value(Flag) }
pub fn wrapped_niche(values: &[WrappedBool]) { let _ = values.len(); }
#[derive(Clone, Copy)]
#[repr(C, packed)]
pub struct Packed { value: u16 }
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum PackedPacket { Empty, Value(Packed) }
pub fn packed_zero(values: &[([PackedPacket; 0], u16)]) { let _ = values.len(); }
#[derive(Clone, Copy)]
pub struct Child<T: Copy> { empty: [T; 0] }
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum ChildPacket<T: Copy> { Empty, Value(Child<T>) }
pub fn reference_zero(values: &[ChildPacket<&'static u16>]) { let _ = values.len(); }
pub fn refined_zero(values: &[ChildPacket<core::pattern_type!(u16 is 1..)>]) {
    let _ = values.len();
}
pub fn core_zero(values: &[ChildPacket<core::num::NonZeroU16>]) { let _ = values.len(); }
pub struct Dropped;
impl Drop for Dropped { fn drop(&mut self) {} }
pub enum DroppedPacket { Empty, Value([Dropped; 0]) }
pub fn drop_zero(values: &[DroppedPacket]) { let _ = values.len(); }
#[derive(Clone, Copy)]
pub struct Huge { values: [u16; 129] }
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum HugePacket { Empty, Value(Huge) }
pub fn type_budget(values: &[HugePacket]) { let _ = values.len(); }
#[cfg(not(test))]
pub mod analyzer_only {
    use super::*;
    use core::intrinsics::mir::*;
    unsafe extern "Rust" { fn unavailable(value: Record) -> u16; }
    pub fn missing_body(values: &[Packet], index: usize) {
        if index < values.len() {
            if let Packet::Data(record) = values[index] {
                assert!(unsafe { unavailable(record) } == record.left);
            }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn inactive(value: Packet) -> u16 {
        mir! { let record: Record; { record = Field(Variant(value, 1), 0);
            RET = record.left; Return() } }
    }
    pub fn inactive_payload(values: &[Packet], index: usize) -> u16 {
        if index < values.len() { inactive(values[index]) } else { 0 }
    }
    fn cursor_len(value: &core::slice::Iter<'_, Packet>) -> usize { value.len() }
    fn iterator(values: &[Packet; 0]) -> core::slice::Iter<'_, Packet> { values.iter() }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_empty() -> usize {
        mir! { let backing: [Packet; 0]; let reference: &[Packet; 0];
            let cursor: core::slice::Iter<'_, Packet>; let borrow: &core::slice::Iter<'_, Packet>;
            { backing = []; reference = &backing;
                Call(cursor = iterator(reference), ReturnTo(retire), UnwindUnreachable()) }
            retire = { StorageDead(backing); borrow = &cursor;
                Call(RET = cursor_len(borrow), ReturnTo(done), UnwindUnreachable()) }
            done = { Return() }
        }
    }
    pub fn raw_consumer(values: &[Packet], index: usize) {
        if index < values.len() { let _ = unsafe { values.as_ptr().add(index).read() }; }
    }
}
#[cfg(test)]
mod native {
    use super::*;
    fn record() -> Record { Record { left: 3, right: 7, samples: [17, 19] } }
    #[test]
    fn mutation_guard() { selected(&[Packet::Data(record()); 129], 128); }
    #[test]
    fn positives() {
        let values = [Packet::Data(record()); 129];
        selected(&[], usize::MAX); selected(&values, 128); long_selected(&values);
        view(&values, 128, 0); cursor(&values, 128); cursor(&values, usize::MAX);
        assert!(borrowed_field(&values, 128) == Some(&3)); layout(&values);
        scalar_payload(&[Small::Value(Single { value: 37 })], 0);
        pair_payload(&[Paired::Value(Pair { first: 3, second: 7 })], 0);
        generic_payload(&[GenericPacket::Value(Generic { value: 37, samples: [3, 7] })], 0);
        zero_payload(&[Zero::Value(Marker, [])], 0);
        numerical_bits(&[Numbers::Value(Numerical { character: '🦀', single: f32::NAN,
            double: -0.0 })], 0);
        nested(&[Nest::Value(Nested { record: record(), marker: Marker })], 0);
    }
    #[test]
    #[should_panic]
    fn actual_false_equality() {
        custom_false_equality(&[EqualityPacket::Value(FalseEquality { value: 3 })], 0);
    }
    #[test]
    #[should_panic]
    fn actual_panic_clone() {
        custom_panic_clone(&[ClonePacket::Value(PanicClone { value: 3 })], 0);
    }
    #[test]
    #[should_panic]
    fn false_zero() { falsely_zero(&[Packet::Data(record())], 0); }
    #[test]
    #[should_panic]
    fn false_siblings() {
        falsely_equal(&[Packet::Repeated(record(), Record { left: 7, ..record() })], 0);
    }
}
