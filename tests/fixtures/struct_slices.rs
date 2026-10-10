#![no_std]
#![feature(custom_mir, core_intrinsics, pattern_types, pattern_type_macro)]
#![allow(internal_features)]

#[derive(Clone, Copy, PartialEq)]
pub struct Record {
    left: u16,
    right: u16,
    padding: u8,
}
#[derive(Clone, Copy)]
pub struct Pair(u16, u16);
#[derive(Clone, Copy)]
pub struct Generic<T> {
    payload: T,
    flag: bool,
}
#[derive(Clone, Copy)]
pub struct Rich {
    small: f32,
    wide: f64,
    character: char,
    words: [i16; 2],
    unit: (),
}
#[derive(Clone, Copy)]
pub struct Nested {
    record: Record,
    words: [[u16; 2]; 2],
    empty: [char; 0],
}

#[inline(never)]
fn selected_field(values: &[Record], index: usize) -> u16 {
    values[index].left
}
#[inline(never)]
fn selected_reference(values: &[Record], index: usize) -> &u16 {
    &values[index].right
}

pub fn named_correlation(values: &[Record], index: usize) {
    if index < values.len() {
        let copied = values[index];
        assert!(copied.left == values[index].left);
        assert!(copied.right == values[index].right);
        assert!(copied.padding == values[index].padding);
    }
}
pub fn tuple_struct(values: &[Pair], index: usize) {
    if index < values.len() {
        assert!(values[index].0 == values[index].0);
        assert!(values[index].1 == values[index].1);
    }
}
pub fn generic_struct(values: &[Generic<([u16; 2], char)>], index: usize, field: usize) {
    if index < values.len() && field < 2 {
        let copied = values[index];
        assert!(copied.payload.0[field] == values[index].payload.0[field]);
        assert!(copied.payload.1 == values[index].payload.1);
        assert!(copied.flag == values[index].flag);
    }
}
pub fn nested_struct(values: &[Nested], index: usize, row: usize) {
    if index < values.len() && row < 2 {
        let copied = values[index];
        assert!(copied.record.left == values[index].record.left);
        assert!(copied.words[row][1] == values[index].words[row][1]);
        assert!(copied.empty.len() == 0);
    }
}
pub fn float_char(values: &[Rich], index: usize) {
    if index < values.len() {
        let copied = values[index];
        assert!(copied.small.to_bits() == values[index].small.to_bits());
        assert!(copied.wide.to_bits() == values[index].wide.to_bits());
        assert!(copied.character == values[index].character);
        assert!(copied.words[1] == values[index].words[1]);
        assert!(copied.unit == ());
        let code = copied.character as u32;
        assert!(code <= 0x10ffff && (code < 0xd800 || code > 0xdfff));
        if copied.small.is_nan() {
            assert!(values[index].small.is_nan());
        }
    }
}
pub fn views_and_cursor(values: &[Record], offset: usize, index: usize) {
    if offset <= values.len() {
        let suffix = &values[offset..];
        assert!(suffix.iter().len() == values.len() - offset);
        if index < suffix.len() {
            assert!(suffix.iter().nth(index).unwrap().right == values[offset + index].right);
        }
    }
    let end = values.len();
    assert!(values[end..end].iter().next().is_none());
}
pub fn layout(values: &[Record]) {
    assert!(core::mem::size_of_val(values) == values.len() * core::mem::size_of::<Record>());
    assert!(core::mem::align_of_val(values) == core::mem::align_of::<Record>());
}
pub fn returned_field(values: &[Record], index: usize) {
    if index < values.len() {
        assert!(*selected_reference(values, index) == values[index].right);
    }
}
pub fn owned_mutation(values: &[Record], index: usize) {
    if index < values.len() {
        let original = values[index].left;
        let mut copied = values[index];
        copied.left = copied.left.wrapping_add(1);
        assert!(copied.left == original.wrapping_add(1));
        assert!(values[index].left == original);
        assert!(copied.right == values[index].right);
    }
}
pub fn mutation_claim(values: &[Record]) {
    if values.len() > 128 {
        assert!(selected_field(values, 128) == values[128].left);
    }
}
pub fn independent_fields(values: &[Record], index: usize) {
    if index < values.len() {
        assert!(values[index].left == values[index].right);
    }
}
pub fn no_constructor_invariant(values: &[Record]) {
    if !values.is_empty() {
        assert!(values[0].left != 0);
    }
}
pub fn wrong_padding(values: &[Record]) {
    if !values.is_empty() {
        assert!(
            core::mem::size_of_val(values)
                == values.len() * (2 * core::mem::size_of::<u16>() + core::mem::size_of::<u8>())
        );
    }
}
pub fn bounds_at_end(values: &[Record]) -> u16 {
    values[values.len()].left
}
pub fn float_reflexivity(values: &[Rich], index: usize) {
    if index < values.len() {
        assert!(values[index].small == values[index].small);
    }
}
pub fn mutable_root(values: &mut [Record]) -> usize {
    values.len()
}
pub fn competing_roots(left: &[Record], right: &[Record]) -> bool {
    left.len() == right.len()
}
#[derive(Clone, Copy)]
pub struct Referenced {
    field: &'static u16,
}
pub fn reference_field(values: &[Referenced]) -> usize {
    values.len()
}
#[derive(Clone, Copy)]
pub struct Raw {
    field: *const u16,
}
pub fn raw_field(values: &[Raw]) -> usize {
    values.len()
}
#[derive(Clone, Copy)]
pub struct NonZero {
    field: core::num::NonZeroU16,
}
pub fn nonzero_field(values: &[NonZero]) -> usize {
    values.len()
}
#[derive(Clone, Copy)]
pub struct Wrapper {
    field: core::mem::ManuallyDrop<u16>,
}
pub fn core_wrapper(values: &[Wrapper]) -> usize {
    values.len()
}
pub struct Dropped {
    field: u16,
}
impl Drop for Dropped {
    fn drop(&mut self) {}
}
pub fn drop_field(values: &[Dropped]) -> usize {
    values.len()
}
#[derive(Clone, Copy)]
#[repr(packed)]
pub struct Packed {
    first: u8,
    second: u32,
}
pub fn packed(values: &[Packed]) -> usize {
    values.len()
}
#[derive(Clone, Copy)]
pub struct Zero;
#[derive(Clone, Copy)]
pub struct NestedZero {
    zero: Zero,
    ordinary: u16,
}
pub fn nested_zero_struct(values: &[NestedZero]) -> usize {
    values.len()
}
#[derive(Clone, Copy)]
pub struct EmptyZero {
    zero: [Zero; 0],
    ordinary: u16,
}
pub fn empty_zero_struct(values: &[EmptyZero]) -> usize {
    values.len()
}
pub fn whole_zero_struct(values: &[Zero]) -> usize {
    values.len()
}
type Positive = core::pattern_type!(u32 is 1..);
#[derive(Clone, Copy)]
pub struct Refined {
    field: [Positive; 0],
    ordinary: u16,
}
pub fn refined_zero_array(values: &[Refined]) -> usize {
    values.len()
}
#[derive(Clone, Copy)]
pub struct Large {
    field: [u16; 129],
}
pub fn oversized_shape(values: &[Large]) -> usize {
    values.len()
}
pub fn ambiguous_nested_struct(values: &[[Record; 2]], index: usize, inner: usize) {
    if index < values.len() && inner < 2 {
        assert!(values[index][inner].left != 0);
    }
}
#[derive(Clone, Copy)]
pub enum Choice {
    First(u16),
    Second(u16),
}
#[derive(Clone, Copy)]
pub struct EnumField {
    field: Choice,
}
pub fn enum_field(values: &[EnumField]) -> usize {
    values.len()
}
#[derive(Clone, Copy)]
pub union Union {
    first: u16,
    second: u16,
}
#[derive(Clone, Copy)]
pub struct UnionField {
    field: Union,
}
pub fn union_field(values: &[UnionField]) -> usize {
    values.len()
}

pub fn full_contains(values: &[Record], needle: Record) -> bool {
    values.contains(&needle)
}
pub fn full_equality(values: &[Record]) -> bool {
    values == values
}

#[cfg(not(test))]
mod analyzer_only {
    use core::intrinsics::mir::*;
    unsafe extern "Rust" {
        fn opaque_field(value: u16) -> u16;
    }
    pub fn missing_body(values: &[super::Record]) {
        if !values.is_empty() {
            assert!(unsafe { opaque_field(values[0].left) } == values[0].left);
        }
    }
    pub fn raw_source(pointer: *const super::Record, length: usize) -> usize {
        unsafe { core::slice::from_raw_parts(pointer, length) }.len()
    }
    fn metadata(values: &[super::Record; 0]) -> usize {
        values[..].iter().len()
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_empty() -> usize {
        mir! {
            let backing: [super::Record; 0];
            let source: &[super::Record; 0];
            { backing = []; source = &backing; Goto(retire) }
            retire = {
                StorageDead(backing);
                Call(RET = metadata(source), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }
}

#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn positives() {
        let long = [Record {
            left: 3,
            right: 7,
            padding: 11,
        }; 129];
        for values in [&[][..], &long[..]] {
            layout(values);
            views_and_cursor(values, values.len(), 0);
            for index in [0, 128, values.len()] {
                named_correlation(values, index);
                owned_mutation(values, index);
                returned_field(values, index);
            }
        }
        tuple_struct(&[Pair(3, 7); 129], 128);
        generic_struct(
            &[Generic {
                payload: ([3, 7], '\u{10ffff}'),
                flag: true,
            }; 129],
            128,
            1,
        );
        nested_struct(
            &[Nested {
                record: long[0],
                words: [[3, 7], [5, 11]],
                empty: [],
            }; 129],
            128,
            1,
        );
        float_char(
            &[Rich {
                small: f32::from_bits(0x7fc01234),
                wide: -0.0,
                character: '\u{10ffff}',
                words: [-3, 7],
                unit: (),
            }; 129],
            128,
        );
    }
    #[test]
    fn mutation_guard() {
        mutation_claim(
            &[Record {
                left: 3,
                right: 7,
                padding: 11,
            }; 129],
        );
    }
    #[test]
    #[should_panic]
    fn independent_negative() {
        independent_fields(
            &[Record {
                left: 3,
                right: 7,
                padding: 11,
            }],
            0,
        );
    }
    #[test]
    #[should_panic]
    fn constructor_negative() {
        no_constructor_invariant(&[Record {
            left: 0,
            right: 7,
            padding: 11,
        }]);
    }
    #[test]
    #[should_panic]
    fn padding_negative() {
        wrong_padding(
            &[Record {
                left: 3,
                right: 7,
                padding: 11,
            }; 129],
        );
    }
    #[test]
    #[should_panic]
    fn bounds_negative() {
        bounds_at_end(&[]);
    }
    #[test]
    #[should_panic]
    fn nan_negative() {
        float_reflexivity(
            &[Rich {
                small: f32::NAN,
                wide: 0.0,
                character: '\0',
                words: [0, 0],
                unit: (),
            }],
            0,
        );
    }
}
