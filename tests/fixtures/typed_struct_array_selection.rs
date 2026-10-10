#![no_std]
#![feature(custom_mir, core_intrinsics, pattern_types, pattern_type_macro)]
#![allow(internal_features)]

#[derive(Clone, Copy, PartialEq)]
pub struct Record {
    left: u16,
    right: u16,
}
#[derive(Clone, Copy)]
pub struct TupleRecord(u16, u16);
#[derive(Clone, Copy)]
pub struct Generic<T> {
    payload: T,
    marker: bool,
}
#[derive(Clone, Copy)]
pub struct Nested {
    record: Record,
    words: [u32; 2],
}
#[derive(Clone, Copy)]
pub struct Rich {
    small: f32,
    wide: f64,
    character: char,
}
#[derive(Clone, Copy)]
pub struct Zero {
    unit: (),
    empty: [u16; 0],
}

#[inline(never)]
fn selected_field(values: &[[Record; 2]], outer: usize, inner: usize) -> u16 {
    values[outer][inner].left
}

pub fn named_array(values: [Record; 2], index: usize) {
    if index < 2 {
        let selected = values[index];
        if index == 0 {
            assert!(selected.left == values[0].left);
            assert!(selected.right == values[0].right);
        } else {
            assert!(selected.left == values[1].left);
            assert!(selected.right == values[1].right);
        }
    }
}
pub fn tuple_array(index: usize) {
    let values = [TupleRecord(3, 7), TupleRecord(5, 11)];
    if index < 2 {
        let selected = values[index];
        assert!(selected.1 == selected.0 * 2 + 1);
    }
}
pub fn generic_array(index: usize, field: usize) {
    let values = [
        Generic {
            payload: ([3_u16, 7], -3_i32),
            marker: true,
        },
        Generic {
            payload: ([5, 11], -5),
            marker: false,
        },
    ];
    if index < 2 && field < 2 {
        let selected = values[index];
        assert!(selected.payload.0[1] == selected.payload.0[0] * 2 + 1);
        assert!(selected.payload.1 == -(selected.payload.0[0] as i32));
        if selected.marker {
            assert!(selected.payload.0[0] == 3);
        } else {
            assert!(selected.payload.0[0] == 5);
        }
        assert!(selected.payload.0[field] == values[index].payload.0[field]);
    }
}
pub fn nested_array(values: [Nested; 2], index: usize, word: usize) {
    if index < 2 && word < 2 {
        let selected = values[index];
        assert!(selected.record.left == values[index].record.left);
        assert!(selected.record.right == values[index].record.right);
        assert!(selected.words[word] == values[index].words[word]);
    }
}
pub fn incoming_composite(values: &[[Record; 2]], outer: usize, inner: usize) {
    if outer < values.len() && inner < 2 {
        let selected = values[outer][inner];
        if inner == 0 {
            assert!(selected.left == values[outer][0].left);
            assert!(selected.right == values[outer][0].right);
        } else {
            assert!(selected.left == values[outer][1].left);
            assert!(selected.right == values[outer][1].right);
        }
    }
}
pub fn owned_copy_mutation(values: [Record; 2], index: usize) {
    if index < 2 {
        let before = values[index].left;
        let other = values[index];
        let mut selected = values[index];
        selected.left = selected.left.wrapping_add(1);
        assert!(selected.left == before.wrapping_add(1));
        assert!(values[index].left == before);
        assert!(other.left == before);
        assert!(selected.right == other.right);
    }
}
pub fn float_char_choices(index: usize) {
    let values = [
        Rich {
            small: f32::from_bits(0x80000000),
            wide: f64::from_bits(0x7ff8000000000015),
            character: '\u{d7ff}',
        },
        Rich {
            small: f32::from_bits(0x7fc00025),
            wide: f64::from_bits(0x8000000000000000),
            character: '\u{10ffff}',
        },
    ];
    if index < 2 {
        let selected = values[index];
        if index == 0 {
            assert!(selected.small.to_bits() == 0x80000000);
            assert!(selected.wide.to_bits() == 0x7ff8000000000015);
            assert!(selected.character == '\u{d7ff}');
        } else {
            assert!(selected.small.to_bits() == 0x7fc00025);
            assert!(selected.wide.to_bits() == 0x8000000000000000);
            assert!(selected.character == '\u{10ffff}');
        }
        let code = selected.character as u32;
        assert!(code <= 0x10ffff && (code < 0xd800 || code > 0xdfff));
    }
}
pub fn nominal_zero(index: usize) {
    let values = [Zero {
        unit: (),
        empty: [],
    }; 2];
    if index < 2 {
        assert!(values[index].empty.len() == 0);
        assert!(values[index].unit == ());
    }
}
pub fn owned_nominal_zero(index: usize) {
    let values = [Zero {
        unit: (),
        empty: [],
    }; 2];
    if index < 2 {
        let copied = values[index];
        assert!(copied.empty.len() == 0);
        assert!(copied.unit == ());
    }
}

pub fn mutation_claim(values: &[[Record; 2]], inner: usize) {
    if values.len() > 128 && inner < 2 {
        assert!(selected_field(values, 128, inner) == values[128][inner].left);
    }
}
pub fn wrong_field(values: [Record; 2], index: usize) {
    if index < 2 {
        assert!(values[index].left == values[index].right);
    }
}
pub fn wrong_candidate(index: usize) {
    let values = [Record { left: 3, right: 7 }, Record { left: 5, right: 11 }];
    if index < 2 {
        assert!(values[index].left == 3);
    }
}
pub fn bounds_at_end(values: [Record; 2], index: usize) -> u16 {
    values[index].left
}

#[derive(Clone, Copy)]
struct RefRecord<'a> {
    reference: &'a u16,
}
pub fn singleton_reference(index: usize) {
    let source = 7_u16;
    let values = [RefRecord { reference: &source }];
    if index < values.len() {
        assert!(*values[index].reference == source);
    }
}
pub fn uniquely_guarded_reference(index: usize) {
    let first = 3_u16;
    let second = 7_u16;
    let values = [
        RefRecord { reference: &first },
        RefRecord { reference: &second },
    ];
    if index == 1 {
        assert!(*values[index].reference == second);
    }
}
pub fn ambiguous_reference(index: usize) {
    let first = 3_u16;
    let second = 7_u16;
    let values = [
        RefRecord { reference: &first },
        RefRecord { reference: &second },
    ];
    if index < 2 {
        assert!(*values[index].reference == if index == 0 { first } else { second });
    }
}
pub fn ambiguous_store(index: usize) {
    let mut values = [Record { left: 3, right: 7 }, Record { left: 5, right: 11 }];
    if index < 2 {
        values[index].left = 19;
        assert!(values[index].left == 19);
    }
}
#[derive(Clone, Copy)]
pub struct RawRecord {
    pointer: *const u16,
}
pub fn raw_record(values: [RawRecord; 2], index: usize) {
    if index < 2 {
        assert!(values[index].pointer.is_null());
    }
}
type Positive = core::pattern_type!(u16 is 1..);
#[derive(Clone, Copy)]
pub struct Refined {
    empty: [Positive; 0],
    field: u16,
}
pub fn refined_zero_array(values: [Refined; 2], index: usize) {
    if index < 2 {
        assert!(values[index].field == 0);
    }
}
pub struct Dropped {
    field: u16,
}
impl Drop for Dropped {
    fn drop(&mut self) {}
}
pub fn dropped_record(index: usize) {
    let values = [Dropped { field: 3 }, Dropped { field: 7 }];
    if index < 2 {
        assert!(values[index].field != 0);
    }
}
pub fn byte_choices(index: usize) {
    let values = [[3_u8, 7], [5, 11]];
    if index < 2 {
        assert!(values[index][0] != 0);
    }
}
#[derive(Clone, Copy)]
pub struct Large {
    field: [u16; 129],
}
pub fn oversized_shape(values: [Large; 2], index: usize) {
    if index < 2 {
        assert!(values[index].field[0] == 0);
    }
}
pub fn full_contains(values: &[[Record; 2]], needle: [Record; 2]) -> bool {
    values.contains(&needle)
}
pub fn full_equality(values: &[[Record; 2]]) -> bool {
    values == values
}

#[cfg(not(test))]
mod analyzer_only {
    unsafe extern "Rust" {
        fn opaque_field(value: u16) -> u16;
    }
    pub fn missing_body(values: &[[super::Record; 2]], outer: usize, inner: usize) {
        if outer < values.len() && inner < 2 {
            let value = values[outer][inner].left;
            assert!(unsafe { opaque_field(value) } == value);
        }
    }
    #[inline(never)]
    fn retained(values: &[[super::Record; 2]], outer: usize, inner: usize) -> &super::Record {
        &values[outer][inner]
    }
    pub fn untyped_retained(values: &[[super::Record; 2]], outer: usize, inner: usize) {
        if outer < values.len() && inner < 2 {
            assert!(retained(values, outer, inner).left == values[outer][inner].left);
        }
    }
}

#[cfg(test)]
mod native {
    use super::*;
    fn pair() -> [Record; 2] {
        [Record { left: 3, right: 7 }, Record { left: 5, right: 11 }]
    }
    #[test]
    fn positives() {
        for index in [0, 1, 2, usize::MAX] {
            named_array(pair(), index);
            tuple_array(index);
            generic_array(index, 1);
            incoming_composite(&[pair(); 129], 128, index);
            owned_copy_mutation(pair(), index);
            float_char_choices(index);
            nominal_zero(index);
            owned_nominal_zero(index);
            singleton_reference(index);
            uniquely_guarded_reference(index);
        }
        nested_array(
            [
                Nested {
                    record: pair()[0],
                    words: [3, 7],
                },
                Nested {
                    record: pair()[1],
                    words: [5, 11],
                },
            ],
            1,
            1,
        );
    }
    #[test]
    fn mutation_guard() {
        mutation_claim(&[pair(); 129], 1);
    }
    #[test]
    #[should_panic]
    fn field_negative() {
        wrong_field(pair(), 1);
    }
    #[test]
    #[should_panic]
    fn candidate_negative() {
        wrong_candidate(1);
    }
}
