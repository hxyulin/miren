#![no_std]
#![feature(pattern_types, pattern_type_macro)]
#![allow(internal_features)]

#[derive(Clone, Copy)]
pub struct Packet {
    row: [u8; 2],
    marker: u16,
    floating: f32,
    character: char,
}

#[inline(never)]
fn selected_byte(values: &[[[u8; 2]; 2]], outer: usize, inner: usize) -> u8 {
    let selected = values[outer][inner];
    selected[0]
}
#[inline(never)]
fn empty_row(row: [u8; 0]) -> usize {
    row.len()
}

pub fn local_rows(index: usize) {
    let rows = [[3_u8, 7], [5, 11]];
    if index < 2 {
        let selected = rows[index];
        assert!(selected[1] == selected[0] * 2 + 1);
        assert!(selected[0] == if index == 0 { 3 } else { 5 });
    }
}
pub fn incoming_rows(values: &[[[u8; 2]; 2]], outer: usize, inner: usize) {
    if outer < values.len() && inner < 2 {
        let selected = values[outer][inner];
        if inner == 0 {
            assert!(selected[0] == values[outer][0][0]);
            assert!(selected[1] == values[outer][0][1]);
        } else {
            assert!(selected[0] == values[outer][1][0]);
            assert!(selected[1] == values[outer][1][1]);
        }
    }
}
pub fn owned_input(values: [[u8; 2]; 2], index: usize) {
    if index < 2 {
        let selected = values[index];
        assert!(selected[0] == values[index][0]);
        assert!(selected[1] == values[index][1]);
    }
}
pub fn tuple_rows(index: usize) {
    let rows = [([3_u8, 7], (true, 3_u16)), ([5, 11], (false, 5))];
    if index < 2 {
        let selected = rows[index];
        assert!(selected.0[0] as u16 == selected.1.1);
        assert!(selected.0[1] == selected.0[0] * 2 + 1);
        assert!(selected.1.0 == (index == 0));
    }
}
pub fn struct_rows(index: usize) {
    let rows = [
        Packet {
            row: [3, 7],
            marker: 3,
            floating: f32::from_bits(0x80000000),
            character: '\u{d7ff}',
        },
        Packet {
            row: [5, 11],
            marker: 5,
            floating: f32::from_bits(0x7fc00025),
            character: '\u{10ffff}',
        },
    ];
    if index < 2 {
        let selected = rows[index];
        assert!(selected.row[0] as u16 == selected.marker);
        assert!(selected.row[1] == selected.row[0] * 2 + 1);
        if index == 0 {
            assert!(selected.floating.to_bits() == 0x80000000);
            assert!(selected.character == '\u{d7ff}');
        } else {
            assert!(selected.floating.to_bits() == 0x7fc00025);
            assert!(selected.character == '\u{10ffff}');
        }
    }
}
pub fn selected_copy_mutation(index: usize) {
    let rows = [[3_u8, 7], [5, 11]];
    if index < 2 {
        let before = if index == 0 { 3 } else { 5 };
        let other = rows[index];
        let mut selected = rows[index];
        selected[0] = selected[0].wrapping_add(1);
        assert!(selected[0] == before + 1);
        assert!(other[0] == before);
        assert!(rows[index][0] == before);
        assert!(selected[1] == other[1]);
    }
}
pub fn exact_empty_bytes(index: usize) {
    let rows: [[u8; 0]; 2] = [[], []];
    if index < 2 {
        assert!(empty_row(rows[index]) == 0);
    }
}
pub fn empty_nonbyte_sibling(index: usize) {
    let rows: [([u8; 0], [u16; 0]); 2] = [([], []), ([], [])];
    if index < 2 {
        let selected = rows[index];
        assert!(empty_row(selected.0) == 0);
        assert!(selected.1.len() == 0);
    }
}
pub fn mutation_claim(values: &[[[u8; 2]; 2]], inner: usize) {
    if values.len() > 128 && inner < 2 {
        assert!(selected_byte(values, 128, inner) == values[128][inner][0]);
    }
}
pub fn wrong_byte(index: usize) {
    let rows = [[3_u8, 7], [5, 11]];
    if index < 2 {
        let selected = rows[index];
        assert!(selected[0] == selected[1]);
    }
}
pub fn independent_rows(values: [[u8; 2]; 2], index: usize) {
    if index < 2 {
        let selected = values[index];
        assert!(selected[0] == values[0][0]);
    }
}
pub fn bounds(values: [[u8; 2]; 2], index: usize) -> u8 {
    values[index][0]
}
pub fn retained_borrow(index: usize) {
    let rows = [[3_u8, 7], [5, 11]];
    if index < 2 {
        assert!(rows[index].len() == 2);
    }
}
pub fn ambiguous_store(index: usize) {
    let mut rows = [[3_u8, 7], [5, 11]];
    if index < 2 {
        rows[index][0] = 19;
        assert!(rows[index][0] == 19);
    }
}
#[derive(Clone, Copy)]
pub struct ReferenceRow<'a> {
    bytes: [u8; 2],
    reference: &'a u16,
}
pub fn reference_sibling(index: usize) {
    let value = 7_u16;
    let rows = [
        ReferenceRow {
            bytes: [3, 7],
            reference: &value,
        },
        ReferenceRow {
            bytes: [5, 11],
            reference: &value,
        },
    ];
    if index < 2 {
        let selected = rows[index];
        assert!(*selected.reference == value);
    }
}
#[derive(Clone, Copy)]
pub struct RawRow {
    bytes: [u8; 2],
    pointer: *const u16,
}
pub fn raw_sibling(values: [RawRow; 2], index: usize) {
    if index < 2 {
        assert!(values[index].pointer.is_null());
    }
}
type Positive = core::pattern_type!(u16 is 1..);
#[derive(Clone, Copy)]
pub struct RefinedRow {
    bytes: [u8; 2],
    restricted: [Positive; 0],
}
pub fn refined_sibling(values: [RefinedRow; 2], index: usize) {
    if index < 2 {
        let selected = values[index];
        assert!(selected.bytes[0] == 0);
    }
}
pub fn oversized_shape(values: [[u8; 129]; 2], index: usize) {
    if index < 2 {
        let selected = values[index];
        assert!(selected[0] == 0);
    }
}

#[cfg(not(test))]
mod analyzer_only {
    unsafe extern "Rust" {
        fn opaque_byte(value: u8) -> u8;
    }
    pub fn missing_body(values: &[[[u8; 2]; 2]], outer: usize, inner: usize) {
        if outer < values.len() && inner < 2 {
            let row = values[outer][inner];
            assert!(unsafe { opaque_byte(row[0]) } == row[0]);
        }
    }
    #[inline(never)]
    fn retained(values: &[[[u8; 2]; 2]], outer: usize, inner: usize) -> &[u8; 2] {
        &values[outer][inner]
    }
    #[inline(never)]
    fn retained_local(values: &[[u8; 2]; 2], index: usize) -> &[u8; 2] {
        &values[index]
    }
    pub fn local_untyped_retained(index: usize) {
        let values = [[3_u8, 7], [5, 11]];
        if index < 2 {
            assert!(retained_local(&values, index)[0] == if index == 0 { 3 } else { 5 });
        }
    }
    pub fn untyped_retained(values: &[[[u8; 2]; 2]], outer: usize, inner: usize) {
        if outer < values.len() && inner < 2 {
            assert!(retained(values, outer, inner)[0] == values[outer][inner][0]);
        }
    }
}

#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn positives() {
        for index in [0, 1, 2, usize::MAX] {
            local_rows(index);
            tuple_rows(index);
            struct_rows(index);
            selected_copy_mutation(index);
            exact_empty_bytes(index);
            empty_nonbyte_sibling(index);
            owned_input([[3, 7], [5, 11]], index);
            incoming_rows(&[[[3, 7], [5, 11]]; 129], 128, index);
        }
    }
    #[test]
    fn mutation_guard() {
        mutation_claim(&[[[3, 7], [5, 11]]; 129], 1);
    }
    #[test]
    #[should_panic]
    fn byte_negative() {
        wrong_byte(1);
    }
    #[test]
    #[should_panic]
    fn candidate_negative() {
        independent_rows([[3, 7], [5, 11]], 1);
    }
    #[test]
    #[should_panic]
    fn bounds_negative() {
        bounds([[3, 7], [5, 11]], 2);
    }
}
