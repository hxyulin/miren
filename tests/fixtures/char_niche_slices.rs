#![no_std]
#![feature(pattern_types, pattern_type_macro)]
#![cfg_attr(not(test), feature(custom_mir, core_intrinsics))]
#![allow(internal_features)]

#[derive(Clone, Copy)]
pub enum Switch {
    Empty,
    Value(char),
}
#[derive(Clone, Copy)]
pub enum Reversed {
    Value(char),
    Empty,
}
#[inline(never)]
pub fn selected_char(value: Option<char>) -> char {
    match value {
        Some(value) => value,
        None => '\0',
    }
}
pub fn repeated(values: &[Option<char>], index: usize) {
    if index < values.len() {
        if let Some(value) = values[index] {
            assert!(selected_char(values[index]) == value);
        } else {
            assert!(values[index].is_none());
        }
    }
}
pub fn local_sum(values: &[Switch], index: usize) {
    if index < values.len() {
        match values[index] {
            Switch::Value(value) => {
                if let Switch::Value(again) = values[index] {
                    assert!(value == again);
                } else {
                    panic!("changed variant");
                }
            }
            Switch::Empty => assert!(matches!(values[index], Switch::Empty)),
        }
    }
}
pub fn reversed(values: &[Reversed], index: usize) {
    if index < values.len() {
        if let Reversed::Value(value) = values[index] {
            if let Reversed::Value(again) = values[index] {
                assert!(value == again);
            } else {
                panic!("changed variant");
            }
        }
    }
}
pub fn metadata(values: &[Option<char>]) {
    assert!(core::mem::size_of_val(values) == values.len() * 4);
    assert!(core::mem::align_of_val(values) == 4);
}
pub fn long_selected(values: &[Option<char>]) {
    if values.len() > 128 {
        if let Some(value) = values[128] {
            assert!(selected_char(values[128]) == value);
        }
    }
}
pub fn view(values: &[Option<char>], start: usize, index: usize) {
    if start <= values.len() && index < values.len() - start {
        if let Some(value) = values[start..][index] {
            assert!(selected_char(values[start + index]) == value);
        }
    }
}
pub fn cursor(values: &[Option<char>], index: usize) {
    match values.iter().nth(index) {
        Some(value) => {
            assert!(index < values.len());
            if let Some(value) = *value {
                assert!(selected_char(values[index]) == value);
            }
        }
        None => assert!(index >= values.len()),
    }
}
pub fn cursor_metadata(values: &[Option<char>]) {
    let mut cursor = values.iter();
    assert!(cursor.clone().count() == values.len());
    let _ = cursor.next_back();
    assert!(cursor.len() == values.len().saturating_sub(1));
}
pub fn occurrence(values: &[(Option<char>, [Option<char>; 2])], index: usize) {
    if index < values.len() {
        let (first, pair) = values[index];
        if let Some(first) = first {
            assert!(selected_char(values[index].0) == first);
        }
        if let Some(second) = pair[1] {
            assert!(selected_char(values[index].1[1]) == second);
        }
    }
}
impl Switch {
    #[inline(never)]
    pub fn read(self) -> char {
        match self {
            Self::Value(value) => value,
            Self::Empty => '\0',
        }
    }
}
pub fn user_method(values: &[Switch], index: usize) {
    if index < values.len() {
        if let Switch::Value(value) = values[index] {
            assert!(values[index].read() == value);
        }
    }
}
pub fn borrowed_payload(values: &[Option<char>], index: usize) {
    if index < values.len() {
        if let Some(value) = &values[index] {
            assert!(*value == selected_char(values[index]));
        }
    }
}
pub fn unicode_validity(values: &[Option<char>], index: usize) {
    if index < values.len() {
        if let Some(value) = values[index] {
            let code = value as u32;
            assert!(code <= 0x10ffff);
            assert!(code < 0xd800 || code > 0xdfff);
            assert!(code != u32::MAX);
        }
    }
}
pub fn maximum_scalar(values: &[Option<char>], index: usize) {
    if index < values.len() && values[index] == Some('\u{10ffff}') {
        assert!(selected_char(values[index]) == '\u{10ffff}');
    }
}
pub fn false_ascii(values: &[Option<char>], index: usize) {
    if index < values.len() {
        if let Some(value) = values[index] {
            assert!((value as u32) < 128);
        }
    }
}
pub fn competing(left: &[Option<char>], right: &[Option<char>]) -> usize {
    left.len() + right.len()
}
pub fn false_char(values: &[Option<char>], index: usize) {
    if index < values.len() {
        if let Some(value) = values[index] {
            assert!(value == 'A');
        }
    }
}
pub fn false_variant(values: &[Option<char>], index: usize) {
    if index < values.len() {
        assert!(values[index].is_none());
    }
}
pub fn false_correlation(values: &[(Option<char>, Option<char>)], index: usize) {
    if index < values.len() {
        if let (Some(left), Some(right)) = values[index] {
            assert!(left == right);
        }
    }
}
pub fn unwrap(values: &[Option<char>], index: usize) {
    if index < values.len() {
        let _ = values[index].unwrap();
    }
}
pub fn bounds(values: &[Option<char>]) {
    let _ = values[values.len()];
}
pub fn zero_original(values: &[([Option<char>; 0], u16)]) {
    let _ = values.len();
}
pub fn nonzero_niche(values: &[Option<core::num::NonZeroU16>]) {
    let _ = values.len();
}
pub fn ref_zero(values: &[([Option<&u16>; 0], u16)]) {
    let _ = values.len();
}
type Refined = core::pattern_type!(u8 is 1..);
pub fn refined_zero(values: &[([Option<Refined>; 0], u16)]) {
    let _ = values.len();
}
#[derive(Clone, Copy)]
pub struct Wrapped(pub char);
pub fn wrapped_niche(values: &[Option<Wrapped>]) {
    let _ = values.len();
}
#[derive(Clone, Copy)]
pub enum Three {
    Empty,
    Other,
    Value(char),
}
pub fn multi_niche(values: &[Three]) {
    let _ = values.len();
}
pub fn mutable(values: &mut [Option<char>]) {
    let _ = values.len();
}
pub fn contains(values: &[Option<char>]) {
    let _ = values.contains(&None);
}
pub fn equality(values: &[Option<char>]) {
    assert!(values == values);
}
pub fn type_budget(values: &[([Option<char>; 129], u16)]) {
    let _ = values.len();
}
#[cfg(not(test))]
pub mod analyzer_only {
    use core::intrinsics::mir::*;
    unsafe extern "Rust" {
        fn unavailable(value: Option<char>) -> char;
    }
    pub fn missing_body(values: &[Option<char>], index: usize) {
        if index < values.len() {
            assert!(unsafe { unavailable(values[index]) } == '\0');
        }
    }
    fn slice_cursor(values: &[Option<char>]) -> core::slice::Iter<'_, Option<char>> {
        values.iter()
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn copied_handle_live(values: &[Option<char>]) -> usize {
        mir! {
            let cursor: core::slice::Iter<'_, Option<char>>;
            let borrow: &core::slice::Iter<'_, Option<char>>;
            { Call(cursor = slice_cursor(values), ReturnTo(retire), UnwindUnreachable()) }
            retire = {
                StorageDead(values);
                borrow = &cursor;
                Call(RET = cursor_len(borrow), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn unchecked_payload(value: Option<char>) -> char {
        mir! { { RET = Field(Variant(value, 1), 0); Return() } }
    }
    pub fn inactive_payload(values: &[Option<char>], index: usize) -> char {
        if index < values.len() {
            unchecked_payload(values[index])
        } else {
            '\0'
        }
    }
    fn empty_cursor(values: &[Option<char>; 0]) -> core::slice::Iter<'_, Option<char>> {
        values.iter()
    }
    fn cursor_len(cursor: &core::slice::Iter<'_, Option<char>>) -> usize {
        cursor.len()
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_empty() -> usize {
        mir! {
            let backing: [Option<char>; 0];
            let source: &[Option<char>; 0];
            let cursor: core::slice::Iter<'_, Option<char>>;
            let borrow: &core::slice::Iter<'_, Option<char>>;
            {
                backing = [];
                source = &backing;
                Call(cursor = empty_cursor(source), ReturnTo(retire), UnwindUnreachable())
            }
            retire = {
                StorageDead(backing);
                borrow = &cursor;
                Call(RET = cursor_len(borrow), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }
}
#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn unicode_boundaries() {
        let values = [
            Some('\0'),
            Some('\u{d7ff}'),
            Some('\u{e000}'),
            Some('\u{10ffff}'),
            None,
        ];
        for index in 0..values.len() {
            unicode_validity(&values, index);
            repeated(&values, index);
            maximum_scalar(&values, index);
        }
    }
    #[test]
    fn repeated_cases() {
        for index in [0, 1, 2, usize::MAX] {
            repeated(&[None, Some('A'), Some('B')], index);
        }
        local_sum(&[Switch::Empty, Switch::Value('B')], 1);
        user_method(&[Switch::Value('B')], 0);
        borrowed_payload(&[Some('B')], 0);
        reversed(&[Reversed::Empty, Reversed::Value('A')], 1);
        zero_original(&[([], 7)]);
    }
    #[test]
    fn views_and_cursors() {
        let values = [None, Some('A'), Some('B')];
        view(&values, 1, 1);
        cursor(&values, 2);
        cursor(&values, usize::MAX);
        cursor_metadata(&values);
        cursor_metadata(&[]);
        metadata(&values);
        metadata(&[]);
    }
    #[test]
    fn independent_occurrences() {
        occurrence(&[(Some('B'), [Some('A'), Some('B')])], 0);
    }
    #[test]
    fn mutation_guard() {
        long_selected(&[Some('B'); 129]);
    }
    #[test]
    #[should_panic]
    fn false_char_control() {
        false_char(&[Some('B')], 0);
    }
    #[test]
    #[should_panic]
    fn false_variant_control() {
        false_variant(&[Some('A')], 0);
    }
    #[test]
    #[should_panic]
    fn correlation_control() {
        false_correlation(&[(Some('B'), Some('A'))], 0);
    }
}
