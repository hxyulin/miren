#![no_std]
#![feature(pattern_types, pattern_type_macro)]
#![cfg_attr(not(test), feature(custom_mir, core_intrinsics))]
#![allow(internal_features)]

#[derive(Clone, Copy)]
pub enum Switch {
    Empty,
    Value(bool),
}
#[derive(Clone, Copy)]
pub enum Reversed {
    Value(bool),
    Empty,
}
#[inline(never)]
pub fn selected_bool(value: Option<bool>) -> bool {
    match value {
        Some(value) => value,
        None => false,
    }
}
pub fn repeated(values: &[Option<bool>], index: usize) {
    if index < values.len() {
        if let Some(value) = values[index] {
            assert!(selected_bool(values[index]) == value);
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
pub fn metadata(values: &[Option<bool>]) {
    assert!(core::mem::size_of_val(values) == values.len());
    assert!(core::mem::align_of_val(values) == 1);
}
pub fn long_selected(values: &[Option<bool>]) {
    if values.len() > 128 {
        if let Some(value) = values[128] {
            assert!(selected_bool(values[128]) == value);
        }
    }
}
pub fn view(values: &[Option<bool>], start: usize, index: usize) {
    if start <= values.len() && index < values.len() - start {
        if let Some(value) = values[start..][index] {
            assert!(selected_bool(values[start + index]) == value);
        }
    }
}
pub fn cursor(values: &[Option<bool>], index: usize) {
    match values.iter().nth(index) {
        Some(value) => {
            assert!(index < values.len());
            if let Some(value) = *value {
                assert!(selected_bool(values[index]) == value);
            }
        }
        None => assert!(index >= values.len()),
    }
}
pub fn cursor_metadata(values: &[Option<bool>]) {
    let mut cursor = values.iter();
    assert!(cursor.clone().count() == values.len());
    let _ = cursor.next_back();
    assert!(cursor.len() == values.len().saturating_sub(1));
}
pub fn occurrence(values: &[(Option<bool>, [Option<bool>; 2])], index: usize) {
    if index < values.len() {
        let (first, pair) = values[index];
        if let Some(first) = first {
            assert!(selected_bool(values[index].0) == first);
        }
        if let Some(second) = pair[1] {
            assert!(selected_bool(values[index].1[1]) == second);
        }
    }
}
impl Switch {
    #[inline(never)]
    pub fn read(self) -> bool {
        match self {
            Self::Value(value) => value,
            Self::Empty => false,
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
pub fn borrowed_payload(values: &[Option<bool>], index: usize) {
    if index < values.len() {
        if let Some(value) = &values[index] {
            assert!(*value == selected_bool(values[index]));
        }
    }
}
pub fn competing(left: &[Option<bool>], right: &[Option<bool>]) -> usize {
    left.len() + right.len()
}
pub fn false_bool(values: &[Option<bool>], index: usize) {
    if index < values.len() {
        if let Some(value) = values[index] {
            assert!(!value);
        }
    }
}
pub fn false_variant(values: &[Option<bool>], index: usize) {
    if index < values.len() {
        assert!(values[index].is_none());
    }
}
pub fn false_correlation(values: &[(Option<bool>, Option<bool>)], index: usize) {
    if index < values.len() {
        if let (Some(left), Some(right)) = values[index] {
            assert!(left == right);
        }
    }
}
pub fn unwrap(values: &[Option<bool>], index: usize) {
    if index < values.len() {
        let _ = values[index].unwrap();
    }
}
pub fn bounds(values: &[Option<bool>]) {
    let _ = values[values.len()];
}
pub fn zero_original(values: &[([Option<bool>; 0], u16)]) {
    let _ = values.len();
}
pub fn char_niche(values: &[Option<char>]) {
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
pub struct Wrapped(pub bool);
pub fn wrapped_niche(values: &[Option<Wrapped>]) {
    let _ = values.len();
}
#[derive(Clone, Copy)]
pub enum Three {
    Empty,
    Other,
    Value(bool),
}
pub fn multi_niche(values: &[Three]) {
    let _ = values.len();
}
pub fn mutable(values: &mut [Option<bool>]) {
    let _ = values.len();
}
pub fn contains(values: &[Option<bool>]) {
    let _ = values.contains(&None);
}
pub fn equality(values: &[Option<bool>]) {
    assert!(values == values);
}
pub fn type_budget(values: &[([Option<bool>; 129], u16)]) {
    let _ = values.len();
}
#[cfg(not(test))]
pub mod analyzer_only {
    use core::intrinsics::mir::*;
    unsafe extern "Rust" {
        fn unavailable(value: Option<bool>) -> bool;
    }
    pub fn missing_body(values: &[Option<bool>], index: usize) {
        if index < values.len() {
            assert!(unsafe { unavailable(values[index]) });
        }
    }
    fn slice_cursor(values: &[Option<bool>]) -> core::slice::Iter<'_, Option<bool>> {
        values.iter()
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn copied_handle_live(values: &[Option<bool>]) -> usize {
        mir! {
            let cursor: core::slice::Iter<'_, Option<bool>>;
            let borrow: &core::slice::Iter<'_, Option<bool>>;
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
    fn unchecked_payload(value: Option<bool>) -> bool {
        mir! { { RET = Field(Variant(value, 1), 0); Return() } }
    }
    pub fn inactive_payload(values: &[Option<bool>], index: usize) -> bool {
        if index < values.len() {
            unchecked_payload(values[index])
        } else {
            false
        }
    }
    fn empty_cursor(values: &[Option<bool>; 0]) -> core::slice::Iter<'_, Option<bool>> {
        values.iter()
    }
    fn cursor_len(cursor: &core::slice::Iter<'_, Option<bool>>) -> usize {
        cursor.len()
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_empty() -> usize {
        mir! {
            let backing: [Option<bool>; 0];
            let source: &[Option<bool>; 0];
            let cursor: core::slice::Iter<'_, Option<bool>>;
            let borrow: &core::slice::Iter<'_, Option<bool>>;
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
    fn repeated_cases() {
        for index in [0, 1, 2, usize::MAX] {
            repeated(&[None, Some(false), Some(true)], index);
        }
        local_sum(&[Switch::Empty, Switch::Value(true)], 1);
        user_method(&[Switch::Value(true)], 0);
        borrowed_payload(&[Some(true)], 0);
        reversed(&[Reversed::Empty, Reversed::Value(false)], 1);
        zero_original(&[([], 7)]);
    }
    #[test]
    fn views_and_cursors() {
        let values = [None, Some(false), Some(true)];
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
        occurrence(&[(Some(true), [Some(false), Some(true)])], 0);
    }
    #[test]
    fn mutation_guard() {
        long_selected(&[Some(true); 129]);
    }
    #[test]
    #[should_panic]
    fn false_bool_control() {
        false_bool(&[Some(true)], 0);
    }
    #[test]
    #[should_panic]
    fn false_variant_control() {
        false_variant(&[Some(false)], 0);
    }
    #[test]
    #[should_panic]
    fn correlation_control() {
        false_correlation(&[(Some(true), Some(false))], 0);
    }
}
