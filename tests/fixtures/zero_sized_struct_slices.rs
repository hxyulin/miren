#![no_std]
#![feature(custom_mir, core_intrinsics, pattern_types, pattern_type_macro)]
#![allow(internal_features)]

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct NamedZero {
    unit: (),
    empty: [u16; 0],
}
#[derive(Clone, Copy)]
pub struct NestedZero {
    named: NamedZero,
    other: ((), [char; 0]),
}
#[derive(Clone, Copy)]
pub struct GenericZero<T> {
    empty: [T; 0],
    unit: (),
}
#[derive(Clone, Copy)]
#[repr(align(64))]
pub struct AlignedZero;

#[inline(never)]
fn selected_present(values: &[NamedZero], index: usize) -> bool {
    values.iter().nth(index).is_some()
}
#[inline(never)]
fn selected_unit(values: &[NamedZero], index: usize) -> &() {
    &values[index].unit
}
#[inline(never)]
fn copied_zero(values: &[NamedZero], index: usize) -> NamedZero {
    values[index]
}
impl NamedZero {
    #[inline(never)]
    fn marker(&self) -> u16 {
        7
    }
}

pub fn observations(values: &[NamedZero], index: usize) {
    if index < values.len() {
        let copied = copied_zero(values, index);
        assert!(copied.unit == ());
        assert!(copied.empty.len() == 0);
        assert!(*selected_unit(values, index) == ());
    }
}
pub fn nested(values: &[NestedZero], index: usize) {
    if index < values.len() {
        let copied = values[index];
        assert!(copied.named.empty.len() == 0);
        assert!(copied.other.0 == ());
        assert!(copied.other.1.len() == 0);
    }
}
pub fn generic(values: &[GenericZero<char>], index: usize) {
    if index < values.len() {
        assert!(values[index].empty.len() == 0);
        assert!(values[index].unit == ());
    }
}
pub fn metadata(values: &[NamedZero]) {
    let mut iterator = values.iter();
    assert!(iterator.clone().count() == values.len());
    assert!(iterator.size_hint() == (values.len(), Some(values.len())));
    assert!(iterator.by_ref().count() == values.len());
    assert!(iterator.next().is_none());
}
pub fn views(values: &[NamedZero], offset: usize, index: usize) {
    if offset <= values.len() {
        let suffix = &values[offset..];
        assert!(suffix.len() == values.len() - offset);
        if index < suffix.len() {
            assert!(suffix[index].unit == ());
        }
    }
    let end = values.len();
    assert!(values[end..end].iter().next().is_none());
}
pub fn layout(values: &[AlignedZero]) {
    assert!(core::mem::size_of_val(values) == 0);
    assert!(core::mem::align_of_val(values) == core::mem::align_of::<AlignedZero>());
}
pub fn maximum_cursor(values: &[AlignedZero]) {
    if values.len() == usize::MAX {
        let mut iterator = values.iter();
        assert!(iterator.next_back().is_some());
        assert!(iterator.len() == usize::MAX - 1);
        assert!(iterator.nth(usize::MAX - 2).is_some());
        assert!(iterator.len() == 0);
        assert!(iterator.next().is_none());
        assert!(values.iter().nth(usize::MAX).is_none());
    }
}
pub fn clone_and_method(values: &[NamedZero], index: usize) {
    if index < values.len() {
        let copied = values[index].clone();
        assert!(copied == values[index]);
        assert!(copied.marker() == 7);
    }
}
pub fn mutation_claim(values: &[NamedZero], index: usize) {
    if index < values.len() {
        assert!(selected_present(values, index));
    }
}
pub fn maximum_reachable(values: &[AlignedZero]) {
    assert!(values.len() != usize::MAX);
}
pub fn falsely_isize_bounded(values: &[NamedZero]) {
    assert!(values.len() <= isize::MAX as usize);
}
pub fn wrong_alignment(values: &[AlignedZero]) {
    assert!(core::mem::align_of_val(values) == 1);
}
pub fn wrong_method(values: &[NamedZero]) {
    if !values.is_empty() {
        assert!(values[0].marker() == 0);
    }
}
pub fn bounds_at_end(values: &[NamedZero]) -> () {
    values[values.len()].unit
}

#[derive(Copy)]
pub struct PanickingClone;
impl Clone for PanickingClone {
    #[inline(never)]
    fn clone(&self) -> Self {
        panic!("actual user Clone body executes")
    }
}
pub fn clone_panics(values: &[PanickingClone]) {
    if !values.is_empty() {
        let _ = values[0].clone();
    }
}
#[derive(Clone, Copy)]
pub struct CustomEq;
impl PartialEq for CustomEq {
    #[inline(never)]
    fn eq(&self, _: &Self) -> bool {
        false
    }
}
pub fn custom_eq_refutes(values: &[CustomEq]) {
    if !values.is_empty() {
        assert!(values[0] == values[0]);
    }
}

pub fn mutable_root(values: &mut [NamedZero]) -> usize {
    values.len()
}
pub fn competing_roots(left: &[NamedZero], right: &[NamedZero]) -> bool {
    left.len() == right.len()
}
#[derive(Clone, Copy)]
pub struct RefZero {
    empty: [&'static u16; 0],
}
pub fn reference_under_zero(values: &[RefZero]) -> usize {
    values.len()
}
#[derive(Clone, Copy)]
pub struct CoreZero {
    empty: [core::num::NonZeroU16; 0],
}
pub fn core_under_zero(values: &[CoreZero]) -> usize {
    values.len()
}
type Positive = core::pattern_type!(u32 is 1..);
#[derive(Clone, Copy)]
pub struct RefinedZero {
    empty: [Positive; 0],
}
pub fn refined_under_zero(values: &[RefinedZero]) -> usize {
    values.len()
}
pub struct DroppedZero;
impl Drop for DroppedZero {
    fn drop(&mut self) {}
}
pub fn drop_zero(values: &[DroppedZero]) -> usize {
    values.len()
}
#[derive(Clone, Copy)]
pub struct OversizedZero {
    empty: [(); 129],
}
pub fn oversized_shape(values: &[OversizedZero]) -> usize {
    values.len()
}
pub fn ambiguous_choices(values: &[[NamedZero; 2]], outer: usize, inner: usize) {
    if outer < values.len() && inner < 2 {
        assert!(values[outer][inner].marker() == 7);
    }
}
pub fn full_contains(values: &[NamedZero], needle: NamedZero) -> bool {
    values.contains(&needle)
}
pub fn full_equality(values: &[NamedZero]) -> bool {
    values == values
}

#[cfg(not(test))]
mod analyzer_only {
    use core::intrinsics::mir::*;
    unsafe extern "Rust" {
        fn opaque_unit(value: ()) -> ();
    }
    pub fn missing_body(values: &[super::NamedZero]) {
        if !values.is_empty() {
            unsafe { opaque_unit(values[0].unit) };
        }
    }
    pub fn raw_source(pointer: *const super::NamedZero, length: usize) -> usize {
        unsafe { core::slice::from_raw_parts(pointer, length) }
            .iter()
            .count()
    }
    fn empty_iterator(values: &[super::NamedZero; 0]) -> core::slice::Iter<'_, super::NamedZero> {
        values.iter()
    }
    fn exhausted(mut iterator: core::slice::Iter<'_, super::NamedZero>) -> bool {
        iterator.next().is_none()
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_exhausted() -> bool {
        mir! {
            let backing: [super::NamedZero; 0];
            let source: &[super::NamedZero; 0];
            let iterator: core::slice::Iter<'_, super::NamedZero>;
            {
                backing = []; source = &backing;
                Call(iterator = empty_iterator(source), ReturnTo(retire), UnwindUnreachable())
            }
            retire = {
                StorageDead(backing);
                Call(RET = exhausted(iterator), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }
}

#[cfg(test)]
mod native {
    use super::*;
    const ZERO: NamedZero = NamedZero {
        unit: (),
        empty: [],
    };
    #[test]
    fn positives() {
        let long = [ZERO; 129];
        for values in [&[][..], &long[..]] {
            metadata(values);
            views(values, values.len(), 0);
            for index in [0, 128, values.len()] {
                observations(values, index);
                clone_and_method(values, index);
                mutation_claim(values, index);
            }
        }
        nested(
            &[NestedZero {
                named: ZERO,
                other: ((), []),
            }; 129],
            128,
        );
        generic(
            &[GenericZero {
                empty: [],
                unit: (),
            }; 129],
            128,
        );
        let maximum = [ZERO; usize::MAX];
        observations(&maximum, usize::MAX - 1);
        clone_and_method(&maximum, usize::MAX - 1);
        layout(&[AlignedZero; usize::MAX]);
        maximum_cursor(&[AlignedZero; usize::MAX]);
    }
    #[test]
    fn mutation_guard() {
        mutation_claim(&[ZERO; 129], 128);
    }
    #[test]
    #[should_panic]
    fn alignment_negative() {
        wrong_alignment(&[AlignedZero; 129]);
    }
    #[test]
    #[should_panic]
    fn method_negative() {
        wrong_method(&[ZERO; 129]);
    }
    #[test]
    #[should_panic]
    fn bounds_negative() {
        bounds_at_end(&[]);
    }
    #[test]
    #[should_panic]
    fn clone_negative() {
        clone_panics(&[PanickingClone]);
    }
    #[test]
    #[should_panic]
    fn equality_negative() {
        custom_eq_refutes(&[CustomEq]);
    }
}
