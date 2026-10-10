#![no_std]
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]

// Prospective fixture; analyzer expectations remain provisional.

#[inline(never)]
fn composite_iterator(values: &[(u16, u16)]) -> core::slice::Iter<'_, (u16, u16)> {
    values.iter()
}

#[inline(never)]
fn selected_field(iterator: &mut core::slice::Iter<'_, (u16, u16)>, index: usize) -> u16 {
    iterator.nth(index).unwrap().0
}

pub fn metadata(values: &[(u16, u16)]) {
    let mut iterator = values.iter();
    assert!(iterator.len() == values.len());
    assert!(iterator.size_hint() == (values.len(), Some(values.len())));
    assert!(iterator.clone().count() == values.len());
    assert!(iterator.by_ref().count() == values.len());
    assert!(iterator.len() == 0);
    assert!(iterator.next().is_none());
    assert!(iterator.next_back().is_none());
}

pub fn symbolic_nth(values: &[(u16, u16)], index: usize) {
    let mut iterator = values.iter();
    let selected = iterator.nth(index);
    if index < values.len() {
        let pair = selected.unwrap();
        assert!(pair.0 == values[index].0);
        assert!(pair.1 == values[index].1);
        assert!(iterator.len() == values.len() - index - 1);
    } else {
        assert!(selected.is_none());
        assert!(iterator.len() == 0);
    }
}

pub fn reverse_and_mixed(values: &[(u16, u16)], index: usize) {
    let mut iterator = values.iter();
    if values.len() >= 2 {
        assert!(iterator.next().unwrap().0 == values[0].0);
        assert!(iterator.next_back().unwrap().1 == values[values.len() - 1].1);
        assert!(iterator.len() == values.len() - 2);
        if index < iterator.len() {
            let pair = iterator.nth_back(index).unwrap();
            assert!(pair.0 == values[values.len() - 2 - index].0);
            assert!(pair.1 == values[values.len() - 2 - index].1);
        }
    }
}

pub fn cloned_cursors(values: &[(u16, u16)]) {
    let mut original = values.iter();
    let mut cloned = original.clone();
    if !values.is_empty() {
        assert!(cloned.next_back().unwrap().1 == values[values.len() - 1].1);
        assert!(original.len() == values.len());
        assert!(original.next().unwrap().0 == values[0].0);
        assert!(original.len() == cloned.len());
    }
}

pub fn returned_iterator(values: &[(u16, u16)], index: usize) {
    if index < values.len() {
        let mut iterator = composite_iterator(values);
        let pair = iterator.nth(index).unwrap();
        assert!(pair.0 == values[index].0);
        assert!(pair.1 == values[index].1);
    }
}

pub fn array_bool_char(values: &[[(bool, char); 2]], index: usize) {
    if index < values.len() {
        let selected = values.iter().nth(index).unwrap();
        assert!(selected[0].0 == values[index][0].0);
        assert!(selected[1].0 == values[index][1].0);
        assert!(selected[0].1 == values[index][0].1);
        assert!(selected[1].1 == values[index][1].1);
        let code = selected[1].1 as u32;
        assert!(code <= 0x10ffff);
        assert!(code < 0xd800 || code > 0xdfff);
    }
}

pub fn float_field_bits(values: &[(f32, f64)], index: usize) {
    if index < values.len() {
        let selected = values.iter().nth(index).unwrap();
        assert!(selected.0.to_bits() == values[index].0.to_bits());
        assert!(selected.1.to_bits() == values[index].1.to_bits());
        if selected.0.is_nan() {
            assert!(values[index].0.is_nan());
        }
        if selected.1.to_bits() == 0x8000000000000000 {
            assert!(selected.1 == 0.0);
        }
    }
}

pub fn large_view(values: &[(u16, u16)]) {
    if values.len() > 128 {
        let mut iterator = values.iter();
        assert!(iterator.nth(128).unwrap().0 == values[128].0);
        assert!(iterator.len() == values.len() - 129);
    }
}

pub fn oversized_skip(values: &[(u16, u16)]) {
    let mut iterator = values.iter();
    assert!(iterator.nth(usize::MAX).is_none());
    assert!(iterator.next().is_none());
    assert!(iterator.next_back().is_none());
    assert!(iterator.size_hint() == (0, Some(0)));
}

pub fn mutation_claim(values: &[(u16, u16)]) {
    if values.len() > 128 {
        let mut iterator = values.iter();
        assert!(selected_field(&mut iterator, 128) == values[128].0);
    }
}

// This keeps the arbitrary first-field false claim, now exercised through the real cursor.
pub fn wrong_first_field(values: &[(u16, u16)]) {
    if !values.is_empty() {
        assert!(values.iter().next().unwrap().0 == 0);
    }
}

pub fn open_aggregate_slice(values: &[(u16, u16)]) {
    if !values.is_empty() {
        assert!(values[0].0 == 0);
    }
}

pub fn wrong_clone(values: &[(u16, u16)]) {
    if !values.is_empty() {
        let original = values.iter();
        let mut cloned = original.clone();
        let _ = cloned.next();
        assert!(original.len() == cloned.len());
    }
}

pub fn unguarded_nth(values: &[(u16, u16)], index: usize) -> u16 {
    values.iter().nth(index).unwrap().0
}

pub fn float_numeric_reflexivity(values: &[(f32, f64)]) {
    if !values.is_empty() {
        let selected = values.iter().next().unwrap();
        assert!(selected.0 == selected.0);
    }
}

pub fn mutable_root(values: &mut [(u16, u16)]) {
    let _ = values.iter_mut().next();
}

pub fn competing_roots(left: &[(u16, u16)], right: &[(u16, u16)]) -> bool {
    left.iter().len() == right.iter().len()
}

// Preserve exact old sources: promote only after an actual admitted cursor/body path.
pub fn deferred_iteration(values: &[(u16, u16)], index: usize) -> Option<&(u16, u16)> {
    values.iter().nth(index)
}

pub fn aggregate_input(values: &[(u16, bool)]) {
    let _ = values.iter().next();
}

#[cfg(not(test))]
mod analyzer_only {
    use core::intrinsics::mir::*;

    unsafe extern "Rust" {
        fn opaque_field(value: u16) -> u16;
    }

    pub fn missing_invoked_body(values: &[(u16, u16)]) {
        if let Some(pair) = values.iter().next() {
            let result = unsafe { opaque_field(pair.0) };
            assert!(result == pair.0);
        }
    }

    pub fn raw_source(pointer: *const (u16, u16), length: usize) -> usize {
        // Analysis-only, no validity or allocation premise supplied.
        let values = unsafe { core::slice::from_raw_parts(pointer, length) };
        values.iter().count()
    }

    fn iterator_len(iterator: &core::slice::Iter<'_, (u16, u16)>) -> usize {
        iterator.len()
    }

    fn iterator_next(mut iterator: core::slice::Iter<'_, (u16, u16)>) -> bool {
        iterator.next().is_none()
    }

    fn empty_iterator(values: &[(u16, u16); 0]) -> core::slice::Iter<'_, (u16, u16)> {
        values.iter()
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn copied_handle_live(values: &[(u16, u16)]) -> usize {
        mir! {
            let iterator: core::slice::Iter<'_, (u16, u16)>;
            let borrow: &core::slice::Iter<'_, (u16, u16)>;
            {
                Call(iterator = super::composite_iterator(values),
                    ReturnTo(retire), UnwindUnreachable())
            }
            retire = {
                StorageDead(values);
                borrow = &iterator;
                Call(RET = iterator_len(borrow), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_empty_metadata() -> usize {
        mir! {
            let backing: [(u16, u16); 0];
            let source: &[(u16, u16); 0];
            let iterator: core::slice::Iter<'_, (u16, u16)>;
            let borrow: &core::slice::Iter<'_, (u16, u16)>;
            {
                backing = [];
                source = &backing;
                Call(iterator = empty_iterator(source), ReturnTo(retire), UnwindUnreachable())
            }
            retire = {
                StorageDead(backing);
                borrow = &iterator;
                Call(RET = iterator_len(borrow), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_exhausted_next() -> bool {
        mir! {
            let backing: [(u16, u16); 0];
            let source: &[(u16, u16); 0];
            let iterator: core::slice::Iter<'_, (u16, u16)>;
            {
                backing = [];
                source = &backing;
                Call(iterator = empty_iterator(source), ReturnTo(retire), UnwindUnreachable())
            }
            retire = {
                StorageDead(backing);
                Call(RET = iterator_next(iterator), ReturnTo(done), UnwindUnreachable())
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
        let long = [(3_u16, 7_u16); 129];
        for values in [&[][..], &[(3, 7), (5, 11)][..], &long[..]] {
            metadata(values);
            cloned_cursors(values);
            large_view(values);
            oversized_skip(values);
            mutation_claim(values);
            for index in [0, 1, 128, values.len(), usize::MAX] {
                symbolic_nth(values, index);
                reverse_and_mixed(values, index);
                returned_iterator(values, index);
                let _ = deferred_iteration(values, index);
            }
        }
        aggregate_input(&[(7, true); 129]);
        for unicode in ['\0', '\u{d7ff}', '\u{e000}', '\u{10ffff}'] {
            array_bool_char(&[[(false, '\0'), (true, unicode)]; 129], 128);
        }
        array_bool_char(&[], 0);
        float_field_bits(&[], 0);
        for value in [
            (
                f32::from_bits(0x7fc00015),
                f64::from_bits(0x7ff8000000000015),
            ),
            (-0.0, -0.0),
            (0.0, 0.0),
        ] {
            float_field_bits(&[value; 129], 128);
        }
    }

    #[test]
    fn mutation_guard() {
        mutation_claim(&[(3, 7); 129]);
    }

    #[test]
    #[should_panic]
    fn first_field_failure() {
        wrong_first_field(&[(3, 7); 129]);
    }

    #[test]
    #[should_panic]
    fn unchanged_aggregate_failure() {
        open_aggregate_slice(&[(3, 7); 129]);
    }

    #[test]
    #[should_panic]
    fn clone_failure() {
        wrong_clone(&[(3, 7)]);
    }

    #[test]
    #[should_panic]
    fn nth_failure() {
        let _ = unguarded_nth(&[], 0);
    }

    #[test]
    #[should_panic]
    fn nan_failure() {
        float_numeric_reflexivity(&[(f32::NAN, 0.0)]);
    }
}
