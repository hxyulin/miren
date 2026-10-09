#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;

pub fn safe_prefix(length: usize) {
    if length <= 4 {
        let mut entries = [(1_u16, 0_u32), (2, 0), (1, 0), (3, 0)];
        if let Some(entry) = entries[..length].iter_mut().find(|entry| entry.0 == 1) {
            entry.1 += 1;
        }
        assert!(entries[0].1 == u32::from(length > 0));
        assert!(entries[1].1 == 0);
        assert!(entries[2].1 == 0);
        assert!(entries[3].1 == 0);
    }
}

pub fn ordered_updates(length: usize) {
    if length <= 4 {
        let mut entries = [(1_u16, 0_u32); 4];
        let mut next = 0_u32;
        entries[..length].iter_mut().for_each(|entry| {
            entry.1 = next;
            next += 1;
        });
        assert!(next == length as u32);
        if length > 2 {
            assert!(entries[2].1 == 2);
        }
        if length < 4 {
            assert!(entries[3].1 == 0);
        }
    }
}

pub fn empty_prefix() {
    let mut entries = [(1_u16, 0_u32); 4];
    assert!(entries[..0].iter_mut().next().is_none());
    assert!(entries[0].1 == 0);
}

pub fn bounds_failure(length: usize) {
    let mut entries = [(1_u16, 0_u32); 4];
    let _ = entries[..length].iter_mut().next();
}

pub fn overflow_failure(entries: &mut [(u16, u32); 4], length: usize, id: u16) {
    if length <= 4 {
        if let Some(entry) = entries[..length].iter_mut().find(|entry| entry.0 == id) {
            entry.1 += 1;
        }
    }
}

pub fn wrong_late_effect() {
    let mut entries = [(1_u16, 0_u32); 4];
    entries[..2].iter_mut().for_each(|entry| entry.1 = 9);
    assert!(entries[1].1 == 0);
}

pub fn whole_view_snapshot_is_unknown() {
    let mut entries = [(1_u16, 0_u32); 4];
    let region = &mut entries[..2];
    assert!(region.len() == 2);
}

pub fn floating_elements_are_unknown() {
    let mut entries = [1.0_f32; 4];
    entries[..2].iter_mut().for_each(|entry| *entry = 2.0);
}

fn initial_entries() -> [(u16, u32); 4] {
    [(1, 0); 4]
}

fn borrowed_prefix(entries: &mut [(u16, u32); 4]) {
    entries[..2].iter_mut().for_each(|entry| entry.1 = 7);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_backing_is_unknown() {
    mir! {
        let entries: [(u16, u32); 4];
        let reference: &mut [(u16, u32); 4];
        {
            StorageLive(entries);
            Call(entries = initial_entries(), ReturnTo(initialized), UnwindUnreachable())
        }
        initialized = {
            reference = &mut entries;
            StorageDead(entries);
            Call(RET = borrowed_prefix(reference), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

#[cfg(test)]
mod native {
    #[test]
    fn positive() {
        for length in 0..=4 {
            super::safe_prefix(length);
            super::ordered_updates(length);
        }
        super::empty_prefix();
        super::offset_region();
        super::find_predicate_effects();
        super::valid_nested_mutable_reborrow();
        super::valid_shared_nested_read();
    }
    #[test]
    fn bounds_panic() {
        super::bounds_failure(5);
    }
    #[test]
    fn overflow_panic() {
        let mut entries = [(1, u32::MAX); 4];
        super::overflow_failure(&mut entries, 1, 1);
    }
    #[test]
    fn late_effect_panic() {
        super::wrong_late_effect();
    }
}

pub fn offset_region() {
    let mut entries = [(1_u16, 0_u32); 4];
    entries[1..3].iter_mut().for_each(|entry| entry.1 = 8);
    assert!(entries[0].1 == 0);
    assert!(entries[1].1 == 8);
    assert!(entries[2].1 == 8);
    assert!(entries[3].1 == 0);
}

pub fn arbitrary_slice_is_unknown(entries: &mut [(u16, u32)]) {
    entries[..2].iter_mut().for_each(|entry| entry.1 = 7);
}

pub fn whole_view_assignment_is_unknown() {
    let mut entries = [(1_u16, 0_u32); 4];
    entries[..2].copy_from_slice(&[(2_u16, 1_u32); 2]);
}

pub fn multiple_interior_aliases_are_unknown(
    entries: &mut [(u16, u32); 4],
    other: &core::cell::Cell<u32>,
) {
    entries[..2]
        .iter_mut()
        .for_each(|entry| entry.1 = other.get());
}

pub fn opaque_effect_is_unknown(effect: fn(&mut [(u16, u32); 4])) {
    let mut entries = [(1_u16, 0_u32); 4];
    effect(&mut entries);
    entries[..1].iter_mut().for_each(|entry| entry.1 += 1);
    assert!(entries[0].1 == 1);
}

fn empty_iterator(entries: &mut [(u16, u32); 4]) -> core::slice::IterMut<'_, (u16, u32)> {
    entries[..0].iter_mut()
}

fn consume(iterator: core::slice::IterMut<'_, (u16, u32)>) {
    iterator.for_each(|entry| entry.1 = 7);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn exhausted_dead_source_is_unknown() {
    mir! {
        let entries: [(u16, u32); 4];
        let reference: &mut [(u16, u32); 4];
        let iterator: core::slice::IterMut<'_, (u16, u32)>;
        {
            StorageLive(entries);
            Call(entries = initial_entries(), ReturnTo(initialized), UnwindUnreachable())
        }
        initialized = {
            reference = &mut entries;
            Call(iterator = empty_iterator(reference), ReturnTo(retire), UnwindUnreachable())
        }
        retire = {
            StorageDead(entries);
            Call(RET = consume(iterator), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn forbidden_write(input: &&mut (u16, u32)) -> bool {
    mir! {
        let mutable: &mut (u16, u32);
        { mutable = *input; (*mutable).1 = 99_u32; RET = true; Return() }
    }
}

pub fn shared_predicate_write_is_unknown() {
    let mut entries = [(1_u16, 0_u32); 4];
    let _ = entries[..2].iter_mut().find(forbidden_write);
}

pub fn find_predicate_effects() {
    let mut entries = [(1_u16, 0_u32), (2, 0), (3, 0), (4, 0)];
    let mut visited = 0_u32;
    let found = entries[..3].iter_mut().find(|entry| {
        visited += 1;
        entry.0 == 2
    });
    if let Some(entry) = found {
        entry.1 = visited;
    }
    assert!(visited == 2);
    assert!(entries[0].1 == 0);
    assert!(entries[1].1 == 2);
    assert!(entries[2].1 == 0);
    assert!(entries[3].1 == 0);
}

pub fn wrong_predicate_order() {
    let mut entries = [(1_u16, 0_u32), (2, 0), (3, 0), (4, 0)];
    let mut visited = 0_u32;
    let _ = entries[..3].iter_mut().find(|entry| {
        visited += 1;
        entry.0 == 2
    });
    assert!(visited == 1);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn forged_nested_value() -> u32 {
    mir! {
     let value:u32;
     let inner:&mut u32;
     let outer:&&mut u32;
     let extracted:&mut u32;
     {
      value=1; inner=&mut value; outer=&inner; extracted=*outer; *extracted=7;
      RET=value; Return()
     }
    }
}
pub fn forged_shared_nested_write() {
    assert!(forged_nested_value() == 7);
}
fn mutate(value: &mut u32) {
    *value = 7;
}
pub fn valid_nested_mutable_reborrow() {
    let mut value = 1u32;
    let mut inner = &mut value;
    let outer = &mut inner;
    mutate(&mut **outer);
    assert!(value == 7);
}
pub fn valid_shared_nested_read() {
    let mut value = 17u32;
    let inner = &mut value;
    let outer = &inner;
    assert!(**outer == 17);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn forged_return<'a>(input: &'a &'a mut u32) -> &'a mut u32 {
    mir! {{ RET = *input; Return() }}
}

pub fn shared_handle_escape_is_unknown() {
    let mut value = 1_u32;
    let inner = &mut value;
    let outer = &inner;
    let escaped = forged_return(outer);
    *escaped = 7;
    assert!(value == 7);
}

fn consume_fold(iterator: core::slice::IterMut<'_, (u16, u32)>) -> u32 {
    iterator.fold(0, |_, entry| entry.1)
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn exhausted_dead_fold_is_unknown() -> u32 {
    mir! {
        let entries: [(u16, u32); 4];
        let reference: &mut [(u16, u32); 4];
        let iterator: core::slice::IterMut<'_, (u16, u32)>;
        {
            StorageLive(entries);
            Call(entries = initial_entries(), ReturnTo(initialized), UnwindUnreachable())
        }
        initialized = {
            reference = &mut entries;
            Call(iterator = empty_iterator(reference), ReturnTo(retire), UnwindUnreachable())
        }
        retire = {
            StorageDead(entries);
            Call(RET = consume_fold(iterator), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}
