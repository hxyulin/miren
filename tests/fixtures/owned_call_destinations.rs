#![no_std]
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
use core::intrinsics::mir::*;

#[inline(never)]
pub fn replacement() -> u16 {
    19
}
#[derive(Clone, Copy)]
pub struct Record {
    pub left: u16,
    pub right: u16,
}
#[derive(Clone, Copy)]
pub struct Product {
    pub records: [Record; 2],
    pub marker: u16,
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn array_call(mut values: [u16; 2], index: usize) -> [u16; 2] {
    mir! {
        { Call(values[index] = replacement(), ReturnTo(done), UnwindUnreachable()) }
        done = { RET = values; Return() }
    }
}
pub fn array_destination(values: [u16; 2], index: usize) {
    if index < 2 {
        let changed = array_call(values, index);
        assert!(changed[index] == 19);
        assert!(changed[index ^ 1] == values[index ^ 1]);
    }
}
pub fn false_value(values: [u16; 2], index: usize) {
    if index < 2 {
        assert!(array_call(values, index)[index] == 20);
    }
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn tuple_call(mut values: ([u16; 2], u16), index: usize) -> ([u16; 2], u16) {
    mir! {
        { Call(values.0[index] = replacement(), ReturnTo(done), UnwindUnreachable()) }
        done = { RET = values; Return() }
    }
}
pub fn tuple_destination(values: ([u16; 2], u16), index: usize) {
    if index < 2 {
        let changed = tuple_call(values, index);
        assert!(changed.0[index] == 19);
        assert!(changed.1 == values.1);
    }
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn struct_call(mut values: Product, index: usize) -> Product {
    mir! {
        { Call(values.records[index].left = replacement(), ReturnTo(done), UnwindUnreachable()) }
        done = { RET = values; Return() }
    }
}
pub fn struct_destination(values: Product, index: usize) {
    if index < 2 {
        let changed = struct_call(values, index);
        let selected = changed.records[index];
        let before = values.records[index];
        assert!(selected.left == 19);
        assert!(selected.right == before.right);
        assert!(changed.marker == values.marker);
    }
}
#[inline(never)]
fn advance(index: &mut usize) -> u16 {
    *index ^= 1;
    19
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn changing_index(mut values: [u16; 2], mut index: usize) -> ([u16; 2], usize) {
    mir! {
        let pointer: &mut usize;
        {
            pointer = &mut index;
            Call(values[index] = advance(pointer), ReturnTo(done), UnwindUnreachable())
        }
        done = { RET = (values, index); Return() }
    }
}
pub fn pre_call_destination() {
    let (values, index) = changing_index([3, 7], 0);
    assert!(values[0] == 19);
    assert!(values[1] == 7);
    assert!(index == 1);
}
pub fn post_call_destination() {
    let (values, index) = changing_index([3, 7], 0);
    assert!(values[0] == 3);
    assert!(values[1] == 19);
    assert!(index == 1);
}
#[inline(never)]
fn refresh(values: &mut [u16; 2]) -> u16 {
    values[0] = 11;
    values[1] = 41;
    19
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn refreshed_call(mut values: [u16; 2], index: usize) -> [u16; 2] {
    mir! {
        let pointer: &mut [u16; 2];
        {
            pointer = &mut values;
            Call(values[index] = refresh(pointer), ReturnTo(done), UnwindUnreachable())
        }
        done = { RET = values; Return() }
    }
}
pub fn current_owner() {
    let values = refreshed_call([3, 7], 0);
    assert!(values == [19, 41]);
}
#[inline(never)]
fn count_once(count: &mut u16) -> u16 {
    *count += 1;
    19
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn counted_call(mut values: [u16; 2], index: usize) -> ([u16; 2], u16) {
    mir! {
        let count: u16;
        let pointer: &mut u16;
        {
            count = 0;
            pointer = &mut count;
            Call(values[index] = count_once(pointer), ReturnTo(done), UnwindUnreachable())
        }
        done = { RET = (values, count); Return() }
    }
}
pub fn once_only(values: [u16; 2], index: usize) {
    if index < 2 {
        let (changed, count) = counted_call(values, index);
        assert!(changed[index] == 19);
        assert!(count == 1);
    }
}
#[inline(never)]
fn choose(flag: bool) -> u16 {
    if flag { 19 } else { 23 }
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn branched_call(mut values: [u16; 2], index: usize, flag: bool) -> [u16; 2] {
    mir! {
        { Call(values[index] = choose(flag), ReturnTo(done), UnwindUnreachable()) }
        done = { RET = values; Return() }
    }
}
pub fn branch_results(values: [u16; 2], index: usize, flag: bool) {
    if index < 2 {
        assert!(branched_call(values, index, flag)[index] == if flag { 19 } else { 23 });
    }
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn duplicate_call(mut values: [[u16; 2]; 2], index: usize) -> [[u16; 2]; 2] {
    mir! {
        { Call(values[index][index] = replacement(), ReturnTo(done), UnwindUnreachable()) }
        done = { RET = values; Return() }
    }
}
pub fn repeated_index(values: [[u16; 2]; 2], index: usize) {
    if index < 2 {
        let changed = duplicate_call(values, index);
        let row = changed[index];
        let before = values[index];
        assert!(row[index] == 19);
        assert!(row[index ^ 1] == before[index ^ 1]);
    }
}
#[inline(never)]
fn panic_unit() {
    panic!("actual zero-sized replacement body");
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn unit_call(mut values: [(); 2], index: usize) -> [(); 2] {
    mir! {
        { Call(values[index] = panic_unit(), ReturnTo(done), UnwindUnreachable()) }
        done = { RET = values; Return() }
    }
}
pub fn unit_effect(index: usize) {
    if index < 2 {
        let _ = unit_call([(); 2], index);
    }
}
#[cfg(not(test))]
mod analyzer_only {
    use super::*;
    unsafe extern "Rust" {
        fn unavailable() -> u16;
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn missing_call(mut values: [u16; 2], index: usize) -> [u16; 2] {
        mir! {
            { Call(values[index] = unavailable(), ReturnTo(done), UnwindUnreachable()) }
            done = { RET = values; Return() }
        }
    }
    pub fn missing_body(values: [u16; 2], index: usize) {
        if index < 2 {
            let _ = missing_call(values, index);
        }
    }
    #[inline(never)]
    fn checked(index: usize) -> u16 {
        assert!(index < 2);
        19
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn retroactive_bound(mut values: [u16; 2], index: usize) -> [u16; 2] {
        mir! {
            { Call(values[index] = checked(index), ReturnTo(done), UnwindUnreachable()) }
            done = { RET = values; Return() }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn restricted_call(
        mut values: ([u16; 2], [&'static u16; 0]),
        index: usize,
    ) -> ([u16; 2], [&'static u16; 0]) {
        mir! {
            { Call(values.0[index] = replacement(), ReturnTo(done), UnwindUnreachable()) }
            done = { RET = values; Return() }
        }
    }
    pub fn unsupported_zero(values: ([u16; 2], [&'static u16; 0]), index: usize) {
        if index < 2 {
            let _ = restricted_call(values, index);
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn dead_call(mut values: [u16; 2], index: usize) -> [u16; 2] {
        mir! {
            {
                StorageDead(values);
                Call(values[index] = replacement(), ReturnTo(done), UnwindUnreachable())
            }
            done = { RET = values; Return() }
        }
    }
    pub fn dead_owner(values: [u16; 2], index: usize) {
        if index < 2 {
            let _ = dead_call(values, index);
        }
    }
    #[inline(never)]
    fn never_returns() -> u16 {
        panic!("actual non-returning replacement");
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn invalid_fixed_prefix(mut values: [[u16; 2]; 2], index: usize) -> [[u16; 2]; 2] {
        mir! {
            let fixed: usize;
            {
                fixed = 2;
                Call(values[fixed][index] = never_returns(), ReturnTo(done), UnwindUnreachable())
            }
            done = { RET = values; Return() }
        }
    }
    #[inline(never)]
    fn redirect<'a>(pointer: &mut &'a mut u16, other: &'a mut u16) -> u16 {
        *pointer = other;
        19
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn redirect_call(mut left: u16, mut right: u16) -> (u16, u16) {
        mir! {
            let pointer: &mut u16;
            let other: &mut u16;
            let indirect: &mut &mut u16;
            {
                pointer = &mut left;
                other = &mut right;
                indirect = &mut pointer;
                Call(*pointer = redirect(indirect, other), ReturnTo(done), UnwindUnreachable())
            }
            done = { RET = (left, right); Return() }
        }
    }
    pub fn dereference_correct() {
        let (left, right) = redirect_call(3, 7);
        assert!(left == 19);
        assert!(right == 7);
    }
    pub fn dereference_false() {
        let (left, right) = redirect_call(3, 7);
        assert!(left == 3);
        assert!(right == 19);
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn retained(values: &mut [u16; 2], index: usize) {
        mir! {
            { Call((*values)[index] = replacement(), ReturnTo(done), UnwindUnreachable()) }
            done = { Return() }
        }
    }
}
#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn positives() {
        pre_call_destination();
        current_owner();
        for index in 0..2 {
            array_destination([3, 7], index);
            tuple_destination(([3, 7], 11), index);
            struct_destination(
                Product {
                    records: [Record { left: 3, right: 7 }; 2],
                    marker: 11,
                },
                index,
            );
            once_only([3, 7], index);
            branch_results([3, 7], index, true);
            branch_results([3, 7], index, false);
            repeated_index([[3, 7]; 2], index);
        }
    }
    #[test]
    fn mutation_guard() {
        array_destination([3, 7], 1);
    }
    #[test]
    #[should_panic]
    fn false_claim() {
        false_value([3, 7], 1);
    }
    #[test]
    #[should_panic]
    fn wrong_post_call_address() {
        post_call_destination();
    }
    #[test]
    #[should_panic]
    fn actual_unit_panic() {
        unit_effect(0);
    }
}
