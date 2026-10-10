#![no_std]
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
use core::intrinsics::mir::*;

#[inline(never)]
pub fn replacement() -> u16 {
    19
}
#[inline(never)]
fn redirect<'a>(pointer: &mut &'a mut u16, other: &'a mut u16) -> u16 {
    *pointer = other;
    19
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn update(mut left: u16, mut right: u16) -> (u16, u16) {
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
pub fn pre_call_deref() {
    let (left, right) = update(3, 7);
    assert!(left == 19);
    assert!(right == 7);
}
pub fn post_call_deref() {
    let (left, right) = update(3, 7);
    assert!(left == 3);
    assert!(right == 19);
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn scalar_call(mut value: u16) -> u16 {
    mir! {
        let target: &mut u16;
        { target = &mut value; Call(*target = replacement(), ReturnTo(done), UnwindUnreachable()) }
        done = { RET = value; Return() }
    }
}
pub fn mutation_claim(value: u16) {
    assert!(scalar_call(value) == 19);
}
pub fn wrong_value(value: u16) {
    assert!(scalar_call(value) == 20);
}
#[derive(Clone, Copy)]
pub struct Record {
    pub left: u16,
    pub right: u16,
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn field_call(mut value: Record) -> Record {
    mir! {
        let target: &mut Record;
        {
            target = &mut value;
            Call((*target).left = replacement(), ReturnTo(done), UnwindUnreachable())
        }
        done = { RET = value; Return() }
    }
}
pub fn field_destination(value: Record) {
    let changed = field_call(value);
    assert!(changed.left == 19);
    assert!(changed.right == value.right);
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn tuple_call(mut value: (u16, u16)) -> (u16, u16) {
    mir! {
        let target: &mut (u16, u16);
        {
            target = &mut value;
            Call((*target).0 = replacement(), ReturnTo(done), UnwindUnreachable())
        }
        done = { RET = value; Return() }
    }
}
pub fn tuple_destination(value: (u16, u16)) {
    let changed = tuple_call(value);
    assert!(changed.0 == 19);
    assert!(changed.1 == value.1);
}
#[inline(never)]
fn refresh(values: &mut [u16; 2]) -> u16 {
    values[0] = 11;
    values[1] = 41;
    19
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn refreshed_call(mut values: [u16; 2]) -> [u16; 2] {
    mir! {
        let target: &mut [u16; 2];
        let index: usize;
        {
            target = &mut values;
            index = 0;
            Call((*target)[index] = refresh(target), ReturnTo(done), UnwindUnreachable())
        }
        done = { RET = values; Return() }
    }
}
pub fn current_owner(values: [u16; 2]) {
    assert!(refreshed_call(values) == [19, 41]);
}
#[inline(never)]
fn advance(index: &mut usize) -> u16 {
    *index ^= 1;
    19
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn indexed_call(mut values: [u16; 2]) -> ([u16; 2], usize) {
    mir! {
        let target: &mut [u16; 2];
        let index: usize;
        let pointer: &mut usize;
        {
            target = &mut values;
            index = 0;
            pointer = &mut index;
            Call((*target)[index] = advance(pointer), ReturnTo(done), UnwindUnreachable())
        }
        done = { RET = (values, index); Return() }
    }
}
pub fn base_and_index(values: [u16; 2]) {
    let (changed, index) = indexed_call(values);
    assert!(changed[0] == 19);
    assert!(changed[1] == values[1]);
    assert!(index == 1);
}
#[inline(never)]
fn count_once(count: &mut u16) -> u16 {
    *count += 1;
    19
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn counted_call(mut value: u16) -> (u16, u16) {
    mir! {
        let target: &mut u16;
        let count: u16;
        let pointer: &mut u16;
        {
            target = &mut value;
            count = 0;
            pointer = &mut count;
            Call(*target = count_once(pointer), ReturnTo(done), UnwindUnreachable())
        }
        done = { RET = (value, count); Return() }
    }
}
pub fn once_only(value: u16) {
    let (changed, count) = counted_call(value);
    assert!(changed == 19);
    assert!(count == 1);
}
#[inline(never)]
fn choose(flag: bool) -> u16 {
    if flag { 19 } else { 23 }
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn branched_call(mut value: u16, flag: bool) -> u16 {
    mir! {
        let target: &mut u16;
        { target = &mut value; Call(*target = choose(flag), ReturnTo(done), UnwindUnreachable()) }
        done = { RET = value; Return() }
    }
}
pub fn branch_results(value: u16, flag: bool) {
    assert!(branched_call(value, flag) == if flag { 19 } else { 23 });
}
#[inline(never)]
fn panic_unit() {
    panic!("actual tracked zero-sized replacement body");
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn unit_effect() {
    mir! {
        let value: ();
        let target: &mut ();
        {
            value = ();
            target = &mut value;
            Call(*target = panic_unit(), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}
#[cfg(not(test))]
mod analyzer_only {
    use super::*;
    unsafe extern "Rust" {
        fn unavailable() -> u16;
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn missing_body(mut value: u16) -> u16 {
        mir! {
            let target: &mut u16;
            {
                target = &mut value;
                Call(*target = unavailable(), ReturnTo(done), UnwindUnreachable())
            }
            done = { RET = value; Return() }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    fn inherited_call(target: &mut u16) {
        mir! {
            { Call(*target = replacement(), ReturnTo(done), UnwindUnreachable()) }
            done = { Return() }
        }
    }
    pub fn inherited(mut value: Record) {
        inherited_call(&mut value.left);
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn shared(target: &u16) {
        mir! {
            { Call(*target = replacement(), ReturnTo(done), UnwindUnreachable()) }
            done = { Return() }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn raw(target: *mut u16) {
        mir! {
            { Call(*target = replacement(), ReturnTo(done), UnwindUnreachable()) }
            done = { Return() }
        }
    }
    static mut WORD: u16 = 3;
    pub fn static_target() {
        inherited_call(unsafe { &mut *core::ptr::addr_of_mut!(WORD) });
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_owner(mut value: u16) -> u16 {
        mir! {
            let target: &mut u16;
            {
                target = &mut value;
                StorageDead(value);
                Call(*target = replacement(), ReturnTo(done), UnwindUnreachable())
            }
            done = { RET = value; Return() }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn symbolic_index(mut values: [u16; 2], index: usize) -> [u16; 2] {
        mir! {
            let target: &mut [u16; 2];
            {
                target = &mut values;
                Call((*target)[index] = replacement(), ReturnTo(done), UnwindUnreachable())
            }
            done = { RET = values; Return() }
        }
    }
    pub fn bounded_symbolic_index(values: [u16; 2], index: usize) {
        if index < 2 {
            let changed = symbolic_index(values, index);
            assert!(changed[index] == 19);
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn unsupported_zero(mut value: (u16, [&'static u16; 0])) -> (u16, [&'static u16; 0]) {
        mir! {
            let target: &mut (u16, [&'static u16; 0]);
            {
                target = &mut value;
                Call((*target).0 = replacement(), ReturnTo(done), UnwindUnreachable())
            }
            done = { RET = value; Return() }
        }
    }
}
#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn positives() {
        pre_call_deref();
        mutation_claim(3);
        field_destination(Record { left: 3, right: 7 });
        tuple_destination((3, 7));
        current_owner([3, 7]);
        base_and_index([3, 7]);
        once_only(3);
        branch_results(3, true);
        branch_results(3, false);
    }
    #[test]
    fn mutation_guard() {
        mutation_claim(3);
    }
    #[test]
    #[should_panic]
    fn false_address() {
        post_call_deref();
    }
    #[test]
    #[should_panic]
    fn false_value() {
        wrong_value(3);
    }
    #[test]
    #[should_panic]
    fn actual_unit_panic() {
        unit_effect();
    }
}
