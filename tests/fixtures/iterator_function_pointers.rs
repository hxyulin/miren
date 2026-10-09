#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;

fn decimal(accumulator: u16, digit: u16) -> u16 {
    accumulator * 10 + digit
}

fn borrowed_decimal(accumulator: u16, digit: &u16) -> u16 {
    accumulator * 10 + *digit
}

pub fn owned_fold_and_reverse_fold_keep_order() {
    let callback: fn(u16, u16) -> u16 = decimal;
    assert!([1_u16, 2, 3].into_iter().fold(0, callback) == 123);
    assert!([1_u16, 2, 3].into_iter().rfold(0, callback) == 321);
}

pub fn borrowed_fold_keeps_order() {
    let callback: fn(u16, &u16) -> u16 = borrowed_decimal;
    assert!([1_u16, 2, 3].iter().fold(0, callback) == 123);
}

fn stamp(value: &mut u16) {
    *value = *value * 10 + 1;
}

pub fn for_each_preserves_last_element_effect() {
    let callback: fn(&mut u16) = stamp;
    let mut values = [1_u16, 2, 3];
    values.iter_mut().for_each(callback);
    assert!(values == [11, 21, 31]);
}

fn increment(value: &mut u16) {
    *value += 1;
}
fn double(value: &mut u16) {
    *value *= 2;
}

pub fn selected_pointer_callbacks_preserve_each_branch(flag: bool) {
    let callback: fn(&mut u16) = if flag { increment } else { double };
    let mut values = [1_u16, 2, 3];
    values.iter_mut().for_each(callback);
    if flag {
        assert!(values == [2, 3, 4]);
    } else {
        assert!(values == [2, 4, 6]);
    }
}

fn bounded(value: u16) -> bool {
    value < 4
}

pub fn owned_predicate_runs_actual_body() {
    let callback: fn(u16) -> bool = bounded;
    assert!([1_u16, 2, 3].into_iter().all(callback));
}

fn find_three(value: &u16) -> bool {
    assert!(*value != 5);
    *value == 3
}

pub fn predicate_short_circuit_preserves_cursor() {
    let callback: fn(&u16) -> bool = find_three;
    let values = [1_u16, 3, 5];
    let mut iterator = values.iter();
    assert!(iterator.any(callback));
    assert!(*iterator.next().unwrap() == 5);
}

pub fn a_late_predicate_panic_is_not_skipped() {
    let callback: fn(&u16) -> bool = find_three;
    assert!([1_u16, 2, 5].iter().any(callback));
}

fn map_three(value: &u16) -> Option<u16> {
    assert!(*value != 5);
    if *value == 3 { Some(*value) } else { None }
}

pub fn find_map_pointer_keeps_order_and_short_circuit() {
    let callback: fn(&u16) -> Option<u16> = map_three;
    let values = [1_u16, 3, 5];
    let mut iterator = values.iter();
    assert!(iterator.find_map(callback).unwrap() == 3);
    assert!(*iterator.next().unwrap() == 5);
}

pub fn wrong_fold_result_is_refuted() {
    let callback: fn(u16, u16) -> u16 = decimal;
    assert!([1_u16, 2, 3].into_iter().fold(0, callback) == 321);
}

pub fn arbitrary_pointer_input_is_unknown(callback: fn(u16) -> bool) {
    assert!([1_u16, 2, 3].into_iter().all(callback));
}

pub fn reference_to_callback_remains_unknown() {
    let callback: fn(u16) -> bool = bounded;
    assert!([1_u16, 2, 3].into_iter().all(&callback));
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn unsupported_unsafe_signature_cast(callback: unsafe fn(u16) -> bool) -> fn(u16) -> bool {
    mir! {{ RET = CastTransmute(callback); Return() }}
}

pub fn unsafe_callback_is_not_retyped_as_safe() {
    let callback: unsafe fn(u16) -> bool = bounded;
    let callback = unsupported_unsafe_signature_cast(callback);
    assert!([1_u16, 2, 3].into_iter().all(callback));
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn unsupported_abi_cast(callback: extern "C" fn(u16) -> bool) -> fn(u16) -> bool {
    mir! {{ RET = CastTransmute(callback); Return() }}
}

pub fn non_rust_callback_is_not_retyped_as_rust(callback: extern "C" fn(u16) -> bool) {
    let callback = unsupported_abi_cast(callback);
    assert!([1_u16, 2, 3].into_iter().all(callback));
}

#[cfg(test)]
#[test]
fn native_callbacks_follow_order_and_preserve_effects() {
    owned_fold_and_reverse_fold_keep_order();
    borrowed_fold_keeps_order();
    for_each_preserves_last_element_effect();
    selected_pointer_callbacks_preserve_each_branch(false);
    selected_pointer_callbacks_preserve_each_branch(true);
    owned_predicate_runs_actual_body();
    predicate_short_circuit_preserves_cursor();
    find_map_pointer_keeps_order_and_short_circuit();
}
