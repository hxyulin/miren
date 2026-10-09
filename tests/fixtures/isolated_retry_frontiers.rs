#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;
use core::sync::atomic::{AtomicPtr, Ordering};

static LINK: AtomicPtr<u8> = AtomicPtr::new(core::ptr::null_mut());

pub fn retry_value() -> u32 {
    loop {
        if LINK
            .compare_exchange_weak(
                core::ptr::null_mut(),
                core::ptr::null_mut(),
                Ordering::Relaxed,
                Ordering::Relaxed,
            )
            .is_ok()
        {
            return 7;
        }
    }
}

#[inline(never)]
fn reached_after_retry(value: u32) {
    assert!(value == 7);
}

pub fn retry_then_return() {
    reached_after_retry(retry_value());
}

pub fn retry_then_panic() {
    reached_after_retry(retry_value());
    panic!("actual completed retry path reaches this panic");
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn unsupported_pointer_read(pointer: *const u32) -> u32 {
    mir! { { RET = *pointer; Return() } }
}

pub fn retry_then_unsupported() {
    reached_after_retry(retry_value());
    let _ = unsupported_pointer_read(8_usize as *const u32);
}

pub fn retry_without_return() -> ! {
    loop {
        let _ = LINK.compare_exchange_weak(
            1_usize as *mut u8,
            core::ptr::null_mut(),
            Ordering::Relaxed,
            Ordering::Relaxed,
        );
    }
}

pub fn ordinary_finite_loop() {
    let mut value = 0_u32;
    while value < 12 {
        value += 1;
    }
    assert!(value == 12);
}

pub fn independent_spurious_failures_can_disagree() {
    let first = LINK
        .compare_exchange_weak(
            core::ptr::null_mut(),
            core::ptr::null_mut(),
            Ordering::Relaxed,
            Ordering::Relaxed,
        )
        .is_ok();
    let second = LINK
        .compare_exchange_weak(
            core::ptr::null_mut(),
            core::ptr::null_mut(),
            Ordering::Relaxed,
            Ordering::Relaxed,
        )
        .is_ok();
    assert!(first == second);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn frame_reference() -> &'static u32 {
    mir! {
        let owned: u32;
        { owned = 7; RET = &owned; Return() }
    }
}

pub fn retry_then_frame_escape() -> &'static u32 {
    reached_after_retry(retry_value());
    frame_reference()
}

#[cfg(test)]
#[test]
fn ordinary_loop_and_completed_retry_value_are_native_correct() {
    ordinary_finite_loop();
    retry_then_return();
}
