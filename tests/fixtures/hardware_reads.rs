#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;
use core::sync::atomic::{AtomicU16, Ordering};

const REGISTER: usize = 0x5802_080c;
const WRITE_ONLY: usize = 0x5802_0818;

#[repr(transparent)]
#[derive(Clone, Copy)]
struct Register(u32);
#[derive(Clone, Copy)]
struct Lookalike(u32);
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Narrow(u16);
#[repr(transparent)]
struct Restricted(core::num::NonZeroU32);
#[repr(transparent)]
struct Dropped(u32);
impl Drop for Dropped { fn drop(&mut self) {} }


#[custom_mir(dialect = "runtime", phase = "optimized")]
fn read<T>(pointer: *const T) -> T {
    mir! {
        {
            Call(RET = core::intrinsics::volatile_load(pointer), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn checked_read(pointer: *const u32) -> u32 {
    mir! {
        { Call(RET = core::ptr::read_volatile(pointer), ReturnTo(done), UnwindUnreachable()) }
        done = { Return() }
    }
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn write<T>(pointer: *mut T, value: T) {
    mir! {
        {
            Call(RET = core::intrinsics::volatile_store(pointer, value),
                ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}
fn set_pull(value: &mut Register) { value.0 = (value.0 & !0x30) | 0x20; }
fn modify<F: FnOnce(&mut Register)>(callback: F) -> Register {
    let mut value = read(REGISTER as *const Register);
    callback(&mut value);
    write(REGISTER as *mut Register, value);
    value
}
pub fn bit_identity() {
    let value = read(REGISTER as *const u32);
    assert!((value | 0) == value);
    assert!(((value >> 4) & 3) <= 3);
}
pub fn actual_checked_read() {
    let value = checked_read(REGISTER as *const u32);
    assert!((value & u32::MAX) == value);
}
pub fn f4_read() {
    let value = read(0x4002_1c0c_usize as *const u32);
    assert!((value & 3) <= 3);
}
pub fn restricted_wrapper() { let _ = read(REGISTER as *const Restricted); }
pub fn drop_wrapper() { let _ = read(REGISTER as *const Dropped); }
pub fn transparent_read() {
    let value = read(REGISTER as *const Register);
    assert!((value.0 & 3) <= 3);
}
pub fn actual_rmw_callback() {
    let mut visited = 0;
    let value = modify(|value| { visited += 1; set_pull(value); });
    assert!(visited == 1);
    assert!(value.0 & 0x30 == 0x20);
}
pub fn pure_wrong_claim() { assert!(false); }
pub fn fixed_read_claim() { assert!(read(REGISTER as *const u32) == 0); }
pub fn repeated_read_claim() {
    assert!(read(REGISTER as *const u32) == read(REGISTER as *const u32));
}
pub fn write_read_claim() {
    write(REGISTER as *mut u32, 7);
    assert!(read(REGISTER as *const u32) == 7);
}
pub fn wrong_callback_claim() {
    let value = modify(set_pull);
    assert!(value.0 & 0x30 == 0x10);
}
pub fn wrong_address() { let _ = read((REGISTER + 4) as *const u32); }
pub fn wrong_direction() { let _ = read(WRITE_ONLY as *const u32); }
pub fn read_only_store() { write((REGISTER - 8) as *mut u32, 7); }
pub fn wrong_width() { let _ = read(REGISTER as *const u16); }
pub fn signed_read() { let _ = read(REGISTER as *const i32); }
pub fn lookalike() { let _ = read(REGISTER as *const Lookalike); }
pub fn narrow_wrapper() { let _ = read(REGISTER as *const Narrow); }
pub fn misaligned() { let _ = read((REGISTER + 1) as *const u32); }
pub fn symbolic_address(address: usize) { let _ = read(address as *const u32); }
pub fn guarded_address(address: usize) {
    if address == REGISTER { let value = read(address as *const u32); assert!(value | 0 == value); }
}
pub fn ram_read() { let value = 7u32; assert!(read(&raw const value) == 7); }
static FLAG: AtomicU16 = AtomicU16::new(0);
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn unavailable() -> u32 {
    mir! {
        let pointer: *const u32;
        { pointer = 0x2000_0000_usize as *const u32; RET = *pointer; Return() }
    }
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn missing() -> u32 {
    mir! {
        { Call(RET = unavailable(), ReturnTo(done), UnwindUnreachable()) }
        done = { Return() }
    }
}
pub fn unmodeled_dereference() { let _ = missing(); }
pub fn read_then_dereference() { let _ = read(REGISTER as *const u32); let _ = missing(); }

pub fn startup_history_after_read() {
    assert!(FLAG.load(Ordering::Relaxed) == 0);
    let _ = read(REGISTER as *const u32);
    assert!(FLAG.load(Ordering::Relaxed) == 0);
}

#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn callback_bits() {
        for bits in [0, 1, u32::MAX, 0x1234_5678] {
            let mut value = Register(bits);
            set_pull(&mut value);
            assert!(value.0 & 0x30 == 0x20);
            assert!(value.0 & !0x30 == bits & !0x30);
        }
    }
}
