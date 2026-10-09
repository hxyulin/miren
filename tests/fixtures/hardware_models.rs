#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;
use core::sync::atomic::{AtomicU16, Ordering};

const BASE: usize = 0x5802_0800;
const BSRR: usize = BASE + 0x18;

#[repr(transparent)]
struct Bsrr(u32);
struct Lookalike(u32);
#[repr(transparent)]
struct Narrow(u16);

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn store<T>(pointer: *mut T, value: T) {
    mir! {
        {
            Call(RET = core::intrinsics::volatile_store(pointer, value),
                ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn offset(pointer: *mut u8, count: isize) -> *mut u8 {
    mir! {{ RET = Offset(pointer, count); Return() }}
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn add(pointer: *mut u8, count: usize) -> *mut u8 {
    mir! {
        { Call(RET = pointer.add(count), ReturnTo(done), UnwindUnreachable()) }
        done = { Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn sub(pointer: *mut u8, count: usize) -> *mut u8 {
    mir! {
        { Call(RET = pointer.sub(count), ReturnTo(done), UnwindUnreachable()) }
        done = { Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn load(pointer: *const u32) -> u32 {
    mir! {
        {
            Call(RET = core::intrinsics::volatile_load(pointer), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

fn callback(value: &mut u32) -> Bsrr {
    *value += 1;
    Bsrr(*value)
}

pub fn exact_u32() { store(BSRR as *mut u32, 7); }
pub fn byte_transport() { store(offset(BASE as *mut u8, 24).cast::<u32>(), 7); }
pub fn actual_add() { store(add(BASE as *mut u8, 24).cast::<u32>(), 7); }
pub fn f4_write() { store(0x4002_1c18_usize as *mut u32, 7); }
pub fn callback_body() {
    let mut value = 4;
    let register = callback(&mut value);
    store(BSRR as *mut Bsrr, register);
    assert!(value == 5);
}
pub fn wrong_rust_claim() { exact_u32(); assert!(false); }
pub fn wrong_callback_claim() {
    let mut value = 4;
    let register = callback(&mut value);
    store(BSRR as *mut Bsrr, register);
    assert!(value == 6);
}
pub fn later_unknown() { exact_u32(); let _ = load(BSRR as *const u32); }
pub fn wrong_address() { store((BSRR + 4) as *mut u32, 7); }
pub fn misaligned() { store((BSRR + 1) as *mut u32, 7); }
pub fn ram_write() { store(0x2000_0018_usize as *mut u32, 7); }
pub fn wrong_width() { store(BSRR as *mut u16, 7); }
pub fn signed_write() { store(BSRR as *mut i32, 7); }
pub fn lookalike() { store(BSRR as *mut Lookalike, Lookalike(7)); }
pub fn narrow_wrapper() { store(BSRR as *mut Narrow, Narrow(7)); }
pub fn symbolic_address(address: usize) { store(address as *mut u32, 7); }
pub fn guarded_address(address: usize) {
    if address == BSRR { store(address as *mut u32, 7); }
}
pub fn symbolic_offset(count: isize) { let _ = offset(BASE as *mut u8, count); }
pub fn outside_region() { let _ = offset(BASE as *mut u8, 0x400); }
pub fn huge_add() { let _ = add((BASE + 32) as *mut u8, usize::MAX); }
pub fn huge_sub() { let _ = sub(BASE as *mut u8, usize::MAX - 23); }
pub fn negative_offset() { let _ = offset((BASE + 32) as *mut u8, -8); }
pub fn tracked_storage() { let mut value = 0u32; store(&raw mut value, 7); }
static FLAG: AtomicU16 = AtomicU16::new(0);
pub fn startup_history_after_write() {
    assert!(FLAG.load(Ordering::Relaxed) == 0);
    exact_u32();
    assert!(FLAG.load(Ordering::Relaxed) == 0);
}

#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn callback_effect() {
        let mut value = 4;
        let register = callback(&mut value);
        assert!(value == 5);
        assert!(register.0 == 5);
    }
}
