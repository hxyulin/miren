#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics, pattern_types, pattern_type_macro)]
use core::intrinsics::mir::*;
use core::sync::atomic::{AtomicU16, Ordering};

#[derive(Clone, Copy)]
pub enum Choice { Empty, Pair(u16, u8) }
#[derive(Clone, Copy)]
pub struct Config { pub choice: Choice, pub bytes: [u8; 2], pub words: [u16; 2],
    pub word: Plain, pub flag: Flag }
#[derive(Clone, Copy)]
pub struct Plain(pub u32);
#[derive(Clone, Copy)]
pub struct Flag(pub bool);
#[derive(Clone, Copy)]
pub struct Restricted(pub core::pattern_type!(u32 is 1..));
pub struct RestrictedArray(pub [core::pattern_type!(u32 is 1..); 1]);
pub struct RestrictedTuple(pub (core::pattern_type!(u32 is 1..),));
pub fn consume_restricted_array(_: RestrictedArray) -> u32 { 7 }
pub fn consume_restricted_tuple(_: RestrictedTuple) -> u32 { 7 }
pub fn blocked_restricted_array(value: RestrictedArray) { let _ = consume_restricted_array(value); }
pub fn blocked_restricted_tuple(value: RestrictedTuple) { let _ = consume_restricted_tuple(value); }
pub fn consume_restricted(_: Restricted) -> u32 { 7 }
pub fn blocked_restricted(value: Restricted) { let _ = consume_restricted(value); }
static IMMUTABLE: u32 = 7;
pub fn return_reference(_: Config) -> &'static u32 { &IMMUTABLE }
pub fn return_pointer(_: Config) -> *const u32 { &raw const IMMUTABLE }
pub struct BorrowedOutput { value: &'static u32 }
pub fn return_nested(_: Config) -> BorrowedOutput { BorrowedOutput { value: &IMMUTABLE } }
pub fn blocked_reference_output() { let _ = return_reference(config()); }
pub fn blocked_pointer_output() { let _ = return_pointer(config()); }
pub fn blocked_nested_output() { let _ = return_nested(config()); }
fn config() -> Config {
    Config {
        choice: Choice::Pair(3, 4), bytes: [1, 2], words: [3, 4],
        word: Plain(7), flag: Flag(true),
    }
}
#[inline(never)]
pub fn boundary(_: Config) -> u32 { 7 }
pub fn consume_reference(_: &u32) -> u32 { 7 }
pub fn consume_mutable(_: &mut u32) -> u32 { 7 }
pub fn consume_pointer(_: *const u32) -> u32 { 7 }
pub struct Nested<'a> { value: Option<&'a u32> }
pub fn consume_nested(_: Nested<'_>) -> u32 { 7 }
pub fn consume_cell(_: core::cell::Cell<u32>) -> u32 { 7 }
pub fn consume_atomic(_: AtomicU16) -> u32 { 7 }
pub fn consume_callback(_: fn() -> u32) -> u32 { 7 }
fn callback() -> u32 { 7 }

pub fn ordinary_backing() {
    let mut value = 4u32;
    let reference = &mut value;
    assert!(boundary(config()) == 7);
    *reference += 1;
    assert!(value == 5);
}
pub fn owned_symbolic(config: Config) { assert!(boundary(config) == 7); }
pub async fn fresh_future() -> u32 {
    let result = boundary(config());
    assert!(result == 7);
    result
}
pub fn wrong_later_claim() { ordinary_backing(); assert!(false); }
pub fn blocked_reference() { let value = 3; let _ = consume_reference(&value); }
pub fn blocked_mutable() { let mut value = 3; let _ = consume_mutable(&mut value); }
pub fn blocked_pointer() { let value = 3; let _ = consume_pointer(&raw const value); }
pub fn blocked_nested() { let _ = consume_nested(Nested { value: None }); }
pub fn blocked_cell() { let _ = consume_cell(core::cell::Cell::new(3)); }
pub fn blocked_atomic() { let _ = consume_atomic(AtomicU16::new(3)); }
pub fn blocked_callback() { let _ = consume_callback(callback); }

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn read<T: Copy>(pointer: *const T) -> T { mir! {{ RET = *pointer; Return() }} }
static mut STATIC: u16 = 3;
static ATOMIC: AtomicU16 = AtomicU16::new(3);
pub fn static_precision_is_retired() {
    assert!(read(&raw const STATIC) == 3);
    let _ = boundary(config());
    assert!(read(&raw const STATIC) == 3);
}
pub fn static_atomic_is_retired() {
    assert!(ATOMIC.load(Ordering::Relaxed) == 3);
    let _ = boundary(config());
    assert!(ATOMIC.load(Ordering::Relaxed) == 3);
}
pub fn local_atomic_precision_is_retired() {
    let atomic = AtomicU16::new(3);
    assert!(atomic.load(Ordering::Relaxed) == 3);
    let _ = boundary(config());
    assert!(atomic.load(Ordering::Relaxed) == 3);
}
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_backing_stays_dead() -> u32 {
    mir! {
        let value: u32; let pointer: *const u32; let input: Config; let result: u32;
        { value = 3; pointer = &raw const value; StorageDead(value);
          Call(input = config(), ReturnTo(init), UnwindUnreachable()) }
        init = { Call(result = boundary(input), ReturnTo(done), UnwindUnreachable()) }
        done = { RET = *pointer; Return() }
    }
}
pub fn pure_wrong_claim() { assert!(false); }

#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn valid_rust_storage() {
        ordinary_backing();
        let mut future = core::pin::pin!(fresh_future());
        let mut context = core::task::Context::from_waker(core::task::Waker::noop());
        assert!(
            core::future::Future::poll(future.as_mut(), &mut context) == core::task::Poll::Ready(7)
        );
    }
}
