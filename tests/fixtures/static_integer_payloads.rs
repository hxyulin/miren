#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics, sync_unsafe_cell)]

use core::cell::SyncUnsafeCell;
use core::intrinsics::mir::*;
use core::mem::MaybeUninit;
use core::sync::atomic::{AtomicU16, Ordering};

static mut WHOLE: u32 = 7;
static WIDE: SyncUnsafeCell<u128> = SyncUnsafeCell::new(u128::MAX);
static SIGNED: SyncUnsafeCell<i16> = SyncUnsafeCell::new(-7);
static WRAPPER: SyncUnsafeCell<(u8, u32)> = SyncUnsafeCell::new((3, 7));
static UNINIT: SyncUnsafeCell<MaybeUninit<u32>> = SyncUnsafeCell::new(MaybeUninit::uninit());
static ARRAY: SyncUnsafeCell<[u32; 2]> = SyncUnsafeCell::new([7, 9]);
union Overlay {
    integer: u32,
}
static UNION: SyncUnsafeCell<Overlay> = SyncUnsafeCell::new(Overlay { integer: 7 });
static COUNT: AtomicU16 = AtomicU16::new(0);
static NUMERIC: SyncUnsafeCell<usize> = SyncUnsafeCell::new(7);

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn read<T: Copy>(pointer: *const T) -> T {
    mir! {{ RET = *pointer; Return() }}
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn write<T>(pointer: *mut T, value: T) {
    mir! {{ *pointer = Move(value); Return() }}
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn first(pointer: *mut (u8, u32)) -> *mut u8 {
    mir! {{ RET = &raw mut (*pointer).0; Return() }}
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn second(pointer: *mut (u8, u32)) -> *mut u32 {
    mir! {{ RET = &raw mut (*pointer).1; Return() }}
}

pub fn whole_initializer() {
    assert!(read(&raw const WHOLE) == 7);
}

pub fn signed_initializer() {
    assert!(read(SIGNED.get()) == -7);
}

pub fn wide_initializer() {
    assert!(read(WIDE.get()) == u128::MAX);
}

pub fn valid_scalar() {
    let _value = read(SIGNED.get());
}

pub fn pointer_width_initializer() {
    assert!(read(NUMERIC.get()) == 7);
}

pub fn retained_write() {
    write(&raw mut WHOLE, 11);
    assert!(read(&raw const WHOLE) == 11);
}

pub fn separate_reads() {
    assert!(read(&raw const WHOLE) == read(&raw const WHOLE));
}

pub fn disjoint_fields() {
    write(first(WRAPPER.get()), 9);
    assert!(read(first(WRAPPER.get())) == 9);
    assert!(read(second(WRAPPER.get())) == 7);
}

pub fn disjoint_atomic() {
    COUNT.store(9, Ordering::Relaxed);
    write(SIGNED.get(), -11);
    assert!(COUNT.load(Ordering::Relaxed) == 9);
    assert!(read(SIGNED.get()) == -11);
}

pub fn branch_isolation() {
    if COUNT
        .compare_exchange_weak(0, 1, Ordering::Relaxed, Ordering::Relaxed)
        .is_ok()
    {
        write(SIGNED.get(), -11);
        assert!(read(SIGNED.get()) == -11);
    } else {
        assert!(read(SIGNED.get()) == -7);
    }
}

pub fn false_claim() {
    write(SIGNED.get(), -11);
    assert!(read(SIGNED.get()) == -7);
}

pub fn uninitialized() {
    assert!(read(UNINIT.get().cast::<u32>()) == 0);
}

pub fn numeric_origin() {
    assert!(read(0x2000_0000_usize as *const u32) == 0);
}

pub fn array_origin() {
    assert!(read(ARRAY.get().cast::<u32>()) == 7);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn union_field(pointer: *mut Overlay) -> *mut u32 {
    mir! {{ RET = &raw mut (*pointer).integer; Return() }}
}

pub fn union_origin() {
    assert!(read(union_field(UNION.get())) == 7);
}

pub fn wrong_type() {
    assert!(read(SIGNED.get().cast::<u16>()) == 0);
}

pub fn boundary() {}

pub fn known_boundary() {
    write(SIGNED.get(), -11);
    boundary();
    assert!(read(SIGNED.get()) == -11);
}

pub fn unseen_boundary() {
    boundary();
    whole_initializer();
}

pub fn write_after_boundary() {
    boundary();
    retained_write();
}

#[cfg(test)]
#[test]
fn native_initializer() {
    whole_initializer();
    signed_initializer();
    pointer_width_initializer();
    wide_initializer();
}
