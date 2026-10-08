#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;

static mut TAKEN: bool = false;
static mut BYTE: u8 = 0;
static IMMUTABLE: bool = false;

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn read<T: Copy>(pointer: *const T) -> T {
    mir! {
        {
            RET = *pointer;
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn write<T>(pointer: *mut T, value: T) {
    mir! {
        {
            *pointer = Move(value);
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn cast<S, T>(value: S) -> T {
    mir! {
        {
            RET = CastTransmute(value);
            Return()
        }
    }
}

pub fn valid_bool() {
    let value = read(&raw const TAKEN);
    assert!(value || !value);
}

pub fn writes_valid_bool(value: bool) {
    write(&raw mut TAKEN, value);
}

pub fn already_taken() {
    assert!(!read(&raw const TAKEN));
    write(&raw mut TAKEN, true);
}

pub fn write_does_not_establish_history() {
    write(&raw mut TAKEN, true);
    assert!(read(&raw const TAKEN));
}

pub fn separate_reads_are_not_stable() {
    let first = read(&raw const TAKEN);
    let second = read(&raw const TAKEN);
    assert!(first == second);
}

pub fn wrong_scalar_is_unknown() {
    assert!(read(&raw const BYTE) == 0);
}

pub fn wrong_declared_type_is_unknown() {
    let pointer: *const bool = cast(&raw const BYTE);
    assert!(!read(pointer));
}

pub fn immutable_storage_is_unknown() {
    assert!(!read(&raw const IMMUTABLE));
}

pub fn readonly_write_is_unknown() {
    let pointer: *mut bool = cast(&raw const TAKEN);
    write(pointer, true);
}

pub fn numeric_address_is_unknown() {
    let pointer: *const bool = cast(0x2000_0000_usize);
    assert!(!read(pointer));
}
