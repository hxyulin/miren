#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics, sync_unsafe_cell)]

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

use core::cell::{Cell, SyncUnsafeCell};

struct Wrapper {
    padding: u64,
    value: bool,
    other: bool,
}

static mut CELL: Cell<bool> = Cell::new(false);
static WRAPPER: SyncUnsafeCell<Wrapper> = SyncUnsafeCell::new(Wrapper {
    padding: 7,
    value: false,
    other: false,
});
static BYTE_CELL: SyncUnsafeCell<u8> = SyncUnsafeCell::new(0);
static UNINIT_CELL: SyncUnsafeCell<core::mem::MaybeUninit<bool>> =
    SyncUnsafeCell::new(core::mem::MaybeUninit::uninit());

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn borrow<T>(pointer: *mut T) -> &'static T {
    mir! {{ RET = &*pointer; Return() }}
}

pub fn valid_cell_bool() {
    let value = borrow(&raw mut CELL).get();
    assert!(value || !value);
}

pub fn cell_already_taken() {
    assert!(!borrow(&raw mut CELL).get());
}

pub fn cell_write_does_not_establish_history() {
    borrow(&raw mut CELL).set(true);
    assert!(borrow(&raw mut CELL).get());
}

pub fn nested_cell_already_taken() {
    let wrapper = borrow(WRAPPER.get());
    assert!(!wrapper.value);
}

pub fn wrong_cell_scalar_is_unknown() {
    assert!(read(BYTE_CELL.get()) == 0);
}

pub fn uninitialized_bool_is_unknown() {
    let pointer: *const bool = cast(UNINIT_CELL.get());
    assert!(!read(pointer));
}

pub fn repeated_bool_initialization() {
    already_taken();
    already_taken();
}

pub fn repeated_cell_initialization() {
    let cell = borrow(&raw mut CELL);
    assert!(!cell.get());
    cell.set(true);
    assert!(!cell.get());
}

pub fn independent_boolean_locations() {
    already_taken();
    let cell = borrow(&raw mut CELL);
    assert!(!cell.get());
    cell.set(true);
    assert!(read(&raw const TAKEN));
    assert!(cell.get());
    nested_cell_already_taken();
}

static COUNTER: core::sync::atomic::AtomicU16 = core::sync::atomic::AtomicU16::new(0);

pub fn boolean_and_atomic_histories_are_disjoint() {
    use core::sync::atomic::Ordering;
    COUNTER.store(7, Ordering::Relaxed);
    already_taken();
    assert!(COUNTER.load(Ordering::Relaxed) == 7);
    assert!(read(&raw const TAKEN));
}

pub fn conditional_writes_keep_branch_history() {
    use core::sync::atomic::Ordering;
    if COUNTER
        .compare_exchange_weak(0, 1, Ordering::Relaxed, Ordering::Relaxed)
        .is_ok()
    {
        write(&raw mut TAKEN, true);
        assert!(read(&raw const TAKEN));
    } else {
        assert!(!read(&raw const TAKEN));
    }
}

pub fn boundary() {}

pub fn boundary_invalidates_known_boolean_history() {
    already_taken();
    boundary();
    assert!(read(&raw const TAKEN));
}

pub fn boundary_invalidates_unseen_boolean_history() {
    boundary();
    already_taken();
}

pub fn writes_do_not_restore_invalidated_boolean_history() {
    boundary();
    write(&raw mut TAKEN, false);
    assert!(!read(&raw const TAKEN));
}

pub fn nonboolean_write_invalidates_boolean_history() {
    already_taken();
    write(BYTE_CELL.get(), 1);
    assert!(read(&raw const TAKEN));
}

pub fn independent_fields_in_one_allocation() {
    let wrapper = WRAPPER.get();
    write(synthetic::first(wrapper), true);
    assert!(read(synthetic::first(wrapper)));
    assert!(!read(synthetic::second(wrapper)));
}

mod synthetic {
    use super::*;

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn first(pointer: *mut Wrapper) -> *mut bool {
        mir! {{ RET = &raw mut (*pointer).value; Return() }}
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn second(pointer: *mut Wrapper) -> *mut bool {
        mir! {{ RET = &raw mut (*pointer).other; Return() }}
    }
}

#[cfg(test)]
mod native {
    #[test]
    fn fresh() {
        super::already_taken();
    }

    #[test]
    fn twice() {
        super::repeated_bool_initialization();
    }

    #[test]
    fn fresh_cell() {
        super::cell_write_does_not_establish_history();
    }

    #[test]
    fn twice_cell() {
        super::repeated_cell_initialization();
    }
}
