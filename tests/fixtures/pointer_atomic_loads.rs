#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics, adt_const_params, sync_unsafe_cell)]

use core::intrinsics::mir::*;
use core::sync::atomic::{AtomicPtr, Ordering};

static LINK: AtomicPtr<u32> = AtomicPtr::new(core::ptr::null_mut());

#[repr(C)]
struct Header {
    generation: u32,
    next: AtomicPtr<u32>,
}

static HEADER: Header = Header {
    generation: 7,
    next: AtomicPtr::new(core::ptr::null_mut()),
};

pub fn one_observed_address_has_consistent_nullability() {
    let pointer = LINK.load(Ordering::Acquire);
    if pointer.is_null() {
        assert!(pointer == core::ptr::null_mut());
    } else {
        assert!(pointer != core::ptr::null_mut());
    }
}

pub fn a_nested_pointer_atomic_has_a_certified_storage_offset() {
    let pointer = HEADER.next.load(Ordering::SeqCst);
    if pointer.is_null() {
        assert!(pointer as usize == 0);
    } else {
        assert!(pointer as usize != 0);
    }
}

pub fn guarded_load_ordering(order: Ordering) {
    if matches!(
        order,
        Ordering::Relaxed | Ordering::Acquire | Ordering::SeqCst
    ) {
        let _pointer = LINK.load(order);
    }
}

fn release_order() -> Ordering {
    Ordering::Release
}

fn acquire_release_order() -> Ordering {
    Ordering::AcqRel
}

pub fn release_load_ordering_panics() {
    let _pointer = LINK.load(release_order());
}

pub fn acquire_release_load_ordering_panics() {
    let _pointer = LINK.load(acquire_release_order());
}

pub fn unguarded_load_ordering_can_panic(order: Ordering) {
    let _pointer = LINK.load(order);
}

pub fn an_initializer_does_not_establish_pointer_history() {
    assert!(LINK.load(Ordering::Relaxed).is_null());
}

pub fn separate_reads_do_not_establish_a_stable_address() {
    let first = LINK.load(Ordering::Acquire);
    let second = LINK.load(Ordering::Acquire);
    assert!(first == second);
}

pub fn local_pointer_storage_supports_conservative_reads() {
    let pointer = AtomicPtr::new(core::ptr::null_mut::<u32>());
    let _observed = pointer.load(Ordering::Relaxed);
}

pub fn a_local_pointer_read_does_not_silently_assume_exclusivity() {
    let pointer = AtomicPtr::new(core::ptr::null_mut::<u32>());
    assert!(pointer.load(Ordering::Relaxed).is_null());
}

pub fn uninitialized_atomic_storage_is_not_a_pointer_receiver() {
    let _observed = synthetic::uninitialized_receiver(Ordering::Relaxed);
}

pub fn numeric_addresses_do_not_authorize_atomic_loads() {
    let _observed = synthetic::load(core::ptr::null());
}

mod synthetic {
    use super::*;
    use core::intrinsics::mir::*;
    use core::intrinsics::{AtomicOrdering, atomic_load};

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn load(source: *const *mut u32) -> *mut u32 {
        mir! {
            {
                Call(RET = atomic_load::<*mut u32, {AtomicOrdering::Relaxed}, false>(
                    source), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn uninitialized_receiver(order: Ordering) -> *mut u32 {
        mir! {
            let storage: AtomicPtr<u32>;
            let receiver: &AtomicPtr<u32>;
            {
                receiver = &storage;
                Call(RET = AtomicPtr::<u32>::load(receiver, order),
                    ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_loads_and_guarded_orderings_do_not_panic() {
        one_observed_address_has_consistent_nullability();
        a_nested_pointer_atomic_has_a_certified_storage_offset();
        local_pointer_storage_supports_conservative_reads();
        for order in [
            Ordering::Relaxed,
            Ordering::Acquire,
            Ordering::Release,
            Ordering::AcqRel,
            Ordering::SeqCst,
        ] {
            guarded_load_ordering(order);
        }
    }

    #[test]
    #[should_panic]
    fn a_release_load_panics() {
        release_load_ordering_panics();
    }

    #[test]
    #[should_panic]
    fn an_acquire_release_load_panics() {
        acquire_release_load_ordering_panics();
    }
}

pub fn loaded_addresses_do_not_authorize_pointee_reads() -> u32 {
    let pointer = LINK.load(Ordering::Relaxed);
    if pointer.is_null() {
        0
    } else {
        read_loaded_pointer(pointer)
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn read_loaded_pointer(pointer: *mut u32) -> u32 {
    core::intrinsics::mir::mir! { { RET = *pointer; Return() } }
}

static RETIRABLE_LINK: core::cell::SyncUnsafeCell<AtomicPtr<u32>> =
    core::cell::SyncUnsafeCell::new(AtomicPtr::new(core::ptr::null_mut()));

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn borrow_atomic(pointer: *mut AtomicPtr<u32>) -> &'static AtomicPtr<u32> {
    core::intrinsics::mir::mir! { { RET = &*pointer; Return() } }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn retire_atomic(pointer: *mut AtomicPtr<u32>) {
    core::intrinsics::mir::mir! {
        { Drop(*pointer, ReturnTo(done), UnwindUnreachable()) }
        done = { Return() }
    }
}

pub fn a_pointer_atomic_receiver_cannot_bypass_retirement() -> bool {
    let pointer = RETIRABLE_LINK.get();
    let reference = borrow_atomic(pointer);
    retire_atomic(pointer);
    reference.load(Ordering::Relaxed).is_null()
}

struct SimilarAtomic;

impl SimilarAtomic {
    fn load(&self, _ordering: Ordering) -> *mut u32 {
        panic!("a user method must execute its own MIR");
    }
}

pub fn user_load_methods_are_not_compiler_atomic_models() {
    let _pointer = SimilarAtomic.load(Ordering::Relaxed);
}

#[cfg(test)]
#[test]
#[should_panic]
fn a_user_load_method_keeps_its_native_panic() {
    user_load_methods_are_not_compiler_atomic_models();
}

static NUMERIC_LINK: AtomicPtr<u32> = AtomicPtr::new(0x2000_0000_usize as *mut u32);
static TARGET: u32 = 7;
static RELOCATED_LINK: AtomicPtr<u32> = AtomicPtr::new((&raw const TARGET).cast_mut());
static COUNT: core::sync::atomic::AtomicU32 = core::sync::atomic::AtomicU32::new(0);

pub fn startup_null_and_numeric_addresses_keep_their_initial_bits() {
    assert!(LINK.load(Ordering::Relaxed).is_null());
    assert!(HEADER.next.load(Ordering::Acquire).is_null());
    assert!(NUMERIC_LINK.load(Ordering::SeqCst) as usize == 0x2000_0000);
}

pub fn startup_disjoint_integer_and_pointer_locations_remain_independent() {
    COUNT.store(7, Ordering::Relaxed);
    assert!(LINK.load(Ordering::Relaxed).is_null());
    assert!(COUNT.load(Ordering::Relaxed) == 7);
}

pub fn nonzero_numeric_initializers_do_not_grant_pointee_access() -> u32 {
    read_loaded_pointer(NUMERIC_LINK.load(Ordering::Relaxed))
}

pub fn relocated_initializers_need_a_pointer_provenance_model() {
    let _pointer = RELOCATED_LINK.load(Ordering::Relaxed);
}

pub fn a_pointer_store_discards_initializer_history() {
    assert!(LINK.load(Ordering::Relaxed).is_null());
    LINK.store(core::ptr::null_mut(), Ordering::Release);
    assert!(LINK.load(Ordering::Relaxed).is_null());
}

pub fn pointer_cas_discards_initializer_history() {
    let _result = LINK.compare_exchange(
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        Ordering::Relaxed,
        Ordering::Relaxed,
    );
    assert!(LINK.load(Ordering::Relaxed).is_null());
}

pub fn a_pointer_write_cannot_restore_invalidated_initializer_history() {
    LINK.store(core::ptr::null_mut(), Ordering::Relaxed);
    assert!(HEADER.next.load(Ordering::Relaxed).is_null());
}

pub fn boundary() {}

pub fn a_boundary_discards_pointer_initializer_history() {
    assert!(LINK.load(Ordering::Relaxed).is_null());
    boundary();
    assert!(LINK.load(Ordering::Relaxed).is_null());
}

pub fn a_boundary_prevents_unseen_pointer_initializers() {
    boundary();
    assert!(LINK.load(Ordering::Relaxed).is_null());
}

#[cfg(test)]
#[test]
fn native_startup_pointer_bits() {
    startup_null_and_numeric_addresses_keep_their_initial_bits();
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn borrow_integer_overlay(
    pointer: *mut core::sync::atomic::AtomicUsize,
) -> &'static core::sync::atomic::AtomicUsize {
    mir! {{ RET = &*pointer; Return() }}
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn borrow_pointer_overlay(pointer: *mut AtomicPtr<u32>) -> &'static AtomicPtr<u32> {
    mir! {{ RET = &*pointer; Return() }}
}

static POINTER_OVERLAY: core::cell::SyncUnsafeCell<AtomicPtr<u32>> =
    core::cell::SyncUnsafeCell::new(AtomicPtr::new(core::ptr::null_mut()));
static INTEGER_OVERLAY: core::cell::SyncUnsafeCell<core::sync::atomic::AtomicUsize> =
    core::cell::SyncUnsafeCell::new(core::sync::atomic::AtomicUsize::new(0));

pub fn pointer_storage_cannot_be_read_as_integer_atomic() {
    let _value = borrow_integer_overlay(POINTER_OVERLAY.get().cast()).load(Ordering::Relaxed);
}

pub fn integer_storage_cannot_be_read_as_pointer_atomic() {
    let _value = borrow_pointer_overlay(INTEGER_OVERLAY.get().cast()).load(Ordering::Relaxed);
}
