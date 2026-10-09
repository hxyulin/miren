#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics, sync_unsafe_cell)]

use core::intrinsics::mir::*;
use core::sync::atomic::{AtomicPtr, Ordering};

static LINK: AtomicPtr<u8> = AtomicPtr::new(core::ptr::null_mut());

pub fn local_initializer_is_observed() {
    let link = AtomicPtr::<u8>::new(core::ptr::null_mut());
    assert!(link.load(Ordering::Acquire).is_null());
}

pub fn strong_cas_updates_local_backing() {
    let link = AtomicPtr::<u8>::new(core::ptr::null_mut());
    let result = link.compare_exchange(
        core::ptr::null_mut(),
        7_usize as *mut u8,
        Ordering::AcqRel,
        Ordering::Acquire,
    );
    assert!(result.is_ok());
    assert!(link.load(Ordering::Relaxed) as usize == 7);
}

pub fn strong_failure_keeps_old_backing() {
    let link = AtomicPtr::<u8>::new(core::ptr::null_mut());
    let result = link.compare_exchange(
        1_usize as *mut u8,
        7_usize as *mut u8,
        Ordering::Relaxed,
        Ordering::Relaxed,
    );
    assert!(result.is_err());
    assert!(link.load(Ordering::Relaxed).is_null());
}

pub fn weak_cas_updates_only_on_success() {
    let link = AtomicPtr::<u8>::new(core::ptr::null_mut());
    let result = link.compare_exchange_weak(
        core::ptr::null_mut(),
        7_usize as *mut u8,
        Ordering::Relaxed,
        Ordering::Relaxed,
    );
    match result {
        Ok(old) => {
            assert!(old.is_null());
            assert!(link.load(Ordering::Relaxed) as usize == 7);
        }
        Err(old) => {
            assert!(old.is_null());
            assert!(link.load(Ordering::Relaxed).is_null());
        }
    }
}

pub fn weak_cas_may_fail_spuriously() {
    let link = AtomicPtr::<u8>::new(core::ptr::null_mut());
    assert!(
        link.compare_exchange_weak(
            core::ptr::null_mut(),
            core::ptr::null_mut(),
            Ordering::Relaxed,
            Ordering::Relaxed,
        )
        .is_ok()
    );
}

pub fn static_cas_preserves_history_after_publication() {
    assert!(
        LINK.compare_exchange(
            core::ptr::null_mut(),
            7_usize as *mut u8,
            Ordering::Relaxed,
            Ordering::Relaxed,
        )
        .is_ok()
    );
    assert!(LINK.load(Ordering::Relaxed) as usize == 7);
}

struct Holder {
    link: AtomicPtr<u8>,
    other: u8,
}

pub fn projected_receiver_preserves_other_fields() {
    let holder = Holder {
        link: AtomicPtr::new(core::ptr::null_mut()),
        other: 9,
    };
    assert!(
        holder
            .link
            .compare_exchange(
                core::ptr::null_mut(),
                7_usize as *mut u8,
                Ordering::Relaxed,
                Ordering::Relaxed,
            )
            .is_ok()
    );
    assert!(holder.link.load(Ordering::Relaxed) as usize == 7);
    assert!(holder.other == 9);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn read_pointer(pointer: *mut u8) -> u8 {
    core::intrinsics::mir::mir! { { RET = *pointer; Return() } }
}

pub fn actual_constructor_provenance_is_retained() {
    let mut byte = 11_u8;
    let pointer = &mut byte as *mut u8;
    let link = AtomicPtr::new(pointer);
    assert!(link.load(Ordering::Relaxed) == pointer);
    assert!(!link.load(Ordering::Relaxed).is_null());
}

pub fn actual_cas_replacement_provenance_is_retained() {
    let mut byte = 11_u8;
    let pointer = &mut byte as *mut u8;
    let link = AtomicPtr::<u8>::new(core::ptr::null_mut());
    assert!(
        link.compare_exchange(
            core::ptr::null_mut(),
            pointer,
            Ordering::Relaxed,
            Ordering::Relaxed,
        )
        .is_ok()
    );
    assert!(link.load(Ordering::Relaxed) == pointer);
    assert!(!link.load(Ordering::Relaxed).is_null());
}

pub fn numeric_address_does_not_gain_provenance() {
    let link = AtomicPtr::new(7_usize as *mut u8);
    let _ = read_pointer(link.load(Ordering::Relaxed));
}

fn release_ordering() -> Ordering {
    Ordering::Release
}

pub fn invalid_failure_ordering_panics() {
    let link = AtomicPtr::<u8>::new(core::ptr::null_mut());
    let _ = link.compare_exchange(
        core::ptr::null_mut(),
        core::ptr::null_mut(),
        Ordering::Relaxed,
        release_ordering(),
    );
}

#[cfg(test)]
#[test]
fn native_pointer_history() {
    local_initializer_is_observed();
    strong_cas_updates_local_backing();
    strong_failure_keeps_old_backing();
    weak_cas_updates_only_on_success();
    projected_receiver_preserves_other_fields();
    static_cas_preserves_history_after_publication();
    static_pointer_strong_cas_preserves_the_actual_address();
    static_pointer_cas_failure_retains_original_address();
    weak_mixed_origins_retain_bits_and_disjoint_history();
}

#[inline(never)]
pub fn boundary() {}

pub fn opaque_call_discards_local_pointer_history() {
    let link = AtomicPtr::<u8>::new(core::ptr::null_mut());
    assert!(link.load(Ordering::Relaxed).is_null());
    boundary();
    assert!(link.load(Ordering::Relaxed).is_null());
}

pub fn local_store_updates_projected_backing() {
    let holder = Holder {
        link: AtomicPtr::new(core::ptr::null_mut()),
        other: 9,
    };
    holder.link.store(7_usize as *mut u8, Ordering::Release);
    assert!(holder.link.load(Ordering::Acquire) as usize == 7);
    assert!(holder.other == 9);
}

pub fn static_store_retains_actual_pointer_identity() {
    let mut byte = 11_u8;
    let pointer = &mut byte as *mut u8;
    LINK.store(pointer, Ordering::Release);
    assert!(LINK.load(Ordering::Acquire) == pointer);
    assert!(!LINK.load(Ordering::Acquire).is_null());
}

fn acquire_ordering() -> Ordering {
    Ordering::Acquire
}

pub fn invalid_store_ordering_panics() {
    let link = AtomicPtr::<u8>::new(core::ptr::null_mut());
    link.store(core::ptr::null_mut(), acquire_ordering());
}

pub fn local_store_cannot_revive_history_after_opaque_call() {
    let link = AtomicPtr::<u8>::new(core::ptr::null_mut());
    boundary();
    link.store(core::ptr::null_mut(), Ordering::Relaxed);
    assert!(link.load(Ordering::Relaxed).is_null());
}

pub fn static_store_retains_numeric_bits() {
    LINK.store(7_usize as *mut u8, Ordering::Release);
    assert!(LINK.load(Ordering::Acquire) as usize == 7);
}

pub fn local_store_retains_actual_pointer_identity() {
    let mut byte = 11_u8;
    let pointer = &mut byte as *mut u8;
    let link = AtomicPtr::<u8>::new(core::ptr::null_mut());
    link.store(pointer, Ordering::Release);
    assert!(link.load(Ordering::Acquire) == pointer);
    assert!(!link.load(Ordering::Acquire).is_null());
}

static BYTE: core::cell::SyncUnsafeCell<u8> = core::cell::SyncUnsafeCell::new(11);
static DISJOINT: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);

pub fn static_pointer_strong_cas_preserves_the_actual_address() {
    let pointer = BYTE.get();
    LINK.store(pointer, Ordering::Relaxed);
    let result = LINK.compare_exchange(
        pointer,
        core::ptr::null_mut(),
        Ordering::Relaxed,
        Ordering::Relaxed,
    );
    let old = result.unwrap();
    assert!(old as usize == pointer as usize);
    assert!(LINK.load(Ordering::Relaxed).is_null());
}

pub fn static_pointer_cas_failure_retains_original_address() {
    let pointer = BYTE.get();
    let link = AtomicPtr::<u8>::new(core::ptr::null_mut());
    link.store(pointer, Ordering::Relaxed);
    assert!(
        link.compare_exchange(
            core::ptr::null_mut(),
            core::ptr::null_mut(),
            Ordering::Relaxed,
            Ordering::Relaxed,
        )
        .is_err()
    );
    assert!(link.load(Ordering::Relaxed) as usize == pointer as usize);
}

pub fn static_pointer_cas_does_not_claim_success_for_null_expected() {
    let link = AtomicPtr::<u8>::new(core::ptr::null_mut());
    link.store(BYTE.get(), Ordering::Relaxed);
    assert!(
        link.compare_exchange(
            core::ptr::null_mut(),
            core::ptr::null_mut(),
            Ordering::Relaxed,
            Ordering::Relaxed,
        )
        .is_ok()
    );
}

pub fn weak_mixed_origins_retain_bits_and_disjoint_history() {
    DISJOINT.store(9, Ordering::Relaxed);
    let pointer = BYTE.get();
    let link = AtomicPtr::<u8>::new(core::ptr::null_mut());
    match link.compare_exchange_weak(
        core::ptr::null_mut(),
        pointer,
        Ordering::Relaxed,
        Ordering::Relaxed,
    ) {
        Ok(old) => {
            assert!(old.is_null());
            assert!(link.load(Ordering::Relaxed) as usize == pointer as usize);
        }
        Err(old) => {
            assert!(old.is_null());
            assert!(link.load(Ordering::Relaxed).is_null());
        }
    }
    assert!(DISJOINT.load(Ordering::Relaxed) == 9);
}

pub fn weak_mixed_origins_do_not_grant_pointee_provenance() {
    let pointer = BYTE.get();
    let link = AtomicPtr::<u8>::new(core::ptr::null_mut());
    if link
        .compare_exchange_weak(
            core::ptr::null_mut(),
            pointer,
            Ordering::Relaxed,
            Ordering::Relaxed,
        )
        .is_ok()
    {
        let _ = read_pointer(link.load(Ordering::Relaxed));
    }
}

pub fn invalidated_store_cannot_expose_stale_constructor_through_into_inner() {
    let link = AtomicPtr::<u8>::new(core::ptr::null_mut());
    boundary();
    link.store(7_usize as *mut u8, Ordering::Relaxed);
    assert!(link.into_inner().is_null());
}

pub fn default_cas_cannot_expose_stale_constructor_through_into_inner() {
    let link = AtomicPtr::<u8>::new(core::ptr::null_mut());
    let _ = link.compare_exchange(
        core::ptr::null_mut(),
        7_usize as *mut u8,
        Ordering::Relaxed,
        Ordering::Relaxed,
    );
    assert!(link.into_inner().is_null());
}
