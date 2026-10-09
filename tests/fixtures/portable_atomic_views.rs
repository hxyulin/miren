#![no_std]

use portable_atomic::{AtomicBool, Ordering};
use static_cell::StaticCell;

static FLAG: AtomicBool = AtomicBool::new(true);
static CORE_FLAG: core::sync::atomic::AtomicBool = core::sync::atomic::AtomicBool::new(true);
static CELL: StaticCell<[u8; 256]> = StaticCell::new();

pub fn matching_cas() {
    let result = FLAG.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed);
    assert!(matches!(result, Ok(false) | Err(true)));
}

pub fn wrong_cas() {
    let result = FLAG.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed);
    assert!(matches!(result, Ok(true) | Err(false)));
}

pub fn core_bool() {
    let _ = CORE_FLAG.compare_exchange(false, true,
        core::sync::atomic::Ordering::Acquire, core::sync::atomic::Ordering::Relaxed);
}

pub fn uninitialized_payload() {
    let _ = CELL.try_init([0; 256]);
}

pub fn possibly_already_full() {
    let _ = CELL.init([0; 256]);
}

pub fn invalid_ordering() {
    let _ = FLAG.compare_exchange(false, true, Ordering::Acquire, Ordering::Release);
}

pub fn numeric_address(address: usize) {
    let flag = unsafe { &*(address as *const AtomicBool) };
    let _ = flag.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed);
}

struct Lookalike(core::cell::UnsafeCell<bool>);
unsafe impl Sync for Lookalike {}
static LOOKALIKE: Lookalike = Lookalike(core::cell::UnsafeCell::new(false));

impl Lookalike {
    fn as_atomic_u8(&self) -> &core::sync::atomic::AtomicU8 {
        unsafe { &*(self as *const Self as *const core::sync::atomic::AtomicU8) }
    }
}

pub fn lookalike_restricted_cell() {
    let _ = LOOKALIKE.as_atomic_u8().load(core::sync::atomic::Ordering::Relaxed);
}

#[cfg(test)]
mod native {
    use super::*;

    #[test]
    fn actual_boolean_cas_preserves_both_outcomes() {
        for previous in [false, true] {
            let flag = AtomicBool::new(previous);
            let result = flag.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed);
            assert_eq!(result, if previous { Err(true) } else { Ok(false) });
            assert!(matches!(result, Ok(false) | Err(true)));
        }
        matching_cas();
    }

    #[test]
    fn actual_used_cell_panics_without_reading_uninitialized_bytes() {
        static USED: StaticCell<[u8; 256]> = StaticCell::new();
        assert_eq!(USED.init([3; 256])[255], 3);
        assert!(std::panic::catch_unwind(|| USED.init([4; 256])).is_err());
    }
}

#[cfg(test)]
extern crate std;
