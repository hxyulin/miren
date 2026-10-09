#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;

fn initialize(taken: &mut bool) {
    assert!(!*taken, "initialization repeated");
    *taken = true;
}

pub fn fresh_once() {
    let mut taken = false;
    initialize(&mut taken);
    assert!(taken);
}

pub fn fresh_twice() {
    let mut taken = false;
    initialize(&mut taken);
    initialize(&mut taken);
}

pub fn arbitrary_incoming_state(mut taken: bool) {
    initialize(&mut taken);
}

pub fn established_incoming_domain(mut taken: bool) {
    if !taken {
        initialize(&mut taken);
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn unsupported_startup_pointer(pointer: *const bool) {
    mir! {
        let value: bool;
        {
            value = *pointer;
            RET = ();
            Return()
        }
    }
}

#[cfg(test)]
mod native {
    #[test]
    fn fresh() {
        super::fresh_once();
    }

    #[test]
    fn twice() {
        super::fresh_twice();
    }

    #[test]
    fn incoming_true() {
        super::arbitrary_incoming_state(true);
    }

    #[test]
    fn incoming_false() {
        super::arbitrary_incoming_state(false);
    }
}
