#![no_std]
#![forbid(unsafe_code)]

use core::sync::atomic::{AtomicU32, Ordering};

static LOCAL: AtomicU32 = AtomicU32::new(7);
static FROZEN: u32 = 7;

pub fn local_initializer() {
    assert!(LOCAL.load(Ordering::Relaxed) == 7);
}

pub fn local_frozen_initializer() {
    assert!(FROZEN == 7);
}

pub fn dependency_atomic() {
    let _ = dependency_statics::word().load(Ordering::Relaxed);
}

pub fn dependency_frozen() {
    assert!(dependency_statics::frozen() == 7);
}

pub fn dependency_slice() {
    assert!(dependency_statics::frozen_slice() == 7);
}
