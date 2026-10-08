#![no_std]
#![forbid(unsafe_code)]

use core::sync::atomic::Ordering;

pub fn dependency_atomic() {
    let _ = dependency_statics::word().load(Ordering::Relaxed);
}

pub fn dependency_atomic_expected() {
    assert!(dependency_statics::word().load(Ordering::Relaxed) == 7);
}

pub fn dependency_site() {
    let _ = dependency_statics::site().0.load(Ordering::Relaxed);
}

pub fn dependency_site_expected() {
    assert!(dependency_statics::site().0.load(Ordering::Relaxed) == 7);
}
