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

pub fn dependency_nested_constant() {
    let _ = dependency_statics::channel().0.load(Ordering::Relaxed);
}
pub fn dependency_nested_constant_expected() {
    assert!(dependency_statics::channel().0.load(Ordering::Relaxed) == 7);
}

pub fn dependency_aggregate_parameter() {
    let _ = dependency_statics::aggregate_parameter()
        .0
        .0
        .load(Ordering::Relaxed);
}

pub fn dependency_nested_mutex() {
    let _ = dependency_statics::NESTED_MUTEX
        .counter
        .load(Ordering::Relaxed);
}

pub fn dependency_nested_mutex_expected() {
    assert!(
        dependency_statics::NESTED_MUTEX
            .counter
            .load(Ordering::Relaxed)
            == 7
    );
}

pub fn dependency_callback_argument() {
    let _ = dependency_statics::CALLBACK_ARGUMENT
        .counter
        .load(Ordering::Relaxed);
}

pub fn dependency_reference_argument() {
    let _ = dependency_statics::REFERENCE_ARGUMENT
        .counter
        .load(Ordering::Relaxed);
}

pub fn dependency_union_argument() {
    let _ = dependency_statics::UNION_ARGUMENT
        .counter
        .load(Ordering::Relaxed);
}

pub fn dependency_spoof_argument() {
    let _ = dependency_statics::SPOOF_ARGUMENT
        .counter
        .load(Ordering::Relaxed);
}

pub fn dependency_usize_channel() {
    let _ = dependency_statics::USIZE_CHANNELS[11]
        .count
        .load(Ordering::Relaxed);
}

pub fn dependency_usize_channel_expected() {
    assert!(
        dependency_statics::USIZE_CHANNELS[11]
            .count
            .load(Ordering::Relaxed)
            == 7
    );
}

pub fn dependency_spoof_usize() {
    let _ = dependency_statics::SPOOF_USIZE
        .counter
        .load(Ordering::Relaxed);
}

pub fn dependency_forwarded_atomic() {
    let _ = dependency_statics::FORWARDED_ATOMIC.load(Ordering::Relaxed);
}

pub fn dependency_mixed_forward() {
    let _ = dependency_statics::MIXED_FORWARD
        .counter
        .load(Ordering::Relaxed);
}

pub fn dependency_required_trait_origin() {
    let _ = dependency_statics::REQUIRED_TRAIT_ORIGIN
        .0
        .load(Ordering::Relaxed);
}

pub fn dependency_concrete_trait_origin() {
    let _ = dependency_statics::CONCRETE_TRAIT_ORIGIN
        .0
        .load(Ordering::Relaxed);
}

pub fn dependency_concrete_body_origin() {
    let _ = dependency_statics::CONCRETE_BODY_ORIGIN
        .0
        .load(Ordering::Relaxed);
}
