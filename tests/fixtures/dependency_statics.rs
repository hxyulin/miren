#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::sync::atomic::AtomicU32;

pub static WORD: AtomicU32 = AtomicU32::new(7);
pub static FROZEN: u32 = 7;
pub static FROZEN_SLICE: [u32; 2] = [7, 9];

#[inline(always)]
pub fn word() -> &'static AtomicU32 {
    &WORD
}

#[inline(always)]
pub fn frozen() -> u32 {
    FROZEN
}

#[inline(always)]
pub fn frozen_slice() -> u32 {
    let values: &[u32] = &FROZEN_SLICE;
    values[0]
}

pub struct Site(pub AtomicU32);

impl Site {
    const fn new() -> Self {
        Self(AtomicU32::new(7))
    }
}

pub static SITE: Site = Site::new();

#[inline(always)]
pub fn site() -> &'static Site {
    &SITE
}

pub struct ChannelState(pub AtomicU32);

impl ChannelState {
    pub const NEW: Self = Self(AtomicU32::new(7));
}

pub static STATES: [ChannelState; 16] = [ChannelState::NEW; 16];

#[inline(always)]
pub fn channel() -> &'static ChannelState {
    &STATES[11]
}

pub struct AggregateParameter(pub ChannelState);

const fn wrap(value: ChannelState) -> AggregateParameter {
    AggregateParameter(value)
}

pub static AGGREGATE_PARAMETER: AggregateParameter = wrap(ChannelState::NEW);

#[inline(always)]
pub fn aggregate_parameter() -> &'static AggregateParameter {
    &AGGREGATE_PARAMETER
}

#[cfg(test)]
#[test]
fn nested_constructor_native() {
    assert_eq!(channel().0.load(core::sync::atomic::Ordering::Relaxed), 7);
}

pub struct Empty {
    marker: core::marker::PhantomData<()>,
}

const fn empty() -> Empty {
    Empty {
        marker: core::marker::PhantomData,
    }
}
pub struct GenericMutex<R, T> {
    pub raw: R,
    pub data: T,
    pub counter: AtomicU32,
}

const fn generic_mutex<R, T>(raw: R, data: T, counter: AtomicU32) -> GenericMutex<R, T> {
    GenericMutex { raw, data, counter }
}

const fn nested_mutex() -> GenericMutex<Empty, Option<fn()>> {
    generic_mutex(empty(), None, AtomicU32::new(7))
}

pub static NESTED_MUTEX: GenericMutex<Empty, Option<fn()>> = nested_mutex();

fn callback() {}

pub static CALLBACK_ARGUMENT: GenericMutex<Empty, Option<fn()>> =
    generic_mutex(empty(), Some(callback), AtomicU32::new(7));
pub static REFERENCE_ARGUMENT: GenericMutex<Empty, &'static u32> =
    generic_mutex(empty(), &FROZEN, AtomicU32::new(7));

pub union UnionArgument {
    pub word: u32,
}
pub static UNION_ARGUMENT: GenericMutex<Empty, UnionArgument> =
    generic_mutex(empty(), UnionArgument { word: 7 }, AtomicU32::new(7));

pub mod spoof {
    #[repr(transparent)]
    pub struct Atomic<T>(pub T);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
const fn erased_atomic(value: u32) -> spoof::Atomic<u32> {
    use core::intrinsics::mir::*;
    mir! {{ RET = CastTransmute(value); Return() }}
}

pub static SPOOF_ARGUMENT: GenericMutex<Empty, spoof::Atomic<u32>> =
    generic_mutex(empty(), erased_atomic(7), AtomicU32::new(7));

pub struct UsizeChannel {
    pub count: core::sync::atomic::AtomicUsize,
    pub mutex: GenericMutex<Empty, Option<fn()>>,
}

impl UsizeChannel {
    pub const NEW: Self = Self {
        count: core::sync::atomic::AtomicUsize::new(7),
        mutex: nested_mutex(),
    };
}

pub static USIZE_CHANNELS: [UsizeChannel; 16] = [UsizeChannel::NEW; 16];

#[custom_mir(dialect = "runtime", phase = "optimized")]
const fn erased_usize(value: usize) -> spoof::Atomic<usize> {
    use core::intrinsics::mir::*;
    mir! {{ RET = CastTransmute(value); Return() }}
}

pub static SPOOF_USIZE: GenericMutex<Empty, spoof::Atomic<usize>> =
    generic_mutex(empty(), erased_usize(7), AtomicU32::new(7));

#[cfg(test)]
#[test]
fn nested_mutex_native() {
    assert_eq!(
        NESTED_MUTEX
            .counter
            .load(core::sync::atomic::Ordering::Relaxed),
        7
    );
    assert_eq!(
        USIZE_CHANNELS[11]
            .count
            .load(core::sync::atomic::Ordering::Relaxed),
        7
    );
}

const fn forward_atomic(value: AtomicU32) -> AtomicU32 {
    value
}
pub static FORWARDED_ATOMIC: AtomicU32 = forward_atomic(AtomicU32::new(7));

const fn constructed_atomic() -> AtomicU32 {
    Site::new().0
}
pub static MIXED_FORWARD: GenericMutex<Empty, (AtomicU32, AtomicU32)> = generic_mutex(
    empty(),
    (
        forward_atomic(AtomicU32::new(7)),
        forward_atomic(constructed_atomic()),
    ),
    AtomicU32::new(7),
);
