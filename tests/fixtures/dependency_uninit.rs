#![no_std]
#![forbid(unsafe_code)]
#![feature(sync_unsafe_cell)]

use core::cell::SyncUnsafeCell;
use core::mem::MaybeUninit;

pub static BUFFER: SyncUnsafeCell<MaybeUninit<[u8; 256]>> =
    SyncUnsafeCell::new(MaybeUninit::uninit());
pub static INITIALIZED: SyncUnsafeCell<MaybeUninit<[u8; 256]>> =
    SyncUnsafeCell::new(MaybeUninit::new([7; 256]));

pub union Pretend {
    pub uninit: (),
    pub bytes: [u8; 256],
}

impl Pretend {
    const fn uninit() -> Self {
        Self { uninit: () }
    }
}

pub static SPOOF: SyncUnsafeCell<Pretend> = SyncUnsafeCell::new(Pretend::uninit());
pub static SHORT: SyncUnsafeCell<MaybeUninit<[u8; 255]>> =
    SyncUnsafeCell::new(MaybeUninit::uninit());

const fn encode(value: bool) -> u8 {
    value as u8
}

pub static BOOL_BYTE: SyncUnsafeCell<u8> = SyncUnsafeCell::new(encode(true));
