#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]

use core::intrinsics::mir::*;

pub struct Info {
    word: u32,
    pair: (u16, u16),
}

static INFO: Info = Info {
    word: 7,
    pair: (3, 4),
};

fn info() -> &'static Info {
    &INFO
}

fn pair() -> &'static (u16, u16) {
    &info().pair
}

pub fn static_reborrow() {
    assert!(info().word == 7);
    assert!(pair().0 == 3);
}

pub fn dependency_reborrow() {
    assert!(shared_reborrow_dependency::info().0 == 7);
    assert!(shared_reborrow_dependency::info().1.1 == 4);
}

pub fn wrong_static_reborrow() {
    assert!(info().word == 8);
}

fn projected(value: &Info) -> &u16 {
    &value.pair.1
}

pub fn input_reborrow(value: &Info) {
    assert!(*projected(value) == value.pair.1);
}

pub fn owned_local_reborrow() {
    let mut value = Info {
        word: 7,
        pair: (3, 4),
    };
    let before = *projected(&value);
    value.pair.1 = 9;
    assert!(before == 4 && *projected(&value) == 9);
}

pub fn snapshot_address() -> usize {
    pair() as *const (u16, u16) as usize
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_local_reborrow() -> &'static u32 {
    mir! {
        let storage: u32;
        let reference: &u32;
        {
            storage = 7;
            reference = &storage;
            StorageDead(storage);
            RET = &*reference;
            Return()
        }
    }
}

pub struct Borrowed<'a> {
    word: &'a u32,
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn nested_dead_local_reborrow() -> &'static u32 {
    mir! {
        let storage: u32;
        let reference: &u32;
        let borrowed: Borrowed<'static>;
        let outer: &Borrowed<'static>;
        let inner: &u32;
        {
            storage = 7;
            reference = &storage;
            borrowed = Borrowed { word: reference };
            outer = &borrowed;
            StorageDead(storage);
            inner = (*outer).word;
            RET = &*inner;
            Return()
        }
    }
}

pub fn local_pointer_escape() -> *const u32 {
    let storage = 7;
    &raw const storage
}
