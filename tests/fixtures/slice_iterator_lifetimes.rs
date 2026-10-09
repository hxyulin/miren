#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;

fn make_iter(array: &mut [u8; 0]) -> core::slice::IterMut<'_, u8> {
    array.iter_mut()
}

fn consume_for_each(iterator: core::slice::IterMut<'_, u8>) {
    iterator.for_each(|_| {});
}

fn consume_fold(iterator: core::slice::IterMut<'_, u8>) {
    iterator.fold((), |(), _| ());
}

fn consume_all(mut iterator: core::slice::IterMut<'_, u8>) {
    assert!(iterator.all(|_| true));
}

fn consume_next(mut iterator: core::slice::IterMut<'_, u8>) {
    assert!(iterator.next().is_none());
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn live_empty_for_each() {
    mir! {
        let storage: [u8; 0];
        let borrowed: &mut [u8; 0];
        let iterator: core::slice::IterMut<'_, u8>;
        {
            storage = [];
            borrowed = &mut storage;
            Call(iterator = make_iter(Move(borrowed)), ReturnTo(next), UnwindUnreachable())
        }
        next = {
            Call(RET = consume_for_each(Move(iterator)), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_empty_for_each() {
    mir! {
        let storage: [u8; 0];
        let borrowed: &mut [u8; 0];
        let iterator: core::slice::IterMut<'_, u8>;
        {
            storage = [];
            borrowed = &mut storage;
            Call(iterator = make_iter(Move(borrowed)), ReturnTo(next), UnwindUnreachable())
        }
        next = {
            StorageDead(storage);
            Call(RET = consume_for_each(Move(iterator)), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn live_empty_fold() {
    mir! {
        let storage: [u8; 0];
        let borrowed: &mut [u8; 0];
        let iterator: core::slice::IterMut<'_, u8>;
        {
            storage = [];
            borrowed = &mut storage;
            Call(iterator = make_iter(Move(borrowed)), ReturnTo(next), UnwindUnreachable())
        }
        next = {
            Call(RET = consume_fold(Move(iterator)), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_empty_fold() {
    mir! {
        let storage: [u8; 0];
        let borrowed: &mut [u8; 0];
        let iterator: core::slice::IterMut<'_, u8>;
        {
            storage = [];
            borrowed = &mut storage;
            Call(iterator = make_iter(Move(borrowed)), ReturnTo(next), UnwindUnreachable())
        }
        next = {
            StorageDead(storage);
            Call(RET = consume_fold(Move(iterator)), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn live_empty_all() {
    mir! {
        let storage: [u8; 0];
        let borrowed: &mut [u8; 0];
        let iterator: core::slice::IterMut<'_, u8>;
        {
            storage = [];
            borrowed = &mut storage;
            Call(iterator = make_iter(Move(borrowed)), ReturnTo(next), UnwindUnreachable())
        }
        next = {
            Call(RET = consume_all(Move(iterator)), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_empty_all() {
    mir! {
        let storage: [u8; 0];
        let borrowed: &mut [u8; 0];
        let iterator: core::slice::IterMut<'_, u8>;
        {
            storage = [];
            borrowed = &mut storage;
            Call(iterator = make_iter(Move(borrowed)), ReturnTo(next), UnwindUnreachable())
        }
        next = {
            StorageDead(storage);
            Call(RET = consume_all(Move(iterator)), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn live_empty_next() {
    mir! {
        let storage: [u8; 0];
        let borrowed: &mut [u8; 0];
        let iterator: core::slice::IterMut<'_, u8>;
        {
            storage = [];
            borrowed = &mut storage;
            Call(iterator = make_iter(Move(borrowed)), ReturnTo(next), UnwindUnreachable())
        }
        next = {
            Call(RET = consume_next(Move(iterator)), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_empty_next() {
    mir! {
        let storage: [u8; 0];
        let borrowed: &mut [u8; 0];
        let iterator: core::slice::IterMut<'_, u8>;
        {
            storage = [];
            borrowed = &mut storage;
            Call(iterator = make_iter(Move(borrowed)), ReturnTo(next), UnwindUnreachable())
        }
        next = {
            StorageDead(storage);
            Call(RET = consume_next(Move(iterator)), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}
