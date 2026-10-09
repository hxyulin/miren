#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics, trusted_random_access)]

use core::intrinsics::mir::*;
use core::slice::Iter;

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn get_shared<'a, T>(iterator: &mut Iter<'a, T>, index: usize) -> &'a T {
    mir! {
        { Call(RET = <Iter<'a, T> as Iterator>::__iterator_get_unchecked(iterator, index),
            ReturnTo(done), UnwindUnreachable()) }
        done = { Return() }
    }
}

pub fn shared_zip(values: &[u16; 3]) {
    let mut output = [0; 3];
    for (source, destination) in values.iter().zip(output.iter_mut()) {
        *destination = *source;
    }
    assert!(output == *values);
}

pub struct Packet {
    pub channels: [i16; 5],
    pub flags: u8,
}

pub fn projected_zip(packet: &Packet, offset: i16) {
    let mut output = [0; 5];
    for (source, destination) in packet.channels.iter().zip(output.iter_mut()) {
        *destination = *source;
    }
    assert!(output == packet.channels);
    let _ = offset;
}

pub fn byte_zip(values: &[u8; 3]) {
    let mut output = [0; 3];
    for (source, destination) in values.iter().zip(output.iter_mut()) {
        *destination = *source;
    }
    assert!(output == *values);
}

fn returned_view(values: &[u16; 3]) -> &[u16; 3] { values }

pub fn returned_and_reborrowed(values: &[u16; 3]) {
    let view = returned_view(values);
    let mut iterator = view.iter();
    let item = get_shared(&mut iterator, 1);
    assert!(*item == values[1]);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn root_local_storage_dead(values: &[u16; 3]) -> u16 {
    mir! {
        let slice: &[u16];
        let iterator: Iter<'_, u16>;
        let receiver: &mut Iter<'_, u16>;
        let item: &u16;
        {
            slice = CastUnsize(values);
            Call(iterator = <[u16]>::iter(slice), ReturnTo(dead), UnwindUnreachable())
        }
        dead = {
            receiver = &mut iterator;
            StorageDead(values);
            StorageDead(slice);
            Call(item = get_shared(receiver, 0), ReturnTo(done), UnwindUnreachable())
        }
        done = { RET = *item; Return() }
    }
}

pub fn competing_shared_unknown(left: &[u16; 3], right: &[u16; 3]) {
    let mut iterator = left.iter();
    let _ = get_shared(&mut iterator, 0);
    let _ = right;
}

pub fn competing_mutable_unknown(left: &[u16; 3], right: &mut u8) {
    let mut iterator = left.iter();
    let _ = get_shared(&mut iterator, 0);
    let _ = right;
}

pub fn competing_pointer_unknown(left: &[u16; 3], right: *const u8) {
    let mut iterator = left.iter();
    let _ = get_shared(&mut iterator, 0);
    let _ = right;
}

pub struct Nested<'a> { pub values: &'a [u16; 3] }

pub fn nested_reference_unknown(value: &Nested<'_>) {
    let mut iterator = value.values.iter();
    let _ = get_shared(&mut iterator, 0);
}

pub struct Pointer { pub values: [u16; 3], pub pointer: *const u8 }

pub fn nested_pointer_unknown(value: &Pointer) {
    let mut iterator = value.values.iter();
    let _ = get_shared(&mut iterator, 0);
}

pub fn wrong_shared_claim(values: &[u16; 3]) { shared_zip(values); assert!(values[0] == 0); }

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_local_source_unknown(values: [u16; 3]) -> u16 {
    mir! {
        let array: &[u16; 3];
        let slice: &[u16];
        let iterator: Iter<'_, u16>;
        let receiver: &mut Iter<'_, u16>;
        let item: &u16;
        {
            array = &values;
            slice = CastUnsize(array);
            Call(iterator = <[u16]>::iter(slice), ReturnTo(dead), UnwindUnreachable())
        }
        dead = {
            receiver = &mut iterator;
            StorageDead(values);
            Call(item = get_shared(receiver, 0), ReturnTo(done), UnwindUnreachable())
        }
        done = { RET = *item; Return() }
    }
}

#[cfg(test)]
#[test]
fn native_immutable_iteration() {
    shared_zip(&[1, 2, 3]);
    incoming_address_identity(&17);
    byte_zip(&[1, 2, 3]);
    projected_zip(&Packet { channels: [-3, -2, 0, 2, 3], flags: 1 }, 0);
    returned_and_reborrowed(&[1, 2, 3]);
}


pub fn owned_nested_reference_unknown(left: &[u16; 3], other: Nested<'_>) {
    let mut iterator = left.iter();
    let _ = get_shared(&mut iterator, 0);
    let _ = other;
}

pub fn owned_nested_pointer_unknown(left: &[u16; 3], other: Pointer) {
    let mut iterator = left.iter();
    let _ = get_shared(&mut iterator, 0);
    let _ = other;
}

pub fn competing_interior_unknown(left: &[u16; 3], other: &core::cell::Cell<u8>) {
    let mut iterator = left.iter();
    let _ = get_shared(&mut iterator, 0);
    let _ = other;
}


fn returned_scalar(value: &u16) -> &u16 { value }

pub fn incoming_address_identity(value: &u16) {
    let original = value as *const u16;
    let returned = returned_scalar(value) as *const u16;
    assert!(original == returned);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn shared_write_unknown(values: &[u16; 3]) {
    mir! { let index: usize; { index = 0; (*values)[index] = 7; Return() } }
}

pub struct Feedback { pub velocity: f32 }
pub struct Motor { pub feedback: Option<Feedback> }
pub struct Bus { pub wheels: [Motor; 2], pub heard: [Option<u32>; 2] }

impl Motor {
    fn feedback(&self) -> Option<&Feedback> { self.feedback.as_ref() }
}

pub fn aggregate_feedback_views(bus: &Bus, tick: u32) -> Option<[f32; 2]> {
    let mut output = [0.0; 2];
    for ((motor, heard), destination) in bus.wheels.iter().zip(&bus.heard).zip(&mut output) {
        if heard.is_none() { return None; }
        *destination = motor.feedback()?.velocity;
    }
    let _ = tick;
    Some(output)
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
fn dead_callee_iterator() -> Iter<'static, u16> {
    mir! {
        let values: [u16; 3];
        let array: &[u16; 3];
        let slice: &[u16];
        let iterator: Iter<'static, u16>;
        {
            values = [1, 2, 3];
            array = &values;
            slice = CastUnsize(array);
            Call(iterator = <[u16]>::iter(slice), ReturnTo(dead), UnwindUnreachable())
        }
        dead = { StorageDead(values); RET = Move(iterator); Return() }
    }
}

pub fn dead_callee_source_unknown(values: &[u16; 3]) {
    let mut iterator = dead_callee_iterator();
    let _ = get_shared(&mut iterator, 0);
    let _ = values;
}

fn returned_bytes(values: &[u8; 3]) -> &[u8; 3] { values }

// A fixture-only trusted summary overrides this body and deliberately omits modifies.
pub fn fixture_opaque_boundary() {}

pub fn opaque_invalidates_incoming_byte_view(values: &[u8; 3]) -> u8 {
    let view = returned_bytes(values);
    fixture_opaque_boundary();
    view[0]
}
