#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;

pub fn fixed_packet_header() {
    let mut packet = [0_u8; 136];
    packet[..5].copy_from_slice(&[1, 2, 3, 4, 5]);
    assert!(packet[0] == 1);
    assert!(packet[4] == 5);
    assert!(packet[5] == 0);
    assert!(packet[135] == 0);
}

pub fn empty_end_range() {
    let mut packet = [9_u8; 136];
    packet[136..136].copy_from_slice(&[]);
    assert!(packet[135] == 9);
}

pub fn fixed_middle_preserves_neighbors() {
    let mut packet = [9_u8; 256];
    packet[127..131].copy_from_slice(&[1, 2, 3, 4]);
    assert!(packet[126] == 9);
    assert!(packet[127] == 1);
    assert!(packet[130] == 4);
    assert!(packet[131] == 9);
    assert!(packet[255] == 9);
}

pub fn guarded_offset(offset: usize) {
    let mut packet = [0_u8; 136];
    if offset <= 132 {
        packet[offset..offset + 4].copy_from_slice(&[1, 2, 3, 4]);
        assert!(packet[offset] == 1);
        assert!(packet[offset + 3] == 4);
    }
}

pub fn nested_region() {
    let mut packet = [0_u8; 256];
    let region = &mut packet[64..200];
    region[5..9].copy_from_slice(&[1, 2, 3, 4]);
    assert!(packet[68] == 0);
    assert!(packet[69] == 1);
    assert!(packet[72] == 4);
    assert!(packet[73] == 0);
    assert!(packet[255] == 0);
}

pub fn large_compact_allocation() {
    let mut packet = [7_u8; 4096];
    packet[4000..4004].copy_from_slice(&[1, 2, 3, 4]);
    assert!(packet[3999] == 7);
    assert!(packet[4000] == 1);
    assert!(packet[4003] == 4);
    assert!(packet[4004] == 7);
    assert!(packet[4095] == 7);
}

pub fn exact_write_budget() {
    let mut packet = [0_u8; 256];
    packet[64..192].copy_from_slice(&[7_u8; 128]);
    assert!(packet[63] == 0);
    assert!(packet[64] == 7);
    assert!(packet[191] == 7);
    assert!(packet[192] == 0);
}

pub fn wrong_preserved_tail() {
    let mut packet = [0_u8; 136];
    packet[..5].copy_from_slice(&[1, 2, 3, 4, 5]);
    assert!(packet[135] == 5);
}

pub fn unbounded_offset(offset: usize) {
    let mut packet = [0_u8; 136];
    packet[offset..offset + 4].copy_from_slice(&[1, 2, 3, 4]);
}

pub fn over_write_budget() {
    let mut packet = [0_u8; 256];
    packet[..129].copy_from_slice(&[7_u8; 129]);
    assert!(packet[0] == 7);
}

pub fn symbolic_write_length(length: usize) {
    let mut packet = [0_u8; 136];
    let source = [7_u8; 136];
    if length <= 4 {
        packet[..length].copy_from_slice(&source[..length]);
        assert!(packet[135] == 0);
    }
}

fn write_header(packet: &mut [u8; 136]) {
    packet[..5].copy_from_slice(&[1, 2, 3, 4, 5]);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn dead_destination() {
    mir! {
        let storage: [u8; 136];
        let borrowed: &mut [u8; 136];
        {
            storage = [0_u8; 136];
            borrowed = &mut storage;
            Goto(next)
        }
        next = {
            StorageDead(storage);
            Call(RET = write_header(Move(borrowed)), ReturnTo(done), UnwindUnreachable())
        }
        done = { Return() }
    }
}

#[cfg(test)]
#[test]
fn native_fixed_writes() {
    fixed_packet_header();
    empty_end_range();
    fixed_middle_preserves_neighbors();
    for offset in [0, 1, 128, 132, 133, usize::MAX] {
        guarded_offset(offset);
    }
    nested_region();
    large_compact_allocation();
    exact_write_budget();
}
