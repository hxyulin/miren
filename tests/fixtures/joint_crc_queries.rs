#![no_std]
#![forbid(unsafe_code)]
#![feature(custom_mir, core_intrinsics)]

use core::intrinsics::mir::*;

const fn table() -> [u16; 256] {
    let mut values = [0_u16; 256];
    let mut index = 0;
    while index < values.len() {
        let mut value = index as u16;
        let mut bit = 0;
        while bit < 8 {
            value = if value & 1 != 0 {
                (value >> 1) ^ 0xa001
            } else {
                value >> 1
            };
            bit += 1;
        }
        values[index] = value;
        index += 1;
    }
    values
}

const TABLE: [u16; 256] = table();

fn checksum(bytes: &[u8]) -> u16 {
    let mut crc = 0xffff_u16;
    let mut position = 0;
    while position < bytes.len() {
        let index = usize::from((crc ^ u16::from(bytes[position])) & 0xff);
        crc = TABLE[index] ^ (crc >> 8);
        position += 1;
    }
    crc
}

pub fn packet_checksum(payload: [u8; 12]) -> u16 {
    let mut packet = [0_u8; 136];
    packet[..5].copy_from_slice(&[1, 2, 3, 4, 5]);
    packet[5..17].copy_from_slice(&payload);
    checksum(&packet[..17])
}

pub fn standard_vector() {
    assert!(checksum(b"123456789") == 0x4b37);
}

pub fn wrong_checksum_claim() {
    assert!(checksum(b"123456789") == 0x4b36);
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn unsupported_pointer_read(pointer: *const u8) {
    mir! { let value: u8; { value = *pointer; Return() } }
}

#[cfg(test)]
#[test]
fn native_crc_vectors_and_symbolic_packet_inputs() {
    standard_vector();
    for seed in 0..16_u8 {
        packet_checksum([seed; 12]);
    }
}
