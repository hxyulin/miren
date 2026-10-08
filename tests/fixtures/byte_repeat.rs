#![no_std]
#![forbid(unsafe_code)]

pub fn repeated_byte_storage(byte: u8, index: usize) {
    let mut bytes = [byte; 4096];
    assert!(bytes.len() == 4096);
    if index < bytes.len() {
        assert!(bytes[index] == byte);
        bytes[index] = byte.wrapping_add(1);
        assert!(bytes[index] == byte.wrapping_add(1));
        if index != 4095 {
            assert!(bytes[4095] == byte);
        }
    }
}

pub fn wrong_repeated_byte(byte: u8) {
    let bytes = [byte; 4096];
    assert!(bytes[4095] != byte);
}

pub fn unbounded_repeated_index(index: usize) -> u8 {
    let bytes = [7_u8; 4096];
    bytes[index]
}

pub fn expanded_nonbyte_repeat() -> [u16; 129] {
    [7_u16; 129]
}

pub fn oversized_owned_repeat() -> [(u16, u16); 128] {
    [(7, 8); 128]
}

pub fn repeated_references(value: &u8) -> [&u8; 129] {
    [value; 129]
}

#[cfg(test)]
#[test]
fn native_byte_reads_and_updates() {
    for byte in [0, 1, 127, 255] {
        for index in [0, 128, 4095, 4096] {
            repeated_byte_storage(byte, index);
        }
    }
}
