#![no_std]
#![forbid(unsafe_code)]

const fn words() -> [u16; 256] {
    let mut table = [0; 256];
    let mut index = 0;
    while index < 256 {
        table[index] = index as u16;
        index += 1;
    }
    table
}

const WORDS: [[u16; 256]; 1] = [words()];
const BYTES: [u8; 256] = [23; 256];
const BOOLS: [bool; 256] = [true; 256];
const SIGNED: [i16; 256] = [-7; 256];
const FLOATS: [f32; 256] = [f32::from_bits(0x7fc0_1234); 256];
const DOUBLES: [f64; 256] = [f64::from_bits(0x8000_0000_0000_0000); 256];
const OVER_SCALARS: [u16; 257] = [7; 257];
const OVER_COMPOSITES: [(u16, u16); 129] = [(7, 7); 129];
const OVER_TOTAL: [[u16; 256]; 8] = [[7; 256]; 8];
const UNINITIALIZED: [core::mem::MaybeUninit<u16>; 256] = [core::mem::MaybeUninit::uninit(); 256];

pub fn table_lookup(index: u8) {
    assert!(WORDS[0][index as usize] == index as u16);
    assert!(BYTES[index as usize] == 23);
    assert!(BOOLS[index as usize]);
    assert!(SIGNED[index as usize] == -7);
}

pub fn float_bits(index: u8) {
    assert!(FLOATS[index as usize].to_bits() == 0x7fc0_1234);
    assert!(DOUBLES[index as usize].to_bits() == 0x8000_0000_0000_0000);
}

pub fn guarded_lookup(index: usize) {
    if index < 256 {
        assert!(WORDS[0][index] == index as u16);
    }
}

pub fn bounds_failure(index: usize) -> u16 {
    WORDS[0][index]
}
pub fn scalar_budget() -> [u16; 257] {
    OVER_SCALARS
}
pub fn composite_budget() -> [(u16, u16); 129] {
    OVER_COMPOSITES
}
pub fn total_budget() -> [[u16; 256]; 8] {
    OVER_TOTAL
}
pub fn uninitialized_table() -> [core::mem::MaybeUninit<u16>; 256] {
    UNINITIALIZED
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_tables_preserve_values_and_float_bits() {
        for index in 0..=255 {
            table_lookup(index);
            float_bits(index);
            guarded_lookup(index as usize);
        }
        guarded_lookup(256);
    }

    #[test]
    #[should_panic]
    fn native_bounds_check_rejects_one_past_end() {
        bounds_failure(256);
    }
}
