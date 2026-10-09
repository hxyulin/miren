#![no_std]
pub fn correlated(index: usize) {
    let values = [(3u32, 7u32), (5, 11), (9, 19)];
    if index < values.len() {
        let value = values[index];
        assert!(value.1 == value.0 * 2 + 1);
    }
}
pub fn nested(index: usize) {
    let values = [((true, -3i16), ((), 8u64)), ((false, 4), ((), 9))];
    if index < 2 {
        let value = values[index];
        if value.0.0 { assert!(value.0.1 == -3 && value.1.1 == 8); }
        else { assert!(value.0.1 == 4 && value.1.1 == 9); }
    }
}
pub fn floats(index: usize) {
    let values = [(1.0f32, true), (2.0, false)];
    if index < 2 {
        let value = values[index];
        if value.1 { assert!(value.0 == 1.0); } else { assert!(value.0 == 2.0); }
    }
}
pub fn units(index: usize) { let values = [(), ()]; if index < 2 { let _ = values[index]; } }
pub fn wrong_claim(index: usize) {
    let values = [(3u32, 7u32), (5, 11)];
    if index < 2 { assert!(values[index].1 == 7); }
}
pub fn bounds_failure(index: usize) { let values = [(3u32, 7u32), (5, 11)]; let _ = values[index]; }
pub fn references(index: usize) {
    let a=3; let b=5; let values=[(&a, 7u32), (&b, 11)];
    if index < 2 { let value=values[index]; assert!(*value.0 * 2 + 1 == value.1); }
}
#[derive(Clone, Copy)]
struct Pair { left: u32, right: u32 }
pub fn structs(index: usize) {
    let values=[(Pair {left:3,right:7}, ()), (Pair {left:5,right:11}, ())];
    if index < 2 { let value=values[index]; assert!(value.0.right == value.0.left*2+1); }
}
pub fn symbolic_write(index: usize) {
    let mut values=[(3u32,7u32),(5,11)];
    if index < 2 { values[index]=(9,19); assert!(values[index].1==19); }
}
#[cfg(test)]
#[test]
fn native_valid_values() {
    for index in 0..3 { correlated(index); nested(index); floats(index); units(index); }
}

pub fn incoming(values: [(u32, bool); 2], index: usize) {
    if index < 2 {
        let selected = values[index];
        if index == 0 {
            assert!(selected.0 == values[0].0 && selected.1 == values[0].1);
        } else {
            assert!(selected.0 == values[1].0 && selected.1 == values[1].1);
        }
    }
}

pub fn float_bits(index: usize) {
    let values = [
        (f32::from_bits(0x80000000), f64::from_bits(0x8000000000000000),
         (0x80000000u32, 0x8000000000000000u64)),
        (f32::from_bits(0x7fc00015), f64::from_bits(0x7ff8000000000015),
         (0x7fc00015, 0x7ff8000000000015)),
    ];
    if index < 2 {
        let value = values[index];
        assert!(value.0.to_bits() == value.2.0);
        assert!(value.1.to_bits() == value.2.1);
    }
}
#[cfg(test)]
#[test]
fn native_float_bits() { for index in 0..2 { float_bits(index); } }

struct Drops;
impl Drop for Drops { fn drop(&mut self) {} }
pub fn drop_zst(index: usize) {
    let values = [(Drops, ()), (Drops, ())];
    if index < 2 { let _ = &values[index]; }
}

pub fn wrong_float_bits(index: usize) {
    let values = [(f32::from_bits(0x80000000), 0u32),
                  (f32::from_bits(0x7fc00015), 0x7fc00015)];
    if index < 2 { let value = values[index]; assert!(value.0.to_bits() == value.1); }
}
#[cfg(test)]
#[test]
#[should_panic]
fn native_wrong_float_bits() { wrong_float_bits(0); }
pub fn incoming_references(values: [(&u32, u32); 2], index: usize) {
    if index < 2 {
        let selected = values[index];
        if index == 0 { assert!(*selected.0 == *values[0].0 && selected.1 == values[0].1); }
        else { assert!(*selected.0 == *values[1].0 && selected.1 == values[1].1); }
    }
}

#[cfg(test)]
#[test]
fn native_incoming_snapshots() {
    let a = 3; let b = 5;
    for index in 0..2 { incoming_references([(&a, 7), (&b, 11)], index); }
}

pub fn incoming_reference_address(values: [(&u32, u32); 2], index: usize) {
    if index < 2 {
        let address = values[index].0 as *const u32 as usize;
        assert!(address != 0);
    }
}
