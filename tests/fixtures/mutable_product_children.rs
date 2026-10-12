#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn stored_float() -> f32 {
    f32::from_bits(0x7fc0_1234)
}

#[inline(never)]
pub fn write_float(values: &mut [[f32; 2]], index: usize) {
    if index < values.len() {
        values[index][0] = stored_float();
    }
}

pub fn float_call(values: &mut [[f32; 2]], index: usize) {
    if index < values.len() {
        let untouched = values[index][1].to_bits();
        write_float(values, index);
        assert!(values[index][0].to_bits() == 0x7fc0_1234);
        assert!(values[index][1].to_bits() == untouched);
    }
}

pub fn wrong_float_call(values: &mut [[f32; 2]], index: usize) {
    if index < values.len() {
        write_float(values, index);
        assert!(values[index][0].to_bits() == 0x7fc0_1235);
    }
}

pub fn sequential(values: &mut [[f32; 2]]) {
    if values.len() >= 2 {
        let untouched = values[1][1].to_bits();
        write_float(values, 0);
        write_float(values, 1);
        assert!(values[0][0].to_bits() == 0x7fc0_1234);
        assert!(values[1][0].to_bits() == 0x7fc0_1234);
        assert!(values[1][1].to_bits() == untouched);
    }
}

pub fn false_retention(values: &mut [[f32; 2]]) {
    if values.len() >= 2 {
        let untouched = values[1][1].to_bits();
        write_float(values, 0);
        assert!(values[1][1].to_bits() != untouched);
    }
}

#[inline(never)]
pub fn wide_return(values: &mut [[f64; 2]], index: usize) -> u64 {
    if index < values.len() {
        values[index] = [-0.0, f64::from_bits(0x7ff8_0000_0000_1234)];
        values[index][0].to_bits()
    } else {
        0
    }
}

pub fn wide_call(values: &mut [[f64; 2]], index: usize) {
    if index < values.len() {
        let bits = wide_return(values, index);
        assert!(bits == 0x8000_0000_0000_0000);
        assert!(values[index][1].to_bits() == 0x7ff8_0000_0000_1234);
    }
}

#[inline(never)]
pub fn write_tuple(values: &mut [(bool, char)], index: usize) {
    if index < values.len() {
        values[index] = (true, '\u{1f980}');
    }
}

pub fn tuple_call(values: &mut [(bool, char)], index: usize) {
    if index < values.len() {
        write_tuple(values, index);
        assert!(values[index].0 && values[index].1 as u32 == 0x1f980);
    }
}

#[derive(Clone, Copy)]
pub struct Record {
    pub word: u16,
    pub ready: bool,
}

#[inline(never)]
pub fn write_record(values: &mut [Record], index: usize) {
    if index < values.len() {
        values[index].ready = true;
    }
}

pub fn record_call(values: &mut [Record], index: usize) {
    if index < values.len() {
        let old = values[index].word;
        write_record(values, index);
        assert!(values[index].ready && values[index].word == old);
    }
}

#[inline(never)]
pub fn metadata_child(values: &mut [[f32; 2]]) -> bool {
    let length = values.len();
    assert!(values.is_empty() == (length == 0));
    values.is_empty()
}

pub fn metadata_call(values: &mut [[f32; 2]]) {
    let empty = metadata_child(values);
    assert!(empty == (values.len() == 0));
}

#[inline(never)]
pub fn zero_child(values: &mut [()], index: usize) {
    if index < values.len() {
        values[index] = ();
    }
}

pub fn zero_call(values: &mut [()], index: usize) {
    let length = values.len();
    zero_child(values, index);
    assert!(values.len() == length);
}

#[inline(never)]
pub fn unchecked_child(values: &mut [[f32; 2]], index: usize) {
    values[index][0] = stored_float();
}

pub fn unchecked_call(values: &mut [[f32; 2]], index: usize) {
    unchecked_child(values, index);
    let _ = values.len();
}

#[inline(never)]
pub fn nested_child(values: &mut [[f32; 2]], index: usize) {
    write_float(values, index);
    let _ = values.len();
}

pub fn nested_owner_unknown(values: &mut [[f32; 2]], index: usize) {
    nested_child(values, index);
    let _ = values.len();
}

pub fn moved_parent_unknown(values: &mut [[f32; 2]], index: usize) {
    let moved = values;
    write_float(moved, index);
}

pub fn interval_unknown(values: &mut [[f32; 2]]) {
    if !values.is_empty() {
        write_float(&mut values[0..1], 0);
        let _ = values.len();
    }
}

#[inline(never)]
pub fn symbolic_child(values: &mut [[f32; 2]], outer: usize, inner: usize) {
    if outer < values.len() && inner < 2 {
        values[outer][inner] = stored_float();
    }
}

pub fn symbolic_unknown(values: &mut [[f32; 2]], outer: usize, inner: usize) {
    symbolic_child(values, outer, inner);
    let _ = values.len();
}

#[inline(never)]
pub fn returned_owner(values: &mut [[f32; 2]]) -> &mut [[f32; 2]] {
    values
}

pub fn escape_unknown(values: &mut [[f32; 2]]) {
    let child = returned_owner(values);
    let _ = child.len();
}

pub fn scalar_seed(value: u16) -> u16 {
    value
}

#[cfg(test)]
mod native {
    #[test]
    fn callers_keep_their_actual_store_claims() {
        let mut values = [[1.0, -0.0], [f32::from_bits(0x7fc0_4567), 3.0]];
        super::float_call(&mut values, 0);
        super::float_call(&mut values, 1);
        super::sequential(&mut values);
        super::metadata_call(&mut values);
        super::metadata_call(&mut []);
        let mut wide = [[1.0, 2.0]];
        super::wide_call(&mut wide, 0);
        let mut tuple = [(false, 'a')];
        super::tuple_call(&mut tuple, 0);
        let mut record = [super::Record {
            word: 7,
            ready: false,
        }];
        super::record_call(&mut record, 0);
        assert!(record[0].word == 7);
        super::zero_call(&mut [(), ()], 1);
    }
}

// Standalone compiler identity controls; never called by an analyzed guest claim.
pub mod host_float_impostor {
    pub fn from_bits(_: u32) -> f32 {
        0.0
    }
}
