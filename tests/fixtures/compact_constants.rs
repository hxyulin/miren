#![no_std]
#![forbid(unsafe_code)]

#[derive(Clone, Copy)]
struct Configuration {
    coefficients: [[f32; 6]; 40],
}

const fn coefficients() -> [[f32; 6]; 40] {
    let mut values = [[0.0; 6]; 40];
    let mut row = 0;
    while row < 40 {
        let mut column = 0;
        while column < 6 {
            values[row][column] = (row * 6 + column) as f32;
            column += 1;
        }
        row += 1;
    }
    values
}

const COEFFICIENTS: [[f32; 6]; 40] = coefficients();
const SHARED_ROWS: [[u16; 8]; 64] = [[23; 8]; 64];
const OVER_BUDGET: [[u16; 16]; 128] = [[7; 16]; 128];
const OVER_ELEMENTS: [(u16, u16); 129] = [(7, 7); 129];

pub fn initialized_configuration_copies() {
    let mut changed = Configuration {
        coefficients: COEFFICIENTS,
    };
    let original = changed;
    changed.coefficients[39][5] = 999.0;
    assert!(original.coefficients[39][5] == 239.0);
    assert!(changed.coefficients[39][5] == 999.0);
    assert!(changed.coefficients[0][0] == 0.0);
}

pub fn initialized_shared_rows() {
    let mut changed = SHARED_ROWS;
    let original = changed;
    changed[0][0] = 17;
    assert!(changed[1][0] == 23);
    assert!(original[0][0] == 23);
}

pub fn lqr_default_repeat() {
    let mut gains = [[0.0_f32; 6]; 40];
    gains[0][0] = 17.0;
    assert!(gains[39][0] == 0.0);
    assert!(gains[0][0] == 17.0);
}

pub fn deep_repeat(value: u16) {
    let mut values = [[[value; 8]; 8]; 8];
    values[0][0][0] = 19;
    assert!(values[7][0][0] == value);
}

pub fn constant_bounds_failure(index: usize) -> f32 {
    let configuration = Configuration {
        coefficients: COEFFICIENTS,
    };
    configuration.coefficients[index][0]
}

pub fn constant_value_budget() -> [[u16; 16]; 128] {
    OVER_BUDGET
}
pub fn constant_element_budget() -> [(u16, u16); 129] {
    OVER_ELEMENTS
}
pub fn repeat_clone_budget(value: u16) -> [(u16, u16); 86] {
    [(value, value); 86]
}
pub fn repeat_element_budget(value: u16) -> [u16; 129] {
    [value; 129]
}
pub fn interior_repeat() -> [core::cell::Cell<u16>; 40] {
    [const { core::cell::Cell::new(23) }; 40]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_initialized_constants_and_repeats_keep_independent_storage() {
        initialized_configuration_copies();
        initialized_shared_rows();
        lqr_default_repeat();
        deep_repeat(23);
    }
}
