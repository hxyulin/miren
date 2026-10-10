#![no_std]

#[derive(Clone, Copy)]
pub struct Record {
    pub words: [u8; 2],
    pub mark: u16,
    pub character: char,
    pub floating: f32,
}
#[derive(Clone, Copy)]
pub struct Zero;

#[inline(never)]
pub fn replace(mut values: [(u16, u16); 2], index: usize) -> [(u16, u16); 2] {
    values[index] = (19, 23);
    values
}
pub fn mutation_claim(index: usize) {
    let original = [(3, 7), (5, 11)];
    if index < 2 {
        let updated = replace(original, index);
        assert!(updated[index] == (19, 23));
        assert!(updated[index ^ 1] == original[index ^ 1]);
        assert!(original[0] == (3, 7) && original[1] == (5, 11));
    }
}
pub fn primitive(mut values: [u32; 2], index: usize) {
    if index < 2 {
        let before = values;
        values[index] = 19;
        assert!(values[index] == 19);
        assert!(values[index ^ 1] == before[index ^ 1]);
    }
}
pub fn tuple(mut values: [(i16, bool, u32); 2], index: usize) {
    if index < 2 {
        let before = values;
        values[index] = (-7, true, 19);
        let selected = values[index];
        assert!(selected.0 == -7 && selected.1 && selected.2 == 19);
        let untouched = values[index ^ 1];
        let old = before[index ^ 1];
        assert!(untouched == old);
    }
}
pub fn nested(mut values: [[(u16, bool); 2]; 2], index: usize) {
    if index < 2 {
        let before = values;
        values[index] = [(19, true), (23, false)];
        let copy = values[index];
        assert!(copy[0].0 == 19 && copy[0].1);
        assert!(copy[1].0 == 23 && !copy[1].1);
        let untouched = values[index ^ 1];
        assert!(untouched[1] == before[index ^ 1][1]);
    }
}
pub fn bytes(mut values: [[u8; 2]; 2], index: usize) {
    if index < 2 {
        let before = values;
        values[index] = [19, 23];
        let row = values[index];
        assert!(row[0] == 19 && row[1] == 23);
        let untouched = values[index ^ 1];
        assert!(untouched[0] == before[index ^ 1][0]);
    }
}
pub fn record(mut values: [Record; 2], index: usize) {
    if index < 2 {
        let before = values;
        values[index] = Record {
            words: [19, 23], mark: 7, character: '\u{10ffff}', floating: -0.0,
        };
        let copy = values[index];
        assert!(copy.words[1] == 23 && copy.mark == 7 && copy.character == '\u{10ffff}');
        assert!(copy.floating.to_bits() == (-0.0f32).to_bits());
        let untouched = values[index ^ 1];
        let old = before[index ^ 1];
        assert!(untouched.words[0] == old.words[0]);
        assert!(untouched.floating.to_bits() == old.floating.to_bits());
    }
}
pub fn float_char(mut values: [(f32, f64, char); 2], index: usize) {
    if index < 2 {
        let before = values;
        values[index] = (-0.0, f64::from_bits(0x7ff8000000000123), '\u{d7ff}');
        let copy = values[index];
        assert!(copy.0.to_bits() == (-0.0f32).to_bits());
        assert!(copy.1.to_bits() == 0x7ff8000000000123);
        assert!(copy.2 == '\u{d7ff}');
        let old = before[index ^ 1];
        let untouched = values[index ^ 1];
        assert!(untouched.0.to_bits() == old.0.to_bits());
        assert!(untouched.2 == old.2);
    }
}
pub fn sequential(mut values: [(u16, u16); 2], first: usize, second: usize) {
    if first < 2 && second < 2 {
        let before = values;
        values[first] = (19, 23);
        values[second] = (29, 31);
        assert!(values[second] == (29, 31));
        if first != second {
            assert!(values[first] == (19, 23));
        } else {
            assert!(values[first ^ 1] == before[first ^ 1]);
        }
    }
}
pub fn allocated_source(index: usize) {
    let mut values = [(3u16, 7u16), (5, 11)];
    if index < 2 {
        let read = &values;
        assert!(read[0].0 == 3);
        values[index] = (19, 23);
        assert!(values[index].1 == 23);
    }
}
pub fn unit_product(mut values: [((), [u16; 0]); 2], index: usize) {
    if index < 2 {
        values[index] = ((), []);
        let copy = values[index];
        assert!(copy.0 == () && copy.1.len() == 0);
    }
}

pub fn nominal_zero(mut values: [Zero; 2], index: usize) {
    if index < 2 {
        values[index] = Zero;
        let copied = values[index];
        assert!(core::mem::size_of_val(&copied) == 0);
    }
}
pub fn constant_reference<'a>(mut values: [&'a u16; 2], replacement: &'a u16) {
    values[0] = replacement;
    assert!(*values[0] == *replacement);
}
pub fn wrong_field(index: usize) {
    if index < 2 {
        let values = replace([(3, 7), (5, 11)], index);
        assert!(values[index].1 == 19);
    }
}
pub fn wrong_overwrite(mut values: [(u16, u16); 2], index: usize) {
    if index < 2 {
        values[index] = (19, 23);
        values[index] = (29, 31);
        assert!(values[index].0 == 19);
    }
}
pub fn bounds(mut values: [(u16, u16); 2], index: usize) {
    values[index] = (19, 23);
}
pub fn nan_reflexive(mut values: [f64; 2], index: usize) {
    if index < 2 {
        values[index] = f64::NAN;
        assert!(values[index] == values[index]);
    }
}
pub fn reference_store<'a>(mut values: [&'a u16; 2], replacement: &'a u16, index: usize) {
    if index < 2 {
        values[index] = replacement;
    }
}
pub fn raw_store(mut values: [*const u16; 2], replacement: *const u16, index: usize) {
    if index < 2 {
        values[index] = replacement;
    }
}
pub fn retained_store(values: &mut [(u16, u16); 2], index: usize) {
    if index < 2 {
        values[index] = (19, 23);
    }
}
pub fn deeper_store(mut values: [[u16; 2]; 2], index: usize) {
    if index < 2 {
        values[index][0] = 19;
    }
}
pub fn oversized(mut values: [[u16; 129]; 2], replacement: [u16; 129], index: usize) {
    if index < 2 {
        values[index] = replacement;
    }
}

#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn positives() {
        for index in [0, 1, 2, usize::MAX] {
            mutation_claim(index);
            primitive([3, 7], index);
            tuple([(3, false, 7), (5, true, 11)], index);
            nested([[(3, false), (7, true)]; 2], index);
            bytes([[3, 7], [5, 11]], index);
            float_char([(f32::NAN, 0.0, '\0'); 2], index);
            record([Record {words:[3,7], mark:1, character:'\0', floating:f32::NAN};2], index);
            allocated_source(index);
            nominal_zero([Zero; 2], index);
            unit_product([((), []); 2], index);
            for second in 0..3 { sequential([(3,7),(5,11)], index, second); }
        }
        constant_reference([&3, &7], &11);
    }
    #[test]
    fn mutation_guard() { mutation_claim(1); }
    #[test]
    #[should_panic]
    fn negative_field() { wrong_field(1); }
    #[test]
    #[should_panic]
    fn negative_overwrite() { wrong_overwrite([(3,7),(5,11)], 1); }
    #[test]
    #[should_panic]
    fn negative_bounds() { bounds([(3,7),(5,11)], 2); }
    #[test]
    #[should_panic]
    fn negative_nan() { nan_reflexive([0.0;2], 1); }
}
