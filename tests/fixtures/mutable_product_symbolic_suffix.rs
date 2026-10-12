#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn actual_float() -> f32 {
    f32::from_bits(0x7fc0_1234)
}
#[inline(never)]
pub fn actual_double() -> f64 {
    f64::from_bits(0x7ff8_0000_0000_1234)
}
#[inline(never)]
pub fn actual_word() -> u16 {
    37
}
#[inline(never)]
pub fn actual_inner(index: usize) -> usize {
    index ^ 0
}

pub fn float_selected(values: &mut [[f32; 2]], outer: usize, inner: usize) {
    if outer < values.len() && inner < 2 {
        let old = values[outer][1 - inner].to_bits();
        let target = actual_inner(inner);
        values[outer][target] = actual_float();
        assert!(values[outer][inner].to_bits() == 0x7fc0_1234);
        assert!(values[outer][1 - inner].to_bits() == old);
    }
}

pub fn float_other_outer(values: &mut [[f32; 2]], outer: usize, inner: usize, other: usize) {
    if outer < values.len() && other < values.len() && inner < 2 && outer != other {
        let old = values[other][inner].to_bits();
        values[outer][inner] = actual_float();
        assert!(values[other][inner].to_bits() == old);
    }
}

pub fn two_indices(values: &mut [[[u16; 2]; 2]], outer: usize, i: usize, j: usize) {
    if outer < values.len() && i < 2 && j < 2 {
        let old = values[outer][1 - i][j];
        values[outer][i][j] = actual_word();
        assert!(values[outer][i][j] == 37);
        assert!(values[outer][1 - i][j] == old);
    }
}

pub fn correlated(values: &mut [[[i32; 2]; 2]], outer: usize, i: usize) {
    if outer < values.len() && i < 2 {
        let old = values[outer][i][1 - i];
        values[outer][i][i] = -19;
        assert!(values[outer][i][i] == -19);
        assert!(values[outer][i][1 - i] == old);
    }
}

pub fn bool_selected(values: &mut [[bool; 2]], outer: usize, inner: usize) {
    if outer < values.len() && inner < 2 {
        let old = values[outer][1 - inner];
        values[outer][inner] = true;
        assert!(values[outer][inner]);
        assert!(values[outer][1 - inner] == old);
    }
}

pub fn char_selected(values: &mut [[char; 2]], outer: usize, inner: usize) {
    if outer < values.len() && inner < 2 {
        let old = values[outer][1 - inner];
        values[outer][inner] = 'λ';
        assert!(values[outer][inner] == 'λ');
        assert!(values[outer][1 - inner] == old);
    }
}

pub fn whole_tuple(values: &mut [[(u16, bool, char, f32); 2]], outer: usize, inner: usize) {
    if outer < values.len() && inner < 2 {
        let old = values[outer][1 - inner].0;
        values[outer][inner] = (actual_word(), true, 'λ', actual_float());
        let packet = values[outer][inner];
        assert!(packet.0 == 37 && packet.1 && packet.2 == 'λ');
        assert!(packet.3.to_bits() == 0x7fc0_1234);
        assert!(values[outer][1 - inner].0 == old);
    }
}

pub fn whole_array(values: &mut [[[f64; 2]; 2]], outer: usize, inner: usize) {
    if outer < values.len() && inner < 2 {
        let old = values[outer][1 - inner][0].to_bits();
        values[outer][inner] = [actual_double(), -0.0];
        let packet = values[outer][inner];
        assert!(packet[0].to_bits() == 0x7ff8_0000_0000_1234);
        assert!(packet[1].to_bits() == 0x8000_0000_0000_0000);
        assert!(values[outer][1 - inner][0].to_bits() == old);
    }
}

#[derive(Clone, Copy)]
pub struct Record {
    pub ints: [u16; 2],
    pub flag: bool,
    pub mark: char,
    pub wide: f64,
}

pub fn record_fields(values: &mut [[Record; 2]], outer: usize, inner: usize, field: usize) {
    if outer < values.len() && inner < 2 && field < 2 {
        let old = values[outer][inner].ints[1 - field];
        values[outer][inner].ints[field] = actual_word();
        values[outer][inner].flag = true;
        values[outer][inner].mark = 'λ';
        values[outer][inner].wide = actual_double();
        assert!(values[outer][inner].ints[field] == 37);
        assert!(values[outer][inner].ints[1 - field] == old);
        assert!(values[outer][inner].flag && values[outer][inner].mark == 'λ');
        assert!(values[outer][inner].wide.to_bits() == 0x7ff8_0000_0000_1234);
    }
}

pub fn tuple_fields(values: &mut [([u16; 2], bool)], outer: usize, inner: usize) {
    if outer < values.len() && inner < 2 {
        let old = values[outer].1;
        values[outer].0[inner] = actual_word();
        assert!(values[outer].0[inner] == 37);
        assert!(values[outer].1 == old);
    }
}

pub fn whole_record(values: &mut [[Record; 2]], outer: usize, inner: usize) {
    if outer < values.len() && inner < 2 {
        let old = values[outer][1 - inner].mark;
        values[outer][inner] = Record {
            ints: [37, 38],
            flag: true,
            mark: 'λ',
            wide: actual_double(),
        };
        let record = values[outer][inner];
        assert!(record.ints[0] == 37 && record.ints[1] == 38);
        assert!(record.flag && record.mark == 'λ');
        assert!(record.wide.to_bits() == 0x7ff8_0000_0000_1234);
        assert!(values[outer][1 - inner].mark == old);
    }
}

pub fn zero_selected(values: &mut [[(); 2]], outer: usize, inner: usize) {
    if outer < values.len() && inner < 2 {
        let length = values.len();
        values[outer][inner] = ();
        let _selected = values[outer][inner];
        assert!(values.len() == length);
    }
}

pub fn sequential(values: &mut [[f32; 2]], outer: usize, inner: usize) {
    if outer < values.len() && inner < 2 {
        values[outer][inner] = actual_float();
        values[outer][1 - inner] = 0.0;
        assert!(values[outer][inner].to_bits() == 0x7fc0_1234);
        assert!(values[outer][1 - inner].to_bits() == 0);
    }
}

pub fn branch(values: &mut [[u32; 2]], outer: usize, inner: usize, choose: bool) {
    if outer < values.len() && inner < 2 {
        values[outer][inner] = if choose { 17 } else { 19 };
        assert!(values[outer][inner] == if choose { 17 } else { 19 });
    }
}

pub fn current_child(values: &mut [[f32; 2]], outer: usize, inner: usize) {
    float_selected(values, outer, inner);
}

pub fn wrong_float(values: &mut [[f32; 2]], outer: usize, inner: usize) {
    if outer < values.len() && inner < 2 {
        values[outer][inner] = actual_float();
        assert!(values[outer][inner].to_bits() == 0x7fc0_1235);
    }
}

pub fn wrong_retention(values: &mut [[f32; 2]], outer: usize, inner: usize) {
    if outer < values.len() && inner < 2 {
        let old = values[outer][1 - inner].to_bits();
        values[outer][inner] = actual_float();
        assert!(values[outer][1 - inner].to_bits() != old);
    }
}

pub fn unguarded_inner(values: &mut [[f32; 2]], outer: usize, inner: usize) {
    if outer < values.len() {
        values[outer][inner] = actual_float();
    }
}

pub fn alias_unknown(values: &mut [[f32; 2]], outer: usize, inner: usize) {
    if outer < values.len() && inner < 2 {
        let alias = &mut values[outer][inner];
        *alias = actual_float();
    }
}

pub fn budget_unknown(values: &mut [[u16; 128]], outer: usize, inner: usize) {
    if outer < values.len() && inner < 128 {
        values[outer][inner] = actual_word();
    }
}

pub fn whole_budget(values: &mut [[(u16, bool, char, f32, f64); 16]], outer: usize, inner: usize) {
    if outer < values.len() && inner < 16 {
        values[outer][inner] = (37, true, 'λ', actual_float(), actual_double());
    }
}

pub fn scalar_seed(value: u16) -> u16 {
    value
}

#[cfg(test)]
mod native {
    #[test]
    fn actual_symbolic_callers_preserve_the_same_store_claims() {
        for outer in 0..2 {
            for inner in 0..2 {
                let mut values = [[-0.0; 2]; 2];
                super::float_selected(&mut values, outer, inner);
                super::current_child(&mut values, outer, inner);
                super::sequential(&mut values, outer, inner);
                super::bool_selected(&mut [[false; 2]; 2], outer, inner);
                super::char_selected(&mut [['x'; 2]; 2], outer, inner);
                super::whole_tuple(&mut [[(0, false, 'x', 0.0); 2]; 2], outer, inner);
                super::whole_array(&mut [[[0.0; 2]; 2]; 2], outer, inner);
                let record = super::Record {
                    ints: [0; 2],
                    flag: false,
                    mark: 'x',
                    wide: 0.0,
                };
                let mut records = [[record; 2]; 2];
                super::record_fields(&mut records, outer, inner, inner);
                super::whole_record(&mut records, outer, inner);
                super::tuple_fields(&mut [([0; 2], false); 2], outer, inner);
                super::zero_selected(&mut [[(); 2]; 2], outer, inner);
                super::branch(&mut [[0; 2]; 2], outer, inner, true);
                super::branch(&mut [[0; 2]; 2], outer, inner, false);
                for other in 0..2 {
                    super::float_other_outer(&mut values, outer, inner, other);
                    super::two_indices(&mut [[[0; 2]; 2]; 2], outer, inner, other);
                    super::correlated(&mut [[[0; 2]; 2]; 2], outer, inner);
                }
            }
        }
    }
}
