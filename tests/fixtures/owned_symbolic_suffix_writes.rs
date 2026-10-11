#![no_std]
#![forbid(unsafe_code)]

#[inline(never)]
pub fn actual_word(word: u16) -> u16 {
    word ^ 0
}

pub fn selected(mut values: [[[u16; 2]; 2]; 2], i: usize, j: usize, k: usize, word: u16) {
    if i < 2 && j < 2 && k < 2 {
        let old = values;
        values[i][j][k] = actual_word(word);
        assert!(values[i][j][k] == word);
        assert!(values[i ^ 1][j][k] == old[i ^ 1][j][k]);
        assert!(values[i][j ^ 1][k] == old[i][j ^ 1][k]);
        assert!(values[i][j][k ^ 1] == old[i][j][k ^ 1]);
    }
}

pub fn wrong(mut values: [[[u16; 2]; 2]; 2], i: usize, j: usize, k: usize, word: u16) {
    if i < 2 && j < 2 && k < 2 {
        values[i][j][k] = actual_word(word);
        assert!(values[i][j][k] == word ^ 1);
    }
}

pub fn correlated(mut values: [[[u16; 2]; 2]; 2], i: usize, word: u16) {
    if i < 2 {
        let old = values;
        values[i][i][i] = actual_word(word);
        assert!(values[i][i][i] == word);
        assert!(values[i][i ^ 1][i] == old[i][i ^ 1][i]);
    }
}

pub fn tuple_field(mut values: ([[[u16; 2]; 2]; 2], u16), i: usize, j: usize, k: usize) {
    if i < 2 && j < 2 && k < 2 {
        let old = values;
        values.0[i][j][k] = actual_word(19);
        assert!(values.0[i][j][k] == 19 && values.1 == old.1);
    }
}

pub fn sequential(mut values: [[[u16; 2]; 2]; 2], i: usize, j: usize, k: usize) {
    if i < 2 && j < 2 && k < 2 {
        values[i][j][k] = actual_word(19);
        values[i][j][k ^ 1] = actual_word(23);
        assert!(values[i][j][k] == 19 && values[i][j][k ^ 1] == 23);
    }
}

pub fn mixed(mut values: [[[u16; 2]; 2]; 2], i: usize, j: usize) {
    if i < 2 && j < 2 {
        values[0][i][j] = actual_word(19);
        assert!(values[0][i][j] == 19);
    }
}

pub fn branch(mut values: [[[u16; 2]; 2]; 2], i: usize, j: usize, k: usize, choose: bool) {
    if i < 2 && j < 2 && k < 2 {
        if choose {
            values[i][j][k] = actual_word(19);
        } else {
            values[i][j][k] = actual_word(23);
        }
        assert!(values[i][j][k] == if choose { 19 } else { 23 });
    }
}

pub fn two_indices(mut values: [[u16; 2]; 2], i: usize, j: usize) {
    if i < 2 && j < 2 {
        values[i][j] = actual_word(19);
        assert!(values[i][j] == 19);
    }
}

pub fn wrong_two_indices(mut values: [[u16; 2]; 2], i: usize, j: usize) {
    if i < 2 && j < 2 {
        values[i][j] = actual_word(19);
        assert!(values[i][j] == 20);
    }
}

pub fn unsupported_ref<'a>(mut values: [[[&'a u16; 2]; 2]; 2], i: usize, j: usize, k: usize) {
    if i < 2 && j < 2 && k < 2 {
        values[i][j][k] = values[0][0][0];
        assert!(*values[i][j][k] == *values[0][0][0]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_valid_indices_and_current_siblings() {
        for i in 0..2 {
            for j in 0..2 {
                for k in 0..2 {
                    let values = [[[3, 5], [7, 11]], [[13, 17], [19, 23]]];
                    selected(values, i, j, k, 29);
                    correlated(values, i, 31);
                    tuple_field((values, 37), i, j, k);
                    sequential(values, i, j, k);
                    mixed(values, j, k);
                    branch(values, i, j, k, true);
                    branch(values, i, j, k, false);
                    two_indices(values[0], j, k);
                }
            }
        }
    }
}
