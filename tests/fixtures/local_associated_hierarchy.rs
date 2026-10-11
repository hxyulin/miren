#![forbid(unsafe_code)]
#![cfg_attr(not(test), no_std)]

struct Local;
trait Child {
    fn scalar(word: u16) -> u16;
    fn leaf(values: &mut [u16], word: u16);
    fn outer(values: &mut [u16], word: u16);
    #[inline(never)]
    fn default_outer(values: &mut [u16], word: u16) {
        Self::leaf(values, word);
    }
}
impl Child for Local {
    #[inline(never)]
    fn scalar(word: u16) -> u16 {
        word ^ 0
    }
    #[inline(never)]
    fn leaf(values: &mut [u16], word: u16) {
        if values.len() > 0 {
            values[0] = <Self as Child>::scalar(word);
        }
    }
    #[inline(never)]
    fn outer(values: &mut [u16], word: u16) {
        Self::leaf(&mut *values, word);
    }
}
impl Local {
    #[inline(never)]
    fn scalar(word: u16) -> u16 {
        word ^ 0
    }
    #[inline(never)]
    fn leaf(values: &mut [u16], word: u16) {
        if values.len() > 0 {
            values[0] = Self::scalar(word);
        }
    }
    #[inline(never)]
    fn outer(values: &mut [u16], word: u16) {
        Self::leaf(&mut *values, word);
    }
    #[inline(never)]
    fn retain(values: &mut [u16]) -> &mut [u16] {
        Self::leaf(values, 17);
        values
    }
}
#[inline(never)]
fn generic_outer<T: Child>(values: &mut [u16], word: u16) {
    T::leaf(&mut *values, word);
}
#[inline(never)]
fn deeper_outer(values: &mut [u16], word: u16) {
    <Local as Child>::outer(values, word);
}

macro_rules! cases {
    ($selected:ident, $wrong:ident, $call:expr) => {
        pub fn $selected(values: &mut [u16], word: u16) {
            if values.len() > 0 {
                $call(values, word);
                assert!(values[0] == word);
            }
        }
        pub fn $wrong(values: &mut [u16], word: u16) {
            if values.len() > 0 {
                $call(values, word);
                assert!(values[0] != word);
            }
        }
    };
}
cases!(inherent, wrong_inherent, Local::outer);
cases!(implemented, wrong_implemented, <Local as Child>::outer);
cases!(defaulted, wrong_defaulted, <Local as Child>::default_outer);
cases!(generic, wrong_generic, generic_outer::<Local>);
cases!(deeper, wrong_deeper, deeper_outer);

pub fn retained(values: &mut [u16]) {
    let length = values.len();
    let result = Local::retain(values);
    assert!(result.len() == length);
}
pub fn direct_scalar(word: u16) {
    assert!(<Local as Child>::scalar(word) == word);
}
pub fn wrong_direct_scalar(word: u16) {
    assert!(<Local as Child>::scalar(word) != word);
}

#[cfg(test)]
mod tests {
    #[test]
    fn native_local_associated_claims() {
        for length in [1, 2, 129] {
            for word in [0, 1, 17, u16::MAX] {
                let mut values = std::vec![0; length];
                super::inherent(&mut values, word);
                super::implemented(&mut values, word);
                super::defaulted(&mut values, word);
                super::generic(&mut values, word);
            }
        }
    }
}
