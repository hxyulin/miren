#![no_std]
#![forbid(unsafe_code)]
#[inline(never)]
pub fn child(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        values[index] = word ^ 0;
    }
}
#[inline(never)]
pub fn scalar_child(values: &mut [u16], index: usize, word: u16) -> u16 {
    if index < values.len() {
        values[index] = word;
        values[index]
    } else {
        0
    }
}
pub fn selected(values: &mut [u16], start: usize, end: usize, index: usize, word: u16) {
    if start <= end && end <= values.len() && index < end - start {
        child(&mut values[start..end], index, word);
        assert!(values[start + index] == word);
    }
}
pub fn wrong(values: &mut [u16], start: usize, end: usize, index: usize, word: u16) {
    if start <= end && end <= values.len() && index < end - start {
        child(&mut values[start..end], index, word);
        assert!(values[start + index] != word);
    }
}
pub fn wrong_offset(values: &mut [u16], start: usize, end: usize, index: usize, word: u16) {
    if start <= end && end <= values.len() && index < end - start {
        child(&mut values[start..end], index, word);
        assert!(values[index] == word);
    }
}
pub fn empty_preserves_payload(values: &mut [u16], point: usize) {
    if point < values.len() {
        let old = values[point];
        child(&mut values[point..point], 0, 19);
        assert!(values[point] == old);
    }
}
pub fn untouched(values: &mut [u16], start: usize, end: usize, index: usize, other: usize) {
    if start <= end && end <= values.len() && index < end - start
        && other < values.len() && other != start + index
    {
        let old = values[other];
        child(&mut values[start..end], index, 19);
        assert!(values[other] == old);
    }
}
pub fn scalar_return(values: &mut [u16], start: usize, end: usize, index: usize, word: u16) {
    if start <= end && end <= values.len() && index < end - start {
        let result = scalar_child(&mut values[start..end], index, word);
        assert!(result == word && values[start + index] == word);
    }
}
pub fn empty(values: &mut [u16], point: usize) {
    if point <= values.len() {
        child(&mut values[point..point], 0, 19);
        assert!(values.len() >= point);
    }
}
pub fn sequential(values: &mut [u16], start: usize, end: usize) {
    if start < end && end <= values.len() {
        child(&mut values[start..end], 0, 17);
        child(&mut values[start..end], 0, 29);
        assert!(values[start] == 29);
    }
}
pub fn branches(values: &mut [u16], start: usize, end: usize, choice: bool) {
    if start < end && end <= values.len() {
        if choice { child(&mut values[start..end], 0, 17); }
        else { child(&mut values[start..end], 0, 29); }
        assert!(values[start] == if choice { 17 } else { 29 });
    }
}
pub fn unguarded(values: &mut [u16], start: usize, end: usize) {
    child(&mut values[start..end], 0, 19);
}
pub fn retained_view(values: &mut [u16], start: usize, end: usize) {
    if start < end && end <= values.len() {
        let view = &mut values[start..end];
        view[0] = 19;
        assert!(view[0] == 19);
    }
}
#[inline(never)]
pub fn nested_child(values: &mut [u16]) { child(values, 0, 19); }
pub fn nested(values: &mut [u16], start: usize, end: usize) {
    if start <= end && end <= values.len() { nested_child(&mut values[start..end]); }
}
pub fn whole_anchor(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        child(values, index, word);
        assert!(values[index] == word);
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn valid_interval_cases() {
        for start in 0..129 {
            for end in start..=129 {
                let mut values = [7; 129];
                empty(&mut values, start);
                empty_preserves_payload(&mut values, start);
                if start < end {
                    selected(&mut values, start, end, end - start - 1, 31);
                    untouched(&mut values, start, end, 0, 128);
                    scalar_return(&mut values, start, end, 0, 23);
                    sequential(&mut values, start, end);
                    branches(&mut values, start, end, true);
                    branches(&mut values, start, end, false);
                }
            }
        }
    }
    #[test]
    fn mutation_guard() {
        let mut values = [7; 129];
        selected(&mut values, 1, 128, 126, 19);
        assert_eq!(values[127], 19);
        assert_eq!(values[0], 7);
        assert_eq!(values[128], 7);
    }
}

#[cfg(external_control)]
extern crate stage196_dependency;
#[cfg(external_control)]
pub fn external_child(values: &mut [u16], start: usize, end: usize, index: usize, word: u16) {
    if start <= end && end <= values.len() && index < end - start {
        stage196_dependency::selected(&mut values[start..end], index, word);
        assert!(values[start + index] == word);
    }
}
