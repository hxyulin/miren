#![no_std]
#![forbid(unsafe_code)]
#![cfg_attr(not(test), feature(custom_mir, core_intrinsics))]
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
#[inline(never)]
pub fn branch_child(values: &mut [u16], index: usize, choice: bool) {
    if index < values.len() {
        values[index] = if choice { 17 } else { 29 };
    }
}
pub fn selected(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        child(values, index, word);
        assert!(values[index] == word);
    }
}
pub fn wrong(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        child(values, index, word);
        assert!(values[index] != word);
    }
}
pub fn explicit(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        let borrowed = &mut *values;
        child(borrowed, index, word);
        assert!(values[index] == word);
    }
}
pub fn scalar_return(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        let returned = scalar_child(values, index, word);
        assert!(returned == word && values[index] == word);
    }
}
pub fn sequential(values: &mut [u16], index: usize, other: usize) {
    if index < values.len() && other < values.len() && index != other {
        child(values, index, 17);
        child(values, other, 29);
        assert!(values[index] == 17 && values[other] == 29);
    }
}
pub fn branches(values: &mut [u16], index: usize, choice: bool) {
    if index < values.len() {
        branch_child(values, index, choice);
        assert!(values[index] == if choice { 17 } else { 29 });
    }
}
pub fn untouched(values: &mut [u16], index: usize, other: usize, word: u16) {
    if index < values.len() && other < values.len() && index != other {
        let old = values[other];
        child(values, index, word);
        assert!(values[other] == old);
    }
}
pub fn child_empty(values: &mut [u16]) {
    if values.len() == 0 {
        child(values, 0, 17);
        assert!(values.len() == 0);
    }
}
#[inline(never)]
pub fn nested_child(values: &mut [u16], index: usize, word: u16) {
    child(values, index, word);
}
pub fn nested(values: &mut [u16], index: usize, word: u16) {
    nested_child(values, index, word);
}
#[inline(never)]
pub fn retained_child(values: &mut [u16]) {
    let shared = &*values;
    assert!(shared.len() == 0);
}
pub fn retained_metadata(values: &mut [u16]) {
    retained_child(values);
}
#[inline(never)]
pub fn shared_child(values: &[u16]) -> usize {
    values.len()
}
pub fn shared_view(values: &mut [u16]) {
    let _ = shared_child(&*values);
}
#[inline(never)]
pub fn two_child(left: &mut [u16], right: &mut [u16]) {
    if left.len() > 0 {
        left[0] = 17;
    }
    if right.len() > 0 {
        right[0] = 29;
    }
}
pub fn two_arguments(left: &mut [u16], right: &mut [u16]) {
    two_child(left, right);
}
#[inline(never)]
pub fn reference_child(values: &mut [u16]) -> &mut [u16] {
    values
}
pub fn reference_escape(values: &mut [u16]) -> &mut [u16] {
    reference_child(values)
}
pub fn unreachable_panic(values: &mut [u16]) {
    child(values, 0, 17);
    panic!();
}
#[cfg(external_control)]
pub fn external_child(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        stage189_dependency::selected(values, index, word);
        assert!(values[index] == word);
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn finite_129_current_data() {
        let mut values = [0_u16; 129];
        selected(&mut values, 128, 41);
        explicit(&mut values, 128, 41);
        scalar_return(&mut values, 128, 41);
        sequential(&mut values, 128, 0);
        branches(&mut values, 128, true);
        branches(&mut values, 128, false);
        untouched(&mut values, 128, 0, 41);
        child_empty(&mut []);
    }
    #[test]
    fn mutation_guard() {
        selected(&mut [0; 129], 128, 41);
        scalar_nested(&mut [0; 129], 128, 41);
    }
}

// Invalid borrow/alias protocols are analyzer-only controls, never native executions.
#[cfg(not(test))]
pub mod analyzer_only {
    use core::intrinsics::mir::*;
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn duplicate_arguments(values: &mut [u16]) {
        mir! {
            {
                Call(RET = super::two_child(values, values), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn moved_parent(values: &mut [u16]) {
        mir! {
            {
                Call(RET = super::child(Move(values), 0, 17), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn pending_return(values: &mut [u16]) {
        mir! {
            let borrowed: &mut [u16];
            { borrowed = &mut *values; Return() }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn duplicate_alias(values: &mut [u16]) {
        mir! {
            let borrowed: &mut [u16];
            let duplicate: &mut [u16];
            {
                borrowed = &mut *values;
                duplicate = borrowed;
                Call(RET = super::two_child(Move(borrowed),Move(duplicate)), ReturnTo(done),
                    UnwindUnreachable())
            }
            done = { Return() }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn parent_during_lease(values: &mut [u16], index: usize) -> u16 {
        mir! {
            let borrowed: &mut [u16];
            {
                borrowed = &mut *values;
                RET = (*values)[index];
                Return()
            }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn stale_child(values: &mut [u16], index: usize, word: u16) -> u16 {
        mir! {
            let borrowed: &mut [u16];
            let unit: ();
            {
                borrowed = &mut *values;
                Call(unit = super::child(borrowed,index,word), ReturnTo(done),
                    UnwindUnreachable())
            }
            done = { RET = (*borrowed)[index]; Return() }
        }
    }
}

#[inline(never)]
pub fn scalar_operation(word: u16) -> u16 {
    word ^ 0
}
#[inline(never)]
pub fn scalar_operation_child(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        values[index] = scalar_operation(word);
    }
}
pub fn scalar_nested(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        scalar_operation_child(values, index, word);
        assert!(values[index] == word);
    }
}
