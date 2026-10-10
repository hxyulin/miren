#![no_std]
#![forbid(unsafe_code)]
#![cfg_attr(not(test), feature(custom_mir, core_intrinsics))]

#[inline(never)]
pub fn replacement(word: u16) -> u16 { word }

pub fn selected(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        values[index] = replacement(word);
        assert!(values[index] == word);
    }
}
pub fn wrong(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        values[index] = replacement(word);
        assert!(values[index] != word);
    }
}
pub fn untouched(values: &mut [u16], index: usize, other: usize, word: u16) {
    if index < values.len() && other < values.len() && index != other {
        let old = values[other];
        values[index] = word;
        assert!(values[other] == old);
    }
}
pub fn sequential(values: &mut [u16], index: usize) {
    if index < values.len() {
        values[index] = 17;
        values[index] = 29;
        assert!(values[index] == 29);
    }
}
pub fn branches(values: &mut [u16], index: usize, flag: bool) {
    if index < values.len() {
        if flag { values[index] = 17; } else { values[index] = 29; }
        assert!(values[index] == if flag { 17 } else { 29 });
    }
}
pub fn ghost_length(values: &mut [u16]) {
    if values.len() > 0 { values[0] = 19; }
}
pub fn empty(values: &mut [u16]) {
    if values.len() == 0 { assert!(values.len() == 0); }
}
pub fn bounds(values: &mut [u16], index: usize) { values[index] = 19; }
#[inline(never)]
pub fn child(values: &mut [u16], index: usize) { values[index] = 19; }
pub fn child_unknown(values: &mut [u16], index: usize) {
    if index < values.len() { child(values, index); }
}
pub fn retained_shared(values: &mut [u16], index: usize) {
    let shared = &*values;
    if index < shared.len() { assert!(shared[index] == values[index]); }
}
pub fn raw_unknown(values: &mut [u16]) { let _ = values.as_mut_ptr(); }
pub fn duplicate_root(left: &mut [u16], right: &mut [u16]) {
    assert!(left.len() == right.len());
}
pub fn return_unknown(values: &mut [u16]) -> &mut [u16] { values }
pub fn closure_unknown(values: &mut [u16], index: usize) {
    let mut write = || { if index < values.len() { values[index] = 19; } };
    write();
}
#[inline(never)]
pub fn shared_len(values: &[u16]) -> usize { values.len() }
pub fn metadata_helper_unknown(values: &mut [u16]) -> usize { shared_len(&*values) }
#[inline(never)]
pub fn two_lengths(left: &[u16], right: &[u16]) -> bool { left.len() == right.len() }
pub fn duplicate_metadata(values: &mut [u16]) -> bool {
    let metadata = &*values;
    two_lengths(metadata, metadata)
}
#[cfg(missing_dependency)]
pub fn external_scalar(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        values[index] = stage184_dependency::replacement(word);
        assert!(values[index] == word);
    }
}

// Custom MIR controls test unsupported role transport; they never execute natively.
#[cfg(not(test))]
pub mod analyzer_only {
    use core::intrinsics::mir::*;
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn copied_root(values: &mut [u16]) {
        mir! { let alias: &mut [u16]; { alias = values; RET = (); Return() } }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn moved_root(values: &mut [u16]) {
        mir! { let alias: &mut [u16]; { alias = Move(values); RET = (); Return() } }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_root(values: &mut [u16]) -> usize {
        mir! {
            let metadata: &[u16];
            {
                StorageDead(values);
                metadata = &*values;
                Call(RET = <[u16]>::len(Move(metadata)), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn aggregate_metadata(values: &mut [u16]) {
        mir! {
            let metadata: &[u16]; let aggregate: (&[u16],);
            { metadata = &*values; aggregate = (metadata,); RET = (); Return() }
        }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn raw_root(values: &mut [u16]) {
        mir! { let raw: *mut [u16]; { raw = &raw mut *values; RET = (); Return() } }
    }
    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn raw_metadata(values: &mut [u16]) {
        mir! {
            let metadata: &[u16]; let raw: *const &[u16];
            { metadata = &*values; raw = &raw const metadata; RET = (); Return() }
        }
    }
}

pub fn induction_unknown(values: &mut [u16], limit: usize) {
    let mut index = 0;
    while index < limit && index < values.len() { values[index] = 19; index += 1; }
}

#[cfg(test)]
mod native {
    use super::*;
    #[test]
    fn full_extent() {
        let mut words = [0_u16; 129];
        selected(&mut words, 128, 41);
        assert_eq!(words[128], 41);
        untouched(&mut words, 128, 127, 39);
        sequential(&mut words, 128);
        branches(&mut words, 128, true);
        branches(&mut words, 128, false);
        empty(&mut []);
    }
    #[test]
    fn mutation_guard() { selected(&mut [0_u16; 129], 128, 41); }
}
