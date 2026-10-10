#![no_std]
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
use external_struct_values_dependency::*;

pub fn named(values: &[Pair], index: usize) {
    if index < values.len() {
        let copy = values[index];
        assert!(copy.left == values[index].left && copy.right == values[index].right);
    }
}
pub fn tuple(values: &[Tuple], index: usize) {
    if index < values.len() {
        let copy = values[index];
        assert!(copy.0 == values[index].0 && copy.1 == values[index].1);
    }
}
pub fn generic(values: &[Generic<([u8; 2], char)>], index: usize) {
    if index < values.len() {
        let copy = values[index];
        assert!(copy.payload.0[1] == values[index].payload.0[1]);
        assert!(copy.payload.1 == values[index].payload.1 && copy.flag == values[index].flag);
    }
}
pub fn rich(values: &[Rich], index: usize) {
    if index < values.len() {
        let copy = values[index];
        assert!(copy.pair.left == values[index].pair.left);
        assert!(copy.bytes[0] == values[index].bytes[0]);
        assert!(copy.floating.to_bits() == values[index].floating.to_bits());
        assert!(copy.wide.to_bits() == values[index].wide.to_bits());
        assert!(copy.character == values[index].character);
        let code = copy.character as u32;
        assert!(code <= 0x10ffff && (code < 0xd800 || code > 0xdfff));
    }
}
pub fn selected_method(values: &[Pair], index: usize) {
    if index < values.len() {
        assert!(values[index].selected() == values[index].left);
    }
}
pub fn borrowed_method(values: &[Pair], index: usize) {
    if index < values.len() {
        assert!(*values[index].borrowed() == values[index].right);
    }
}
pub fn views(values: &[Pair], offset: usize, index: usize) {
    if offset <= values.len() {
        let suffix = &values[offset..];
        assert!(suffix.iter().len() == values.len() - offset);
        if index < suffix.len() {
            assert!(suffix.iter().nth(index).unwrap().left == values[offset + index].left);
        }
    }
}
pub fn layout(values: &[Pair]) {
    assert!(core::mem::size_of_val(values) == values.len() * core::mem::size_of::<Pair>());
    assert!(core::mem::align_of_val(values) == core::mem::align_of::<Pair>());
}
pub fn owned(values: [Rich; 2], index: usize) {
    if index < 2 {
        let mut copy = values[index];
        let original = copy;
        copy.bytes[0] = copy.bytes[0].wrapping_add(1);
        assert!(original.bytes[0] == values[index].bytes[0]);
        assert!(copy.bytes[0] == original.bytes[0].wrapping_add(1));
        assert!(copy.character == original.character);
    }
}
pub fn zero(values: &[Zero<7>], index: usize) {
    assert!(core::mem::size_of_val(values) == 0);
    assert!(core::mem::align_of_val(values) == 64);
    if index < values.len() {
        let copy = values[index];
        assert!(copy.marker() == 7);
    }
    if values.len() == usize::MAX {
        assert!(values.iter().nth(usize::MAX - 1).is_some());
    }
}
pub fn independent_fields(values: &[Pair]) {
    if !values.is_empty() {
        assert!(values[0].left == values[0].right);
    }
}
pub fn constructor_invariant(values: &[Private]) {
    if !values.is_empty() {
        assert!(values[0].get() != 0);
    }
}
pub fn overflow(values: &[Pair]) {
    if !values.is_empty() {
        let _ = values[0].checked_next();
    }
}
pub fn bounds(values: &[Pair], index: usize) -> u16 {
    values[index].left
}
pub fn wrong_const(values: &[Zero<9>]) {
    if !values.is_empty() {
        assert!(values[0].marker() == 7);
    }
}
pub fn reference_field(values: &[RefField<'_>]) -> usize { values.len() }
pub fn raw_field(values: &[RawField]) -> usize { values.len() }
pub fn refined_field(values: &[PatField]) -> usize { values.len() }
pub fn core_field(values: &[CoreField]) -> usize { values.len() }
pub fn nonzero_field(values: &[NonZeroField]) -> usize { values.len() }
pub fn packed(values: &[Packed]) -> usize { values.len() }
pub fn dropped(values: &[Dropped]) -> usize { values.len() }
pub fn oversized(values: &[Huge]) -> usize { values.len() }
pub fn mutable(values: &mut [Pair]) -> usize { values.len() }
pub fn competing(a: &[Pair], b: &[Pair]) -> bool { a.len() == b.len() }

#[cfg(test)]
mod native {
    use super::*;
    fn pairs() -> [Pair; 129] {
        [Pair { left: 3, right: 7, padding: 1 }; 129]
    }
    #[test]
    fn positives() {
        let values = pairs();
        for index in [0, 128, 129, usize::MAX] {
            named(&values, index);
            selected_method(&values, index);
            borrowed_method(&values, index);
            views(&values, 1, index);
            tuple(&[Tuple(3, true); 129], index);
            generic(&[Generic { payload: ([3, 7], '\u{10ffff}'), flag: true }; 129], index);
        }
        layout(&values);
        named(&[], 0);
        let value = Rich { pair: values[0], bytes: [3, 7], floating: -0.0,
            wide: f64::from_bits(0x7ff8000000000123), character: '\u{d7ff}' };
        rich(&[value; 129], 128);
        owned([value; 2], 1);
        zero(&[Zero::<7>; 129], 128);
        zero(&[Zero::<7>; usize::MAX], usize::MAX - 1);
    }
    #[test]
    fn mutation_guard() { selected_method(&pairs(), 128); }
    #[test]
    #[should_panic]
    fn negative_fields() { independent_fields(&pairs()); }
    #[test]
    #[should_panic]
    fn negative_bounds() { bounds(&pairs(), 129); }
    #[test]
    #[should_panic]
    fn negative_const() { wrong_const(&[Zero::<9>; 2]); }
}


pub fn whole_contains(values: &[Pair], needle: Pair) -> bool {
    values.contains(&needle)
}

#[cfg(not(test))]
mod analyzer_only {
    use core::intrinsics::mir::*;

    fn metadata(source: &[super::Pair; 0]) -> usize {
        source.len()
    }

    #[custom_mir(dialect = "runtime", phase = "optimized")]
    pub fn dead_empty() -> usize {
        mir! {
            let backing: [super::Pair; 0];
            let source: &[super::Pair; 0];
            { backing = []; source = &backing; Goto(retire) }
            retire = {
                StorageDead(backing);
                Call(RET = metadata(source), ReturnTo(done), UnwindUnreachable())
            }
            done = { Return() }
        }
    }
}
