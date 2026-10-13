#![no_std]
#![forbid(unsafe_code)]
#![feature(fn_traits)]

fn leaf(word: u16) -> u16 { word }
#[inline(never)]
pub fn shim_middle(word: u16) -> u16 {
    let function: fn(u16) -> u16 = leaf;
    core::ops::Fn::call(&function, (word,))
}
pub fn shim_unknown(values: &mut [u16], word: u16) {
    if !values.is_empty() {
        let child = &mut values[0..1];
        assert!(child.len() == 1);
        child[0] = shim_middle(word);
    }
}
