#![no_std]
#![forbid(unsafe_code)]

use core::marker::PhantomData;

#[derive(Clone, Copy)]
pub struct Token<const TAG: usize> {
    unit: (),
    marker: PhantomData<&'static mut [u8; TAG]>,
}

impl<const TAG: usize> Token<TAG> {
    pub fn new() -> Self {
        Self {
            unit: (),
            marker: PhantomData,
        }
    }
}

macro_rules! wide {
    ($($field:ident: $tag:literal,)*) => {
        pub struct Wide { $(pub $field: Token<$tag>,)* }
        pub fn make_wide() -> Wide {
            Wide { $($field: Token::<$tag>::new(),)* }
        }
    };
}

wide! {
    p000: 0,
    p001: 1,
    p002: 2,
    p003: 3,
    p004: 4,
    p005: 5,
    p006: 6,
    p007: 7,
    p008: 8,
    p009: 9,
    p010: 10,
    p011: 11,
    p012: 12,
    p013: 13,
    p014: 14,
    p015: 15,
    p016: 16,
    p017: 17,
    p018: 18,
    p019: 19,
    p020: 20,
    p021: 21,
    p022: 22,
    p023: 23,
    p024: 24,
    p025: 25,
    p026: 26,
    p027: 27,
    p028: 28,
    p029: 29,
    p030: 30,
    p031: 31,
    p032: 32,
    p033: 33,
    p034: 34,
    p035: 35,
    p036: 36,
    p037: 37,
    p038: 38,
    p039: 39,
    p040: 40,
    p041: 41,
    p042: 42,
    p043: 43,
    p044: 44,
    p045: 45,
    p046: 46,
    p047: 47,
    p048: 48,
    p049: 49,
    p050: 50,
    p051: 51,
    p052: 52,
    p053: 53,
    p054: 54,
    p055: 55,
    p056: 56,
    p057: 57,
    p058: 58,
    p059: 59,
    p060: 60,
    p061: 61,
    p062: 62,
    p063: 63,
    p064: 64,
    p065: 65,
    p066: 66,
    p067: 67,
    p068: 68,
    p069: 69,
    p070: 70,
    p071: 71,
    p072: 72,
    p073: 73,
    p074: 74,
    p075: 75,
    p076: 76,
    p077: 77,
    p078: 78,
    p079: 79,
    p080: 80,
    p081: 81,
    p082: 82,
    p083: 83,
    p084: 84,
    p085: 85,
    p086: 86,
    p087: 87,
    p088: 88,
    p089: 89,
    p090: 90,
    p091: 91,
    p092: 92,
    p093: 93,
    p094: 94,
    p095: 95,
    p096: 96,
    p097: 97,
    p098: 98,
    p099: 99,
    p100: 100,
    p101: 101,
    p102: 102,
    p103: 103,
    p104: 104,
    p105: 105,
    p106: 106,
    p107: 107,
    p108: 108,
    p109: 109,
    p110: 110,
    p111: 111,
    p112: 112,
    p113: 113,
    p114: 114,
    p115: 115,
    p116: 116,
    p117: 117,
    p118: 118,
    p119: 119,
    p120: 120,
    p121: 121,
    p122: 122,
    p123: 123,
    p124: 124,
    p125: 125,
    p126: 126,
    p127: 127,
    p128: 128,
    p129: 129,
    p130: 130,
    p131: 131,
    p132: 132,
    p133: 133,
    p134: 134,
    p135: 135,
    p136: 136,
    p137: 137,
    p138: 138,
    p139: 139,
    p140: 140,
    p141: 141,
    p142: 142,
    p143: 143,
    p144: 144,
    p145: 145,
    p146: 146,
    p147: 147,
    p148: 148,
    p149: 149,
    p150: 150,
    p151: 151,
    p152: 152,
    p153: 153,
    p154: 154,
    p155: 155,
    p156: 156,
    p157: 157,
    p158: 158,
    p159: 159,
    p160: 160,
    p161: 161,
    p162: 162,
    p163: 163,
    p164: 164,
    p165: 165,
    p166: 166,
    p167: 167,
    p168: 168,
    p169: 169,
    p170: 170,
    p171: 171,
    p172: 172,
    p173: 173,
    p174: 174,
    p175: 175,
    p176: 176,
    p177: 177,
    p178: 178,
    p179: 179,
    // EXTRA_ZERO_FIELDS
}

pub fn projected(value: Wide, index: usize) {
    let pieces = [0u8; 2];
    if index < 2 {
        assert!(pieces[index] == 0);
        touch(value.p000);
    }
    touch(value.p179);
}

pub fn trusted_use(index: usize) {
    projected(make_wide(), index);
}

pub fn touch<const TAG: usize>(value: Token<TAG>) {
    let Token { unit, marker } = value;
    let _ = (unit, marker);
}

pub fn nested_arrays(value: [[Token<0>; 256]; 256]) {
    touch(value[255][255]);
}

pub fn wrong_guard(value: Wide, index: usize) {
    let pieces = [0u8; 2];
    if index <= 2 {
        assert!(pieces[index] == 0);
        touch(value.p000);
    }
}

pub enum Empty {}
pub struct Uninhabited {
    inner: Empty,
}
pub fn unknown_uninhabited(value: Uninhabited) {
    let _ = value;
}

pub union Union {
    unit: (),
}
pub fn unknown_union(value: Union) {
    let _ = value;
}

pub struct HoldsRef {
    reference: &'static u8,
}
pub fn unknown_reference(value: &mut HoldsRef) {
    let _ = value;
}

pub fn unknown_array_budget(value: [Token<0>; 257]) {
    let _ = value;
}

type Deep0 = ();
type Deep1 = ((), Deep0);
type Deep2 = ((), Deep1);
type Deep3 = ((), Deep2);
type Deep4 = ((), Deep3);
type Deep5 = ((), Deep4);
type Deep6 = ((), Deep5);
type Deep7 = ((), Deep6);
type Deep8 = ((), Deep7);
type Deep9 = ((), Deep8);
type Deep10 = ((), Deep9);
type Deep11 = ((), Deep10);
type Deep12 = ((), Deep11);
type Deep13 = ((), Deep12);
type Deep14 = ((), Deep13);
type Deep15 = ((), Deep14);
type Deep16 = ((), Deep15);
type Deep17 = ((), Deep16);
pub fn unknown_depth(value: Deep17) {
    let _ = value;
}

#[cfg(test)]
extern crate std;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn native_zero_sized_projection_and_bounds() {
        projected(make_wide(), 0);
        projected(make_wide(), 1);
        projected(make_wide(), 2);
        nested_arrays([[Token::new(); 256]; 256]);
    }
}
