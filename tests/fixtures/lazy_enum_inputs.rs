#![no_std]
#![forbid(unsafe_code)]

#[derive(Clone, Copy)]
#[repr(i16)]
pub enum Driver {
    Idle = -7,
    Small(u16, u32) = 9,
    Wide([u16; 32]) = 300,
}

pub struct Bench {
    pub motors: [Option<Driver>; 8],
    pub watching: bool,
}

pub fn watching(bench: &Bench) -> bool {
    bench.watching
}
pub fn observing_unvisited_enum_payloads_keeps_the_actual_field(bench: &Bench) {
    assert!(watching(bench) == bench.watching);
}

pub fn same_occurrence_keeps_exact_variant_and_payload(bench: &Bench) {
    match (&bench.motors[0], &bench.motors[0]) {
        (Some(Driver::Small(a, b)), Some(Driver::Small(c, d))) => {
            assert!(*a == *c);
            assert!(*b == *d);
        }
        (Some(Driver::Wide(a)), Some(Driver::Wide(b))) => {
            assert!(a[31] == b[31]);
        }
        _ => {}
    }
}

pub fn separate_occurrences_can_differ(bench: &Bench) {
    if let (Some(Driver::Small(a, _)), Some(Driver::Small(b, _))) =
        (&bench.motors[0], &bench.motors[1])
    {
        assert!(*a == *b);
    }
}

pub fn sparse_signed_tags_keep_only_actual_variants(values: &[Driver; 16]) {
    assert!(matches!(
        values[15],
        Driver::Idle | Driver::Small(_, _) | Driver::Wide(_)
    ));
}

pub fn late_payload_claim_is_refuted(bench: &Bench) {
    if let Some(Driver::Wide(values)) = &bench.motors[7] {
        assert!(values[31] == 0);
    }
}

pub fn owned_enum_copy_preserves_untouched_payloads(bench: Bench) {
    let first = bench.motors[0];
    let mut copied = bench;
    copied.motors[7] = Some(Driver::Idle);
    if let (Some(Driver::Small(a, b)), Some(Driver::Small(c, d))) = (first, copied.motors[0]) {
        assert!(a == c);
        assert!(b == d);
    }
}

pub fn restricted_payloads_remain_unknown(values: &[Option<core::num::NonZeroU16>; 256]) -> bool {
    values.is_empty()
}

pub enum Pointer {
    Nil,
    Data(*const u32),
}
pub fn pointer_payloads_remain_unknown(values: &[Pointer; 256]) -> bool {
    values.is_empty()
}

pub enum Interior {
    Nil,
    Data(core::cell::Cell<u16>),
}
pub fn interior_payloads_remain_unknown(values: &[Interior; 256]) -> bool {
    values.is_empty()
}

pub fn symbol_slot_exhaustion_remains_unknown(values: &[Option<[[u16; 256]; 256]>; 8]) -> bool {
    values.is_empty()
}

#[cfg(test)]
#[test]
fn native_lazy_enum_controls() {
    let bench = Bench {
        motors: [Some(Driver::Small(17, 99)); 8],
        watching: true,
    };
    observing_unvisited_enum_payloads_keeps_the_actual_field(&bench);
    same_occurrence_keeps_exact_variant_and_payload(&bench);
    sparse_signed_tags_keep_only_actual_variants(&[Driver::Wide([3; 32]); 16]);
    owned_enum_copy_preserves_untouched_payloads(bench);
    for value in [
        Large::First([3; 256]),
        Large::Middle([5; 256]),
        Large::Last([9; 256]),
    ] {
        direct_large_enum_payloads_keep_identity(value);
    }
}

#[derive(Clone, Copy)]
#[repr(i16)]
pub enum Large {
    First([u16; 256]) = -17,
    Middle([u16; 256]) = 0,
    Last([u16; 256]) = 400,
}

pub fn direct_large_enum_payloads_keep_identity(value: Large) {
    match value {
        Large::First(values) | Large::Middle(values) | Large::Last(values) => {
            assert!(values[255] == values[255]);
        }
    }
}

pub fn direct_sparse_negative_tag_is_reachable(value: Large) {
    if let Large::First(_) = value {
        assert!(false);
    }
}
pub fn direct_sparse_zero_tag_is_reachable(value: Large) {
    if let Large::Middle(_) = value {
        assert!(false);
    }
}
pub fn direct_sparse_positive_tag_is_reachable(value: Large) {
    if let Large::Last(_) = value {
        assert!(false);
    }
}

pub enum Borrowed<'a> {
    Nil,
    Data(Option<&'a u16>),
}
pub fn reference_payloads_remain_unknown(values: &[Borrowed<'_>; 256]) -> bool {
    values.is_empty()
}

pub fn negative_driver_tag_is_reachable(values: &[Driver; 16]) {
    if let Driver::Idle = values[15] {
        assert!(false);
    }
}
pub fn positive_small_driver_tag_is_reachable(values: &[Driver; 16]) {
    if let Driver::Small(_, _) = values[15] {
        assert!(false);
    }
}
pub fn positive_wide_driver_tag_is_reachable(values: &[Driver; 16]) {
    if let Driver::Wide(_) = values[15] {
        assert!(false);
    }
}
pub union Bits {
    pub first: u32,
    pub second: u16,
}
pub enum UnionPayload {
    Nil,
    Data(Bits),
}
pub fn union_payloads_remain_unknown(values: &[UnionPayload; 256]) -> bool {
    values.is_empty()
}

pub enum TooManyPayloadVariants {
    V0(u16),
    V1(u16),
    V2(u16),
    V3(u16),
    V4(u16),
    V5(u16),
    V6(u16),
    V7(u16),
    V8(u16),
    V9(u16),
    V10(u16),
    V11(u16),
    V12(u16),
    V13(u16),
    V14(u16),
    V15(u16),
    V16(u16),
    V17(u16),
    V18(u16),
    V19(u16),
    V20(u16),
    V21(u16),
    V22(u16),
    V23(u16),
    V24(u16),
    V25(u16),
    V26(u16),
    V27(u16),
    V28(u16),
    V29(u16),
    V30(u16),
    V31(u16),
    V32(u16),
    V33(u16),
    V34(u16),
    V35(u16),
    V36(u16),
    V37(u16),
    V38(u16),
    V39(u16),
    V40(u16),
    V41(u16),
    V42(u16),
    V43(u16),
    V44(u16),
    V45(u16),
    V46(u16),
    V47(u16),
    V48(u16),
    V49(u16),
    V50(u16),
    V51(u16),
    V52(u16),
    V53(u16),
    V54(u16),
    V55(u16),
    V56(u16),
    V57(u16),
    V58(u16),
    V59(u16),
    V60(u16),
    V61(u16),
    V62(u16),
    V63(u16),
    V64(u16),
}
pub fn payload_variant_cap_stays_unknown(values: &[TooManyPayloadVariants; 8]) -> bool {
    values.is_empty()
}

pub enum TooManyFieldlessVariants {
    V0,
    V1,
    V2,
    V3,
    V4,
    V5,
    V6,
    V7,
    V8,
    V9,
    V10,
    V11,
    V12,
    V13,
    V14,
    V15,
    V16,
    V17,
    V18,
    V19,
    V20,
    V21,
    V22,
    V23,
    V24,
    V25,
    V26,
    V27,
    V28,
    V29,
    V30,
    V31,
    V32,
    V33,
    V34,
    V35,
    V36,
    V37,
    V38,
    V39,
    V40,
    V41,
    V42,
    V43,
    V44,
    V45,
    V46,
    V47,
    V48,
    V49,
    V50,
    V51,
    V52,
    V53,
    V54,
    V55,
    V56,
    V57,
    V58,
    V59,
    V60,
    V61,
    V62,
    V63,
    V64,
    V65,
    V66,
    V67,
    V68,
    V69,
    V70,
    V71,
    V72,
    V73,
    V74,
    V75,
    V76,
    V77,
    V78,
    V79,
    V80,
    V81,
    V82,
    V83,
    V84,
    V85,
    V86,
    V87,
    V88,
    V89,
    V90,
    V91,
    V92,
    V93,
    V94,
    V95,
    V96,
    V97,
    V98,
    V99,
    V100,
    V101,
    V102,
    V103,
    V104,
    V105,
    V106,
    V107,
    V108,
    V109,
    V110,
    V111,
    V112,
    V113,
    V114,
    V115,
    V116,
    V117,
    V118,
    V119,
    V120,
    V121,
    V122,
    V123,
    V124,
    V125,
    V126,
    V127,
    V128,
    V129,
    V130,
    V131,
    V132,
    V133,
    V134,
    V135,
    V136,
    V137,
    V138,
    V139,
    V140,
    V141,
    V142,
    V143,
    V144,
    V145,
    V146,
    V147,
    V148,
    V149,
    V150,
    V151,
    V152,
    V153,
    V154,
    V155,
    V156,
    V157,
    V158,
    V159,
    V160,
    V161,
    V162,
    V163,
    V164,
    V165,
    V166,
    V167,
    V168,
    V169,
    V170,
    V171,
    V172,
    V173,
    V174,
    V175,
    V176,
    V177,
    V178,
    V179,
    V180,
    V181,
    V182,
    V183,
    V184,
    V185,
    V186,
    V187,
    V188,
    V189,
    V190,
    V191,
    V192,
    V193,
    V194,
    V195,
    V196,
    V197,
    V198,
    V199,
    V200,
    V201,
    V202,
    V203,
    V204,
    V205,
    V206,
    V207,
    V208,
    V209,
    V210,
    V211,
    V212,
    V213,
    V214,
    V215,
    V216,
    V217,
    V218,
    V219,
    V220,
    V221,
    V222,
    V223,
    V224,
    V225,
    V226,
    V227,
    V228,
    V229,
    V230,
    V231,
    V232,
    V233,
    V234,
    V235,
    V236,
    V237,
    V238,
    V239,
    V240,
    V241,
    V242,
    V243,
    V244,
    V245,
    V246,
    V247,
    V248,
    V249,
    V250,
    V251,
    V252,
    V253,
    V254,
    V255,
    V256,
}
pub fn fieldless_variant_cap_stays_unknown(value: TooManyFieldlessVariants) {
    let _ = value;
}
