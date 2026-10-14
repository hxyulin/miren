#![forbid(unsafe_code)]
#![cfg_attr(crux, feature(register_tool))]
#![cfg_attr(crux, register_tool(crux))]

#[cfg(crux)]
extern crate crucible;

use miren_dr16::Raw;

pub fn parser_fixed(bytes: [u8; 18]) {
    let parsed = Raw::parse(&bytes).unwrap();
    assert!(parsed.right_switch <= 3 && parsed.left_switch <= 3);
    for channel in parsed.channels {
        assert!((-1024..=1023).contains(&channel));
    }
}

pub fn parser_lengths(bytes: [u8; 20], length: u8) {
    if length <= 20 {
        let parsed = Raw::parse(&bytes[..usize::from(length)]);
        assert_eq!(parsed.is_some(), length == 18);
    }
}

#[cfg(kani)]
#[kani::proof]
pub fn check_fixed() {
    parser_fixed(kani::any());
}

#[cfg(kani)]
#[kani::proof]
pub fn check_lengths() {
    parser_lengths(kani::any(), kani::any());
}

#[cfg(crux)]
#[crux::test]
pub fn check_fixed() {
    use crucible::Symbolic;
    parser_fixed(<[u8; 18]>::symbolic("bytes"));
}

#[cfg(crux)]
#[crux::test]
pub fn check_lengths() {
    use crucible::Symbolic;
    parser_lengths(<[u8; 20]>::symbolic("bytes"), u8::symbolic("length"));
}

#[cfg(test)]
mod native {
    use super::*;

    #[test]
    fn boundaries() {
        for byte in [0, 1, 127, 255] {
            parser_fixed([byte; 18]);
            for length in 0..=255 {
                parser_lengths([byte; 20], length);
            }
        }
    }
}
