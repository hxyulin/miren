#![forbid(unsafe_code)]
use miren::{ProofStatus, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::Command;
#[path = "support/table_verification.rs"]
mod table_verification;
use table_verification::{Directory, native, verify};

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/float_function_pointer_repeat.rs")
}

#[test]
fn float_repeat_preserves_actual_raw_bits_and_conservative_boundaries() {
    let entries = [
        ("selected32", ProofStatus::Proved),
        ("selected64", ProofStatus::Proved),
        ("sign32", ProofStatus::Proved),
        ("sign64", ProofStatus::Proved),
        ("wrong32", ProofStatus::Refuted),
        ("wrong64", ProofStatus::Refuted),
        ("opaque32", ProofStatus::Unknown),
        ("opaque64", ProofStatus::Unknown),
        ("generic32", ProofStatus::Unknown),
        ("foreign32", ProofStatus::Unknown),
        ("mixed_width", ProofStatus::Unknown),
        ("last32", ProofStatus::Proved),
        ("last64", ProofStatus::Proved),
        ("count_budget", ProofStatus::Unknown),
        ("dispatch_budget", ProofStatus::Unknown),
        ("zero", ProofStatus::Proved),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&fixture(), &entries, target, optimized, &[]);
            for (name, helper) in [
                ("selected32", "identity32"),
                ("selected64", "identity64"),
                ("sign32", "negate32"),
                ("sign64", "negate64"),
            ] {
                let proof = report
                    .functions
                    .iter()
                    .find(|function| function.name == name)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert!(
                    proof
                        .body_entries
                        .iter()
                        .any(|entry| entry.function == helper)
                );
            }
        }
    }
}

#[test]
fn actual_float_repeat_mutations_refute_the_same_unchanged_bit_claim() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
    }
    for (helper, selected, old, new) in [
        (
            "identity32",
            "selected32",
            "pub fn identity32(value: f32) -> f32 {\n    value\n}",
            "pub fn identity32(value: f32) -> f32 {\n    -value\n}",
        ),
        (
            "identity64",
            "selected64",
            "pub fn identity64(value: f64) -> f64 {\n    value\n}",
            "pub fn identity64(value: f64) -> f64 {\n    -value\n}",
        ),
    ] {
        assert_eq!(source.matches(old).count(), 1);
        let path = directory.0.join(format!("{helper}.rs"));
        std::fs::write(&path, source.replacen(old, new, 1)).unwrap();
        for optimized in [false, true] {
            native(&path, optimized, true);
            for target in [None, Some("thumbv7em-none-eabihf")] {
                let report = verify(
                    &path,
                    &[(selected, ProofStatus::Refuted)],
                    target,
                    optimized,
                    &[],
                );
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == selected)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert!(
                    proof
                        .body_entries
                        .iter()
                        .any(|entry| entry.function == helper)
                );
                assert!(proof.obligations.iter().any(|obligation| {
                    obligation.status == ProofStatus::Refuted
                        && obligation.query.is_some()
                        && obligation.model.is_some()
                }));
            }
        }
    }
}

#[test]
fn genuine_float_repeat_targets_require_bodies_even_for_constant_callers() {
    let directory = Directory::new();
    let dependency = directory.0.join("dependency.rs");
    let caller = directory.0.join("caller.rs");
    std::fs::write(
        &dependency,
        r#"#![no_std]
#![forbid(unsafe_code)]
#[inline(never)] pub fn sign32(value: f32) -> f32 { -value }
#[inline(never)] pub fn sign64(value: f64) -> f64 { -value }
#[inline(never)] pub fn constant32(_: f32) -> f32 { 1.0 }
#[inline(never)] pub fn constant64(_: f64) -> f64 { 1.0 }
"#,
    )
    .unwrap();
    std::fs::write(
        &caller,
        r#"#![no_std]
#![forbid(unsafe_code)]
pub fn selected32(index: usize, value: f32) {
    let table: [fn(f32)->f32;2] = [repeat_external::sign32;2];
    if index < 2 { assert!(table[index](value).to_bits() == (value.to_bits() ^ 0x8000_0000)); }
}
pub fn selected64(index: usize, value: f64) {
    let table: [fn(f64)->f64;2] = [repeat_external::sign64;2];
    if index < 2 {
        assert!(table[index](value).to_bits() == (value.to_bits() ^ 0x8000_0000_0000_0000));
    }
}
pub fn constant32() {
    let table: [fn(f32)->f32;2] = [repeat_external::constant32;2];
    assert!(table[0](-0.0).to_bits() == 1.0f32.to_bits());
}
pub fn constant64() {
    let table: [fn(f64)->f64;2] = [repeat_external::constant64;2];
    assert!(table[0](-0.0).to_bits() == 1.0f64.to_bits());
}
"#,
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let archive = directory.0.join(format!(
                    "librepeat_{}_{optimized}_{retained}.rlib",
                    target.unwrap_or("host")
                ));
                let sysroot = Path::new(env!("MIREN_SYSROOT"));
                let mut command = Command::new(sysroot.join("bin/rustc"));
                command
                    .args(["--sysroot"])
                    .arg(sysroot)
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=repeat_external",
                        "--edition=2024",
                        "-Cpanic=abort",
                        "-Coverflow-checks=yes",
                    ])
                    .arg(format!("-Copt-level={}", if optimized { 2 } else { 0 }))
                    .arg(format!(
                        "-Zalways-encode-mir={}",
                        if retained { "yes" } else { "no" }
                    ))
                    .arg(&dependency)
                    .arg("-o")
                    .arg(&archive);
                if let Some(target) = target {
                    command.args(["--target", target]);
                }
                let output = command.output().unwrap();
                assert!(
                    output.status.success(),
                    "{}",
                    String::from_utf8_lossy(&output.stderr)
                );
                let status = if retained {
                    ProofStatus::Proved
                } else {
                    ProofStatus::Unknown
                };
                let report = verify(
                    &caller,
                    &[
                        ("selected32", status),
                        ("selected64", status),
                        ("constant32", status),
                        ("constant64", status),
                    ],
                    target,
                    optimized,
                    &[
                        "--extern".into(),
                        format!("repeat_external={}", archive.display()),
                    ],
                );
                for name in ["selected32", "selected64", "constant32", "constant64"] {
                    let proof = report
                        .functions
                        .iter()
                        .find(|f| f.name == name)
                        .unwrap()
                        .proof
                        .as_ref()
                        .unwrap();
                    let entered = proof
                        .body_entries
                        .iter()
                        .any(|entry| entry.function.starts_with("repeat_external::"));
                    if retained {
                        assert!(entered);
                    } else {
                        assert!(!entered);
                        assert!(proof.obligations.iter().any(|obligation| {
                            obligation.unknown_category
                                == Some(UnknownCategory::MissingCompilerEvidence)
                        }));
                    }
                }
            }
        }
    }
}
