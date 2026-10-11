#![forbid(unsafe_code)]
use miren::{ProofStatus, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::Command;
#[path = "support/table_verification.rs"]
mod table_verification;
use table_verification::{Directory, native, verify};

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/float_function_tables.rs")
}

#[test]
fn exact_float_tables_follow_actual_bits_and_bodies() {
    let entries = [
        ("selected32", ProofStatus::Proved),
        ("wrong32", ProofStatus::Refuted),
        ("opaque32", ProofStatus::Unknown),
        ("repeat32", ProofStatus::Unknown),
        ("selected64", ProofStatus::Proved),
        ("wrong64", ProofStatus::Refuted),
        ("opaque64", ProofStatus::Unknown),
        ("repeat64", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&fixture(), &entries, target, optimized, &[]);
            for (name, body) in [("selected32", "second32"), ("selected64", "second64")] {
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == name)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert!(
                    proof
                        .body_entries
                        .iter()
                        .any(|entry| entry.function == body)
                );
            }
        }
    }
}

#[test]
fn actual_float_helper_and_order_mutations_fail_bit_claims() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
    }
    for (name, old, new, selected) in [
        (
            "helper32",
            "pub fn first32(value: f32) -> f32 { value }",
            "pub fn first32(value: f32) -> f32 { -value }",
            "selected32",
        ),
        (
            "helper64",
            "pub fn first64(value: f64) -> f64 { value }",
            "pub fn first64(value: f64) -> f64 { -value }",
            "selected64",
        ),
        (
            "order",
            concat!(
                "pub fn selected32(index: usize, value: f32) {\n",
                "    let table: [fn(f32) -> f32; 2] = [first32, second32];"
            ),
            concat!(
                "pub fn selected32(index: usize, value: f32) {\n",
                "    let table: [fn(f32) -> f32; 2] = [second32, first32];"
            ),
            "selected32",
        ),
    ] {
        assert_eq!(source.matches(old).count(), 1);
        let path = directory.0.join(format!("{name}.rs"));
        std::fs::write(&path, source.replacen(old, new, 1)).unwrap();
        for optimized in [false, true] {
            native(&path, optimized, true);
            for target in [None, Some("thumbv7em-none-eabihf")] {
                verify(
                    &path,
                    &[(selected, ProofStatus::Refuted)],
                    target,
                    optimized,
                    &[],
                );
            }
        }
    }
}

#[test]
fn genuine_float_bodies_are_required_even_for_constant_targets() {
    let directory = Directory::new();
    let dependency = directory.0.join("dependency.rs");
    let caller = directory.0.join("caller.rs");
    std::fs::write(
        &dependency,
        r#"#![no_std]
#![forbid(unsafe_code)]
#[inline(never)] pub fn identity32(value: f32) -> f32 { value }
#[inline(never)] pub fn identity64(value: f64) -> f64 { value }
#[inline(never)] pub fn constant32(_: f32) -> f32 { 1.0 }
#[inline(never)] pub fn constant64(_: f64) -> f64 { 1.0 }
"#,
    )
    .unwrap();
    std::fs::write(
        &caller,
        r#"#![no_std]
#![forbid(unsafe_code)]
fn identity32(value: f32) -> f32 { value }
fn identity64(value: f64) -> f64 { value }
fn constant32(_: f32) -> f32 { 1.0 }
fn constant64(_: f64) -> f64 { 1.0 }
pub fn selected32(index: usize, value: f32) {
    let table: [fn(f32)->f32;2] = [identity32, float_external::identity32];
    if index < 2 { assert!(table[index](value).to_bits() == value.to_bits()); }
}
pub fn selected64(index: usize, value: f64) {
    let table: [fn(f64)->f64;2] = [identity64, float_external::identity64];
    if index < 2 { assert!(table[index](value).to_bits() == value.to_bits()); }
}
pub fn literal32(index: usize) {
    let table: [fn(f32)->f32;2] = [constant32, float_external::constant32];
    if index < 2 { assert!(table[index](0.0).to_bits() == 1.0_f32.to_bits()); }
}
pub fn literal64(index: usize) {
    let table: [fn(f64)->f64;2] = [constant64, float_external::constant64];
    if index < 2 { assert!(table[index](0.0).to_bits() == 1.0_f64.to_bits()); }
}
"#,
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let archive = directory.0.join(format!(
                    "libfloat_{}_{optimized}_{retained}.rlib",
                    target.unwrap_or("host")
                ));
                let mut command = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
                command
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=float_external",
                        "--edition=2024",
                        "-Cpanic=abort",
                        "--sysroot",
                        env!("MIREN_SYSROOT"),
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
                        ("literal32", status),
                        ("literal64", status),
                    ],
                    target,
                    optimized,
                    &[
                        "--extern".into(),
                        format!("float_external={}", archive.display()),
                    ],
                );
                for function in report.functions {
                    let Some(proof) = function.proof else {
                        continue;
                    };
                    if retained {
                        assert!(
                            proof
                                .body_entries
                                .iter()
                                .any(|entry| entry.function.starts_with("float_external::"))
                        );
                    } else {
                        assert!(
                            proof
                                .obligations
                                .iter()
                                .any(|obligation| obligation.unknown_category
                                    == Some(UnknownCategory::MissingCompilerEvidence))
                        );
                        assert!(
                            !proof
                                .body_entries
                                .iter()
                                .any(|entry| entry.function.starts_with("float_external::"))
                        );
                    }
                }
            }
        }
    }
}
