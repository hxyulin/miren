#![forbid(unsafe_code)]
use miren::ProofStatus;
use std::path::{Path, PathBuf};
use std::process::Command;
#[path = "support/table_verification.rs"]
mod table_verification;
use table_verification::{Directory, native, verify};

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/known_function_pointer_repeat.rs")
}

// These are proposed outcomes for the first measured compiler checkpoint, not prior evidence.
#[test]
fn original_known_repeat_calls_preserve_signatures_and_limits() {
    let entries = [
        ("unary", ProofStatus::Proved),
        ("unary_wrong", ProofStatus::Refuted),
        ("binary", ProofStatus::Proved),
        ("binary_wrong", ProofStatus::Refuted),
        ("last", ProofStatus::Proved),
        ("dispatch_budget", ProofStatus::Unknown),
        ("count_budget", ProofStatus::Unknown),
        ("zero", ProofStatus::Proved),
        ("sequential", ProofStatus::Proved),
        ("opaque", ProofStatus::Unknown),
        ("product", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&fixture(), &entries, target, optimized, &[]);
            for (name, helper) in [
                ("unary", "identity"),
                ("binary", "pair"),
                ("last", "identity"),
            ] {
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
                        .any(|entry| entry.function == helper)
                );
            }
        }
    }
}

#[test]
fn real_helper_and_argument_order_mutations_fail_unchanged_claims() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
    }
    for (name, old, new, selected) in [
        ("helper", "value ^ 0", "value ^ 1", "unary"),
        (
            "order",
            "((a as i64) - (b as i64)) ^ 0",
            "((b as i64) - (a as i64)) ^ 0",
            "binary",
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
fn genuine_repeat_targets_require_available_bodies_including_constant_calls() {
    let directory = Directory::new();
    let dependency = directory.0.join("dependency.rs");
    std::fs::write(
        &dependency,
        r#"#![no_std]
#![forbid(unsafe_code)]
#[inline(never)] pub fn identity(word: u16) -> u16 { word }
#[inline(never)] pub fn constant(_: u16) -> u16 { 7 }
"#,
    )
    .unwrap();
    let caller = directory.0.join("caller.rs");
    std::fs::write(
        &caller,
        r#"#![no_std]
#![forbid(unsafe_code)]
pub fn selected(index: usize, word: u16) {
    let table: [fn(u16)->u16;2] = [repeat_external::identity;2];
    if index < 2 { assert!(table[index](word) == word); }
}
pub fn constant() {
    let table: [fn(u16)->u16;1] = [repeat_external::constant;1];
    assert!(table[0](0) == 7);
}
pub fn zero() {
    let table: [fn(u16)->u16;0] = [repeat_external::constant;0];
    assert!(table.len() == 0);
}
"#,
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let archive = directory.0.join(format!(
                    "librepeat-{}-{optimized}-{retained}.rlib",
                    target.unwrap_or("host"),
                ));
                let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
                compiler
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=repeat_external",
                        "--edition=2024",
                        "-Cpanic=abort",
                    ])
                    .arg(if retained {
                        "-Zalways-encode-mir=yes"
                    } else {
                        "-Zalways-encode-mir=no"
                    })
                    .arg(if optimized {
                        "-Copt-level=2"
                    } else {
                        "-Copt-level=0"
                    })
                    .arg(&dependency)
                    .arg("-o")
                    .arg(&archive);
                if let Some(target) = target {
                    compiler.args(["--target", target]);
                }
                let output = compiler.output().unwrap();
                assert!(
                    output.status.success(),
                    "{}",
                    String::from_utf8_lossy(&output.stderr)
                );
                let expected = if retained {
                    ProofStatus::Proved
                } else {
                    ProofStatus::Unknown
                };
                let report = verify(
                    &caller,
                    &[
                        ("selected", expected),
                        ("constant", expected),
                        ("zero", ProofStatus::Proved),
                    ],
                    target,
                    optimized,
                    &[
                        "--extern".into(),
                        format!("repeat_external={}", archive.display()),
                    ],
                );
                for name in ["selected", "constant"] {
                    let proof = report
                        .functions
                        .iter()
                        .find(|f| f.name == name)
                        .unwrap()
                        .proof
                        .as_ref()
                        .unwrap();
                    if retained {
                        let helper = if name == "selected" {
                            "identity"
                        } else {
                            "constant"
                        };
                        assert!(proof.body_entries.iter()
                            .any(|entry| entry.function == format!("repeat_external::{helper}")));
                    } else {
                        assert!(proof.obligations.iter().any(|q| q.unknown_category
                            == Some(miren::UnknownCategory::MissingCompilerEvidence)));
                    }
                }
            }
        }
    }
}
