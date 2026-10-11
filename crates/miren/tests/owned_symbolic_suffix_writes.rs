#![forbid(unsafe_code)]

use miren::{ProofStatus, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::Command;
#[path = "support/table_verification.rs"]
mod table_verification;
use table_verification::{Directory, native, verify};

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/owned_symbolic_suffix_writes.rs")
}

#[test]
fn bounded_suffix_scope_preserves_legacy_and_measured_new_outcomes() {
    let entries = [
        ("selected", ProofStatus::Proved),
        ("wrong", ProofStatus::Refuted),
        ("correlated", ProofStatus::Proved),
        ("tuple_field", ProofStatus::Proved),
        ("sequential", ProofStatus::Proved),
        ("mixed", ProofStatus::Proved),
        ("branch", ProofStatus::Proved),
        ("two_indices", ProofStatus::Proved),
        ("wrong_two_indices", ProofStatus::Refuted),
        ("unsupported_ref", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&fixture(), &entries, target, optimized, &[]);
            for name in ["selected", "two_indices", "wrong_two_indices"] {
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
                        .any(|entry| entry.function == "actual_word")
                );
            }
        }
    }
}

#[test]
fn actual_rhs_mutation_changes_valid_native_execution_and_existing_two_index_proof() {
    let source = std::fs::read_to_string(fixture()).unwrap();
    assert_eq!(source.matches("word ^ 0").count(), 1);
    let directory = Directory::new();
    let mutant = directory.0.join("mutant.rs");
    std::fs::write(&mutant, source.replace("word ^ 0", "word ^ 1")).unwrap();
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
        native(&mutant, optimized, true);
    }
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(
                &mutant,
                &[("two_indices", ProofStatus::Refuted)],
                target,
                optimized,
                &[],
            );
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "two_indices")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == "actual_word")
            );
        }
    }
}

#[test]
fn genuine_rhs_dependency_requires_available_mir_before_any_suffix_write() {
    let directory = Directory::new();
    let library = directory.0.join("dependency.rs");
    let source = directory.0.join("caller.rs");
    std::fs::write(
        &library,
        "#![no_std]\n#![forbid(unsafe_code)]\n\
         #[inline(never)] pub fn actual_word(word:u16)->u16 {word ^ 0}\n",
    )
    .unwrap();
    std::fs::write(
        &source,
        r#"
#![no_std]
#![forbid(unsafe_code)]
extern crate suffix_dependency;
pub fn selected(mut a: [[[u16; 2]; 2]; 2], i: usize, j: usize, k: usize) {
    if i < 2 && j < 2 && k < 2 {
        a[i][j][k] = suffix_dependency::actual_word(19);
        assert!(a[i][j][k] == 19);
    }
}
pub fn two_indices(mut a: [[u16; 2]; 2], i: usize, j: usize) {
    if i < 2 && j < 2 {
        a[i][j] = suffix_dependency::actual_word(19);
        assert!(a[i][j] == 19);
    }
}
"#,
    )
    .unwrap();
    for retained in [false, true] {
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for optimized in [false, true] {
                let archive = directory.0.join("libsuffix_dependency.rlib");
                let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
                compiler
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=suffix_dependency",
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
                    .arg(&library)
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
                let extra = [
                    "--extern".into(),
                    format!("suffix_dependency={}", archive.display()),
                ];
                let report = verify(
                    &source,
                    &[
                        (
                            "selected",
                            if retained {
                                ProofStatus::Proved
                            } else {
                                ProofStatus::Unknown
                            },
                        ),
                        (
                            "two_indices",
                            if retained {
                                ProofStatus::Proved
                            } else {
                                ProofStatus::Unknown
                            },
                        ),
                    ],
                    target,
                    optimized,
                    &extra,
                );
                for function in &report.functions {
                    let Some(proof) = &function.proof else {
                        continue;
                    };
                    if retained {
                        assert!(
                            proof.body_entries.iter().any(|entry| {
                                entry.function == "suffix_dependency::actual_word"
                            })
                        );
                    } else {
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
