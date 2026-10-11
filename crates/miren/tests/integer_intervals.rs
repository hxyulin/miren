#![forbid(unsafe_code)]
use miren::{ProofStatus, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::Command;
#[path = "support/table_verification.rs"]
mod table_verification;
use table_verification::{Directory, native, verify};

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/integer_intervals.rs")
}

#[test]
fn checked_integer_intervals_execute_actual_children_and_preserve_checked_u16() {
    use ProofStatus::{Proved as P, Refuted as R};
    let entries = [
        ("i32_range", P),
        ("i32_sibling", P),
        ("i32_empty", P),
        ("i32_wrong", R),
        ("i32_bounds", R),
        ("usize_range", P),
        ("usize_sibling", P),
        ("usize_empty", P),
        ("usize_wrong", R),
        ("u16_range", P),
        ("u16_sibling", P),
        ("u16_empty", P),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&fixture(), &entries, target, optimized, &[]);
            for function in &report.functions {
                let Some(proof) = &function.proof else {
                    continue;
                };
                assert!(proof.assumptions.is_empty());
                assert!(proof.trusted_calls.is_empty());
                if function.name != "i32_bounds" {
                    assert!(proof.models.iter().any(|model| {
                        model.contains("certified checked integer interval; one pending grant")
                            || model.contains("certified checked u16 interval; one pending grant")
                    }));
                }
            }
        }
    }
}

#[test]
fn data_mutation_refutes_unchanged_interval_claims_and_fails_native_assertions() {
    use ProofStatus::Refuted as R;
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    assert_eq!(source.matches("word ^ 0").count(), 2);
    let mutant = directory.0.join("mutant.rs");
    std::fs::write(&mutant, source.replace("word ^ 0", "word ^ 1")).unwrap();
    let entries = [
        ("i32_range", R),
        ("i32_sibling", R),
        ("usize_range", R),
        ("usize_sibling", R),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&mutant, &entries, target, optimized, &[]);
        }
    }
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
        native(&mutant, optimized, true);
    }
}

#[test]
fn integer_interval_external_children_require_actual_available_bodies() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let directory = Directory::new();
                let library = directory.0.join("libstage205_dependency.rlib");
                let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
                compiler
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=stage205_dependency",
                        "--edition=2024",
                        "-Cpanic=abort",
                        "-Coverflow-checks=yes",
                    ])
                    .arg(if retained {
                        "-Zalways-encode-mir=yes"
                    } else {
                        "-Zalways-encode-mir=no"
                    })
                    .arg(fixture().with_file_name("integer_intervals_dependency.rs"))
                    .arg("-o")
                    .arg(&library);
                if optimized {
                    compiler.arg("-Copt-level=2");
                }
                if let Some(target) = target {
                    compiler.args(["--target", target]);
                }
                assert!(compiler.output().unwrap().status.success());
                let status = if retained {
                    ProofStatus::Proved
                } else {
                    ProofStatus::Unknown
                };
                let store_status = if retained && optimized {
                    ProofStatus::Unknown
                } else {
                    status
                };
                let entries = [
                    ("selected_i32", store_status),
                    ("selected_usize", store_status),
                    ("empty_i32", status),
                    ("empty_usize", status),
                ];
                let report = verify(
                    &fixture().with_file_name("integer_intervals_foreign.rs"),
                    &entries,
                    target,
                    optimized,
                    &[
                        "--extern".into(),
                        format!("stage205_dependency={}", library.display()),
                    ],
                );
                for function in &report.functions {
                    let Some(proof) = &function.proof else {
                        continue;
                    };
                    if retained && (!optimized || function.name.starts_with("empty_")) {
                        assert!(proof.body_entries.iter().any(|entry| entry.function
                            == format!("stage205_dependency::{}", function.name)));
                    } else if retained {
                        assert!(proof.obligations.iter().any(|obligation| {
                            obligation.unknown_category == Some(UnknownCategory::Semantics)
                                && obligation
                                    .detail
                                    .contains("mutable u16 store requires direct whole element")
                        }));
                    } else {
                        assert!(proof.obligations.iter().any(|obligation| {
                            obligation.unknown_category
                                == Some(UnknownCategory::MissingCompilerEvidence)
                                && obligation.detail.contains("stage205_dependency::")
                        }));
                    }
                }
            }
        }
    }
}
