#![forbid(unsafe_code)]

use miren::{ProofStatus, Report, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct Directory(PathBuf);

impl Directory {
    fn new() -> Self {
        let id = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "miren-nonzero-niche-slices-{}-{id}",
            std::process::id()
        ));
        std::fs::create_dir_all(&path).unwrap();
        Self(path)
    }
}

impl Drop for Directory {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/nonzero_niche_slices.rs")
}

fn verify(
    path: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    dependency: Option<&Path>,
) {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    for (name, _) in entries {
        command.args(["--entry", name]);
    }
    command
        .args(["--", "--crate-type=lib", "--edition=2024"])
        .arg(path)
        .arg("--out-dir")
        .arg(&directory.0)
        .args(["-Cpanic=abort", "-Coverflow-checks=yes"]);
    if let Some(dependency) = dependency {
        command
            .arg("--extern")
            .arg(format!("nonzero_niche_dependency={}", dependency.display()));
    }
    if optimized {
        command.arg("-Copt-level=2");
    }
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    let output = command.output().unwrap();
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    assert_eq!(
        output.status.success(),
        entries
            .iter()
            .all(|(_, status)| *status == ProofStatus::Proved)
    );
    for (name, expected) in entries {
        let proof = report
            .functions
            .iter()
            .find(|function| function.name == *name)
            .unwrap()
            .proof
            .as_ref()
            .unwrap();
        assert_eq!(
            proof.status, *expected,
            "{target:?} optimized={optimized} {name}: {:?}",
            proof.obligations
        );
        assert!(proof.assumptions.is_empty());
        assert!(proof.entry_assumptions.is_empty());
        assert!(proof.trusted_calls.is_empty());
        if *expected == ProofStatus::Unknown {
            let (category, reason) = match *name {
                "expanded_budget" => (
                    UnknownCategory::ResourceLimit,
                    "NonZero niche original child exceeds composite shape budget",
                ),
                "over_budget" => (
                    UnknownCategory::ResourceLimit,
                    "composite slice type array exceeds the 128-element shape budget",
                ),
                "signed_niche" | "unsupported_zero" => (
                    UnknownCategory::Semantics,
                    "NonZero wrapper original identity mismatch",
                ),
                "explicit_tag" => (
                    UnknownCategory::Semantics,
                    "NonZero niche requires actual niche encoding",
                ),
                "whole_membership" => (
                    UnknownCategory::Semantics,
                    "whole composite slice membership is unsupported",
                ),
                "foreign_selected" => (
                    UnknownCategory::MissingCompilerEvidence,
                    "nonzero_niche_dependency::selected",
                ),
                "independent_roots" | "wrong_independent" | "mutable_niche" | "nonzero"
                | "pointer_niche" => (
                    UnknownCategory::Semantics,
                    "only read-only byte slices and byte arrays are modeled",
                ),
                other => panic!("missing frontier for {other}"),
            };
            assert!(proof.obligations.iter().any(|obligation| {
                obligation.status == ProofStatus::Unknown
                    && obligation.unknown_category == Some(category)
                    && obligation.detail.contains(reason)
            }));
        }
        if matches!(
            *name,
            "repeated" | "fixed_array" | "tuple_child" | "none_branch"
        ) {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == "selected")
            );
        }
        if *name == "helper_payload" {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == "identity")
            );
        }
        if *name == "foreign_selected" && *expected == ProofStatus::Proved {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| { entry.function == "nonzero_niche_dependency::selected" })
            );
        }
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|obligation| {
                obligation.status == ProofStatus::Refuted
                    && obligation.query.is_some()
                    && obligation.model.is_some()
            }));
        }
    }
}

fn native(path: &Path, directory: &Directory, optimized: bool) -> bool {
    let compiler = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
    let executable = directory.0.join("native");
    let mut command = Command::new(compiler);
    command
        .args(["--test", "--edition=2024"])
        .arg(path)
        .arg("-o")
        .arg(&executable);
    if optimized {
        command.arg("-Copt-level=2");
    }
    let output = command.output().unwrap();
    assert!(output.status.success(), "{output:?}");
    Command::new(executable).output().unwrap().status.success()
}

#[test]
fn exact_nonzero_niches_keep_payloads_guarded_and_conservative_frontiers() {
    let entries = [
        ("repeated", ProofStatus::Proved),
        ("wrong", ProofStatus::Refuted),
        ("local_sum", ProofStatus::Proved),
        ("reversed", ProofStatus::Proved),
        ("nonzero", ProofStatus::Unknown),
        ("zero_array", ProofStatus::Proved),
        ("pointer_niche", ProofStatus::Unknown),
        ("copied_payload", ProofStatus::Proved),
        ("helper_payload", ProofStatus::Proved),
        ("shared_payload", ProofStatus::Proved),
        ("fixed_array", ProofStatus::Proved),
        ("tuple_child", ProofStatus::Proved),
        ("independent_roots", ProofStatus::Unknown),
        ("wrong_independent", ProofStatus::Unknown),
        ("none_branch", ProofStatus::Proved),
        ("wrong_none", ProofStatus::Refuted),
        ("wrong_bounds", ProofStatus::Refuted),
        ("zero_max", ProofStatus::Proved),
        ("unsupported_zero", ProofStatus::Unknown),
        ("signed_niche", ProofStatus::Unknown),
        ("over_budget", ProofStatus::Unknown),
        ("expanded_budget", ProofStatus::Unknown),
        ("whole_membership", ProofStatus::Unknown),
        ("mutable_niche", ProofStatus::Unknown),
        ("explicit_tag", ProofStatus::Unknown),
        ("paired_columns", ProofStatus::Proved),
        ("wrong_paired_columns", ProofStatus::Refuted),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized, None);
        }
    }
}

#[test]
fn actual_selected_helper_mutation_refutes_and_fails_valid_native_claim() {
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "Some(value) => value.get(),";
    assert_eq!(source.matches(original).count(), 1);
    let directory = Directory::new();
    let mutant = directory.0.join("mutant.rs");
    std::fs::write(
        &mutant,
        source.replace(original, "Some(value) => value.get().wrapping_add(1),"),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &mutant,
                &[("repeated", ProofStatus::Refuted)],
                target,
                optimized,
                None,
            );
        }
    }
    for optimized in [false, true] {
        assert!(native(&fixture(), &Directory::new(), optimized));
        assert!(!native(&mutant, &Directory::new(), optimized));
    }
}

#[test]
fn genuine_foreign_helper_body_availability_precedes_success() {
    let compiler = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
    let source = fixture().with_file_name("nonzero_niche_dependency.rs");
    let root = fixture().with_file_name("nonzero_niche_foreign.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let directory = Directory::new();
                let library = directory.0.join("libnonzero_niche_dependency.rlib");
                let mut command = Command::new(&compiler);
                command
                    .args([
                        "--crate-name=nonzero_niche_dependency",
                        "--crate-type=rlib",
                        "--edition=2024",
                        "-Cpanic=abort",
                    ])
                    .arg(&source)
                    .arg("-o")
                    .arg(&library)
                    .arg(if retained {
                        "-Zalways-encode-mir=yes"
                    } else {
                        "-Zalways-encode-mir=no"
                    });
                if optimized {
                    command.arg("-Copt-level=2");
                }
                if let Some(target) = target {
                    command.args(["--target", target]);
                }
                let output = command.output().unwrap();
                assert!(output.status.success(), "{output:?}");
                verify(
                    &root,
                    &[(
                        "foreign_selected",
                        if retained {
                            ProofStatus::Proved
                        } else {
                            ProofStatus::Unknown
                        },
                    )],
                    target,
                    optimized,
                    Some(&library),
                );
            }
        }
    }
}
