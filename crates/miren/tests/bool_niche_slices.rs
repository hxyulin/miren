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
            "miren-bool-niche-slices-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/bool_niche_slices.rs")
}

fn verify(path: &Path, entries: &[(&str, ProofStatus)], target: Option<&str>, optimized: bool) {
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
            .find(|f| f.name == *name)
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
        assert!(proof.trusted_calls.is_empty());
        assert!(proof.entry_assumptions.is_empty());
        if *expected == ProofStatus::Unknown {
            let (category, reason) = match *name {
                "ref_zero" | "refined_zero" | "wrapped_niche" | "multi_niche" | "mutable"
                | "competing" => (
                    UnknownCategory::Semantics,
                    "only read-only byte slices and byte arrays are modeled",
                ),
                "analyzer_only::inactive_payload" => (
                    UnknownCategory::Unclassified,
                    "enum downcast lacks a proven variant check",
                ),
                "contains" => (
                    UnknownCategory::Semantics,
                    "whole composite slice membership is unsupported",
                ),
                "equality" => (
                    UnknownCategory::Semantics,
                    "whole composite slice equality is unsupported",
                ),
                "type_budget" => (
                    UnknownCategory::ResourceLimit,
                    "composite slice type array exceeds the 128-element shape budget",
                ),
                "analyzer_only::missing_body" => (
                    UnknownCategory::MissingCompilerEvidence,
                    "no compiler-exported Rust definition matches the foreign symbol",
                ),
                "analyzer_only::dead_empty" => (
                    UnknownCategory::Unclassified,
                    "reference points to dead or uninitialized storage",
                ),
                other => panic!("missing expected frontier for {other}"),
            };
            assert!(
                proof.obligations.iter().any(|obligation| {
                    obligation.status == ProofStatus::Unknown
                        && obligation.unknown_category == Some(category)
                        && obligation.detail.contains(reason)
                }),
                "{name}: {:?}",
                proof.obligations
            );
        }
        if matches!(
            *name,
            "repeated" | "long_selected" | "view" | "cursor" | "borrowed_payload"
        ) {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == "selected_bool")
            );
        }
        if *name == "user_method" {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == "Switch::read")
            );
        }
        if *expected != ProofStatus::Unknown {
            let label = if *name == "zero_original" {
                concat!(
                    "readonly composite slice; exact compiler shape ",
                    "and independent primitive leaf arrays"
                )
            } else {
                "readonly tagged slice; legal tag and correlated latent payload columns"
            };
            assert!(
                proof.models.iter().any(|model| model.contains(label)),
                "{name}: {:?}",
                proof.models
            );
        }
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|obligation| {
                obligation.status == ProofStatus::Refuted
                    && obligation.model.is_some()
                    && obligation.query.is_some()
            }));
        }
    }
}

fn native_tests(path: &Path, directory: &Directory, optimized: bool, filter: Option<&str>) -> bool {
    let executable = directory.0.join("native");
    let compiler = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
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
    let mut command = Command::new(executable);
    if let Some(filter) = filter {
        command.arg(filter);
    }
    command.output().unwrap().status.success()
}

#[test]
fn bool_niche_slices_preserve_active_values_and_exact_source() {
    let entries = [
        ("analyzer_only::copied_handle_live", ProofStatus::Proved),
        ("analyzer_only::dead_empty", ProofStatus::Unknown),
        ("analyzer_only::inactive_payload", ProofStatus::Unknown),
        ("analyzer_only::missing_body", ProofStatus::Unknown),
        ("borrowed_payload", ProofStatus::Proved),
        ("bounds", ProofStatus::Refuted),
        ("competing", ProofStatus::Unknown),
        ("char_niche", ProofStatus::Proved),
        ("contains", ProofStatus::Unknown),
        ("cursor", ProofStatus::Proved),
        ("cursor_metadata", ProofStatus::Proved),
        ("equality", ProofStatus::Unknown),
        ("false_bool", ProofStatus::Refuted),
        ("false_correlation", ProofStatus::Refuted),
        ("false_variant", ProofStatus::Refuted),
        ("local_sum", ProofStatus::Proved),
        ("long_selected", ProofStatus::Proved),
        ("metadata", ProofStatus::Proved),
        ("multi_niche", ProofStatus::Unknown),
        ("mutable", ProofStatus::Unknown),
        // Original source is PROVED in all four profiles after exact NZ16 certification.
        ("nonzero_niche", ProofStatus::Proved),
        ("occurrence", ProofStatus::Proved),
        ("ref_zero", ProofStatus::Unknown),
        ("refined_zero", ProofStatus::Unknown),
        ("repeated", ProofStatus::Proved),
        ("reversed", ProofStatus::Proved),
        ("type_budget", ProofStatus::Unknown),
        ("unwrap", ProofStatus::Refuted),
        ("user_method", ProofStatus::Proved),
        ("view", ProofStatus::Proved),
        ("wrapped_niche", ProofStatus::Unknown),
        ("zero_original", ProofStatus::Proved),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn actual_bool_flip_refutes_and_fails_valid_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutation.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "Some(value) => value,";
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(&mutated, source.replace(original, "Some(value) => !value,")).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &mutated,
                &[("long_selected", ProofStatus::Refuted)],
                target,
                optimized,
            );
        }
    }
    for optimized in [false, true] {
        assert!(native_tests(&fixture(), &Directory::new(), optimized, None));
        assert!(!native_tests(
            &mutated,
            &Directory::new(),
            optimized,
            Some("mutation_guard"),
        ));
    }
}
