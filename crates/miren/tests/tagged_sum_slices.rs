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
            "miren-tagged-sum-slices-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/tagged_sum_slices.rs")
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
                "mutable_root"
                | "reference_zero"
                | "refined_zero"
                | "dropped_zero"
                | "niche_char"
                | "niche_nonzero"
                | "nominal_payload_zero" => (
                    UnknownCategory::Semantics,
                    "only read-only byte slices and byte arrays are modeled",
                ),
                "unsupported_contains" => (
                    UnknownCategory::Semantics,
                    "whole composite slice membership is unsupported",
                ),
                "unsupported_equality" => (
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
                "analyzer_only::dead_empty_metadata" => (
                    UnknownCategory::Unclassified,
                    "reference points to dead or uninitialized storage",
                ),
                "analyzer_only::inactive_payload" => (
                    UnknownCategory::Unclassified,
                    "enum downcast lacks a proven variant check",
                ),
                "analyzer_only::raw_source" => (
                    UnknownCategory::Unclassified,
                    if optimized {
                        "raw slice construction requires a shared compiler-typed byte slice"
                    } else {
                        "tracked raw addresses require a sized pointee"
                    },
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
            "guarded_pair" | "long_selected" | "checked_cursor" | "selected_view" | "payload_tuple"
        ) {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == "selected_pair")
            );
        }
        if *name == "analyzer_only::inactive_payload" {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| { entry.function == "analyzer_only::unchecked_payload" })
            );
        }
        if matches!(
            *name,
            "guarded_pair"
                | "false_pair"
                | "arbitrary_tag"
                | "option_selected"
                | "option_unwrap"
                | "long_selected"
                | "checked_cursor"
                | "selected_view"
                | "signed_tags"
                | "numerical_bits"
                | "payload_tuple"
                | "nested_sum"
                | "cursor_metadata"
                | "dynamic_layout"
                | "out_of_bounds"
                | "analyzer_only::copied_handle_live"
                | "analyzer_only::inactive_payload"
        ) {
            assert!(
                proof.models.iter().any(|model| model.contains(
                    "readonly tagged slice; legal tag and correlated latent payload columns"
                )),
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
fn direct_tag_slices_preserve_active_payload_and_source_validity() {
    let entries = [
        ("analyzer_only::copied_handle_live", ProofStatus::Proved),
        ("analyzer_only::dead_empty_metadata", ProofStatus::Unknown),
        ("analyzer_only::inactive_payload", ProofStatus::Unknown),
        ("analyzer_only::missing_body", ProofStatus::Unknown),
        ("analyzer_only::raw_source", ProofStatus::Unknown),
        ("arbitrary_tag", ProofStatus::Refuted),
        ("checked_cursor", ProofStatus::Proved),
        ("cursor_metadata", ProofStatus::Proved),
        ("dropped_zero", ProofStatus::Unknown),
        ("dynamic_layout", ProofStatus::Proved),
        ("false_pair", ProofStatus::Refuted),
        ("guarded_pair", ProofStatus::Proved),
        ("long_selected", ProofStatus::Proved),
        ("mutable_root", ProofStatus::Unknown),
        ("niche_bool", ProofStatus::Proved),
        ("niche_char", ProofStatus::Unknown),
        ("niche_nonzero", ProofStatus::Unknown),
        ("numerical_bits", ProofStatus::Proved),
        ("option_selected", ProofStatus::Proved),
        ("option_unwrap", ProofStatus::Refuted),
        ("out_of_bounds", ProofStatus::Refuted),
        ("payload_tuple", ProofStatus::Proved),
        ("reference_zero", ProofStatus::Unknown),
        ("refined_zero", ProofStatus::Unknown),
        ("selected_view", ProofStatus::Proved),
        ("signed_tags", ProofStatus::Proved),
        ("type_budget", ProofStatus::Unknown),
        ("unsupported_contains", ProofStatus::Unknown),
        ("unsupported_equality", ProofStatus::Unknown),
        ("zero_payload", ProofStatus::Proved),
        ("nested_sum", ProofStatus::Proved),
        ("nominal_payload_zero", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn actual_payload_mutation_refutes_and_fails_valid_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutation.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "Reading::Pair(left, _) => Some(left),";
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(
        &mutated,
        source.replace(original, "Reading::Pair(_, right) => Some(right),"),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &mutated,
                &[("guarded_pair", ProofStatus::Refuted)],
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
