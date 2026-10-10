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
            "miren-retained-owned-field-projections-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/retained_owned_field_projections.rs")
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
        if matches!(
            *name,
            "tuple"
                | "named"
                | "nested"
                | "equality"
                | "aliases"
                | "refreshed"
                | "record"
                | "floats"
                | "mutation_claim"
                | "different_roots"
                | "wrong_field"
                | "bounds"
                | "actual_false_equality"
        ) {
            assert_eq!(
                proof
                    .inputs
                    .values()
                    .filter(|v| v.starts_with("lazy input;"))
                    .count(),
                3
            );
        }
        if *expected == ProofStatus::Unknown {
            let (category, reason) = match *name {
                "lazy_reference_zero" | "lazy_refined_zero" | "lazy_core_zero" => (
                    UnknownCategory::Unclassified,
                    "non-scalar array index is not uniquely determined on this path",
                ),
                "over_cap" => (
                    UnknownCategory::ResourceLimit,
                    "composite slice type array exceeds the 128-element shape budget",
                ),
                "analyzer_only::missing_body" => (
                    UnknownCategory::MissingCompilerEvidence,
                    "no compiler-exported Rust definition matches the foreign symbol",
                ),
                "lifecycle::raw" => (
                    UnknownCategory::Unclassified,
                    "unsupported place projection Deref",
                ),
                "lifecycle::dead_owner" => (
                    UnknownCategory::Unclassified,
                    "reference points to dead or uninitialized storage",
                ),
                "lifecycle::frame_escape" => (
                    UnknownCategory::Semantics,
                    "reference to frame-owned storage cannot escape",
                ),
                "lifecycle::shared_to_mut" => (
                    UnknownCategory::Semantics,
                    "mutable borrow needs writable allocation storage",
                ),
                other => panic!("missing expected frontier for {other}"),
            };
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.status == ProofStatus::Unknown
                        && o.unknown_category == Some(category)
                        && o.detail.contains(reason)),
                "{name}: {:?}",
                proof.obligations
            );
        }
        let body = match *name {
            "tuple" | "aliases" | "refreshed" | "mutation_claim" | "wrong_field"
            | "different_roots" => Some("first"),
            "named" => Some("identity"),
            "record" => Some("record_left"),
            "zero" => Some("zero_marker"),
            "direct_array" => Some("first"),
            "direct_bytes" => Some("byte_first"),
            "actual_false_equality" => Some("<FalseEquality as core::cmp::PartialEq>::eq"),
            "lifecycle::shared_to_mut" => Some("lifecycle::reborrow_write"),
            _ => None,
        };
        if let Some(body) = body {
            assert!(
                proof.body_entries.iter().any(|b| b.function == body),
                "{name}: {:?}",
                proof.body_entries
            );
        }
        if (*expected == ProofStatus::Proved
            && !matches!(
                *name,
                "reference_zero"
                    | "refined_zero"
                    | "core_zero"
                    | "mutable_root"
                    | "direct_array"
                    | "direct_bytes"
                    | "static_source"
                    | "characters"
            ))
            || matches!(
                *name,
                "wrong_field"
                    | "different_roots"
                    | "actual_false_equality"
                    | "lifecycle::shared_to_mut"
            )
        {
            assert!(
                proof.models.iter().any(|model| model
                    == "compiler-certified retained owned field-array shared projection"),
                "{name}: {:?}",
                proof.models
            );
        }
        if matches!(*name, "direct_array" | "direct_bytes") {
            assert!(
                proof
                    .models
                    .iter()
                    .any(|model| model
                        == "compiler-certified retained owned array shared projection")
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
fn field_prefixed_shared_projections_preserve_live_roots() {
    let entries = [
        ("tuple", ProofStatus::Proved),
        ("named", ProofStatus::Proved),
        ("nested", ProofStatus::Proved),
        ("equality", ProofStatus::Proved),
        ("aliases", ProofStatus::Proved),
        ("refreshed", ProofStatus::Proved),
        ("record", ProofStatus::Proved),
        ("floats", ProofStatus::Proved),
        ("characters", ProofStatus::Proved),
        ("bytes", ProofStatus::Proved),
        ("zero", ProofStatus::Proved),
        ("mutation_claim", ProofStatus::Proved),
        ("wrong_field", ProofStatus::Refuted),
        ("bounds", ProofStatus::Refuted),
        ("different_roots", ProofStatus::Refuted),
        ("actual_false_equality", ProofStatus::Refuted),
        ("analyzer_only::missing_body", ProofStatus::Unknown),
        ("reference_zero", ProofStatus::Proved),
        ("refined_zero", ProofStatus::Proved),
        ("core_zero", ProofStatus::Proved),
        ("over_cap", ProofStatus::Unknown),
        ("mutable_root", ProofStatus::Proved),
        ("lifecycle::frame_escape", ProofStatus::Unknown),
        ("lifecycle::dead_owner", ProofStatus::Unknown),
        ("lifecycle::shared_to_mut", ProofStatus::Unknown),
        ("lifecycle::raw", ProofStatus::Unknown),
        ("lazy_reference_zero", ProofStatus::Unknown),
        ("lazy_refined_zero", ProofStatus::Unknown),
        ("lazy_core_zero", ProofStatus::Unknown),
        ("direct_array", ProofStatus::Proved),
        ("direct_bytes", ProofStatus::Proved),
        ("static_source", ProofStatus::Proved),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn actual_inner_assignment_mutation_refutes_and_fails_valid_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutation.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "pub fn first(value: &[u16; 2]) -> u16 {\n    value[0]\n}";
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(
        &mutated,
        source.replace(original, &original.replace("value[0]", "value[1]")),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &mutated,
                &[("mutation_claim", ProofStatus::Refuted)],
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
