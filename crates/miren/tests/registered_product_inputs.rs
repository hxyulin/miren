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
            "miren-registered-product-inputs-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/registered_product_inputs.rs")
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
            "repeated"
                | "constant_paths"
                | "copied_root"
                | "whole_write"
                | "untouched"
                | "alignment"
                | "root_alignment"
                | "mutation_claim"
                | "roots_are_equal"
                | "occurrences_are_equal"
                | "fields_are_equal"
                | "bounds"
                | "retained_borrow"
                | "floating_observations"
        ) {
            for input in ["a", "_b", "_c"] {
                if let Some(description) = proof.inputs.get(input) {
                    assert!(
                        description.starts_with("lazy input;"),
                        "{name}: {:?}",
                        proof.inputs
                    );
                }
            }
            assert_eq!(
                proof
                    .inputs
                    .values()
                    .filter(|v| v.starts_with("lazy input;"))
                    .count(),
                3,
                "{name}: {:?}",
                proof.inputs,
            );
        }
        if matches!(*name, "alignment" | "root_alignment") {
            assert!(proof.models.iter().any(|model| model.contains(concat!(
                "safe sized alignment; exact pure receiver ",
                "and compiler ABI alignment",
            ))));
        }
        if *expected == ProofStatus::Unknown {
            let (category, reason) = match *name {
                "reference_zero" | "refined_zero" | "core_zero" => (
                    UnknownCategory::Unclassified,
                    "non-scalar array index is not uniquely determined on this path",
                ),
                "enum_origin" => (UnknownCategory::Semantics, "source reservation certificate"),
                "oversized" => (
                    UnknownCategory::ResourceLimit,
                    "composite slice type exceeds its depth or expanded node budget",
                ),
                "observations" => (
                    UnknownCategory::Unclassified,
                    "input shape exceeds the 512-value budget",
                ),
                "analyzer_only::missing_body" => (
                    UnknownCategory::MissingCompilerEvidence,
                    "no compiler-exported Rust definition matches the foreign symbol",
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
            "mutation_claim" => Some("chosen"),
            _ => None,
        };
        if let Some(body) = body {
            assert!(
                proof.body_entries.iter().any(|b| b.function == body),
                "{name}: {:?}",
                proof.body_entries
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
fn registered_product_inputs_preserves_exact_abi_and_source_lifetimes() {
    let entries = [
        ("repeated", ProofStatus::Proved),
        ("constant_paths", ProofStatus::Proved),
        ("copied_root", ProofStatus::Proved),
        ("whole_write", ProofStatus::Proved),
        ("untouched", ProofStatus::Proved),
        ("alignment", ProofStatus::Proved),
        ("root_alignment", ProofStatus::Proved),
        ("mutation_claim", ProofStatus::Proved),
        ("floating_observations", ProofStatus::Proved),
        ("observations", ProofStatus::Unknown),
        ("roots_are_equal", ProofStatus::Refuted),
        ("occurrences_are_equal", ProofStatus::Refuted),
        ("fields_are_equal", ProofStatus::Refuted),
        ("bounds", ProofStatus::Refuted),
        ("retained_borrow", ProofStatus::Proved),
        ("reference_zero", ProofStatus::Unknown),
        ("refined_zero", ProofStatus::Unknown),
        ("core_zero", ProofStatus::Unknown),
        ("enum_origin", ProofStatus::Unknown),
        ("oversized", ProofStatus::Unknown),
        ("analyzer_only::missing_body", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn actual_field_getter_mutation_refutes_and_fails_valid_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutation.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "pub fn chosen(record: Record) -> u16 {\n    record.left\n}";
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(
        &mutated,
        source.replace(
            original,
            "pub fn chosen(record: Record) -> u16 {\n    record.right\n}",
        ),
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
            Some("mutation_guard")
        ));
    }
}
