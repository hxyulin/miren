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
            "miren-nominal-enum-payloads-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/nominal_enum_payloads.rs")
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
                "mutable" | "packed_zero" | "reference_zero" | "refined_zero" | "core_zero"
                | "drop_zero" | "wrapped_niche" => (
                    UnknownCategory::Semantics,
                    "only read-only byte slices and byte arrays are modeled",
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
                "analyzer_only::inactive_payload" => (
                    UnknownCategory::Unclassified,
                    "enum downcast lacks a proven variant check",
                ),
                "analyzer_only::raw_consumer" => (
                    UnknownCategory::Unclassified,
                    "tracked raw addresses require a sized pointee",
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
            "selected"
                | "falsely_zero"
                | "falsely_equal"
                | "long_selected"
                | "view"
                | "cursor"
                | "nested"
        ) {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == "Record::selected")
            );
        }
        let custom_body = match *name {
            "custom_false_equality" => Some("<FalseEquality as core::cmp::PartialEq>::eq"),
            "custom_panic_clone" => Some("<PanicClone as core::clone::Clone>::clone"),
            _ => None,
        };
        if let Some(body) = custom_body {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == body),
                "{name}: {:?}",
                proof.body_entries
            );
        }
        if *name == "analyzer_only::inactive_payload" {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == "analyzer_only::inactive")
            );
        }
        if *expected != ProofStatus::Unknown || *name == "analyzer_only::inactive_payload" {
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
fn nominal_enum_payloads_preserve_original_fields_and_lifetime() {
    let entries = [
        ("analyzer_only::dead_empty", ProofStatus::Unknown),
        ("analyzer_only::inactive_payload", ProofStatus::Unknown),
        ("analyzer_only::missing_body", ProofStatus::Unknown),
        ("analyzer_only::raw_consumer", ProofStatus::Unknown),
        ("borrowed_field", ProofStatus::Proved),
        ("contains", ProofStatus::Unknown),
        ("core_zero", ProofStatus::Unknown),
        ("cursor", ProofStatus::Proved),
        ("custom_false_equality", ProofStatus::Refuted),
        ("custom_panic_clone", ProofStatus::Refuted),
        ("drop_zero", ProofStatus::Unknown),
        ("equality", ProofStatus::Unknown),
        ("falsely_equal", ProofStatus::Refuted),
        ("falsely_zero", ProofStatus::Refuted),
        ("generic_payload", ProofStatus::Proved),
        ("layout", ProofStatus::Proved),
        ("long_selected", ProofStatus::Proved),
        ("mutable", ProofStatus::Unknown),
        ("nested", ProofStatus::Proved),
        ("numerical_bits", ProofStatus::Proved),
        ("out_of_bounds", ProofStatus::Refuted),
        ("packed_zero", ProofStatus::Unknown),
        ("pair_payload", ProofStatus::Proved),
        ("reference_zero", ProofStatus::Unknown),
        ("refined_zero", ProofStatus::Unknown),
        ("scalar_payload", ProofStatus::Proved),
        ("selected", ProofStatus::Proved),
        ("type_budget", ProofStatus::Unknown),
        ("view", ProofStatus::Proved),
        ("wrapped_niche", ProofStatus::Unknown),
        ("zero_payload", ProofStatus::Proved),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn actual_getter_mutation_refutes_and_fails_valid_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutation.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "pub fn selected(self) -> u16 {\n        self.left\n    }";
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(
        &mutated,
        source.replace(original, &original.replace("self.left", "self.right")),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &mutated,
                &[("selected", ProofStatus::Refuted)],
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
