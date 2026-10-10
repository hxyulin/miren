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
            "miren-owned-call-destinations-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/owned_call_destinations.rs")
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
                "analyzer_only::missing_body" => (
                    UnknownCategory::MissingCompilerEvidence,
                    "no compiler-exported Rust definition matches the foreign symbol",
                ),
                "analyzer_only::retained" => (
                    UnknownCategory::Semantics,
                    "call destination dereference requires pre-call base-location capture",
                ),
                "analyzer_only::retroactive_bound" | "analyzer_only::invalid_fixed_prefix" => (
                    UnknownCategory::Unclassified,
                    "memory index lacks a proven bounds check",
                ),
                "analyzer_only::unsupported_zero" => (
                    UnknownCategory::Semantics,
                    "indexed call destination requires a complete pure owned root type",
                ),
                "analyzer_only::dead_owner" => (
                    UnknownCategory::Unclassified,
                    "uninitialized or unavailable local",
                ),
                "analyzer_only::dereference_correct" | "analyzer_only::dereference_false" => (
                    UnknownCategory::Semantics,
                    "call destination dereference requires pre-call base-location capture",
                ),
                other => panic!("missing frontier for {other}"),
            };
            assert!(
                proof.obligations.iter().any(|o| {
                    o.status == ProofStatus::Unknown
                        && o.unknown_category == Some(category)
                        && o.detail.contains(reason)
                }),
                "{name}: {:?}",
                proof.obligations
            );
        }
        let body = match *name {
            "array_destination" | "tuple_destination" | "struct_destination" | "false_value"
            | "repeated_index" => Some("replacement"),
            "pre_call_destination" | "post_call_destination" => Some("advance"),
            "current_owner" => Some("refresh"),
            "once_only" => Some("count_once"),
            "branch_results" => Some("choose"),
            "unit_effect" => Some("panic_unit"),
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
fn call_destinations_use_pre_call_addresses_and_returned_owner_storage() {
    let entries = [
        ("array_destination", ProofStatus::Proved),
        ("tuple_destination", ProofStatus::Proved),
        ("struct_destination", ProofStatus::Proved),
        ("pre_call_destination", ProofStatus::Proved),
        ("current_owner", ProofStatus::Proved),
        ("once_only", ProofStatus::Proved),
        ("branch_results", ProofStatus::Proved),
        ("repeated_index", ProofStatus::Proved),
        ("false_value", ProofStatus::Refuted),
        ("post_call_destination", ProofStatus::Refuted),
        ("unit_effect", ProofStatus::Refuted),
        ("analyzer_only::missing_body", ProofStatus::Unknown),
        ("analyzer_only::retained", ProofStatus::Unknown),
        ("analyzer_only::retroactive_bound", ProofStatus::Unknown),
        ("analyzer_only::unsupported_zero", ProofStatus::Unknown),
        ("analyzer_only::dead_owner", ProofStatus::Unknown),
        ("analyzer_only::invalid_fixed_prefix", ProofStatus::Unknown),
        ("analyzer_only::dereference_correct", ProofStatus::Unknown),
        ("analyzer_only::dereference_false", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn actual_replacement_mutation_refutes_and_fails_valid_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutation.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "pub fn replacement() -> u16 {\n    19\n}";
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(
        &mutated,
        source.replace(original, &original.replace("19", "20")),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &mutated,
                &[("array_destination", ProofStatus::Refuted)],
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
