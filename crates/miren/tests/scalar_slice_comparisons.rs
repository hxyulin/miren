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
            "miren-scalar-slice-comparisons-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/scalar_slice_comparisons.rs")
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
        if *expected == ProofStatus::Proved {
            assert!(proof.models.iter().any(|model| {
                model.contains("single incoming immutable Rust borrow; caller-owned live storage")
            }));
        }
        if *expected == ProofStatus::Proved {
            assert!(proof.models.iter().any(|model| {
                model.contains("bounded primitive slice membership")
                    || model.contains("bounded primitive slice equality")
                    || model.contains("slice equality; length check before element comparisons")
                    || model.contains("full-domain primitive scalar slice membership")
                    || model.contains("full-domain primitive scalar slice equality")
            }));
        }
        let full_domain = match *name {
            "unbounded_contains" => Some("full-domain primitive scalar slice membership"),
            "unbounded_equality" => Some("full-domain primitive scalar slice equality"),
            _ => None,
        };
        if let Some(model) = full_domain {
            assert!(proof.models.iter().any(|actual| actual.contains(model)));
        }
        if *expected == ProofStatus::Unknown {
            let (category, reason) = match *name {
                "analyzer_only::missing_custom_body" => (
                    UnknownCategory::MissingCompilerEvidence,
                    "no compiler-exported Rust definition matches the foreign symbol",
                ),
                "analyzer_only::dead_empty_source" | "analyzer_only::dead_mismatch_source" => (
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
                "wrong frontier for {name}: {:?}",
                proof.obligations
            );
        }
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|o| o.model.is_some()));
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
fn bounded_comparisons_preserve_numeric_semantics_and_source_validity() {
    let entries = [
        ("integer_member", ProofStatus::Proved),
        ("bool_member", ProofStatus::Proved),
        ("char_member", ProofStatus::Proved),
        ("float32_numeric", ProofStatus::Proved),
        ("float64_numeric", ProofStatus::Proved),
        ("integer_equality", ProofStatus::Proved),
        ("local_array_equality", ProofStatus::Proved),
        ("large_parent_short_views", ProofStatus::Proved),
        ("mismatch_is_not_a_scan", ProofStatus::Proved),
        ("mutation_claim", ProofStatus::Proved),
        ("wrong_membership", ProofStatus::Refuted),
        ("wrong_float_reflexivity", ProofStatus::Refuted),
        ("analyzer_only::missing_custom_body", ProofStatus::Unknown),
        ("unbounded_contains", ProofStatus::Proved),
        ("unbounded_equality", ProofStatus::Proved),
        ("analyzer_only::dead_empty_source", ProofStatus::Unknown),
        ("analyzer_only::dead_mismatch_source", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn actual_helper_index_mutation_refutes_and_fails_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "pub fn selected_needle(values: &[u16]) -> u16 {\n    values[0]\n}";
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(
        &mutated,
        source.replace(
            original,
            "pub fn selected_needle(values: &[u16]) -> u16 {\n    values[1]\n}",
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
