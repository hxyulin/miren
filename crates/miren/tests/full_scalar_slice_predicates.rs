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
            "miren-full-scalar-slice-predicates-{}-{id}",
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
        .join("../../tests/fixtures/full_scalar_slice_predicates.rs")
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
        let comparison_model = match *name {
            "integer_self_equality"
            | "bool_member_and_equality"
            | "char_member_and_equality"
            | "different_scalar_views"
            | "wrong_scalar_view_equality"
            | "float32_self_equality"
            | "float64_self_equality" => Some(
                "full-domain primitive scalar slice equality; scoped universal numeric equality",
            ),
            "integer_member"
            | "float32_selected_member"
            | "float64_selected_member"
            | "float32_nan_is_absent"
            | "float64_nan_is_absent"
            | "float32_zero_signs"
            | "float64_zero_signs"
            | "derived_views"
            | "large_domain_and_empty_end"
            | "mutation_claim"
            | "unbounded_scalar_contains"
            | "false_zero_claim" => Some(concat!(
                "full-domain primitive scalar slice membership; ",
                "scoped existential numeric equality"
            )),
            "different_lengths_are_equal" => {
                Some("slice equality; length check before element comparisons")
            }
            _ => None,
        };
        if let Some(model) = comparison_model {
            assert!(
                proof.models.iter().any(|actual| actual.contains(model)),
                "missing comparison attribution for {name}: {:?}",
                proof.models
            );
        }
        if *expected == ProofStatus::Unknown {
            let (category, reason) = match *name {
                "mutable_root" => (
                    UnknownCategory::Semantics,
                    "mutable u16 roles require selected metadata-only operation",
                ),
                "competing_roots" | "open_custom_root" => (
                    UnknownCategory::Semantics,
                    "only read-only byte slices and byte arrays are modeled",
                ),
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
        if *name == "mutation_claim" {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|body| body.function == "selected_needle")
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
fn full_domain_predicates_preserve_numeric_semantics_and_sources() {
    let entries = [
        ("integer_member", ProofStatus::Proved),
        ("integer_self_equality", ProofStatus::Proved),
        ("bool_member_and_equality", ProofStatus::Proved),
        ("char_member_and_equality", ProofStatus::Proved),
        ("float32_selected_member", ProofStatus::Proved),
        ("float64_selected_member", ProofStatus::Proved),
        ("float32_nan_is_absent", ProofStatus::Proved),
        ("float64_nan_is_absent", ProofStatus::Proved),
        ("float32_zero_signs", ProofStatus::Proved),
        ("float64_zero_signs", ProofStatus::Proved),
        ("derived_views", ProofStatus::Proved),
        ("large_domain_and_empty_end", ProofStatus::Proved),
        ("finite_array_counterpart", ProofStatus::Proved),
        ("different_scalar_views", ProofStatus::Proved),
        ("mutation_claim", ProofStatus::Proved),
        ("unbounded_scalar_contains", ProofStatus::Proved),
        ("false_zero_claim", ProofStatus::Refuted),
        ("float32_self_equality", ProofStatus::Refuted),
        ("float64_self_equality", ProofStatus::Refuted),
        ("different_lengths_are_equal", ProofStatus::Refuted),
        ("wrong_scalar_view_equality", ProofStatus::Refuted),
        (
            "analyzer_only::custom_comparison_panics",
            ProofStatus::Refuted,
        ),
        ("mutable_root", ProofStatus::Unknown),
        ("competing_roots", ProofStatus::Unknown),
        ("open_custom_root", ProofStatus::Unknown),
        ("analyzer_only::missing_custom_body", ProofStatus::Unknown),
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
fn actual_needle_value_mutation_refutes_and_fails_valid_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = concat!(
        "fn selected_needle(values: &[u16], index: usize) -> u16 {\n",
        "    values[index]\n}"
    );
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(
        &mutated,
        source.replace(
            original,
            concat!(
                "fn selected_needle(values: &[u16], index: usize) -> u16 {\n",
                "    values[index].wrapping_add(1)\n}"
            ),
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
