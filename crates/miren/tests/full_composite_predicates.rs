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
            "miren-full-composite-predicates-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/full_composite_predicates.rs")
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
                "mutable_root" | "competing_roots" | "reference_zero" | "refined_zero"
                | "drop_zero" => (
                    UnknownCategory::Semantics,
                    "only read-only byte slices and byte arrays are modeled",
                ),
                "nominal_contains" | "nominal_panicking" => (
                    UnknownCategory::Semantics,
                    "whole composite slice membership is unsupported",
                ),
                "nominal_equality" => (
                    UnknownCategory::Semantics,
                    "whole composite slice equality is unsupported",
                ),
                "one_byte_membership" => (
                    UnknownCategory::Semantics,
                    "one-byte composite membership transport is unsupported",
                ),
                "mixed_finite_equality" => (
                    UnknownCategory::Semantics,
                    "mixed composite slice equality is unsupported",
                ),
                "analyzer_only::missing_body" => (
                    UnknownCategory::MissingCompilerEvidence,
                    "no compiler-exported Rust definition matches the foreign symbol",
                ),
                "lifecycle::dead_empty" => (
                    UnknownCategory::Unclassified,
                    "reference points to dead or uninitialized storage",
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
            "tuple_selected" | "tuple_absent" | "long_selected" => Some("selected_needle"),
            "finite_custom_false" => Some("<FalseEquality as core::cmp::PartialEq>::eq"),
            _ => None,
        };
        if let Some(body) = body {
            assert!(
                proof.body_entries.iter().any(|b| b.function == body),
                "{name}: {:?}",
                proof.body_entries
            );
        }
        let model = match *name {
            "tuple_selected" | "tuple_absent" | "array_selected" | "nested_selected"
            | "char_selected" | "long_selected" | "nan_absent" | "signed_zero"
            | "non_nan_selected" | "zero_contains" | "maximum_contains" => Some(concat!(
                "full-domain pure composite slice membership; ",
                "scoped existential structural numeric equality"
            )),
            "tuple_self"
            | "same_views"
            | "distinct_views"
            | "falsely_equal_views"
            | "falsely_float_self"
            | "zero_self" => Some(concat!(
                "full-domain pure composite slice equality; ",
                "scoped universal structural numeric equality"
            )),
            "falsely_equal_lengths" => {
                Some("slice equality; length check before element comparisons")
            }
            _ => None,
        };
        if let Some(model) = model {
            assert!(
                proof.models.iter().any(|observed| observed.contains(model)),
                "{name}: {:?}",
                proof.models
            );
        }
        if *name == "maximum_reachable" {
            let maximum = if target.is_some() {
                u128::from(u32::MAX)
            } else {
                usize::MAX as u128
            };
            let bits = if target.is_some() { 32 } else { usize::BITS };
            let represented = format!("(_ bv{maximum} {bits})");
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.status == ProofStatus::Refuted
                        && o.query.is_some()
                        && o.model.as_ref().is_some_and(|m| m.contains(&represented)))
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
fn full_length_composite_predicates_preserve_rust_numeric_equality() {
    let entries = [
        ("tuple_selected", ProofStatus::Proved),
        ("tuple_self", ProofStatus::Proved),
        ("array_selected", ProofStatus::Proved),
        ("nested_selected", ProofStatus::Proved),
        ("char_selected", ProofStatus::Proved),
        ("long_selected", ProofStatus::Proved),
        ("same_views", ProofStatus::Proved),
        ("distinct_views", ProofStatus::Proved),
        ("nan_absent", ProofStatus::Proved),
        ("signed_zero", ProofStatus::Proved),
        ("non_nan_selected", ProofStatus::Proved),
        ("zero_contains", ProofStatus::Proved),
        ("zero_self", ProofStatus::Proved),
        ("maximum_contains", ProofStatus::Proved),
        ("tuple_absent", ProofStatus::Refuted),
        ("falsely_equal_views", ProofStatus::Refuted),
        ("falsely_equal_lengths", ProofStatus::Refuted),
        ("falsely_float_self", ProofStatus::Refuted),
        ("maximum_reachable", ProofStatus::Refuted),
        ("finite_custom_false", ProofStatus::Refuted),
        ("mutable_root", ProofStatus::Unknown),
        ("competing_roots", ProofStatus::Unknown),
        ("reference_zero", ProofStatus::Unknown),
        ("refined_zero", ProofStatus::Unknown),
        ("drop_zero", ProofStatus::Unknown),
        ("nominal_contains", ProofStatus::Unknown),
        ("nominal_equality", ProofStatus::Unknown),
        ("nominal_panicking", ProofStatus::Unknown),
        ("analyzer_only::missing_body", ProofStatus::Unknown),
        ("lifecycle::dead_empty", ProofStatus::Unknown),
        ("one_byte_membership", ProofStatus::Unknown),
        ("mixed_finite_equality", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn actual_needle_mutation_refutes_and_fails_valid_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutation.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = concat!(
        "pub fn selected_needle(values: &[(u16, u16)], index: usize) -> (u16, u16) {\n",
        "    values[index]\n}",
    );
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(
        &mutated,
        source.replace(
            original,
            &original.replace(
                "    values[index]",
                concat!(
                    "    let selected = values[index];\n",
                    "    (selected.0, selected.1.wrapping_add(1))"
                ),
            ),
        ),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &mutated,
                &[("tuple_selected", ProofStatus::Refuted)],
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
