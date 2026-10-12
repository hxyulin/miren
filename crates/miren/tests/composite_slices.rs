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
            "miren-composite-slices-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/composite_slices.rs")
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
        if *name == "mutable_root" {
            assert!(proof.models.iter().any(|model| {
                model.contains("mutable product metadata-only length; actual body certified")
            }));
        }
        if matches!(*expected, ProofStatus::Proved | ProofStatus::Refuted)
            && *name != "mutable_root"
        {
            assert!(proof.models.iter().any(|model| {
                model.contains(concat!(
                    "readonly composite slice; exact compiler shape ",
                    "and independent primitive leaf arrays"
                ))
            }));
        }
        if *expected == ProofStatus::Unknown {
            let (category, reason) = match *name {
                "mutable_root"
                | "competing_roots"
                | "nested_references"
                | "adt_leaf"
                | "nonzero_leaf"
                | "drop_leaf"
                | "empty_reference_array"
                | "empty_refined_array" => (
                    UnknownCategory::Semantics,
                    "only read-only byte slices and byte arrays are modeled",
                ),
                "oversized_type_array" => (
                    UnknownCategory::ResourceLimit,
                    "composite slice type array exceeds the 128-element shape budget",
                ),
                "analyzer_only::readonly_cannot_restore_mutation" => (
                    UnknownCategory::Semantics,
                    "readonly composite slice mutation is unsupported",
                ),
                "analyzer_only::missing_body" => (
                    UnknownCategory::MissingCompilerEvidence,
                    "no compiler-exported Rust definition matches the foreign symbol",
                ),
                "analyzer_only::dead_original_backing" => (
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
        let helper = match *name {
            "long_field_mutation_claim" => Some("selected_field"),
            "owned_helper_copy" => Some("copied_pair"),
            "caller_backed_borrows" => Some("selected_pair"),
            _ => None,
        };
        if let Some(helper) = helper {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|body| body.function == helper)
            );
        }
        if *name == "caller_backed_borrows" {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|body| body.function == "selected_second")
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
fn typed_composite_slices_retain_fields_views_and_caller_sources() {
    let entries = [
        ("pair_correlation", ProofStatus::Proved),
        ("owned_helper_copy", ProofStatus::Proved),
        ("owned_copy_mutation", ProofStatus::Proved),
        ("caller_backed_borrows", ProofStatus::Proved),
        ("same_index_relation", ProofStatus::Proved),
        ("nested_mixed", ProofStatus::Proved),
        ("nested_arrays", ProofStatus::Proved),
        ("pure_empty_fields", ProofStatus::Proved),
        ("float_field_bits", ProofStatus::Proved),
        ("subview_correlation", ProofStatus::Proved),
        ("long_field_mutation_claim", ProofStatus::Proved),
        ("open_aggregate_slice", ProofStatus::Refuted),
        ("wrong_field_correlation", ProofStatus::Refuted),
        ("wrong_nested_position", ProofStatus::Refuted),
        ("bounds_at_end", ProofStatus::Refuted),
        ("float_numeric_reflexivity", ProofStatus::Refuted),
        ("mutable_root", ProofStatus::Proved),
        ("competing_roots", ProofStatus::Unknown),
        ("nested_references", ProofStatus::Unknown),
        ("adt_leaf", ProofStatus::Unknown),
        ("nonzero_leaf", ProofStatus::Unknown),
        ("drop_leaf", ProofStatus::Unknown),
        ("empty_reference_array", ProofStatus::Unknown),
        ("empty_refined_array", ProofStatus::Unknown),
        ("wholly_zero_sized", ProofStatus::Proved),
        ("full_composite_contains", ProofStatus::Proved),
        ("full_composite_equality", ProofStatus::Proved),
        ("deferred_iteration", ProofStatus::Proved),
        ("oversized_type_array", ProofStatus::Unknown),
        (
            "analyzer_only::readonly_cannot_restore_mutation",
            ProofStatus::Unknown,
        ),
        ("analyzer_only::missing_body", ProofStatus::Unknown),
        ("analyzer_only::dead_original_backing", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn actual_tuple_field_mutation_refutes_and_fails_valid_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = concat!(
        "fn selected_field(values: &[(u16, u16)], index: usize) -> u16 {\n",
        "    values[index].0\n}"
    );
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(
        &mutated,
        source.replace(
            original,
            concat!(
                "fn selected_field(values: &[(u16, u16)], index: usize) -> u16 {\n",
                "    values[index].1\n}"
            ),
        ),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &mutated,
                &[("long_field_mutation_claim", ProofStatus::Refuted)],
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
