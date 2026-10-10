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
            "miren-typed-byte-array-selection-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/typed_byte_array_selection.rs")
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
            "incoming_rows" | "mutation_claim" | "analyzer_only::untyped_retained"
        ) {
            assert!(proof.models.iter().any(|model| model.contains(concat!(
                "readonly composite slice; exact compiler shape ",
                "and independent primitive leaf arrays"
            ))));
        }
        if *expected == ProofStatus::Unknown {
            let (category, reason) = match *name {
                "reference_sibling"
                | "raw_sibling"
                | "refined_sibling"
                | "analyzer_only::local_untyped_retained" => (
                    UnknownCategory::Unclassified,
                    "non-scalar array index is not uniquely determined on this path",
                ),
                "oversized_shape" => (
                    UnknownCategory::ResourceLimit,
                    "composite slice type array exceeds the 128-element shape budget",
                ),
                "analyzer_only::missing_body" => (
                    UnknownCategory::MissingCompilerEvidence,
                    "no compiler-exported Rust definition matches the foreign symbol",
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
            "mutation_claim" => Some("selected_byte"),
            "analyzer_only::untyped_retained" => Some("analyzer_only::retained"),
            "exact_empty_bytes" | "empty_nonbyte_sibling" => Some("empty_row"),
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
fn typed_byte_choices_preserve_original_lengths_fields_and_owned_copies() {
    let entries = [
        ("local_rows", ProofStatus::Proved),
        ("incoming_rows", ProofStatus::Proved),
        ("owned_input", ProofStatus::Proved),
        ("tuple_rows", ProofStatus::Proved),
        ("struct_rows", ProofStatus::Proved),
        ("selected_copy_mutation", ProofStatus::Proved),
        ("exact_empty_bytes", ProofStatus::Proved),
        ("empty_nonbyte_sibling", ProofStatus::Proved),
        ("mutation_claim", ProofStatus::Proved),
        ("wrong_byte", ProofStatus::Refuted),
        ("independent_rows", ProofStatus::Refuted),
        ("bounds", ProofStatus::Refuted),
        ("retained_borrow", ProofStatus::Proved),
        ("ambiguous_store", ProofStatus::Proved),
        ("reference_sibling", ProofStatus::Unknown),
        ("raw_sibling", ProofStatus::Unknown),
        ("refined_sibling", ProofStatus::Unknown),
        ("oversized_shape", ProofStatus::Unknown),
        ("analyzer_only::missing_body", ProofStatus::Unknown),
        ("analyzer_only::untyped_retained", ProofStatus::Proved),
        (
            "analyzer_only::local_untyped_retained",
            ProofStatus::Unknown,
        ),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn actual_byte_position_mutation_refutes_and_fails_valid_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "    selected[0]\n}";
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(&mutated, source.replace(original, "    selected[1]\n}")).unwrap();
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
