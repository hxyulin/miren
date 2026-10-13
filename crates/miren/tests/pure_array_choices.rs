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
            "miren-pure-array-choices-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/pure_array_choices.rs")
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
        if *name == "incoming_composite_row" {
            assert!(proof.models.iter().any(|model| model.contains(concat!(
                "readonly composite slice; exact compiler shape ",
                "and independent primitive leaf arrays"
            ))));
        }
        if *expected == ProofStatus::Unknown {
            let (category, reason) = match *name {
                "ambiguous_references" => (
                    UnknownCategory::Unclassified,
                    "non-scalar array index is not uniquely determined on this path",
                ),
                "ambiguous_drop" => (
                    UnknownCategory::Unclassified,
                    "non-scalar array index is not uniquely determined on this path",
                ),
                other => panic!("missing expected frontier for {other}"),
            };
            assert!(
                proof.obligations.iter().any(|obligation| {
                    obligation.status == ProofStatus::Unknown
                        && obligation.unknown_category == Some(category)
                        && obligation.detail.contains(reason)
                        && (*name != "ambiguous_drop"
                            || obligation.call_chain == ["ambiguous_drop"])
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
                    .any(|body| body.function == "selected_word")
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
fn pure_nested_array_choices_preserve_correlations_and_existing_rights() {
    let entries = [
        ("nested_integer_arrays", ProofStatus::Proved),
        ("incoming_array_correlation", ProofStatus::Proved),
        ("array_of_tuples", ProofStatus::Proved),
        ("tuple_containing_arrays", ProofStatus::Proved),
        ("float_and_char_choices", ProofStatus::Proved),
        ("float64_bits", ProofStatus::Proved),
        ("empty_nested_arrays", ProofStatus::Proved),
        ("singleton_reference", ProofStatus::Proved),
        ("constant_reference", ProofStatus::Proved),
        ("mutation_claim", ProofStatus::Proved),
        ("incoming_composite_row", ProofStatus::Proved),
        ("owned_selected_copy_mutation", ProofStatus::Proved),
        ("wrong_field_relation", ProofStatus::Refuted),
        ("wrong_index_relation", ProofStatus::Refuted),
        ("bounds_failure", ProofStatus::Refuted),
        ("nan_numeric_reflexivity", ProofStatus::Refuted),
        ("ambiguous_references", ProofStatus::Unknown),
        ("ambiguous_adt", ProofStatus::Proved),
        ("ambiguous_drop", ProofStatus::Unknown),
        ("byte_array_choices", ProofStatus::Proved),
        ("symbolic_mutation", ProofStatus::Proved),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn actual_inner_array_position_mutation_refutes_and_fails_valid_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = concat!(
        "fn selected_word(values: [[u16; 2]; 2], index: usize) -> u16 {\n",
        "    values[index][0]\n}"
    );
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(
        &mutated,
        source.replace(
            original,
            concat!(
                "fn selected_word(values: [[u16; 2]; 2], index: usize) -> u16 {\n",
                "    values[index][1]\n}"
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
