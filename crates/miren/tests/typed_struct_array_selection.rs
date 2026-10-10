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
            "miren-typed-struct-array-selection-{}-{id}",
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
        .join("../../tests/fixtures/typed_struct_array_selection.rs")
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
        if matches!(*name, "incoming_composite" | "mutation_claim") {
            assert!(proof.models.iter().any(|model| model.contains(concat!(
                "readonly composite slice; exact compiler shape ",
                "and independent primitive leaf arrays"
            ))));
        }
        if matches!(*name, "full_contains" | "full_equality") {
            let model = if *name == "full_contains" {
                "full-domain pure composite slice membership"
            } else {
                "full-domain pure composite slice equality"
            };
            assert!(proof.models.iter().any(|observed| observed.contains(model)));
        }
        if *expected == ProofStatus::Unknown {
            let (category, reason) = match *name {
                "ambiguous_reference"
                | "raw_record"
                | "refined_zero_array"
                | "analyzer_only::untyped_retained" => (
                    UnknownCategory::Unclassified,
                    "non-scalar array index is not uniquely determined on this path",
                ),
                "dropped_record" => (
                    UnknownCategory::Unclassified,
                    "static views require sized layouts",
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
        if *name == "dropped_record" {
            assert!(proof.obligations.iter().any(|obligation| {
                obligation.status == ProofStatus::Unknown
                    && obligation.unknown_category == Some(UnknownCategory::Unclassified)
                    && obligation
                        .detail
                        .contains("static views require sized layouts")
                    && obligation
                        .call_chain
                        .iter()
                        .any(|call| call == "core::ptr::drop_glue")
            }));
        }
        let helper = match *name {
            "mutation_claim" => Some("selected_field"),
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
fn typed_array_selection_preserves_nominal_fields_and_correlations() {
    let entries = [
        ("named_array", ProofStatus::Proved),
        ("tuple_array", ProofStatus::Proved),
        ("generic_array", ProofStatus::Proved),
        ("nested_array", ProofStatus::Proved),
        ("incoming_composite", ProofStatus::Proved),
        ("owned_copy_mutation", ProofStatus::Proved),
        ("float_char_choices", ProofStatus::Proved),
        ("nominal_zero", ProofStatus::Proved),
        ("owned_nominal_zero", ProofStatus::Proved),
        ("mutation_claim", ProofStatus::Proved),
        ("singleton_reference", ProofStatus::Proved),
        ("uniquely_guarded_reference", ProofStatus::Proved),
        ("wrong_field", ProofStatus::Refuted),
        ("wrong_candidate", ProofStatus::Refuted),
        ("bounds_at_end", ProofStatus::Refuted),
        ("ambiguous_reference", ProofStatus::Unknown),
        ("ambiguous_store", ProofStatus::Proved),
        ("raw_record", ProofStatus::Unknown),
        ("refined_zero_array", ProofStatus::Unknown),
        ("dropped_record", ProofStatus::Unknown),
        ("byte_choices", ProofStatus::Proved),
        ("oversized_shape", ProofStatus::Unknown),
        ("full_contains", ProofStatus::Proved),
        ("full_equality", ProofStatus::Proved),
        ("analyzer_only::missing_body", ProofStatus::Unknown),
        ("analyzer_only::untyped_retained", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn actual_typed_selection_field_mutation_refutes_and_fails_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "    values[outer][inner].left";
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(
        &mutated,
        source.replace(original, "    values[outer][inner].right"),
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
