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
        let path =
            std::env::temp_dir().join(format!("miren-struct-slices-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/struct_slices.rs")
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
        if matches!(*expected, ProofStatus::Proved | ProofStatus::Refuted) {
            let expected_model = if *name == "enum_field" {
                "readonly tagged slice; legal tag and correlated latent payload columns"
            } else {
                concat!(
                    "readonly composite slice; exact compiler shape ",
                    "and independent primitive leaf arrays"
                )
            };
            assert!(
                proof
                    .models
                    .iter()
                    .any(|model| model.contains(expected_model))
            );
        }
        if matches!(*name, "layout" | "wrong_padding") {
            assert!(proof.models.iter().any(|model| {
                model.contains("compiler-sized value or slice length times compiler element size")
            }));
        }
        if *name == "layout" {
            assert!(proof.models.iter().any(|model| {
                model.contains("readonly slice alignment; exact compiler element ABI alignment")
            }));
        }
        if *name == "views_and_cursor" {
            assert!(proof.models.iter().any(|model| {
                model.contains("slice iterator; ordered elements and tracked cursor")
            }));
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
                "mutable_root" | "competing_roots" | "reference_field" | "raw_field"
                | "nonzero_field" | "core_wrapper" | "drop_field" | "packed"
                | "refined_zero_array" | "union_field" => (
                    UnknownCategory::Semantics,
                    "only read-only byte slices and byte arrays are modeled",
                ),
                "oversized_shape" => (
                    UnknownCategory::ResourceLimit,
                    "composite slice type array exceeds the 128-element shape budget",
                ),
                "analyzer_only::missing_body" => (
                    UnknownCategory::MissingCompilerEvidence,
                    "no compiler-exported Rust definition matches the foreign symbol",
                ),
                "analyzer_only::raw_source" => (
                    UnknownCategory::Unclassified,
                    if optimized {
                        "raw slice construction requires a shared compiler-typed byte slice"
                    } else {
                        "tracked raw addresses require a sized pointee"
                    },
                ),
                "analyzer_only::dead_empty" => (
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
            "mutation_claim" => Some("selected_field"),
            "returned_field" => Some("selected_reference"),
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
fn local_struct_slices_preserve_fields_layout_and_source_rights() {
    let entries = [
        ("named_correlation", ProofStatus::Proved),
        ("tuple_struct", ProofStatus::Proved),
        ("generic_struct", ProofStatus::Proved),
        ("nested_struct", ProofStatus::Proved),
        ("float_char", ProofStatus::Proved),
        ("views_and_cursor", ProofStatus::Proved),
        ("layout", ProofStatus::Proved),
        ("returned_field", ProofStatus::Proved),
        ("owned_mutation", ProofStatus::Proved),
        ("mutation_claim", ProofStatus::Proved),
        ("independent_fields", ProofStatus::Refuted),
        ("no_constructor_invariant", ProofStatus::Refuted),
        ("wrong_padding", ProofStatus::Refuted),
        ("bounds_at_end", ProofStatus::Refuted),
        ("float_reflexivity", ProofStatus::Refuted),
        ("mutable_root", ProofStatus::Unknown),
        ("competing_roots", ProofStatus::Unknown),
        ("reference_field", ProofStatus::Unknown),
        ("raw_field", ProofStatus::Unknown),
        ("nonzero_field", ProofStatus::Unknown),
        ("core_wrapper", ProofStatus::Unknown),
        ("drop_field", ProofStatus::Unknown),
        ("packed", ProofStatus::Unknown),
        ("whole_zero_struct", ProofStatus::Proved),
        ("nested_zero_struct", ProofStatus::Proved),
        ("empty_zero_struct", ProofStatus::Proved),
        ("refined_zero_array", ProofStatus::Unknown),
        ("oversized_shape", ProofStatus::Unknown),
        ("ambiguous_nested_struct", ProofStatus::Refuted),
        ("enum_field", ProofStatus::Proved),
        ("union_field", ProofStatus::Unknown),
        ("full_contains", ProofStatus::Proved),
        ("full_equality", ProofStatus::Proved),
        ("analyzer_only::missing_body", ProofStatus::Unknown),
        ("analyzer_only::raw_source", ProofStatus::Unknown),
        ("analyzer_only::dead_empty", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn actual_struct_field_mutation_refutes_and_fails_valid_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = concat!(
        "fn selected_field(values: &[Record], index: usize) -> u16 {\n",
        "    values[index].left\n}"
    );
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(
        &mutated,
        source.replace(
            original,
            concat!(
                "fn selected_field(values: &[Record], index: usize) -> u16 {\n",
                "    values[index].right\n}"
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
