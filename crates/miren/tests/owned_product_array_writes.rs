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
            "miren-owned-array-product-array-writes-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/owned_product_array_writes.rs")
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
        if *name == "lazy_roots" {
            assert_eq!(
                proof
                    .inputs
                    .values()
                    .filter(|v| v.starts_with("lazy input;"))
                    .count(),
                3,
                "{name}: {:?}",
                proof.inputs,
            );
        }
        if *expected == ProofStatus::Unknown {
            let (category, reason) = match *name {
                "dynamic_twice" | "retained" | "reference_zero" | "refined_zero" | "drop_zero"
                | "core_zero" => (
                    UnknownCategory::Semantics,
                    "array write index is not uniquely determined",
                ),
                "analyzer_only::raw" => (
                    UnknownCategory::Unclassified,
                    "unsupported memory projection",
                ),
                "oversized" => (
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
            "mutation_claim" => Some("change"),
            "allocated" => Some("first"),
            "retained_alias" => Some("observe"),
            "nominal_zero" => Some("zero_effect"),
            "unit_effect" => Some("effect"),
            "panicking_effect" => Some("panic_unit"),
            "analyzer_only::call_destination" => Some("analyzer_only::replacement"),
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
fn product_roots_preserve_owned_sibling_spans() {
    let entries = [
        ("selected", ProofStatus::Proved),
        ("named", ProofStatus::Proved),
        ("nested", ProofStatus::Proved),
        ("generic", ProofStatus::Proved),
        ("sequential", ProofStatus::Proved),
        ("copied", ProofStatus::Proved),
        ("allocated", ProofStatus::Proved),
        ("retained_alias", ProofStatus::Proved),
        ("bytes", ProofStatus::Proved),
        ("float_char", ProofStatus::Proved),
        ("unit_effect", ProofStatus::Proved),
        ("nominal_zero", ProofStatus::Proved),
        ("lazy_roots", ProofStatus::Proved),
        ("mutation_claim", ProofStatus::Proved),
        ("wrong_field", ProofStatus::Refuted),
        ("wrong_row", ProofStatus::Refuted),
        ("wrong_sibling", ProofStatus::Refuted),
        ("bounds", ProofStatus::Refuted),
        ("panicking_effect", ProofStatus::Refuted),
        ("dynamic_twice", ProofStatus::Unknown),
        ("retained", ProofStatus::Unknown),
        ("reference_zero", ProofStatus::Unknown),
        ("refined_zero", ProofStatus::Unknown),
        ("drop_zero", ProofStatus::Unknown),
        ("core_zero", ProofStatus::Unknown),
        ("oversized", ProofStatus::Unknown),
        ("analyzer_only::missing_body", ProofStatus::Unknown),
        ("analyzer_only::raw", ProofStatus::Unknown),
        ("analyzer_only::call_destination", ProofStatus::Proved),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn actual_inner_assignment_mutation_refutes_and_fails_valid_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutation.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = concat!(
        "pub fn change(mut values: ([u16; 2], u16), index: usize) ",
        "-> ([u16; 2], u16) {\n    values.0[index] = 19;\n    values\n}",
    );
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(
        &mutated,
        source.replace(
            original,
            &original.replace("[index] = 19", "[index ^ 1] = 19"),
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
            Some("mutation_guard"),
        ));
    }
}
