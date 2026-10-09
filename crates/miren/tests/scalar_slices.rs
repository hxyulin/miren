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
            std::env::temp_dir().join(format!("miren-scalar-slices-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/scalar_slices.rs")
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
        if matches!(*name, "nested_subviews" | "empty_at_end") {
            assert!(proof.models.iter().any(|model| {
                model.contains("checked core readonly scalar range; retained caller allocation")
            }));
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|body| body.function == "range")
            );
        }
        if *expected == ProofStatus::Unknown {
            let (category, reason) = match *name {
                "mutable_input"
                | "raw_elements"
                | "zero_sized_elements"
                | "pattern_elements"
                | "competing_inputs" => (
                    UnknownCategory::Semantics,
                    "only read-only byte slices and byte arrays are modeled",
                ),
                "dead_handle" => (
                    UnknownCategory::Unclassified,
                    "uninitialized or unavailable local",
                ),
                "char_reinterpret" => (UnknownCategory::Unclassified, "unsupported transmute from"),
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
fn arbitrary_readonly_scalars_preserve_domains_correlations_and_extent() {
    let entries = [
        ("repeated_integer", ProofStatus::Proved),
        ("signed_integer", ProofStatus::Proved),
        ("wide_integer", ProofStatus::Proved),
        ("bool_values", ProofStatus::Proved),
        ("float32_bits", ProofStatus::Proved),
        ("float64_bits", ProofStatus::Proved),
        ("char_values", ProofStatus::Proved),
        ("extent", ProofStatus::Proved),
        ("retained_return", ProofStatus::Proved),
        ("mutation_claim", ProofStatus::Proved),
        ("nested_subviews", ProofStatus::Proved),
        ("empty_at_end", ProofStatus::Proved),
        ("first_word_zero", ProofStatus::Refuted),
        ("large_slice_wrong_claim", ProofStatus::Refuted),
        ("unguarded_index", ProofStatus::Refuted),
        ("invalid_range", ProofStatus::Refuted),
        ("float_reflexivity", ProofStatus::Refuted),
        ("mutable_input", ProofStatus::Unknown),
        ("raw_elements", ProofStatus::Unknown),
        ("zero_sized_elements", ProofStatus::Unknown),
        ("pattern_elements", ProofStatus::Unknown),
        ("competing_inputs", ProofStatus::Unknown),
        ("dead_handle", ProofStatus::Unknown),
        ("char_reinterpret", ProofStatus::Unknown),
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
    let original = "pub fn first(values: &[u16]) -> u16 {\n    values[0]\n}";
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(
        &mutated,
        source.replace(
            original,
            "pub fn first(values: &[u16]) -> u16 {\n    values[1]\n}",
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
            Some("native_mutation_guard")
        ));
    }
}
