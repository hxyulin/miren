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
            "miren-safe-sized-layout-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/safe_sized_layout.rs")
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
        if (*expected == ProofStatus::Proved && *name != "analyzer_only::legacy_raw_size")
            || matches!(*name, "wrong_zero_alignment" | "wrong_helper")
        {
            assert!(proof.models.iter().any(|m| {
                m.contains("safe sized alignment; exact pure receiver and compiler ABI alignment")
            }));
        }
        if *expected == ProofStatus::Unknown {
            let (category, reason) = match *name {
                "trait_object" => (UnknownCategory::Semantics, "unsupported argument type dyn"),
                "analyzer_only::raw_alignment" | "analyzer_only::deprecated" => {
                    (UnknownCategory::Unclassified, "::intrinsics::align_of_val")
                }
                "analyzer_only::invalid_reference" => (
                    UnknownCategory::Unclassified,
                    "unsupported place projection Deref",
                ),
                "analyzer_only::dead_backing" => {
                    (UnknownCategory::Unclassified, "dead or uninitialized")
                }
                "wrapper" => (
                    UnknownCategory::Semantics,
                    "sized alignment requires an exact primitive or pure owned product",
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
            "mutation_claim" | "wrong_helper" => Some("measured_alignment"),
            "returned_view" => Some("returned_word"),
            "lookalike" => Some("align_of_val"),
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
fn safe_sized_layout_preserves_exact_abi_and_source_lifetimes() {
    let entries = [
        ("primitive", ProofStatus::Proved),
        ("padded", ProofStatus::Proved),
        ("aligned", ProofStatus::Proved),
        ("generic", ProofStatus::Proved),
        ("zero", ProofStatus::Proved),
        ("copied", ProofStatus::Proved),
        ("returned_view", ProofStatus::Proved),
        ("mutation_claim", ProofStatus::Proved),
        ("shared_reference", ProofStatus::Proved),
        ("wrong_padding", ProofStatus::Refuted),
        ("wrong_zero_alignment", ProofStatus::Refuted),
        ("lookalike", ProofStatus::Refuted),
        ("wrong_helper", ProofStatus::Refuted),
        ("wrapper", ProofStatus::Unknown),
        ("trait_object", ProofStatus::Unknown),
        ("analyzer_only::raw_alignment", ProofStatus::Unknown),
        ("analyzer_only::legacy_raw_size", ProofStatus::Proved),
        ("analyzer_only::invalid_reference", ProofStatus::Unknown),
        ("analyzer_only::deprecated", ProofStatus::Unknown),
        ("analyzer_only::dead_backing", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn actual_generic_metadata_helper_mutation_refutes_and_fails_valid_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutation.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original =
        "pub fn measured_alignment<T>(value: &T) -> usize {\n    core::mem::align_of_val(value)\n}";
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(
        &mutated,
        source.replace(
            original,
            concat!(
                "pub fn measured_alignment<T>(value: &T) -> usize {\n",
                "    core::mem::align_of_val(value) + 1\n}",
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
