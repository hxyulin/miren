#![forbid(unsafe_code)]

use miren::{ProofStatus, Report};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct Directory(PathBuf);

impl Directory {
    fn new() -> Self {
        let id = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "miren-unchecked-iterators-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/unchecked_iterators.rs")
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
        assert!(proof.trusted_calls.is_empty());
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|o| o.model.is_some()));
        }
    }
}

#[test]
fn typed_unchecked_iterators_preserve_bounds_aliases_and_writes() {
    let entries = [
        ("zipped_floats", ProofStatus::Proved),
        ("zipped_shared", ProofStatus::Proved),
        ("distinct_mutable_indices", ProofStatus::Proved),
        ("cursor_before_unchecked", ProofStatus::Proved),
        ("shared_duplicate_indices", ProofStatus::Proved),
        ("guarded_symbolic_unchecked", ProofStatus::Proved),
        ("wrong_zip_claim", ProofStatus::Refuted),
        ("unchecked_bounds_unknown", ProofStatus::Unknown),
        ("unknown_source", ProofStatus::Unknown),
        ("empty_iterator_unknown", ProofStatus::Unknown),
        ("dead_backing_unknown", ProofStatus::Unknown),
        ("dead_bytes_snapshot_unknown", ProofStatus::Unknown),
        ("similarly_named_method_executes_body", ProofStatus::Refuted),
        ("duplicate_mutable_unknown", ProofStatus::Unknown),
        ("possible_duplicate_unknown", ProofStatus::Unknown),
        (
            "ordinary_next_after_unchecked_unknown",
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
fn changing_zip_writes_breaks_the_proof_and_native_execution() {
    let source = std::fs::read_to_string(fixture()).unwrap();
    let mutation = source.replace("[1.0f32, 2.0, 3.0]", "[1.0f32, 2.0, 2.0]");
    assert_ne!(source, mutation);
    let directory = Directory::new();
    let path = directory.0.join("mutant.rs");
    std::fs::write(&path, mutation).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &path,
                &[("zipped_floats", ProofStatus::Refuted)],
                target,
                optimized,
            );
        }
    }
    assert!(native_tests(&fixture(), &directory));
    assert!(!native_tests(&path, &directory));
}

fn native_tests(path: &Path, directory: &Directory) -> bool {
    let binary = directory.0.join("native-tests");
    let output = Command::new("rustc")
        .args(["--test", "--edition=2024"])
        .arg(path)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    Command::new(binary).output().unwrap().status.success()
}
