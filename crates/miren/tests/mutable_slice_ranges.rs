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
        let path =
            std::env::temp_dir().join(format!("miren-mutable-range-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/mutable_slice_ranges.rs")
}

fn verify(path: &Path, target: Option<&str>, optimized: bool) {
    let entries = [
        ("guarded_region", ProofStatus::Proved),
        ("guarded_borrowed_region", ProofStatus::Proved),
        ("different_abi_uses_its_actual_body", ProofStatus::Proved),
        ("nested_ranges_keep_storage", ProofStatus::Proved),
        ("empty_range_at_end", ProofStatus::Proved),
        ("out_of_bounds", ProofStatus::Refuted),
        ("reversed_bounds", ProofStatus::Refuted),
        ("wrong_write_claim", ProofStatus::Refuted),
        ("readonly_storage_is_unknown", ProofStatus::Unknown),
        ("arbitrary_raw_slice_is_unknown", ProofStatus::Unknown),
        ("nonbyte_region_is_unknown", ProofStatus::Unknown),
        ("dead_range_backing_is_unknown", ProofStatus::Unknown),
        ("lookalike_index_uses_its_actual_body", ProofStatus::Proved),
    ];
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    for (name, _) in entries {
        command.args(["--entry", name]);
    }
    command
        .args([
            "--",
            "--crate-name=mutable_slice_ranges",
            "--crate-type=lib",
            "--edition=2024",
        ])
        .arg(path)
        .arg("--out-dir")
        .arg(&directory.0)
        .args(["-Cpanic=abort", "-Coverflow-checks=yes"]);
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    if optimized {
        command.arg("-Copt-level=2");
    }
    let output = command.output().unwrap();
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    assert!(!output.status.success());
    for (name, expected) in entries {
        let proof = report
            .functions
            .iter()
            .find(|f| f.name == name)
            .unwrap()
            .proof
            .as_ref()
            .unwrap();
        assert_eq!(
            proof.status, expected,
            "{target:?} optimized={optimized} {name}: {:?}",
            proof.obligations
        );
        assert!(proof.assumptions.is_empty());
        assert!(proof.trusted_calls.is_empty());
        if matches!(
            name,
            "guarded_region"
                | "guarded_borrowed_region"
                | "nested_ranges_keep_storage"
                | "empty_range_at_end"
        ) {
            assert!(
                proof
                    .models
                    .iter()
                    .any(|model| model.contains("checked mutable byte range"))
            );
        }
        if matches!(
            name,
            "lookalike_index_uses_its_actual_body" | "different_abi_uses_its_actual_body"
        ) {
            assert!(
                proof
                    .models
                    .iter()
                    .all(|model| !model.contains("checked mutable byte range"))
            );
        }
        if expected == ProofStatus::Refuted {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|obligation| { obligation.model.is_some() })
            );
        }
    }
}

fn native(path: &Path, name: &str) -> bool {
    let directory = Directory::new();
    let executable = directory.0.join("native");
    let compiler = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
    let output = Command::new(compiler)
        .args(["--test", "--edition=2024"])
        .arg(path)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let output = Command::new(executable)
        .args(["--exact", name])
        .output()
        .unwrap();
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("running 1 test"),
        "{output:?}"
    );
    output.status.success()
}

#[test]
fn mutable_byte_ranges_preserve_nested_writes_and_real_bounds_checks() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), target, optimized);
        }
    }
    assert!(native(&fixture(), "native::positive"));
    assert!(!native(&fixture(), "native::bounds_panic"));
    assert!(!native(&fixture(), "native::reversed_panic"));
    assert!(!native(&fixture(), "native::wrong_claim_panic"));
}

#[test]
fn changed_nested_write_claim_fails_verification_and_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    assert!(source.contains("assert!(bytes[4] == 17)"));
    std::fs::write(
        &mutated,
        source.replace("assert!(bytes[4] == 17)", "assert!(bytes[4] == 18)"),
    )
    .unwrap();
    assert!(!native(&mutated, "native::positive"));
    let output = Command::new(env!("CARGO_BIN_EXE_miren"))
        .args([
            "--verify",
            "--json",
            "--quiet",
            "--entry",
            "nested_ranges_keep_storage",
            "--",
            "--crate-type=lib",
            "--edition=2024",
            "-Cpanic=abort",
            "-Coverflow-checks=yes",
        ])
        .arg(&mutated)
        .arg("--out-dir")
        .arg(&directory.0)
        .output()
        .unwrap();
    let report: Report = serde_json::from_slice(&output.stdout).unwrap();
    assert!(!output.status.success());
    assert_eq!(
        report
            .functions
            .iter()
            .find(|f| f.name == "nested_ranges_keep_storage")
            .unwrap()
            .proof
            .as_ref()
            .unwrap()
            .status,
        ProofStatus::Refuted
    );
}
