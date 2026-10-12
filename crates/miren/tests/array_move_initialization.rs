#![forbid(unsafe_code)]

use miren::{ProofStatus, Report};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Directory(PathBuf);
impl Directory {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "miren-array-moves-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/array_move_initialization.rs")
}
fn verify(path: &Path, target: Option<&str>, level: &str, mutant: bool) {
    use ProofStatus::{Proved as P, Refuted as R};
    let entries = [
        ("array_claim", if mutant { R } else { P }),
        ("array_wrong", R),
        ("nested_claim", P),
        ("nested_wrong", R),
        ("covering_array_repair", P),
    ];
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    for (entry, _) in entries {
        command.args(["--entry", entry]);
    }
    command
        .args([
            "--",
            "--crate-type=lib",
            "--edition=2024",
            "-Cpanic=abort",
            "-Coverflow-checks=yes",
        ])
        .arg(format!("-Copt-level={level}"))
        .arg(path)
        .arg("--out-dir")
        .arg(&directory.0);
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    let output = command.output().unwrap();
    assert!(!output.status.success());
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    for (name, expected) in entries {
        let proof = report
            .functions
            .iter()
            .find(|function| function.name == name)
            .unwrap()
            .proof
            .as_ref()
            .unwrap();
        assert_eq!(
            proof.status, expected,
            "{target:?}/O{level}/{name}: {:?}",
            proof.obligations
        );
        assert!(
            proof.assumptions.is_empty()
                && proof.trusted_calls.is_empty()
                && proof.entry_assumptions.is_empty()
        );
        if name != "covering_array_repair" {
            assert!(
                proof
                    .analyzed_bodies
                    .iter()
                    .any(|body| body.starts_with("unpack"))
            );
        }
        if expected == R {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|obligation| obligation.status == R
                        && obligation.query.is_some()
                        && obligation.model.is_some()
                        && obligation.abstraction_reasons.is_empty())
            );
        }
    }
}
fn native(path: &Path, name: &str, level: &str) -> bool {
    let directory = Directory::new();
    let binary = directory.0.join("native");
    let output = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"))
        .args(["--test", "--edition=2024"])
        .arg(format!("-Copt-level={level}"))
        .arg(path)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let output = Command::new(binary)
        .args(["--exact", name])
        .output()
        .unwrap();
    assert!(String::from_utf8_lossy(&output.stdout).contains("running 1 test"));
    output.status.success()
}
#[test]
fn fixed_array_destructuring_and_covering_repair_preserve_real_claims() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in ["0", "2"] {
            verify(&fixture(), target, level, false);
        }
    }
    for level in ["0", "2"] {
        for name in ["native::array", "native::nested", "native::repair"] {
            assert!(native(&fixture(), name, level));
        }
        for name in ["native::array_wrong", "native::nested_wrong"] {
            assert!(!native(&fixture(), name, level));
        }
    }
}
#[test]
fn actual_array_helper_mutation_refutes_and_fails_native() {
    let directory = Directory::new();
    let path = directory.0.join("mutant.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    assert_eq!(source.matches("    (left, right)\n").count(), 1);
    let changed = source.replacen("    (left, right)\n", "    (right, left)\n", 1);
    assert_ne!(source, changed);
    std::fs::write(&path, changed).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in ["0", "2"] {
            verify(&path, target, level, true);
        }
    }
    for level in ["0", "2"] {
        assert!(!native(&path, "native::array", level));
    }
}
