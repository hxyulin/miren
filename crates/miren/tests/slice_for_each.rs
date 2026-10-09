#![forbid(unsafe_code)]

use miren::{ProofStatus, Report};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct Directory(PathBuf);

impl Directory {
    fn new() -> Self {
        let id = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("miren-slice-for-each-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/slice_for_each.rs")
}

fn contract_library() -> PathBuf {
    let profile = Path::new(env!("CARGO_BIN_EXE_miren")).parent().unwrap();
    let mut libraries = Vec::new();
    for entry in std::fs::read_dir(profile.join("build/miren-contracts")).unwrap() {
        let output = entry.unwrap().path().join("out");
        if !output.is_dir() {
            continue;
        }
        for file in std::fs::read_dir(output).unwrap() {
            let path = file.unwrap().path();
            if path
                .file_name()
                .unwrap()
                .to_string_lossy()
                .starts_with("libmiren_contracts-")
                && path
                    .extension()
                    .is_some_and(|ext| ext == "dylib" || ext == "so")
            {
                libraries.push((std::fs::metadata(&path).unwrap().modified().unwrap(), path));
            }
        }
    }
    libraries.sort();
    libraries.pop().unwrap().1
}

fn verify(path: &Path, names: &[&str], target: Option<&str>, optimize: &str) -> (Output, Report) {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json"]);
    for name in names {
        command.args(["--entry", name]);
    }
    command.args(["--", "--crate-type=lib", "--edition=2024"]);
    command.arg(path).arg("--out-dir").arg(&directory.0);
    command
        .arg("--extern")
        .arg(format!("miren_contracts={}", contract_library().display()));
    command.args(["-Cpanic=abort", "-Coverflow-checks=yes", "-C", optimize]);
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    let output = command.output().unwrap();
    let report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    (output, report)
}

#[test]
fn slice_for_each_executes_callbacks_and_preserves_mutable_backing_on_host_and_arm() {
    let entries = [
        ("reset_bank", ProofStatus::Proved),
        ("captured_order", ProofStatus::Proved),
        ("borrowed_cursor", ProofStatus::Proved),
        ("shared_order", ProofStatus::Proved),
        ("empty", ProofStatus::Proved),
        ("last_callback_panics", ProofStatus::Refuted),
        ("callback_overflows", ProofStatus::Refuted),
        ("wrong_effect", ProofStatus::Refuted),
        ("function_pointer", ProofStatus::Proved),
        ("unbounded", ProofStatus::Unknown),
        ("ambiguous", ProofStatus::Unknown),
        ("callback_destructor", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimize in ["opt-level=0", "opt-level=2"] {
            let names: Vec<_> = entries.iter().map(|(name, _)| *name).collect();
            let (output, report) = verify(&fixture(), &names, target, optimize);
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
                    proof.status,
                    expected,
                    "{target:?} {optimize} {name}: {:?}",
                    proof
                        .obligations
                        .iter()
                        .map(|o| (&o.status, &o.detail))
                        .collect::<Vec<_>>()
                );
                if expected == ProofStatus::Proved {
                    assert!(
                        proof
                            .models
                            .iter()
                            .any(|model| model.contains("slice iterator"))
                    );
                }
            }
        }
    }
}

fn native_test(path: &Path, directory: &Path, optimize: &str) -> Output {
    let binary = directory.join("slice-for-each-native");
    let build = Command::new("rustup")
        .args([
            "run",
            "nightly-2026-09-22",
            "rustc",
            "--edition=2024",
            "--test",
            "-C",
            optimize,
        ])
        .arg(path)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    Command::new(binary).output().unwrap()
}

#[test]
fn skipping_the_final_reset_fails_symbolic_and_native_checks() {
    let directory = Directory::new();
    let original = std::fs::read_to_string(fixture()).unwrap();
    let reset = "self.total = 0;";
    assert_eq!(original.matches(reset).count(), 1);
    let mutated = original.replace(reset, "if self.slot != 3 { self.total = 0; }");
    let path = directory.0.join("slice_for_each.rs");
    std::fs::write(&path, mutated).unwrap();
    for optimize in ["opt-level=0", "opt-level=2"] {
        let baseline = native_test(&fixture(), &directory.0, optimize);
        assert!(
            baseline.status.success(),
            "{}",
            String::from_utf8_lossy(&baseline.stdout)
        );
        let mutation = native_test(&path, &directory.0, optimize);
        assert!(!mutation.status.success());
        for target in [None, Some("thumbv7em-none-eabihf")] {
            let (output, report) = verify(&path, &["reset_bank"], target, optimize);
            assert!(!output.status.success());
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "reset_bank")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert_eq!(
                proof.status,
                ProofStatus::Refuted,
                "{target:?} {optimize}: {:?}",
                proof
                    .obligations
                    .iter()
                    .map(|o| (&o.status, &o.detail))
                    .collect::<Vec<_>>()
            );
            assert!(proof.obligations.iter().any(|o| o.model.is_some()));
        }
    }
}

#[test]
fn exhausted_consumers_validate_retained_backing_before_returning() {
    let path = fixture().with_file_name("slice_iterator_lifetimes.rs");
    let entries = [
        ("dead_empty_for_each", ProofStatus::Unknown),
        ("dead_empty_fold", ProofStatus::Unknown),
        ("dead_empty_all", ProofStatus::Unknown),
        ("dead_empty_next", ProofStatus::Unknown),
        ("live_empty_for_each", ProofStatus::Proved),
        ("live_empty_fold", ProofStatus::Proved),
        ("live_empty_all", ProofStatus::Proved),
        ("live_empty_next", ProofStatus::Proved),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimize in ["opt-level=0", "opt-level=2"] {
            let names: Vec<_> = entries.iter().map(|(name, _)| *name).collect();
            let (output, report) = verify(&path, &names, target, optimize);
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
                    proof.status,
                    expected,
                    "{target:?} {optimize} {name}: {:?}",
                    proof
                        .obligations
                        .iter()
                        .map(|o| (&o.status, &o.detail))
                        .collect::<Vec<_>>()
                );
                if expected == ProofStatus::Unknown {
                    assert!(proof.obligations.iter().any(|o| o.detail.contains("dead")));
                }
            }
        }
    }
}
