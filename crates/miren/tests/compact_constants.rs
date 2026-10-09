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
            "miren-compact-constants-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/compact_constants.rs")
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
        let boundary = match *name {
            "constant_value_budget" => Some("constant shape exceeds depth or value budget"),
            "constant_element_budget" => Some("constant array exceeds element budget"),
            "repeat_clone_budget" => Some("owned repeat exceeds the 256-value budget"),
            "repeat_element_budget" => Some("array repeat exceeds the 128-element limit"),
            "interior_repeat" => Some("repeated interior mutable storage is not modeled"),
            _ => None,
        };
        if let Some(boundary) = boundary {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| { o.status == ProofStatus::Unknown && o.detail.contains(boundary) }),
                "{name}: {:?}",
                proof.obligations
            );
        }
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|o| o.model.is_some()));
        }
    }
}

#[test]
fn compact_initialized_constants_and_repeats_on_host_and_arm() {
    let entries = [
        ("initialized_configuration_copies", ProofStatus::Proved),
        ("initialized_shared_rows", ProofStatus::Proved),
        ("lqr_default_repeat", ProofStatus::Proved),
        ("deep_repeat", ProofStatus::Proved),
        ("constant_bounds_failure", ProofStatus::Refuted),
        ("constant_value_budget", ProofStatus::Unknown),
        ("constant_element_budget", ProofStatus::Unknown),
        ("repeat_clone_budget", ProofStatus::Unknown),
        ("repeat_element_budget", ProofStatus::Unknown),
        ("interior_repeat", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

fn native_tests(path: &Path, directory: &Directory) -> bool {
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
    Command::new(executable).output().unwrap().status.success()
}

#[test]
fn changing_a_copied_constant_or_repeat_claim_fails_static_and_native_checks() {
    assert!(native_tests(&fixture(), &Directory::new()));
    for (original, replacement, entry) in [
        (
            "original.coefficients[39][5] == 239.0",
            "original.coefficients[39][5] == 240.0",
            "initialized_configuration_copies",
        ),
        (
            "gains[39][0] == 0.0",
            "gains[39][0] == 17.0",
            "lqr_default_repeat",
        ),
    ] {
        let directory = Directory::new();
        let mutant = directory.0.join("mutant.rs");
        let source = std::fs::read_to_string(fixture()).unwrap();
        assert!(source.contains(original));
        std::fs::write(&mutant, source.replacen(original, replacement, 1)).unwrap();
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for optimized in [false, true] {
                verify(&mutant, &[(entry, ProofStatus::Refuted)], target, optimized);
            }
        }
        assert!(!native_tests(&mutant, &directory));
    }
}
