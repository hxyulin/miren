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
            std::env::temp_dir().join(format!("miren-enum-transmutes-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/enum_transmutes.rs")
}

fn verify(path: &Path, target: Option<&str>, optimized: bool) {
    let entries = [
        ("concrete", ProofStatus::Proved),
        ("symbolic", ProofStatus::Proved),
        ("sparse", ProofStatus::Proved),
        ("signed_sparse", ProofStatus::Proved),
        ("wide", ProofStatus::Proved),
        ("pointer_sized", ProofStatus::Proved),
        ("wrong_claim", ProofStatus::Refuted),
        ("excludes_negative", ProofStatus::Refuted),
        ("excludes_positive", ProofStatus::Refuted),
        ("excludes_sparse", ProofStatus::Refuted),
        ("reverse", ProofStatus::Unknown),
        ("payload", ProofStatus::Unknown),
        ("default_repr", ProofStatus::Unknown),
        ("c_repr", ProofStatus::Unknown),
        ("wrong_sign", ProofStatus::Unknown),
        ("wrong_width", ProofStatus::Unknown),
        ("singleton", ProofStatus::Proved),
        ("dropped", ProofStatus::Unknown),
        ("bool_target", ProofStatus::Unknown),
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
            "--crate-name=enum_transmutes",
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
        assert!(proof.entry_assumptions.is_empty());
        assert!(proof.trusted_calls.is_empty());
        if name == "singleton" {
            assert!(proof.models.iter().any(|model| {
                model.contains("compiler-certified fieldless enum; exact integer repr bits")
            }));
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
fn compiler_integer_repr_enums_preserve_exact_sparse_and_signed_tags() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), target, optimized);
        }
    }
    assert!(native(&fixture(), "native::positives"));
}

#[test]
fn changed_tag_claim_refutes_and_fails_native_execution() {
    let directory = Directory::new();
    let path = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    assert!(source.contains("to_bits(Pull::Up) == 1"));
    std::fs::write(
        &path,
        source.replace("to_bits(Pull::Up) == 1", "to_bits(Pull::Up) == 2"),
    )
    .unwrap();
    assert!(!native(&path, "native::positives"));
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let output = Command::new(env!("CARGO_BIN_EXE_miren"))
                .args([
                    "--verify",
                    "--json",
                    "--quiet",
                    "--entry",
                    "concrete",
                    "--",
                    "--crate-type=lib",
                    "--edition=2024",
                    "-Cpanic=abort",
                    "-Coverflow-checks=yes",
                ])
                .arg(&path)
                .arg("--out-dir")
                .arg(&directory.0)
                .args(if optimized {
                    vec!["-Copt-level=2"]
                } else {
                    vec![]
                })
                .args(
                    target
                        .map(|target| vec!["--target", target])
                        .unwrap_or_default(),
                )
                .output()
                .unwrap();
            let report: Report = serde_json::from_slice(&output.stdout).unwrap();
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "concrete")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert_eq!(
                proof.status,
                ProofStatus::Refuted,
                "{:?}",
                proof.obligations
            );
            assert!(proof.assumptions.is_empty());
            assert!(proof.entry_assumptions.is_empty());
            assert!(proof.entry_assumptions.is_empty());
        }
    }
}
