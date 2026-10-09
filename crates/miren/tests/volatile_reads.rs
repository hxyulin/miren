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
        let path = std::env::temp_dir().join(format!("miren-volatile-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/volatile_reads.rs")
}

fn verify(path: &Path, target: Option<&str>, optimized: bool) {
    let entries = [
        ("retains_f32_bits", ProofStatus::Proved),
        ("retains_f64_bits", ProofStatus::Proved),
        ("retains_boolean_and_integer", ProofStatus::Proved),
        ("special_float_bits", ProofStatus::Proved),
        ("wrong_float_claim", ProofStatus::Refuted),
        ("numeric_mmio_is_unknown", ProofStatus::Unknown),
        ("arbitrary_pointer_is_unknown", ProofStatus::Unknown),
        ("punned_type_is_unknown", ProofStatus::Unknown),
        ("projected_scalar_is_unknown", ProofStatus::Unknown),
        ("static_storage_is_unknown", ProofStatus::Unknown),
        ("cursor_is_unknown", ProofStatus::Unknown),
        ("dead_storage_is_unknown", ProofStatus::Unknown),
        ("uninitialized_storage_is_unknown", ProofStatus::Unknown),
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
            "--crate-name=volatile_reads",
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
fn tracked_volatile_scalars_preserve_bits_and_reject_unsupported_storage() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), target, optimized);
        }
    }
    assert!(native(&fixture(), "native::floats"));
    assert!(!native(&fixture(), "native::wrong_claim"));
}

#[test]
fn changed_float_claim_fails_both_verification_and_native_execution() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    assert!(source.contains("== 0x7fc0_1234"));
    std::fs::write(&mutated, source.replace("== 0x7fc0_1234", "== 0x7fc0_1235")).unwrap();
    assert!(!native(&mutated, "native::floats"));
    let output = Command::new(env!("CARGO_BIN_EXE_miren"))
        .args([
            "--verify",
            "--json",
            "--quiet",
            "--entry",
            "special_float_bits",
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
            .find(|f| f.name == "special_float_bits")
            .unwrap()
            .proof
            .as_ref()
            .unwrap()
            .status,
        ProofStatus::Refuted
    );
}

#[test]
fn external_effects_cannot_leave_readable_stale_scalar_storage() {
    let directory = Directory::new();
    let config = directory.0.join("contracts.json");
    std::fs::write(
        &config,
        serde_json::to_vec(&serde_json::json!({
            "schema_version": 1,
            "functions": [{"function": "volatile_reads::opaque_effect", "trusted": true,
                           "no_panic": true, "reason": "explicit invalidation regression"}]
        }))
        .unwrap(),
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_miren"))
        .args([
            "--verify",
            "--json",
            "--quiet",
            "--allow-assumptions",
            "--contracts",
        ])
        .arg(config)
        .args([
            "--entry",
            "effects_invalidate_backing",
            "--",
            "--crate-name=volatile_reads",
            "--crate-type=lib",
            "--edition=2024",
            "-Cpanic=abort",
            "-Coverflow-checks=yes",
        ])
        .arg(fixture())
        .arg("--out-dir")
        .arg(&directory.0)
        .output()
        .unwrap();
    let report: Report = serde_json::from_slice(&output.stdout).unwrap();
    assert!(!output.status.success());
    let proof = report
        .functions
        .iter()
        .find(|f| f.name == "effects_invalidate_backing")
        .unwrap()
        .proof
        .as_ref()
        .unwrap();
    assert_eq!(
        proof.status,
        ProofStatus::Unknown,
        "{:?}",
        proof.obligations
    );
    assert!(!proof.trusted_calls.is_empty());
    assert!(
        proof
            .obligations
            .iter()
            .any(|obligation| obligation.detail.contains("dead")
                || obligation.detail.contains("unavailable"))
    );
}
