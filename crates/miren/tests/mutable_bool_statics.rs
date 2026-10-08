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
            std::env::temp_dir().join(format!("miren-mutable-bool-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/mutable_bool_statics.rs")
}

fn verify(path: &Path, target: Option<&str>, optimized: bool) {
    let entries = [
        ("valid_bool", ProofStatus::Proved),
        ("writes_valid_bool", ProofStatus::Proved),
        ("already_taken", ProofStatus::Refuted),
        ("write_does_not_establish_history", ProofStatus::Refuted),
        ("separate_reads_are_not_stable", ProofStatus::Refuted),
        ("wrong_scalar_is_unknown", ProofStatus::Unknown),
        ("wrong_declared_type_is_unknown", ProofStatus::Unknown),
        ("immutable_storage_is_unknown", ProofStatus::Unknown),
        ("readonly_write_is_unknown", ProofStatus::Unknown),
        ("numeric_address_is_unknown", ProofStatus::Unknown),
        ("valid_cell_bool", ProofStatus::Proved),
        ("cell_already_taken", ProofStatus::Refuted),
        (
            "cell_write_does_not_establish_history",
            ProofStatus::Refuted,
        ),
        ("nested_cell_already_taken", ProofStatus::Refuted),
        ("wrong_cell_scalar_is_unknown", ProofStatus::Unknown),
        ("uninitialized_bool_is_unknown", ProofStatus::Unknown),
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
            "--crate-name=mutable_bool_statics",
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
                proof.obligations.iter().any(|obligation| {
                    obligation.model.is_some()
                        && obligation
                            .abstraction_reasons
                            .iter()
                            .any(|reason| reason.contains("mutable boolean static"))
                }),
                "{name}: {:?}",
                proof.obligations
            );
        }
    }
}

#[test]
fn mutable_boolean_statics_admit_arbitrary_state_and_conservative_effects() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), target, optimized);
        }
    }
}

#[test]
fn changing_the_initializer_does_not_establish_runtime_state() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    assert!(source.contains("static mut TAKEN: bool = false;"));
    std::fs::write(
        &mutated,
        source.replace(
            "static mut TAKEN: bool = false;",
            "static mut TAKEN: bool = true;",
        ),
    )
    .unwrap();
    verify(&mutated, None, false);
}
