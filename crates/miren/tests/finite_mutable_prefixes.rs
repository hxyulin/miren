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
            std::env::temp_dir().join(format!("miren-finite-prefix-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/finite_mutable_prefixes.rs")
}

fn verify(path: &Path, target: Option<&str>, optimized: bool, mutated: bool) {
    let entries = [
        (
            "safe_prefix",
            if mutated {
                ProofStatus::Refuted
            } else {
                ProofStatus::Proved
            },
        ),
        ("ordered_updates", ProofStatus::Proved),
        ("empty_prefix", ProofStatus::Proved),
        ("offset_region", ProofStatus::Proved),
        ("find_predicate_effects", ProofStatus::Proved),
        ("wrong_predicate_order", ProofStatus::Refuted),
        ("shared_predicate_write_is_unknown", ProofStatus::Unknown),
        ("forged_shared_nested_write", ProofStatus::Unknown),
        ("shared_handle_escape_is_unknown", ProofStatus::Unknown),
        ("exhausted_dead_fold_is_unknown", ProofStatus::Unknown),
        ("valid_nested_mutable_reborrow", ProofStatus::Proved),
        ("valid_shared_nested_read", ProofStatus::Proved),
        ("bounds_failure", ProofStatus::Refuted),
        ("overflow_failure", ProofStatus::Refuted),
        ("wrong_late_effect", ProofStatus::Refuted),
        ("whole_view_snapshot", ProofStatus::Proved),
        ("floating_elements_are_unknown", ProofStatus::Unknown),
        ("dead_backing_is_unknown", ProofStatus::Unknown),
        ("exhausted_dead_source_is_unknown", ProofStatus::Unknown),
        ("arbitrary_slice_is_unknown", ProofStatus::Unknown),
        ("whole_view_assignment_is_unknown", ProofStatus::Unknown),
        (
            "multiple_interior_aliases_are_unknown",
            ProofStatus::Unknown,
        ),
        ("opaque_effect_is_unknown", ProofStatus::Unknown),
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
            "--crate-name=finite_mutable_prefixes",
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
fn finite_mutable_prefixes_keep_real_storage_bounds_and_callback_effects() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), target, optimized, false);
        }
    }
    assert!(native(&fixture(), "native::positive"));
    assert!(!native(&fixture(), "native::bounds_panic"));
    assert!(!native(&fixture(), "native::overflow_panic"));
    assert!(!native(&fixture(), "native::late_effect_panic"));
}

#[test]
fn first_match_mutation_is_refuted_in_the_solver_and_native_execution() {
    let directory = Directory::new();
    let path = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let mutated = source.replacen("entry.1 += 1;", "entry.1 += 2;", 1);
    assert_ne!(source, mutated);
    std::fs::write(&path, mutated).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&path, target, optimized, true);
        }
    }
    assert!(!native(&path, "native::positive"));
}
