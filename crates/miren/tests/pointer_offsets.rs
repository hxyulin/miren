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
            std::env::temp_dir().join(format!("miren-pointer-offsets-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/pointer_offsets.rs")
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
        if matches!(*name, "negative_out_of_bounds" | "scaled_offset_overflow") {
            assert!(proof.obligations.iter().any(|obligation| {
                matches!(obligation.kind, miren::ObligationKind::Validity)
                    && obligation.status == ProofStatus::Refuted
            }));
            assert!(!proof.obligations.iter().any(|obligation| {
                matches!(obligation.kind, miren::ObligationKind::PanicSafety)
                    && obligation.status == ProofStatus::Refuted
            }));
        }
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|o| o.model.is_some()));
        }
    }
}

#[test]
fn bounded_offsets_preserve_provenance_on_host_and_arm() {
    let entries = [
        ("array_cursor", ProofStatus::Proved),
        ("stride_relationship", ProofStatus::Proved),
        ("scalar_one_past", ProofStatus::Proved),
        ("offset_keeps_later_panic", ProofStatus::Refuted),
        ("negative_out_of_bounds", ProofStatus::Refuted),
        ("scaled_offset_overflow", ProofStatus::Refuted),
        ("numeric_origin", ProofStatus::Unknown),
        ("unknown_reference", ProofStatus::Unknown),
        ("zero_sized_stride", ProofStatus::Unknown),
        ("one_past_read", ProofStatus::Unknown),
        ("offset_frame_escape", ProofStatus::Unknown),
        ("dead_origin", ProofStatus::Unknown),
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
fn stride_and_bound_mutations_fail() {
    assert!(native_tests(&fixture(), &Directory::new()));
    for (original, replacement, entry, native_failure) in [
        (
            "offset(start, 1)",
            "offset(start, 2)",
            "stride_relationship",
            true,
        ),
        ("index <= 4", "index <= 5", "array_cursor", false),
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
        if native_failure {
            assert!(!native_tests(&mutant, &directory));
        }
    }
}
