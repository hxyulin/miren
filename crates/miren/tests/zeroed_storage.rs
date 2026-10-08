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
            std::env::temp_dir().join(format!("miren-zeroed-storage-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/zeroed_storage.rs")
}

fn verify(path: &Path, names: &[&str], target: Option<&str>, optimized: bool) -> (Output, Report) {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json"]);
    for name in names {
        command.args(["--entry", name]);
    }
    command.args(["--", "--crate-type=lib", "--edition=2024"]);
    command.arg(path).arg("--out-dir").arg(&directory.0);
    command.args(["-Cpanic=abort", "-Coverflow-checks=yes"]);
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    if optimized {
        command.arg("-Copt-level=3");
    }
    let output = command.output().unwrap();
    let report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    (output, report)
}

#[test]
fn checked_zeroed_payloads_preserve_values_and_unknown_boundaries() {
    let entries = [
        ("scalar_fields", ProofStatus::Proved),
        ("large_bytes", ProofStatus::Proved),
        ("empty_types", ProofStatus::Proved),
        ("wrong_zero", ProofStatus::Refuted),
        ("zero_then_panic", ProofStatus::Refuted),
        ("invalid_reference", ProofStatus::Refuted),
        ("invalid_nonzero", ProofStatus::Refuted),
        ("invalid_pattern", ProofStatus::Refuted),
        ("same_name", ProofStatus::Refuted),
        ("unknown_pointer", ProofStatus::Unknown),
        ("unknown_uninit", ProofStatus::Unknown),
        ("unknown_maybe_uninit_constructor", ProofStatus::Unknown),
        ("unknown_union", ProofStatus::Unknown),
        ("direct_tag_enum", ProofStatus::Proved),
        ("invalid_enum", ProofStatus::Refuted),
        ("unknown_payload_enum", ProofStatus::Unknown),
        ("unknown_niche_enum", ProofStatus::Unknown),
        ("unknown_pattern", ProofStatus::Unknown),
        ("unknown_elements_budget", ProofStatus::Unknown),
        ("unknown_array_budget", ProofStatus::Unknown),
    ];
    let names: Vec<_> = entries.iter().map(|(name, _)| *name).collect();
    for (target, optimized) in [
        (None, false),
        (None, true),
        (Some("thumbv7em-none-eabihf"), false),
        (Some("thumbv7em-none-eabihf"), true),
    ] {
        let (_, report) = verify(&fixture(), &names, target, optimized);
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
                "{target:?} {optimized} {name}: {:?}",
                proof.obligations
            );
            assert!(proof.assumptions.is_empty());
            if name.starts_with("invalid_") {
                assert!(proof.obligations.iter().any(|obligation| {
                    obligation.kind == miren::ObligationKind::PanicSafety
                        && obligation.status == ProofStatus::Refuted
                        && obligation.detail.contains("zero-initialization validity")
                }));
            }
        }
    }
}

#[test]
fn initialized_value_and_payload_validity_mutations_fail() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    let mutated = source.replace("assert!(value.count == 0)", "assert!(value.count == 1)");
    assert_ne!(source, mutated);
    let path = directory.0.join("zero_mutation.rs");
    std::fs::write(&path, mutated).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let (_, report) = verify(&path, &["scalar_fields"], target, optimized);
            assert_eq!(
                report
                    .functions
                    .iter()
                    .find(|f| f.name == "scalar_fields")
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap()
                    .status,
                ProofStatus::Refuted
            );
        }
    }
    let original = "pub fn unknown_pointer() -> *const u32";
    assert!(source.contains(original));
    std::fs::write(
        &path,
        source.replace(original, "pub fn unknown_pointer() -> &'static u32"),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        let (_, report) = verify(&path, &["unknown_pointer"], target, false);
        assert_eq!(
            report
                .functions
                .iter()
                .find(|f| f.name == "unknown_pointer")
                .unwrap()
                .proof
                .as_ref()
                .unwrap()
                .status,
            ProofStatus::Refuted
        );
    }
}

#[test]
fn native_valid_payloads_confirm_zero_bits_and_mutation_failure() {
    let directory = Directory::new();
    for mutated in [false, true] {
        let source = std::fs::read_to_string(fixture()).unwrap();
        let source = if mutated {
            source.replace("assert!(value.count == 0)", "assert!(value.count == 1)")
        } else {
            source
        };
        let path = directory.0.join("zero_native.rs");
        let executable = directory.0.join("zero_native");
        std::fs::write(&path, source).unwrap();
        let output = Command::new("rustc")
            .args(["--test", "--edition=2024", "-Coverflow-checks=yes"])
            .arg(&path)
            .arg("-o")
            .arg(&executable)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let output = Command::new(&executable).output().unwrap();
        assert_eq!(
            output.status.success(),
            !mutated,
            "{}",
            String::from_utf8_lossy(&output.stdout)
        );
    }
}
