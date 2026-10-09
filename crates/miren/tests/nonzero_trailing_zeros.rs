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
            "miren-nonzero-trailing-zeros-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/nonzero_trailing_zeros.rs")
}

fn verify(
    path: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    specification: Option<serde_json::Value>,
) {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    if let Some(specification) = specification {
        let config = directory.0.join("contracts.json");
        std::fs::write(&config, serde_json::to_vec(&specification).unwrap()).unwrap();
        command.arg("--contracts").arg(config);
    }
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
        assert!(proof.entry_assumptions.is_empty());
        if name.starts_with("safe_") {
            assert!(proof.analyzed_bodies.iter().any(|body| {
                body.starts_with("core::num::NonZero::<") && body.contains("::trailing_zeros ")
            }));
            assert!(
                proof
                    .models
                    .iter()
                    .any(|model| model.starts_with("core::intrinsics::cttz_nonzero:"))
            );
        }
        if matches!(*name, "zero_scan" | "scan_u32") {
            assert!(proof.obligations.iter().any(|o| {
                o.detail
                    .contains("cttz_nonzero requires a proven nonzero primitive operand")
            }));
        }
        if name.starts_with("lookalike_") {
            assert!(
                !proof
                    .models
                    .iter()
                    .any(|model| model.contains("cttz_nonzero"))
            );
        }
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|o| o.model.is_some()));
        }
    }
}

fn native_tests(path: &Path, directory: &Directory, optimized: bool) -> bool {
    let executable = directory.0.join("native");
    let compiler = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
    let mut command = Command::new(compiler);
    command
        .args(["--test", "--edition=2024"])
        .arg(path)
        .arg("-o")
        .arg(&executable);
    if optimized {
        command.arg("-Copt-level=2");
    }
    let output = command.output().unwrap();
    assert!(output.status.success(), "{output:?}");
    Command::new(executable).output().unwrap().status.success()
}

#[test]
fn exact_nonzero_trailing_counts_follow_core_bodies_and_refuse_zero() {
    let mut entries = Vec::new();
    entries.push(("check_u8_scan", ProofStatus::Proved));
    entries.push(("check_u16_scan", ProofStatus::Proved));
    entries.push(("check_u32_scan", ProofStatus::Proved));
    entries.push(("check_u64_scan", ProofStatus::Proved));
    entries.push(("check_u128_scan", ProofStatus::Proved));
    entries.push(("check_usize_scan", ProofStatus::Proved));
    entries.push(("check_i8_scan", ProofStatus::Proved));
    entries.push(("check_i16_scan", ProofStatus::Proved));
    entries.push(("check_i32_scan", ProofStatus::Proved));
    entries.push(("check_i64_scan", ProofStatus::Proved));
    entries.push(("check_i128_scan", ProofStatus::Proved));
    entries.push(("check_isize_scan", ProofStatus::Proved));
    entries.push(("safe_u8", ProofStatus::Proved));
    entries.push(("safe_u16", ProofStatus::Proved));
    entries.push(("safe_u32", ProofStatus::Proved));
    entries.push(("safe_u64", ProofStatus::Proved));
    entries.push(("safe_u128", ProofStatus::Proved));
    entries.push(("safe_usize", ProofStatus::Proved));
    entries.push(("safe_i32", ProofStatus::Proved));
    entries.push(("negative_value", ProofStatus::Proved));
    entries.push(("mutation_claim", ProofStatus::Proved));
    entries.push(("zero_scan", ProofStatus::Unknown));
    entries.push(("scan_u32", ProofStatus::Unknown));
    entries.push(("wrong_count", ProofStatus::Refuted));
    entries.push(("lookalike_body", ProofStatus::Proved));
    entries.push(("lookalike_wrong_claim", ProofStatus::Refuted));
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized, None);
        }
    }
}
#[test]
fn valid_native_counts_pass_and_mutated_count_fails() {
    let directory = Directory::new();
    let mutation = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    assert!(source.contains("assert!(scan_u8(8) == 3)"));
    std::fs::write(
        &mutation,
        source.replace("assert!(scan_u8(8) == 3)", "assert!(scan_u8(8) == 4)"),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &mutation,
                &[("mutation_claim", ProofStatus::Refuted)],
                target,
                optimized,
                None,
            );
        }
    }
    for optimized in [false, true] {
        assert!(native_tests(&fixture(), &Directory::new(), optimized));
        assert!(!native_tests(&mutation, &Directory::new(), optimized));
    }
}
