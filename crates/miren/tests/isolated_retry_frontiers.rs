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
            std::env::temp_dir().join(format!("miren-isolated-retry-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/isolated_retry_frontiers.rs")
}

fn verify(
    path: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    startup: bool,
) -> Report {
    verify_with_specification(path, entries, target, optimized, startup, None)
}

fn verify_with_specification(
    path: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    startup: bool,
    specification: Option<serde_json::Value>,
) -> Report {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    if startup {
        command.args(["--startup-isolated", "--allow-assumptions"]);
    }
    if let Some(specification) = &specification {
        let path = directory.0.join("contracts.json");
        std::fs::write(&path, serde_json::to_vec(specification).unwrap()).unwrap();
        command.arg("--contracts").arg(path);
    }
    for (name, _) in entries {
        command.args(["--entry", name]);
    }
    command
        .args([
            "--",
            "--crate-name=isolated_retry_frontiers",
            "--crate-type=lib",
            "--edition=2024",
        ])
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
        entries.iter().all(|(_, status)| matches!(
            status,
            ProofStatus::Proved | ProofStatus::ProvedWithAssumptions
        ))
    );
    for (name, expected) in entries {
        let proof = report
            .functions
            .iter()
            .find(|function| function.name == *name)
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
        assert_eq!(!proof.entry_assumptions.is_empty(), startup);
    }
    report
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
fn checked_returns_continue_while_unfinished_retry_paths_remain_unknown() {
    let entries = [
        ("retry_then_return", ProofStatus::Unknown),
        ("retry_then_panic", ProofStatus::Refuted),
        ("retry_then_unsupported", ProofStatus::Unknown),
        ("retry_without_return", ProofStatus::Unknown),
        ("ordinary_finite_loop", ProofStatus::ProvedWithAssumptions),
        (
            "independent_spurious_failures_can_disagree",
            ProofStatus::Refuted,
        ),
        ("retry_then_frame_escape", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&fixture(), &entries, target, optimized, true);
            for name in [
                "retry_then_return",
                "retry_then_panic",
                "retry_then_unsupported",
            ] {
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == name)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert!(
                    proof
                        .body_entries
                        .iter()
                        .any(|entry| entry.function == "reached_after_retry")
                );
                let unfinished = proof
                    .obligations
                    .iter()
                    .find(|obligation| obligation.detail.contains("weak-CAS retry frontier"))
                    .unwrap();
                assert_eq!(unfinished.status, ProofStatus::Unknown);
                assert_eq!(
                    unfinished.unknown_category,
                    Some(miren::UnknownCategory::ResourceLimit)
                );
                assert_eq!(unfinished.function, "retry_value");
                assert_eq!(unfinished.call_chain, vec![name, "retry_value"]);
            }
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "retry_without_return")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(
                !proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == "reached_after_retry")
            );
            assert!(
                !proof
                    .obligations
                    .iter()
                    .any(|obligation| obligation.detail.contains("weak-CAS retry frontier"))
            );
            verify(
                &fixture(),
                &[("ordinary_finite_loop", ProofStatus::Proved)],
                target,
                optimized,
                false,
            );
        }
    }
}

#[test]
fn retry_returns_must_satisfy_real_postconditions_before_the_caller_continues() {
    let specification = serde_json::json!({
        "schema_version": 1,
        "functions": [{"function": "isolated_retry_frontiers::retry_value",
                       "ensures": ["result == 9"]}]
    });
    for target in [None, Some("thumbv7em-none-eabihf")] {
        let report = verify_with_specification(
            &fixture(),
            &[("retry_then_return", ProofStatus::Refuted)],
            target,
            false,
            true,
            Some(specification.clone()),
        );
        let proof = report
            .functions
            .iter()
            .find(|f| f.name == "retry_then_return")
            .unwrap()
            .proof
            .as_ref()
            .unwrap();
        assert!(proof.obligations.iter().any(|obligation| obligation.kind
            == miren::ObligationKind::Postcondition
            && obligation.status == ProofStatus::Refuted));
        assert!(
            !proof
                .body_entries
                .iter()
                .any(|entry| entry.function == "reached_after_retry")
        );
    }
}

#[test]
fn changing_the_real_retry_return_value_fails_symbolic_and_native_continuations() {
    assert!(native_tests(&fixture(), &Directory::new()));
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    assert_eq!(source.matches("return 7;").count(), 1);
    let mutant = directory.0.join("mutant.rs");
    std::fs::write(&mutant, source.replace("return 7;", "return 9;")).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        verify(
            &mutant,
            &[("retry_then_return", ProofStatus::Refuted)],
            target,
            false,
            true,
        );
    }
    assert!(!native_tests(&mutant, &directory));
}
