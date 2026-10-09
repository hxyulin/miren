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
            "miren-isolated-pointer-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/isolated_pointer_atomics.rs")
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
            "--crate-name=isolated_pointer_atomics",
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
        assert_eq!(
            proof.trusted_calls.len(),
            usize::from(specification.is_some())
        );
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
fn isolated_pointer_history_checks_success_failure_and_provenance() {
    let entries = [
        (
            "local_initializer_is_observed",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "strong_cas_updates_local_backing",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "strong_failure_keeps_old_backing",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "weak_cas_updates_only_on_success",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "static_cas_preserves_history_after_publication",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "projected_receiver_preserves_other_fields",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "actual_constructor_provenance_is_retained",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "actual_cas_replacement_provenance_is_retained",
            ProofStatus::ProvedWithAssumptions,
        ),
        ("weak_cas_may_fail_spuriously", ProofStatus::Refuted),
        (
            "local_store_updates_projected_backing",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "static_store_retains_actual_pointer_identity",
            ProofStatus::Unknown,
        ),
        (
            "static_store_retains_numeric_bits",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "local_store_retains_actual_pointer_identity",
            ProofStatus::ProvedWithAssumptions,
        ),
        ("invalid_store_ordering_panics", ProofStatus::Refuted),
        (
            "static_pointer_strong_cas_preserves_the_actual_address",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "static_pointer_cas_failure_retains_original_address",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "static_pointer_cas_does_not_claim_success_for_null_expected",
            ProofStatus::Refuted,
        ),
        (
            "weak_mixed_origins_retain_bits_and_disjoint_history",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "weak_mixed_origins_do_not_grant_pointee_provenance",
            ProofStatus::Unknown,
        ),
        (
            "numeric_address_does_not_gain_provenance",
            ProofStatus::Unknown,
        ),
        ("invalid_failure_ordering_panics", ProofStatus::Refuted),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized, true);
        }
    }
    assert!(native_tests(&fixture(), &Directory::new()));
}

#[test]
fn changing_pointer_constructor_refutes_the_claim() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    let mutant = source.replacen(
        "let link = AtomicPtr::<u8>::new(core::ptr::null_mut());",
        "let link = AtomicPtr::<u8>::new(1_usize as *mut u8);",
        1,
    );
    assert_ne!(source, mutant);
    let path = directory.0.join("mutant.rs");
    std::fs::write(&path, mutant).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &path,
                &[("local_initializer_is_observed", ProofStatus::Refuted)],
                target,
                optimized,
                true,
            );
        }
    }
    assert!(!native_tests(&path, &directory));
}

#[test]
fn default_analysis_does_not_assume_pointer_exclusivity() {
    let entries = [
        ("local_initializer_is_observed", ProofStatus::Refuted),
        ("strong_cas_updates_local_backing", ProofStatus::Refuted),
        (
            "actual_constructor_provenance_is_retained",
            ProofStatus::Refuted,
        ),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized, false);
        }
    }
}

#[test]
fn opaque_calls_cannot_revive_local_pointer_history() {
    let specification = serde_json::json!({
        "schema_version": 1,
        "functions": [{
            "function": "isolated_pointer_atomics::boundary",
            "trusted": true,
            "no_panic": true,
            "reason": "Explicit opaque effect boundary",
            "modifies": []
        }]
    });
    let entries = [
        (
            "opaque_call_discards_local_pointer_history",
            ProofStatus::Refuted,
        ),
        (
            "invalidated_store_cannot_expose_stale_constructor_through_into_inner",
            ProofStatus::Unknown,
        ),
        (
            "local_store_cannot_revive_history_after_opaque_call",
            ProofStatus::Unknown,
        ),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify_with_specification(
                &fixture(),
                &entries,
                target,
                optimized,
                true,
                Some(specification.clone()),
            );
        }
    }
}

#[test]
fn changing_cas_replacement_refutes_the_observed_update() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    let mutant = source.replacen("7_usize as *mut u8", "8_usize as *mut u8", 1);
    assert_ne!(source, mutant);
    let path = directory.0.join("mutant.rs");
    std::fs::write(&path, mutant).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &path,
                &[("strong_cas_updates_local_backing", ProofStatus::Refuted)],
                target,
                optimized,
                true,
            );
        }
    }
    assert!(!native_tests(&path, &directory));
}

#[test]
fn ordinary_cas_cannot_expose_stale_constructor_through_owned_getter() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &fixture(),
                &[(
                    "default_cas_cannot_expose_stale_constructor_through_into_inner",
                    ProofStatus::Unknown,
                )],
                target,
                optimized,
                false,
            );
        }
    }
}
