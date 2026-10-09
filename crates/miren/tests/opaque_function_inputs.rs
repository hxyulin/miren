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
            "miren-opaque-functions-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/opaque_function_inputs.rs")
}

fn verify(path: &Path, entries: &[(&str, ProofStatus)], target: Option<&str>, optimized: bool) {
    verify_configured(path, entries, target, optimized, None);
}

fn verify_configured(
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
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|o| o.model.is_some()));
        }
    }
}

#[test]
fn unused_function_pointer_inputs_keep_their_full_domain() {
    let entries = [
        ("ignore_callback", ProofStatus::Proved),
        ("store_opaque_callback", ProofStatus::Proved),
        ("binders_unused", ProofStatus::Proved),
        ("unused_fields", ProofStatus::Proved),
        ("unsafe_signature_unused", ProofStatus::Proved),
        ("raw_waker_unused", ProofStatus::Proved),
        ("shared_waker_unused", ProofStatus::Proved),
        ("large_lazy_unused", ProofStatus::Proved),
        ("replaced_with_known_target", ProofStatus::Proved),
        ("unused_callback_does_not_hide_panic", ProofStatus::Refuted),
        ("waker_does_not_hide_panic", ProofStatus::Refuted),
        ("large_lazy_panic", ProofStatus::Refuted),
        ("invoked_callback_unknown", ProofStatus::Unknown),
        ("field_invocation_unknown", ProofStatus::Unknown),
        ("unsafe_invocation_unknown", ProofStatus::Unknown),
        ("wrong_stored_signature_unknown", ProofStatus::Unknown),
        ("unsafe_signature_change_unknown", ProofStatus::Unknown),
        ("abi_signature_change_unknown", ProofStatus::Unknown),
        ("binders_invocation_unknown", ProofStatus::Unknown),
        ("waker_effects_unknown", ProofStatus::Unknown),
        ("waker_drop_unknown", ProofStatus::Unknown),
        ("equality_unknown", ProofStatus::Unknown),
        ("address_unknown", ProofStatus::Unknown),
        ("large_lazy_invocation_unknown", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn invoking_an_unused_callback_changes_the_result_to_unknown() {
    let source = std::fs::read_to_string(fixture()).unwrap();
    let mutation = source.replacen("    let _ = callback;", "    let _ = callback(value);", 1);
    assert_ne!(source, mutation);
    let directory = Directory::new();
    let path = directory.0.join("mutant.rs");
    std::fs::write(&path, mutation).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &path,
                &[("ignore_callback", ProofStatus::Unknown)],
                target,
                optimized,
            );
        }
    }
}

#[test]
fn widening_the_guard_refutes_and_fails_native_replay() {
    let source = std::fs::read_to_string(fixture()).unwrap();
    let mutation = source.replacen("if value < 16", "if value <= 16", 1);
    assert_ne!(source, mutation);
    let directory = Directory::new();
    let path = directory.0.join("mutant.rs");
    std::fs::write(&path, mutation).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &path,
                &[("ignore_callback", ProofStatus::Refuted)],
                target,
                optimized,
            );
        }
    }
    let failing_native = std::fs::read_to_string(&path).unwrap().replace(
        "super::ignore_callback(super::low_bits, 15)",
        "super::ignore_callback(super::low_bits, 16)",
    );
    std::fs::write(&path, failing_native).unwrap();
    assert!(!native_tests(&path, &directory));
}

#[test]
fn unused_callbacks_replay_natively_without_invented_targets() {
    let directory = Directory::new();
    assert!(native_tests(&fixture(), &directory));
}

fn native_tests(path: &Path, directory: &Directory) -> bool {
    let binary = directory.0.join("native-tests");
    let output = Command::new("rustc")
        .args(["--test", "--edition=2024"])
        .arg(path)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    Command::new(binary).output().unwrap().status.success()
}

#[test]
fn shared_signature_tokens_do_not_prove_contract_identity() {
    let specification = serde_json::json!({"schema_version": 1, "functions": [{
        "function": "opaque_function_inputs::contract_identity",
        "requires": ["first == second"]
    }]});
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify_configured(
                &fixture(),
                &[("contract_identity", ProofStatus::Unknown)],
                target,
                optimized,
                Some(specification.clone()),
            );
        }
    }
}
