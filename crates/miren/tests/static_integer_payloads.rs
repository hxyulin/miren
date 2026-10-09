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
            "miren-integer-payloads-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/static_integer_payloads.rs")
}

fn verify_entries(
    path: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    startup: bool,
    extra: &[&str],
) {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    if startup {
        command.args(["--startup", "--allow-assumptions"]);
    }
    command.args(extra);
    for (name, _) in entries {
        command.args(["--entry", *name]);
    }
    command
        .args([
            "--",
            "--crate-name=static_integer_payloads",
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
        assert!(proof.assumptions.is_empty());
        assert_eq!(proof.entry_assumptions.len(), if startup { 2 } else { 0 });
        assert_eq!(proof.trusted_calls.len(), usize::from(!extra.is_empty()));
        if *expected == ProofStatus::Refuted && !startup {
            assert!(
                proof.obligations.iter().any(|obligation| {
                    obligation.model.is_some()
                        && obligation
                            .abstraction_reasons
                            .iter()
                            .any(|reason| reason.contains("mutable integer static"))
                }),
                "{name}: {:?}",
                proof.obligations
            );
        }
    }
}

#[test]
fn ordinary_integer_payloads_admit_arbitrary_runtime_values() {
    let entries = [
        ("valid_scalar", ProofStatus::Proved),
        ("whole_initializer", ProofStatus::Refuted),
        ("signed_initializer", ProofStatus::Refuted),
        ("wide_initializer", ProofStatus::Refuted),
        ("pointer_width_initializer", ProofStatus::Refuted),
        ("retained_write", ProofStatus::Refuted),
        ("separate_reads", ProofStatus::Refuted),
        ("disjoint_fields", ProofStatus::Refuted),
        ("false_claim", ProofStatus::Refuted),
        ("uninitialized", ProofStatus::Unknown),
        ("numeric_origin", ProofStatus::Unknown),
        ("wrong_type", ProofStatus::Unknown),
        ("array_origin", ProofStatus::Unknown),
        ("union_origin", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify_entries(&fixture(), &entries, target, optimized, false, &[]);
        }
    }
}

#[test]
fn explicit_startup_preserves_exact_typed_integer_histories() {
    let entries = [
        ("whole_initializer", ProofStatus::ProvedWithAssumptions),
        ("signed_initializer", ProofStatus::ProvedWithAssumptions),
        ("wide_initializer", ProofStatus::ProvedWithAssumptions),
        (
            "pointer_width_initializer",
            ProofStatus::ProvedWithAssumptions,
        ),
        ("retained_write", ProofStatus::ProvedWithAssumptions),
        ("separate_reads", ProofStatus::ProvedWithAssumptions),
        ("disjoint_fields", ProofStatus::ProvedWithAssumptions),
        ("disjoint_atomic", ProofStatus::ProvedWithAssumptions),
        ("branch_isolation", ProofStatus::ProvedWithAssumptions),
        ("false_claim", ProofStatus::Refuted),
        ("uninitialized", ProofStatus::Unknown),
        ("numeric_origin", ProofStatus::Unknown),
        ("wrong_type", ProofStatus::Unknown),
        ("array_origin", ProofStatus::Unknown),
        ("union_origin", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify_entries(&fixture(), &entries, target, optimized, true, &[]);
        }
    }
}

#[test]
fn opaque_boundaries_retire_known_unseen_and_subsequent_write_history() {
    let directory = Directory::new();
    let contracts = directory.0.join("contracts.json");
    std::fs::write(
        &contracts,
        serde_json::to_vec(&serde_json::json!({
            "schema_version": 1,
            "functions": [{ "function": "static_integer_payloads::boundary", "trusted": true,
                "no_panic": true, "modifies": [], "reason": "Explicit opaque effect boundary" }]
        }))
        .unwrap(),
    )
    .unwrap();
    let entries = [
        ("known_boundary", ProofStatus::Refuted),
        ("unseen_boundary", ProofStatus::Refuted),
        ("write_after_boundary", ProofStatus::Refuted),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify_entries(
                &fixture(),
                &entries,
                target,
                optimized,
                true,
                &["--contracts", contracts.to_str().unwrap()],
            );
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
fn initializer_mutation_refutes_the_conditional_claim_and_native_assertion() {
    let directory = Directory::new();
    assert!(native_tests(&fixture(), &directory));
    let source = std::fs::read_to_string(fixture()).unwrap();
    let mutation = source.replace("static mut WHOLE: u32 = 7;", "static mut WHOLE: u32 = 8;");
    assert_ne!(source, mutation);
    let path = directory.0.join("mutation.rs");
    std::fs::write(&path, mutation).unwrap();
    let entries = [("whole_initializer", ProofStatus::Refuted)];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify_entries(&path, &entries, target, optimized, true, &[]);
        }
    }
    assert!(!native_tests(&path, &directory));
}

#[test]
fn startup_integer_history_enforces_the_shared_location_budget() {
    let directory = Directory::new();
    let mut source = std::fs::read_to_string(fixture()).unwrap();
    for index in 0..129 {
        source.push_str(&format!("\nstatic mut SLOT_{index}: u8 = 0;\n"));
    }
    source.push_str("\npub fn within_budget() {\n");
    for index in 0..128 {
        source.push_str(&format!("write(&raw mut SLOT_{index}, 1);\n"));
    }
    source.push_str("assert!(read(&raw const SLOT_0) == 1);\n}\n");
    source
        .push_str("pub fn beyond_budget() {\nwithin_budget();\nwrite(&raw mut SLOT_128, 1);\n}\n");
    let path = directory.0.join("budget.rs");
    std::fs::write(&path, source).unwrap();
    let entries = [
        ("within_budget", ProofStatus::ProvedWithAssumptions),
        ("beyond_budget", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify_entries(&path, &entries, target, optimized, true, &[]);
        }
    }
}
