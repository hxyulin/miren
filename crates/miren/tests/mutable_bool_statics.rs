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
    verify_entries(path, &entries, target, optimized, false, &[]);
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

#[test]
fn explicit_startup_tracks_boolean_initializers_writes_and_branches() {
    let entries = [
        ("already_taken", ProofStatus::ProvedWithAssumptions),
        (
            "write_does_not_establish_history",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "separate_reads_are_not_stable",
            ProofStatus::ProvedWithAssumptions,
        ),
        ("cell_already_taken", ProofStatus::ProvedWithAssumptions),
        (
            "cell_write_does_not_establish_history",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "nested_cell_already_taken",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "independent_boolean_locations",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "independent_fields_in_one_allocation",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "boolean_and_atomic_histories_are_disjoint",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "conditional_writes_keep_branch_history",
            ProofStatus::ProvedWithAssumptions,
        ),
        ("repeated_bool_initialization", ProofStatus::Refuted),
        ("repeated_cell_initialization", ProofStatus::Refuted),
        (
            "nonboolean_write_invalidates_boolean_history",
            ProofStatus::Refuted,
        ),
        ("wrong_declared_type_is_unknown", ProofStatus::Unknown),
        ("readonly_write_is_unknown", ProofStatus::Unknown),
        ("numeric_address_is_unknown", ProofStatus::Unknown),
        ("uninitialized_bool_is_unknown", ProofStatus::Unknown),
        ("writes_valid_bool", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify_entries(&fixture(), &entries, target, optimized, true, &[]);
        }
    }
}

#[test]
fn opaque_calls_invalidate_boolean_history_without_restoring_initializers() {
    let directory = Directory::new();
    let contracts = directory.0.join("contracts.json");
    std::fs::write(
        &contracts,
        serde_json::to_vec(&serde_json::json!({
            "schema_version": 1,
            "functions": [{
                "function": "mutable_bool_statics::boundary", "trusted": true,
                "no_panic": true, "modifies": [], "reason": "Explicit opaque effect boundary"
            }]
        }))
        .unwrap(),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify_entries(
                &fixture(),
                &[
                    (
                        "boundary_invalidates_known_boolean_history",
                        ProofStatus::Refuted,
                    ),
                    (
                        "boundary_invalidates_unseen_boolean_history",
                        ProofStatus::Refuted,
                    ),
                    (
                        "writes_do_not_restore_invalidated_boolean_history",
                        ProofStatus::Refuted,
                    ),
                ],
                target,
                optimized,
                true,
                &["--contracts", contracts.to_str().unwrap()],
            );
        }
    }
}

#[test]
fn changing_the_initializer_refutes_explicit_startup_first_use() {
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "static mut TAKEN: bool = false;";
    assert!(source.contains(original));
    std::fs::write(
        &mutated,
        source.replace(original, "static mut TAKEN: bool = true;"),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify_entries(
                &mutated,
                &[("already_taken", ProofStatus::Refuted)],
                target,
                optimized,
                true,
                &[],
            );
        }
    }
}

fn native(path: &Path, entry: &str) -> bool {
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
        .args(["--exact", entry])
        .output()
        .unwrap();
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("running 1 test"),
        "{output:?}"
    );
    output.status.success()
}

#[test]
fn native_first_use_repeated_use_and_initializer_mutation_match_conditional_results() {
    assert!(native(&fixture(), "native::fresh"));
    assert!(!native(&fixture(), "native::twice"));
    assert!(native(&fixture(), "native::fresh_cell"));
    assert!(!native(&fixture(), "native::twice_cell"));
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "static mut TAKEN: bool = false;";
    assert!(source.contains(original));
    std::fs::write(
        &mutated,
        source.replace(original, "static mut TAKEN: bool = true;"),
    )
    .unwrap();
    assert!(!native(&mutated, "native::fresh"));
}
