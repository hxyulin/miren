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
            "miren-isolated-aggregate-fields-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/isolated_aggregate_fields.rs")
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
        command.args([
            if *name == "async_factory" {
                "--async-entry"
            } else {
                "--entry"
            },
            name,
        ]);
    }
    command
        .args([
            "--",
            "--crate-name=isolated_aggregate_fields",
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
        assert_eq!(
            !proof.entry_assumptions.is_empty(),
            startup && *name != "async_factory"
        );
    }
    report
}

#[test]
fn isolated_actual_parent_values_support_typed_fields_and_updates() {
    let entries = [
        ("stored_child", ProofStatus::ProvedWithAssumptions),
        (
            "identical_parent_child_footprints_are_typed_projections",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "child_update_preserves_sibling",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "nested_fields_and_tuples",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "whole_write_replaces_children",
            ProofStatus::ProvedWithAssumptions,
        ),
        ("branch_isolation", ProofStatus::ProvedWithAssumptions),
        ("old_initializer_is_refuted", ProofStatus::Refuted),
        ("wrong_field_type", ProofStatus::Unknown),
        ("numeric_pointee_remains_unknown", ProofStatus::Unknown),
        (
            "array_element_history_remains_unknown",
            ProofStatus::Unknown,
        ),
        (
            "retired_child_is_unknown",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "retired_reference_in_parent_is_unknown",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "matching_child_reinitialization_then_parent_store",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "retirement_does_not_resurrect_sibling",
            ProofStatus::Refuted,
        ),
        (
            "whole_reinitialization_after_retirement",
            ProofStatus::ProvedWithAssumptions,
        ),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized, true);
        }
    }
}

#[test]
fn ordinary_roots_do_not_retain_aggregate_write_history() {
    let entries = [
        ("stored_child", ProofStatus::Refuted),
        ("child_update_preserves_sibling", ProofStatus::Refuted),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized, false);
        }
    }
}

#[test]
fn opaque_calls_irreversibly_discard_parent_and_child_history() {
    let specification = serde_json::json!({"schema_version":1,"functions":[{
        "function":"isolated_aggregate_fields::boundary", "trusted":true,"no_panic":true,
        "modifies":[],"reason":"Explicit opaque aggregate boundary"
    }]});
    let entries = [
        ("opaque_boundary_discards_parent", ProofStatus::Refuted),
        (
            "opaque_boundary_child_write_does_not_restore_parent",
            ProofStatus::Refuted,
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
fn changing_an_actual_written_sibling_refutes_the_claim_and_native_execution() {
    let directory = Directory::new();
    assert!(native_tests(&fixture(), &directory));
    let source = std::fs::read_to_string(fixture()).unwrap();
    let needle = "write(PAIR.get(), Pair { left: 3, right: 4 });";
    assert_eq!(source.matches(needle).count(), 1);
    let mutation = source.replace(needle, "write(PAIR.get(), Pair { left: 3, right: 6 });");
    let path = directory.0.join("mutation.rs");
    std::fs::write(&path, mutation).unwrap();
    let entries = [("child_update_preserves_sibling", ProofStatus::Refuted)];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&path, &entries, target, optimized, true);
        }
    }
    assert!(!native_tests(&path, &directory));
}
