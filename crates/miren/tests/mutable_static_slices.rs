#![forbid(unsafe_code)]

use miren::{ContractConfig, ProofStatus, Report};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Directory(PathBuf);
impl Directory {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "miren-mutable-static-slices-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/mutable_static_slices.rs")
}
fn model() -> ContractConfig {
    serde_json::from_value(serde_json::json!({"schema_version":1,"functions":[{
        "function":"mutable_static_slices::boundary", "trusted":true,"no_panic":true,
        "storage_effect":"preserve_existing_ordinary_storage_and_static_validity",
        "reason":concat!("preserve live ordinary storage and initialized static allocation/type ",
            "and existing access rights; values and atomic history unverified"),
        "ensures":["result == 7"]
    }, {"function":"mutable_static_slices::opaque_boundary", "trusted":true,
        "no_panic":true,"reason":"unknown memory effects", "ensures":["result == 7"]
    }]}))
    .unwrap()
}
fn verify(
    path: &Path,
    entries: &[(&str, ProofStatus, bool)],
    config: Option<ContractConfig>,
    target: Option<&str>,
    optimized: bool,
    markers: &[&str],
    startup: bool,
) {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    let assumption = config
        .as_ref()
        .and_then(|config| config.functions[0].storage_assumption());
    if let Some(config) = config {
        let path = directory.0.join("config.json");
        std::fs::write(&path, serde_json::to_vec(&config).unwrap()).unwrap();
        command.arg("--contracts").arg(path);
    }
    if startup {
        command.arg("--startup");
    }
    for (name, _, _) in entries {
        command.args(["--entry", name]);
    }
    command
        .args([
            "--",
            "--crate-type=lib",
            "--crate-name=mutable_static_slices",
            "--edition=2024",
        ])
        .arg(path)
        .arg("--out-dir")
        .arg(&directory.0)
        .args(["-Cpanic=abort", "-Coverflow-checks=yes"]);
    for marker in markers {
        command.arg("--cfg").arg(format!("feature=\"{marker}\""));
    }
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    if optimized {
        command.arg("-Copt-level=2");
    }
    let output = command.output().unwrap();
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    for (name, expected, used) in entries {
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
            "{target:?} O2={optimized} {name}: {:?}",
            proof.obligations
        );
        let diagnostic = match *name {
            "ambiguous_index" => Some("non-scalar array index is not uniquely determined"),
            "retired_parent_before_none_is_unknown"
            | "retired_parent_before_escape_is_unknown"
            | "retired_parent_before_exhausted_next_is_unknown" => {
                Some("overlaps retired uninitialized storage")
            }
            "retired_empty_before_none_is_unknown" => Some("zero-sized static drops"),
            "oversized_array_is_unknown" => Some("128-element budget"),
            "wrong_element_is_unknown" => Some("exact whole mutable byte array"),
            "mutable_iterator_is_unknown" => Some("mutable static slice iterators remain"),
            "forged_shared_element_write_is_unknown"
            | "forged_shared_element_escape_is_unknown"
            | "forged_shared_tuple_write_is_unknown" => {
                Some("mutable handles cannot be exposed through shared storage")
            }
            "forged_shared_slice_write_is_unknown" => Some("readonly static slice"),
            "shared_reborrow_cannot_restore_mutation"
            | "shared_iterator_cannot_restore_mutation"
            | "readonly_array_cannot_unsize_mutable" => {
                Some("static borrowing requires a typed place")
            }
            "numeric_array_cannot_unsize_mutable" => Some("unsupported place projection Deref"),
            "dead_epoch_before_none_is_unknown" | "dead_empty_epoch_before_none_is_unknown" => {
                Some("static storage view invalidated")
            }
            _ => None,
        };
        if let Some(diagnostic) = diagnostic {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.detail.contains(diagnostic)),
                "{name}: {:?}",
                proof.obligations
            );
        }
        if *expected == ProofStatus::Refuted
            && matches!(
                *name,
                "selected_element_is_valid"
                    | "selected_element_can_overflow"
                    | "zero_is_not_restored"
                    | "static_store_does_not_restore_history"
            )
        {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.abstraction_reasons.iter().any(|reason| reason
                        .contains("mutable integer static reads admit arbitrary valid values"))),
                "{name}: abstract counterexample must retain read reason"
            );
        }
        if *name == "selected_element_is_valid" {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function.contains("SliceIndex")
                        && entry.function.contains("get_mut")),
                "actual core get_mut body must execute: {:?}",
                proof.body_entries
            );
        }
        let actual = proof
            .entry_assumptions
            .iter()
            .filter(|s| s.starts_with("trusted-storage:"))
            .collect::<Vec<_>>();
        if *used {
            assert_eq!(actual, vec![assumption.as_ref().unwrap()]);
        } else {
            assert!(actual.is_empty(), "{name}");
        }
        if *used {
            assert_eq!(
                proof
                    .trusted_calls
                    .iter()
                    .filter(|call| call.contract.storage_effect.is_some())
                    .count(),
                1
            );
        } else if assumption.is_some() {
            assert!(
                proof
                    .trusted_calls
                    .iter()
                    .all(|call| call.contract.storage_effect.is_none())
            );
        }
    }
}
#[test]
fn mutable_static_byte_slices_retain_exact_rights_and_parent_validity() {
    use ProofStatus::{ProvedWithAssumptions as P, Refuted as R, Unknown as U};
    let entries = [
        ("selected_element_is_valid", P, true),
        ("selected_element_can_overflow", R, true),
        ("zero_is_not_restored", R, true),
        ("outside_returns_none", P, true),
        ("outside_unwrap_panics", R, true),
        ("empty_returns_none", P, true),
        ("uniquely_guarded_index", P, true),
        ("ambiguous_index", U, true),
        ("retired_parent_before_none_is_unknown", U, true),
        ("retired_empty_before_none_is_unknown", U, true),
        ("oversized_array_is_unknown", U, true),
        ("wrong_element_is_unknown", U, true),
        ("mutable_iterator_is_unknown", U, true),
        ("shared_reborrow_reads", P, true),
        ("shared_iterator_reads", P, true),
        ("static_store_does_not_restore_history", R, true),
        ("forged_shared_element_write_is_unknown", U, true),
        ("forged_shared_element_escape_is_unknown", U, true),
        ("forged_shared_slice_write_is_unknown", U, true),
        ("legitimate_nested_shared_read", P, true),
        ("shared_reborrow_cannot_restore_mutation", U, true),
        ("shared_iterator_cannot_restore_mutation", U, true),
        ("readonly_array_cannot_unsize_mutable", U, true),
        ("numeric_array_cannot_unsize_mutable", U, true),
        ("dead_epoch_before_none_is_unknown", U, true),
        ("dead_empty_epoch_before_none_is_unknown", U, true),
        ("retired_parent_before_escape_is_unknown", U, true),
        ("retired_parent_before_exhausted_next_is_unknown", U, true),
        ("forged_shared_tuple_write_is_unknown", U, true),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &fixture(),
                &entries,
                Some(model()),
                target,
                optimized,
                &[],
                false,
            );
            verify(
                &fixture(),
                &[
                    ("selected_element_is_valid", ProofStatus::Proved, false),
                    ("outside_returns_none", ProofStatus::Proved, false),
                    ("empty_returns_none", ProofStatus::Proved, false),
                    ("selected_element_can_overflow", R, false),
                    ("forged_shared_element_write_is_unknown", U, false),
                ],
                None,
                target,
                optimized,
                &[],
                false,
            );
        }
    }
}

fn native(path: &Path) -> bool {
    let directory = Directory::new();
    let executable = directory.0.join("native");
    let output = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"))
        .args(["--test", "--edition=2024"])
        .arg(path)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    Command::new(executable)
        .args(["--exact", "native::only_pure_byte_arithmetic"])
        .output()
        .unwrap()
        .status
        .success()
}
#[test]
fn actual_byte_claim_mutation_refutes_and_fails_pure_native_execution() {
    assert!(native(&fixture()));
    let directory = Directory::new();
    let path = directory.0.join("mutation.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    assert!(source.contains("+ 1 <= 256"));
    std::fs::write(&path, source.replace("+ 1 <= 256", "+ 1 <= 255")).unwrap();
    assert!(!native(&path));
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &path,
                &[("selected_element_is_valid", ProofStatus::Refuted, true)],
                Some(model()),
                target,
                optimized,
                &[],
                false,
            );
        }
    }
}
