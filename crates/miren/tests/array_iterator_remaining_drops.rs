#![forbid(unsafe_code)]

use miren::{ProofStatus, Report, UnknownCategory};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

const ENTRIES: [&str; 13] = [
    "full",
    "front",
    "back",
    "mixed",
    "exhausted",
    "empty",
    "zero",
    "wrong_remaining",
    "address_unknown",
    "nested_unknown",
    "callback_unknown",
    "from_fn_unknown",
    "map_unknown",
];
const MUTATION_ENTRIES: [&str; 5] = ["full", "front", "back", "mixed", "exhausted"];
fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/array_iterator_remaining_drops.rs")
}
fn verify(path: &Path, target: Option<&str>, level: &str, mutant: bool, default: bool) {
    let directory = std::env::temp_dir().join(format!(
        "miren-remaining-drop-{}-{}-{level}-{mutant}-{default}",
        std::process::id(),
        target.unwrap_or("host")
    ));
    std::fs::create_dir_all(&directory).unwrap();
    let entries: &[&str] = if mutant { &MUTATION_ENTRIES } else { &ENTRIES };
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    if !default {
        command.args(["--max-steps", "60000"]);
    }
    for entry in entries {
        command.args(["--entry", entry]);
    }
    command
        .args([
            "--",
            "--crate-type=lib",
            "--edition=2024",
            "-Cpanic=abort",
            "-Coverflow-checks=yes",
        ])
        .arg(format!("-Copt-level={level}"))
        .arg(path)
        .arg("--out-dir")
        .arg(&directory);
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    let output = command.output().unwrap();
    std::fs::remove_dir_all(&directory).unwrap();
    assert_eq!(output.status.code(), Some(1));
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    let selected = report
        .functions
        .iter()
        .filter(|function| function.proof.is_some())
        .collect::<Vec<_>>();
    assert_eq!(selected.len(), entries.len());
    assert_eq!(
        selected
            .iter()
            .map(|function| function.name.as_str())
            .collect::<BTreeSet<_>>(),
        entries.iter().copied().collect::<BTreeSet<_>>()
    );
    for function in selected {
        let proof = function.proof.as_ref().unwrap();
        let expected = if default {
            ProofStatus::Unknown
        } else if mutant {
            ProofStatus::Refuted
        } else {
            match function.name.as_str() {
                "wrong_remaining" => ProofStatus::Refuted,
                "address_unknown" | "nested_unknown" | "callback_unknown" | "from_fn_unknown"
                | "map_unknown" => ProofStatus::Unknown,
                "full" | "front" | "back" | "mixed" | "exhausted" | "empty" | "zero" => {
                    ProofStatus::Proved
                }
                _ => panic!("unexpected selected root"),
            }
        };
        assert_eq!(
            proof.status, expected,
            "{target:?}/O{level}/{}: {:?}",
            function.name, proof.obligations
        );
        assert!(
            proof.assumptions.is_empty()
                && proof.entry_assumptions.is_empty()
                && proof.trusted_calls.is_empty()
        );
        if expected == ProofStatus::Unknown {
            let reason = if default {
                "IntoIter shared execution step limit reached"
            } else if function.name == "address_unknown" {
                "IntoIter child Drop physical address operations remain unsupported"
            } else if function.name == "callback_unknown" {
                "IntoIter active Drop indirect call/early adapter remains unsupported"
            } else if matches!(function.name.as_str(), "from_fn_unknown" | "map_unknown") {
                "IntoIter Drop original signature type domain remains unsupported"
            } else {
                "IntoIter nested element Drop requires its active child lease"
            };
            let category = if default {
                UnknownCategory::ResourceLimit
            } else {
                UnknownCategory::Semantics
            };
            assert!(proof.obligations.iter().any(|obligation| obligation.status
                == ProofStatus::Unknown
                && obligation.unknown_category == Some(category)
                && obligation.detail == reason
                && obligation.query.is_none()
                && obligation.model.is_none()));
        }
        if !default && function.name == "callback_unknown" {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == "<Callback as core::ops::Drop>::drop")
            );
            assert!(
                proof
                    .body_entries
                    .iter()
                    .all(|entry| entry.function != "callback")
            );
        }
        if !default && matches!(function.name.as_str(), "from_fn_unknown" | "map_unknown") {
            let actual = if function.name == "from_fn_unknown" {
                "core::array::from_fn"
            } else {
                "core::array::<impl [T; N]>::map"
            };
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == actual)
            );
            assert!(
                proof
                    .body_entries
                    .iter()
                    .all(|entry| !entry.function.contains("closure"))
            );
        }
        if expected == ProofStatus::Refuted {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|obligation| obligation.status == ProofStatus::Refuted
                        && obligation.query.is_some()
                        && obligation.model.is_some())
            );
        }
        if !mutant && !default && function.name == "full" {
            assert_eq!(
                proof
                    .body_entries
                    .iter()
                    .filter(|entry| entry.function == "<Stamp as core::ops::Drop>::drop")
                    .count(),
                1
            );
            let actual_slice = proof
                .body_entries
                .iter()
                .any(|entry| entry.instance == "core::ptr::drop_glue [[Stamp]]");
            assert_eq!(actual_slice, target.is_none());
        }
    }
}
#[test]
fn actual_remaining_destruction_under_explicit_diagnostic_budget() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in ["0", "2"] {
            verify(&fixture(), target, level, false, false);
        }
    }
}
#[test]
fn real_destructor_effect_mutation_refutes_remaining_and_taken_elements() {
    let original = std::fs::read_to_string(fixture()).unwrap();
    let mutant = original.replace("self.0.wrapping_add(1)", "self.0.wrapping_add(2)");
    assert_ne!(original, mutant);
    let path = std::env::temp_dir().join(format!(
        "miren-remaining-drop-mutant-{}.rs",
        std::process::id()
    ));
    std::fs::write(&path, mutant).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in ["0", "2"] {
            verify(&path, target, level, true, false);
        }
    }
    std::fs::remove_file(path).unwrap();
}

#[test]
fn native_remaining_effects_follow_actual_front_back_and_ascending_order() {
    // This native reference-bearing payload is an execution control, not analyzer coverage.
    struct Trace(u16, std::rc::Rc<std::cell::RefCell<Vec<u16>>>);
    impl Drop for Trace {
        fn drop(&mut self) {
            self.0 = self.0.wrapping_add(1);
            self.1.borrow_mut().push(self.0);
        }
    }
    let effects = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
    let mut iterator = [
        Trace(11, effects.clone()),
        Trace(22, effects.clone()),
        Trace(33, effects.clone()),
        Trace(44, effects.clone()),
    ]
    .into_iter();
    drop(iterator.next().unwrap());
    drop(iterator.next_back().unwrap());
    drop(iterator);
    assert_eq!(*effects.borrow(), [12, 45, 23, 34]);
}

#[test]
fn unchanged_default_budget_records_resource_refusals_without_promotion() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in ["0", "2"] {
            verify(&fixture(), target, level, false, true);
        }
    }
}

#[test]
fn configured_effect_and_alias_summaries_refuse_before_actual_child_or_model() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in ["0", "2"] {
            for field in ["trusted", "storage_effect", "returns_alias"] {
                let directory = std::env::temp_dir().join(format!(
                    "miren-drop-summary-{}-{}-{level}-{field}",
                    std::process::id(),
                    target.unwrap_or("host")
                ));
                std::fs::create_dir_all(&directory).unwrap();
                let mut spec = serde_json::json!({
                    "function": "array_iterator_remaining_drops::<Stamp as core::ops::Drop>::drop",
                    "trusted": true, "no_panic": true, "arguments": ["value"],
                    "reason": "hostile summary control; no assumption may be adopted"
                });
                if field == "storage_effect" {
                    spec[field] = serde_json::json!("preserve_existing_ordinary_storage");
                } else if field == "returns_alias" {
                    spec[field] = serde_json::json!("value");
                }
                let config = directory.join("contracts.json");
                std::fs::write(
                    &config,
                    serde_json::to_vec(&serde_json::json!({
                        "schema_version": 1, "functions": [spec]
                    }))
                    .unwrap(),
                )
                .unwrap();
                let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
                command
                    .args([
                        "--verify",
                        "--json",
                        "--quiet",
                        "--max-steps",
                        "60000",
                        "--allow-assumptions",
                        "--entry",
                        "full",
                        "--contracts",
                    ])
                    .arg(&config)
                    .args([
                        "--",
                        "--crate-type=lib",
                        "--edition=2024",
                        "-Cpanic=abort",
                        "-Coverflow-checks=yes",
                    ])
                    .arg(format!("-Copt-level={level}"))
                    .arg(fixture())
                    .arg("--out-dir")
                    .arg(&directory);
                if let Some(target) = target {
                    command.args(["--target", target]);
                }
                let output = command.output().unwrap();
                std::fs::remove_dir_all(&directory).unwrap();
                assert_eq!(output.status.code(), Some(1));
                let report: Report =
                    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
                        panic!("{error}: {}", String::from_utf8_lossy(&output.stderr))
                    });
                let selected = report
                    .functions
                    .iter()
                    .filter(|function| function.proof.is_some())
                    .collect::<Vec<_>>();
                assert_eq!(selected.len(), 1);
                assert_eq!(selected[0].name, "full");
                let proof = selected[0].proof.as_ref().unwrap();
                assert_eq!(proof.status, ProofStatus::Unknown);
                assert!(proof.assumptions.is_empty() && proof.trusted_calls.is_empty());
                assert!(
                    proof
                        .body_entries
                        .iter()
                        .all(|entry| entry.function != "<Stamp as core::ops::Drop>::drop")
                );
                assert!(proof.obligations.iter().any(|obligation| obligation.status
                    == ProofStatus::Unknown
                    && obligation.unknown_category == Some(UnknownCategory::Semantics)
                    && obligation.detail
                        == "IntoIter active Drop summary/foreign adapter remains unsupported"
                    && obligation.query.is_none()
                    && obligation.model.is_none()));
            }
        }
    }
}
