#![forbid(unsafe_code)]

use miren::{ProofStatus, Report, UnknownCategory};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

const DIAGNOSTIC_STEPS: &str = "30000";
const ENTRIES: [&str; 9] = [
    "front_drop",
    "back_drop",
    "wrong_front",
    "mixed",
    "empty",
    "zero_sized",
    "remaining_unknown",
    "mem_forget_unknown",
    "helper_transport",
];
fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/array_iterator_transfers.rs")
}
fn verify(path: &Path, target: Option<&str>, level: &str, mutant: bool) {
    let output_directory = std::env::temp_dir().join(format!(
        "miren-iterator-transfer-output-{}-{}-{level}-{mutant}",
        std::process::id(),
        target.unwrap_or("host")
    ));
    std::fs::create_dir_all(&output_directory).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args([
        "--verify",
        "--json",
        "--quiet",
        "--max-steps",
        DIAGNOSTIC_STEPS,
    ]);
    for entry in ENTRIES {
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
        .arg(&output_directory);
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    let output = command.output().unwrap();
    std::fs::remove_dir_all(output_directory).unwrap();
    assert_eq!(output.status.code(), Some(1));
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    let selected = report
        .functions
        .iter()
        .filter(|function| function.proof.is_some())
        .collect::<Vec<_>>();
    assert_eq!(selected.len(), ENTRIES.len());
    assert_eq!(
        selected
            .iter()
            .map(|function| function.name.as_str())
            .collect::<BTreeSet<_>>(),
        ENTRIES.into_iter().collect::<BTreeSet<_>>()
    );
    for function in selected {
        let proof = function.proof.as_ref().unwrap();
        let expected = match function.name.as_str() {
            "wrong_front" => ProofStatus::Refuted,
            "front_drop" | "back_drop" | "remaining_unknown" | "mem_forget_unknown"
            | "helper_transport"
                if mutant =>
            {
                ProofStatus::Refuted
            }
            "remaining_unknown" | "mem_forget_unknown" => ProofStatus::Unknown,
            "front_drop" | "back_drop" | "mixed" | "empty" | "zero_sized" | "helper_transport" => {
                ProofStatus::Proved
            }
            _ => panic!("unexpected selected root"),
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
            assert!(proof.obligations.iter().any(|obligation| obligation.status
                == ProofStatus::Unknown
                && obligation.unknown_category == Some(UnknownCategory::Semantics)
                && obligation.detail
                    == "owned array iterator element destructors are not modeled"
                && obligation.query.is_none()
                && obligation.model.is_none()));
        }
        if matches!(function.name.as_str(), "front_drop" | "back_drop") {
            assert!(
                proof
                    .analyzed_bodies
                    .iter()
                    .any(|body| body.contains("<Stamp as core::ops::Drop>"))
            );
            assert!(
                proof
                    .analyzed_bodies
                    .iter()
                    .any(|body| body.contains("PolymorphicIter"))
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
    }
}
#[test]
fn actual_transfer_and_drop_paths_under_explicit_diagnostic_budget() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in ["0", "2"] {
            verify(&fixture(), target, level, false);
        }
    }
}
#[test]
fn actual_taken_element_destructor_mutation_refutes_under_diagnostic_budget() {
    let original = std::fs::read_to_string(fixture()).unwrap();
    let mutant = original.replace("self.0.wrapping_add(1)", "self.0.wrapping_add(2)");
    assert_ne!(original, mutant);
    let path = std::env::temp_dir().join(format!(
        "miren-iterator-transfer-mutant-{}.rs",
        std::process::id()
    ));
    std::fs::write(&path, mutant).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in ["0", "2"] {
            verify(&path, target, level, true);
        }
    }
    std::fs::remove_file(path).unwrap();
}

#[test]
fn host_execution_checks_taken_and_remaining_element_destructor_mutation() {
    let directory = std::env::temp_dir().join(format!(
        "miren-iterator-transfer-host-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).unwrap();
    let original = std::fs::read_to_string(fixture()).unwrap();
    let source = original.replace("#![no_std]", "");
    let main = "\nfn main() { let _ = front_drop(); let _ = back_drop(); \
        let _ = mixed(); let _ = empty(); let _ = zero_sized(); \
        remaining_unknown(); let _ = helper_transport(); }\n";
    for mutant in [false, true] {
        let source = if mutant {
            source.replace("self.0.wrapping_add(1)", "self.0.wrapping_add(2)")
        } else {
            source.clone()
        };
        let guest = directory.join("guest.rs");
        let executable = directory.join(if mutant { "mutant" } else { "original" });
        std::fs::write(&guest, source + main).unwrap();
        let compiler = Command::new("rustc")
            .args(["--edition=2024", "-Coverflow-checks=yes"])
            .arg(&guest)
            .arg("-o")
            .arg(&executable)
            .output()
            .unwrap();
        assert!(
            compiler.status.success(),
            "{}",
            String::from_utf8_lossy(&compiler.stderr)
        );
        let execution = Command::new(&executable).output().unwrap();
        assert_eq!(execution.status.success(), !mutant);
        if mutant {
            assert!(String::from_utf8_lossy(&execution.stderr).contains("assertion failed"));
        }
    }
    std::fs::remove_dir_all(directory).unwrap();
}
