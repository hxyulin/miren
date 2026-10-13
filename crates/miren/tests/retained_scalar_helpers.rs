#![forbid(unsafe_code)]
use miren::{ProofStatus, Report, UnknownCategory};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;
#[path = "support/table_verification.rs"]
mod table_verification;
use table_verification::{Directory, native, verify};

const INTEGER_ENTRIES: [&str; 12] = [
    "integer_u8",
    "integer_u16",
    "integer_u32",
    "integer_u64",
    "integer_u128",
    "integer_usize",
    "integer_i8",
    "integer_i16",
    "integer_i32",
    "integer_i64",
    "integer_i128",
    "integer_isize",
];
fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(name)
}
fn selected(report: &Report, entries: &[(&str, ProofStatus)]) {
    let actual = report
        .functions
        .iter()
        .filter(|f| f.proof.is_some())
        .map(|f| f.name.as_str())
        .collect::<BTreeSet<_>>();
    assert_eq!(actual, entries.iter().map(|(name, _)| *name).collect());
}
#[test]
fn primitive_helpers_execute_actual_bodies_preserving_retained_storage() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let mut entries = INTEGER_ENTRIES
                .iter()
                .map(|e| (*e, ProofStatus::Proved))
                .collect::<Vec<_>>();
            for entry in [
                "scalar",
                "product",
                "boolean",
                "character",
                "float32",
                "float64",
                "unit",
                "associated",
                "mixed",
            ] {
                entries.push((entry, ProofStatus::Proved));
            }
            entries.push(("wrong", ProofStatus::Refuted));
            entries.push(("nested_unknown", ProofStatus::Unknown));
            let report = verify(
                &fixture("retained_scalar_helpers.rs"),
                &entries,
                target,
                optimized,
                &[],
            );
            selected(&report, &entries);
            for (name, _) in entries
                .iter()
                .filter(|(_, status)| *status == ProofStatus::Proved)
            {
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == *name)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert!(proof.body_entries.iter().any(|b| b.function == *name));
                assert!(
                    proof
                        .body_entries
                        .iter()
                        .any(|b| b.function.starts_with("id_")
                            || b.function == "flip"
                            || b.function.ends_with("::flip")
                            || b.function == "choose")
                );
            }
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "nested_unknown")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.status == ProofStatus::Unknown
                        && o.unknown_category == Some(UnknownCategory::Semantics)
                        && o.detail.contains("nested scalar calls are unsupported"))
            );
        }
    }
}
#[test]
fn helper_mutation_refutes_and_native_programs_execute() {
    let source = fixture("retained_scalar_helpers.rs");
    let original = std::fs::read_to_string(&source).unwrap();
    assert_eq!(original.matches("word ^ mask").count(), 1);
    let directory = Directory::new();
    let mutant = directory.0.join("mutant.rs");
    std::fs::write(
        &mutant,
        original.replace("word ^ mask", "word ^ (mask ^ 3)"),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let entries = [
                ("scalar", ProofStatus::Refuted),
                ("product", ProofStatus::Refuted),
            ];
            let report = verify(&mutant, &entries, target, optimized, &[]);
            selected(&report, &entries);
        }
    }
    for optimized in [false, true] {
        native(&source, optimized, false);
        native(&mutant, optimized, true);
    }
}
#[test]
fn missing_scalar_helper_body_is_unknown_on_every_profile() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let directory = Directory::new();
            let library = directory
                .0
                .join("libretained_scalar_helper_dependency.rlib");
            let mut rustc = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
            rustc
                .args(["--crate-type=rlib", "--edition=2024", "-Cpanic=abort"])
                .arg(fixture("retained_scalar_helper_dependency.rs"))
                .arg("-o")
                .arg(&library);
            if let Some(target) = target {
                rustc.args(["--target", target]);
            }
            if optimized {
                rustc.arg("-Copt-level=2");
            }
            let output = rustc.output().unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            let report = verify(
                &fixture("retained_scalar_helper_missing.rs"),
                &[("missing", ProofStatus::Unknown)],
                target,
                optimized,
                &[
                    "--extern".into(),
                    format!("retained_scalar_helper_dependency={}", library.display()),
                ],
            );
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "missing")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.status == ProofStatus::Unknown
                        && o.unknown_category == Some(UnknownCategory::MissingCompilerEvidence)),
                "{:?}",
                proof.obligations
            );
        }
    }
}
#[test]
fn helper_contracts_check_real_preconditions_and_postconditions() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let directory = Directory::new();
            let contracts = directory.0.join("contracts.json");
            std::fs::write(
                &contracts,
                serde_json::to_vec(&serde_json::json!({
                    "schema_version": 1, "functions": [{
                        "function": "function_tables::guarded", "arguments": ["word"],
                        "requires": ["word < 10"], "ensures": ["result != word"],
                        "no_panic": true
                    }]
                }))
                .unwrap(),
            )
            .unwrap();
            // Contract switches precede rustc arguments, so use a dedicated real CLI call.
            let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
            command
                .args(["--verify", "--json", "--quiet", "--contracts"])
                .arg(&contracts)
                .args([
                    "--entry",
                    "contract_positive",
                    "--entry",
                    "contract_negative",
                    "--",
                    "--crate-type=lib",
                    "--crate-name=function_tables",
                    "--edition=2024",
                    "-Cpanic=abort",
                    "-Coverflow-checks=yes",
                ])
                .arg(fixture("retained_scalar_helpers.rs"))
                .arg("--out-dir")
                .arg(&directory.0);
            if let Some(target) = target {
                command.args(["--target", target]);
            }
            if optimized {
                command.arg("-Copt-level=2");
            }
            let output = command.output().unwrap();
            assert_eq!(output.status.code(), Some(1));
            let report: Report = serde_json::from_slice(&output.stdout).unwrap();
            let entries = [
                ("contract_positive", ProofStatus::Proved),
                ("contract_negative", ProofStatus::Refuted),
            ];
            selected(&report, &entries);
            for (name, status) in entries {
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == name)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert_eq!(proof.status, status, "{:?}", proof.obligations);
                assert!(proof.assumptions.is_empty() && proof.trusted_calls.is_empty());
            }
        }
    }
}
