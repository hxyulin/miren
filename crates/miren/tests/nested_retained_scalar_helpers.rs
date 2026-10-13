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
fn nested_primitive_helpers_execute_real_ancestry_and_preserve_storage() {
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
            entries.push(("finite_recursive", ProofStatus::Proved));
            for entry in [
                "nested_unknown",
                "unbounded_recursive",
                "indirect_unknown",
                "foreign_unknown",
                "owner_unknown",
                "closure_unknown",
            ] {
                entries.push((entry, ProofStatus::Unknown));
            }
            let report = verify(
                &fixture("nested_retained_scalar_helpers.rs"),
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
                if *name == "finite_recursive" {
                    // BodyEntry records distinct Instances; actual recursive visits share one.
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|entry| entry.function == "recursive")
                    );
                } else {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|entry| entry.call_chain.len() >= 3)
                    );
                }
            }
            for entry in ["nested_unknown", "unbounded_recursive"] {
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == entry)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert!(
                    proof
                        .obligations
                        .iter()
                        .any(|obligation| obligation.status == ProofStatus::Unknown
                            && obligation.unknown_category == Some(UnknownCategory::ResourceLimit))
                );
            }
        }
    }
}
#[test]
fn helper_mutation_refutes_and_native_programs_execute() {
    let source = fixture("nested_retained_scalar_helpers.rs");
    let original = std::fs::read_to_string(&source).unwrap();
    let leaf = "fn leaf(word: u16) -> u16 {\n    word ^ 1\n}";
    assert_eq!(original.matches(leaf).count(), 1);
    let directory = Directory::new();
    let mutant = directory.0.join("mutant.rs");
    std::fs::write(
        &mutant,
        original.replace(leaf, "fn leaf(word: u16) -> u16 {\n    word ^ 3\n}"),
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
                &fixture("nested_retained_scalar_missing.rs"),
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
                        "function": "function_tables::guarded_leaf", "arguments": ["word"],
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
                .arg(fixture("nested_retained_scalar_helpers.rs"))
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

#[test]
fn actual_function_pointer_trait_shim_remains_unknown() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let entries = [("shim_unknown", ProofStatus::Unknown)];
            let report = verify(
                &fixture("nested_retained_scalar_shim.rs"),
                &entries,
                target,
                optimized,
                &[],
            );
            selected(&report, &entries);
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "shim_unknown")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(proof.obligations.iter().any(|o| {
                o.unknown_category == Some(UnknownCategory::Semantics)
                    && o.detail
                        .contains("nested callee lacks a supported primitive lease")
            }));
        }
    }
}
