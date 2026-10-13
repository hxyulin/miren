#![forbid(unsafe_code)]
use miren::{ProofStatus, Report};
use std::path::Path;
use std::process::Command;

#[test]
fn actual_calls_preserve_constructor_returns_across_profiles() {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/array_iterator_constructors.rs");
    let scratch =
        std::env::temp_dir().join(format!("miren-intoiter-survey-{}", std::process::id()));
    std::fs::create_dir_all(&scratch).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
            command.args(["--verify", "--json", "--quiet"]);
            for name in [
                "constructor",
                "constructor_move",
                "constructor_wrong",
                "remaining_drop_unknown",
                "next_unknown",
                "helper_argument_unknown",
            ] {
                command.args(["--entry", name]);
            }
            command
                .args([
                    "--",
                    "--crate-type=lib",
                    "--edition=2024",
                    "-Cpanic=abort",
                    "-Coverflow-checks=yes",
                ])
                .arg(&fixture)
                .arg("--out-dir")
                .arg(&scratch)
                .arg(format!("-Copt-level={level}"));
            if let Some(target) = target {
                command.args(["--target", target]);
            }
            let output = command.output().unwrap();
            let report: Report = serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
                panic!("{error}: {}", String::from_utf8_lossy(&output.stderr))
            });
            assert_eq!(output.status.code(), Some(1));
            let expected_names = [
                "constructor",
                "constructor_move",
                "constructor_wrong",
                "remaining_drop_unknown",
                "next_unknown",
                "helper_argument_unknown",
            ];
            let selected = report
                .functions
                .iter()
                .filter(|function| function.proof.is_some())
                .collect::<Vec<_>>();
            let actual_names = selected
                .iter()
                .map(|function| function.name.as_str())
                .collect::<std::collections::BTreeSet<_>>();
            assert_eq!(
                selected.len(),
                expected_names.len(),
                "selected roots or duplicates differ"
            );
            assert_eq!(actual_names, expected_names.into_iter().collect());
            for function in report
                .functions
                .iter()
                .filter(|function| function.proof.is_some())
            {
                let proof = function.proof.as_ref().unwrap();
                let expected = match function.name.as_str() {
                    "constructor" | "constructor_move" => ProofStatus::Proved,
                    "constructor_wrong" => ProofStatus::Refuted,
                    "remaining_drop_unknown" | "next_unknown" | "helper_argument_unknown" => {
                        ProofStatus::Unknown
                    }
                    name => panic!("unexpected selected function {name}"),
                };
                assert_eq!(proof.status, expected, "{}: {proof:?}", function.name);
                assert!(
                    proof.assumptions.is_empty()
                        && proof.entry_assumptions.is_empty()
                        && proof.trusted_calls.is_empty()
                );
                if expected == ProofStatus::Proved {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|entry| entry.function.contains("IntoIterator")
                                && entry.function.ends_with("into_iter"))
                    );
                }
                if expected == ProofStatus::Refuted {
                    assert!(
                        proof
                            .obligations
                            .iter()
                            .any(|obligation| obligation.status == ProofStatus::Refuted
                                && obligation.model.is_some())
                    );
                }
                if function.name == "helper_argument_unknown" {
                    assert!(proof.obligations.iter().any(|obligation| {
                        obligation
                            .detail
                            .contains("private frame-bound metadata snapshot")
                    }));
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .all(|entry| entry.function != "pass")
                    );
                }
                if expected == ProofStatus::Unknown {
                    let expected_detail = match function.name.as_str() {
                        "next_unknown" | "remaining_drop_unknown" => {
                            "owned array iterator element destructors are not modeled"
                        }
                        "helper_argument_unknown" => {
                            "IntoIter owner requires a private frame-bound metadata snapshot"
                        }
                        name => panic!("unexpected Unknown root {name}"),
                    };
                    assert!(proof.obligations.iter().any(|obligation| obligation.status
                        == ProofStatus::Unknown
                        && obligation.unknown_category == Some(miren::UnknownCategory::Semantics)
                        && obligation.detail == expected_detail));
                }
            }
        }
    }
    std::fs::remove_dir_all(scratch).unwrap();
}

#[test]
fn unavailable_constructor_wrapper_does_not_gain_a_body_or_success() {
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures");
    let scratch =
        std::env::temp_dir().join(format!("miren-intoiter-missing-{}", std::process::id()));
    std::fs::create_dir_all(&scratch).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let mut compiler = Command::new("rustc");
            compiler
                .args([
                    "--crate-type=rlib",
                    "--crate-name=array_iterator_dependency",
                    "--edition=2024",
                    "-Cpanic=abort",
                    "-Zalways-encode-mir=no",
                    "-Zmir-opt-level=0",
                ])
                .arg(fixtures.join("array_iterator_constructor_dependency.rs"))
                .arg("--out-dir")
                .arg(&scratch)
                .arg(format!("-Copt-level={level}"));
            if let Some(target) = target {
                compiler.args(["--target", target]);
            }
            let built = compiler.output().unwrap();
            assert!(
                built.status.success(),
                "{}",
                String::from_utf8_lossy(&built.stderr)
            );
            let library = scratch.join("libarray_iterator_dependency.rlib");
            let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
            command
                .args([
                    "--verify",
                    "--json",
                    "--quiet",
                    "--entry",
                    "unavailable",
                    "--",
                    "--crate-type=lib",
                    "--edition=2024",
                    "-Cpanic=abort",
                    "-Coverflow-checks=yes",
                ])
                .arg(fixtures.join("array_iterator_constructor_dependent.rs"))
                .arg("--extern")
                .arg(format!("array_iterator_dependency={}", library.display()))
                .arg("--out-dir")
                .arg(&scratch)
                .arg(format!("-Copt-level={level}"));
            if let Some(target) = target {
                command.args(["--target", target]);
            }
            let output = command.output().unwrap();
            let report: Report = serde_json::from_slice(&output.stdout).unwrap();
            assert_eq!(output.status.code(), Some(1));
            let proof = report
                .functions
                .iter()
                .find(|function| function.name == "unavailable")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert_eq!(proof.status, ProofStatus::Unknown);
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|obligation| obligation.unknown_category
                        == Some(miren::UnknownCategory::MissingCompilerEvidence))
            );
            assert!(
                proof
                    .body_entries
                    .iter()
                    .all(|entry| !entry.function.ends_with("::build"))
            );
        }
    }
    std::fs::remove_dir_all(scratch).unwrap();
}
