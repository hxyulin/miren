#![forbid(unsafe_code)]

use miren::{ProofStatus, Report, UnknownCategory};
use std::collections::BTreeSet;
use std::path::Path;
use std::process::Command;

#[test]
fn actual_fieldless_box_drop_executes_under_recorded_diagnostic_budget() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let output_directory = std::env::temp_dir().join(format!(
                "miren-effectful-box-{}-{}-{optimized}",
                std::process::id(),
                target.unwrap_or("host"),
            ));
            std::fs::create_dir_all(&output_directory).unwrap();
            for diagnostic in [false, true] {
                let entries = ["panicking", "helper_box", "implicit", "effectful"];
                let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
                command.args(["--verify", "--json", "--quiet"]);
                if diagnostic {
                    command.args(["--max-steps", "2000000"]);
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
                        "-Zmir-opt-level=0",
                    ])
                    .arg(
                        Path::new(env!("CARGO_MANIFEST_DIR"))
                            .join("../../tests/fixtures/effect_free_zst_box_drop.rs"),
                    )
                    .arg("--out-dir")
                    .arg(&output_directory);
                if optimized {
                    command.arg("-Copt-level=2");
                }
                if let Some(target) = target {
                    command.args(["--target", target]);
                }
                let output = command.output().unwrap();
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
                assert_eq!(selected.len(), entries.len());
                assert_eq!(
                    selected
                        .iter()
                        .map(|function| function.name.as_str())
                        .collect::<BTreeSet<_>>(),
                    entries.into_iter().collect()
                );
                for function in selected {
                    let proof = function.proof.as_ref().unwrap();
                    let expected = match (function.name.as_str(), diagnostic) {
                        ("implicit", _) | ("helper_box", true) => ProofStatus::Proved,
                        ("panicking", true) => ProofStatus::Refuted,
                        ("panicking" | "helper_box", false) => ProofStatus::Unknown,
                        ("effectful", _) => ProofStatus::Unknown,
                        _ => panic!("unexpected root"),
                    };
                    assert_eq!(
                        proof.status, expected,
                        "{target:?}/{optimized}/{diagnostic}/{}: {:?}",
                        function.name, proof.obligations
                    );
                    assert!(proof.assumptions.is_empty() && proof.trusted_calls.is_empty());
                    if expected == ProofStatus::Unknown {
                        let category = if function.name == "effectful" && diagnostic {
                            UnknownCategory::Semantics
                        } else {
                            UnknownCategory::ResourceLimit
                        };
                        assert!(
                            proof
                                .obligations
                                .iter()
                                .any(|obligation| obligation.unknown_category == Some(category))
                        );
                        if function.name == "effectful" && diagnostic {
                            assert!(proof.obligations.iter().any(|obligation| {
                                obligation.detail
                                    == "executable Box helper intrinsic frontier unsupported"
                            }));
                        }
                    }
                    println!(
                        concat!(
                            "EXECUTABLE_BOX target={:?} optimized={} ",
                            "diagnostic={} entry={} status={:?}"
                        ),
                        target, optimized, diagnostic, function.name, proof.status
                    );
                }
            }
            std::fs::remove_dir_all(output_directory).unwrap();
        }
    }
}
