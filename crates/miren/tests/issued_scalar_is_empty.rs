#![forbid(unsafe_code)]
use miren::{ProofStatus, Report};
use std::path::Path;
use std::process::Command;

#[test]
fn scalar_metadata_observations_preserve_original_types_and_boundaries() {
    let source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/issued_scalar_is_empty.rs");
    let entries = [
        ("bool_empty", ProofStatus::Proved),
        ("char_empty", ProofStatus::Proved),
        ("i32_empty", ProofStatus::Proved),
        ("usize_empty", ProofStatus::Proved),
        ("u16_anchor", ProofStatus::Proved),
        ("float_excluded", ProofStatus::Unknown),
        ("boolean_helper", ProofStatus::Proved),
        ("boolean_wrong", ProofStatus::Refuted),
        ("bool_wrong", ProofStatus::Refuted),
        ("char_wrong", ProofStatus::Refuted),
        ("i32_wrong", ProofStatus::Refuted),
        ("usize_wrong", ProofStatus::Refuted),
        ("bool_partition", ProofStatus::Proved),
        ("char_partition", ProofStatus::Proved),
        ("i32_partition", ProofStatus::Proved),
        ("usize_partition", ProofStatus::Proved),
        ("i8_empty", ProofStatus::Proved),
        ("u128_empty", ProofStatus::Proved),
    ];
    let directory =
        std::env::temp_dir().join(format!("miren-stage210-disabled-{}", std::process::id(),));
    std::fs::create_dir_all(&directory).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
            command.args(["--verify", "--json", "--quiet"]);
            for (name, _) in entries {
                command.args(["--entry", name]);
            }
            command
                .args(["--", "--crate-type=lib", "--edition=2024", "-Cpanic=abort"])
                .arg(&source)
                .arg("--out-dir")
                .arg(&directory);
            if optimized {
                command.arg("-Copt-level=2");
            }
            if let Some(target) = target {
                command.args(["--target", target]);
            }
            let output = command.output().unwrap();
            let report: Report = serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
                panic!("{error}: {}", String::from_utf8_lossy(&output.stderr))
            });
            for (name, expected) in entries {
                let proof = report
                    .functions
                    .iter()
                    .find(|function| function.name == name)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert_eq!(proof.status, expected, "{name}");
                assert!(proof.entry_assumptions.is_empty());
            }
        }
    }
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn foreign_boolean_helper_requires_actual_body_after_metadata_even_when_empty() {
    let directory = std::env::temp_dir().join(format!(
        "miren-stage210-foreign-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&directory).unwrap();
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures");
    let compiler = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let output = directory.join(format!(
                    "{}-{optimized}-{retained}",
                    target.unwrap_or("host"),
                ));
                std::fs::create_dir(&output).unwrap();
                let archive = output.join("libscalar_metadata_dependency.rlib");
                let mut command = Command::new(&compiler);
                command
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=scalar_metadata_dependency",
                        "--edition=2024",
                        "-Cpanic=abort",
                    ])
                    .arg(fixtures.join("issued_scalar_metadata_dependency.rs"))
                    .arg("-o")
                    .arg(&archive)
                    .arg(if retained {
                        "-Zalways-encode-mir=yes"
                    } else {
                        "-Zalways-encode-mir=no"
                    });
                if optimized {
                    command.arg("-Copt-level=2");
                }
                if let Some(target) = target {
                    command.args(["--target", target]);
                }
                let build = command.output().unwrap();
                assert!(
                    build.status.success(),
                    "{}",
                    String::from_utf8_lossy(&build.stderr)
                );
                let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
                command.args(["--verify", "--json", "--quiet"]);
                for entry in ["foreign_bool", "foreign_char", "foreign_empty"] {
                    command.args(["--entry", entry]);
                }
                command
                    .args(["--", "--crate-type=lib", "--edition=2024", "-Cpanic=abort"])
                    .arg(fixtures.join("issued_scalar_metadata_external.rs"))
                    .arg("--extern")
                    .arg(format!("scalar_metadata_dependency={}", archive.display()))
                    .arg("--out-dir")
                    .arg(&output);
                if optimized {
                    command.arg("-Copt-level=2");
                }
                if let Some(target) = target {
                    command.args(["--target", target]);
                }
                let result = command.output().unwrap();
                let report: Report = serde_json::from_slice(&result.stdout).unwrap();
                for entry in ["foreign_bool", "foreign_char", "foreign_empty"] {
                    let proof = report
                        .functions
                        .iter()
                        .find(|f| f.name == entry)
                        .unwrap()
                        .proof
                        .as_ref()
                        .unwrap();
                    assert_eq!(
                        proof.status,
                        if retained {
                            ProofStatus::Proved
                        } else {
                            ProofStatus::Unknown
                        },
                        "{entry}"
                    );
                    if retained {
                        assert!(
                            proof
                                .body_entries
                                .iter()
                                .any(|body| body.function.contains("metadata_result"))
                        );
                    } else {
                        assert!(
                            proof
                                .obligations
                                .iter()
                                .any(|obligation| obligation.unknown_category
                                    == Some(miren::UnknownCategory::MissingCompilerEvidence))
                        );
                    }
                }
            }
        }
    }
    std::fs::remove_dir_all(directory).unwrap();
}
