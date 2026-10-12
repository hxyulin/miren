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
        ("float_excluded", ProofStatus::Proved),
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

#[test]
fn issued_float_metadata_exact_current_length_and_helper_mutation() {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/issued_scalar_is_empty.rs");
    let source = std::fs::read_to_string(&fixture).unwrap();
    let directory = table_verification_float::Directory::new();
    let mutant = directory.0.join("float-metadata-mutant.rs");
    assert_eq!(source.matches("    value\n}").count(), 1);
    std::fs::write(
        &mutant,
        source.replacen("    value\n}", "    value ^ true\n}", 1),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            table_verification_float::verify(
                &fixture,
                &[
                    ("float32_metadata", ProofStatus::Proved),
                    ("float64_metadata", ProofStatus::Proved),
                    ("float32_wrong", ProofStatus::Refuted),
                    ("float64_wrong", ProofStatus::Refuted),
                    ("float_nested_metadata", ProofStatus::Proved),
                ],
                target,
                optimized,
                &[],
            );
            let report = table_verification_float::verify(
                &mutant,
                &[
                    ("float32_metadata", ProofStatus::Refuted),
                    ("float64_metadata", ProofStatus::Refuted),
                ],
                target,
                optimized,
                &[],
            );
            for entry in ["float32_metadata", "float64_metadata"] {
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
                        .any(|o| o.status == ProofStatus::Refuted
                            && o.query.is_some()
                            && o.model.is_some())
                );
                assert!(
                    proof
                        .body_entries
                        .iter()
                        .any(|b| b.function == "metadata_boolean")
                );
            }
        }
    }
    for optimized in [false, true] {
        table_verification_float::native(&fixture, optimized, false);
        table_verification_float::native(&mutant, optimized, true);
    }
}

#[path = "support/table_verification.rs"]
mod table_verification_float;

#[test]
fn float_metadata_boolean_dependency_requires_its_actual_body() {
    let directory = table_verification_float::Directory::new();
    let dependency = directory.0.join("dependency.rs");
    let caller = directory.0.join("caller.rs");
    std::fs::write(
        &dependency,
        "#![no_std]\n#![forbid(unsafe_code)]\n\
        #[inline(never)] pub fn result(value:bool)->bool { value }\n",
    )
    .unwrap();
    std::fs::write(
        &caller,
        "#![no_std]\n#![forbid(unsafe_code)]\n\
        pub fn f32_metadata(v:&mut[f32]) {\
          assert!(float_metadata_dependency::result(v.is_empty())==(v.len()==0)); }\n\
        pub fn f64_metadata(v:&mut[f64]) {\
          assert!(float_metadata_dependency::result(v.is_empty())==(v.len()==0)); }\n",
    )
    .unwrap();
    let compiler = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let archive = directory.0.join(format!(
                    "libfloat_metadata_{}_{optimized}_{retained}.rlib",
                    target.unwrap_or("host"),
                ));
                let mut command = Command::new(&compiler);
                command
                    .args([
                        "--sysroot",
                        env!("MIREN_SYSROOT"),
                        "--crate-type=rlib",
                        "--crate-name=float_metadata_dependency",
                        "--edition=2024",
                        "-Cpanic=abort",
                    ])
                    .arg(&dependency)
                    .arg("-o")
                    .arg(&archive);
                command.arg(if retained {
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
                let output = command.output().unwrap();
                assert!(
                    output.status.success(),
                    "{}",
                    String::from_utf8_lossy(&output.stderr)
                );
                let expected = if retained {
                    ProofStatus::Proved
                } else {
                    ProofStatus::Unknown
                };
                let report = table_verification_float::verify(
                    &caller,
                    &[("f32_metadata", expected), ("f64_metadata", expected)],
                    target,
                    optimized,
                    &[
                        "--extern".into(),
                        format!("float_metadata_dependency={}", archive.display()),
                    ],
                );
                for name in ["f32_metadata", "f64_metadata"] {
                    let proof = report
                        .functions
                        .iter()
                        .find(|f| f.name == name)
                        .unwrap()
                        .proof
                        .as_ref()
                        .unwrap();
                    let entered = proof
                        .body_entries
                        .iter()
                        .any(|b| b.function.contains("float_metadata_dependency::result"));
                    if retained {
                        assert!(entered);
                    } else {
                        assert!(!entered);
                        assert!(proof.obligations.iter().any(|o| o.unknown_category
                            == Some(miren::UnknownCategory::MissingCompilerEvidence)));
                    }
                }
            }
        }
    }
}
