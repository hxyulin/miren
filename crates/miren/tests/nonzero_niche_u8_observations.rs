#![forbid(unsafe_code)]

use miren::{ProofStatus, Report};
use std::path::{Path, PathBuf};
use std::process::Command;
#[path = "support/table_verification.rs"]
mod table_verification;
use table_verification::{Directory, verify};

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/nonzero_niche_u8_observations.rs")
}

fn has_body(report: &Report, entry: &str, body: &str) {
    let proof = report
        .functions
        .iter()
        .find(|function| function.name == entry)
        .unwrap()
        .proof
        .as_ref()
        .unwrap();
    assert!(
        proof
            .body_entries
            .iter()
            .any(|entry| entry.function == body)
    );
}

#[test]
fn exact_option8_observations_comparisons_and_boundaries() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(
                &fixture(),
                &[
                    ("observe_correlated8", ProofStatus::Proved),
                    ("wrong_some_zero8", ProofStatus::Refuted),
                    ("same_observation_eq8", ProofStatus::Proved),
                    ("same_observation_ne8", ProofStatus::Proved),
                    ("wrong_ne8", ProofStatus::Refuted),
                    ("asserted_contains8", ProofStatus::Unknown),
                    ("local_enum_unknown", ProofStatus::Unknown),
                    ("mutable_unknown", ProofStatus::Unknown),
                    ("signed_unknown", ProofStatus::Unknown),
                    ("pointer_unknown", ProofStatus::Unknown),
                ],
                target,
                optimized,
                &[],
            );
            has_body(&report, "observe_correlated8", "selected_observer");
            has_body(&report, "same_observation_eq8", "selected_equal8");
            has_body(&report, "same_observation_ne8", "selected_not_equal8");
            has_body(&report, "wrong_ne8", "selected_not_equal8");
            has_body(&report, "asserted_contains8", "selected_member8");
            let proof = report
                .functions
                .iter()
                .find(|function| function.name == "asserted_contains8")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(proof.obligations.iter().any(|obligation| {
                obligation.unknown_category == Some(miren::UnknownCategory::Semantics)
                    && obligation
                        .detail
                        .contains("niche byte-sized transport needs")
            }));
        }
    }
}

fn mutant(source: &str, observer: bool) -> String {
    let (original, replacement) = if observer {
        (
            "        Some(word) => word.get(),",
            "        Some(word) => word.get() ^ 1,",
        )
    } else {
        ("    left == right", "    left != right")
    };
    assert_eq!(source.matches(original).count(), 1);
    let changed = source.replacen(original, replacement, 1);
    let claims = |source: &str| {
        source
            .lines()
            .filter(|line| line.contains("assert!"))
            .map(str::to_owned)
            .collect::<Vec<_>>()
    };
    assert_eq!(claims(source), claims(&changed));
    changed
}

fn native(source: &Path, optimized: bool, observer: bool, expected: i32) {
    let directory = Directory::new();
    let executable = directory.0.join("native");
    let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
    compiler
        .args(["--test", "--edition=2024", "-Coverflow-checks=yes"])
        .arg(source)
        .arg("-o")
        .arg(&executable);
    if optimized {
        compiler.arg("-Copt-level=2");
    }
    let output = compiler.output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let test = if observer {
        "native::observer_claims"
    } else {
        "native::equality_claims"
    };
    let result = Command::new(executable)
        .args(["--exact", test])
        .output()
        .unwrap();
    assert_eq!(result.status.code(), Some(expected));
    let stdout = String::from_utf8(result.stdout).unwrap();
    assert!(stdout.contains(if expected == 0 {
        "test result: ok. 1 passed; 0 failed;"
    } else {
        "test result: FAILED. 0 passed; 1 failed;"
    }));
}

#[test]
fn actual_option8_helpers_mutate_unchanged_claims_and_fail_natively() {
    let directory = Directory::new();
    let original = std::fs::read_to_string(fixture()).unwrap();
    for optimized in [false, true] {
        table_verification::native(&fixture(), optimized, false);
    }
    for observer in [true, false] {
        let path = directory.0.join(if observer {
            "observer.rs"
        } else {
            "equality.rs"
        });
        std::fs::write(&path, mutant(&original, observer)).unwrap();
        let entry = if observer {
            "observe_correlated8"
        } else {
            "same_observation_eq8"
        };
        let body = if observer {
            "selected_observer"
        } else {
            "selected_equal8"
        };
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for optimized in [false, true] {
                let report = verify(
                    &path,
                    &[(entry, ProofStatus::Refuted)],
                    target,
                    optimized,
                    &[],
                );
                has_body(&report, entry, body);
            }
        }
        for optimized in [false, true] {
            native(&path, optimized, observer, 101);
        }
    }
}

#[test]
fn genuine_external_option8_helpers_require_available_bodies() {
    let directory = Directory::new();
    let dependency = fixture();
    let caller = directory.0.join("caller.rs");
    std::fs::write(
        &caller,
        "#![no_std]\n#![forbid(unsafe_code)]\n\
        pub fn external_observation(values: &[Option<core::num::NonZeroU8>], index: usize) {\n\
            if index < values.len() {\n\
                let value = values[index];\n\
                match value {\n\
                    None => assert!(option8_dependency::selected_observer(value) == 0),\n\
                    Some(word) => assert!(\n\
                        option8_dependency::selected_observer(value) == word.get()),\n\
                }\n\
            }\n}\n\
        pub fn external_equality(values: &[Option<core::num::NonZeroU8>], index: usize) {\n\
            if index < values.len() {\n\
                let value = values[index];\n\
                assert!(option8_dependency::selected_equal8(value, value));\n\
            }\n}\n",
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let library = directory.0.join("liboption8_dependency.rlib");
                let mut command = Command::new("rustc");
                command
                    .arg(&dependency)
                    .args([
                        "--crate-name=option8_dependency",
                        "--crate-type=rlib",
                        "--edition=2024",
                        "-Cpanic=abort",
                        "-Coverflow-checks=yes",
                    ])
                    .arg(if retained {
                        "-Zalways-encode-mir=yes"
                    } else {
                        "-Zalways-encode-mir=no"
                    })
                    .arg("-o")
                    .arg(&library);
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
                verify(
                    &caller,
                    &[
                        ("external_observation", expected),
                        ("external_equality", expected),
                    ],
                    target,
                    optimized,
                    &[
                        "--extern".into(),
                        format!("option8_dependency={}", library.display()),
                    ],
                );
            }
        }
    }
}
