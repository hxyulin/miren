#![forbid(unsafe_code)]
use miren::{ProofStatus, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::Command;
#[path = "support/table_verification.rs"]
mod table_verification;
use table_verification::{Directory, native, verify};

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/nonzero_niche_membership.rs")
}

#[test]
fn exact_readonly_niche_membership_checks_positive_negative_and_unknown() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &fixture(),
                &[
                    ("selected_none", ProofStatus::Proved),
                    ("selected_some", ProofStatus::Proved),
                    ("empty", ProofStatus::Proved),
                    ("wrong_empty", ProofStatus::Refuted),
                    ("unsupported_width", ProofStatus::Refuted),
                ],
                target,
                optimized,
                &[],
            );
        }
    }
}

#[test]
fn actual_helper_mutation_fails_unchanged_claims_and_native() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    assert_eq!(source.matches("values.contains(&needle)").count(), 3);
    let mutant = directory.0.join("mutant.rs");
    std::fs::write(
        &mutant,
        source.replacen("values.contains(&needle)", "!values.contains(&needle)", 1),
    )
    .unwrap();
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
        native(&mutant, optimized, true);
        for target in [None, Some("thumbv7em-none-eabihf")] {
            let report = verify(
                &mutant,
                &[("selected_none", ProofStatus::Refuted)],
                target,
                optimized,
                &[],
            );
            let proof = report
                .functions
                .iter()
                .find(|entry| entry.name == "selected_none")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == "member")
            );
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
fn genuine_external_member_body_is_required() {
    let directory = Directory::new();
    let dependency = directory.0.join("dependency.rs");
    let caller = directory.0.join("caller.rs");
    std::fs::write(
        &dependency,
        r#"#![no_std]
#![forbid(unsafe_code)]
#[inline(never)] pub fn member(v: &[Option<core::num::NonZeroU16>]) -> bool { v.contains(&None) }
"#,
    )
    .unwrap();
    std::fs::write(
        &caller,
        r#"#![no_std]
#![forbid(unsafe_code)]
pub fn selected(v: &[Option<core::num::NonZeroU16>]) {
    if !v.is_empty() && v[0].is_none() { assert!(niche_external::member(v)); }
}
"#,
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let archive = directory
                    .0
                    .join(format!("libniche_{target:?}_{optimized}_{retained}.rlib"));
                let mut command = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
                command
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=niche_external",
                        "--edition=2024",
                        "-Cpanic=abort",
                    ])
                    .arg(&dependency)
                    .arg("-o")
                    .arg(&archive);
                if retained {
                    command.arg("-Zalways-encode-mir=yes");
                }
                if optimized {
                    command.arg("-Copt-level=2");
                }
                if let Some(target) = target {
                    command.args(["--target", target]);
                }
                assert!(command.status().unwrap().success());
                let status = if retained {
                    ProofStatus::Proved
                } else {
                    ProofStatus::Unknown
                };
                let report = verify(
                    &caller,
                    &[("selected", status)],
                    target,
                    optimized,
                    &[
                        "--extern".into(),
                        format!("niche_external={}", archive.display()),
                    ],
                );
                let proof = report.functions[0].proof.as_ref().unwrap();
                if retained {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|entry| entry.function.contains("member"))
                    );
                } else {
                    assert!(proof.obligations.iter().any(|entry| entry.unknown_category
                        == Some(UnknownCategory::MissingCompilerEvidence)));
                }
            }
        }
    }
}

#[test]
fn unsigned_u32_niche_membership_checks_prospective_statuses() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &fixture(),
                &[
                    ("selected_none_u32", ProofStatus::Proved),
                    ("selected_some_u32", ProofStatus::Proved),
                    ("empty_u32", ProofStatus::Proved),
                    ("wrong_empty_u32", ProofStatus::Refuted),
                    ("unsupported_byte_niche", ProofStatus::Unknown),
                ],
                target,
                optimized,
                &[],
            );
        }
    }
}

#[test]
fn unsigned_u32_helper_mutation_fails_unchanged_claims_and_native() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    assert_eq!(source.matches("values.contains(&needle)").count(), 3);
    let at = source.rfind("values.contains(&needle)").unwrap();
    let changed = format!(
        "{}{}",
        &source[..at],
        source[at..].replacen("values.contains(&needle)", "!values.contains(&needle)", 1)
    );
    let mutant = directory.0.join("u32-mutant.rs");
    std::fs::write(&mutant, changed).unwrap();
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
        native(&mutant, optimized, true);
        for target in [None, Some("thumbv7em-none-eabihf")] {
            let report = verify(
                &mutant,
                &[("selected_none_u32", ProofStatus::Refuted)],
                target,
                optimized,
                &[],
            );
            let proof = report
                .functions
                .iter()
                .find(|entry| entry.name == "selected_none_u32")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == "member_u32")
            );
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
fn unsigned_u32_selected_external_body_is_required() {
    let directory = Directory::new();
    let dependency = directory.0.join("dependency_u32.rs");
    let caller = directory.0.join("caller_u32.rs");
    std::fs::write(
        &dependency,
        "#![no_std]\n#![forbid(unsafe_code)]\n\
        #[inline(never)] pub fn member(v:&[Option<core::num::NonZeroU32>])->bool{\n\
        v.contains(&None)}\n",
    )
    .unwrap();
    std::fs::write(
        &caller,
        "#![no_std]\n#![forbid(unsafe_code)]\n\
        pub fn selected(v:&[Option<core::num::NonZeroU32>]){\n\
        if !v.is_empty() && v[0].is_none(){assert!(niche_external_u32::member(v));}}\n",
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let archive = directory.0.join(format!(
                    "libniche_u32_{target:?}_{optimized}_{retained}.rlib"
                ));
                let mut command = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
                command
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=niche_external_u32",
                        "--edition=2024",
                        "-Cpanic=abort",
                    ])
                    .arg(&dependency)
                    .arg("-o")
                    .arg(&archive);
                if retained {
                    command.arg("-Zalways-encode-mir=yes");
                }
                if optimized {
                    command.arg("-Copt-level=2");
                }
                if let Some(target) = target {
                    command.args(["--target", target]);
                }
                assert!(command.status().unwrap().success());
                let report = verify(
                    &caller,
                    &[(
                        "selected",
                        if retained {
                            ProofStatus::Proved
                        } else {
                            ProofStatus::Unknown
                        },
                    )],
                    target,
                    optimized,
                    &[
                        "--extern".into(),
                        format!("niche_external_u32={}", archive.display()),
                    ],
                );
                let proof = report.functions[0].proof.as_ref().unwrap();
                if retained {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|entry| entry.function.contains("member"))
                    );
                } else {
                    assert!(proof.obligations.iter().any(|entry| entry.unknown_category
                        == Some(UnknownCategory::MissingCompilerEvidence)));
                }
            }
        }
    }
}
