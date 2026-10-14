#![forbid(unsafe_code)]
use miren::{ProofStatus, Report, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::Command;
#[path = "support/table_verification.rs"]
mod table_verification;
use table_verification::{Directory, native, verify};

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/nested_function_choices.rs")
}

fn diagnostic(
    source: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
) -> Report {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet", "--max-steps", "60000"]);
    for (entry, _) in entries {
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
        .arg(source)
        .arg("--out-dir")
        .arg(&directory.0);
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    if optimized {
        command.arg("-Copt-level=2");
    }
    let output = command.output().unwrap();
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    assert_eq!(
        output.status.code(),
        Some(if entries.iter().all(|(_, s)| *s == ProofStatus::Proved) {
            0
        } else {
            1
        })
    );
    for (name, status) in entries {
        let proof = report
            .functions
            .iter()
            .find(|function| function.name == *name)
            .unwrap()
            .proof
            .as_ref()
            .unwrap();
        assert_eq!(
            proof.status, *status,
            "{name}/{target:?}/{optimized}: {:?}",
            proof.obligations
        );
        assert!(
            proof.assumptions.is_empty()
                && proof.entry_assumptions.is_empty()
                && proof.trusted_calls.is_empty()
        );
        match status {
            ProofStatus::Proved => {}
            ProofStatus::Refuted => {
                assert!(
                    proof
                        .obligations
                        .iter()
                        .any(|obligation| obligation.status == ProofStatus::Refuted
                            && obligation.query.is_some()
                            && obligation.model.is_some())
                )
            }
            ProofStatus::Unknown => {
                assert!(
                    proof
                        .obligations
                        .iter()
                        .any(|obligation| obligation.status == ProofStatus::Unknown
                            && obligation.query.is_none()
                            && obligation.model.is_none())
                )
            }
            ProofStatus::ProvedWithAssumptions => panic!("new assumptions are not permitted"),
        }
    }
    report
}

#[test]
fn default_integer_nested_calls_and_opaque_refusal() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(
                &fixture(),
                &[
                    ("nested_u8", ProofStatus::Proved),
                    ("nested_i128", ProofStatus::Proved),
                    ("opaque_bool", ProofStatus::Unknown),
                ],
                target,
                optimized,
                &[],
            );
            let unknown = report
                .functions
                .iter()
                .find(|function| function.name == "opaque_bool")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(
                unknown
                    .obligations
                    .iter()
                    .any(|obligation| obligation.unknown_category
                        == Some(UnknownCategory::Semantics))
            );
        }
    }
}

#[test]
fn diagnostic_budget_executes_full_family_and_harder_correlated_cases() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    let entries = [
        ("nested_bool", P),
        ("nested_char", P),
        ("nested_f32", P),
        ("nested_f64", P),
        ("nested_u8", P),
        ("nested_u16", P),
        ("nested_u32", P),
        ("nested_u64", P),
        ("nested_u128", P),
        ("nested_usize", P),
        ("nested_i8", P),
        ("nested_i16", P),
        ("nested_i32", P),
        ("nested_i64", P),
        ("nested_i128", P),
        ("nested_isize", P),
        ("repeat_bool", P),
        ("repeat_bool_once", P),
        ("nested_pair", P),
        ("nested_pair_direct", P),
        ("wrong_correlation", R),
        ("opaque_bool", U),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            diagnostic(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn actual_leaf_mutants_refute_unchanged_correlated_claims_and_fail_native() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
    }
    for (name, old, new, entries) in [
        (
            "bool",
            "fn flip_bool(value: bool) -> bool {\n    !value\n}",
            "fn flip_bool(value: bool) -> bool {\n    value\n}",
            vec!["nested_bool", "repeat_bool", "repeat_bool_once"],
        ),
        (
            "char",
            "if value == 'a' { 'b' } else { value }",
            "if value == 'a' { 'c' } else { value }",
            vec!["nested_char"],
        ),
        (
            "float",
            "fn second_f32(value: f32) -> f32 {\n    -value\n}",
            "fn second_f32(value: f32) -> f32 {\n    value\n}",
            vec!["nested_f32"],
        ),
        (
            "pair",
            "pair_first(a, b) ^ 1",
            "pair_first(a, b) ^ 3",
            vec!["nested_pair"],
        ),
        (
            "integer",
            "fn second_u128(value: u128) -> u128 {\n    value ^ 1\n}",
            "fn second_u128(value: u128) -> u128 {\n    value ^ 3\n}",
            vec!["nested_u128"],
        ),
    ] {
        assert!(source.contains(old), "{name}");
        let mutant = directory.0.join(format!("{name}.rs"));
        std::fs::write(&mutant, source.replacen(old, new, 1)).unwrap();
        let entries = entries
            .iter()
            .map(|name| (*name, ProofStatus::Refuted))
            .collect::<Vec<_>>();
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for optimized in [false, true] {
                diagnostic(&mutant, &entries, target, optimized);
            }
        }
        for optimized in [false, true] {
            native(&mutant, optimized, true);
        }
    }
}
