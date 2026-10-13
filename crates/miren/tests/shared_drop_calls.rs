#![forbid(unsafe_code)]
use miren::{ProofStatus, Report, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::Command;
#[path = "support/table_verification.rs"]
mod table_verification;
use table_verification::{Directory, native, verify};

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/shared_drop_calls.rs")
}
fn entered(report: &Report, entry: &str, callee: &str) {
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
            .body_entries
            .iter()
            .any(|body| body.function.contains(callee))
    );
    assert!(proof.assumptions.is_empty() && proof.trusted_calls.is_empty());
}
#[test]
fn actual_whole_shared_drop_helpers_preserve_storage_and_scalar_codecs() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(
                &fixture(),
                &[
                    ("claim", P),
                    ("forwarded", P),
                    ("lazy", P),
                    ("codecs", P),
                    ("wrong", R),
                    ("unguarded", R),
                    ("mutable_unknown", U),
                    ("raw_unknown", U),
                    ("product_unknown", U),
                ],
                target,
                optimized,
                &[],
            );
            for entry in ["claim", "forwarded", "lazy"] {
                for callee in [
                    "observe",
                    "word",
                    "Record as core::ops::Drop",
                    "release_guard",
                ] {
                    entered(&report, entry, callee);
                }
            }
            for callee in [
                "flag",
                "letter",
                "signed",
                "float",
                "wide",
                "Codecs as core::ops::Drop",
                "release_guard",
            ] {
                entered(&report, "codecs", callee);
            }
            for (entry, reason) in [
                ("mutable_unknown", "grants no mutable reference authority"),
                ("raw_unknown", "grants no raw pointer authority"),
                (
                    "product_unknown",
                    "cannot materialize or copy a non-Copy owner",
                ),
            ] {
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == entry)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert!(proof.obligations.iter().any(|o| o.status == U
                    && o.unknown_category == Some(UnknownCategory::Semantics)
                    && o.detail.contains(reason)));
            }
        }
    }
}

fn verify_contract(
    target: Option<&str>,
    optimized: bool,
    rule: serde_json::Value,
    expected: ProofStatus,
) -> Report {
    let directory = Directory::new();
    let config = directory.0.join("contracts.json");
    std::fs::write(
        &config,
        serde_json::to_vec(&serde_json::json!({
            "schema_version": 1, "functions": [rule],
        }))
        .unwrap(),
    )
    .unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command
        .args([
            "--verify",
            "--json",
            "--quiet",
            "--entry",
            "claim",
            "--contracts",
        ])
        .arg(config)
        .args([
            "--",
            "--crate-type=lib",
            "--crate-name=function_tables",
            "--edition=2024",
            "-Coverflow-checks=yes",
            "-Cpanic=abort",
        ])
        .arg(fixture())
        .arg("--out-dir")
        .arg(&directory.0);
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    if optimized {
        command.arg("-Copt-level=2");
    }
    let output = command.output().unwrap();
    assert_eq!(
        output.status.code(),
        Some(if expected == ProofStatus::Proved {
            0
        } else {
            1
        })
    );
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|e| panic!("{e}: {}", String::from_utf8_lossy(&output.stderr)));
    let proof = report
        .functions
        .iter()
        .find(|f| f.name == "claim")
        .unwrap()
        .proof
        .as_ref()
        .unwrap();
    assert_eq!(proof.status, expected, "{:?}", proof.obligations);
    assert!(proof.assumptions.is_empty() && proof.trusted_calls.is_empty());
    if expected == ProofStatus::Unknown {
        assert!(proof.obligations.iter().any(|o| {
            o.status == ProofStatus::Unknown
                && o.unknown_category == Some(UnknownCategory::Semantics)
                && o.detail
                    .contains("cannot materialize or copy a non-Copy owner")
        }));
    }
    report
}
#[test]
fn ordinary_no_panic_and_named_whole_contracts_keep_their_existing_semantics() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify_contract(
                target,
                optimized,
                serde_json::json!({
                    "function": "function_tables::observe", "no_panic": true,
                }),
                ProofStatus::Proved,
            );
            entered(&report, "claim", "observe");
            entered(&report, "claim", "Record as core::ops::Drop");
            for rule in [
                serde_json::json!({"function": "function_tables::observe",
                "arguments": ["value"], "requires": ["true"]}),
                serde_json::json!({"function": "function_tables::observe",
                    "arguments": ["value"], "ensures": ["result == value.word"]}),
            ] {
                verify_contract(target, optimized, rule, ProofStatus::Unknown);
            }
        }
    }
}
#[test]
fn genuine_whole_helper_and_destructor_mutations_refute() {
    use ProofStatus::Refuted as R;
    let original = std::fs::read_to_string(fixture()).unwrap();
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
    }
    for (before, after, callee) in [
        (
            "pub fn observe(value: &Record) -> u16 {\n    word(&value.word)\n}",
            "pub fn observe(value: &Record) -> u16 {\n    word(&value.word) ^ 1\n}",
            "observe",
        ),
        (
            "pub fn release_guard(value: u16) -> u16 {\n    value\n}",
            "pub fn release_guard(value: u16) -> u16 {\n    value ^ 1\n}",
            "release_guard",
        ),
    ] {
        assert_eq!(original.matches(before).count(), 1);
        let directory = Directory::new();
        let source = directory.0.join("mutated.rs");
        std::fs::write(&source, original.replacen(before, after, 1)).unwrap();
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for optimized in [false, true] {
                let report = verify(
                    &source,
                    &[("claim", R), ("forwarded", R), ("lazy", R)],
                    target,
                    optimized,
                    &[],
                );
                for entry in ["claim", "forwarded", "lazy"] {
                    entered(&report, entry, callee);
                }
            }
        }
        for optimized in [false, true] {
            native(&source, optimized, true);
        }
    }
}
