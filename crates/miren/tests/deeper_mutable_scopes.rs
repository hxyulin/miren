#![forbid(unsafe_code)]
use miren::{ProofStatus, Report, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
static NEXT: AtomicU64 = AtomicU64::new(0);
struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "miren-deeper-scopes-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/deeper_mutable_scopes.rs")
}
fn inspect(path: &Path, entries: &[(&str, ProofStatus, Option<&str>)]) {
    inspect_with_steps(path, entries, 8192);
}
fn inspect_with_steps(path: &Path, entries: &[(&str, ProofStatus, Option<&str>)], steps: usize) {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let scratch = Scratch::new();
            let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
            command.args([
                "--verify",
                "--json",
                "--quiet",
                "--max-steps",
                &steps.to_string(),
            ]);
            for (name, _, _) in entries {
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
                .arg(path)
                .arg("--out-dir")
                .arg(&scratch.0)
                .arg(format!("-Copt-level={level}"));
            if let Some(target) = target {
                command.args(["--target", target]);
            }
            let output = command.output().unwrap();
            let report: Report = serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
                panic!("{error}: {}", String::from_utf8_lossy(&output.stderr))
            });
            assert_eq!(
                output.status.code(),
                Some(
                    if entries.iter().all(|(_, s, _)| *s == ProofStatus::Proved) {
                        0
                    } else {
                        1
                    }
                )
            );
            for (name, expected, frontier) in entries {
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == *name)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert_eq!(proof.status, *expected, "{name}: {proof:?}");
                assert!(
                    proof.assumptions.is_empty()
                        && proof.entry_assumptions.is_empty()
                        && proof.trusted_calls.is_empty()
                );
                if *name == "product_unknown" && *expected == ProofStatus::Proved {
                    for helper in ["product_outer", "product_leaf"] {
                        assert!(
                            proof
                                .body_entries
                                .iter()
                                .any(|entry| entry.function == helper)
                        );
                    }
                    assert!(proof.obligations.iter().any(|o| o.query.is_some()));
                }
                match expected {
                    ProofStatus::Proved => assert!(
                        proof
                            .obligations
                            .iter()
                            .all(|o| o.status == ProofStatus::Proved)
                    ),
                    ProofStatus::Refuted => assert!(
                        proof
                            .obligations
                            .iter()
                            .any(|o| o.status == ProofStatus::Refuted
                                && o.query.is_some()
                                && o.model.is_some())
                    ),
                    ProofStatus::Unknown => assert!(
                        proof
                            .obligations
                            .iter()
                            .any(|o| o.status == ProofStatus::Unknown
                                && o.unknown_category
                                    == Some(if *name == "product_unknown" {
                                        UnknownCategory::ResourceLimit
                                    } else {
                                        UnknownCategory::Semantics
                                    })
                                && o.detail.contains(frontier.unwrap())
                                && o.query.is_none()
                                && o.model.is_none()),
                        "{name}: {proof:?}"
                    ),
                    ProofStatus::ProvedWithAssumptions => panic!("new premises forbidden"),
                }
            }
        }
    }
}

#[test]
fn actual_deeper_mutable_scopes_follow_body_effects_and_conservative_views() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    inspect(
        &fixture(),
        &[
            ("claim_u16", P, None),
            ("wrong_u16", R, None),
            ("claim_i32", P, None),
            ("wrong_i32", R, None),
            ("claim_bool", P, None),
            ("wrong_bool", R, None),
            ("claim_char", P, None),
            ("wrong_char", R, None),
            ("claim_f32", P, None),
            ("wrong_f32", R, None),
            ("claim_f64", P, None),
            ("wrong_f64", R, None),
            ("claim_associated", P, None),
            ("wrong_associated", R, None),
            ("sibling_retention", P, None),
            ("unchecked_bounds", R, None),
            (
                "interval_unknown",
                U,
                Some("mutable u16 staging needs a pending child"),
            ),
            (
                "product_unknown",
                U,
                Some("mutable product hierarchy shared execution step limit reached"),
            ),
        ],
    );
}
#[test]
fn nested_product_diagnostic_executes_actual_helpers() {
    inspect_with_steps(
        &fixture(),
        &[("product_unknown", ProofStatus::Proved, None)],
        2_000_000,
    );
}

fn mutant(source: &str, name: &str) -> String {
    let (needle, replacement) = match name {
        "u16" => (
            "pub fn payload_u16(word: u16) -> u16 {\n    word\n}",
            "pub fn payload_u16(word: u16) -> u16 {\n    word ^ 1\n}",
        ),
        "i32" => (
            "pub fn payload_i32(word: i32) -> i32 {\n    word\n}",
            "pub fn payload_i32(word: i32) -> i32 {\n    word ^ 1\n}",
        ),
        "bool" => (
            "pub fn payload_bool(word: bool) -> bool {\n    word\n}",
            "pub fn payload_bool(word: bool) -> bool {\n    !word\n}",
        ),
        "char" => (
            "pub fn payload_char(word: char) -> char {\n    word\n}",
            "pub fn payload_char(word: char) -> char {\n    let _actual = word;\n    '\\0'\n}",
        ),
        "f32" => (
            "pub fn payload_f32(word: f32) -> f32 {\n    word\n}",
            "pub fn payload_f32(word: f32) -> f32 {\n    let _actual = word;\n    0.0\n}",
        ),
        "f64" => (
            "pub fn payload_f64(word: f64) -> f64 {\n    word\n}",
            "pub fn payload_f64(word: f64) -> f64 {\n    let _actual = word;\n    0.0\n}",
        ),
        "associated" => (
            "pub fn payload(word: u16) -> u16 {\n        word\n    }",
            "pub fn payload(word: u16) -> u16 {\n        word ^ 1\n    }",
        ),
        _ => panic!("unknown actual helper"),
    };
    assert_eq!(source.matches(needle).count(), 1);
    source.replace(needle, replacement)
}
#[test]
fn genuine_deep_helper_mutations_refute_unchanged_claims() {
    let original = std::fs::read_to_string(fixture()).unwrap();
    for name in ["u16", "i32", "bool", "char", "f32", "f64", "associated"] {
        let scratch = Scratch::new();
        let path = scratch.0.join("mutant.rs");
        std::fs::write(&path, mutant(&original, name)).unwrap();
        inspect(
            &path,
            &[(format!("claim_{name}").as_str(), ProofStatus::Refuted, None)],
        );
    }
}
fn native(path: &Path, level: u8, expected: i32) {
    let scratch = Scratch::new();
    let executable = scratch.0.join("native");
    let output = Command::new("rustc")
        .arg(path)
        .args(["--test", "--edition=2024"])
        .arg(format!("-Copt-level={level}"))
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(0));
    let output = Command::new(executable)
        .args([
            "--exact",
            "native::actual_deep_helpers_preserve_original_claims",
        ])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(expected));
}
#[test]
fn actual_deep_native_original_and_mutants_use_the_same_claims() {
    let original = std::fs::read_to_string(fixture()).unwrap();
    for level in [0, 2] {
        native(&fixture(), level, 0);
    }
    for name in ["u16", "i32", "bool", "char", "f32", "f64", "associated"] {
        let scratch = Scratch::new();
        let path = scratch.0.join("mutant.rs");
        std::fs::write(&path, mutant(&original, name)).unwrap();
        for level in [0, 2] {
            native(&path, level, 101);
        }
    }
}

#[test]
fn genuine_external_deep_payload_still_requires_available_body() {
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let scratch = Scratch::new();
            let library = scratch.0.join("libdeeper_scope_dependency.rlib");
            let mut rustc = Command::new("rustc");
            rustc
                .arg(fixtures.join("deeper_scope_dependency.rs"))
                .args([
                    "--crate-type=rlib",
                    "--crate-name=deeper_scope_dependency",
                    "--edition=2024",
                ])
                .arg("-Cpanic=abort")
                .arg(format!("-Copt-level={level}"))
                .arg("-o")
                .arg(&library);
            if let Some(target) = target {
                rustc.args(["--target", target]);
            }
            let compile = rustc.output().unwrap();
            assert_eq!(compile.status.code(), Some(0));
            let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
            command
                .args([
                    "--verify",
                    "--json",
                    "--quiet",
                    "--entry",
                    "missing_payload",
                    "--",
                ])
                .arg(fixtures.join("deeper_scope_dependent.rs"))
                .args(["--crate-type=lib", "--edition=2024", "-Cpanic=abort"])
                .arg(format!("-Copt-level={level}"))
                .arg("--extern")
                .arg(format!("deeper_scope_dependency={}", library.display()))
                .arg("--out-dir")
                .arg(&scratch.0);
            if let Some(target) = target {
                command.args(["--target", target]);
            }
            let output = command.output().unwrap();
            assert_eq!(output.status.code(), Some(1));
            let report: Report = serde_json::from_slice(&output.stdout).unwrap();
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "missing_payload")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert_eq!(proof.status, ProofStatus::Unknown);
            assert!(
                proof.assumptions.is_empty()
                    && proof.entry_assumptions.is_empty()
                    && proof.trusted_calls.is_empty()
            );
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.status == ProofStatus::Unknown
                        && o.unknown_category == Some(UnknownCategory::MissingCompilerEvidence)
                        && o.detail.contains("payload")
                        && o.query.is_none()
                        && o.model.is_none())
            );
        }
    }
}
