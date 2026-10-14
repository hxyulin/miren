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
            "miren-effect-free-drop-{}-{}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/effect_free_zst_box_drop.rs")
}
fn inspect(path: &Path, entries: &[(&str, ProofStatus, Option<&str>)]) {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let scratch = Scratch::new();
            let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
            command.args(["--verify", "--json", "--quiet"]);
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
            let selected = report
                .functions
                .iter()
                .filter(|f| f.proof.is_some())
                .map(|f| f.name.as_str())
                .collect::<Vec<_>>();
            assert_eq!(selected.len(), entries.len());
            assert_eq!(
                selected
                    .into_iter()
                    .collect::<std::collections::BTreeSet<_>>(),
                entries
                    .iter()
                    .map(|(name, _, _)| *name)
                    .collect::<std::collections::BTreeSet<_>>()
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
                                && o.unknown_category == Some(if frontier.unwrap()
                                    == "Box constructor source shared execution step limit reached"
                                {
                                    UnknownCategory::ResourceLimit
                                } else { UnknownCategory::Semantics })
                                && o.detail.contains(frontier.unwrap())
                                && o.query.is_none()
                                && o.model.is_none()),
                        "{name}: {proof:?}"
                    ),
                    ProofStatus::ProvedWithAssumptions => panic!("new premises forbidden"),
                }
                if matches!(
                    *name,
                    "implicit" | "explicit" | "transfer" | "independent" | "branches"
                ) && *expected != ProofStatus::Unknown
                {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|b| b.function == "actual_tag")
                    );
                }
            }
        }
    }
}
#[test]
fn actual_effect_free_destructor_preserves_ownership_and_refuses_effects() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    inspect(
        &fixture(),
        &[
            ("implicit", P, None),
            ("explicit", P, None),
            ("transfer", P, None),
            ("independent", P, None),
            ("branches", P, None),
            ("wrong_tag", R, None),
            (
                "panicking",
                U,
                Some("Box constructor source shared execution step limit reached"),
            ),
            (
                "effectful",
                U,
                Some("Box constructor source shared execution step limit reached"),
            ),
            (
                "nested",
                U,
                Some("effect-free Box Drop requires local fieldless unpacked Freeze storage"),
            ),
            (
                "nonzero",
                U,
                Some("effect-free Box Drop requires local fieldless unpacked Freeze storage"),
            ),
            (
                "zero_array",
                U,
                Some("effect-free Box Drop requires local fieldless unpacked Freeze storage"),
            ),
            (
                "not_freeze",
                U,
                Some("effect-free Box Drop requires local fieldless unpacked Freeze storage"),
            ),
        ],
    );
}
fn helper_mutant(source: &str) -> String {
    let old = "pub fn actual_tag() -> u16 {\n    17\n}";
    assert_eq!(source.matches(old).count(), 1);
    source.replace(old, &old.replace("17", "18"))
}
fn destructor_mutant(source: &str) -> String {
    let old = "impl Drop for Marker {\n    fn drop(&mut self) {}\n}";
    assert_eq!(source.matches(old).count(), 1);
    source.replace(
        old,
        "impl Drop for Marker {\n    fn drop(&mut self) { panic!(\"mutant\"); }\n}",
    )
}
#[test]
fn actual_helper_and_destructor_mutations_preserve_caller_claims() {
    let scratch = Scratch::new();
    let original = std::fs::read_to_string(fixture()).unwrap();
    let helper = scratch.0.join("helper.rs");
    std::fs::write(&helper, helper_mutant(&original)).unwrap();
    inspect(
        &helper,
        &[
            ("implicit", ProofStatus::Refuted, None),
            ("transfer", ProofStatus::Refuted, None),
        ],
    );
    let destructor = scratch.0.join("destructor.rs");
    std::fs::write(&destructor, destructor_mutant(&original)).unwrap();
    inspect(
        &destructor,
        &[
            (
                "implicit",
                ProofStatus::Unknown,
                Some("Box constructor source shared execution step limit reached"),
            ),
            (
                "transfer",
                ProofStatus::Unknown,
                Some("Box constructor source shared execution step limit reached"),
            ),
        ],
    );
}
#[test]
fn genuine_native_destructor_and_helper_mutations_fail_the_same_claims() {
    let scratch = Scratch::new();
    let original = std::fs::read_to_string(fixture()).unwrap();
    for (name, source, expected) in [
        ("original", original.clone(), 0),
        ("helper", helper_mutant(&original), 101),
        ("destructor", destructor_mutant(&original), 101),
    ] {
        let path = scratch.0.join(format!("{name}.rs"));
        std::fs::write(&path, source).unwrap();
        for level in [0, 2] {
            let exe = scratch.0.join(format!("{name}-{level}"));
            let output = Command::new("rustc")
                .arg(&path)
                .args(["--test", "--edition=2024"])
                .arg(format!("-Copt-level={level}"))
                .arg("-o")
                .arg(&exe)
                .output()
                .unwrap();
            assert_eq!(output.status.code(), Some(0), "{output:?}");
            let output = Command::new(&exe)
                .args([
                    "--exact",
                    "native::unchanged_claims_execute_actual_destructor_and_helper",
                ])
                .output()
                .unwrap();
            assert_eq!(output.status.code(), Some(expected), "{output:?}");
        }
    }
}
