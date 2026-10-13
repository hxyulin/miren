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
            "miren-signed-niche-{}-{}",
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
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/signed_nonzero_niche_slices.rs")
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
                                && o.unknown_category == Some(UnknownCategory::Semantics)
                                && o.detail.contains(frontier.unwrap())
                                && o.query.is_none()
                                && o.model.is_none()),
                        "{name}: {proof:?}"
                    ),
                    ProofStatus::ProvedWithAssumptions => panic!("new premises forbidden"),
                }
                if matches!(*name, "correlated8" | "correlated16" | "correlated32")
                    && *expected != ProofStatus::Unknown
                {
                    assert!(proof.body_entries.iter().any(|b| b.function
                        == if *name == "correlated8" {
                            "actual_get8"
                        } else if *name == "correlated16" {
                            "actual_get16"
                        } else {
                            "actual_get32"
                        }));
                }
            }
        }
    }
}

#[test]
fn actual_signed_readonly_niches_preserve_tags_negative_payloads_and_refusals() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    inspect(
        &fixture(),
        &[
            ("correlated8", P, None),
            ("correlated16", P, None),
            ("correlated32", P, None),
            ("same16", P, None),
            ("minimums", P, None),
            ("fixed_array", P, None),
            ("contains_selected", P, None),
            ("wrong_nonnegative", R, None),
            ("wrong_zero", R, None),
            ("wrong_minimum", R, None),
            ("local_enum_unknown", P, None),
            (
                "mutable_unknown",
                U,
                Some("only read-only byte slices and byte arrays are modeled"),
            ),
            ("pointer_unknown", P, None),
            ("width64_unknown", P, None),
            (
                "signed_byte_unknown",
                U,
                Some("byte source statement debug payload is unsupported"),
            ),
        ],
    );
}
fn getter_mutant(source: &str) -> String {
    let old = "pub fn actual_get8(value: NonZeroI8) -> i8 {\n    value.get()\n}";
    assert_eq!(source.matches(old).count(), 1);
    source.replace(
        old,
        "pub fn actual_get8(value: NonZeroI8) -> i8 {\n    let _actual = value.get();\n    0\n}",
    )
}
fn equality_mutant(source: &str) -> String {
    let old = concat!(
        "pub fn actual_equal16(left: Option<NonZeroI16>, ",
        "right: Option<NonZeroI16>) -> bool {\n    left == right\n}"
    );
    assert_eq!(source.matches(old).count(), 1);
    source.replace(old, &old.replace("left == right", "left != right"))
}
#[test]
fn genuine_signed_helper_mutations_refute_unchanged_caller_claims() {
    let scratch = Scratch::new();
    let original = std::fs::read_to_string(fixture()).unwrap();
    for (name, text, entry) in [
        ("getter", getter_mutant(&original), "correlated8"),
        ("equal", equality_mutant(&original), "same16"),
    ] {
        let path = scratch.0.join(format!("{name}.rs"));
        std::fs::write(&path, text).unwrap();
        inspect(&path, &[(entry, ProofStatus::Refuted, None)]);
    }
}
#[test]
fn actual_native_signed_originals_and_helper_mutants_use_the_same_claims() {
    let scratch = Scratch::new();
    let original = std::fs::read_to_string(fixture()).unwrap();
    for (name, text, expected) in [
        ("original", original.clone(), 0),
        ("getter", getter_mutant(&original), 101),
        ("equal", equality_mutant(&original), 101),
    ] {
        let path = scratch.0.join(format!("{name}.rs"));
        std::fs::write(&path, text).unwrap();
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
                    "native::actual_signed_helpers_preserve_negative_claims",
                ])
                .output()
                .unwrap();
            assert_eq!(output.status.code(), Some(expected), "{output:?}");
        }
    }
}
