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
            "miren-full-integer-niche-{}-{}",
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
        .join("../../tests/fixtures/full_integer_nonzero_niches.rs")
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
                if name.starts_with("niche_") && *expected != ProofStatus::Unknown {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|b| b.function.starts_with("actual_get_"))
                    );
                }
            }
        }
    }
}

#[test]
fn actual_full_integer_niches_cover_widths_signedness_and_target_metadata() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    inspect(
        &fixture(),
        &[
            ("niche_u64", P, None),
            ("wrong_u64", R, None),
            ("same_u64", P, None),
            ("member_u64", P, None),
            ("niche_u128", P, None),
            ("wrong_u128", R, None),
            ("same_u128", P, None),
            ("member_u128", P, None),
            ("niche_usize", P, None),
            ("wrong_usize", R, None),
            ("same_usize", P, None),
            ("member_usize", P, None),
            ("niche_i64", P, None),
            ("wrong_i64", R, None),
            ("same_i64", P, None),
            ("member_i64", P, None),
            ("niche_i128", P, None),
            ("wrong_i128", R, None),
            ("same_i128", P, None),
            ("member_i128", P, None),
            ("niche_isize", P, None),
            ("wrong_isize", R, None),
            ("same_isize", P, None),
            ("member_isize", P, None),
            ("extremes", P, None),
            ("local_unknown", P, None),
            (
                "mutable_unknown",
                U,
                Some("only read-only byte slices and byte arrays are modeled"),
            ),
            (
                "pointer_unknown",
                U,
                Some(concat!(
                    "only read-only byte slices and byte arrays are modeled: ",
                    "[core::option::Option<&",
                )),
            ),
        ],
    );
}

#[test]
fn actual_full_width_getter_mutation_refutes_unchanged_claims() {
    let original = std::fs::read_to_string(fixture()).unwrap();
    let helper =
        "pub fn actual_get_i128(value: core::num::NonZeroI128) -> i128 {\n    value.get()\n}";
    assert_eq!(original.matches(helper).count(), 1);
    let mutant = original.replace(
        helper,
        concat!(
            "pub fn actual_get_i128(value: core::num::NonZeroI128) -> i128 {\n",
            "    let _actual = value.get();\n    0\n}",
        ),
    );
    let scratch = Scratch::new();
    let path = scratch.0.join("mutant.rs");
    std::fs::write(&path, mutant).unwrap();
    inspect(&path, &[("niche_i128", ProofStatus::Refuted, None)]);
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
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = Command::new(executable)
        .args([
            "--exact",
            "native::actual_integer_helpers_keep_original_claims",
        ])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(expected));
}
#[test]
fn actual_full_width_native_originals_and_mutants_use_unchanged_claims() {
    let original = std::fs::read_to_string(fixture()).unwrap();
    let helper =
        "pub fn actual_get_i128(value: core::num::NonZeroI128) -> i128 {\n    value.get()\n}";
    let mutant = original.replace(
        helper,
        concat!(
            "pub fn actual_get_i128(value: core::num::NonZeroI128) -> i128 {\n",
            "    let _actual = value.get();\n    0\n}",
        ),
    );
    assert_ne!(mutant, original);
    let scratch = Scratch::new();
    let path = scratch.0.join("mutant.rs");
    std::fs::write(&path, mutant).unwrap();
    for level in [0, 2] {
        native(&fixture(), level, 0);
        native(&path, level, 101);
    }
}

fn equality_mutant(original: &str) -> String {
    let start = original.find("pub fn actual_equal_u128(").unwrap();
    let end = start + original[start..].find("\n}").unwrap() + 2;
    let helper = &original[start..end];
    assert_eq!(helper.matches("left == right").count(), 1);
    original.replace(helper, &helper.replace("left == right", "left != right"))
}
#[test]
fn actual_full_width_equality_mutation_refutes_unchanged_claims() {
    let original = std::fs::read_to_string(fixture()).unwrap();
    let scratch = Scratch::new();
    let path = scratch.0.join("equal-mutant.rs");
    std::fs::write(&path, equality_mutant(&original)).unwrap();
    inspect(&path, &[("same_u128", ProofStatus::Refuted, None)]);
    for level in [0, 2] {
        native(&path, level, 101);
    }
}
