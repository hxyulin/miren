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
            "miren-local-integer-niche-{}-{}",
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
        .join("../../tests/fixtures/local_integer_nonzero_niches.rs")
}
fn inspect(path: &Path, entries: &[(&str, ProofStatus, Option<&str>)], extra: &[String]) {
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
            command.args(extra);
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
                if (name.starts_with("read_") || name.starts_with("reverse_"))
                    && *expected == ProofStatus::Proved
                {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|b| b.function.contains("get_"))
                    );
                }
            }
        }
    }
}

#[test]
fn actual_local_integer_niches_preserve_both_variant_orders_and_refuse_other_domains() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    inspect(
        &fixture(),
        &[
            ("read_u8", P, None),
            ("reverse_u8", P, None),
            ("wrong_u8", R, None),
            ("read_u16", P, None),
            ("reverse_u16", P, None),
            ("wrong_u16", R, None),
            ("read_u32", P, None),
            ("reverse_u32", P, None),
            ("wrong_u32", R, None),
            ("read_u64", P, None),
            ("reverse_u64", P, None),
            ("wrong_u64", R, None),
            ("read_u128", P, None),
            ("reverse_u128", P, None),
            ("wrong_u128", R, None),
            ("read_usize", P, None),
            ("reverse_usize", P, None),
            ("wrong_usize", R, None),
            ("read_i8", P, None),
            ("reverse_i8", P, None),
            ("wrong_i8", R, None),
            ("read_i16", P, None),
            ("reverse_i16", P, None),
            ("wrong_i16", R, None),
            ("read_i32", P, None),
            ("reverse_i32", P, None),
            ("wrong_i32", R, None),
            ("read_i64", P, None),
            ("reverse_i64", P, None),
            ("wrong_i64", R, None),
            ("read_i128", P, None),
            ("reverse_i128", P, None),
            ("wrong_i128", R, None),
            ("read_isize", P, None),
            ("reverse_isize", P, None),
            ("wrong_isize", R, None),
            (
                "mutable_unknown",
                U,
                Some("only read-only byte slices and byte arrays are modeled"),
            ),
            (
                "reference_unknown",
                U,
                Some("only read-only byte slices and byte arrays are modeled"),
            ),
            (
                "extra_unknown",
                U,
                Some("NonZero niche original variant schema mismatch"),
            ),
            (
                "drop_unknown",
                U,
                Some("only read-only byte slices and byte arrays are modeled: [Dropping]"),
            ),
        ],
        &[],
    );
}

fn mutate(original: &str, primitive: &str, nonzero: &str) -> String {
    let helper = format!(
        "pub fn get_{primitive}(value: core::num::{nonzero}) -> {primitive} {{\n    value.get()\n}}"
    );
    assert_eq!(original.matches(&helper).count(), 1);
    original.replacen(
        &helper,
        &helper.replace("value.get()", "value.get() ^ 1"),
        1,
    )
}
const ROWS: [(&str, &str); 12] = [
    ("u8", "NonZeroU8"),
    ("u16", "NonZeroU16"),
    ("u32", "NonZeroU32"),
    ("u64", "NonZeroU64"),
    ("u128", "NonZeroU128"),
    ("usize", "NonZeroUsize"),
    ("i8", "NonZeroI8"),
    ("i16", "NonZeroI16"),
    ("i32", "NonZeroI32"),
    ("i64", "NonZeroI64"),
    ("i128", "NonZeroI128"),
    ("isize", "NonZeroIsize"),
];

#[test]
fn genuine_all_width_getter_mutations_refute_unchanged_local_claims() {
    let original = std::fs::read_to_string(fixture()).unwrap();
    for (primitive, nonzero) in ROWS {
        let scratch = Scratch::new();
        let source = scratch.0.join("mutant.rs");
        std::fs::write(&source, mutate(&original, primitive, nonzero)).unwrap();
        let read = format!("read_{primitive}");
        let reverse = format!("reverse_{primitive}");
        inspect(
            &source,
            &[
                (&read, ProofStatus::Refuted, None),
                (&reverse, ProofStatus::Refuted, None),
            ],
            &[],
        );
    }
}

fn native(path: &Path, level: u8, expected: i32) {
    let scratch = Scratch::new();
    let executable = scratch.0.join("native");
    let output = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"))
        .arg(path)
        .args(["--test", "--edition=2024", "-Coverflow-checks=yes"])
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
        .args(["--exact", "native::original_local_integer_rows"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(expected));
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("running 1 test"));
}

#[test]
fn actual_all_width_native_originals_and_mutants_keep_the_same_claims() {
    for level in [0, 2] {
        native(&fixture(), level, 0);
    }
    let original = std::fs::read_to_string(fixture()).unwrap();
    for (primitive, nonzero) in ROWS {
        let scratch = Scratch::new();
        let source = scratch.0.join("mutant.rs");
        std::fs::write(&source, mutate(&original, primitive, nonzero)).unwrap();
        for level in [0, 2] {
            native(&source, level, 101);
        }
    }
}

#[test]
fn genuine_missing_local_enum_helper_body_stays_unknown() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let scratch = Scratch::new();
            let rlib = scratch.0.join("liblocal_niche_dependency.rlib");
            let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
            compiler
                .args([
                    "--crate-type=rlib",
                    "--crate-name=local_niche_dependency",
                    "--edition=2024",
                    "-Zalways-encode-mir=no",
                    "-Cpanic=abort",
                ])
                .arg(
                    Path::new(env!("CARGO_MANIFEST_DIR"))
                        .join("../../tests/fixtures/local_integer_niche_dependency.rs"),
                )
                .arg("-o")
                .arg(&rlib)
                .arg(format!("-Copt-level={level}"));
            if let Some(target) = target {
                compiler.args(["--target", target]);
            }
            let output = compiler.output().unwrap();
            assert_eq!(output.status.code(), Some(0));
            let path = Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../tests/fixtures/local_integer_niche_dependent.rs");
            let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
            command
                .args([
                    "--verify",
                    "--json",
                    "--quiet",
                    "--entry",
                    "claim",
                    "--",
                    "--crate-type=lib",
                    "--edition=2024",
                    "-Cpanic=abort",
                ])
                .arg(path)
                .arg("--extern")
                .arg(format!("local_niche_dependency={}", rlib.display()))
                .arg("--out-dir")
                .arg(&scratch.0)
                .arg(format!("-Copt-level={level}"));
            if let Some(target) = target {
                command.args(["--target", target]);
            }
            let output = command.output().unwrap();
            assert_eq!(output.status.code(), Some(1));
            let report: Report = serde_json::from_slice(&output.stdout).unwrap();
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "claim")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert_eq!(proof.status, ProofStatus::Unknown);
            assert!(proof.obligations.iter().any(|o| {
                o.unknown_category == Some(UnknownCategory::MissingCompilerEvidence)
                    && o.detail
                        .contains("MIR body unavailable for local_niche_dependency::observe")
                    && o.query.is_none()
                    && o.model.is_none()
            }));
            assert!(
                !proof
                    .body_entries
                    .iter()
                    .any(|b| b.function.ends_with("::observe"))
            );
            assert!(
                proof.assumptions.is_empty()
                    && proof.entry_assumptions.is_empty()
                    && proof.trusted_calls.is_empty()
            );
        }
    }
}
