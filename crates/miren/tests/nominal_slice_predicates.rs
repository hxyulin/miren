#![forbid(unsafe_code)]

use miren::{ProofStatus, Report, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct Directory(PathBuf);

impl Directory {
    fn new() -> Self {
        let id = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "miren-nominal-slice-predicates-{}-{id}",
            std::process::id()
        ));
        std::fs::create_dir_all(&path).unwrap();
        Self(path)
    }
}

impl Drop for Directory {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/nominal_slice_predicates.rs")
}

fn verify(path: &Path, entries: &[(&str, ProofStatus)], target: Option<&str>, optimized: bool) {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    for (name, _) in entries {
        command.args(["--entry", name]);
    }
    command
        .args(["--", "--crate-type=lib", "--edition=2024"])
        .arg(path)
        .arg("--out-dir")
        .arg(&directory.0)
        .args(["-Cpanic=abort", "-Coverflow-checks=yes"]);
    if optimized {
        command.arg("-Copt-level=2");
    }
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    let output = command.output().unwrap();
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    assert_eq!(
        output.status.success(),
        entries
            .iter()
            .all(|(_, status)| *status == ProofStatus::Proved)
    );
    for (name, expected) in entries {
        let proof = report
            .functions
            .iter()
            .find(|f| f.name == *name)
            .unwrap()
            .proof
            .as_ref()
            .unwrap();
        assert_eq!(
            proof.status, *expected,
            "{target:?} optimized={optimized} {name}: {:?}",
            proof.obligations
        );
        assert!(proof.assumptions.is_empty());
        assert!(proof.trusted_calls.is_empty());
        assert!(proof.entry_assumptions.is_empty());
        if *expected == ProofStatus::Unknown {
            let (category, reason) = match *name {
                "nonstructural" => (
                    UnknownCategory::Semantics,
                    "nominal comparison does not compute all corresponding field equalities",
                ),
                "panicking_comparator" => (
                    UnknownCategory::Semantics,
                    "nominal comparison contains an unsupported terminator or effect",
                ),
                "selected" => (
                    UnknownCategory::Semantics,
                    "nominal comparison compares different or repeated receiver fields",
                ),
                "mutable_root" => (
                    UnknownCategory::Unclassified,
                    "mutable product metadata needs the original direct root",
                ),
                "competing_roots" | "reference_zero" | "refined_zero" => (
                    UnknownCategory::Semantics,
                    "only read-only byte slices and byte arrays are modeled",
                ),
                "analyzer_only::missing_body" => (
                    UnknownCategory::MissingCompilerEvidence,
                    "no compiler-exported Rust definition matches the foreign symbol",
                ),
                other => panic!("missing actual unknown frontier for {other}"),
            };
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| o.status == ProofStatus::Unknown
                        && o.unknown_category == Some(category)
                        && o.detail.contains(reason)),
                "{name}: {:?}",
                proof.obligations
            );
        } else {
            let model = if matches!(
                *name,
                "selected"
                    | "absent"
                    | "generic_selected"
                    | "nested_selected"
                    | "non_nan_selected"
                    | "signed_zero"
                    | "char_selected"
                    | "zero_contains"
                    | "zero_maximum"
                    | "array_lowering"
            ) {
                concat!(
                    "full-domain pure composite slice membership; ",
                    "scoped existential structural numeric equality"
                )
            } else {
                concat!(
                    "full-domain pure composite slice equality; ",
                    "scoped universal structural numeric equality"
                )
            };
            assert!(
                proof.models.iter().any(|observed| observed.contains(model)),
                "{name}: {:?}",
                proof.models
            );
        }
        if *name == "selected" || *name == "absent" {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|b| b.function == "selected_needle")
            );
        }
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|obligation| {
                obligation.status == ProofStatus::Refuted
                    && obligation.model.is_some()
                    && obligation.query.is_some()
            }));
        }
    }
}

fn native_guard(path: &Path, directory: &Directory, optimized: bool, mutant: bool) -> bool {
    let executable = directory.0.join("native");
    let compiler = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
    let output = Command::new(compiler)
        .args(["--test", "--edition=2024"])
        .arg(path)
        .arg(if optimized {
            "-Copt-level=2"
        } else {
            "-Copt-level=0"
        })
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let mut command = Command::new(executable);
    if mutant {
        command.args(["--exact", "tests::mutation_guard"]);
    }
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let start = Instant::now();
    loop {
        if child.try_wait().unwrap().is_some() {
            break;
        }
        if start.elapsed() >= Duration::from_secs(10) {
            child.kill().unwrap();
            let output = child.wait_with_output().unwrap();
            panic!("native control exceeded ten seconds: {output:?}");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    let output = child.wait_with_output().unwrap();
    assert!(matches!(output.status.code(), Some(0 | 101)), "{output:?}");
    output.status.success()
}

#[test]
fn certified_nominal_comparisons_preserve_complete_numeric_field_relations() {
    let entries = [
        ("selected", ProofStatus::Proved),
        ("self_equal", ProofStatus::Proved),
        ("same_views", ProofStatus::Proved),
        ("distinct_views", ProofStatus::Proved),
        ("generic_selected", ProofStatus::Proved),
        ("nested_selected", ProofStatus::Proved),
        ("non_nan_selected", ProofStatus::Proved),
        ("signed_zero", ProofStatus::Proved),
        ("char_selected", ProofStatus::Proved),
        ("zero_contains", ProofStatus::Proved),
        ("zero_maximum", ProofStatus::Proved),
        ("absent", ProofStatus::Refuted),
        ("falsely_equal_views", ProofStatus::Refuted),
        ("falsely_float_self", ProofStatus::Refuted),
        ("array_lowering", ProofStatus::Proved),
        ("nonstructural", ProofStatus::Unknown),
        ("panicking_comparator", ProofStatus::Unknown),
        ("mutable_root", ProofStatus::Unknown),
        ("competing_roots", ProofStatus::Unknown),
        ("reference_zero", ProofStatus::Unknown),
        ("refined_zero", ProofStatus::Unknown),
        ("analyzer_only::missing_body", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

#[test]
fn data_mutation_refutes_while_nonstructural_comparator_mutation_refuses() {
    let source = std::fs::read_to_string(fixture()).unwrap();
    let directory = Directory::new();
    let data_mutant = directory.0.join("data-mutant.rs");
    let original = "    values[index]\n";
    assert_eq!(source.matches(original).count(), 1);
    std::fs::write(
        &data_mutant,
        source.replace(
            original,
            concat!(
                "    let selected = values[index];\n",
                "    Record { left: selected.left, right: selected.right.wrapping_add(1) }\n"
            ),
        ),
    )
    .unwrap();
    let comparator_mutant = directory.0.join("comparator-mutant.rs");
    let record = concat!(
        "#[derive(Clone, Copy, PartialEq)]\n",
        "pub struct Record {\n    pub left: u16,\n    pub right: u16,\n}"
    );
    assert_eq!(source.matches(record).count(), 1);
    let changed = record.replace("Clone, Copy, PartialEq", "Clone, Copy");
    let changed = format!("{changed}\nimpl PartialEq for Record {{\n",);
    let changed = format!(
        concat!(
            "{changed}    fn eq(&self, other: &Self) -> bool {{\n",
            "        self.left == other.left && self.right == other.left\n",
            "    }}\n}}"
        ),
        changed = changed
    );
    std::fs::write(&comparator_mutant, source.replace(record, &changed)).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &data_mutant,
                &[("selected", ProofStatus::Refuted)],
                target,
                optimized,
            );
            verify(
                &comparator_mutant,
                &[("selected", ProofStatus::Unknown)],
                target,
                optimized,
            );
        }
    }
    for optimized in [false, true] {
        assert!(native_guard(
            &fixture(),
            &Directory::new(),
            optimized,
            false
        ));
        assert!(!native_guard(
            &data_mutant,
            &Directory::new(),
            optimized,
            true
        ));
    }
}
