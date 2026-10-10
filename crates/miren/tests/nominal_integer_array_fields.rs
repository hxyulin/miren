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
            "miren-external-nominal-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/nominal_integer_array_fields.rs")
}

fn dependency() -> PathBuf {
    fixture().with_file_name("nominal_integer_array_dependency.rs")
}

fn compiler() -> PathBuf {
    Path::new(env!("MIREN_SYSROOT")).join("bin/rustc")
}

fn build_dependency(
    source: &Path,
    directory: &Directory,
    target: Option<&str>,
    optimized: bool,
    retained: bool,
    native: bool,
) -> PathBuf {
    let library = directory.0.join("libinteger_array_dependency.rlib");
    let mut command = Command::new(compiler());
    command
        .args([
            "--crate-name=integer_array_dependency",
            "--crate-type=rlib",
            "--edition=2024",
            "-Zmir-opt-level=0",
            "-Coverflow-checks=yes",
        ])
        .arg(if retained {
            "-Zalways-encode-mir=yes"
        } else {
            "-Zalways-encode-mir=no"
        })
        .arg(source)
        .arg("-o")
        .arg(&library)
        .arg(if optimized {
            "-Copt-level=2"
        } else {
            "-Copt-level=0"
        });
    if !native {
        command.arg("-Cpanic=abort");
    }
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    let output = command.output().unwrap();
    assert!(output.status.success(), "{output:?}");
    library
}

fn verify(
    source: &Path,
    dependency_source: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    retained: bool,
) {
    let directory = Directory::new();
    let library = build_dependency(
        dependency_source,
        &directory,
        target,
        optimized,
        retained,
        false,
    );
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    for (name, _) in entries {
        command.args(["--entry", name]);
    }
    command
        .args(["--", "--crate-type=lib", "--edition=2024"])
        .arg(source)
        .arg("--extern")
        .arg(format!("integer_array_dependency={}", library.display()))
        .arg("--out-dir")
        .arg(&directory.0)
        .args(["-Cpanic=abort", "-Coverflow-checks=yes"])
        .arg(if optimized {
            "-Copt-level=2"
        } else {
            "-Copt-level=0"
        });
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
            .find(|function| function.name == *name)
            .unwrap()
            .proof
            .as_ref()
            .unwrap();
        assert_eq!(
            proof.status, *expected,
            "{target:?}/{optimized}/{retained}/{name}: {proof:?}"
        );
        assert!(proof.assumptions.is_empty());
        assert!(proof.trusted_calls.is_empty());
        assert!(proof.entry_assumptions.is_empty());
        if *expected == ProofStatus::Unknown {
            let (category, reason) = if !retained {
                (
                    UnknownCategory::MissingCompilerEvidence,
                    "MIR body unavailable for",
                )
            } else {
                match *name {
                    "vacant_ref" | "vacant_core" | "vacant_pat" | "mutable_root" => (
                        UnknownCategory::Semantics,
                        "only read-only byte slices and byte arrays are modeled",
                    ),
                    "large_type" | "expanded_type" => {
                        (UnknownCategory::ResourceLimit, "composite slice")
                    }
                    "wrong_array_comparer" | "same_receiver" | "membership" => (
                        UnknownCategory::Semantics,
                        "nominal comparison compares different or repeated receiver fields",
                    ),
                    "omitted_array" => (
                        UnknownCategory::Semantics,
                        "nominal comparison does not compute all corresponding field equalities",
                    ),
                    other => panic!("missing actual frontier {other}"),
                }
            };
            assert!(
                proof.obligations.iter().any(|obligation| {
                    obligation.status == ProofStatus::Unknown
                        && obligation.unknown_category == Some(category)
                        && obligation.detail.contains(reason)
                        && (retained || obligation.detail.contains("core::cmp::PartialEq>::eq"))
                }),
                "{name}: {:?}",
                proof.obligations
            );
        } else if name.starts_with("direct_") {
            assert!(proof.body_entries.iter().any(|entry| {
                entry.function.contains("integer_array_dependency::")
                    && entry.function.ends_with("core::cmp::PartialEq>::eq")
            }));
        } else {
            let model = if matches!(
                *name,
                "equality"
                    | "empty"
                    | "different_views"
                    | "wrong_views"
                    | "float_sibling_self"
                    | "floating"
                    | "bool_arrays"
                    | "char_arrays"
                    | "external_empty"
                    | "external_mismatch"
            ) {
                "full-domain pure composite slice equality"
            } else {
                "full-domain pure composite slice membership"
            };
            assert!(
                proof.models.iter().any(|observed| observed.contains(model))
                    || *name == "external_mismatch"
            );
        }
        if matches!(*name, "membership" | "wrong_claim") {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == "selected")
            );
        }
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|obligation| {
                obligation.status == ProofStatus::Refuted
                    && obligation.query.is_some()
                    && obligation.model.is_some()
            }));
        }
    }
}

fn native(source: &Path, optimized: bool, mutant: bool) {
    let directory = Directory::new();
    let library = build_dependency(&dependency(), &directory, None, optimized, true, true);
    let executable = directory.0.join("native");
    let output = Command::new(compiler())
        .args(["--test", "--edition=2024"])
        .arg(source)
        .arg("--extern")
        .arg(format!("integer_array_dependency={}", library.display()))
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
    let started = Instant::now();
    while child.try_wait().unwrap().is_none() {
        if started.elapsed() >= Duration::from_secs(10) {
            child.kill().unwrap();
            panic!("native timeout: {:?}", child.wait_with_output().unwrap());
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    let output = child.wait_with_output().unwrap();
    assert_eq!(
        output.status.code(),
        Some(if mutant { 101 } else { 0 }),
        "{output:?}"
    );
}

#[test]
fn integer_array_child_comparers_and_missing_external_bodies_are_certified() {
    let entries = [
        ("membership", ProofStatus::Proved),
        ("equality", ProofStatus::Proved),
        ("empty", ProofStatus::Proved),
        ("nested", ProofStatus::Proved),
        ("different_views", ProofStatus::Proved),
        ("empty_member", ProofStatus::Proved),
        ("empty_maximum", ProofStatus::Proved),
        ("numeric_sibling", ProofStatus::Proved),
        ("external_selected", ProofStatus::Proved),
        ("external_empty", ProofStatus::Proved),
        ("external_mismatch", ProofStatus::Proved),
        ("wrong_claim", ProofStatus::Refuted),
        ("wrong_views", ProofStatus::Refuted),
        ("float_sibling_self", ProofStatus::Refuted),
        ("floating", ProofStatus::Proved),
        ("bool_arrays", ProofStatus::Proved),
        ("char_arrays", ProofStatus::Proved),
        ("vacant_ref", ProofStatus::Unknown),
        ("vacant_core", ProofStatus::Unknown),
        ("vacant_pat", ProofStatus::Unknown),
        ("large_type", ProofStatus::Unknown),
        ("expanded_type", ProofStatus::Unknown),
        ("wrong_array_comparer", ProofStatus::Unknown),
        ("same_receiver", ProofStatus::Unknown),
        ("omitted_array", ProofStatus::Unknown),
        ("mutable_root", ProofStatus::Unknown),
    ];
    let omitted: Vec<_> = entries
        .iter()
        .filter(|(name, _)| name.starts_with("external_"))
        .map(|(name, _)| (*name, ProofStatus::Unknown))
        .collect();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &dependency(), &entries, target, optimized, true);
            verify(
                &fixture(),
                &dependency(),
                &omitted,
                target,
                optimized,
                false,
            );
        }
    }
}

#[test]
fn integer_array_data_mutation_refutes_but_comparator_mutation_is_unknown() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "value.words[1].wrapping_add(0)";
    assert_eq!(source.matches(original).count(), 1);
    let mutant = directory.0.join("data-mutant.rs");
    std::fs::write(
        &mutant,
        source.replace(original, "value.words[1].wrapping_add(1)"),
    )
    .unwrap();
    let record = "#[derive(Clone, Copy, PartialEq)]\npub struct Words {";
    assert_eq!(source.matches(record).count(), 1);
    let wrong = directory.0.join("comparator-mutant.rs");
    let changed = source.replace(record, "#[derive(Clone, Copy)]\npub struct Words {");
    let implementation = concat!(
        "\nimpl PartialEq for Words {\n",
        "    fn eq(&self, other: &Self) -> bool {\n",
        "        self.words == self.words && self.marker == other.marker\n",
        "    }\n}\n"
    );
    std::fs::write(&wrong, format!("{changed}{implementation}")).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &mutant,
                &dependency(),
                &[("membership", ProofStatus::Refuted)],
                target,
                optimized,
                true,
            );
            verify(
                &wrong,
                &dependency(),
                &[("membership", ProofStatus::Unknown)],
                target,
                optimized,
                true,
            );
        }
    }
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
        native(&mutant, optimized, true);
    }
}
