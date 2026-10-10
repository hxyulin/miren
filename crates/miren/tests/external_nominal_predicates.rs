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
        .join("../../tests/fixtures/external_nominal_predicates.rs")
}

fn dependency() -> PathBuf {
    fixture().with_file_name("external_nominal_dependency.rs")
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
    let library = directory.0.join("libstage185_dependency.rlib");
    let mut command = Command::new(compiler());
    command
        .args([
            "--crate-name=stage185_dependency",
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
        .arg(format!("stage185_dependency={}", library.display()))
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
            let (category, reason) = if retained {
                (
                    UnknownCategory::Semantics,
                    "nominal comparison compares different or repeated receiver fields",
                )
            } else {
                (
                    UnknownCategory::MissingCompilerEvidence,
                    "MIR body unavailable for",
                )
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
                entry.function.contains("stage185_dependency::")
                    && entry.function.ends_with("core::cmp::PartialEq>::eq")
            }));
        } else {
            let model = if matches!(
                *name,
                "self_equal" | "unequal_views" | "falsely_equal_views"
            ) {
                "full-domain pure composite slice equality"
            } else {
                "full-domain pure composite slice membership"
            };
            assert!(
                proof.models.iter().any(|observed| observed.contains(model))
                    || *name == "unequal_views"
            );
        }
        if matches!(*name, "selected" | "absent") {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == "selected_needle")
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
        .arg(format!("stage185_dependency={}", library.display()))
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
fn external_selected_comparer_mir_is_required_even_before_shortcuts() {
    let entries = [
        ("selected", ProofStatus::Proved),
        ("self_equal", ProofStatus::Proved),
        ("empty_contains", ProofStatus::Proved),
        ("unequal_views", ProofStatus::Proved),
        ("zero_contains", ProofStatus::Proved),
        ("zero_empty", ProofStatus::Proved),
        ("zero_maximum", ProofStatus::Proved),
        ("direct_owned", ProofStatus::Proved),
        ("direct_zero", ProofStatus::Proved),
        ("direct_false", ProofStatus::Refuted),
        ("absent", ProofStatus::Refuted),
        ("falsely_equal_views", ProofStatus::Refuted),
    ];
    let omitted: Vec<_> = entries
        .iter()
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
fn external_data_mutation_refutes_but_comparator_mutation_is_unknown() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "    values[index]\n";
    assert_eq!(source.matches(original).count(), 1);
    let mutant = directory.0.join("data-mutant.rs");
    std::fs::write(
        &mutant,
        source.replace(
            original,
            concat!(
                "    let selected = values[index];\n",
                "    Record { left: selected.left, right: selected.right.wrapping_add(1) }\n"
            ),
        ),
    )
    .unwrap();
    let dependency_source = std::fs::read_to_string(dependency()).unwrap();
    let field = "self.right == other.right";
    assert_eq!(dependency_source.matches(field).count(), 1);
    let wrong = directory.0.join("comparator-mutant.rs");
    std::fs::write(
        &wrong,
        dependency_source.replace(field, "self.right == other.left"),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &mutant,
                &dependency(),
                &[("selected", ProofStatus::Refuted)],
                target,
                optimized,
                true,
            );
            verify(
                &fixture(),
                &wrong,
                &[("selected", ProofStatus::Unknown)],
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
