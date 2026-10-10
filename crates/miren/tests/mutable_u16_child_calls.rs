#![forbid(unsafe_code)]
use miren::{ProofStatus, Report, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Directory(PathBuf);
impl Directory {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "miren-u16-child-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/mutable_u16_child_calls.rs")
}
fn verify(
    source: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    extra: &[String],
) -> Report {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    for (name, _) in entries {
        command.args(["--entry", name]);
    }
    command
        .args([
            "--",
            "--crate-type=lib",
            "--crate-name=mutable_u16_child_calls",
            "--edition=2024",
            "-Coverflow-checks=yes",
        ])
        .arg(source)
        .arg("--out-dir")
        .arg(&directory.0);
    if !extra.iter().any(|arg| arg == "-Cpanic=unwind") {
        command.arg("-Cpanic=abort");
    }
    if optimized {
        command.arg("-Copt-level=2");
    }
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    command.args(extra);
    let output = command.output().unwrap();
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    assert_eq!(
        output.status.success(),
        entries
            .iter()
            .all(|(_, status)| *status == ProofStatus::Proved)
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
fn synchronous_whole_child_retains_current_data_and_refuses_other_leases() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    let entries = [
        ("selected", P),
        ("explicit", P),
        ("scalar_return", P),
        ("sequential", P),
        ("branches", P),
        ("untouched", P),
        ("child_empty", P),
        ("scalar_nested", P),
        ("wrong", R),
        ("unreachable_panic", R),
        ("nested", U),
        ("retained_metadata", U),
        ("shared_view", U),
        ("two_arguments", U),
        ("reference_escape", U),
        ("analyzer_only::duplicate_alias", U),
        ("analyzer_only::duplicate_arguments", U),
        ("analyzer_only::parent_during_lease", U),
        ("analyzer_only::stale_child", U),
        ("analyzer_only::moved_parent", U),
        ("analyzer_only::pending_return", U),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&fixture(), &entries, target, optimized, &[]);
            for name in ["selected", "wrong", "sequential", "explicit"] {
                let proof = report
                    .functions
                    .iter()
                    .find(|function| function.name == name)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert!(
                    proof
                        .body_entries
                        .iter()
                        .any(|entry| entry.function == "child")
                );
            }
            let proof = report
                .functions
                .iter()
                .find(|function| function.name == "scalar_nested")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == "scalar_operation_child")
            );
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == "scalar_operation")
            );
            for (name, _) in entries.iter().filter(|(_, status)| *status == U) {
                let proof = report
                    .functions
                    .iter()
                    .find(|function| function.name == *name)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                let reason = match *name {
                    "nested" => "staging needs a pending child",
                    "retained_metadata" | "shared_view" => "metadata needs original direct root",
                    "two_arguments" => "one original borrow",
                    "reference_escape" => "direct abort-only Rust body",
                    "analyzer_only::duplicate_alias"
                    | "analyzer_only::parent_during_lease"
                    | "analyzer_only::stale_child" => "suspended or its child generation has ended",
                    "analyzer_only::duplicate_arguments" => "duplicates root authority",
                    "analyzer_only::moved_parent" => "moved parent transport is deferred",
                    "analyzer_only::pending_return" => "pending mutable u16 child cannot leave",
                    _ => panic!("unmatched UNKNOWN {name}"),
                };
                assert!(
                    proof
                        .obligations
                        .iter()
                        .any(|obligation| obligation.status == U
                            && obligation.unknown_category == Some(UnknownCategory::Semantics)
                            && obligation.detail.contains(reason))
                );
            }
            verify(
                &fixture(),
                &[("selected", P), ("explicit", P), ("scalar_nested", P)],
                target,
                optimized,
                &["-Zmir-opt-level=0".into()],
            );
            let report = verify(
                &fixture(),
                &[("selected", U)],
                target,
                optimized,
                &["-Cpanic=unwind".into()],
            );
            let proof = report
                .functions
                .iter()
                .find(|function| function.name == "selected")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|obligation| obligation.unknown_category
                        == Some(UnknownCategory::Semantics)
                        && obligation.detail.contains("abort-only"))
            );
        }
    }
}

fn native(source: &Path, optimized: bool, mutant: bool) {
    let directory = Directory::new();
    let executable = directory.0.join("native");
    let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
    compiler
        .args(["--test", "--edition=2024", "-Coverflow-checks=yes"])
        .arg(source)
        .arg("-o")
        .arg(&executable);
    if optimized {
        compiler.arg("-Copt-level=2");
    }
    let output = compiler.output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mut command = Command::new(executable);
    if mutant {
        command.arg("mutation_guard");
    }
    assert_eq!(
        command.output().unwrap().status.code(),
        Some(if mutant { 101 } else { 0 })
    );
}

#[test]
fn actual_child_and_nested_scalar_body_mutations_refute_and_fail_finite_native() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    let patterns = [
        (
            "values[index] = word ^ 0;",
            "values[index] = word ^ 1;",
            "selected",
        ),
        (
            "pub fn scalar_operation(word: u16) -> u16 {\n    word ^ 0\n}",
            "pub fn scalar_operation(word: u16) -> u16 {\n    word ^ 1\n}",
            "scalar_nested",
        ),
    ];
    for (old, new, root) in patterns {
        assert_eq!(source.matches(old).count(), 1);
        let mutant = directory.0.join(format!("{root}.rs"));
        std::fs::write(&mutant, source.replace(old, new)).unwrap();
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for optimized in [false, true] {
                verify(
                    &mutant,
                    &[(root, ProofStatus::Refuted)],
                    target,
                    optimized,
                    &[],
                );
            }
        }
        for optimized in [false, true] {
            native(&mutant, optimized, true);
        }
    }
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
    }
}

#[test]
fn external_selected_child_requires_genuinely_retained_compiler_body() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let directory = Directory::new();
                let library = directory.0.join("libstage189_dependency.rlib");
                let dependency = fixture().with_file_name("mutable_u16_child_dependency.rs");
                let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
                compiler
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=stage189_dependency",
                        "--edition=2024",
                        "-Cpanic=abort",
                        "-Coverflow-checks=yes",
                    ])
                    .arg(if retained {
                        "-Zalways-encode-mir=yes"
                    } else {
                        "-Zalways-encode-mir=no"
                    })
                    .arg(dependency)
                    .arg("-o")
                    .arg(&library);
                if optimized {
                    compiler.arg("-Copt-level=2");
                }
                if let Some(target) = target {
                    compiler.args(["--target", target]);
                }
                assert!(compiler.output().unwrap().status.success());
                let report = verify(
                    &fixture(),
                    &[(
                        "external_child",
                        if retained {
                            ProofStatus::Proved
                        } else {
                            ProofStatus::Unknown
                        },
                    )],
                    target,
                    optimized,
                    &[
                        "--cfg=external_control".into(),
                        "--extern".into(),
                        format!("stage189_dependency={}", library.display()),
                    ],
                );
                let proof = report
                    .functions
                    .iter()
                    .find(|function| function.name == "external_child")
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                if retained {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|entry| entry.function == "stage189_dependency::selected")
                    );
                } else {
                    assert!(proof.obligations.iter().any(|obligation| obligation.status
                        == ProofStatus::Unknown
                        && obligation.unknown_category
                            == Some(UnknownCategory::MissingCompilerEvidence)
                        && obligation.detail.contains("stage189_dependency::selected")));
                }
            }
        }
    }
}
