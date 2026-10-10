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
            "miren-checked-interval-{}-{}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/checked_mutable_subslice.rs")
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
            "--crate-name=checked_mutable_subslice",
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
fn checked_intervals_resume_parent_with_current_data() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    let entries = [
        ("selected", P),
        ("wrong", R),
        ("wrong_offset", R),
        ("empty_preserves_payload", P),
        ("untouched", P),
        ("scalar_return", P),
        ("empty", P),
        ("sequential", P),
        ("branches", P),
        ("unguarded", R),
        ("retained_view", U),
        ("nested", U),
        ("whole_anchor", P),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized, &[]);
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
fn actual_interval_child_data_mutation_refutes_and_fails_native_guard() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    let old = "values[index] = word ^ 0;";
    assert_eq!(source.matches(old).count(), 1);
    let mutant = directory.0.join("mutant.rs");
    std::fs::write(&mutant, source.replace(old, "values[index] = word ^ 1;")).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(
                &mutant,
                &[("selected", ProofStatus::Refuted)],
                target,
                optimized,
                &[],
            );
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "selected")
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
    }
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
        native(&mutant, optimized, true);
    }
}

#[test]
fn external_selected_child_requires_genuinely_retained_compiler_body() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let directory = Directory::new();
                let library = directory.0.join("libstage196_dependency.rlib");
                let dependency = fixture().with_file_name("checked_mutable_subslice_dependency.rs");
                let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
                compiler
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=stage196_dependency",
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
                        format!("stage196_dependency={}", library.display()),
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
                            .any(|entry| entry.function == "stage196_dependency::selected")
                    );
                } else {
                    assert!(proof.obligations.iter().any(|obligation| obligation.status
                        == ProofStatus::Unknown
                        && obligation.unknown_category
                            == Some(UnknownCategory::MissingCompilerEvidence)
                        && obligation.detail.contains("stage196_dependency::selected")));
                }
            }
        }
    }
}
