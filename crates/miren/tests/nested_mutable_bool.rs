#![forbid(unsafe_code)]
use miren::{ProofStatus, Report};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Directory(PathBuf);
impl Directory {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "miren-nested-bool-{}-{}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/nested_mutable_bool.rs")
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
            "--crate-name=nested_mutable_bool",
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

fn run_native(executable: &Path) -> std::process::Output {
    let mut child = Command::new(executable)
        .arg("--test-threads=1")
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let started = std::time::Instant::now();
    loop {
        if child.try_wait().unwrap().is_some() {
            return child.wait_with_output().unwrap();
        }
        if started.elapsed() >= std::time::Duration::from_secs(10) {
            child.kill().unwrap();
            let _ = child.wait();
            panic!("native Boolean guard exceeded ten seconds");
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
}

#[test]
fn bool_and_char_hierarchies_use_actual_bodies() {
    let entries: Vec<_> = ["boolean", "character"]
        .into_iter()
        .flat_map(|module| {
            [
                "selected",
                "sibling",
                "scalar_return",
                "wrong",
                "bounds",
                "deeper",
            ]
            .into_iter()
            .map(move |entry| {
                let status = match entry {
                    "selected" | "sibling" | "scalar_return" => ProofStatus::Proved,
                    "wrong" | "bounds" => ProofStatus::Refuted,
                    "deeper" => ProofStatus::Unknown,
                    _ => unreachable!(),
                };
                (format!("{module}::{entry}"), status)
            })
        })
        .collect();
    let entries: Vec<_> = entries
        .iter()
        .map(|(name, status)| (name.as_str(), *status))
        .collect();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&fixture(), &entries, target, optimized, &[]);
            for root in [
                "boolean::selected",
                "boolean::sibling",
                "boolean::scalar_return",
            ] {
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == root)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                for name in ["boolean::outer", "boolean::leaf", "boolean::scalar"] {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|entry| entry.function == name)
                    );
                }
            }
        }
    }
}

#[test]
fn actual_bool_helper_mutation_has_a_native_guard() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    assert_eq!(source.matches("word ^ false").count(), 1);
    let mutated = directory.0.join("mutant.rs");
    std::fs::write(&mutated, source.replace("word ^ false", "word ^ true")).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &mutated,
                &[
                    ("boolean::selected", ProofStatus::Refuted),
                    ("boolean::sibling", ProofStatus::Refuted),
                    ("boolean::scalar_return", ProofStatus::Refuted),
                ],
                target,
                optimized,
                &[],
            );
        }
    }
    for optimized in [false, true] {
        for (source, success) in [(fixture(), true), (mutated.clone(), false)] {
            let executable = directory.0.join("native");
            assert!(
                Command::new("rustc")
                    .args(["--test", "--edition=2024"])
                    .arg(&source)
                    .arg("-o")
                    .arg(&executable)
                    .arg(if optimized {
                        "-Copt-level=2"
                    } else {
                        "-Copt-level=0"
                    })
                    .status()
                    .unwrap()
                    .success()
            );
            let output = run_native(&executable);
            assert_eq!(output.status.code(), Some(if success { 0 } else { 101 }));
            assert!(String::from_utf8_lossy(&output.stdout).contains("running 2 tests"));
        }
    }
}

#[test]
fn genuine_nested_bool_dependency_availability_precedes_empty_shortcuts() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for library_optimized in [false, true] {
            for retained in [false, true] {
                let directory = Directory::new();
                let library = directory.0.join("libnested_bool_dependency.rlib");
                let mut compiler = Command::new("rustc");
                compiler
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=nested_bool_dependency",
                        "--edition=2024",
                        "-Cpanic=abort",
                        "-Coverflow-checks=yes",
                    ])
                    .arg(if retained {
                        "-Zalways-encode-mir=yes"
                    } else {
                        "-Zalways-encode-mir=no"
                    })
                    .arg(root.join("nested_mutable_bool_dependency.rs"))
                    .arg("-o")
                    .arg(&library)
                    .arg(if library_optimized {
                        "-Copt-level=2"
                    } else {
                        "-Copt-level=0"
                    });
                if let Some(target) = target {
                    compiler.args(["--target", target]);
                }
                assert!(compiler.output().unwrap().status.success());
                for caller_optimized in [false, true] {
                    let report = verify(
                        &root.join("nested_mutable_bool_foreign.rs"),
                        &[
                            (
                                "selected",
                                if retained {
                                    ProofStatus::Proved
                                } else {
                                    ProofStatus::Unknown
                                },
                            ),
                            (
                                "empty",
                                if retained {
                                    ProofStatus::Proved
                                } else {
                                    ProofStatus::Unknown
                                },
                            ),
                        ],
                        target,
                        caller_optimized,
                        &[
                            "--extern".into(),
                            format!("nested_bool_dependency={}", library.display()),
                        ],
                    );
                    for name in ["selected", "empty"] {
                        let proof = report
                            .functions
                            .iter()
                            .find(|f| f.name == name)
                            .unwrap()
                            .proof
                            .as_ref()
                            .unwrap();
                        if !retained {
                            assert!(proof.obligations.iter().any(|o| o.status
                                == ProofStatus::Unknown
                                && o.unknown_category
                                    == Some(miren::UnknownCategory::MissingCompilerEvidence)
                                && o.detail.contains("nested_bool_dependency::outer")));
                        } else {
                            assert!(
                                proof
                                    .body_entries
                                    .iter()
                                    .any(|e| e.function == "nested_bool_dependency::outer")
                            );
                        }
                    }
                }
            }
        }
    }
}
