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
            "miren-local-associated-{}-{}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/local_associated_hierarchy.rs")
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
            "--crate-name=local_associated_hierarchy",
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
            panic!("native associated guard exceeded ten seconds");
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
}

#[test]
fn local_associated_calls_follow_actual_available_bodies() {
    use ProofStatus::{Proved, Refuted, Unknown};
    let entries = [
        ("inherent", Proved),
        ("wrong_inherent", Refuted),
        ("implemented", Proved),
        ("wrong_implemented", Refuted),
        ("defaulted", Proved),
        ("wrong_defaulted", Refuted),
        ("generic", Proved),
        ("wrong_generic", Refuted),
        ("deeper", Proved),
        ("wrong_deeper", Refuted),
        ("retained", Unknown),
        ("direct_scalar", Proved),
        ("wrong_direct_scalar", Refuted),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized, &[]);
        }
    }
}

#[test]
fn actual_associated_scalar_mutation_has_a_native_guard() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    assert_eq!(source.matches("word ^ 0").count(), 2);
    let mutant = source.replace("word ^ 0", "word ^ 1");
    let compiler_mutant = directory.0.join("compiler-mutant.rs");
    std::fs::write(&compiler_mutant, &mutant).unwrap();
    let entries = [
        "inherent",
        "implemented",
        "defaulted",
        "generic",
        "direct_scalar",
    ]
    .map(|name| (name, ProofStatus::Refuted));
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&compiler_mutant, &entries, target, optimized, &[]);
            for function in report
                .functions
                .iter()
                .filter(|function| function.proof.is_some())
            {
                assert!(
                    function
                        .proof
                        .as_ref()
                        .unwrap()
                        .body_entries
                        .iter()
                        .any(|entry| entry.function.ends_with("::scalar"))
                );
            }
        }
    }
    for (name, source, expected) in [("original", source, 0), ("mutant", mutant, 101)] {
        let path = directory.0.join(format!("{name}.rs"));
        std::fs::write(&path, source).unwrap();
        for optimized in [false, true] {
            let executable = directory.0.join(format!("{name}-{optimized}"));
            let mut compiler = Command::new("rustc");
            compiler
                .args(["--test", "--edition=2024", "-Coverflow-checks=yes"])
                .arg(&path)
                .arg("-o")
                .arg(&executable);
            if optimized {
                compiler.arg("-Copt-level=2");
            }
            assert!(compiler.status().unwrap().success());
            let output = run_native(&executable);
            assert_eq!(output.status.code(), Some(expected));
            assert!(String::from_utf8_lossy(&output.stdout).contains("running 1 test"));
        }
    }
}

#[test]
fn associated_outer_requires_available_foreign_body_even_when_empty() {
    let dependency = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/local_associated_hierarchy_dependency.rs");
    let source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/local_associated_hierarchy_foreign.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [true, false] {
                let directory = Directory::new();
                let archive = directory.0.join("liblocal_associated_dependency.rlib");
                let mut compiler = Command::new("rustc");
                compiler
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=local_associated_dependency",
                        "--edition=2024",
                        "-Cpanic=abort",
                        "-Coverflow-checks=yes",
                    ])
                    .arg(if retained {
                        "-Zalways-encode-mir=yes"
                    } else {
                        "-Zalways-encode-mir=no"
                    })
                    .arg(&dependency)
                    .arg("-o")
                    .arg(&archive);
                if optimized {
                    compiler.arg("-Copt-level=2");
                }
                if let Some(target) = target {
                    compiler.args(["--target", target]);
                }
                assert!(compiler.status().unwrap().success());
                let selected = if retained {
                    ProofStatus::Proved
                } else {
                    ProofStatus::Unknown
                };
                let empty = if retained {
                    ProofStatus::Proved
                } else {
                    ProofStatus::Unknown
                };
                let report = verify(
                    &source,
                    &[("selected", selected), ("empty", empty)],
                    target,
                    optimized,
                    &[
                        "--extern".into(),
                        format!("local_associated_dependency={}", archive.display()),
                    ],
                );
                for function in report
                    .functions
                    .iter()
                    .filter(|function| function.proof.is_some())
                {
                    let proof = function.proof.as_ref().unwrap();
                    if !retained {
                        assert!(proof.obligations.iter().any(|obligation| {
                            obligation.detail.contains(
                                "MIR body unavailable for local_associated_dependency::leaf",
                            )
                        }));
                    } else {
                        assert!(
                            proof
                                .body_entries
                                .iter()
                                .any(|entry| entry.function == "local_associated_dependency::leaf")
                        );
                    }
                }
            }
        }
    }
}
