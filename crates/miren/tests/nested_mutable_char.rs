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
            "miren-nested-char-{}-{}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/nested_mutable_char.rs")
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
            "--crate-name=nested_mutable_char",
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
            panic!("native Char guard exceeded ten seconds");
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
}

#[test]
fn char_hierarchy_executes_actual_bodies_and_preserves_deeper_effects() {
    let entries = [
        ("character::selected", ProofStatus::Proved),
        ("character::sibling", ProofStatus::Proved),
        ("character::scalar_return", ProofStatus::Proved),
        ("character::wrong", ProofStatus::Refuted),
        ("character::bounds", ProofStatus::Refuted),
        ("character::deeper", ProofStatus::Proved),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&fixture(), &entries, target, optimized, &[]);
            for name in [
                "character::selected",
                "character::sibling",
                "character::scalar_return",
            ] {
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == name)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                for body in ["character::outer", "character::leaf", "character::scalar"] {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|entry| entry.function == body)
                    );
                }
            }
        }
    }
}

#[test]
fn actual_char_helper_mutation_has_a_valid_unicode_native_guard() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "if word == '\\0' { '\\0' } else { word }";
    assert_eq!(source.matches(original).count(), 1);
    let mutated = directory.0.join("mutant.rs");
    std::fs::write(
        &mutated,
        source.replace(original, "if word == '\\0' { 'B' } else { word }"),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &mutated,
                &[
                    ("character::selected", ProofStatus::Refuted),
                    ("character::sibling", ProofStatus::Refuted),
                    ("character::scalar_return", ProofStatus::Refuted),
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
                    .args(["--test", "--edition=2024", "-Coverflow-checks=yes"])
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
            assert!(String::from_utf8_lossy(&output.stdout).contains("running 1 test"));
        }
    }
}

#[test]
fn genuine_char_dependency_requires_bodies_even_for_empty_callers() {
    let directory = Directory::new();
    let library_source = directory.0.join("library.rs");
    let caller = directory.0.join("caller.rs");
    std::fs::write(
        &library_source,
        r"#![no_std]
#![forbid(unsafe_code)]
#[inline(never)]
fn word(v: char) -> char { if v == '\0' { '\0' } else { v } }
#[inline(never)]
fn leaf(v: &mut [char]) { if v.len() > 0 { v[0] = word(v[0]); } }
#[inline(never)]
pub fn outer(v: &mut [char]) { leaf(&mut *(&mut *v)); }
",
    )
    .unwrap();
    std::fs::write(
        &caller,
        r"#![no_std]
#![forbid(unsafe_code)]
extern crate char_dependency;
pub fn selected(v: &mut [char]) {
    if v.len() > 0 && v[0] == '\0' { char_dependency::outer(v); assert!(v[0] == '\0'); }
}
pub fn empty(v: &mut [char]) {
    if v.len() == 0 { char_dependency::outer(v); assert!(v.len() == 0); }
}
",
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let library = directory.0.join("libchar_dependency.rlib");
                let mut compiler = Command::new("rustc");
                compiler
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=char_dependency",
                        "--edition=2024",
                        "-Cpanic=abort",
                    ])
                    .arg(&library_source)
                    .arg("-o")
                    .arg(&library)
                    .arg(if optimized {
                        "-Copt-level=2"
                    } else {
                        "-Copt-level=0"
                    })
                    .arg(if retained {
                        "-Zalways-encode-mir=yes"
                    } else {
                        "-Zalways-encode-mir=no"
                    });
                if let Some(target) = target {
                    compiler.args(["--target", target]);
                }
                assert!(compiler.output().unwrap().status.success());
                let report = verify(
                    &caller,
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
                    optimized,
                    &[
                        "--extern".into(),
                        format!("char_dependency={}", library.display()),
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
                    if retained {
                        assert!(
                            proof
                                .body_entries
                                .iter()
                                .any(|e| e.function == "char_dependency::outer")
                        );
                    } else {
                        assert!(
                            proof
                                .obligations
                                .iter()
                                .any(|o| o.status == ProofStatus::Unknown
                                    && o.unknown_category
                                        == Some(miren::UnknownCategory::MissingCompilerEvidence)
                                    && o.detail.contains("char_dependency::outer"))
                        );
                    }
                }
            }
        }
    }
}
