#![forbid(unsafe_code)]
use miren::{ProofStatus, Report, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Directory(PathBuf);
impl Directory {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "miren-function-tables-{}-{}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/function_tables.rs")
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
            "--crate-name=function_tables",
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
fn correlated_tables_execute_actual_bodies_and_keep_unsupported_targets_unknown() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    let entries = [
        ("selected", P),
        ("duplicates", P),
        ("field", P),
        ("second_call", P),
        ("wrong", R),
        ("opaque", U),
        ("wide", U),
        ("shared", U),
        ("excessive", U),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&fixture(), &entries, target, optimized, &[]);
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "selected")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            for helper in ["first", "second"] {
                assert!(
                    proof
                        .body_entries
                        .iter()
                        .any(|entry| entry.function == helper)
                );
            }
        }
    }
}

fn native(source: &Path, optimized: bool, mutant: bool) {
    let directory = Directory::new();
    let executable = directory.0.join("native");
    let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
    compiler
        .args(["--test", "--edition=2024"])
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
    let mut child = Command::new(executable)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let start = std::time::Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if start.elapsed() >= std::time::Duration::from_secs(10) {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("finite native table fixture exceeded ten seconds");
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    };
    assert_eq!(status.code(), Some(if mutant { 101 } else { 0 }));
}

#[test]
fn actual_helper_and_table_order_mutations_refute_the_unchanged_assertion() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
    }
    for (name, old, new) in [
        ("helper", "value ^ 1 }", "value ^ 3 }"),
        ("order", "[first,second]", "[second,first]"),
    ] {
        assert!(source.contains(old));
        let mutant = directory.0.join(format!("{name}.rs"));
        std::fs::write(&mutant, source.replacen(old, new, 1)).unwrap();
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for optimized in [false, true] {
                verify(
                    &mutant,
                    &[("selected", ProofStatus::Refuted)],
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
}

#[test]
fn feasible_external_targets_require_mir_and_infeasible_targets_are_pruned() {
    let directory = Directory::new();
    let dependency = directory.0.join("dependency.rs");
    let source = directory.0.join("external.rs");
    std::fs::write(
        &dependency,
        "#![no_std]\n#![forbid(unsafe_code)]\n\
        #[inline(never)] pub fn first(value: u16) -> u16 {value}\n\
        #[inline(never)] pub fn second(value: u16) -> u16 {value ^ 1}\n",
    )
    .unwrap();
    std::fs::write(
        &source,
        r#"#![no_std]
#![forbid(unsafe_code)]
pub fn external(index: usize, value: u16) {
    let table: [fn(u16)->u16;2] = [fn_table_external::first, fn_table_external::second];
    if index < 2 {assert!(table[index](value) == if index == 0 {value} else {value ^ 1});}
}
#[inline(never)] pub fn local(value: u16) -> u16 {value}
pub fn infeasible_external(index: usize, value: u16) {
    let table: [fn(u16)->u16;2] = [local, fn_table_external::second];
    if index == 0 {assert!(table[index](value) == value);}
}
"#,
    )
    .unwrap();
    for retained in [false, true] {
        for target in [None, Some("thumbv7em-none-eabihf")] {
            let archive = directory.0.join("libfn_table_external.rlib");
            let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
            compiler
                .args([
                    "--crate-type=rlib",
                    "--crate-name=fn_table_external",
                    "--edition=2024",
                    "-Cpanic=abort",
                    "-Copt-level=0",
                ])
                .arg(if retained {
                    "-Zalways-encode-mir=yes"
                } else {
                    "-Zalways-encode-mir=no"
                })
                .arg(&dependency)
                .arg("-o")
                .arg(&archive);
            if let Some(target) = target {
                compiler.args(["--target", target]);
            }
            let output = compiler.output().unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            let extra = [
                "--extern".into(),
                format!("fn_table_external={}", archive.display()),
            ];
            for optimized in [false, true] {
                let report = verify(
                    &source,
                    &[
                        (
                            "external",
                            if retained {
                                ProofStatus::Proved
                            } else {
                                ProofStatus::Unknown
                            },
                        ),
                        ("infeasible_external", ProofStatus::Proved),
                    ],
                    target,
                    optimized,
                    &extra,
                );
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == "external")
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                if retained {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|e| e.function == "fn_table_external::second")
                    );
                } else {
                    assert!(
                        proof.obligations.iter().any(|o| o.unknown_category
                            == Some(UnknownCategory::MissingCompilerEvidence))
                    );
                }
            }
        }
    }
}
