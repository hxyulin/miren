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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/mutable_integer_slices.rs")
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
fn exact_integer_kinds_current_stores_and_child_calls_cover_four_profiles() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    let modules = [
        "signed8",
        "signed16",
        "signed32",
        "signed64",
        "signed128",
        "signed_size",
        "unsigned16",
        "unsigned32",
        "unsigned64",
        "unsigned128",
        "unsigned_size",
    ];
    let names = modules
        .iter()
        .flat_map(|module| {
            [
                "selected",
                "direct",
                "bounds",
                "wrong",
                "untouched",
                "sequential",
                "branches",
                "scalar_return",
                "nested",
                "shared",
            ]
            .map(|root| {
                (
                    format!("{module}::{root}"),
                    match root {
                        "wrong" | "bounds" => R,
                        "nested" => P,
                        "shared" => U,
                        _ => P,
                    },
                )
            })
        })
        .collect::<Vec<_>>();
    let mut entries = names
        .iter()
        .map(|(name, status)| (name.as_str(), *status))
        .collect::<Vec<_>>();
    entries.extend([
        ("bool_unknown", P),
        ("char_unknown", P),
        ("float_unknown", P),
    ]);
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&fixture(), &entries, target, optimized, &[]);
            let proof = report
                .functions
                .iter()
                .find(|function| function.name == "signed32::selected")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| entry.function == "operation_i32")
            );
            for (name, _) in entries
                .iter()
                .filter(|(name, status)| *status == U && name.contains("::"))
            {
                let proof = report
                    .functions
                    .iter()
                    .find(|function| function.name == *name)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert!(
                    proof
                        .obligations
                        .iter()
                        .any(|obligation| obligation.unknown_category
                            == Some(UnknownCategory::Semantics))
                );
            }
        }
    }
}

#[test]
fn actual_integer_helper_mutation_refutes_and_fails_valid_129_element_native() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    let pattern = "pub fn operation_i32(word: i32) -> i32 {\n    word ^ 0\n}";
    assert_eq!(source.matches(pattern).count(), 1);
    let mutant = directory.0.join("mutant.rs");
    std::fs::write(
        &mutant,
        source.replace(
            pattern,
            "pub fn operation_i32(word: i32) -> i32 {\n    word ^ 1\n}",
        ),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(
                &mutant,
                &[("signed32::selected", ProofStatus::Refuted)],
                target,
                optimized,
                &[],
            );
            assert!(
                report
                    .functions
                    .iter()
                    .find(|f| f.name == "signed32::selected")
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap()
                    .body_entries
                    .iter()
                    .any(|e| e.function == "operation_i32")
            );
        }
    }
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
        native(&mutant, optimized, true);
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
fn external_integer_child_requires_actual_selected_compiler_body() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let directory = Directory::new();
                let library = directory.0.join("libstage191_dependency.rlib");
                let dependency = fixture().with_file_name("mutable_integer_dependency.rs");
                let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
                compiler
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=stage191_dependency",
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
                        "external_i32",
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
                        format!("stage191_dependency={}", library.display()),
                    ],
                );
                let proof = report
                    .functions
                    .iter()
                    .find(|function| function.name == "external_i32")
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                if retained {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|entry| entry.function == "stage191_dependency::selected")
                    );
                } else {
                    assert!(proof.obligations.iter().any(|obligation| obligation.status
                        == ProofStatus::Unknown
                        && obligation.unknown_category
                            == Some(UnknownCategory::MissingCompilerEvidence)
                        && obligation.detail.contains("stage191_dependency::selected")));
                }
            }
        }
    }
}
