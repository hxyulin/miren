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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/mutable_bool_slices.rs")
}
fn verify(
    source: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    extra: &[String],
) -> Report {
    verify_contract(source, entries, target, optimized, extra, None)
}
fn verify_contract(
    source: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    extra: &[String],
    predicate: Option<&str>,
) -> Report {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    if let Some(predicate) = predicate {
        let config = directory.0.join("contracts.json");
        std::fs::write(
            &config,
            serde_json::to_vec(&serde_json::json!({
                "schema_version": 1, "functions": [{
                    "function": "mutable_bool_slices::ghost_length",
                    "arguments": ["values"], "ensures": [predicate]
                }]
            }))
            .unwrap(),
        )
        .unwrap();
        command.arg("--contracts").arg(config);
    }

    for (name, _) in entries {
        command.args(["--entry", name]);
    }
    command
        .args([
            "--",
            "--crate-type=lib",
            "--crate-name=mutable_bool_slices",
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
fn logical_bool_stores_and_actual_child_bodies_cover_four_profiles() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    let entries = [
        ("selected", P),
        ("direct", P),
        ("untouched", P),
        ("sequential", P),
        ("branches", P),
        ("returned", P),
        ("empty", P),
        ("ghost_length", P),
        ("wrong", R),
        ("bounds", R),
        ("child_assertion", R),
        ("wrong_sibling", R),
        ("reached_panic", U),
        ("competing", U),
        ("shared", U),
        ("raw", U),
        ("escape", U),
        ("nested", U),
        ("char_unknown", U),
        ("float_unknown", U),
        ("u8_unknown", P),
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
            for name in ["child", "replacement"] {
                assert!(proof.body_entries.iter().any(|e| e.function == name));
            }
            for (name, detail) in [
                (
                    "competing",
                    "one original borrow and owned primitive inputs",
                ),
                ("shared", "metadata needs original direct root"),
                ("raw", "child needs direct abort-only Rust body"),
                ("escape", "staging needs a private whole tip"),
                ("nested", "mutable bool staging needs a pending child"),
                (
                    "reached_panic",
                    "ancestor admits only direct scalar Rust frames",
                ),
                (
                    "char_unknown",
                    "mutable u16 roles require selected metadata-only operation",
                ),
                (
                    "float_unknown",
                    "only read-only byte slices and byte arrays are modeled",
                ),
            ] {
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == name)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert!(
                    proof
                        .obligations
                        .iter()
                        .any(|o| o.unknown_category == Some(UnknownCategory::Semantics)
                            && o.detail.contains(detail))
                );
            }
        }
    }
}

#[test]
fn detached_bool_ghost_contracts_observe_length_without_executable_index_rights() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for (predicate, status) in [
                ("final_values.len() == values.len()", ProofStatus::Proved),
                ("final_values.len() != values.len()", ProofStatus::Refuted),
                ("values[0] == true", ProofStatus::Unknown),
            ] {
                verify_contract(
                    &fixture(),
                    &[("ghost_length", status)],
                    target,
                    optimized,
                    &[],
                    Some(predicate),
                );
            }
        }
    }
}

#[test]
fn actual_bool_helper_mutation_refutes_and_fails_valid_129_element_native() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    let pattern = "pub fn replacement(value: bool) -> bool {\n    !value\n}";
    assert_eq!(source.matches(pattern).count(), 1);
    let mutant = directory.0.join("mutant.rs");
    std::fs::write(
        &mutant,
        source.replace(
            pattern,
            "pub fn replacement(value: bool) -> bool {\n    value\n}",
        ),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(
                &mutant,
                &[("selected", ProofStatus::Refuted)],
                target,
                optimized,
                &[],
            );
            assert!(
                report
                    .functions
                    .iter()
                    .find(|f| f.name == "selected")
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap()
                    .body_entries
                    .iter()
                    .any(|e| e.function == "replacement")
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
fn external_bool_child_requires_actual_selected_compiler_body() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let directory = Directory::new();
                let library = directory.0.join("libstage192_dependency.rlib");
                let dependency = fixture().with_file_name("mutable_bool_dependency.rs");
                let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
                compiler
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=stage192_dependency",
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
                        "external_bool",
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
                        format!("stage192_dependency={}", library.display()),
                    ],
                );
                let proof = report
                    .functions
                    .iter()
                    .find(|function| function.name == "external_bool")
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                if retained {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|entry| entry.function == "stage192_dependency::selected")
                    );
                } else {
                    assert!(proof.obligations.iter().any(|obligation| obligation.status
                        == ProofStatus::Unknown
                        && obligation.unknown_category
                            == Some(UnknownCategory::MissingCompilerEvidence)
                        && obligation.detail.contains("stage192_dependency::selected")));
                }
            }
        }
    }
}
