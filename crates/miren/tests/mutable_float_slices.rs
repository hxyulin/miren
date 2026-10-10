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
            "miren-float-child-{}-{}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/mutable_float_slices.rs")
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
                    "function": "mutable_float_slices::ghost_length",
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
            "--crate-name=mutable_float_slices",
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
fn exact_float_storage_and_actual_child_bodies_cover_four_profiles() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    let entries = [
        ("selected", P),
        ("direct_bits", P),
        ("negate_bits", P),
        ("abs_bits", P),
        ("direct64", P),
        ("negate64", P),
        ("untouched", P),
        ("arithmetic", P),
        ("arithmetic64", P),
        ("branches", P),
        ("signed_zero", P),
        ("nan_payload", P),
        ("returned", P),
        ("empty", P),
        ("ghost_length", P),
        ("wrong", R),
        ("bounds", R),
        ("nan_self", R),
        ("wrong_zero_bits", R),
        ("arithmetic_nan_is_nan", P),
        ("arithmetic_nan_fixed_payload", R),
        ("retained", U),
        ("raw", U),
        ("competing", U),
        ("nested", U),
        ("escape", U),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&fixture(), &entries, target, optimized, &[]);
            for (name, reason) in [
                (
                    "competing",
                    "one original borrow and owned primitive inputs",
                ),
                ("escape", "mutable u16 staging needs a private whole tip"),
                ("nested", "mutable float staging needs a pending child"),
                ("raw", "mutable u16 child needs direct abort-only Rust body"),
                (
                    "retained",
                    "mutable u16 metadata needs original direct root",
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
                        .any(|obligation| obligation.status == U
                            && obligation.unknown_category == Some(UnknownCategory::Semantics)
                            && obligation.detail.contains(reason))
                );
            }
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "selected")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            for function in ["child", "replacement"] {
                assert!(
                    proof
                        .body_entries
                        .iter()
                        .any(|entry| entry.function == function)
                );
            }
        }
    }
}

#[test]
fn detached_float_ghost_contracts_observe_length_without_executable_index_rights() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for (predicate, status) in [
                ("final_values.len() == values.len()", ProofStatus::Proved),
                ("final_values.len() != values.len()", ProofStatus::Refuted),
                ("values[0] == 1.0", ProofStatus::Unknown),
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
fn actual_float_helper_mutation_refutes_and_fails_valid_129_element_native() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    let pattern =
        "pub fn replacement(value: f32) -> f32 {\n    if value == 1.0 { 2.0 } else { 1.0 }\n}";
    assert_eq!(source.matches(pattern).count(), 1);
    let mutant = directory.0.join("mutant.rs");
    std::fs::write(
        &mutant,
        source.replacen(pattern, &pattern.replace("else { 1.0 }", "else { 3.0 }"), 1),
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
fn external_float_child_requires_actual_selected_compiler_body() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let directory = Directory::new();
                let library = directory.0.join("libstage195_dependency.rlib");
                let dependency = fixture().with_file_name("mutable_float_dependency.rs");
                let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
                compiler
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=stage195_dependency",
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
                        "external_float",
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
                        format!("stage195_dependency={}", library.display()),
                    ],
                );
                let proof = report
                    .functions
                    .iter()
                    .find(|function| function.name == "external_float")
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                if retained {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|entry| entry.function == "stage195_dependency::selected")
                    );
                } else {
                    assert!(proof.obligations.iter().any(|obligation| obligation.status
                        == ProofStatus::Unknown
                        && obligation.unknown_category
                            == Some(UnknownCategory::MissingCompilerEvidence)
                        && obligation.detail.contains("stage195_dependency::selected")));
                }
            }
        }
    }
}
