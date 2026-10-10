#![forbid(unsafe_code)]

use miren::{ProofStatus, Report};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct Directory(PathBuf);

impl Directory {
    fn new() -> Self {
        let id = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "miren-isolated-startup-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/isolated_startup.rs")
}

fn verify(
    path: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    startup: bool,
) -> Report {
    verify_with_specification(path, entries, target, optimized, startup, None)
}

fn verify_with_specification(
    path: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    startup: bool,
    specification: Option<serde_json::Value>,
) -> Report {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    if startup {
        command.args(["--startup-isolated", "--allow-assumptions"]);
    }
    if let Some(specification) = &specification {
        let path = directory.0.join("contracts.json");
        std::fs::write(&path, serde_json::to_vec(specification).unwrap()).unwrap();
        command.arg("--contracts").arg(path);
    }
    for (name, _) in entries {
        command.args([
            if *name == "async_factory" {
                "--async-entry"
            } else {
                "--entry"
            },
            name,
        ]);
    }
    command
        .args([
            "--",
            "--crate-name=isolated_startup",
            "--crate-type=lib",
            "--edition=2024",
        ])
        .arg(path)
        .arg("--out-dir")
        .arg(&directory.0)
        .args(["-Cpanic=abort", "-Coverflow-checks=yes"]);
    if optimized {
        command.arg("-Copt-level=2");
    }
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    let output = command.output().unwrap();
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    assert_eq!(
        output.status.success(),
        entries.iter().all(|(_, status)| matches!(
            status,
            ProofStatus::Proved | ProofStatus::ProvedWithAssumptions
        ))
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
            "{target:?} optimized={optimized} {name}: {:?}",
            proof.obligations
        );
        assert_eq!(
            proof.trusted_calls.len(),
            usize::from(specification.is_some())
        );
        assert_eq!(
            !proof.entry_assumptions.is_empty(),
            startup && *name != "async_factory"
        );
    }
    report
}

#[test]
fn isolated_static_history_retains_actual_writes_and_preserves_boundaries() {
    let entries = [
        (
            "isolated_publication_keeps_disjoint_initializers",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "isolated_callback_store_executes_the_actual_function",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "overwritten_parent_cannot_resurrect_a_child_initializer",
            ProofStatus::Refuted,
        ),
        ("async_factory", ProofStatus::Unknown),
        ("root_with_argument", ProofStatus::Unknown),
        (
            "isolated_retirement_preserves_disjoint_history_and_requires_reinitialization",
            ProofStatus::ProvedWithAssumptions,
        ),
        (
            "isolated_retired_payload_reads_are_unknown",
            ProofStatus::ProvedWithAssumptions,
        ),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&fixture(), &entries, target, optimized, true);
            for proof in report
                .functions
                .iter()
                .filter_map(|function| function.proof.as_ref())
            {
                if !proof.entry_assumptions.is_empty() {
                    assert!(
                        proof
                            .entry_assumptions
                            .iter()
                            .any(|reason| reason.contains("Isolated startup"))
                    );
                }
            }
        }
    }
}

#[test]
fn isolated_opaque_effects_discard_known_and_unseen_history() {
    let specification = serde_json::json!({"schema_version":1,"functions":[{
        "function":"isolated_startup::boundary", "trusted":true,"no_panic":true,
        "modifies":[],"reason":"Explicit opaque boundary for isolated initialization"
    }]});
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify_with_specification(
                &fixture(),
                &[
                    (
                        "isolated_opaque_calls_discard_unseen_initializers",
                        ProofStatus::Refuted,
                    ),
                    (
                        "isolated_opaque_calls_discard_written_callbacks",
                        ProofStatus::Refuted,
                    ),
                ],
                target,
                optimized,
                true,
                Some(specification.clone()),
            );
        }
    }
}

#[test]
fn callback_mutations_refute_conditional_and_native_results() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    let original = "value + 2";
    assert_eq!(source.matches(original).count(), 1);
    let mutant = directory.0.join("mutant.rs");
    std::fs::write(&mutant, source.replace(original, "value + 3")).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &mutant,
                &[(
                    "isolated_callback_store_executes_the_actual_function",
                    ProofStatus::Refuted,
                )],
                target,
                optimized,
                true,
            );
        }
    }
    for (path, success) in [(fixture(), true), (mutant, false)] {
        let executable = directory.0.join("native-callback");
        let output = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"))
            .args(["--test", "--edition=2024"])
            .arg(path)
            .arg("-o")
            .arg(&executable)
            .output()
            .unwrap();
        assert!(output.status.success(), "{output:?}");
        let output = Command::new(&executable)
            .args(["--exact", "native_callback_store"])
            .output()
            .unwrap();
        assert!(String::from_utf8_lossy(&output.stdout).contains("running 1 test"));
        assert_eq!(output.status.success(), success, "{output:?}");
    }
}

#[test]
fn cargo_configuration_records_isolation_and_cli_can_clear_it() {
    let directory = Directory::new();
    std::fs::create_dir(directory.0.join("src")).unwrap();
    std::fs::write(
        directory.0.join("Cargo.toml"),
        "[package]\nname='isolated-init'\nversion='0.0.0'\nedition='2024'\n[workspace]\n",
    )
    .unwrap();
    std::fs::copy(fixture(), directory.0.join("src/lib.rs")).unwrap();
    let configuration = serde_json::json!({"schema_version":1,
        "entries":["isolated_publication_keeps_disjoint_initializers"],
        "startup_isolated":true,"allow_assumptions":true,"dependency_mir":false});
    std::fs::write(
        directory.0.join("miren.json"),
        serde_json::to_vec(&configuration).unwrap(),
    )
    .unwrap();
    let run = |extra: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_cargo-miren"))
            .args(["--verify", "--quiet"])
            .args(extra)
            .current_dir(&directory.0)
            .output()
            .unwrap()
    };
    let output = run(&[]);
    assert!(output.status.success(), "{output:?}");
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("entry assumption: Isolated startup"));
    let reports = text
        .lines()
        .find_map(|line| line.strip_prefix("JSON reports: "))
        .unwrap();
    let path = std::fs::read_dir(reports)
        .unwrap()
        .next()
        .unwrap()
        .unwrap()
        .path();
    let output = Command::new(env!("CARGO_BIN_EXE_miren"))
        .args(["report", "--allow-assumptions", "--quiet"])
        .arg(&path)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(String::from_utf8_lossy(&output.stdout).contains("entry assumption: Isolated startup"));
    let output = run(&["--startup"]);
    assert!(!output.status.success(), "{output:?}");
    assert!(
        !String::from_utf8_lossy(&output.stdout).contains("entry assumption: Isolated startup")
    );
    let output = run(&["--no-startup"]);
    assert!(!output.status.success(), "{output:?}");
    assert!(!String::from_utf8_lossy(&output.stdout).contains("entry assumption:"));
}

#[test]
fn isolated_startup_requires_verification_and_saved_arguments_do_not_enable_it() {
    let output = Command::new(env!("CARGO_BIN_EXE_miren"))
        .args(["--startup-isolated", "--", "--crate-type=lib"])
        .arg(fixture())
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("--startup requires --verify"));
    let report = verify(
        &fixture(),
        &[(
            "isolated_publication_keeps_disjoint_initializers",
            ProofStatus::ProvedWithAssumptions,
        )],
        None,
        false,
        true,
    );
    let directory = Directory::new();
    let path = directory.0.join("saved.json");
    std::fs::write(&path, serde_json::to_vec(&report).unwrap()).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_miren"))
        .args(["--verify", "--json", "--quiet", "--from-report"])
        .arg(path)
        .args([
            "--entry",
            "isolated_publication_keeps_disjoint_initializers",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success(), "{output:?}");
    let report: Report = serde_json::from_slice(&output.stdout).unwrap();
    let proof = report
        .functions
        .iter()
        .find(|function| function.name == "isolated_publication_keeps_disjoint_initializers")
        .unwrap()
        .proof
        .as_ref()
        .unwrap();
    assert!(proof.entry_assumptions.is_empty());
}
