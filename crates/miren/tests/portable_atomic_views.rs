#![forbid(unsafe_code)]

use miren::{ProofStatus, Report};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct Directory(PathBuf);

impl Directory {
    fn new(source: &str) -> Self {
        let id = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("miren-portable-atomic-{}-{id}", std::process::id()));
        std::fs::create_dir_all(path.join("src")).unwrap();
        std::fs::write(path.join("src/lib.rs"), source).unwrap();
        std::fs::write(
            path.join("Cargo.toml"),
            concat!(
                "[package]\nname='portable-atomic-fixture'\nversion='0.0.0'\nedition='2024'\n",
                "[workspace]\n[dependencies]\nportable-atomic='=1.15.0'\nstatic_cell='=2.1.1'\n",
                "[profile.release]\noverflow-checks=true\n"
            ),
        )
        .unwrap();
        Self(path)
    }
}

impl Drop for Directory {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn fixture() -> String {
    std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/portable_atomic_views.rs"),
    )
    .unwrap()
}

fn verify(directory: &Directory, target: Option<&str>, optimized: bool) {
    let entries = [
        ("matching_cas", ProofStatus::Proved),
        ("wrong_cas", ProofStatus::Refuted),
        ("invalid_ordering", ProofStatus::Refuted),
        ("core_bool", ProofStatus::Unknown),
        ("uninitialized_payload", ProofStatus::Unknown),
        ("possibly_already_full", ProofStatus::Refuted),
        ("numeric_address", ProofStatus::Unknown),
        ("lookalike_restricted_cell", ProofStatus::Unknown),
    ];
    verify_entries(directory, target, optimized, &entries);
}

fn verify_entries(
    directory: &Directory,
    target: Option<&str>,
    optimized: bool,
    entries: &[(&str, ProofStatus)],
) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_cargo-miren"));
    command.args(["--verify", "--quiet"]);
    for &(name, _) in entries {
        command.args(["--entry", name]);
    }
    command
        .args(["--", "--offline", "--manifest-path"])
        .arg(directory.0.join("Cargo.toml"));
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    if optimized {
        command.arg("--release");
    }
    let output = command.output().unwrap();
    let text = format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let reports = text
        .lines()
        .find_map(|line| line.strip_prefix("JSON reports: "))
        .unwrap_or_else(|| panic!("{text}\n{}", String::from_utf8_lossy(&output.stderr)));
    let files = std::fs::read_dir(reports)
        .unwrap()
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    assert_eq!(files.len(), 1);
    let report: Report = serde_json::from_slice(&std::fs::read(files[0].path()).unwrap()).unwrap();
    for &(name, expected) in entries {
        let function = report.functions.iter().find(|f| f.name == name).unwrap();
        let proof = function.proof.as_ref().unwrap();
        assert_eq!(
            proof.status, expected,
            "{target:?} optimized={optimized} {name}: {:?}",
            proof.obligations
        );
        assert!(proof.assumptions.is_empty());
        assert!(proof.entry_assumptions.is_empty());
        assert!(proof.trusted_calls.is_empty());
        if expected != ProofStatus::Unknown
            && matches!(name, "matching_cas" | "wrong_cas" | "possibly_already_full")
        {
            assert!(proof.models.iter().any(|model| {
                model.contains("body-certified portable AtomicBool shared byte-atomic view")
            }));
        }
        if expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|o| o.model.is_some()));
        }
        if expected == ProofStatus::Refuted && matches!(name, "wrong_cas" | "possibly_already_full")
        {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| !o.abstraction_reasons.is_empty())
            );
        }
        if name == "uninitialized_payload" {
            assert!(
                proof.obligations.iter().any(|o| {
                    o.status == ProofStatus::Unknown
                        && o.detail.contains("core::mem::MaybeUninit")
                        && o.detail.contains("unsupported aggregate kind")
                }),
                "{:?}",
                proof.obligations
            );
        }
        if name == "matching_cas" && expected == ProofStatus::Unknown {
            assert!(proof.obligations.iter().any(|o| {
                o.detail
                    .contains("atomic byte wrapper actual method has unsupported control flow")
            }));
            assert!(!proof.models.iter().any(|model| {
                model.contains("body-certified portable AtomicBool shared byte-atomic view")
            }));
        }
    }
}

#[test]
fn actual_portable_atomic_bodies_preserve_cas_outcomes_and_refuse_uninitialized_payloads() {
    let directory = Directory::new(&fixture());
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&directory, target, optimized);
        }
    }
    changed_dependency_body_is_unknown();
}

fn copy_dependency(source: &Path, target: &Path) {
    std::fs::create_dir_all(target).unwrap();
    for entry in std::fs::read_dir(source).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_dir() {
            copy_dependency(&entry.path(), &target.join(entry.file_name()));
        } else {
            std::fs::copy(entry.path(), target.join(entry.file_name())).unwrap();
        }
    }
}

fn changed_dependency_body_is_unknown() {
    let directory = Directory::new(&fixture());
    let output = Command::new("cargo")
        .args([
            "metadata",
            "--offline",
            "--format-version=1",
            "--manifest-path",
        ])
        .arg(directory.0.join("Cargo.toml"))
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let metadata: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    let package = metadata["packages"]
        .as_array()
        .unwrap()
        .iter()
        .find(|package| package["name"] == "portable-atomic")
        .unwrap();
    let manifest = Path::new(package["manifest_path"].as_str().unwrap());
    let copied = directory.0.join("changed-portable");
    copy_dependency(manifest.parent().unwrap(), &copied);
    let source_path = copied.join("src/lib.rs");
    let source = std::fs::read_to_string(&source_path).unwrap();
    let changed = source.replace(
        "unsafe { &*(self as *const Self as *const imp::AtomicU8) }",
        "panic!(\"changed conversion body\")",
    );
    assert_ne!(source, changed);
    std::fs::write(source_path, changed).unwrap();
    let manifest_path = directory.0.join("Cargo.toml");
    let mut manifest = std::fs::read_to_string(&manifest_path).unwrap();
    manifest.push_str("\n[patch.crates-io]\nportable-atomic={path='changed-portable'}\n");
    std::fs::write(manifest_path, manifest).unwrap();
    verify_entries(
        &directory,
        None,
        false,
        &[("matching_cas", ProofStatus::Unknown)],
    );
}

#[test]
fn actual_native_cas_and_used_cell_controls_pass_and_the_value_mutation_fails() {
    for optimized in [false, true] {
        let directory = Directory::new(&fixture());
        let mut command = Command::new("cargo");
        command
            .args(["test", "--offline", "--manifest-path"])
            .arg(directory.0.join("Cargo.toml"));
        if optimized {
            command.arg("--release");
        }
        let output = command.output().unwrap();
        assert!(output.status.success(), "{output:?}");
        let mutated = fixture().replace(
            "assert!(matches!(result, Ok(false) | Err(true)));",
            "assert!(matches!(result, Ok(true) | Err(false)));",
        );
        assert_ne!(mutated, fixture());
        std::fs::write(directory.0.join("src/lib.rs"), mutated).unwrap();
        let output = command.output().unwrap();
        assert!(
            !output.status.success(),
            "mutation unexpectedly passed: {output:?}"
        );
        assert!(String::from_utf8_lossy(&output.stdout).contains("FAILED"));
    }
}
