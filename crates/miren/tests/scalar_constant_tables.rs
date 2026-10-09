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
            "miren-scalar-constant-tables-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/scalar_constant_tables.rs")
}

fn verify(path: &Path, entries: &[(&str, ProofStatus)], target: Option<&str>, optimized: bool) {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    for (name, _) in entries {
        command.args(["--entry", name]);
    }
    command
        .args(["--", "--crate-type=lib", "--edition=2024"])
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
        entries
            .iter()
            .all(|(_, status)| *status == ProofStatus::Proved)
    );
    for (name, expected) in entries {
        let proof = report
            .functions
            .iter()
            .find(|f| f.name == *name)
            .unwrap()
            .proof
            .as_ref()
            .unwrap();
        assert_eq!(
            proof.status, *expected,
            "{target:?} optimized={optimized} {name}: {:?}",
            proof.obligations
        );
        assert!(proof.trusted_calls.is_empty());
        let boundary = match *name {
            "scalar_budget" | "composite_budget" | "uninitialized_table" => {
                Some("constant array exceeds element budget")
            }
            "total_budget" => Some("constant shape exceeds depth or value budget"),
            _ => None,
        };
        if let Some(boundary) = boundary {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|o| { o.status == ProofStatus::Unknown && o.detail.contains(boundary) }),
                "{name}: {:?}",
                proof.obligations
            );
        }
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|o| o.model.is_some()));
        }
    }
}

#[test]
fn initialized_scalar_tables_preserve_types_bits_and_bounds_on_host_and_arm() {
    let entries = [
        ("table_lookup", ProofStatus::Proved),
        ("float_bits", ProofStatus::Proved),
        ("guarded_lookup", ProofStatus::Proved),
        ("bounds_failure", ProofStatus::Refuted),
        ("scalar_budget", ProofStatus::Unknown),
        ("composite_budget", ProofStatus::Unknown),
        ("total_budget", ProofStatus::Unknown),
        ("uninitialized_table", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized);
        }
    }
}

fn native_tests(path: &Path, directory: &Directory) -> bool {
    let executable = directory.0.join("native");
    let compiler = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
    let output = Command::new(compiler)
        .args(["--test", "--edition=2024"])
        .arg(path)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    Command::new(executable).output().unwrap().status.success()
}

#[test]
fn changing_a_table_value_or_nan_payload_fails_static_and_native_checks() {
    assert!(native_tests(&fixture(), &Directory::new()));
    for (original, replacement, entry) in [
        (
            "table[index] = index as u16;",
            "table[index] = (index as u16) ^ 1;",
            "table_lookup",
        ),
        (
            "FLOATS[index as usize].to_bits() == 0x7fc0_1234",
            "FLOATS[index as usize].to_bits() == 0x7fc0_1235",
            "float_bits",
        ),
        ("if index < 256 {", "if index <= 256 {", "guarded_lookup"),
    ] {
        let directory = Directory::new();
        let mutant = directory.0.join("mutant.rs");
        let source = std::fs::read_to_string(fixture()).unwrap();
        assert!(source.contains(original));
        std::fs::write(&mutant, source.replacen(original, replacement, 1)).unwrap();
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for optimized in [false, true] {
                verify(&mutant, &[(entry, ProofStatus::Refuted)], target, optimized);
            }
        }
        assert!(!native_tests(&mutant, &directory));
    }
}
