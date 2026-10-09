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
        let path =
            std::env::temp_dir().join(format!("miren-nonzero-options-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/nonzero_options.rs")
}

fn verify(
    path: &Path,
    entries: &[(&str, ProofStatus)],
    target: Option<&str>,
    optimized: bool,
    specification: Option<serde_json::Value>,
) {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    if let Some(specification) = specification {
        let config = directory.0.join("contracts.json");
        std::fs::write(&config, serde_json::to_vec(&specification).unwrap()).unwrap();
        command.arg("--contracts").arg(config);
    }
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
        assert!(proof.entry_assumptions.is_empty());
        if matches!(
            *name,
            "correlated_unsigned"
                | "correlated_signed"
                | "correlated_wide_signed"
                | "correlated_pointer_width"
        ) {
            assert!(
                proof
                    .analyzed_bodies
                    .iter()
                    .any(|body| body.contains("core::num::")
                        && body.contains("NonZero")
                        && body.contains("::new"))
            );
        }
        if *expected == ProofStatus::Refuted {
            assert!(proof.obligations.iter().any(|o| o.model.is_some()));
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
fn compiler_zero_niches_preserve_none_and_exact_some_payloads() {
    let entries = [
        ("correlated_unsigned", ProofStatus::Proved),
        ("correlated_signed", ProofStatus::Proved),
        ("correlated_wide_signed", ProofStatus::Proved),
        ("correlated_pointer_width", ProofStatus::Proved),
        ("unsigned_byte", ProofStatus::Proved),
        ("unsigned_short", ProofStatus::Proved),
        ("unsigned_long", ProofStatus::Proved),
        ("unsigned_wide", ProofStatus::Proved),
        ("signed_byte", ProofStatus::Proved),
        ("signed_word", ProofStatus::Proved),
        ("signed_long", ProofStatus::Proved),
        ("signed_pointer_width", ProofStatus::Proved),
        ("zero_is_none", ProofStatus::Proved),
        ("same_name_constructor_body_runs", ProofStatus::Proved),
        ("negative_is_some", ProofStatus::Proved),
        ("unguarded_unwrap", ProofStatus::Refuted),
        ("zero_unwrap", ProofStatus::Refuted),
        ("wrong_none_claim", ProofStatus::Refuted),
        ("signedness_mismatch", ProofStatus::Unknown),
        ("wrapper_is_not_core_nonzero", ProofStatus::Unknown),
        ("pointer_niche_is_not_integer", ProofStatus::Unknown),
        ("different_niche", ProofStatus::Unknown),
        ("unguarded_some_payload", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized, None);
        }
    }
    assert!(native_tests(&fixture(), &Directory::new()));
    let directory = Directory::new();
    let path = directory.0.join("layout_control.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    let control = r#"
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn mismatched_size(raw: u64) -> Option<NonZeroU32> {
    mir! { { RET = CastTransmute(raw); Return() } }
}
"#;
    std::fs::write(&path, format!("{source}\n{control}")).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &path,
                &[("mismatched_size", ProofStatus::Unknown)],
                target,
                optimized,
                None,
            );
        }
    }
}

#[test]
fn mutating_the_actual_none_claim_refutes_and_fails_native_execution() {
    let source = std::fs::read_to_string(fixture()).unwrap();
    let needle = "None => assert!(raw == 0)";
    assert_eq!(source.matches(needle).count(), 4);
    let mutation = source.replacen(needle, "None => assert!(raw != 0)", 1);
    let directory = Directory::new();
    let path = directory.0.join("mutation.rs");
    std::fs::write(&path, mutation).unwrap();
    let entries = [("correlated_unsigned", ProofStatus::Refuted)];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&path, &entries, target, optimized, None);
        }
    }
    assert!(!native_tests(&path, &directory));
}
