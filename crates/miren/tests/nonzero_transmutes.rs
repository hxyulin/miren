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
            "miren-nonzero-transmutes-{}-{id}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/nonzero_transmutes.rs")
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
        if *name == "guarded_power" {
            assert!(
                proof
                    .analyzed_bodies
                    .iter()
                    .any(|body| body.starts_with("core::num::<impl u8>::checked_pow "))
            );
            assert!(proof.models.iter().any(|model| {
                model.contains("compiler-certified NonZero storage; exact primitive integer")
            }));
        }
        if matches!(
            *name,
            "mixed_width_overflow" | "mixed_width_narrowing" | "signed_count_negative"
        ) {
            assert!(proof.obligations.iter().any(|o| {
                o.detail
                    .contains("unchecked left shift lacks a proven in-range count")
            }));
        }
        if matches!(*name, "mixed_width_valid" | "signed_count_valid") {
            assert!(proof.models.iter().any(|model| {
                model.contains("MIR unchecked left shift; proven original count in range")
            }));
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
fn certified_reverse_transmutes_execute_checked_power_and_preserve_values() {
    let entries = [
        ("exact_u8", ProofStatus::Proved),
        ("exact_u16", ProofStatus::Proved),
        ("exact_u32", ProofStatus::Proved),
        ("exact_u64", ProofStatus::Proved),
        ("exact_u128", ProofStatus::Proved),
        ("exact_usize", ProofStatus::Proved),
        ("exact_i8", ProofStatus::Proved),
        ("exact_i16", ProofStatus::Proved),
        ("exact_i32", ProofStatus::Proved),
        ("exact_i64", ProofStatus::Proved),
        ("exact_i128", ProofStatus::Proved),
        ("exact_isize", ProofStatus::Proved),
        ("check_u8_scan", ProofStatus::Proved),
        ("check_u16_scan", ProofStatus::Proved),
        ("check_u32_scan", ProofStatus::Proved),
        ("check_u64_scan", ProofStatus::Proved),
        ("check_u128_scan", ProofStatus::Proved),
        ("check_usize_scan", ProofStatus::Proved),
        ("check_i8_scan", ProofStatus::Proved),
        ("check_i16_scan", ProofStatus::Proved),
        ("check_i32_scan", ProofStatus::Proved),
        ("check_i64_scan", ProofStatus::Proved),
        ("check_i128_scan", ProofStatus::Proved),
        ("check_isize_scan", ProofStatus::Proved),
        ("zero_scan", ProofStatus::Unknown),
        ("scan_u32", ProofStatus::Unknown),
        ("wrong_count", ProofStatus::Refuted),
        ("lookalike_body", ProofStatus::Proved),
        ("lookalike_wrong_claim", ProofStatus::Refuted),
        ("mixed_width_valid", ProofStatus::Proved),
        ("mixed_width_overflow", ProofStatus::Unknown),
        ("mixed_width_narrowing", ProofStatus::Unknown),
        ("signed_count_negative", ProofStatus::Unknown),
        ("signed_count_valid", ProofStatus::Proved),
        ("guarded_shift", ProofStatus::Proved),
        ("zero_shift", ProofStatus::Proved),
        ("largest_shift", ProofStatus::Proved),
        ("invalid_shift", ProofStatus::Unknown),
        ("negative_shift", ProofStatus::Unknown),
        ("unchecked_shift", ProofStatus::Unknown),
        ("wrong_shift", ProofStatus::Refuted),
        ("guarded_power", ProofStatus::Proved),
        ("negative_value", ProofStatus::Proved),
        ("mutation_claim", ProofStatus::Proved),
        ("unchecked_power", ProofStatus::Unknown),
        ("zero_unwrap", ProofStatus::Refuted),
        ("wrong_value", ProofStatus::Refuted),
        ("signedness_mismatch", ProofStatus::Unknown),
        ("noncore_wrapper", ProofStatus::Unknown),
        ("wrong_primitive", ProofStatus::Unknown),
        ("raw_integer_is_not_nonzero", ProofStatus::Unknown),
        ("unchecked_payload", ProofStatus::Unknown),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(&fixture(), &entries, target, optimized, None);
        }
    }
    assert!(native_tests(&fixture(), &Directory::new()));
    let directory = Directory::new();
    let path = directory.0.join("width_control.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    std::fs::write(
        &path,
        format!(
            "{source}\n{}",
            r#"
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn width_mismatch(value: NonZero<u64>) -> u32 {
    mir! { { RET = CastTransmute(value); Return() } }
}
"#
        ),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &path,
                &[("width_mismatch", ProofStatus::Unknown)],
                target,
                optimized,
                None,
            );
        }
    }
}

#[test]
fn mutated_reverse_transmute_claim_refutes_and_fails_native_execution() {
    let source = std::fs::read_to_string(fixture()).unwrap();
    let needle = "cast_u32(value) == value.get()";
    assert_eq!(source.matches(needle).count(), 1);
    let directory = Directory::new();
    let path = directory.0.join("mutation.rs");
    std::fs::write(
        &path,
        source.replace(needle, "cast_u32(value) != value.get()"),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &path,
                &[("mutation_claim", ProofStatus::Refuted)],
                target,
                optimized,
                None,
            );
        }
    }
    assert!(!native_tests(&path, &directory));
    let power_path = directory.0.join("power_mutation.rs");
    let needle = "value.pow(2) >= value";
    assert_eq!(source.matches(needle).count(), 1);
    std::fs::write(&power_path, source.replace(needle, "value.pow(2) > value")).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &power_path,
                &[("guarded_power", ProofStatus::Refuted)],
                target,
                optimized,
                None,
            );
        }
    }
    assert!(!native_tests(&power_path, &directory));
}
