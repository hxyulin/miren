#![forbid(unsafe_code)]

use miren::{ContractConfig, HardwareDevice, HardwareModel, ProofStatus, Report};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Directory(PathBuf);
impl Directory {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "miren-hardware-reads-{}-{}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/hardware_reads.rs")
}
fn model(device: HardwareDevice) -> HardwareModel {
    let base = match device {
        HardwareDevice::Stm32h723vg => 0x5802_0800,
        HardwareDevice::Stm32f407ig => 0x4002_1c00,
    };
    HardwareModel::new(device, 32,
        "selected device has valid byte transports, independent arbitrary terminating u32 reads, and terminating u32 writes; no tracked Rust writes during access; no later interference guarantee")
        .with_region("gpio", base, 0x400)
        .with_write_register("bsrr", base + 24)
    .with_write_register("pupdr", base + 12)
    .with_read_register("pupdr", base + 12)
    .with_read_register("read-only", base + 4)
}
fn verify(
    path: &Path,
    entries: &[(&str, ProofStatus, bool)],
    hardware: Option<HardwareModel>,
    target: Option<&str>,
    optimized: bool,
    markers: &[&str],
    startup: bool,
) {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    let assumption = hardware.as_ref().map(HardwareModel::assumption);
    if let Some(hardware) = hardware {
        let config = directory.0.join("config.json");
        std::fs::write(
            &config,
            serde_json::to_vec(&ContractConfig::default().with_hardware(hardware)).unwrap(),
        )
        .unwrap();
        command.arg("--contracts").arg(config);
    }
    if startup {
        command.arg("--startup");
    }
    for (name, _, _) in entries {
        command.args(["--entry", name]);
    }
    command
        .args(["--", "--crate-type=lib", "--edition=2024"])
        .arg(path)
        .arg("--out-dir")
        .arg(&directory.0)
        .args(["-Cpanic=abort", "-Coverflow-checks=yes"]);
    for marker in markers {
        command.arg("--cfg").arg(format!("feature=\"{marker}\""));
    }
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    if optimized {
        command.arg("-Copt-level=2");
    }
    let output = command.output().unwrap();
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
    for (name, expected, used) in entries {
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
            "{target:?} O2={optimized} {name}: {:?}",
            proof.obligations
        );
        if *name == "ram_read" {
            assert!(proof.obligations.iter().any(|o| {
                o.unknown_category == Some(miren::UnknownCategory::Semantics)
                    && o.detail
                        .contains("verified temporal permission certificate")
            }));
        }
        let actual = proof
            .entry_assumptions
            .iter()
            .filter(|s| s.starts_with("hardware-model:"))
            .collect::<Vec<_>>();
        if *used {
            assert_eq!(actual, vec![assumption.as_ref().unwrap()]);
        } else {
            assert!(actual.is_empty(), "{name}");
        }
        assert!(proof.trusted_calls.is_empty());
        if matches!(
            *name,
            "fixed_read_claim" | "repeated_read_claim" | "write_read_claim"
        ) {
            assert!(proof.obligations.iter().any(|o| o.abstraction_reasons.iter().any(|reason|
                reason == "external hardware reads admit independent arbitrary u32 values; device correlations are unverified")), "{name}");
        }
    }
}
#[test]
fn independent_reads_execute_rmw_bodies_and_preserve_refusals() {
    use ProofStatus::{ProvedWithAssumptions as C, Refuted as R, Unknown as U};
    let entries = [
        ("bit_identity", C, true),
        ("actual_checked_read", C, true),
        ("transparent_read", C, true),
        ("actual_rmw_callback", C, true),
        ("fixed_read_claim", R, true),
        ("repeated_read_claim", R, true),
        ("write_read_claim", R, true),
        ("wrong_callback_claim", R, true),
        ("wrong_address", U, false),
        ("wrong_direction", U, false),
        ("read_only_store", U, false),
        ("wrong_width", U, false),
        ("signed_read", U, false),
        ("lookalike", U, false),
        ("narrow_wrapper", U, false),
        ("restricted_wrapper", U, false),
        ("drop_wrapper", U, false),
        ("misaligned", U, false),
        ("symbolic_address", U, false),
        ("guarded_address", C, true),
        ("ram_read", U, false),
        ("unmodeled_dereference", U, false),
        ("read_then_dereference", U, true),
    ];
    for optimized in [false, true] {
        verify(
            &fixture(),
            &entries,
            Some(model(HardwareDevice::Stm32h723vg)),
            Some("thumbv7em-none-eabihf"),
            optimized,
            &["stm32h723vg"],
            false,
        );
        verify(
            &fixture(),
            &[("f4_read", C, true)],
            Some(model(HardwareDevice::Stm32f407ig)),
            Some("thumbv7em-none-eabihf"),
            optimized,
            &["stm32f407ig"],
            false,
        );
        verify(
            &fixture(),
            &[("startup_history_after_read", R, true)],
            Some(model(HardwareDevice::Stm32h723vg)),
            Some("thumbv7em-none-eabihf"),
            optimized,
            &["stm32h723vg"],
            true,
        );
        verify(
            &fixture(),
            &[("bit_identity", U, false)],
            Some(model(HardwareDevice::Stm32h723vg)),
            None,
            optimized,
            &["stm32h723vg"],
            false,
        );
        for markers in [
            &[][..],
            &["stm32f407ig"][..],
            &["stm32h723vg", "stm32f407ig"][..],
        ] {
            verify(
                &fixture(),
                &[("bit_identity", U, false)],
                Some(model(HardwareDevice::Stm32h723vg)),
                Some("thumbv7em-none-eabihf"),
                optimized,
                markers,
                false,
            );
        }
        let mut legacy = model(HardwareDevice::Stm32h723vg);
        legacy.schema_version = 1;
        legacy.read_registers.clear();
        verify(
            &fixture(),
            &[("bit_identity", U, false)],
            Some(legacy),
            Some("thumbv7em-none-eabihf"),
            optimized,
            &["stm32h723vg"],
            false,
        );
        for target in [None, Some("thumbv7em-none-eabihf")] {
            verify(
                &fixture(),
                &[("bit_identity", U, false), ("ram_read", U, false)],
                None,
                target,
                optimized,
                &[],
                false,
            );
        }
    }
}
fn native(path: &Path) -> bool {
    let directory = Directory::new();
    let executable = directory.0.join("native");
    let output = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"))
        .args(["--test", "--edition=2024"])
        .arg(path)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    Command::new(executable)
        .args(["--exact", "native::callback_bits"])
        .output()
        .unwrap()
        .status
        .success()
}
#[test]
fn rmw_callback_mutation_refutes_original_claim_without_native_mmio() {
    assert!(native(&fixture()));
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    assert!(source.contains("| 0x20"));
    std::fs::write(&mutated, source.replace("| 0x20", "| 0x10")).unwrap();
    assert!(!native(&mutated));
    for optimized in [false, true] {
        verify(
            &mutated,
            &[("actual_rmw_callback", ProofStatus::Refuted, true)],
            Some(model(HardwareDevice::Stm32h723vg)),
            Some("thumbv7em-none-eabihf"),
            optimized,
            &["stm32h723vg"],
            false,
        );
    }
}

#[test]
fn native_replay_refuses_used_and_unused_external_device_models() {
    let directory = Directory::new();
    let config = directory.0.join("hardware.json");
    std::fs::write(
        &config,
        serde_json::to_vec(
            &ContractConfig::default().with_hardware(model(HardwareDevice::Stm32h723vg)),
        )
        .unwrap(),
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_miren"))
        .args([
            "--verify",
            "--json",
            "--quiet",
            "--entry",
            "pure_wrong_claim",
        ])
        .arg("--contracts")
        .arg(config)
        .args(["--", "--crate-type=lib", "--edition=2024", "-Cpanic=abort"])
        .arg(fixture())
        .arg("--out-dir")
        .arg(&directory.0)
        .output()
        .unwrap();
    let mut report: Report = serde_json::from_slice(&output.stdout).unwrap();
    let proof = report
        .functions
        .iter()
        .find(|f| f.name == "pure_wrong_claim")
        .unwrap()
        .proof
        .as_ref()
        .unwrap();
    assert_eq!(proof.status, ProofStatus::Refuted);
    assert!(proof.entry_assumptions.is_empty());
    miren::replay::replay_report(&mut report);
    let verify_refusal = |report: &Report| {
        let proof = report
            .functions
            .iter()
            .find(|f| f.name == "pure_wrong_claim")
            .unwrap()
            .proof
            .as_ref()
            .unwrap();
        let replay = proof
            .obligations
            .iter()
            .find_map(|o| o.replay.as_ref())
            .unwrap();
        assert_eq!(replay.status, miren::replay::ReplayStatus::Unsupported);
        assert_eq!(
            replay.detail,
            "external hardware models have no native replay implementation"
        );
    };
    verify_refusal(&report);
    let model = report.contract_config.take().unwrap().hardware.unwrap();
    let proof = report
        .functions
        .iter_mut()
        .find(|f| f.name == "pure_wrong_claim")
        .unwrap()
        .proof
        .as_mut()
        .unwrap();
    proof.entry_assumptions.push(model.assumption());
    miren::replay::replay_report(&mut report);
    verify_refusal(&report);
}
