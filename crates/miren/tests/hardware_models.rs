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
            "miren-hardware-{}-{}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/hardware_models.rs")
}
fn model(device: HardwareDevice) -> HardwareModel {
    let base = match device {
        HardwareDevice::Stm32h723vg => 0x5802_0800,
        HardwareDevice::Stm32f407ig => 0x4002_1c00,
    };
    HardwareModel::new(device, 32,
        "selected device has valid byte transports and terminating write-only u32 access; no tracked Rust writes during access; no later interference guarantee")
        .with_region("gpio", base, 0x400)
        .with_write_register("bsrr", base + 24)
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
    }
}
#[test]
fn exact_device_effects_preserve_rust_bodies_and_conservative_refusals() {
    use ProofStatus::{ProvedWithAssumptions as P, Refuted as R, Unknown as U};
    let entries = [
        ("exact_u32", P, true),
        ("byte_transport", P, true),
        ("actual_add", P, true),
        ("callback_body", P, true),
        ("wrong_rust_claim", R, true),
        ("wrong_callback_claim", R, true),
        ("later_unknown", U, true),
        ("guarded_address", P, true),
        ("wrong_address", U, false),
        ("misaligned", U, false),
        ("ram_write", U, false),
        ("wrong_width", U, false),
        ("signed_write", U, false),
        ("lookalike", U, false),
        ("narrow_wrapper", U, false),
        ("symbolic_address", U, false),
        ("symbolic_offset", U, false),
        ("outside_region", U, false),
        ("huge_add", U, false),
        ("huge_sub", U, false),
        ("negative_offset", U, false),
        ("tracked_storage", U, false),
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
            &[("f4_write", P, true)],
            Some(model(HardwareDevice::Stm32f407ig)),
            Some("thumbv7em-none-eabihf"),
            optimized,
            &["stm32f407ig"],
            false,
        );
        verify(
            &fixture(),
            &[("exact_u32", U, false)],
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
                &[("exact_u32", U, false)],
                Some(model(HardwareDevice::Stm32h723vg)),
                Some("thumbv7em-none-eabihf"),
                optimized,
                markers,
                false,
            );
        }
        verify(
            &fixture(),
            &[("startup_history_after_write", R, true)],
            Some(model(HardwareDevice::Stm32h723vg)),
            Some("thumbv7em-none-eabihf"),
            optimized,
            &["stm32h723vg"],
            true,
        );
        for target in [None, Some("thumbv7em-none-eabihf")] {
            verify(
                &fixture(),
                &[("exact_u32", U, false), ("byte_transport", U, false)],
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
        .args(["--exact", "native::callback_effect"])
        .output()
        .unwrap()
        .status
        .success()
}
#[test]
fn callback_mutation_refutes_original_claim_without_native_mmio() {
    assert!(native(&fixture()));
    let directory = Directory::new();
    let mutated = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    assert!(source.contains("*value += 1"));
    std::fs::write(&mutated, source.replace("*value += 1", "*value += 2")).unwrap();
    assert!(!native(&mutated));
    for optimized in [false, true] {
        verify(
            &mutated,
            &[("callback_body", ProofStatus::Refuted, true)],
            Some(model(HardwareDevice::Stm32h723vg)),
            Some("thumbv7em-none-eabihf"),
            optimized,
            &["stm32h723vg"],
            false,
        );
    }
}
