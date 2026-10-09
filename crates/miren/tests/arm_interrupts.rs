#![forbid(unsafe_code)]

use miren::{ProofStatus, Report};
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct Project(PathBuf);

impl Project {
    fn new() -> Self {
        let id = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("miren-arm-interrupts-{}-{id}", std::process::id()));
        std::fs::create_dir_all(&path).unwrap();
        let patches = extract_dependencies(&path);
        std::fs::write(
            path.join("Cargo.toml"),
            "[package]\nname='arm_interrupts'\nversion='0.1.0'\nedition='2024'\n\
             [lib]\npath='lib.rs'\n[dependencies]\ncortex-m='=0.7.9'\n[workspace]\n"
                .to_owned()
                + &patches,
        )
        .unwrap();
        std::fs::write(path.join("lib.rs"), FIXTURE).unwrap();
        Self(path)
    }

    fn verify(&self, target: Option<&str>, optimized: bool) -> Report {
        let report_path = self.0.join("report.jsonl");
        let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
        command
            .args(["--no-config", "--quiet", "--lib", "--offline", "--jsonl"])
            .arg(&report_path)
            .current_dir(&self.0)
            .env_remove("CARGO_TARGET_DIR");
        for name in [
            "read_mask",
            "read_bit",
            "disable",
            "free",
            "free_panic",
            "unsupported",
            "independent_reads",
            "reserved_bits",
            "send_event",
            "wait_event",
            "wait_interrupt",
        ] {
            command.args(["--entry", name]);
        }
        if let Some(target) = target {
            command.args(["--target", target]);
        }
        if optimized {
            command.arg("--release");
        }
        let output = command.output().unwrap();
        let bytes = std::fs::read(report_path)
            .unwrap_or_else(|error| panic!("{error}: {}", String::from_utf8_lossy(&output.stderr)));
        let mut reports = bytes
            .split(|b| *b == b'\n')
            .filter(|line| !line.is_empty())
            .map(|line| serde_json::from_slice::<Report>(line).unwrap());
        let report = reports.find(|r| r.crate_name == "arm_interrupts").unwrap();
        assert!(!output.status.success());
        report
    }
}

impl Drop for Project {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn proof<'a>(report: &'a Report, name: &str) -> &'a miren::Proof {
    report
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap()
        .proof
        .as_ref()
        .unwrap()
}

const FIXTURE: &str = r#"#![no_std]
#![forbid(unsafe_code)]
pub fn read_mask() -> u32 { cortex_m::register::primask::read_raw() }
pub fn read_bit() { assert!(cortex_m::register::primask::read_raw() & 1 <= 1); }
pub fn disable() { cortex_m::interrupt::disable(); }
pub fn free() { assert_eq!(cortex_m::interrupt::free(|_| 7_u32), 7); }
pub fn free_panic() { cortex_m::interrupt::free(|_| panic!("reached closure")); }
pub fn unsupported() -> u32 { cortex_m::register::control::read().bits() }
pub fn independent_reads() {
    assert!(cortex_m::register::primask::read_raw() == cortex_m::register::primask::read_raw());
}
pub fn reserved_bits() { assert!(cortex_m::register::primask::read_raw() <= 1); }
pub fn send_event() { cortex_m::asm::sev(); }
pub fn wait_event() { cortex_m::asm::wfe(); }
pub fn wait_interrupt() { cortex_m::asm::wfi(); }
"#;

#[test]
fn compiler_arm_instructions_reach_safe_dependency_calls_and_keep_unknown_boundaries() {
    let project = Project::new();
    for optimized in [false, true] {
        let report = project.verify(Some("thumbv7em-none-eabihf"), optimized);
        for name in ["read_mask", "read_bit", "disable", "free"] {
            let proof = proof(&report, name);
            assert_eq!(
                proof.status,
                ProofStatus::Proved,
                "{name}: {:?}",
                proof.obligations
            );
            assert!(proof.assumptions.is_empty());
            assert!(proof.trusted_calls.is_empty());
            assert!(
                proof
                    .models
                    .iter()
                    .any(|m| m == "Cortex-M PRIMASK assembly")
            );
        }
        for name in ["free_panic", "independent_reads", "reserved_bits"] {
            let proof = proof(&report, name);
            assert_eq!(
                proof.status,
                ProofStatus::Refuted,
                "{name}: {:?}",
                proof.obligations
            );
            if name != "free_panic" {
                assert!(proof.obligations.iter().any(|o| {
                    o.abstraction_reasons
                        .iter()
                        .any(|reason| reason.contains("PRIMASK"))
                }));
            }
        }
        assert_eq!(proof(&report, "unsupported").status, ProofStatus::Unknown);
        for (name, mnemonic) in [
            ("send_event", "sev"),
            ("wait_event", "wfe"),
            ("wait_interrupt", "wfi"),
        ] {
            let proof = proof(&report, name);
            assert_eq!(
                proof.status,
                ProofStatus::Unknown,
                "{name}: {:?}",
                proof.obligations
            );
            assert!(proof.assumptions.is_empty());
            assert!(proof.trusted_calls.is_empty());
            assert!(proof.models.is_empty());
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|obligation| obligation.detail.contains(&format!(
                        "unsupported Cortex-M instruction `{mnemonic}`; \
                     hardware event/wait semantics are unmodeled"
                    )))
            );
        }
    }
}

fn extract_dependencies(project: &Path) -> String {
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/third_party");
    let manifest: serde_json::Value =
        serde_json::from_slice(&std::fs::read(fixtures.join("manifest.json")).unwrap()).unwrap();
    assert_eq!(manifest["schema_version"], 1);
    let archives = manifest["archives"].as_array().unwrap();
    assert_eq!(archives.len(), 14);
    let destination = project.join("third-party");
    std::fs::create_dir_all(&destination).unwrap();
    let mut patches = String::from("\n[patch.crates-io]\n");
    for archive in archives {
        let name = archive["name"].as_str().unwrap();
        let version = archive["version"].as_str().unwrap();
        assert!(
            name.chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_')
        );
        assert!(version.chars().all(|c| c.is_ascii_digit() || c == '.'));
        let directory = format!("{name}-{version}");
        let filename = format!("{directory}.crate");
        assert_eq!(archive["archive"].as_str().unwrap(), filename);
        let path = fixtures.join(filename);
        let bytes = std::fs::read(&path).unwrap();
        assert_eq!(bytes.len() as u64, archive["bytes"].as_u64().unwrap());
        assert!(bytes.len() <= 500 * 1024);
        assert_eq!(
            format!("{:x}", Sha256::digest(&bytes)),
            archive["sha256"].as_str().unwrap()
        );
        let listing = Command::new("tar").arg("-tzf").arg(&path).output().unwrap();
        assert!(
            listing.status.success(),
            "{}",
            String::from_utf8_lossy(&listing.stderr)
        );
        let listing = String::from_utf8(listing.stdout).unwrap();
        assert!(listing.lines().count() <= 10_000);
        for entry in listing.lines() {
            let components: Vec<_> = Path::new(entry).components().collect();
            assert_eq!(
                components.first(),
                Some(&std::path::Component::Normal(directory.as_ref()))
            );
            assert!(
                components
                    .iter()
                    .all(|c| matches!(c, std::path::Component::Normal(_)))
            );
        }
        // Only checksum-verified original registry archives reach the system extractor.
        let extracted = Command::new("tar")
            .arg("-xzf")
            .arg(&path)
            .arg("-C")
            .arg(&destination)
            .output()
            .unwrap();
        assert!(
            extracted.status.success(),
            "{}",
            String::from_utf8_lossy(&extracted.stderr)
        );
        let alias = format!("{}_{}", name.replace('-', "_"), version.replace('.', "_"));
        patches.push_str(&format!(
            "{alias}={{package='{name}',path='third-party/{directory}'}}\n"
        ));
    }
    patches
}

#[test]
fn dependency_instruction_and_option_mutations_cannot_be_accepted_as_primask() {
    for (before, after) in [
        ("mrs {}, PRIMASK", "mrs {}, CONTROL"),
        ("out(reg)", "lateout(reg)"),
        ("nomem, nostack, preserves_flags", "nomem, nostack"),
        ("let r: u32;", "let r: u16;"),
    ] {
        let project = Project::new();
        let dependency = project.0.join("third-party/cortex-m-0.7.9");
        let path = dependency.join("src/register/primask.rs");
        let original = std::fs::read_to_string(&path).unwrap();
        assert!(original.contains(before));
        let changed = original.replacen(before, after, 1);
        // Keep the public return type stable while changing the compiler operand width.
        let changed = if before == "let r: u32;" {
            changed.replacen("    r\n", "    r as u32\n", 1)
        } else {
            changed
        };
        std::fs::write(path, changed).unwrap();
        let report = project.verify(Some("thumbv7em-none-eabihf"), false);
        assert_eq!(
            proof(&report, "read_mask").status,
            ProofStatus::Unknown,
            "{before}: {:?}",
            proof(&report, "read_mask").obligations
        );
    }
}

#[test]
fn compiler_cpsie_shape_in_copied_dependency_remains_a_narrow_supported_instruction() {
    let project = Project::new();
    let dependency = project.0.join("third-party/cortex-m-0.7.9");
    let path = dependency.join("src/register/primask.rs");
    let original = std::fs::read_to_string(&path).unwrap();
    let before = "asm!(\"msr PRIMASK, {}\", in(reg) r, options(nomem, nostack, preserves_flags))";
    let after = "asm!(\"cpsie i\", options(nomem, nostack, preserves_flags))";
    assert!(original.contains(before));
    // Reuse the third-party unsafe assembly body; the safe test root remains unchanged.
    std::fs::write(path, original.replace(before, after)).unwrap();
    let report = project.verify(Some("thumbv7em-none-eabihf"), false);
    assert_eq!(
        proof(&report, "free").status,
        ProofStatus::Proved,
        "{:?}",
        proof(&report, "free").obligations
    );
}

#[test]
fn bare_send_event_template_is_reported_before_primask_option_checks() {
    let project = Project::new();
    let assembly = project.0.join("third-party/cortex-m-0.7.9/src/asm.rs");
    let original = std::fs::read_to_string(&assembly).unwrap();
    let instruction = "asm!(\"sev\", options(nomem, nostack, preserves_flags))";
    assert_eq!(original.matches(instruction).count(), 1);
    std::fs::write(&assembly, original.replace(instruction, "asm!(\"sev\")")).unwrap();
    for optimized in [false, true] {
        let report = project.verify(Some("thumbv7em-none-eabihf"), optimized);
        let proof = proof(&report, "send_event");
        assert!(
            proof
                .obligations
                .iter()
                .any(|o| o.unknown_category == Some(miren::UnknownCategory::ExternalEnvironment))
        );
        assert_eq!(proof.status, ProofStatus::Unknown);
        assert!(proof.assumptions.is_empty());
        assert!(proof.trusted_calls.is_empty());
        assert!(proof.models.is_empty());
        assert!(proof.obligations.iter().any(|obligation| {
            obligation.detail.contains(
            "unsupported Cortex-M instruction `sev`; hardware event/wait semantics are unmodeled"
        )
        }));
    }
}
