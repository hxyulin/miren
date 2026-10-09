#![forbid(unsafe_code)]

use miren::{ContractConfig, ProofStatus, Report};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Directory(PathBuf);
impl Directory {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "miren-trusted-storage-{}-{}",
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/trusted_storage.rs")
}
fn model(preserve: bool) -> ContractConfig {
    let functions = [
        "boundary",
        "consume_reference",
        "consume_mutable",
        "consume_pointer",
        "consume_nested",
        "consume_cell",
        "consume_atomic",
        "consume_callback",
        "consume_restricted",
        "consume_restricted_array",
        "consume_restricted_tuple",
        "return_reference",
        "return_pointer",
        "return_nested",
    ]
    .map(|name| {
        let mut spec = serde_json::json!({ "function": format!("trusted_storage::{name}"),
                "trusted": true, "no_panic": true,
                "reason": concat!("exact call has no mutation, publication or retirement of ",
                    "pre-existing ordinary tracked storage; global state may change; ",
                    "subsequent interference remains unverified"),
                "ensures": ["result == 7"] });
        if name.starts_with("return_") {
            spec["ensures"] = serde_json::json!([]);
        }
        if preserve {
            spec["storage_effect"] = serde_json::json!("preserve_existing_ordinary_storage");
        }
        spec
    });
    serde_json::from_value(serde_json::json!({"schema_version":1,"functions":functions})).unwrap()
}
fn verify(
    path: &Path,
    entries: &[(&str, ProofStatus, bool)],
    config: Option<ContractConfig>,
    target: Option<&str>,
    optimized: bool,
    markers: &[&str],
    startup: bool,
) {
    let directory = Directory::new();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command.args(["--verify", "--json", "--quiet"]);
    let assumption = config
        .as_ref()
        .and_then(|config| config.functions[0].storage_assumption());
    if let Some(config) = config {
        let path = directory.0.join("config.json");
        std::fs::write(&path, serde_json::to_vec(&config).unwrap()).unwrap();
        command.arg("--contracts").arg(path);
    }
    if startup {
        command.arg("--startup");
    }
    for (name, _, _) in entries {
        command.args([
            if *name == "fresh_future" {
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
            "--crate-type=lib",
            "--crate-name=trusted_storage",
            "--edition=2024",
        ])
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
            .filter(|s| s.starts_with("trusted-storage:"))
            .collect::<Vec<_>>();
        if *used {
            assert_eq!(actual, vec![assumption.as_ref().unwrap()]);
        } else {
            assert!(actual.is_empty(), "{name}");
        }
        if *name == "constructed_many" && *expected == ProofStatus::Unknown {
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|obligation| obligation.detail.contains("has 1025 variants; limit 1024"))
            );
        }
        if name.starts_with("blocked_restricted") {
            assert!(proof.obligations.iter().any(|obligation| {
                obligation
                    .detail
                    .contains("owned inputs with restricted pattern validity are unsupported")
            }));
        }
        if *used {
            assert_eq!(proof.trusted_calls.len(), 1);
        } else if assumption.is_some() {
            assert!(proof.trusted_calls.is_empty());
        }
    }
}
#[test]
fn explicit_frame_effect_preserves_ordinary_lifetimes_and_retires_global_precision() {
    use ProofStatus::{ProvedWithAssumptions as C, Refuted as R, Unknown as U};
    let entries = [
        ("ordinary_backing", C, true),
        ("owned_symbolic", C, true),
        ("fresh_future", C, true),
        ("wrong_later_claim", R, true),
        ("dead_backing_stays_dead", U, true),
        ("blocked_reference", U, false),
        ("blocked_mutable", U, false),
        ("blocked_pointer", U, false),
        ("blocked_nested", U, false),
        ("blocked_cell", U, false),
        ("blocked_atomic", U, false),
        ("blocked_callback", U, false),
        ("blocked_restricted", U, false),
        ("blocked_restricted_array", U, false),
        ("blocked_restricted_tuple", U, false),
        ("blocked_reference_output", U, false),
        ("blocked_pointer_output", U, false),
        ("blocked_nested_output", U, false),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &fixture(),
                &entries,
                Some(model(true)),
                target,
                optimized,
                &[],
                false,
            );
            verify(
                &fixture(),
                &[
                    ("static_precision_is_retired", U, true),
                    ("static_atomic_is_retired", U, true),
                    ("local_atomic_precision_is_retired", R, true),
                ],
                Some(model(true)),
                target,
                optimized,
                &[],
                true,
            );
            verify(
                &fixture(),
                &[("ordinary_backing", U, false), ("fresh_future", U, false)],
                Some(model(false)),
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
        .args(["--exact", "native::valid_rust_storage"])
        .output()
        .unwrap()
        .status
        .success()
}
#[test]
fn changed_ordinary_claim_refutes_and_fails_native_execution() {
    assert!(native(&fixture()));
    let directory = Directory::new();
    let path = directory.0.join("mutated.rs");
    let source = std::fs::read_to_string(fixture()).unwrap();
    assert!(source.contains("value == 5"));
    std::fs::write(&path, source.replace("value == 5", "value == 6")).unwrap();
    assert!(!native(&path));
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            verify(
                &path,
                &[("ordinary_backing", ProofStatus::Refuted, true)],
                Some(model(true)),
                target,
                optimized,
                &[],
                false,
            );
        }
    }
}

#[test]
fn native_replay_refuses_configured_and_retained_storage_effects() {
    let directory = Directory::new();
    let config = directory.0.join("storage.json");
    std::fs::write(&config, serde_json::to_vec(&model(true)).unwrap()).unwrap();
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
        .args([
            "--",
            "--crate-type=lib",
            "--crate-name=trusted_storage",
            "--edition=2024",
            "-Cpanic=abort",
        ])
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
            "external storage effects have no native replay implementation"
        );
    };
    verify_refusal(&report);
    let config = report.contract_config.take().unwrap();
    let assumption = config.functions[0].storage_assumption().unwrap();
    let proof = report
        .functions
        .iter_mut()
        .find(|f| f.name == "pure_wrong_claim")
        .unwrap()
        .proof
        .as_mut()
        .unwrap();
    proof.entry_assumptions.push(assumption);
    miren::replay::replay_report(&mut report);
    verify_refusal(&report);
}

#[test]
fn large_constructed_fieldless_enums_have_bounded_owned_boundary_certificates() {
    for count in [512, 1024, 1025] {
        let directory = Directory::new();
        let path = directory.0.join("large.rs");
        let variants = (0..count)
            .map(|index| format!("V{index}={index},"))
            .collect::<String>();
        let source = format!(
            concat!(
                "#![no_std]\n#![forbid(unsafe_code)]\n",
                "#[repr(u16)]\npub enum Many {{ {variants} }}\n",
                "#[inline(never)] pub fn consume_many(_:Many)->u32 {{7}}\n",
                "pub fn constructed_many() {{assert!(consume_many(Many::V{})==7);}}\n"
            ),
            count - 1,
            variants = variants
        );
        std::fs::write(&path, source).unwrap();
        let mut config = model(true);
        let mut spec = config.functions.remove(0);
        spec.function = "trusted_storage::consume_many".into();
        config.functions = vec![spec];
        let expected = if count <= 1024 {
            ProofStatus::ProvedWithAssumptions
        } else {
            ProofStatus::Unknown
        };
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for optimized in [false, true] {
                verify(
                    &path,
                    &[("constructed_many", expected, count <= 1024)],
                    Some(config.clone()),
                    target,
                    optimized,
                    &[],
                    false,
                );
            }
        }
    }
}
