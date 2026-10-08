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
            std::env::temp_dir().join(format!("miren-zst-inputs-{}-{id}", std::process::id()));
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
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/zero_sized_inputs.rs")
}

fn verify(path: &Path, entries: &[&str], target: Option<&str>, optimized: bool) -> Report {
    let directory = Directory::new();
    let contracts = directory.0.join("contracts.json");
    std::fs::write(
        &contracts,
        serde_json::to_vec(&serde_json::json!({"schema_version": 1, "functions": [{
            "function": "zero_sized_inputs::make_wide",
            "trusted": true, "no_panic": true, "modifies": [],
            "reason": "TEST ONLY: assume the factory returns valid owned zero-sized tokens"
        }]}))
        .unwrap(),
    )
    .unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    command
        .args(["--verify", "--json", "--allow-assumptions", "--contracts"])
        .arg(contracts);
    for entry in entries {
        command.args(["--entry", entry]);
    }
    command.args([
        "--",
        "--crate-name=zero_sized_inputs",
        "--crate-type=lib",
        "--edition=2024",
        "-Cpanic=abort",
        "-Coverflow-checks=yes",
    ]);
    command.arg(path).arg("--out-dir").arg(&directory.0);
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    if optimized {
        command.arg("-Copt-level=3");
    }
    let output = command.output().unwrap();
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| panic!("{error}: {output:?}"))
}

fn proof<'a>(report: &'a Report, entry: &str) -> &'a miren::Proof {
    report
        .functions
        .iter()
        .find(|function| function.name == entry)
        .unwrap()
        .proof
        .as_ref()
        .unwrap()
}

#[test]
fn exact_zero_sized_inputs_and_conditional_factory_results_preserve_boundaries() {
    let entries = [
        ("projected", ProofStatus::Proved),
        ("trusted_use", ProofStatus::ProvedWithAssumptions),
        ("nested_arrays", ProofStatus::Proved),
        ("wrong_guard", ProofStatus::Refuted),
        ("unknown_uninhabited", ProofStatus::Unknown),
        ("unknown_union", ProofStatus::Unknown),
        ("unknown_reference", ProofStatus::Unknown),
        ("unknown_array_budget", ProofStatus::Unknown),
        ("unknown_depth", ProofStatus::Unknown),
    ];
    let names: Vec<_> = entries.iter().map(|(entry, _)| *entry).collect();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&fixture(), &names, target, optimized);
            for (entry, expected) in entries {
                assert_eq!(
                    proof(&report, entry).status,
                    expected,
                    "{entry}: {report:?}"
                );
            }
            assert!(proof(&report, "projected").trusted_calls.is_empty());
            assert!(proof(&report, "projected").assumptions.is_empty());
            assert!(
                proof(&report, "nested_arrays")
                    .obligations
                    .iter()
                    .all(|obligation| {
                        obligation
                            .query
                            .as_ref()
                            .is_none_or(|query| !query.contains("declare-fun"))
                    })
            );
            let conditional = proof(&report, "trusted_use");
            assert_eq!(conditional.trusted_calls.len(), 1);
            assert_eq!(
                conditional.trusted_calls[0].contract.function,
                "zero_sized_inputs::make_wide"
            );
        }
    }
}

#[test]
fn zero_sized_caller_mutations_refute_and_descriptor_budget_remains_unknown() {
    let directory = Directory::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    let path = directory.0.join("mutation.rs");
    let mutation = source.replace("if index < 2", "if index <= 2");
    assert_ne!(source, mutation);
    std::fs::write(&path, mutation).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&path, &["projected", "trusted_use"], target, optimized);
            assert_eq!(proof(&report, "projected").status, ProofStatus::Refuted);
            assert_eq!(proof(&report, "trusted_use").status, ProofStatus::Refuted);
            assert_eq!(proof(&report, "trusted_use").trusted_calls.len(), 1);
        }
    }
    let additional = (0..1500)
        .map(|index| format!("    budget{index:04}: 0,\n"))
        .collect::<String>();
    let mutation = source.replace("    // EXTRA_ZERO_FIELDS", &additional);
    assert_ne!(source, mutation);
    std::fs::write(&path, mutation).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        let report = verify(&path, &["projected", "trusted_use"], target, false);
        for entry in ["projected", "trusted_use"] {
            let proof = proof(&report, entry);
            assert_eq!(proof.status, ProofStatus::Unknown);
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|obligation| { obligation.detail.contains("2048-node budget") }),
                "{entry}: {proof:?}"
            );
        }
    }
}

#[test]
fn native_zero_sized_shapes_execute() {
    let directory = Directory::new();
    let executable = directory.0.join("native");
    let compiler = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
    let output = Command::new(compiler)
        .args(["--test", "--edition=2024"])
        .arg(fixture())
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let output = Command::new(executable).output().unwrap();
    assert!(output.status.success(), "{output:?}");
}
