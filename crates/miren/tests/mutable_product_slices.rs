#![forbid(unsafe_code)]
use miren::{ProofStatus, Report};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "miren-product-slices-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/mutable_product_slices.rs")
}
fn inspect(source: &Path, entries: &[(&str, ProofStatus)]) {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let scratch = Scratch::new();
            let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
            command.args(["--verify", "--json", "--quiet"]);
            for (name, _) in entries {
                command.args(["--entry", name]);
            }
            command
                .args([
                    "--",
                    "--crate-type=lib",
                    "--crate-name=mutable_product_slices",
                    "--edition=2024",
                    "-Cpanic=abort",
                    "-Coverflow-checks=yes",
                ])
                .arg(source)
                .arg("--out-dir")
                .arg(&scratch.0)
                .arg(format!("-Copt-level={level}"));
            if let Some(target) = target {
                command.args(["--target", target]);
            }
            let output = command.output().unwrap();
            let report: Report = serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
                panic!("{error}: {}", String::from_utf8_lossy(&output.stderr))
            });
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
                    "{name}/{target:?}/{level}: {proof:?}"
                );
                assert!(
                    proof.assumptions.is_empty()
                        && proof.entry_assumptions.is_empty()
                        && proof.trusted_calls.is_empty()
                );
                match expected {
                    ProofStatus::Proved => assert!(
                        proof
                            .obligations
                            .iter()
                            .all(|o| o.status == ProofStatus::Proved)
                    ),
                    ProofStatus::Refuted => assert!(
                        proof
                            .obligations
                            .iter()
                            .any(|o| o.status == ProofStatus::Refuted
                                && o.query.is_some()
                                && o.model.is_some())
                    ),
                    ProofStatus::Unknown => assert!(
                        proof
                            .obligations
                            .iter()
                            .any(|o| o.status == ProofStatus::Unknown
                                && o.query.is_none()
                                && o.model.is_none())
                    ),
                    ProofStatus::ProvedWithAssumptions => panic!("new premises are forbidden"),
                }
                if *name == "copied_helper" {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|b| b.function == "observe_bits")
                    );
                }
                if matches!(
                    *name,
                    "store_nan" | "wrong_stored_bits" | "outer_retention" | "unsupported_child"
                ) {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|b| b.function == "stored_word")
                    );
                }
            }
        }
    }
}

#[test]
fn mutable_product_root_storage_metadata_and_refusals() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    inspect(
        &fixture(),
        &[
            ("metadata32", P),
            ("metadata64", P),
            ("wrong_metadata", R),
            ("copied_helper", P),
            ("store_nan", P),
            ("wrong_stored_bits", R),
            ("wrong_untouched_leaf", R),
            ("whole64", P),
            ("outer_retention", P),
            ("unguarded", R),
            ("integer_pair", P),
            ("tuple_pair", P),
            ("struct_fields", P),
            ("zero_inner", P),
            ("proper_reborrow", P),
            ("unsupported_child", P),
            ("symbolic_suffix", P),
            ("pointer_product", U),
            ("reference_product", U),
            ("niche_product", U),
            ("oversized", U),
        ],
    );
}

fn mutate(source: &str, original: &str, changed: &str) -> String {
    assert_eq!(source.matches(original).count(), 1);
    source.replace(original, changed)
}
fn helper_mutant(source: &str) -> String {
    mutate(
        source,
        "pub fn observe_bits(value: f32) -> u32 {\n    value.to_bits()\n}",
        "pub fn observe_bits(value: f32) -> u32 {\n    value.to_bits() ^ 1\n}",
    )
}
fn store_mutant(source: &str) -> String {
    mutate(
        source,
        "pub fn stored_word() -> f32 {\n    f32::from_bits(0x7fc0_1234)\n}",
        "pub fn stored_word() -> f32 {\n    f32::from_bits(0x7fc0_1235)\n}",
    )
}

#[test]
fn actual_helper_and_store_mutations_preserve_caller_claims() {
    let scratch = Scratch::new();
    let source = std::fs::read_to_string(fixture()).unwrap();
    for (name, mutant, entry) in [
        ("helper", helper_mutant(&source), "copied_helper"),
        ("store", store_mutant(&source), "store_nan"),
    ] {
        let path = scratch.0.join(format!("{name}.rs"));
        std::fs::write(&path, mutant).unwrap();
        inspect(&path, &[(entry, ProofStatus::Refuted)]);
    }
}

#[test]
fn genuine_native_originals_pass_and_mutants_fail() {
    let scratch = Scratch::new();
    let original = std::fs::read_to_string(fixture()).unwrap();
    let helper = helper_mutant(&original);
    let store = store_mutant(&original);
    for (label, source, test, expected) in [
        (
            "original-helper",
            &original,
            "native::copied_helper_claims",
            0,
        ),
        (
            "original-store",
            &original,
            "native::actual_store_claims",
            0,
        ),
        (
            "mutant-helper",
            &helper,
            "native::copied_helper_claims",
            101,
        ),
        ("mutant-store", &store, "native::actual_store_claims", 101),
    ] {
        let path = scratch.0.join(format!("{label}.rs"));
        std::fs::write(&path, source).unwrap();
        for level in [0, 2] {
            let executable = scratch.0.join(format!("{label}-{level}"));
            let result = Command::new("rustc")
                .arg(&path)
                .args(["--test", "--edition=2024", "-Coverflow-checks=yes"])
                .arg(format!("-Copt-level={level}"))
                .arg("-o")
                .arg(&executable)
                .output()
                .unwrap();
            assert!(
                result.status.success(),
                "{}",
                String::from_utf8_lossy(&result.stderr)
            );
            let result = Command::new(executable)
                .args(["--exact", test])
                .output()
                .unwrap();
            assert_eq!(result.status.code(), Some(expected));
            assert!(
                String::from_utf8(result.stdout)
                    .unwrap()
                    .contains(if expected == 0 {
                        "test result: ok. 1 passed; 0 failed;"
                    } else {
                        "test result: FAILED. 0 passed; 1 failed;"
                    })
            );
        }
    }
}

#[test]
fn external_copied_helper_requires_an_actual_available_body() {
    let scratch = Scratch::new();
    let dependency = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/mutable_product_dependency.rs");
    let original = std::fs::read_to_string(dependency).unwrap();
    let changed = helper_mutant(&original);
    let caller = scratch.0.join("caller.rs");
    std::fs::write(
        &caller,
        concat!(
            "#![no_std]\n#![forbid(unsafe_code)]\n",
            "extern crate mutable_product_dependency;\n",
            "pub fn external_root(values:&mut[[f32;2]],index:usize) {\n",
            "if index<values.len() {let value=values[index][0];\n",
            "assert!(mutable_product_dependency::observe_bits(value)==value.to_bits());}}\n",
        ),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            for (name, source, encoded, expected) in [
                ("available", &original, true, ProofStatus::Proved),
                ("mutated", &changed, true, ProofStatus::Refuted),
                ("unavailable", &original, false, ProofStatus::Unknown),
            ] {
                let output = scratch.0.join(format!("{name}-{target:?}-{level}"));
                std::fs::create_dir(&output).unwrap();
                let dep = output.join("dependency.rs");
                std::fs::write(&dep, source).unwrap();
                let library = output.join("libmutable_product_dependency.rlib");
                let mut command = Command::new("rustc");
                command
                    .arg(&dep)
                    .args([
                        "--crate-type=rlib",
                        "--edition=2024",
                        "--crate-name=mutable_product_dependency",
                        "-Cpanic=abort",
                    ])
                    .arg(format!("-Copt-level={level}"))
                    .arg("-o")
                    .arg(&library);
                if encoded {
                    command.arg("-Zalways-encode-mir=yes");
                }
                if let Some(target) = target {
                    command.args(["--target", target]);
                }
                let compiled = command.output().unwrap();
                assert!(
                    compiled.status.success(),
                    "{}",
                    String::from_utf8_lossy(&compiled.stderr)
                );
                let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
                command
                    .args([
                        "--verify",
                        "--json",
                        "--quiet",
                        "--entry",
                        "external_root",
                        "--",
                        "--crate-type=lib",
                        "--crate-name=mutable_product_caller",
                        "--edition=2024",
                        "-Cpanic=abort",
                        "-Coverflow-checks=yes",
                    ])
                    .arg(&caller)
                    .arg("--out-dir")
                    .arg(&output)
                    .arg(format!("-Copt-level={level}"))
                    .arg("--extern")
                    .arg(format!("mutable_product_dependency={}", library.display()));
                if let Some(target) = target {
                    command.args(["--target", target]);
                }
                let output = command.output().unwrap();
                let report: Report =
                    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
                        panic!("{error}: {}", String::from_utf8_lossy(&output.stderr))
                    });
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == "external_root")
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert_eq!(
                    proof.status, expected,
                    "{name}/{target:?}/{level}: {proof:?}"
                );
                assert_eq!(output.status.success(), expected == ProofStatus::Proved);
                assert!(
                    proof.assumptions.is_empty()
                        && proof.entry_assumptions.is_empty()
                        && proof.trusted_calls.is_empty()
                );
                match expected {
                    ProofStatus::Proved | ProofStatus::Refuted => {
                        assert!(
                            proof.body_entries.iter().any(|entry| entry.function
                                == "mutable_product_dependency::observe_bits")
                        )
                    }
                    ProofStatus::Unknown => assert!(
                        proof
                            .obligations
                            .iter()
                            .any(|o| o.status == ProofStatus::Unknown && o.detail.contains("MIR"))
                    ),
                    ProofStatus::ProvedWithAssumptions => panic!("unexpected premises"),
                }
                if expected == ProofStatus::Refuted {
                    assert!(
                        proof
                            .obligations
                            .iter()
                            .any(|o| o.status == ProofStatus::Refuted
                                && o.query.is_some()
                                && o.model.is_some())
                    );
                }
            }
        }
    }
}
