#![forbid(unsafe_code)]
use miren::{ProofStatus, Report, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "miren-product-symbolic-{}-{}",
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
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/mutable_product_symbolic_suffix.rs")
}
fn check_report(output: std::process::Output, entries: &[(&str, ProofStatus)]) {
    let report: Report = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|e| panic!("{e}: {}", String::from_utf8_lossy(&output.stderr)));
    assert_eq!(
        output.status.code(),
        Some(
            if entries
                .iter()
                .all(|(_, status)| *status == ProofStatus::Proved)
            {
                0
            } else {
                1
            }
        )
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
        assert_eq!(proof.status, *expected, "{name}: {proof:?}");
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
            ProofStatus::Unknown => {
                // These are prospective exact frontiers. Initial raw captures must corroborate
                // them; an unrelated UNKNOWN never satisfies this control.
                let (category, reason) = match *name {
                    "alias_unknown" => (
                        UnknownCategory::Semantics,
                        "mutable u16 staging needs a private whole tip",
                    ),
                    "budget_unknown" | "whole_budget" => (
                        UnknownCategory::ResourceLimit,
                        concat!(
                            "mutable product symbolic projection exceeds",
                            " its shared node or depth budget",
                        ),
                    ),
                    "external_root" => (
                        UnknownCategory::MissingCompilerEvidence,
                        "MIR body unavailable for product_child_dependency::actual_float",
                    ),
                    _ => panic!("missing exact UNKNOWN control for {name}"),
                };
                assert!(
                    proof.obligations.iter().any(|o| {
                        o.status == ProofStatus::Unknown
                            && o.unknown_category == Some(category)
                            && o.detail.contains(reason)
                            && o.query.is_none()
                            && o.model.is_none()
                    }),
                    "{name}: {proof:?}"
                );
            }
            ProofStatus::ProvedWithAssumptions => panic!("new premises are forbidden"),
        }
        if matches!(*name, "float_selected" | "current_child") {
            for helper in ["actual_float", "actual_inner"] {
                assert!(
                    proof.body_entries.iter().any(|b| b.function == helper),
                    "{helper}"
                );
            }
        }
        if *name == "external_root" && *expected != ProofStatus::Unknown {
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|b| b.function == "product_child_dependency::actual_float")
            );
        }
    }
}
fn inspect(source: &Path, entries: &[(&str, ProofStatus)]) {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let scratch = Scratch::new();
            let mut cmd = Command::new(env!("CARGO_BIN_EXE_miren"));
            cmd.args(["--verify", "--json", "--quiet"]);
            for (name, _) in entries {
                cmd.args(["--entry", name]);
            }
            cmd.args([
                "--",
                "--crate-type=lib",
                "--crate-name=mutable_product_symbolic_suffix",
                "--edition=2024",
                "-Cpanic=abort",
                "-Coverflow-checks=yes",
            ])
            .arg(source)
            .arg("--out-dir")
            .arg(&scratch.0)
            .arg(format!("-Copt-level={level}"));
            if let Some(target) = target {
                cmd.args(["--target", target]);
            }
            check_report(cmd.output().unwrap(), entries);
        }
    }
}
#[test]
fn actual_symbolic_suffix_preserves_current_typed_storage_and_refusals() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    inspect(
        &fixture(),
        &[
            ("float_selected", P),
            ("float_other_outer", P),
            ("two_indices", P),
            ("correlated", P),
            ("bool_selected", P),
            ("char_selected", P),
            ("whole_tuple", P),
            ("whole_array", P),
            ("record_fields", P),
            ("tuple_fields", P),
            ("whole_record", P),
            ("zero_selected", P),
            ("sequential", P),
            ("branch", P),
            ("current_child", P),
            ("wrong_float", R),
            ("wrong_retention", R),
            ("unguarded_inner", R),
            ("alias_unknown", U),
            ("budget_unknown", U),
            ("whole_budget", U),
        ],
    );
}

fn changed_payload(source: &str) -> String {
    assert_eq!(source.matches("0x7fc0_1234").count(), 1);
    source.replace("0x7fc0_1234", "0x7fc0_1235")
}
fn helper_mutant(source: &str) -> String {
    assert_eq!(source.matches("index ^ 0").count(), 1);
    source.replace("index ^ 0", "index ^ 1")
}
fn payload_mutant(source: &str) -> String {
    let old = "pub fn actual_float() -> f32 {\n    f32::from_bits(0x7fc0_1234)\n}";
    assert_eq!(source.matches(old).count(), 1);
    source.replace(old, &changed_payload(old))
}

#[test]
fn actual_index_and_payload_mutants_refute_unchanged_caller_claims() {
    let scratch = Scratch::new();
    let original = std::fs::read_to_string(fixture()).unwrap();
    for (name, mutant) in [
        ("helper", helper_mutant(&original)),
        ("payload", payload_mutant(&original)),
    ] {
        let path = scratch.0.join(format!("{name}.rs"));
        std::fs::write(&path, mutant).unwrap();
        inspect(
            &path,
            &[
                ("float_selected", ProofStatus::Refuted),
                ("current_child", ProofStatus::Refuted),
            ],
        );
    }
}
#[test]
fn genuine_native_symbolic_original_and_mutants_keep_the_same_claims() {
    let scratch = Scratch::new();
    let original = std::fs::read_to_string(fixture()).unwrap();
    for (name, source, expected) in [
        ("original", original.clone(), 0),
        ("helper", helper_mutant(&original), 101),
        ("payload", payload_mutant(&original), 101),
    ] {
        let path = scratch.0.join(format!("{name}.rs"));
        std::fs::write(&path, source).unwrap();
        for level in [0, 2] {
            let exe = scratch.0.join(format!("{name}-{level}"));
            let result = Command::new("rustc")
                .arg(&path)
                .args(["--test", "--edition=2024", "-Coverflow-checks=yes"])
                .arg(format!("-Copt-level={level}"))
                .arg("-o")
                .arg(&exe)
                .output()
                .unwrap();
            assert!(result.status.success(), "{result:?}");
            let result = Command::new(&exe)
                .args([
                    "--exact",
                    "native::actual_symbolic_callers_preserve_the_same_store_claims",
                ])
                .output()
                .unwrap();
            assert_eq!(result.status.code(), Some(expected), "{result:?}");
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
fn exact_retained_and_missing_symbolic_rhs_dependency_bodies() {
    let scratch = Scratch::new();
    let source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/mutable_product_symbolic_suffix_dependency.rs");
    let original = std::fs::read_to_string(source).unwrap();
    let changed = changed_payload(&original);
    let caller = scratch.0.join("caller.rs");
    std::fs::write(
        &caller,
        concat!(
            "#![no_std]\n#![forbid(unsafe_code)]\nextern crate product_child_dependency;\n",
            "pub fn external_root(values:&mut[[f32;2]],outer:usize,inner:usize) {\n",
            "if outer<values.len()&&inner<2{let old=values[outer][1-inner].to_bits();\n",
            "values[outer][inner]=product_child_dependency::actual_float();\n",
            "assert!(values[outer][inner].to_bits()==0x7fc0_1234);\n",
            "assert!(values[outer][1-inner].to_bits()==old);}}\n",
        ),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            for (name, source, encoded, expected) in [
                ("retained", &original, true, ProofStatus::Proved),
                ("changed", &changed, true, ProofStatus::Refuted),
                ("missing", &original, false, ProofStatus::Unknown),
            ] {
                let out = scratch.0.join(format!("{name}-{target:?}-{level}"));
                std::fs::create_dir(&out).unwrap();
                let dep = out.join("dependency.rs");
                std::fs::write(&dep, source).unwrap();
                let library = out.join("libproduct_child_dependency.rlib");
                let mut cmd = Command::new("rustc");
                cmd.arg(&dep)
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=product_child_dependency",
                        "--edition=2024",
                        "-Cpanic=abort",
                    ])
                    .arg(format!("-Copt-level={level}"))
                    .arg("-o")
                    .arg(&library);
                if encoded {
                    cmd.arg("-Zalways-encode-mir=yes");
                }
                if let Some(target) = target {
                    cmd.args(["--target", target]);
                }
                let compiled = cmd.output().unwrap();
                assert!(compiled.status.success(), "{compiled:?}");
                let mut cmd = Command::new(env!("CARGO_BIN_EXE_miren"));
                cmd.args([
                    "--verify",
                    "--json",
                    "--quiet",
                    "--entry",
                    "external_root",
                    "--",
                    "--crate-type=lib",
                    "--crate-name=product_child_caller",
                    "--edition=2024",
                    "-Cpanic=abort",
                    "-Coverflow-checks=yes",
                ])
                .arg(&caller)
                .arg("--out-dir")
                .arg(&out)
                .arg(format!("-Copt-level={level}"))
                .arg("--extern")
                .arg(format!("product_child_dependency={}", library.display()));
                if let Some(target) = target {
                    cmd.args(["--target", target]);
                }
                check_report(cmd.output().unwrap(), &[("external_root", expected)]);
            }
        }
    }
}
