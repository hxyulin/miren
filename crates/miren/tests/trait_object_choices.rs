#![forbid(unsafe_code)]
use miren::{ProofStatus, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::Command;
#[path = "support/table_verification.rs"]
mod table_verification;
use table_verification::{Directory, native, verify};

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/trait_object_choices.rs")
}

#[test]
fn stored_shared_choices_dispatch_actual_methods_and_return_sources() {
    let entries = [
        ("constant", ProofStatus::Proved),
        ("symbolic", ProofStatus::Proved),
        ("wrong", ProofStatus::Refuted),
        ("slice_helper", ProofStatus::Proved),
        ("inherited", ProofStatus::Proved),
        ("upcast", ProofStatus::Proved),
        ("opaque", ProofStatus::Unknown),
        ("caller_backed_return", ProofStatus::Proved),
        ("captured_index", ProofStatus::Proved),
        ("repeated", ProofStatus::Proved),
        ("returned_memory", ProofStatus::Proved),
    ];
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&fixture(), &entries, target, optimized, &[]);
            for name in ["symbolic", "slice_helper", "caller_backed_return"] {
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == name)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                for body in ["<Masked as Parent>::read", "<Different as Parent>::read"] {
                    assert!(
                        proof
                            .body_entries
                            .iter()
                            .any(|entry| entry.function == body)
                    );
                }
            }
        }
    }
}

#[test]
fn actual_implementation_mutation_refutes_unchanged_shared_claims() {
    let directory = Directory::new();
    let original = std::fs::read_to_string(fixture()).unwrap();
    let needle = "        self.0 & 15";
    assert_eq!(original.matches(needle).count(), 1);
    let path = directory.0.join("mutant.rs");
    std::fs::write(&path, original.replace(needle, "        self.0")).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(
                &path,
                &[("symbolic", ProofStatus::Refuted)],
                target,
                optimized,
                &[],
            );
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "symbolic")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(
                proof
                    .body_entries
                    .iter()
                    .any(|entry| { entry.function == "<Masked as Parent>::read" })
            );
            assert!(proof.obligations.iter().any(|obligation| {
                obligation.status == ProofStatus::Refuted
                    && obligation.query.is_some()
                    && obligation.model.is_some()
            }));
        }
    }
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
        native(&path, optimized, true);
    }
}

#[test]
fn real_retained_and_omitted_virtual_bodies_remain_distinct() {
    let directory = Directory::new();
    let dependency = directory.0.join("dependency.rs");
    std::fs::write(
        &dependency,
        r#"#![no_std]
#![forbid(unsafe_code)]
pub trait Read { fn read(&self) -> u8; }
pub struct First(pub u8);
pub struct Second(pub u8);
impl Read for First {
    #[inline(never)] fn read(&self) -> u8 { self.0 & 15 }
}
impl Read for Second {
    #[inline(never)] fn read(&self) -> u8 { self.0 % 16 }
}
"#,
    )
    .unwrap();
    let caller = directory.0.join("caller.rs");
    std::fs::write(
        &caller,
        r#"#![no_std]
#![forbid(unsafe_code)]
use shared_choice_dependency::{Read, First, Second};
#[inline(never)] fn invoke(value: &dyn Read) -> u8 { value.read() }
pub fn selected(word: u8, index: usize) {
    if index >= 2 { return; }
    let first = First(word);
    let second = Second(word);
    let values: [&dyn Read;2] = [&first, &second];
    assert!(invoke(values[index]) <= 15);
}
pub fn constant() {
    let first = First(7);
    let value: &dyn Read = &first;
    assert!(invoke(value) == 7);
}
"#,
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let archive = directory.0.join(format!(
                    "libshared_choice_dependency-{}-{optimized}-{retained}.rlib",
                    target.unwrap_or("host")
                ));
                let mut command = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
                command
                    .args([
                        "--sysroot",
                        env!("MIREN_SYSROOT"),
                        "--crate-type=rlib",
                        "--edition=2024",
                        "--crate-name=shared_choice_dependency",
                        "-Cpanic=abort",
                        "-Coverflow-checks=yes",
                    ])
                    .arg(format!("-Copt-level={}", if optimized { 2 } else { 0 }))
                    .arg(format!(
                        "-Zalways-encode-mir={}",
                        if retained { "yes" } else { "no" }
                    ))
                    .arg(&dependency)
                    .arg("-o")
                    .arg(&archive);
                if let Some(target) = target {
                    command.args(["--target", target]);
                }
                let output = command.output().unwrap();
                assert!(
                    output.status.success(),
                    "{}",
                    String::from_utf8_lossy(&output.stderr)
                );
                let flag = format!("shared_choice_dependency={}", archive.display());
                let status = if retained {
                    ProofStatus::Proved
                } else {
                    ProofStatus::Unknown
                };
                let report = verify(
                    &caller,
                    &[("selected", status), ("constant", status)],
                    target,
                    optimized,
                    &["--extern".to_owned(), flag],
                );
                for name in ["selected", "constant"] {
                    let proof = report
                        .functions
                        .iter()
                        .find(|f| f.name == name)
                        .unwrap()
                        .proof
                        .as_ref()
                        .unwrap();
                    let entered = proof.body_entries.iter().any(|entry| {
                        matches!(
                            entry.function.as_str(),
                            "<shared_choice_dependency::First as \
                                 shared_choice_dependency::Read>::read"
                                | "<shared_choice_dependency::Second as \
                                       shared_choice_dependency::Read>::read"
                        )
                    });
                    if retained {
                        assert!(entered);
                    } else {
                        assert!(!entered);
                        assert!(proof.obligations.iter().any(|obligation| {
                            obligation.unknown_category
                                == Some(UnknownCategory::MissingCompilerEvidence)
                        }));
                    }
                }
            }
        }
    }
}
