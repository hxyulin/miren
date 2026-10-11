#![forbid(unsafe_code)]
use miren::ProofStatus;
use std::path::{Path, PathBuf};
use std::process::Command;
#[path = "support/table_verification.rs"]
mod table_verification;
use table_verification::{Directory, native, verify};

const ENABLED: bool = true;
const MODULES: [&str; 18] = [
    "unsigned8",
    "unsigned16",
    "unsigned32",
    "unsigned64",
    "unsigned128",
    "unsigned_pointer",
    "signed8",
    "signed16",
    "signed32",
    "signed64",
    "signed128",
    "signed_pointer",
    "cross_width",
    "cross_sign",
    "pointer_first",
    "pointer_second",
    "signed_pointer_first",
    "signed_pointer_second",
];
fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/two_argument_integer_tables.rs")
}
fn selected_status(enabled: ProofStatus) -> ProofStatus {
    if ENABLED {
        enabled
    } else {
        ProofStatus::Unknown
    }
}
#[test]
fn two_arguments_preserve_original_types_and_correlated_actual_calls() {
    let mut names = Vec::new();
    for module in MODULES {
        names.push((
            format!("{module}::selected"),
            selected_status(ProofStatus::Proved),
        ));
        names.push((
            format!("{module}::wrong"),
            selected_status(ProofStatus::Refuted),
        ));
        names.push((format!("{module}::opaque"), ProofStatus::Unknown));
    }
    names.push((
        "checked_overflow".into(),
        selected_status(ProofStatus::Refuted),
    ));
    let entries: Vec<_> = names
        .iter()
        .map(|(name, status)| (name.as_str(), *status))
        .collect();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(&fixture(), &entries, target, optimized, &[]);
            if ENABLED {
                for module in MODULES {
                    let proof = report
                        .functions
                        .iter()
                        .find(|f| f.name == format!("{module}::selected"))
                        .unwrap()
                        .proof
                        .as_ref()
                        .unwrap();
                    for helper in ["first", "second"] {
                        assert!(
                            proof
                                .body_entries
                                .iter()
                                .any(|entry| entry.function == format!("{module}::{helper}"))
                        );
                    }
                }
            }
        }
    }
}
#[test]
fn actual_two_argument_helper_and_order_mutations_fail_unchanged_claims() {
    let directory = Directory::new();
    let original = fixture();
    let source = std::fs::read_to_string(&original).unwrap();
    let names: Vec<_> = MODULES.map(|module| format!("{module}::selected")).into();
    let entries: Vec<_> = names
        .iter()
        .map(|name| (name.as_str(), selected_status(ProofStatus::Refuted)))
        .collect();
    for optimized in [false, true] {
        native(&original, optimized, false);
    }
    for (name, old, new) in [
        (
            "helper",
            "wrapping_add(b as $r) ^ 1",
            "wrapping_add(b as $r) ^ 3",
        ),
        ("order", "[first, second]", "[second, first]"),
    ] {
        let position = source.find(old).unwrap();
        let mut changed = source.clone();
        changed.replace_range(position..position + old.len(), new);
        let path = directory.0.join(format!("{name}.rs"));
        std::fs::write(&path, changed).unwrap();
        for optimized in [false, true] {
            native(&path, optimized, true);
        }
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for optimized in [false, true] {
                verify(&path, &entries, target, optimized, &[]);
            }
        }
    }
}
#[test]
fn genuine_two_argument_dependency_bodies_remain_required() {
    let directory = Directory::new();
    let dependency = directory.0.join("dependency.rs");
    std::fs::write(
        &dependency,
        r#"#![no_std]
#![forbid(unsafe_code)]
#[inline(never)] pub fn first(a: u16, b: i32) -> i64 { (a as i64) + (b as i64) }
#[inline(never)] pub fn second(a: u16, b: i32) -> i64 { (a as i64) - (b as i64) }
#[inline(never)] pub fn constant(_: u16, _: i32) -> i64 { 7 }
"#,
    )
    .unwrap();
    let caller = directory.0.join("caller.rs");
    std::fs::write(
        &caller,
        r#"#![no_std]
#![forbid(unsafe_code)]
pub fn selected(index: usize, a: u16, b: i32) {
    let table: [fn(u16,i32)->i64;2] = [two_argument_external::first,two_argument_external::second];
    if index < 2 {
        let actual = table[index](a,b);
        assert!(actual == if index == 0 { (a as i64)+(b as i64) } else { (a as i64)-(b as i64) });
    }
}
pub fn constant(index: usize, a: u16, b: i32) {
    let table: [fn(u16,i32)->i64;2] = [two_argument_external::constant;2];
    if index < 2 { assert!(table[index](a,b) == 7); }
}
pub fn literal_constant(index: usize, a: u16, b: i32) {
    let table: [fn(u16,i32)->i64;2] =
        [two_argument_external::constant,two_argument_external::constant];
    if index < 2 { assert!(table[index](a,b) == 7); }
}
"#,
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            for retained in [false, true] {
                let archive = directory.0.join(format!(
                    "lib{}-{}-{retained}.rlib",
                    target.unwrap_or("host"),
                    optimized,
                ));
                let mut command = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
                command
                    .args([
                        "--crate-type=rlib",
                        "--crate-name=two_argument_external",
                        "--edition=2024",
                        "-Cpanic=abort",
                    ])
                    .arg(if retained {
                        "-Zalways-encode-mir=yes"
                    } else {
                        "-Zalways-encode-mir=no"
                    })
                    .arg(if optimized {
                        "-Copt-level=2"
                    } else {
                        "-Copt-level=0"
                    })
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
                let expected = if retained {
                    selected_status(ProofStatus::Proved)
                } else {
                    ProofStatus::Unknown
                };
                let report = verify(
                    &caller,
                    &[
                        ("selected", expected),
                        ("constant", ProofStatus::Unknown),
                        ("literal_constant", expected),
                    ],
                    target,
                    optimized,
                    &[
                        "--extern".into(),
                        format!("two_argument_external={}", archive.display()),
                    ],
                );
                let repeat = report
                    .functions
                    .iter()
                    .find(|f| f.name == "constant")
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert!(
                    repeat
                        .obligations
                        .iter()
                        .any(|q| q.detail
                            == "constant bb0: repeat operand needs a small owned value")
                );
                assert!(
                    !repeat
                        .body_entries
                        .iter()
                        .any(|entry| entry.function == "two_argument_external::constant")
                );
                if ENABLED && retained {
                    let literal = report
                        .functions
                        .iter()
                        .find(|f| f.name == "literal_constant")
                        .unwrap()
                        .proof
                        .as_ref()
                        .unwrap();
                    assert!(
                        literal
                            .body_entries
                            .iter()
                            .any(|entry| entry.function == "two_argument_external::constant")
                    );
                }
                if ENABLED && !retained {
                    for function in report.functions.iter().filter(|function| {
                        matches!(function.name.as_str(), "selected" | "literal_constant")
                    }) {
                        assert!(
                            function
                                .proof
                                .as_ref()
                                .unwrap()
                                .obligations
                                .iter()
                                .any(|q| q.unknown_category
                                    == Some(miren::UnknownCategory::MissingCompilerEvidence))
                        );
                    }
                }
            }
        }
    }
}
