#![forbid(unsafe_code)]
use miren::{ProofStatus, Report, UnknownCategory};
use std::path::{Path, PathBuf};
use std::process::Command;
#[path = "support/table_verification.rs"]
mod table_verification;
use std::time::{Duration, Instant};
use table_verification::{Directory, native, verify};

#[derive(Clone, Copy)]
enum NativeControl {
    Accessor,
    Destructor,
    FieldlessDestructor,
}

fn native_control(source: &Path, optimized: bool, control: NativeControl) {
    let directory = Directory::new();
    let executable = directory.0.join("native");
    let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
    compiler
        .args(["--test", "--edition=2024", "-Coverflow-checks=yes"])
        .arg(source)
        .arg("-o")
        .arg(&executable);
    if optimized {
        compiler.arg("-Copt-level=2");
    }
    let output = compiler.output().unwrap();
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    let stdout = directory.0.join("native.stdout");
    let stderr = directory.0.join("native.stderr");
    let mut child = Command::new(executable)
        .stdout(std::fs::File::create(&stdout).unwrap())
        .stderr(std::fs::File::create(&stderr).unwrap())
        .spawn()
        .unwrap();
    let start = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if start.elapsed() >= Duration::from_secs(10) {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("finite native Drop projection fixture exceeded ten seconds");
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let stdout = std::fs::read_to_string(stdout).unwrap();
    let stderr = std::fs::read_to_string(stderr).unwrap();
    match control {
        NativeControl::Accessor => {
            assert_eq!(status.code(), Some(101), "{stdout}\n{stderr}");
            assert!(
                stdout.contains(concat!(
                    "assertion failed: actual_word(&selected.word) == ",
                    "if index == 0 { 3 } else { 7 }"
                )),
                "{stdout}"
            );
        }
        NativeControl::Destructor | NativeControl::FieldlessDestructor => {
            assert_eq!(status.code(), None, "{stdout}\n{stderr}");
            #[cfg(unix)]
            {
                use std::os::unix::process::ExitStatusExt;
                assert_eq!(status.signal(), Some(6), "{stdout}\n{stderr}");
            }
            #[cfg(not(unix))]
            panic!("destructor abort control requires an observed Unix SIGABRT status");
            let assertion = match control {
                NativeControl::FieldlessDestructor => "assertion failed: fieldless_tag() == 8",
                NativeControl::Destructor => "assertion failed: self.guard == 8",
                NativeControl::Accessor => unreachable!("accessor requires exit101"),
            };
            assert!(stdout.matches(assertion).count() >= 2, "{stdout}");
            let origin = match control {
                NativeControl::FieldlessDestructor => "fieldless_drop",
                NativeControl::Destructor => "borrowed",
                NativeControl::Accessor => unreachable!("accessor requires exit101"),
            };
            assert!(stdout.contains(origin), "{stdout}");
            assert!(
                stderr.contains("panic in a destructor during cleanup"),
                "{stderr}"
            );
            assert!(stderr.contains("aborting"), "{stderr}");
        }
    }
}

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/drop_shared_projections.rs")
}
fn body(report: &Report, entry: &str, expected: &str) {
    let proof = report
        .functions
        .iter()
        .find(|f| f.name == entry)
        .unwrap()
        .proof
        .as_ref()
        .unwrap();
    assert!(
        proof
            .body_entries
            .iter()
            .any(|body| body.function.contains(expected))
    );
}
#[test]
fn genuine_shared_drop_storage_observations_preserve_types_and_refuse_rights() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(
                &fixture(),
                &[
                    ("borrowed", P),
                    ("direct", P),
                    ("nested", P),
                    ("scalar_codecs", P),
                    ("wrong", R),
                    ("unguarded", R),
                    ("whole_receiver_unknown", U),
                    ("mutable_unknown", U),
                    ("raw_unknown", U),
                ],
                target,
                optimized,
                &[],
            );
            body(&report, "borrowed", "actual_word");
            for entry in ["borrowed", "direct", "nested", "scalar_codecs"] {
                body(&report, entry, "Dropped as core::ops::Drop");
            }
            for (entry, reason) in [
                (
                    "whole_receiver_unknown",
                    "cannot materialize or copy a non-Copy owner",
                ),
                ("mutable_unknown", "grants no mutable reference authority"),
                ("raw_unknown", "grants no raw pointer authority"),
            ] {
                let proof = report
                    .functions
                    .iter()
                    .find(|f| f.name == entry)
                    .unwrap()
                    .proof
                    .as_ref()
                    .unwrap();
                assert!(proof.obligations.iter().any(|o| o.status == U
                    && o.unknown_category == Some(UnknownCategory::Semantics)
                    && o.detail.contains(reason)
                    && o.query.is_none()
                    && o.model.is_none()));
            }
        }
    }
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
    }
}
#[test]
fn actual_accessor_and_destructor_mutations_fail_unchanged_borrow_claims() {
    let source = std::fs::read_to_string(fixture()).unwrap();
    for (name, old, new) in [
        (
            "accessor",
            "pub fn actual_word(value: &u16) -> u16 {\n    *value\n}",
            "pub fn actual_word(value: &u16) -> u16 {\n    *value ^ 1\n}",
        ),
        (
            "destructor",
            "assert!(self.guard == 7);",
            "assert!(self.guard == 8);",
        ),
    ] {
        let directory = Directory::new();
        let path = directory.0.join(format!("{name}.rs"));
        assert!(source.contains(old));
        let mutant = source.replacen(old, new, 1);
        assert_ne!(source, mutant);
        std::fs::write(&path, mutant).unwrap();
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for optimized in [false, true] {
                let report = verify(
                    &path,
                    &[("borrowed", ProofStatus::Refuted)],
                    target,
                    optimized,
                    &[],
                );
                body(
                    &report,
                    "borrowed",
                    if name == "accessor" {
                        "actual_word"
                    } else {
                        "Dropped as core::ops::Drop"
                    },
                );
            }
        }
        for optimized in [false, true] {
            native_control(
                &path,
                optimized,
                if name == "accessor" {
                    NativeControl::Accessor
                } else {
                    NativeControl::Destructor
                },
            );
        }
    }
}
#[test]
fn genuine_missing_scalar_accessor_body_stays_unknown_after_typed_borrow() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        let directory = Directory::new();
        let source = directory.0.join("dependency.rs");
        let library = directory.0.join("libdrop_observer_dependency.rlib");
        std::fs::write(
            &source,
            concat!(
                "#![no_std]\n#[inline(never)]\n",
                "pub fn observe(value: &u16) -> u16 { *value }\n"
            ),
        )
        .unwrap();
        let mut command = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
        command
            .args([
                "--crate-type=rlib",
                "--crate-name=drop_observer_dependency",
                "--edition=2024",
                "-Cpanic=abort",
                "-Copt-level=0",
            ])
            .arg(&source)
            .arg("-o")
            .arg(&library);
        if let Some(target) = target {
            command.args(["--target", target]);
        }
        let output = command.output().unwrap();
        assert_eq!(output.status.code(), Some(0), "{output:?}");
        for optimized in [false, true] {
            let report = verify(
                &fixture(),
                &[("missing_accessor", ProofStatus::Unknown)],
                target,
                optimized,
                &[
                    "--cfg=external_control".into(),
                    "--extern".into(),
                    format!("drop_observer_dependency={}", library.display()),
                ],
            );
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "missing_accessor")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(proof.obligations.iter().any(|o| o.unknown_category
                == Some(UnknownCategory::MissingCompilerEvidence)
                && o.detail.contains("MIR body unavailable")
                && o.query.is_none()
                && o.model.is_none()));
        }
    }
}

#[test]
fn fieldless_lazy_views_preserve_original_drop_effects_and_missing_bodies() {
    use ProofStatus::{Proved as P, Refuted as R, Unknown as U};
    let original = std::fs::read_to_string(fixture()).unwrap();
    let directory = Directory::new();
    let mutant = directory.0.join("fieldless_destructor.rs");
    let old = "assert!(fieldless_tag() == 7);";
    assert_eq!(original.matches(old).count(), 1);
    std::fs::write(
        &mutant,
        original.replace(old, "assert!(fieldless_tag() == 8);"),
    )
    .unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(
                &fixture(),
                &[
                    ("fieldless_drop::incoming", P),
                    ("fieldless_drop::local", P),
                    ("fieldless_drop::wrong", R),
                    ("fieldless_drop::unguarded", R),
                    ("fieldless_drop::whole_unknown", U),
                ],
                target,
                optimized,
                &[],
            );
            for entry in ["fieldless_drop::incoming", "fieldless_drop::local"] {
                body(&report, entry, "Fieldless as core::ops::Drop");
                body(&report, entry, "fieldless_tag");
            }
            let changed = verify(
                &mutant,
                &[("fieldless_drop::incoming", R)],
                target,
                optimized,
                &[],
            );
            body(
                &changed,
                "fieldless_drop::incoming",
                "Fieldless as core::ops::Drop",
            );
            let dependency_source = directory.0.join("fieldless_dependency.rs");
            let dependency = directory.0.join("libfieldless_dependency.rlib");
            std::fs::write(
                &dependency_source,
                "#![no_std]\n#[inline(never)] pub fn observe(value: &u16) -> u16 { *value }\n",
            )
            .unwrap();
            let mut compiler = Command::new(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"));
            compiler
                .args([
                    "--crate-type=rlib",
                    "--crate-name=drop_observer_dependency",
                    "--edition=2024",
                    "-Cpanic=abort",
                    "-Copt-level=0",
                ])
                .arg(&dependency_source)
                .arg("-o")
                .arg(&dependency);
            if let Some(target) = target {
                compiler.args(["--target", target]);
            }
            let output = compiler.output().unwrap();
            assert_eq!(output.status.code(), Some(0), "{output:?}");
            let absent = verify(
                &fixture(),
                &[("fieldless_drop::incoming", U)],
                target,
                optimized,
                &[
                    "--cfg=fieldless_missing".into(),
                    "--extern".into(),
                    format!("drop_observer_dependency={}", dependency.display()),
                ],
            );
            body(
                &absent,
                "fieldless_drop::incoming",
                "Fieldless as core::ops::Drop",
            );
            let proof = absent
                .functions
                .iter()
                .find(|function| function.name == "fieldless_drop::incoming")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(
                proof
                    .obligations
                    .iter()
                    .any(|obligation| obligation.unknown_category
                        == Some(UnknownCategory::MissingCompilerEvidence)
                        && obligation.detail.contains("MIR body unavailable")
                        && obligation.query.is_none()
                        && obligation.model.is_none())
            );
        }
    }
    for optimized in [false, true] {
        native(&fixture(), optimized, false);
        native_control(&mutant, optimized, NativeControl::FieldlessDestructor);
    }
}
