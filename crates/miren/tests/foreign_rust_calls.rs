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
            std::env::temp_dir().join(format!("miren-foreign-rust-{}-{id}", std::process::id()));
        std::fs::create_dir_all(&path).unwrap();
        Self(path)
    }
}

impl Drop for Directory {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn registry_dependency() -> PathBuf {
    let cargo_home = std::env::var_os("CARGO_HOME")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(std::env::var_os("HOME").unwrap()).join(".cargo"));
    std::fs::read_dir(cargo_home.join("registry/src"))
        .unwrap()
        .map(|entry| entry.unwrap().path().join("critical-section-1.2.0"))
        .find(|path| path.join("src/lib.rs").is_file())
        .expect("fleet's pinned critical-section 1.2.0 registry sources")
}

fn replace_body(source: &str, signature: &str, body: &str) -> String {
    let start = source.find(signature).unwrap() + signature.len();
    let mut depth = 1usize;
    let end = source[start..]
        .char_indices()
        .find_map(|(index, ch)| {
            match ch {
                '{' => depth += 1,
                '}' => depth -= 1,
                _ => {}
            }
            (depth == 0).then_some(start + index)
        })
        .unwrap();
    format!("{}{body}{}", &source[..start], &source[end..])
}

#[derive(Clone, Copy, Debug)]
enum Boundary {
    Ordinary,
    CAbi,
    NativeLibrary,
    Duplicate,
    SafeExport,
    SafeDeclaration,
    WrongReturnType,
}

fn dependency(
    directory: &Path,
    body: Option<&str>,
    target: Option<&str>,
    optimized: bool,
    boundary: Boundary,
) -> PathBuf {
    let original = registry_dependency();
    let source_dir = directory.join("third_party/src");
    std::fs::create_dir_all(&source_dir).unwrap();
    std::fs::copy(
        original.join("README.md"),
        directory.join("third_party/README.md"),
    )
    .unwrap();
    for entry in std::fs::read_dir(original.join("src")).unwrap() {
        let path = entry.unwrap().path();
        std::fs::copy(&path, source_dir.join(path.file_name().unwrap())).unwrap();
    }
    let mut source = std::fs::read_to_string(original.join("src/lib.rs")).unwrap();
    if let Some(body) = body {
        // Only this temporary copy of an existing third-party implementation is mutated.
        // Its unsafe declarations, trait implementation and export macro remain third-party text.
        // The crate under analysis and this test both forbid unsafe code.
        let implementation = std::fs::read_to_string(original.join("src/std.rs")).unwrap();
        let start = implementation.find("struct StdCriticalSection;").unwrap();
        let end = implementation.find("#[cfg(test)]").unwrap();
        let implementation =
            replace_body(&implementation[start..end], "fn acquire() -> bool {", body);
        let implementation = replace_body(
            &implementation,
            "fn release(nested_cs: bool) {",
            "let _ = nested_cs;",
        );
        std::fs::write(source_dir.join("fixture_impl.rs"), implementation).unwrap();
        source.push_str("\nmod fixture_impl;\n");
        if matches!(boundary, Boundary::Duplicate) {
            std::fs::copy(
                source_dir.join("fixture_impl.rs"),
                source_dir.join("competing_impl.rs"),
            )
            .unwrap();
            source.push_str("\nmod competing_impl;\n");
        }
    }
    match boundary {
        Boundary::Ordinary | Boundary::Duplicate => {}
        Boundary::SafeExport => {
            source = source
                .replace(
                    "unsafe fn _critical_section_1_0_acquire",
                    "fn _critical_section_1_0_acquire",
                )
                .replace(
                    "unsafe fn _critical_section_1_0_release",
                    "fn _critical_section_1_0_release",
                );
            source = replace_body(
                &source,
                "fn _critical_section_1_0_acquire() -> $crate::RawRestoreState {",
                body.unwrap(),
            );
            source = replace_body(
                &source,
                "fn _critical_section_1_0_release(restore_state: $crate::RawRestoreState) {",
                "let _ = restore_state;",
            );
        }
        Boundary::SafeDeclaration => {
            source = source
                .replace("extern \"Rust\" {", "unsafe extern \"Rust\" {")
                .replace(
                    "fn _critical_section_1_0_acquire() -> RawRestoreState;",
                    "safe fn _critical_section_1_0_acquire() -> RawRestoreState;",
                );
        }
        Boundary::WrongReturnType => {
            source = source
                .replace("-> $crate::RawRestoreState {", "-> u8 {")
                .replace("<$t as $crate::Impl>::acquire()", "0u8");
        }
        Boundary::CAbi => {
            let previous = "fn _critical_section_1_0_acquire() -> $crate::RawRestoreState";
            let mutated = source.replace(
                previous,
                "extern \"C\" fn _critical_section_1_0_acquire() -> $crate::RawRestoreState",
            );
            assert_ne!(source, mutated);
            source = mutated;
        }
        Boundary::NativeLibrary => {
            let previous = "extern \"Rust\" {";
            let mutated = source.replace(
                previous,
                "#[link(name = \"miren_fixture_native_boundary\")] extern \"C\" {",
            );
            assert_ne!(source, mutated);
            source = mutated;
        }
    }
    let path = source_dir.join("lib.rs");
    std::fs::write(&path, source).unwrap();
    let artifact = directory.join("libcritical_section.rmeta");
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren-rustc"));
    command
        .arg(Path::new(env!("MIREN_SYSROOT")).join("bin/rustc"))
        .args([
            "--crate-name=critical_section",
            "--crate-type=rlib",
            "--edition=2018",
            "--emit=metadata",
            "--cfg=feature=\"restore-state-bool\"",
            "-Cpanic=abort",
        ])
        .arg(&path)
        .arg("-o")
        .arg(&artifact);
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    if optimized {
        command.arg("-Copt-level=3");
    }
    let output = command.output().unwrap();
    assert!(output.status.success(), "{output:?}");
    artifact
}

fn verify(body: Option<&str>, target: Option<&str>, optimized: bool) -> Report {
    verify_boundary(body, target, optimized, Boundary::Ordinary, None)
}

fn verify_boundary(
    body: Option<&str>,
    target: Option<&str>,
    optimized: bool,
    boundary: Boundary,
    contract: Option<serde_json::Value>,
) -> Report {
    let directory = Directory::new();
    let artifact = dependency(&directory.0, body, target, optimized, boundary);
    let fixture =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/foreign_rust_calls.rs");
    let mut command = Command::new(env!("CARGO_BIN_EXE_miren"));
    if let Some(contract) = contract {
        let path = directory.0.join("contracts.json");
        std::fs::write(&path, serde_json::to_vec(&contract).unwrap()).unwrap();
        command.arg("--contracts").arg(path);
    }
    command.args([
        "--verify",
        "--json",
        "--entry",
        "returned_value",
        "--entry",
        "wrong_value",
        "--",
        "--crate-type=lib",
        "--edition=2024",
        "-Cpanic=abort",
        "-Coverflow-checks=yes",
    ]);
    command
        .arg(fixture)
        .arg(format!("--extern=critical_section={}", artifact.display()))
        .arg("--out-dir")
        .arg(&directory.0);
    if let Some(target) = target {
        command.args(["--target", target]);
    }
    if optimized {
        command.arg("-Copt-level=3");
    }
    let output = command.output().unwrap();
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| panic!("{error}: {output:?}"))
}

fn status(report: &Report, name: &str) -> ProofStatus {
    report
        .functions
        .iter()
        .find(|function| function.name == name)
        .unwrap()
        .proof
        .as_ref()
        .unwrap()
        .status
}

#[test]
fn retained_foreign_rust_bodies_execute_and_body_mutations_fail() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report = verify(Some("false"), target, optimized);
            assert_eq!(
                status(&report, "returned_value"),
                ProofStatus::Proved,
                "{report:?}"
            );
            let proof = report
                .functions
                .iter()
                .find(|f| f.name == "returned_value")
                .unwrap()
                .proof
                .as_ref()
                .unwrap();
            assert!(proof.models.iter().any(|model| model.contains(
                "executes retained critical_section::fixture_impl::_critical_section_1_0_acquire"
            )));
            assert!(proof.models.iter().any(|model| model.contains(
                "executes retained critical_section::fixture_impl::_critical_section_1_0_release"
            )));
            assert_eq!(
                status(&report, "wrong_value"),
                ProofStatus::Refuted,
                "{report:?}"
            );
            assert!(
                report
                    .functions
                    .iter()
                    .filter_map(|f| f.proof.as_ref())
                    .all(|proof| {
                        proof.assumptions.is_empty() && proof.trusted_calls.is_empty()
                    })
            );
            let report = verify(
                Some("panic!(\"mutated third-party acquire\")"),
                target,
                optimized,
            );
            assert_eq!(
                status(&report, "returned_value"),
                ProofStatus::Refuted,
                "{report:?}"
            );
        }
    }
}

#[test]
fn missing_or_unsupported_foreign_bodies_remain_unknown() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for body in [None, Some("core::hint::spin_loop(); false")] {
            let report = verify(body, target, false);
            assert_eq!(
                status(&report, "returned_value"),
                ProofStatus::Unknown,
                "{report:?}"
            );
        }
    }
}

#[test]
fn mismatched_native_and_ambiguous_exports_remain_unknown() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for boundary in [Boundary::CAbi, Boundary::NativeLibrary, Boundary::Duplicate] {
            let report = verify_boundary(Some("false"), target, false, boundary, None);
            assert_eq!(
                status(&report, "returned_value"),
                ProofStatus::Unknown,
                "{boundary:?}: {report:?}"
            );
        }
    }
}

#[test]
fn target_contracts_execute_and_declaration_contracts_are_not_skipped() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        let target_contract = serde_json::json!({"schema_version": 1, "functions": [{
            "function": "critical_section::fixture_impl::_critical_section_1_0_acquire",
            "ensures": ["result == true"]
        }]});
        let report = verify_boundary(
            Some("false"),
            target,
            false,
            Boundary::Ordinary,
            Some(target_contract),
        );
        assert_eq!(
            status(&report, "returned_value"),
            ProofStatus::Refuted,
            "{report:?}"
        );
        let declaration_contract = serde_json::json!({"schema_version": 1, "functions": [{
            "function": "critical_section::acquire::_critical_section_1_0_acquire",
            "ensures": ["result == true"]
        }]});
        let report = verify_boundary(
            Some("false"),
            target,
            false,
            Boundary::Ordinary,
            Some(declaration_contract),
        );
        assert_eq!(
            status(&report, "returned_value"),
            ProofStatus::Unknown,
            "{report:?}"
        );
    }
}

#[test]
fn safe_exports_satisfy_unsafe_declarations_and_execute_their_actual_bodies() {
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for optimized in [false, true] {
            let report =
                verify_boundary(Some("false"), target, optimized, Boundary::SafeExport, None);
            assert_eq!(
                status(&report, "returned_value"),
                ProofStatus::Proved,
                "{report:?}"
            );
            assert_eq!(
                status(&report, "wrong_value"),
                ProofStatus::Refuted,
                "{report:?}"
            );
            let mutated = verify_boundary(
                Some("panic!(\"mutated safe export\")"),
                target,
                optimized,
                Boundary::SafeExport,
                None,
            );
            assert_eq!(
                status(&mutated, "returned_value"),
                ProofStatus::Refuted,
                "{mutated:?}"
            );
            for boundary in [Boundary::SafeDeclaration, Boundary::WrongReturnType] {
                let report = verify_boundary(Some("false"), target, optimized, boundary, None);
                assert_eq!(
                    status(&report, "returned_value"),
                    ProofStatus::Unknown,
                    "{report:?}"
                );
            }
        }
    }
}

fn native_safe_export(body: &str) -> bool {
    let directory = Directory::new();
    dependency(&directory.0, Some(body), None, false, Boundary::SafeExport);
    let compiler = Path::new(env!("MIREN_SYSROOT")).join("bin/rustc");
    let artifact = directory.0.join("libcritical_section.rlib");
    let output = Command::new(&compiler)
        .args([
            "--crate-name=critical_section",
            "--crate-type=rlib",
            "--edition=2018",
            "--cfg=feature=\"restore-state-bool\"",
        ])
        .arg(directory.0.join("third_party/src/lib.rs"))
        .arg("-o")
        .arg(&artifact)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let fixture =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/foreign_rust_calls.rs");
    let mut source = std::fs::read_to_string(fixture).unwrap();
    source.push_str("\n#[cfg(test)] #[test] fn native_returned_value() { returned_value(); }\n");
    let path = directory.0.join("native.rs");
    std::fs::write(&path, source).unwrap();
    let executable = directory.0.join("native");
    let output = Command::new(compiler)
        .args(["--test", "--edition=2024"])
        .arg(path)
        .arg(format!("--extern=critical_section={}", artifact.display()))
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    Command::new(executable).output().unwrap().status.success()
}

#[test]
fn safe_export_body_mutation_also_fails_native_execution() {
    assert!(native_safe_export("false"));
    assert!(!native_safe_export("panic!(\"mutated safe export\")"));
}
