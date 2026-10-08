"""Run with python3 -m unittest discover -s tools -p 'test_*.py'."""

import json
import os
import sys
from unittest.mock import patch
from pathlib import Path
import tempfile
import unittest

import fleet_survey as survey


class SurveyTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.source = self.directory / "lib.rs"
        self.source.write_text("pub fn checked() {}\n")
        self.unit = {"id": "./sample/sample", "crate_name": "sample", "kinds": ["lib"],
                     "source": str(self.source)}
        self.inventory = {"schema_version": 9, "crate_name": "sample", "compiler": "fake",
                          "target": "arm", "panic_strategy": "abort", "mir_phase": "runtime",
                          "overflow_checks": True, "rustc_arguments": [
            "--crate-name", "sample", "--crate-type", "lib", str(self.source)],
            "functions": [{"name": "checked", "source": {
                "file": str(self.source), "line": 1, "column": 1}}]}

    def roots(self, status="proved", failure=None):
        verified = json.loads(json.dumps(self.inventory))
        verified["functions"][0]["proof"] = {"status": status, "obligations": []}
        return survey.root_records(self.unit, self.inventory, verified, failure,
                                   self.directory, self.directory)

    def test_outcomes_are_distinct(self):
        for status in sorted(survey.STATUSES):
            with self.subTest(status=status):
                root = self.roots(status)[0]
                self.assertEqual(root["status"], status)
                self.assertEqual(root["classification"], "source_function_heuristic")

    def test_failed_process_cannot_prove(self):
        self.assertEqual(self.roots(failure="compiler crashed")[0]["status"], "unknown")

    def test_missing_mutated_and_invalid_proofs_cannot_prove(self):
        verified = json.loads(json.dumps(self.inventory))
        for change in ("missing", "name", "source", "status", "assumptions"):
            with self.subTest(change=change):
                report = json.loads(json.dumps(verified))
                function = report["functions"][0]
                function["proof"] = {"status": "proved"}
                if change == "missing":
                    report["functions"] = []
                elif change == "name":
                    function["name"] = "different"
                elif change == "source":
                    function["source"]["line"] = 2
                elif change == "status":
                    function["proof"]["status"] = "success"
                else:
                    function["proof"]["assumptions"] = ["trusted"]
                roots = survey.root_records(self.unit, self.inventory, report, None,
                                            self.directory, self.directory)
                self.assertEqual(roots[0]["status"], "unknown")
                self.assertTrue(roots[0]["failure"])

    def test_malformed_jsonl_keeps_partial_reports(self):
        data = (json.dumps(self.inventory) + "\n{bad\n").encode()
        reports, errors = survey.reports(data)
        self.assertEqual(len(reports), 1)
        self.assertEqual(len(errors), 1)

    def test_schema_and_required_fields_reject_malformed_reports(self):
        for key, value in [("schema_version", 99), ("schema_version", True),
                           ("compiler", None), ("target", ""), ("panic_strategy", []),
                           ("mir_phase", None), ("overflow_checks", 1),
                           ("rustc_arguments", [1])]:
            with self.subTest(key=key, value=value):
                report = {**self.inventory, key: value}
                parsed, errors = survey.reports(json.dumps(report).encode())
                self.assertEqual(parsed, [])
                self.assertEqual(len(errors), 1)
        report = {**self.inventory, "functions": []}
        parsed, errors = survey.reports(json.dumps(report).encode())
        self.assertEqual(len(parsed), 1)
        self.assertEqual(errors, [])

    def test_compilation_unit_mutations_fail(self):
        self.assertTrue(survey.unit_matches(self.unit, self.inventory, self.directory))
        for key, value in [("crate_name", "other"), ("rustc_arguments", [])]:
            report = {**self.inventory, key: value}
            self.assertFalse(survey.unit_matches(self.unit, report, self.directory))

    def test_fake_executable_failure_and_timeout_preserve_logs(self):
        executable = self.directory / "fake.py"
        executable.write_text("import sys\nprint('partial')\nsys.exit(1)\n")
        record, data = survey.execute([sys.executable, str(executable)], self.directory,
                                      {}, self.directory / "run", 10)
        self.assertEqual(record["status"], "failed")
        self.assertEqual(data, b"partial\n")
        executable.write_text("import time\ntime.sleep(5)\n")
        record, _ = survey.execute([sys.executable, str(executable)], self.directory,
                                   {}, self.directory / "timeout", 0.05)
        self.assertEqual(record["status"], "timeout")
        self.assertTrue((self.directory / "timeout.command.json").exists())

    def test_diff_stable_ids_and_incompatible_configuration(self):
        previous = {"roots": self.roots(), "provenance": {"target": "arm"}}
        current = {"roots": self.roots("refuted"), "provenance": {"target": "host"}}
        current["roots"][0]["source"]["line"] = 4
        diff = survey.compare(current, previous)
        self.assertEqual(diff["incompatible_provenance"], ["target"])
        self.assertEqual(diff["added"], [])
        self.assertEqual(diff["removed"], [])
        self.assertEqual(diff["changed"][0]["after"], "refuted")

    def test_artifact_fingerprints_cover_transitive_absence_and_generated_inputs(self):
        dependencies = self.directory / "target/deps"
        generated = self.directory / "target/generated"
        dependencies.mkdir(parents=True)
        generated.mkdir()
        dependencies = dependencies.resolve()
        generated = generated.resolve()
        artifact = dependencies / "libdep.rmeta"
        artifact.write_bytes(b"metadata")
        (dependencies / "macro.dylib").write_bytes(b"macro")
        (generated / "included.rs").write_text("const GENERATED: u32 = 1;\n")
        report = {**self.inventory, "rustc_arguments": [
            "--extern=dep=" + str(artifact), "--extern", "other=" + str(artifact),
            "-Ldependency=" + str(dependencies), "-L", "dependency=" + str(dependencies)],
            "compiler_environment": {"OUT_DIR": str(generated)}}
        inputs = survey.artifact_inputs(report, self.directory)
        before = survey.artifact_hashes(inputs)
        sidecar = Path(str(artifact) + ".miren-origins.json")
        self.assertIsNone(before[str(sidecar)])
        self.assertIn(str(dependencies / "macro.dylib"), before)
        for path in [sidecar, dependencies / "transitive.rmeta", generated / "included.rs"]:
            original = path.read_bytes() if path.exists() else None
            path.write_bytes(b"changed")
            self.assertNotEqual(before, survey.artifact_hashes(inputs))
            if original is None:
                path.unlink()
            else:
                path.write_bytes(original)
            self.assertEqual(before, survey.artifact_hashes(inputs))
        with patch.object(survey, "MAX_INPUT_FILES", 1):
            with self.assertRaises(ValueError):
                survey.artifact_hashes(inputs)

    def test_captured_crate_cwd_and_symlink_sidecars_preserve_argument_paths(self):
        workspace = self.directory.resolve()
        crate = workspace / "nested/crate"
        crate.mkdir(parents=True)
        actual = workspace / "actual.rmeta"
        actual.write_bytes(b"metadata")
        link = crate / "linked.rmeta"
        link.symlink_to(actual)
        sidecar = Path(str(link) + ".miren-origins.json")
        sidecar.write_text("{}")
        (crate / "included.rs").write_text("const INPUT: u32 = 1;\n")
        report = {**self.inventory, "working_directory": "nested/crate",
                  "rustc_arguments": ["--extern", "dep=linked.rmeta", "-L", ".",
                                      "-L", "dependency=."],
                  "compiler_environment": {"OUT_DIR": "."}}
        cwd = survey.compiler_cwd(report, workspace)
        inputs = survey.artifact_inputs(report, cwd)
        self.assertIn(str(link), inputs["files"])
        self.assertNotIn(str(actual), inputs["files"])
        self.assertEqual(inputs["directories"][str(crate)], "build")
        fingerprints = survey.artifact_hashes(inputs)
        self.assertEqual(fingerprints[str(sidecar)], survey.digest(sidecar))
        self.assertIn(str(crate / "included.rs"), fingerprints)
        sidecar.write_text('{"changed": true}')
        self.assertNotEqual(fingerprints, survey.artifact_hashes(inputs))

    def test_analyzer_snapshot_survives_original_replacement(self):
        original = self.directory / "miren"
        sibling = self.directory / "miren-rustc"
        original.write_bytes(b"first analyzer")
        sibling.write_bytes(b"first wrapper")
        output = self.directory / "snapshot"
        output.mkdir()
        frozen, hashes = survey.freeze_analyzer(original, output)
        original.write_bytes(b"replacement analyzer")
        sibling.write_bytes(b"replacement wrapper")
        self.assertEqual(frozen.read_bytes(), b"first analyzer")
        self.assertEqual(frozen.with_name("miren-rustc").read_bytes(), b"first wrapper")
        self.assertEqual(hashes["miren"]["original_sha256"], survey.digest(frozen))

    def test_complete_fake_survey_and_failure_mutations(self):
        self.source = self.source.resolve()
        (self.directory / "Cargo.toml").write_text("[package]\nname='sample'\n")
        (self.directory / "miren.json").write_text('{"entries": ["absent"], "startup": true}')
        executable = self.directory / "fake-tool"
        executable.write_text("#!" + sys.executable + "\n" + FAKE_TOOL)
        executable.chmod(0o755)
        for name in ("rustc", "z3"):
            (self.directory / name).symlink_to(executable)
        for mode in ("normal", "host_build", "crate_cwd", "missing", "malformed", "crash",
                     "mismatch",
                     "missing_proof", "configuration_mutation", "file_mutation", "missing_target",
                     "missing_compiler", "unsupported_schema", "artifact_mutation", "new_sidecar",
                     "transitive_mutation", "generated_mutation",
                     "source_mutation", "inventory_fail"):
            with self.subTest(mode=mode):
                self.source.write_text("pub fn checked() {}\n")
                dependencies = self.directory / "target/deps"
                generated = self.directory / "target/generated"
                dependencies.mkdir(parents=True, exist_ok=True)
                generated.mkdir(parents=True, exist_ok=True)
                (dependencies / "libdep.rmeta").write_bytes(b"metadata")
                sidecar = dependencies / "libdep.rmeta.miren-origins.json"
                sidecar.unlink(missing_ok=True)
                (dependencies / "transitive.rmeta").unlink(missing_ok=True)
                (generated / "included.rs").write_text("const GENERATED: u32 = 1;\n")
                output = self.directory / ("output-" + mode)
                args = survey.argparse.Namespace(
                    fleet=self.directory, output=output, analyzer=executable,
                    cargo=str(executable), solver=None, target="arm", profile="dev",
                    features="", jobs=2, build_timeout=10, unit_timeout=10, previous=None,
                    **survey.LIMITS)
                with patch.dict(os.environ, {
                    "PATH": str(self.directory) + os.pathsep + os.environ["PATH"],
                    "FAKE_MODE": mode, "FAKE_ROOT": str(self.directory),
                    "CARGO_REGISTRY_TOKEN": "secret-never-record"}):
                    code = survey.survey(args)
                result = json.loads((output / "summary.json").read_text())
                if mode in ("normal", "host_build", "crate_cwd"):
                    self.assertEqual(code, 0)
                    self.assertEqual(result["counts"]["proved"], 1)
                    self.assertEqual(result["counts"]["refuted"], 1)
                    self.assertEqual(result["counts"]["unknown"], 1)
                else:
                    self.assertEqual(code, 1)
                    self.assertEqual(result["status"], "partial")
                    self.assertEqual(result["counts"]["proved"], 0)
                self.assertNotIn("secret-never-record", (output / "summary.json").read_text())


FAKE_TOOL = r"""
import json
import os
from pathlib import Path
import sys
args = sys.argv[1:]
mode = os.environ.get("FAKE_MODE", "normal")
root = Path(os.environ["FAKE_ROOT"]).resolve()
source = str(root / "lib.rs")
if "-vV" in args or "--version" in args:
    print("fake version 1")
    sys.exit(0)
if "metadata" in args:
    custom = [{"kind": ["custom-build"], "crate_types": ["bin"],
               "name": "build-script-build", "src_path": str(root / "build.rs")}]
    if mode != "host_build":
        custom = []
    print(json.dumps({"workspace_root": str(root), "workspace_members": ["sample"],
                      "packages": [{"id": "sample", "name": "sample", "targets": [{
                          "kind": ["lib"], "crate_types": ["lib"], "name": "sample",
                          "src_path": source}] + custom}]}))
    sys.exit(0)
report = {"schema_version": 9, "crate_name": "sample", "target": "arm",
          "compiler": "fake version 1", "panic_strategy": "abort", "mir_phase": "runtime",
          "overflow_checks": True,
          "working_directory": str(root),
          "compiler_environment": {"OUT_DIR": str(root / "target/generated")},
          "rustc_arguments": ["--crate-name", "sample", "--crate-type", "lib", source,
                              "--extern", "dep=" + str(root / "target/deps/libdep.rmeta"),
                              "-L", "dependency=" + str(root / "target/deps")],
          "functions": [{"name": name, "source": {"file": source, "line": 1, "column": 1}}
                        for name in ["checked", "negative", "unsupported"]]}
if mode == "crate_cwd":
    (root / "nested").mkdir(exist_ok=True)
    report["working_directory"] = "nested"
    report["compiler_environment"]["OUT_DIR"] = "../target/generated"
    report["rustc_arguments"] = ["--crate-name", "sample", "--crate-type", "lib", "../lib.rs",
                                 "--extern", "dep=../target/deps/libdep.rmeta",
                                 "-L", "dependency=../target/deps"]
path = Path(args[args.index("--jsonl") + 1])
if "inventory" in args:
    if "--no-config" not in args:
        sys.exit(2)
    if mode == "inventory_fail":
        sys.exit(1)
else:
    if mode == "missing":
        sys.exit(1)
    if mode == "malformed":
        path.write_text("{bad\n")
        sys.exit(1)
    if mode == "crash":
        sys.exit(2)
    for function, status in zip(report["functions"], ["proved", "refuted", "unknown"]):
        function["proof"] = {"status": status, "obligations": []}
    if mode == "mismatch":
        report["crate_name"] = "other"
    if mode == "missing_proof":
        report["functions"][0]["proof"] = None
    if mode == "artifact_mutation":
        (root / "target/deps/libdep.rmeta").write_bytes(b"different metadata")
    if mode == "new_sidecar":
        (root / "target/deps/libdep.rmeta.miren-origins.json").write_text("{}")
    if mode == "transitive_mutation":
        (root / "target/deps/transitive.rmeta").write_bytes(b"new metadata")
    if mode == "generated_mutation":
        (root / "target/generated/included.rs").write_text("const GENERATED: u32 = 2;\n")
    if mode == "missing_target":
        del report["target"]
    if mode == "missing_compiler":
        del report["compiler"]
    if mode == "unsupported_schema":
        report["schema_version"] = 999
    if mode == "configuration_mutation":
        report["target"] = "different"
    if mode == "file_mutation":
        Path(source).write_text("pub fn changed() {}\n")
    if mode == "source_mutation":
        report["functions"][0]["source"]["line"] = 5
data = json.dumps(report) + "\n"
if mode == "host_build" and "inventory" in args:
    host = dict(report)
    host.update(crate_name="build_script_build", target="host",
                rustc_arguments=["--crate-name", "build_script_build", "--crate-type", "bin",
                                 str(root / "build.rs")])
    data += json.dumps(host) + "\n"
path.write_text(data)
sys.exit(0 if "inventory" in args else 1)
"""


if __name__ == "__main__":
    unittest.main()
