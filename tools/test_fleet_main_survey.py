"""Main surveys retain scope, collection failures and compiler input integrity."""

import argparse
import copy
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import fleet_main_survey as main
import fleet_survey as survey


class MainSurveyTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name).resolve()
        self.source = self.directory / "main.rs"
        self.source.write_text("fn main() {}\n")
        self.unit = {"id": "./sample/bin/sample", "crate_name": "sample", "kinds": ["bin"],
                     "source": str(self.source), "status": "complete"}
        self.inventory = {"schema_version": 9, "compiler": "fake", "target": "arm",
                          "panic_strategy": "abort", "overflow_checks": True,
                          "mir_phase": "runtime", "crate_name": "sample",
                          "working_directory": str(self.directory), "compiler_environment": {},
                          "rustc_arguments": ["--crate-name", "sample", "--crate-type", "bin",
                                              str(self.source)],
                          "functions": [{"name": values[0], "source": {
                              "file": str(self.source), "line": 1, "column": 1}}
                                        for values in main.SCOPES.values()]}

    def report(self, scope="async_body", status="proved"):
        report = copy.deepcopy(self.inventory)
        report["analysis_limits"] = survey.LIMITS
        entry, asynchronous, _ = main.SCOPES[scope]
        function = next(f for f in report["functions"] if f["name"] == entry)
        function["proof"] = {"status": status, "async_entry": asynchronous,
                             "obligations": [] if status == "proved" else [{"status": status}]}
        return report

    def checked(self, report, scope="async_body", returncode=0):
        return main.checked_proof(self.unit, self.inventory, report, self.directory,
                                  scope, survey.LIMITS, returncode)

    def test_positive_refuted_unknown_and_scopes(self):
        for scope in main.SCOPES:
            for status in ("proved", "refuted", "unknown"):
                with self.subTest(scope=scope, status=status):
                    report = self.report(scope, status)
                    self.assertEqual(self.checked(report, scope,
                                                 0 if status == "proved" else 1)["status"], status)

    def test_report_mutations_reject_false_success(self):
        mutations = [lambda r: r.update(target="host"),
                     lambda r: r.update(analysis_limits={}),
                     lambda r: r.update(compiler_environment={"OUT_DIR": "different"}),
                     lambda r: r["functions"][0]["source"].update(line=2),
                     lambda r: r["functions"][0].update(name="other"),
                     lambda r: r["functions"][0]["proof"].update(async_entry=False),
                     lambda r: r["functions"][0]["proof"].update(assumptions=["startup"]),
                     lambda r: r["functions"][0]["proof"].update(trusted_calls=["trusted"]),
                     lambda r: r["functions"][0]["proof"].update(invariants=["induction"]),
                     lambda r: r["functions"][0]["proof"].update(status="proved_with_assumptions"),
                     lambda r: r["functions"][0]["proof"].update(
                         obligations=[{"status": "unknown"}]),
                     lambda r: r["functions"][0]["proof"].update(status="refuted"),
                     lambda r: r["functions"][1].update(proof={"status": "proved"})]
        for index, mutation in enumerate(mutations):
            with self.subTest(index=index):
                report = self.report()
                mutation(report)
                with self.assertRaises(ValueError):
                    self.checked(report)
        for code in (1, 2, None):
            with self.assertRaises(ValueError):
                self.checked(self.report(), returncode=code)

    def conditional_config(self):
        return main.normalized_contract_config({"schema_version": 1, "functions": [{
            "function": "device::initialize", "trusted": True, "no_panic": True,
            "reason": "Explicit test hypothesis", "instance": "[]"}]})

    def conditional_report(self):
        report = self.report(status="proved_with_assumptions")
        config = self.conditional_config()
        report["contract_config"] = config
        proof = report["functions"][0]["proof"]
        proof["obligations"] = []
        proof["matched_contracts"] = ["device::initialize []"]
        proof["trusted_calls"] = [{"contract": config["functions"][0], "instance": "[]"}]
        return report, config

    def test_explicit_conditional_policy_and_mutations(self):
        report, config = self.conditional_report()
        with self.assertRaises(ValueError):
            self.checked(report)
        checked = main.checked_proof(self.unit, self.inventory, report, self.directory,
                                     "async_body", survey.LIMITS, 0, config, True)
        self.assertTrue(main.conditional_proof(checked))
        mutations = [lambda r: r.update(contract_config=None),
                     lambda r: r["contract_config"]["functions"][0].update(reason="Changed"),
                     lambda r: r["contract_config"].update(schema_version=True),
                     lambda r: r["contract_config"]["functions"][0].update(trusted=1),
                     lambda r: r["functions"][0]["proof"].update(entry_assumptions=["startup"]),
                     lambda r: r["functions"][0]["proof"].update(invariants=["induction"]),
                     lambda r: r["functions"][0]["proof"].update(assumptions=["unrecorded"]),
                     lambda r: r["functions"][0]["proof"].update(matched_contracts=["other::call"]),
                     lambda r: r["functions"][0]["proof"]["trusted_calls"][0].update(
                         instance="[u8]"),
                     lambda r: r["functions"][0]["proof"].update(trusted_calls=[])]
        for index, mutation in enumerate(mutations):
            changed = copy.deepcopy(report)
            mutation(changed)
            with self.subTest(index=index), self.assertRaises(ValueError):
                main.checked_proof(self.unit, self.inventory, changed, self.directory,
                                   "async_body", survey.LIMITS, 0, config, True)

    def test_configured_root_preconditions_are_conditional_even_with_proved_status(self):
        report = self.report()
        config = main.normalized_contract_config({"schema_version": 1, "functions": [{
            "function": "sample::" + main.FACTORY, "requires": ["arg0 == 7"]}]})
        report["contract_config"] = config
        proof = report["functions"][0]["proof"]
        proof.update(assumptions=["arg0 == 7"], matched_contracts=["sample::" + main.FACTORY])
        checked = main.checked_proof(self.unit, self.inventory, report, self.directory,
                                     "async_body", survey.LIMITS, 0, config, True)
        self.assertTrue(main.conditional_proof(checked))
        proof["assumptions"] = ["arg0 == 8"]
        with self.assertRaises(ValueError):
            main.checked_proof(self.unit, self.inventory, report, self.directory,
                               "async_body", survey.LIMITS, 0, config, True)

    def test_environment_drops_ambient_policies_and_rejects_captured_policies(self):
        with patch.dict(os.environ, {"MIREN_STARTUP": "1", "CARGO_FAKE": "x", "OUT_DIR": "x"}):
            environment = main.captured_environment(
                {"environment": {"MIREN_Z3": "solver"}}, self.inventory)
        self.assertNotIn("MIREN_STARTUP", environment)
        self.assertNotIn("CARGO_FAKE", environment)
        self.assertNotIn("OUT_DIR", environment)
        for environment in ({"MIREN_STARTUP": "1"}, {"RUSTFLAGS": "-Copt-level=3"}):
            with self.assertRaises(ValueError):
                main.captured_environment({"environment": environment}, self.inventory)
        changed = {**self.inventory, "compiler_environment": {"MIREN_TRUST": "1"}}
        with self.assertRaises(ValueError):
            main.captured_environment({"environment": {}}, changed)

    def prepare(self, missing=False):
        record = copy.deepcopy(self.inventory)
        if missing:
            record["functions"].pop()
        inventory_path = self.directory / "inventory.jsonl"
        inventory_path.write_text(json.dumps(record) + "\n")
        executable = self.directory / "fake-analyzer"
        executable.write_text("#!" + sys.executable + "\n" + FAKE_ANALYZER)
        executable.chmod(0o755)
        captured = {"status": "complete", "units": [self.unit], "roots": [
            {"id": self.unit["id"] + "::" + f["name"], "name": f["name"]}
            for f in record["functions"]], "provenance": {
            "limits": survey.LIMITS, "environment": {},
            "source_files_after": survey.source_hashes(self.directory, self.directory / "unused")},
            "workspaces": [{"id": ".", "inventory": {"cwd": str(self.directory),
                "command": ["tool", "--jsonl", str(inventory_path)]}}]}
        self.unit["artifact_hashes_at_completion"] = survey.artifact_hashes(
            survey.artifact_inputs(record, self.directory))
        survey_path = self.directory / "summary.json"
        survey_path.write_text(json.dumps(captured))
        # The input summary lives in the fake fleet, unlike real captures kept outside it.
        def hashes(fleet, output):
            return {"main.rs": survey.digest(self.source)}
        captured["provenance"]["source_files_after"] = hashes(None, None)
        survey_path.write_text(json.dumps(captured))
        return survey_path, executable, hashes

    def test_complete_scan_and_missing_failed_mutated_reports(self):
        path, executable, hashes = self.prepare()
        for mode in ("normal", "missing", "malformed", "crash", "wrong_scope", "source_mutation"):
            with self.subTest(mode=mode):
                self.source.write_text("fn main() {}\n")
                args = argparse.Namespace(survey=path, analyzer=executable,
                                          output=self.directory / ("output-" + mode), unit=None,
                                          unit_timeout=10,
                                          **{key: None for key in survey.LIMITS})
                with patch.object(main.exporter, "validate"), \
                        patch.object(main.survey, "source_hashes", side_effect=hashes), \
                        patch.dict(os.environ, {"FAKE_MAIN_MODE": mode,
                                                "FAKE_MAIN_INVENTORY": str(self.directory /
                                                                           "inventory.jsonl")}):
                    code = main.run(args)
                result = json.loads((args.output / "summary.json").read_text())
                self.assertEqual(code, 0 if mode == "normal" else 1)
                self.assertEqual(result["coverage_scope"], "all_embassy_binary_mains")
                self.assertEqual(len(result["units"][0]["roots"]), 3)
                self.assertEqual(result["counts"]["async_body"]["proved"],
                                 1 if mode == "normal" else 0)

    def test_milestone_requires_every_supported_body_and_complete_scope(self):
        value = {"status": "complete", "coverage_scope": "all_embassy_binary_mains",
                 "expected_units": ["first", "second"], "units": [
                     {"id": "first", "roots": [{"scope": "async_body", "status": "complete",
                                                "proof_status": "proved"}]},
                     {"id": "second", "roots": [{"scope": "async_body", "status": "complete",
                                                 "proof_status": "refuted"}]}]}
        self.assertTrue(main.milestone_reached(value))
        for mutation in (lambda v: v.update(status="partial"),
                         lambda v: v.update(coverage_scope="selected_embassy_binary_mains"),
                         lambda v: v["units"].pop(),
                         lambda v: v["units"][0]["roots"][0].update(proof_status="unknown"),
                         lambda v: v["units"][0]["roots"][0].update(scope="runtime_entry")):
            changed = copy.deepcopy(value)
            mutation(changed)
            self.assertFalse(main.milestone_reached(changed))

    def test_inventory_cannot_silently_drop_a_main(self):
        path, _, _ = self.prepare()
        summary = json.loads(path.read_text())
        inventory_path = self.directory / "inventory.jsonl"
        record = json.loads(inventory_path.read_text())
        record["functions"].pop(0)
        inventory_path.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, "root set mismatch"):
            main.inventories(summary, self.directory)

    def test_artifact_changes_before_after_and_at_completion_invalidate(self):
        path, executable, hashes = self.prepare()
        for checkpoint in (1, 3, 9):
            calls = 0

            def artifacts(inputs):
                nonlocal calls
                calls += 1
                return {"changed": "hash"} if calls >= checkpoint else {}

            args = argparse.Namespace(survey=path, analyzer=executable,
                                      output=self.directory / ("artifact-" + str(checkpoint)),
                                      unit=None, unit_timeout=10,
                                      **{key: None for key in survey.LIMITS})
            with patch.object(main.exporter, "validate"), \
                    patch.object(main.survey, "source_hashes", side_effect=hashes), \
                    patch.object(main.survey, "artifact_hashes", side_effect=artifacts), \
                    patch.dict(os.environ, {"FAKE_MAIN_INVENTORY": str(self.directory /
                                                                       "inventory.jsonl")}):
                self.assertEqual(main.run(args), 1)
            result = json.loads((args.output / "summary.json").read_text())
            self.assertFalse(result["milestone_reached"])
            self.assertTrue(all(r["proof_status"] == "unknown"
                                for r in result["units"][0]["roots"]))

    def test_assumptions_profiles_snapshot_and_keep_wrapper_scopes_strict(self):
        path, executable, hashes = self.prepare()
        policy = self.directory / "profile.json"
        profile = {"schema_version": 1, "units": {self.unit["id"]: self.conditional_config()}}
        for mode in ("normal", "config_mutation", "profile_file_mutation",
                     "contract_snapshot_mutation", "unknown_conditional"):
            policy.write_text(json.dumps(profile))
            args = argparse.Namespace(survey=path, analyzer=executable,
                                      output=self.directory / ("conditional-" + mode), unit=None,
                                      unit_timeout=10, assumptions_profile=policy,
                                      allow_assumptions=True, contracts=None,
                                      **{key: None for key in survey.LIMITS})
            with patch.object(main.exporter, "validate"), \
                    patch.object(main.survey, "source_hashes", side_effect=hashes), \
                    patch.dict(os.environ, {"FAKE_MAIN_INVENTORY": str(self.directory /
                                                                       "inventory.jsonl"),
                                            "FAKE_MAIN_POLICY": str(policy),
                                            "FAKE_MAIN_MODE": mode}):
                code = main.run(args)
            result = json.loads((args.output / "summary.json").read_text())
            self.assertEqual(code, 0 if mode in ("normal", "unknown_conditional") else 1)
            self.assertFalse(result["milestone_reached"])
            self.assertEqual(result["conditional_milestone_reached"], mode == "normal")
            if mode in ("normal", "unknown_conditional"):
                roots = result["units"][0]["roots"]
                self.assertTrue(roots[0]["conditional"])
                self.assertFalse(roots[1]["conditional"])
                self.assertFalse(roots[2]["conditional"])
            self.assertEqual(Path(result["contracts"]["snapshot"]).read_bytes(),
                             json.dumps(profile).encode())

    def test_profiles_require_explicit_pair_and_exact_known_units(self):
        path, executable, hashes = self.prepare()
        policy = self.directory / "profile.json"
        policy.write_text(json.dumps({"schema_version": 1, "units": {
            "not/a/fleet/unit": self.conditional_config()}}))
        args = argparse.Namespace(survey=path, analyzer=executable,
                                  output=self.directory / "bad-profile", unit=None,
                                  unit_timeout=10, assumptions_profile=policy,
                                  allow_assumptions=True, contracts=None,
                                  **{key: None for key in survey.LIMITS})
        with patch.object(main.exporter, "validate"), self.assertRaisesRegex(ValueError,
                                                                           "unknown unit"):
            main.run(args)
        for contracts, profile_path, flag in [(policy, None, False), (None, None, True),
                                             (policy, policy, True)]:
            args.contracts, args.assumptions_profile = contracts, profile_path
            args.allow_assumptions = flag
            with self.assertRaises(ValueError):
                main.run(args)

    def test_missing_wrapper_is_counted_unknown(self):
        path, executable, hashes = self.prepare(missing=True)
        args = argparse.Namespace(survey=path, analyzer=executable,
                                  output=self.directory / "output", unit=None, unit_timeout=10,
                                  **{key: None for key in survey.LIMITS})
        with patch.object(main.exporter, "validate"), \
                patch.object(main.survey, "source_hashes", side_effect=hashes), \
                patch.dict(os.environ, {"FAKE_MAIN_INVENTORY": str(self.directory /
                                                                   "inventory.jsonl")}):
            self.assertEqual(main.run(args), 1)
        result = json.loads((args.output / "summary.json").read_text())
        self.assertEqual(result["counts"]["runtime_entry"]["unknown"], 1)
        self.assertIn("missing", result["units"][0]["roots"][2]["failure"])


FAKE_ANALYZER = r'''
import json
import os
from pathlib import Path
import sys
args = sys.argv[1:]
mode = os.environ.get("FAKE_MAIN_MODE", "normal")
if mode in ("missing", "crash"):
    sys.exit(1 if mode == "missing" else 2)
path = Path(args[args.index("--jsonl") + 1])
if mode == "malformed":
    path.write_text("{bad\n")
    sys.exit(0)
report = json.loads(Path(os.environ["FAKE_MAIN_INVENTORY"]).read_text())
async_entry = "--async-entry" in args
name = args[args.index("--async-entry" if async_entry else "--entry") + 1]
status = "proved" if async_entry else "refuted"
for function in report["functions"]:
    if function["name"] == name:
        function["proof"] = {"status": status, "async_entry": async_entry,
                             "obligations": [] if status == "proved" else [{"status": status}]}
        if mode == "wrong_scope":
            function["proof"]["async_entry"] = not async_entry
report["analysis_limits"] = {key: int(args[args.index("--" + key.replace("_", "-")) + 1])
                             for key in ["max_steps", "max_call_depth", "max_query_bytes",
                                         "root_timeout_secs", "solver_timeout_ms"]}
if "--contracts" in args:
    assert "--allow-assumptions" in args
    config_path = Path(args[args.index("--contracts") + 1])
    config = json.loads(config_path.read_text())
    report["contract_config"] = config
    function = next(f for f in report["functions"] if f["name"] == name)
    status = "unknown" if mode == "unknown_conditional" else "proved_with_assumptions"
    function["proof"].update(status=status,
        obligations=[{"status": "unknown"}] if status == "unknown" else [],
        matched_contracts=[s["function"] + (" " + s["instance"] if s["instance"] else "")
                           for s in config["functions"]],
        trusted_calls=[{"contract": s, "instance": s["instance"] or "[]"}
                       for s in config["functions"] if s["trusted"]])
    if mode == "config_mutation":
        report["contract_config"]["functions"][0]["reason"] = "Changed"
    if mode == "profile_file_mutation":
        Path(os.environ["FAKE_MAIN_POLICY"]).write_text("{}")
    if mode == "contract_snapshot_mutation":
        config_path.write_text("{}")
if mode == "source_mutation":
    Path(report["functions"][0]["source"]["file"]).write_text("fn changed() {}\n")
path.write_text(json.dumps(report) + "\n")
sys.exit(0 if status in ("proved", "proved_with_assumptions") else 1)
'''


if __name__ == "__main__":
    unittest.main()
