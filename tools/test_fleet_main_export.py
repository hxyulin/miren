"""Main publication rejects incomplete, inconsistent or falsely unconditional evidence."""

import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import fleet_main_export as exporter
import fleet_main_survey as main
import fleet_survey as survey


def sample(conditional=False):
    units = []
    for index in range(exporter.EXPECTED_MAIN_COUNT):
        roots = []
        for scope, values in main.SCOPES.items():
            status = "unknown" if scope == "async_body" else "proved"
            proof = {"status": status, "async_entry": values[1], "assumptions": [],
                     "entry_assumptions": [], "trusted_calls": [], "invariants": [],
                     "obligations": [] if status == "proved" else [{"status": status}]}
            roots.append({"scope": scope, "name": values[0], "status": "complete",
                          "proof_status": status, "proof": proof, "conditional": False,
                          "failure": None})
        artifacts = {"/private/dependency.rmeta": "a" * 64, "directory:/missing": False}
        units.append({"id": f"unit-{index}", "status": "complete", "roots": roots,
                      "contract_config": None, "contract_snapshot": None,
                      "contract_sha256": None,
                      **{key: copy.deepcopy(artifacts) for key in exporter.ARTIFACT_CHECKPOINTS}})
    result = {"schema_version": 1, "status": "complete", "errors": [], "missing_units": [],
              "expected_units": [unit["id"] for unit in units],
              "selected_units": [unit["id"] for unit in units], "units": units,
              "coverage_scope": "all_embassy_binary_mains", "allow_assumptions": conditional,
              "contracts_scope": "async_body_only", "contract_config": None,
              "contract_profiles": {}, "limits": survey.LIMITS,
              "source_files_before": {"main.rs": "b" * 64},
              "source_files_after": {"main.rs": "b" * 64},
              "analyzer_source": {"commit": "revision", "dirty": False},
              "analyzer_binaries": {"miren": {"original_sha256": "c" * 64,
                                              "frozen_sha256": "c" * 64}},
              "survey": "/private/survey.json", "survey_sha256": "d" * 64,
              "scopes": {key: {"entry": value[0], "async_entry": value[1], "scope": value[2]}
                         for key, value in main.SCOPES.items()},
              "milestone_reached": False, "conditional_milestone_reached": False,
              "counts": {scope: {status: exporter.EXPECTED_MAIN_COUNT
                                  if status == ("unknown" if scope == "async_body" else "proved")
                                  else 0 for status in sorted(survey.STATUSES)}
                         for scope in main.SCOPES}}
    if conditional:
        result["contracts"] = {"sha256": "e" * 64, "source_sha256_at_completion": "e" * 64,
                               "snapshot_sha256_at_completion": "e" * 64}
    return result


class MainExportTests(unittest.TestCase):
    def test_entry_milestone_requires_valid_poll_records_and_exports_selected_evidence(self):
        summary = sample()
        name = main.FACTORY + "::{closure#0}"
        entry = {"function": name, "instance": name + " []", "coroutine_poll": True,
                 "source": {"file": "main.rs", "line": 1, "column": 1},
                 "call_chain": [main.FACTORY, name]}
        for unit in summary["units"]:
            unit["roots"][0]["proof"]["body_entries"] = [copy.deepcopy(entry)]
        main.annotate_evidence(summary)
        summary["fresh_future_entry_milestone_reached"] = True
        exporter.validate(summary)
        root = summary["units"][0]["roots"][0]
        compact = exporter.compact_root(root, entry["source"], "a" * 64)
        self.assertTrue(compact["application_body_reached"])
        self.assertEqual(compact["application_body_entries"], [entry])
        self.assertEqual(compact["body_entry_count"], 1)
        self.assertFalse(compact["body_entries_truncated"])
        for mutation in [lambda s: s["units"][0]["roots"][0]["proof"].pop("body_entries"),
                         lambda s: s["units"][0]["roots"][0]["proof"]["body_entries"][0].update(
                             coroutine_poll=False),
                         lambda s: s["units"][0]["roots"][0]["proof"]["body_entries"][0].update(
                             call_chain=["wrong_root"]),
                         lambda s: s["units"][0]["roots"][0]["proof"].update(
                             body_entries_truncated=1),
                         lambda s: s["units"][0]["roots"][0]["proof"].update(
                             body_entries_truncated=True),
                         lambda s: s["units"][0]["roots"][0]["proof"]["body_entries"][0].update(
                             source={}),
                         lambda s: s["units"][0]["roots"][0].update(
                             application_body_reached=False)]:
            changed = copy.deepcopy(summary)
            mutation(changed)
            with self.assertRaises(ValueError):
                exporter.validate(changed)
        old = sample()
        self.assertFalse(exporter.compact_root(old["units"][0]["roots"][0],
                                               entry["source"], "a" * 64)[
                                                   "application_body_reached"])
        old["fresh_future_entry_milestone_reached"] = True
        with self.assertRaises(ValueError):
            exporter.validate(old)

    def test_complete_collection_can_publish_unknown_without_claiming_milestone(self):
        for conditional in (False, True):
            summary = sample(conditional)
            self.assertEqual(exporter.validate(summary, conditional), summary["counts"])
            self.assertFalse(summary["milestone_reached"])
            self.assertFalse(summary["conditional_milestone_reached"])

    def test_domain_labels_cannot_claim_boot_confirmation(self):
        summary = sample()
        main.annotate_evidence(summary)
        exporter.validate(summary)
        for key, value in (("analysis_domain", "boot execution"),
                           ("boot_reachability", "verified"),
                           ("counterexample_evidence", [{"native_confirmation": "confirmed"}])):
            changed = copy.deepcopy(summary)
            changed["units"][0]["roots"][0][key] = value
            with self.assertRaises(ValueError):
                exporter.validate(changed)

    def test_mutations_cannot_launder_missing_or_unsupported_evidence(self):
        mutations = [lambda s: s.update(schema_version=True),
                     lambda s: s.update(status="partial"),
                     lambda s: s.update(errors=["compiler failure"]),
                     lambda s: s.update(coverage_scope="selected_embassy_binary_mains"),
                     lambda s: s["expected_units"].pop(),
                     lambda s: s["selected_units"].pop(),
                     lambda s: s["units"].pop(),
                     lambda s: s["units"].append(s["units"][0]),
                     lambda s: s["units"][0]["roots"].pop(),
                     lambda s: s["units"][0]["roots"][0].update(name="other"),
                     lambda s: s["units"][0]["roots"][0].update(status="failed"),
                     lambda s: s["units"][0]["roots"][0].update(failure="missing body"),
                     lambda s: s["units"][0]["roots"][0].update(proof_status="success"),
                     lambda s: s["units"][0]["roots"][0]["proof"].update(status="proved"),
                     lambda s: s["units"][0]["roots"][0]["proof"].update(async_entry=False),
                     lambda s: s["units"][0]["roots"][0]["proof"].update(obligations=[]),
                     lambda s: s["units"][0].update(artifact_hashes_after={}),
                     lambda s: s["units"][0].pop("artifact_hashes_at_completion"),
                     lambda s: s.update(source_files_after={}),
                     lambda s: s["analyzer_binaries"]["miren"].update(frozen_sha256="f" * 64),
                     lambda s: s["counts"]["async_body"].update(unknown=True),
                     lambda s: s.update(milestone_reached=True),
                     lambda s: s.update(conditional_milestone_reached=True)]
        for index, mutation in enumerate(mutations):
            changed = sample()
            mutation(changed)
            with self.subTest(index=index), self.assertRaises(ValueError):
                exporter.validate(changed)

    def test_conditional_labels_and_policy_checkpoints_are_mandatory(self):
        summary = sample(True)
        root = summary["units"][0]["roots"][0]
        root["proof"]["assumptions"] = ["arg0 == 7"]
        with self.assertRaises(ValueError):
            exporter.validate(summary, True)
        root["conditional"] = True
        exporter.validate(summary, True)
        root["scope"] = "runtime_entry"
        with self.assertRaises(ValueError):
            exporter.validate(summary, True)
        for mutate in [lambda s: s.pop("contracts"),
                       lambda s: s["contracts"].update(snapshot_sha256_at_completion="f" * 64),
                       lambda s: s["units"][0].update(contract_config={"schema_version": 1,
                           "functions": []}, contract_sha256="a" * 64)]:
            changed = sample(True)
            mutate(changed)
            with self.assertRaises(ValueError):
                exporter.validate(changed, True)
        with self.assertRaises(ValueError):
            exporter.validate(sample(True))

    def test_compact_root_preserves_blocker_policy_and_drops_raw_solver_data(self):
        root = sample()["units"][0]["roots"][0]
        root["proof"].update(trusted_calls=[{"reason": "explicit hypothesis"}],
            obligations=[{"status": "unknown", "detail": "missing MIR", "kind": "unsupported",
                          "call_chain": ["main", "helper"], "model": {"value": 7},
                          "query": "raw SMT", "source": {"line": 3}}])
        compact = exporter.compact_root(root, {"file": "main.rs", "line": 1}, "e" * 64)
        self.assertEqual(compact["blockers"][0]["detail"], "missing MIR")
        self.assertEqual(compact["blockers"][0]["call_chain"], ["main", "helper"])
        self.assertEqual(compact["trusted_calls"], root["proof"]["trusted_calls"])
        self.assertNotIn("raw SMT", json.dumps(compact))
        self.assertNotIn("model", compact["blockers"][0])
        self.assertEqual(len(compact["blockers"][0]["counterexample_sha256"]), 64)

    def compact(self):
        return {"survey_sha256": "a" * 64, "analyzer_binaries": {"miren": "b" * 64},
                "analyzer_source": {"commit": "revision"}, "limits": survey.LIMITS,
                "source_files_sha256": "c" * 64, "artifact_inputs_sha256": "d" * 64,
                "source_files": {"main.rs": "e" * 64}, "units": []}

    def test_export_pairs_exact_capture_identity_and_is_deterministic(self):
        strict, conditional = self.compact(), self.compact()
        with patch.object(exporter, "capture", side_effect=[strict, conditional]):
            first = exporter.export(Path("strict"), Path("conditional"))
        with patch.object(exporter, "capture", side_effect=[self.compact(), self.compact()]):
            second = exporter.export(Path("strict"), Path("conditional"))
        self.assertEqual(exporter.encoded(first), exporter.encoded(second))
        self.assertLess(len(exporter.encoded(first)), exporter.MAX_OUTPUT_BYTES)
        for key in ("survey_sha256", "analyzer_binaries", "limits", "source_files_sha256",
                    "artifact_inputs_sha256", "analyzer_source"):
            changed = self.compact()
            changed[key] = {"commit": "other"} if key == "analyzer_source" else "different"
            with self.subTest(key=key), patch.object(exporter, "capture", side_effect=[
                    self.compact(), changed]), self.assertRaises(ValueError):
                exporter.export(Path("strict"), Path("conditional"))

    def test_capture_rechecks_raw_report_configuration_and_proof_identity(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            summary = sample()
            analyzer = directory / "analyzer"
            analyzer.mkdir()
            (analyzer / "miren").write_bytes(b"frozen analyzer")
            digest = survey.digest(analyzer / "miren")
            summary["analyzer_binaries"]["miren"] = {
                "original_sha256": digest, "frozen_sha256": digest}
            base = {"provenance": {key: "captured" for key in exporter.base_export.PROVENANCE}}
            base["provenance"]["source_files_after"] = summary["source_files_before"]
            base_path = directory / "base.json"
            base_path.write_text(json.dumps(base))
            summary.update(survey=str(base_path), survey_sha256=survey.digest(base_path),
                           excluded_binaries=[])
            inventories = []
            for index, unit in enumerate(summary["units"]):
                source = str(directory / "main.rs")
                inventory = {"schema_version": 9, "compiler": "compiler", "target": "arm",
                    "panic_strategy": "abort", "overflow_checks": True, "mir_phase": "runtime",
                    "crate_name": f"unit_{index}", "working_directory": str(directory),
                    "compiler_environment": {}, "rustc_arguments": ["--crate-name", f"unit_{index}",
                        "--crate-type", "bin", source], "functions": [
                        {"name": values[0], "source": {"file": source, "line": 1, "column": 1}}
                        for values in main.SCOPES.values()]}
                original = {"id": unit["id"], "crate_name": f"unit_{index}", "source": source,
                    "kinds": ["bin"],
                    "artifact_hashes_at_completion": unit["artifact_hashes_before"]}
                inventories.append((original, inventory, directory))
                for root in unit["roots"]:
                    report = copy.deepcopy(inventory)
                    report["analysis_limits"] = summary["limits"]
                    function = next(f for f in report["functions"] if f["name"] == root["name"])
                    function["proof"] = root["proof"]
                    path = directory / (f"{index}-" + root["scope"] + ".jsonl")
                    path.write_text(json.dumps(report) + "\n")
                    root.update(report=str(path), verification={
                        "status": "complete" if root["proof_status"] == "proved" else "failed",
                        "returncode": 0 if root["proof_status"] == "proved" else 1})
            path = directory / "summary.json"
            path.write_text(json.dumps(summary))
            with patch.object(exporter.base_export, "validate"), patch.object(main, "inventories",
                    return_value=(inventories, [])):
                compact = exporter.capture(path)
                self.assertEqual(len(compact["units"]), exporter.EXPECTED_MAIN_COUNT)
                self.assertTrue(compact["artifact_inputs_unchanged"])
                report_path = Path(summary["units"][0]["roots"][0]["report"])
                original_report = report_path.read_text()
                report = json.loads(original_report)
                report["target"] = "wrong-target"
                report_path.write_text(json.dumps(report) + "\n")
                with self.assertRaises(ValueError):
                    exporter.capture(path)
                report_path.write_text(original_report)
                report = json.loads(original_report)
                proof = next(f["proof"] for f in report["functions"] if f.get("proof"))
                proof["obligations"][0]["detail"] = "changed diagnostic"
                report_path.write_text(json.dumps(report) + "\n")
                with self.assertRaises(ValueError):
                    exporter.capture(path)

    def test_cli_failure_keeps_previous_publication(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "current.json"
            output.write_text("previous evidence\n")
            summary = Path(temporary) / "summary.json"
            summary.write_text(json.dumps(sample()))
            with patch.object(exporter.sys, "argv", ["fleet_main_export.py", "--strict",
                    str(summary), "--output", str(output)]):
                self.assertEqual(exporter.main(), 1)
            self.assertEqual(output.read_text(), "previous evidence\n")
