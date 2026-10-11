import copy
import json
from pathlib import Path
import tempfile
import unittest

from rust_capability_survey import check_configuration, check_report, load_manifest


class CapabilityReports(unittest.TestCase):
    def setUp(self):
        self.cases = [{"entry": "positive", "family": "integer", "expected": "proved"},
                      {"entry": "mutation", "family": "integer", "expected": "refuted"},
                      {"entry": "frontier", "family": "memory", "expected": "unknown",
                       "unknown_reason": "frontier"}]
        self.report = {"functions": [
            {"name": case["entry"], "proof": {
                "status": case["expected"], "assumptions": [], "entry_assumptions": [],
                "trusted_calls": [], "inputs": {}, "models": [], "analyzed_bodies": [],
                "obligations": [{"status": case["expected"],
                    "kind": "panic_safety", "function": case["entry"],
                    "source": {"file": "fixture.rs", "line": 1, "column": 1},
                    "query": "query", "model": "model" if case["expected"] == "refuted"
                    else None, "detail": "frontier", "unknown_category": "semantics"}]}}
            for case in self.cases]}

    def test_exact_baseline_and_optional_gap_metadata(self):
        results, errors = check_report(self.report, self.cases, 1)
        self.assertEqual(errors, [])
        self.assertEqual(results[2]["gaps"][0]["category"], "semantics")
        del self.report["functions"][2]["proof"]["obligations"][0]["unknown_category"]
        self.assertEqual(check_report(self.report, self.cases, 1)[0][2]["gaps"][0]["category"],
                         "unclassified")

    def test_mutated_outcomes_and_missing_proof_fail(self):
        for index in range(3):
            report = copy.deepcopy(self.report)
            report["functions"][index]["proof"]["status"] = "proved_with_assumptions"
            self.assertTrue(check_report(report, self.cases, 1)[1])
        self.report["functions"][0]["proof"] = None
        self.assertTrue(check_report(self.report, self.cases, 1)[1])

    def test_assumptions_missing_witness_and_unknown_evidence_fail(self):
        for field in ["assumptions", "entry_assumptions", "trusted_calls"]:
            report = copy.deepcopy(self.report)
            report["functions"][0]["proof"][field] = ["premise"]
            self.assertTrue(check_report(report, self.cases, 1)[1])
        for index in [1, 2]:
            report = copy.deepcopy(self.report)
            report["functions"][index]["proof"]["obligations"] = []
            self.assertTrue(check_report(report, self.cases, 1)[1])

    def test_duplicate_and_unselected_inventory_roots(self):
        self.report["functions"].append({"name": "inventory", "proof": None})
        self.assertEqual(check_report(self.report, self.cases, 1)[1], [])
        self.report["functions"].append(copy.deepcopy(self.report["functions"][0]))
        self.assertTrue(check_report(self.report, self.cases, 1)[1])

    def test_unrelated_unknown_does_not_satisfy_frontier(self):
        self.report["functions"][2]["proof"]["obligations"][0]["detail"] = "missing body"
        self.assertTrue(check_report(self.report, self.cases, 1)[1])

    def test_declared_unknown_category_requires_the_matching_producer_cause(self):
        case = self.cases[2]
        obligation = self.report["functions"][2]["proof"]["obligations"][0]
        for category in ["semantics", "missing_compiler_evidence"]:
            case["unknown_category"] = category
            obligation["unknown_category"] = category
            self.assertEqual(check_report(self.report, self.cases, 1)[1], [])
            for wrong in ["unclassified", "solver", None]:
                obligation["unknown_category"] = wrong
                self.assertTrue(check_report(self.report, self.cases, 1)[1])
            del obligation["unknown_category"]
            self.assertTrue(check_report(self.report, self.cases, 1)[1])

    def test_witness_requires_nonempty_query_and_model_strings(self):
        for field in ["query", "model"]:
            for value in [True, 7, {}, "", None]:
                report = copy.deepcopy(self.report)
                report["functions"][1]["proof"]["obligations"][0][field] = value
                self.assertTrue(check_report(report, self.cases, 1)[1])

    def test_contradictory_reducer_and_actual_numeric_exit_fail(self):
        for index in [1, 2]:
            report = copy.deepcopy(self.report)
            report["functions"][index]["proof"]["status"] = "proved"
            self.assertTrue(check_report(report, self.cases, 1)[1])
        for numeric in [True, False, 0, 2, None, "1"]:
            self.assertTrue(check_report(self.report, self.cases, numeric)[1])
        cases = self.cases[:1]
        report = {"functions": self.report["functions"][:1]}
        self.assertEqual(check_report(report, cases, 0)[1], [])
        self.assertTrue(check_report(report, cases, 1)[1])
        report["functions"][0]["proof"]["obligations"] = []
        self.assertEqual(check_report(report, cases, 0)[1], [])

    def test_unknown_prefix_and_mixed_refutation_keep_original_evidence(self):
        original = copy.deepcopy(self.report)
        positive = copy.deepcopy(self.report["functions"][0]["proof"]["obligations"][0])
        self.report["functions"][2]["proof"]["obligations"].insert(0, positive)
        unknown = copy.deepcopy(self.report["functions"][2]["proof"]["obligations"][1])
        unknown["model"] = "partial model"
        self.report["functions"][1]["proof"]["obligations"].insert(0, unknown)
        before = copy.deepcopy(self.report)
        self.assertEqual(check_report(self.report, self.cases, 1)[1], [])
        self.assertEqual(self.report, before)
        self.assertEqual(original["functions"][2]["proof"]["status"], "unknown")

    def test_required_dto_fields_and_selected_set_fail_closed(self):
        for field in ["inputs", "models", "analyzed_bodies"]:
            report = copy.deepcopy(self.report)
            del report["functions"][0]["proof"][field]
            self.assertTrue(check_report(report, self.cases, 1)[1])
        for source in [None, {}, {"file": "fixture.rs", "line": True, "column": 1}]:
            report = copy.deepcopy(self.report)
            report["functions"][0]["proof"]["obligations"][0]["source"] = source
            self.assertTrue(check_report(report, self.cases, 1)[1])
        self.assertTrue(check_report(self.report, [], 1)[1])
        self.assertTrue(check_report(self.report, self.cases + [self.cases[0]], 1)[1])
        report = copy.deepcopy(self.report)
        extra = copy.deepcopy(report["functions"][0])
        extra["name"] = "extra"
        report["functions"].append(extra)
        self.assertTrue(check_report(report, self.cases, 1)[1])
        extra["proof"]["status"] = "proved_with_assumptions"
        self.assertTrue(check_report(report, self.cases, 1)[1])
        report = copy.deepcopy(self.report)
        report["functions"][2]["proof"]["obligations"][0]["unknown_category"] = "rust_semantics"
        self.assertTrue(check_report(report, self.cases, 1)[1])

    def test_compiler_target_and_optimization_match_request(self):
        report = {"crate_name": "rust_capabilities", "overflow_checks": True,
                  "panic_strategy": "abort", "target": "host", "compiler": "rustc pinned",
                  "rustc_arguments": ["fixture.rs", "-Copt-level=2", "--sysroot", "pinned"]}
        check_configuration(report, ["fixture.rs", "-Copt-level=2"], "host", "rustc pinned")
        for field, value in [("target", "other"), ("compiler", "other"),
                             ("overflow_checks", False), ("rustc_arguments", ["fixture.rs"])]:
            changed = dict(report, **{field: value})
            with self.assertRaises(ValueError):
                check_configuration(changed, ["fixture.rs", "-Copt-level=2"],
                                    "host", "rustc pinned")

    def test_malformed_reports_and_missing_premises_fail(self):
        for report in [[], {"functions": [None]}, {"functions": None}]:
            self.assertTrue(check_report(report, self.cases, 1)[1])
        for field in ["assumptions", "entry_assumptions", "trusted_calls", "obligations"]:
            for value in [None, {}, ""]:
                report = copy.deepcopy(self.report)
                report["functions"][0]["proof"][field] = value
                self.assertTrue(check_report(report, self.cases, 1)[1])
            report = copy.deepcopy(self.report)
            del report["functions"][0]["proof"][field]
            if field == "entry_assumptions":
                self.assertEqual(check_report(report, self.cases, 1)[1], [])
            else:
                self.assertTrue(check_report(report, self.cases, 1)[1])
        self.report["functions"][0]["proof"]["obligations"] = [None]
        self.assertTrue(check_report(self.report, self.cases, 1)[1])

    def test_manifest_refuses_duplicate_unknown_and_escaping_fixture(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "fixture.rs").write_text("pub fn positive() {}")
            path = root / "manifest.json"
            manifest = {"schema_version": 1, "fixture": "fixture.rs", "cases": self.cases}
            path.write_text(json.dumps(manifest))
            self.assertEqual(load_manifest(path, root)[0], manifest)
            manifest["schema_version"] = True
            path.write_text(json.dumps(manifest))
            with self.assertRaises(ValueError):
                load_manifest(path, root)
            manifest["schema_version"] = 1
            for cases in [self.cases + [self.cases[0]],
                          [{"entry": "x", "family": "x", "expected": "unknown"}],
                          [{"entry": "x", "family": "x", "expected": "unknown",
                            "unknown_reason": []}],
                          [{"entry": "x", "family": "x", "expected": "proved",
                            "unrecognized": True}],
                          [{"entry": "x", "family": "x", "expected": "unknown",
                            "unknown_reason": "x", "unknown_category": []}],
                          [{"entry": "x", "family": "x", "expected": "unknown",
                            "unknown_reason": "x", "unknown_category": "invented"}],
                          [{"entry": "x", "family": "x", "expected": "proved",
                            "unknown_category": "semantics"}]]:
                manifest["cases"] = cases
                path.write_text(json.dumps(manifest))
                with self.assertRaises(ValueError):
                    load_manifest(path, root)
            manifest["fixture"] = "../outside.rs"
            path.write_text(json.dumps(manifest))
            with self.assertRaises(ValueError):
                load_manifest(path, root)


if __name__ == "__main__":
    unittest.main()
