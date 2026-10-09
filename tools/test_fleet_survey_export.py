"""Publication tests use the checked-in 2,336-root fleet measurement as identity evidence."""

from copy import deepcopy
import json
from pathlib import Path
import unittest

import fleet_survey_export as exporter


def inflate(compact):
    """Reconstruct a raw-format test fixture; source fingerprints here are synthetic."""
    roots = []
    for row in compact["roots"]:
        unit, name, function, status, file, line, column, blocker = row
        roots.append({"id": compact["units"][unit]["id"] + "::" + name, "name": name,
                      "classification": ("source_function_heuristic" if function
                                         else "generated_or_other"),
                      "status": status, "failure": None,
                      "source": {"file": compact["files"][file], "line": line,
                                 "column": column},
                      "first_blocker": (compact["blockers"][blocker]
                                        if blocker is not None else None)})
    provenance = deepcopy(compact["provenance"])
    provenance.update(source_files={"fixture": "0" * 64}, source_files_after={"fixture": "0" * 64},
                      build_files={})
    return {"schema_version": 1, "status": "complete", "errors": [], "provenance": provenance,
            "roots": roots, "counts": exporter.tally(roots),
            "classified_counts": {category: exporter.tally(
                [r for r in roots if r["classification"] == category])
                                  for category in exporter.CATEGORIES},
            "units": [{"id": unit["id"], "status": "complete", "error": None}
                      for unit in compact["units"]],
            "workspaces": [{"errors": [], "inventory": {"status": "complete", "returncode": 0},
                            "expected_units": len(compact["units"])}]}


def identities(compact):
    return {compact["units"][row[0]]["id"] + "::" + row[1]:
            [row[2], row[3], compact["files"][row[4]], row[5], row[6],
             compact["blockers"][row[7]] if row[7] is not None else None]
            for row in compact["roots"]}


class ExportTests(unittest.TestCase):
    def setUp(self):
        path = Path(__file__).resolve().parent.parent / "docs/public/data/fleet-survey-current.json"
        self.compact = json.loads(path.read_text())
        self.raw = inflate(self.compact)

    def test_full_fleet_roundtrip_preserves_root_identity_and_counts(self):
        exported = exporter.export(self.raw, "2026-10-08")
        self.assertEqual(len(exported["roots"]), 2336)
        self.assertEqual(len(exported["units"]), 32)
        self.assertEqual(exported["counts"], self.compact["counts"])
        self.assertEqual(exported["classified_counts"], self.compact["classified_counts"])
        self.assertEqual(identities(exported), identities(self.compact))
        self.assertIsNone(exported["artifact_inputs_unchanged"])
        self.assertIsNone(exported["artifact_inputs_sha256"])

    def test_input_order_does_not_change_serialized_output(self):
        first = exporter.export(self.raw, "2026-10-08")
        self.raw["roots"].reverse()
        self.raw["units"].reverse()
        second = exporter.export(self.raw, "2026-10-08")
        self.assertEqual(json.dumps(first, sort_keys=True), json.dumps(second, sort_keys=True))

    def test_partial_malformed_missing_and_inconsistent_data_reject(self):
        mutations = [lambda s: s.update(status="partial"),
                     lambda s: s.update(schema_version=True),
                     lambda s: s["counts"].update(proved=9999),
                     lambda s: s["roots"].append(s["roots"][0]),
                     lambda s: s["roots"][0].update(status="success"),
                     lambda s: s["roots"][0].update(failure="missing proof"),
                     lambda s: s["roots"][0].pop("failure"),
                     lambda s: s["roots"][0].pop("first_blocker"),
                     lambda s: s["roots"][0].update(id="missing::root"),
                     lambda s: s["units"][0].update(status="failed"),
                     lambda s: s["workspaces"][0].update(expected_units=1),
                     lambda s: s["workspaces"][0]["inventory"].update(returncode=1),
                     lambda s: s["workspaces"][0]["inventory"].update(returncode=False),
                     lambda s: s["workspaces"][0]["inventory"].pop("returncode"),
                     lambda s: s["provenance"].update(source_files_after={}),
                     lambda s: s["provenance"].pop("compiler")]
        for index, mutate in enumerate(mutations):
            with self.subTest(index=index):
                summary = deepcopy(self.raw)
                mutate(summary)
                with self.assertRaises(ValueError):
                    exporter.export(summary, "2026-10-08")

    def test_artifact_checkpoints_aggregate_without_publishing_paths(self):
        for unit in self.raw["units"]:
            for checkpoint in exporter.CHECKPOINTS:
                unit[checkpoint] = {"/private/dependency.rmeta": "a" * 64,
                                    "/private/absent.rmeta.miren-origins.json": None}
        exported = exporter.export(self.raw, "2026-10-08")
        self.assertTrue(exported["artifact_inputs_unchanged"])
        self.assertEqual(exported["artifact_unit_count"], 32)
        self.assertEqual(len(exported["artifact_inputs_sha256"]), 64)
        self.assertNotIn("/private/dependency.rmeta", json.dumps(exported))
        self.raw["units"][0]["artifact_hashes_at_completion"] = {}
        with self.assertRaises(ValueError):
            exporter.export(self.raw, "2026-10-08")

    def test_comparison_records_regressions_and_configuration_changes(self):
        previous = deepcopy(self.raw)
        root = next(root for root in previous["roots"] if root["status"] == "unknown")
        root["status"] = "proved"
        previous["counts"] = exporter.tally(previous["roots"])
        previous["classified_counts"][root["classification"]] = exporter.tally(
            [r for r in previous["roots"] if r["classification"] == root["classification"]])
        previous["provenance"]["target"] = "different"
        result = exporter.export(self.raw, "2026-10-08", previous)["comparison"]
        self.assertEqual(result["previously_proved_regressions"], 1)
        self.assertEqual(result["incompatible_provenance"], ["target"])
        self.assertEqual(result["added_roots"], 0)
        self.assertEqual(result["removed_roots"], 0)
        self.assertEqual(sum(t["count"] for t in result["transitions"]), 2336)

    def test_comparison_tracks_classification_and_hidden_blocker_progress(self):
        previous = deepcopy(self.raw)
        unknowns = [r for r in previous["roots"] if r["status"] == "unknown"
                    and r["classification"] == "source_function_heuristic"]
        unknowns[0]["first_blocker"] = None
        unknowns[1]["first_blocker"] = "earlier unsupported operation"
        changed = next(r for r in previous["roots"]
                       if r["classification"] == "source_function_heuristic"
                       and r["status"] == "proved")
        changed["classification"] = "generated_or_other"
        previous["classified_counts"] = {
            category: exporter.tally([r for r in previous["roots"]
                                     if r["classification"] == category])
            for category in exporter.CATEGORIES}
        result = exporter.export(self.raw, "2026-10-09", previous)["comparison"]
        self.assertEqual(result["changed_roots"], 0)
        self.assertEqual(sum(t["count"] for t in result["classified_transitions"]), 2336)
        self.assertIn({"before_classification": "generated_or_other",
                       "after_classification": "source_function_heuristic",
                       "before": "proved", "after": "proved", "count": 1},
                      result["classified_transitions"])
        self.assertEqual(sum(t["count"] for t in result["unknown_blocker_transitions"]), 2)
        self.assertEqual({t["before"] for t in result["unknown_blocker_transitions"]},
                         {None, "earlier unsupported operation"})
        self.raw["roots"].reverse()
        self.assertEqual(result, exporter.export(self.raw, "2026-10-09", previous)["comparison"])

    def test_null_and_empty_blockers_have_distinct_deterministic_sort_positions(self):
        previous = deepcopy(self.raw)
        unknowns = [i for i, r in enumerate(self.raw["roots"]) if r["status"] == "unknown"
                    and r["classification"] == "source_function_heuristic"]
        for index, blocker in zip(unknowns[:2], [None, ""]):
            previous["roots"][index]["first_blocker"] = blocker
            self.raw["roots"][index]["first_blocker"] = "later unsupported operation"
        result = exporter.export(self.raw, "2026-10-09", previous)["comparison"]
        self.assertEqual(result["unknown_blocker_transitions"], [
            {"before": None, "after": "later unsupported operation", "count": 1},
            {"before": "", "after": "later unsupported operation", "count": 1}])
        previous["roots"].reverse()
        self.raw["roots"].reverse()
        self.assertEqual(result, exporter.export(self.raw, "2026-10-09", previous)["comparison"])

    def test_generated_blocker_changes_are_counted_without_expanding_diagnostic_text(self):
        previous = deepcopy(self.raw)
        generated = next(r for r in previous["roots"] if r["status"] == "unknown"
                         and r["classification"] == "generated_or_other")
        generated["first_blocker"] = "earlier generated blocker"
        result = exporter.export(self.raw, "2026-10-09", previous)["comparison"]
        self.assertEqual(result["unknown_blocker_change_counts"], [
            {"before_classification": "generated_or_other",
             "after_classification": "generated_or_other", "count": 1}])
        self.assertEqual(result["unknown_blocker_transitions"], [])
        self.assertEqual(result["unknown_blocker_transition_scope"],
                         "source_function_heuristic_in_either_collection")

    def test_compiler_display_grouping_preserves_actual_type_and_operation_changes(self):
        a = ("input dyn [Binder { value: Trait(control::Control), bound_vars: [] }, "
             "Binder { value: Projection(DefId(2:4 ~ control[abcd]::Target), "
             "Term::Ty([f32; 4_usize])), bound_vars: [] }]")
        b = ("input dyn [Binder { value: Projection(DefId(8:9 ~ control[1234]::Target), "
             "Term::Ty([f32; 4_usize])), bound_vars: [] }, "
             "Binder { value: Trait(control::Control), bound_vars: [] }]")
        self.assertEqual(exporter.stable_blocker_display(a), exporter.stable_blocker_display(b))
        for mutation in [b.replace("f32", "f64"), b.replace("4_usize", "3_usize"),
                         b.replace("::Target", "::Feedback"), b.replace("input", "call")]:
            self.assertNotEqual(exporter.stable_blocker_display(a),
                                exporter.stable_blocker_display(mutation))
        for unchanged in [None, "", "input dyn [Binder { malformed", "unsupported [abcd]"]:
            self.assertEqual(exporter.stable_blocker_display(unchanged), unchanged)
        previous = deepcopy(self.raw)
        index = next(i for i, r in enumerate(self.raw["roots"]) if r["status"] == "unknown"
                     and r["classification"] == "source_function_heuristic")
        previous["roots"][index]["first_blocker"] = a
        self.raw["roots"][index]["first_blocker"] = b
        result = exporter.comparison(self.raw, previous)
        self.assertEqual(result["unknown_blocker_display_changes"], [
            {"before_classification": "source_function_heuristic",
             "after_classification": "source_function_heuristic",
             "kind": "compiler_display_only", "count": 1}])
        self.assertEqual(result["unknown_blocker_transitions"], [
            {"before": a, "after": b, "count": 1}])
        self.assertEqual(result["changed_roots"], 0)

    def test_compiler_scope_counts_and_factory_rows_do_not_change_outcomes(self):
        result = exporter.export(self.raw, "2026-10-09")
        self.assertEqual(result["analysis_scope_counts"]["unclassified"], result["counts"])
        self.assertEqual(result["coroutine_factory_root_indices"], [])
        self.assertEqual(result["unclassified_root_indices"], list(range(2336)))
        root = self.raw["roots"][0]
        root["analysis_scope"] = "coroutine_factory"
        result = exporter.export(self.raw, "2026-10-09")
        index, = result["coroutine_factory_root_indices"]
        self.assertEqual(result["roots"][index][1], root["name"])
        self.assertEqual(result["analysis_scope_counts"]["coroutine_factory"][root["status"]], 1)
        self.raw["roots"].reverse()
        self.assertEqual(result, exporter.export(self.raw, "2026-10-09"))
        root["analysis_scope"] = "proved async body"
        with self.assertRaises(ValueError):
            exporter.export(self.raw, "2026-10-09")


if __name__ == "__main__":
    unittest.main()
