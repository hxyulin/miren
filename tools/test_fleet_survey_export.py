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


if __name__ == "__main__":
    unittest.main()
