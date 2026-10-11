"""Hostile evidence tests for the pure strict Proof comparison helper."""

import copy
import unittest

from proof_compare import compare_proofs, queried_obligations, selected_proofs


def obligation(status="proved", query="(check-sat)", model=None):
    return {"status": status, "kind": "panic_safety", "function": "root", "detail": "claim",
            "source": {"file": "fixture.rs", "line": 1, "column": 1},
            "query": query, "model": model}


def proof(obligations=None):
    if obligations is None:
        obligations = [obligation()]
    status = "proved"
    if any(item["status"] == "refuted" for item in obligations):
        status = "refuted"
    elif any(item["status"] == "unknown" for item in obligations):
        status = "unknown"
    return {"status": status, "obligations": obligations, "assumptions": [], "trusted_calls": [],
            "inputs": {}, "models": [], "analyzed_bodies": [], "conditions": ["path"]}


def report(value, name="root"):
    return {"functions": [{"name": name, "proof": value}, {"name": "inventory", "proof": None}]}


def fold(chain=None, detail=None):
    root = "scalar_slice_unbounded_fold"
    item = obligation("unknown", None)
    item.update(function=root, kind="unsupported", unknown_category="resource_limit",
                detail=detail or "symbolic root exceeded the 30-second execution budget",
                call_chain=chain if chain is not None else [root])
    return proof([item])


class SelectedProofs(unittest.TestCase):
    def test_empty_proof_and_inventory_are_valid_without_injection(self):
        value = proof([])
        original = copy.deepcopy(value)
        self.assertIs(selected_proofs(report(value), ["root"], 0)["root"], value)
        self.assertEqual(value, original)
        self.assertNotIn("entry_assumptions", value)

    def test_all_nonnull_proofs_must_be_selected(self):
        for extra in [proof([]), dict(proof([]), status="proved_with_assumptions"), {}, False]:
            data = report(proof([]))
            data["functions"].append({"name": "extra", "proof": extra})
            with self.subTest(extra=extra), self.assertRaises(ValueError):
                selected_proofs(data, ["root"], 0)

    def test_empty_duplicate_missing_and_unselected_duplicate_fail(self):
        for entries in [[], ["root", "root"], ["other"], [True], "root"]:
            with self.subTest(entries=entries), self.assertRaises(ValueError):
                selected_proofs(report(proof([])), entries, 0)
        for extra in [None, proof([])]:
            data = report(proof([]))
            data["functions"].append({"name": "root", "proof": extra})
            with self.assertRaises(ValueError):
                selected_proofs(data, ["root"], 0)
        with self.assertRaises(ValueError):
            selected_proofs(report(None), ["root"], 0)

    def test_numeric_exit_policy_rejects_booleans_and_inconsistency(self):
        for value, expected in [(proof([]), 0), (proof([obligation("unknown")]), 1),
                                (proof([obligation("refuted", model="(model)")]), 1)]:
            selected_proofs(report(value), ["root"], expected)
            for code in [True, False, None, "1", 1.0, 2, 1 - expected]:
                with self.subTest(code=code, status=value["status"]), self.assertRaises(ValueError):
                    selected_proofs(report(value), ["root"], code)

    def test_contradictory_statuses_fail(self):
        for item_status, root_status in [("unknown", "proved"), ("refuted", "proved"),
                                         ("proved", "unknown"), ("refuted", "unknown"),
                                         ("proved", "refuted")]:
            value = proof([obligation(item_status, model="(model)" if item_status == "refuted"
                                      else None)])
            value["status"] = root_status
            with self.assertRaises(ValueError):
                selected_proofs(report(value), ["root"], 0)

    def test_refuted_with_unknown_partial_retains_all_rich_evidence(self):
        items = [obligation(), obligation("unknown"), obligation("refuted", model="(model)")]
        items[1]["extra"] = {"source": ["body", 2]}
        value = proof(items)
        selected_proofs(report(value), ["root"], 1)
        self.assertEqual(queried_obligations(value), items)
        self.assertIs(queried_obligations(value)[1], items[1])

    def test_malformed_report_shapes_fail(self):
        for data in [None, [], {}, {"functions": None}, {"functions": [None]},
                     {"functions": [{"name": 7, "proof": proof([])}]}, report([])]:
            with self.subTest(data=data), self.assertRaises(ValueError):
                selected_proofs(data, ["root"], 0)


class LiteralComparison(unittest.TestCase):
    def test_direct_comparison_validates_premises_and_shape(self):
        for field in ["assumptions", "trusted_calls", "entry_assumptions"]:
            for invalid in [None, False, {}, "", ["premise"]]:
                value = proof([])
                value[field] = invalid
                with self.assertRaises(ValueError):
                    compare_proofs("root", proof([]), value)
            if field != "entry_assumptions":
                value = proof([])
                del value[field]
                with self.assertRaises(ValueError):
                    compare_proofs("root", value, proof([]))
        for field, invalid in [("status", []), ("status", "invented"), ("obligations", None)]:
            value = proof([])
            value[field] = invalid
            with self.assertRaises(ValueError):
                compare_proofs("root", value, proof([]))

    def test_json_types_and_all_optional_fields_remain_literal(self):
        left = proof([])
        for a, b in [(True, 1), (1, 1.0), (None, []), ([1, 2], [2, 1])]:
            before, after = copy.deepcopy(left), copy.deepcopy(left)
            before["extra"], after["extra"] = {"nested": a}, {"nested": b}
            self.assertEqual(compare_proofs("root", before, after)["classification"], "DIFFERENT")
        after = dict(left, entry_assumptions=[])
        self.assertEqual(compare_proofs("root", left, after)["classification"], "DIFFERENT")
        self.assertEqual(compare_proofs("root", left, dict(reversed(list(left.items()))))[
            "classification"], "FULL")

    def test_invalid_json_and_missing_query_model_fail(self):
        for extra in [float("nan"), float("inf"), {1: "key"}, (1, 2)]:
            value = dict(proof([]), extra=extra)
            with self.assertRaises(ValueError):
                compare_proofs("root", value, proof([]))
        cyclic = proof([])
        cyclic["cycle"] = cyclic
        with self.assertRaises(ValueError):
            compare_proofs("root", cyclic, proof([]))
        for field in ["query", "model"]:
            value = proof()
            del value["obligations"][0][field]
            with self.assertRaises(ValueError):
                compare_proofs("root", value, proof())
        for query, model in [(None, "(model)"), ("query", None), ("", "(model)")]:
            value = proof([obligation("refuted", query, model)])
            with self.assertRaises(ValueError):
                compare_proofs("root", value, value)

    def test_query_model_source_and_order_mutations_are_differences(self):
        left = proof([obligation("unknown"), obligation("refuted", model="(model)")])
        original = copy.deepcopy(left)
        for field, changed in [("query", "other query"), ("model", "other model"),
                               ("source", {"file": "other.rs", "line": 2, "column": 3}),
                               ("detail", "other detail")]:
            right = copy.deepcopy(left)
            right["obligations"][1][field] = changed
            result = compare_proofs("root", left, right)
            self.assertEqual(result["classification"], "DIFFERENT")
            self.assertFalse(result["rich_queries_equal"])
        right = copy.deepcopy(left)
        right["obligations"].reverse()
        self.assertFalse(compare_proofs("root", left, right)["rich_query_prefix_equal"])
        self.assertEqual(left, original)

    def test_prefix_growth_is_diagnostic_not_full(self):
        left = proof([obligation("unknown")])
        right = copy.deepcopy(left)
        right["obligations"].append(obligation())
        result = compare_proofs("root", left, right)
        self.assertEqual(result["classification"], "DIFFERENT")
        self.assertEqual((result["baseline_ALL"], result["current_ALL"]), (1, 2))
        self.assertTrue(result["rich_query_prefix_equal"])
        self.assertFalse(result["rich_queries_equal"])


class ResourceContext(unittest.TestCase):
    def test_explicit_opt_in_exact_literals_and_immutability(self):
        root = "scalar_slice_unbounded_fold"
        left = fold()
        right = fold([root, root + "::{closure#0}"], root + "::{closure#0} bb0: "
                     "symbolic root exceeded the 30-second execution budget")
        saved = copy.deepcopy((left, right))
        self.assertEqual(compare_proofs(root, left, right)["classification"], "DIFFERENT")
        result = compare_proofs(root, left, right, True)
        self.assertEqual(result["classification"], "resource_context")
        self.assertEqual(result["resource_context"]["before"]["call_chain"], [root])
        self.assertEqual((left, right), saved)
        self.assertEqual(compare_proofs(root, left, left, True)["classification"], "FULL")

    def test_third_frame_and_every_predicate_residual_fail(self):
        root = "scalar_slice_unbounded_fold"
        left = fold()
        mutations = [("call_chain", [root, root + "::{closure#0}", "wrapping_add"]),
                     ("detail", "symbolic root exceeded the 31-second execution budget"),
                     ("query", "query"), ("model", "model"), ("function", "other"),
                     ("kind", "panic_safety"), ("unknown_category", "semantics"),
                     ("extra", True)]
        for field, changed in mutations:
            right = copy.deepcopy(left)
            right["obligations"][0][field] = changed
            with self.subTest(field=field):
                self.assertEqual(compare_proofs(root, left, right, True)["classification"],
                                 "DIFFERENT")
        for field, changed in [("models", ["different"]), ("conditions", ["different"])]:
            right = dict(left, **{field: changed})
            self.assertEqual(compare_proofs(root, left, right, True)["classification"], "DIFFERENT")
        right = fold([root, root + "::{closure#0}"])
        self.assertEqual(compare_proofs("other", left, right, True)["classification"], "DIFFERENT")
        right["obligations"].append(obligation("unknown", None))
        self.assertEqual(compare_proofs(root, left, right, True)["classification"], "DIFFERENT")
        with self.assertRaises(ValueError):
            compare_proofs(root, left, right, 1)


class DtoFields(unittest.TestCase):
    def assert_invalid(self, value):
        with self.assertRaises(ValueError):
            selected_proofs(report(value), ["root"], 0)
        with self.assertRaises(ValueError):
            compare_proofs("root", proof(), value)

    def test_required_source_fields_and_unsigned_coordinates(self):
        for field in ("file", "line", "column"):
            value = proof()
            del value["obligations"][0]["source"][field]
            self.assert_invalid(value)
        for source in [{}, None, {"file": 2, "line": 1, "column": 1},
                       {"file": "f", "line": True, "column": 1},
                       {"file": "f", "line": -1, "column": 1},
                       {"file": "f", "line": 1, "column": 1.0},
                       {"file": "f", "line": 1, "column": 1 << 64}]:
            value = proof()
            value["obligations"][0]["source"] = source
            self.assert_invalid(value)

    def test_required_proof_containers_and_members(self):
        for field in ("inputs", "models", "analyzed_bodies"):
            value = proof()
            del value[field]
            self.assert_invalid(value)
            for invalid in [None, False, "", [1], {"value": 1}]:
                value = proof()
                value[field] = invalid
                self.assert_invalid(value)
        valid = proof()
        valid.update(inputs={"arg": "1"}, models=["model"], analyzed_bodies=["body"])
        self.assertEqual(compare_proofs("root", valid, valid)["classification"], "FULL")

    def test_optional_flags_lists_categories_and_absence_stay_literal(self):
        for field in ("async_entry", "stopped_after_counterexample", "body_entries_truncated"):
            for invalid in [0, None, "false", []]:
                self.assert_invalid(dict(proof(), **{field: invalid}))
            left, right = proof(), dict(proof(), **{field: False})
            self.assertEqual(compare_proofs("root", left, right)["classification"], "DIFFERENT")
        for field in ("invariants", "matched_contracts", "body_entries"):
            for invalid in [None, False, "", [7]]:
                self.assert_invalid(dict(proof(), **{field: invalid}))
        for field in ("call_chain", "abstraction_reasons"):
            for invalid in [None, False, "", [7]]:
                value = proof()
                value["obligations"][0][field] = invalid
                self.assert_invalid(value)
        for invalid in [True, [], "invented"]:
            value = proof()
            value["obligations"][0]["unknown_category"] = invalid
            self.assert_invalid(value)

    def test_body_entry_source_and_instance_typing(self):
        entry = {"function": "callee", "instance": "callee::<u16>", "coroutine_poll": False,
                 "source": {"file": "f", "line": 1, "column": 2}, "call_chain": ["root"]}
        valid = dict(proof(), body_entries=[entry])
        self.assertEqual(compare_proofs("root", valid, valid)["classification"], "FULL")
        for field in entry:
            value = copy.deepcopy(valid)
            del value["body_entries"][0][field]
            self.assert_invalid(value)
        for field, invalid in [("instance", 3), ("coroutine_poll", 0), ("call_chain", [None]),
                               ("source", {"file": "f", "line": True, "column": 2})]:
            value = copy.deepcopy(valid)
            value["body_entries"][0][field] = invalid
            self.assert_invalid(value)

    def test_replay_arguments_nested_type_and_optional_maps(self):
        arguments = {"arguments": [{"name": "arg", "rust_type": "[u16;1]", "value": {
            "kind": "array", "elements": [{"kind": "integer", "symbol": "v0", "bits": 16,
                                            "signed": False}]}}], "unsupported": None,
                     "source_files": {"f": "sha"}, "build_environment": {},
                     "working_directory": "/tmp"}
        valid = dict(proof(), replay_inputs=arguments)
        self.assertEqual(compare_proofs("root", valid, valid)["classification"], "FULL")
        for field, invalid in [("arguments", [None]), ("unsupported", True),
                               ("source_files", {"f": False}), ("build_environment", []),
                               ("working_directory", 7)]:
            value = copy.deepcopy(valid)
            value["replay_inputs"][field] = invalid
            self.assert_invalid(value)
        for field, invalid in [("kind", "invented"), ("bits", True), ("bits", 1 << 32),
                               ("signed", 0), ("symbol", None)]:
            value = copy.deepcopy(valid)
            value["replay_inputs"]["arguments"][0]["value"]["elements"][0][field] = invalid
            self.assert_invalid(value)
        for invalid in [False, [], {"arguments": None}]:
            self.assert_invalid(dict(proof(), replay_inputs=invalid))

    def test_replay_result_and_source_typing(self):
        result = {"status": "not_reproduced", "detail": "replay", "inputs": {"v0": "1"},
                  "panic_source": {"file": "f", "line": 1, "column": 2},
                  "panic_message": None, "matches_obligation": False, "panic_strategy": "abort",
                  "uncontrolled_abstractions": []}
        valid = proof()
        valid["obligations"][0]["replay"] = result
        self.assertEqual(compare_proofs("root", valid, valid)["classification"], "FULL")
        for field, invalid in [("status", "invented"), ("detail", None), ("inputs", []),
                               ("matches_obligation", 0), ("panic_strategy", False),
                               ("panic_message", True), ("uncontrolled_abstractions", [2]),
                               ("panic_source", {"file": "f", "line": 1})]:
            value = copy.deepcopy(valid)
            value["obligations"][0]["replay"][field] = invalid
            self.assert_invalid(value)
        for field in ("status", "detail", "inputs", "matches_obligation", "panic_strategy"):
            value = copy.deepcopy(valid)
            del value["obligations"][0]["replay"][field]
            self.assert_invalid(value)


if __name__ == "__main__":
    unittest.main()
