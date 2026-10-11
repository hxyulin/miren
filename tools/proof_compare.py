"""Pure strict selected-Proof validation and literal JSON comparison.

This validates evidence shape and comparisons, not compiler/input provenance or proof truth.
Callers retain raw records and decide whether a valid DIFFERENT result requires stopping.
"""

import copy
import json


STATUSES = {"proved", "refuted", "unknown"}
KINDS = {"panic_safety", "validity", "call_precondition", "postcondition", "unsupported"}
FOLD_ROOT = "scalar_slice_unbounded_fold"
FOLD_MESSAGE = "symbolic root exceeded the 30-second execution budget"


def _json_keys(value):
    if type(value) is dict:
        if any(type(key) is not str for key in value):
            raise ValueError("JSON object keys must be strings")
        for item in value.values():
            _json_keys(item)
    elif type(value) is list:
        for item in value:
            _json_keys(item)
    elif type(value) not in (str, int, float, bool, type(None)):
        raise ValueError("non-JSON value")


def _literal(value):
    """Keep JSON types, keys and list order exact; object order is immaterial."""
    try:
        _json_keys(value)
        return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)
    except (TypeError, RecursionError) as error:
        raise ValueError("invalid JSON value") from error


def _string(value):
    return type(value) is str and bool(value)


def _string_list(value):
    return type(value) is list and all(type(item) is str for item in value)


def _string_map(value):
    return type(value) is dict and all(type(key) is str and type(item) is str
                                      for key, item in value.items())


def _unsigned(value, maximum=(1 << 64) - 1):
    return type(value) is int and 0 <= value <= maximum


def _validate_source(source):
    if (type(source) is not dict or type(source.get("file")) is not str
            or not _unsigned(source.get("line")) or not _unsigned(source.get("column"))):
        raise ValueError("invalid Source file/line/column")


def _validate_body_entry(entry):
    if (type(entry) is not dict or type(entry.get("function")) is not str
            or type(entry.get("instance")) is not str
            or type(entry.get("coroutine_poll")) is not bool
            or not _string_list(entry.get("call_chain"))):
        raise ValueError("invalid body entry")
    _validate_source(entry.get("source"))


def _validate_replay_value(value):
    if type(value) is not dict or type(value.get("kind")) is not str:
        raise ValueError("invalid replay value")
    kind = value["kind"]
    if kind == "unit":
        return
    if kind in ("bool", "integer"):
        if type(value.get("symbol")) is not str:
            raise ValueError("invalid replay symbol")
        if kind == "integer" and (not _unsigned(value.get("bits"), (1 << 32) - 1)
                                  or type(value.get("signed")) is not bool):
            raise ValueError("invalid replay integer")
        return
    if kind == "array" and type(value.get("elements")) is list:
        for item in value["elements"]:
            _validate_replay_value(item)
        return
    raise ValueError("invalid replay value kind")


def _validate_replay_arguments(arguments):
    if type(arguments) is not dict or type(arguments.get("arguments")) is not list:
        raise ValueError("invalid replay arguments")
    for argument in arguments["arguments"]:
        if (type(argument) is not dict or type(argument.get("name")) is not str
                or type(argument.get("rust_type")) is not str):
            raise ValueError("invalid replay argument")
        _validate_replay_value(argument.get("value"))
    for field in ("unsupported", "working_directory"):
        if (field in arguments and arguments[field] is not None
                and type(arguments[field]) is not str):
            raise ValueError("invalid replay " + field)
    for field in ("source_files", "build_environment"):
        if field in arguments and not _string_map(arguments[field]):
            raise ValueError("invalid replay " + field)


def _validate_replay_result(result):
    statuses = {"confirmed_panic", "not_reproduced", "unsupported", "tool_failure"}
    if (type(result) is not dict or type(result.get("status")) is not str
            or result["status"] not in statuses or type(result.get("detail")) is not str
            or not _string_map(result.get("inputs"))
            or type(result.get("matches_obligation")) is not bool
            or type(result.get("panic_strategy")) is not str):
        raise ValueError("invalid replay result")
    if result.get("panic_source") is not None:
        _validate_source(result["panic_source"])
    if "panic_message" in result and result["panic_message"] is not None:
        if type(result["panic_message"]) is not str:
            raise ValueError("invalid panic message")
    if "uncontrolled_abstractions" in result:
        if not _string_list(result["uncontrolled_abstractions"]):
            raise ValueError("invalid replay abstractions")


def _validate_proof_fields(proof):
    if not _string_map(proof.get("inputs")):
        raise ValueError("invalid required Proof inputs")
    for field in ("models", "analyzed_bodies"):
        if not _string_list(proof.get(field)):
            raise ValueError("invalid required Proof " + field)
    for field in ("async_entry", "stopped_after_counterexample", "body_entries_truncated"):
        if field in proof and type(proof[field]) is not bool:
            raise ValueError("invalid Proof " + field)
    for field in ("invariants", "matched_contracts"):
        if field in proof and not _string_list(proof[field]):
            raise ValueError("invalid Proof " + field)
    if "body_entries" in proof:
        if type(proof["body_entries"]) is not list:
            raise ValueError("invalid body entries")
        for entry in proof["body_entries"]:
            _validate_body_entry(entry)
    if proof.get("replay_inputs") is not None:
        _validate_replay_arguments(proof["replay_inputs"])


def _validate_obligation_fields(obligation):
    _validate_source(obligation.get("source"))
    for field in ("call_chain", "abstraction_reasons"):
        if field in obligation and not _string_list(obligation[field]):
            raise ValueError("invalid obligation " + field)
    categories = {"semantics", "missing_compiler_evidence", "solver", "resource_limit",
                  "external_environment", "unclassified"}
    category = obligation.get("unknown_category")
    if category is not None and (type(category) is not str or category not in categories):
        raise ValueError("invalid unknown category")
    if obligation.get("replay") is not None:
        _validate_replay_result(obligation["replay"])


def _validate_proof(proof):
    _literal(proof)
    if (type(proof) is not dict or type(proof.get("status")) is not str
            or proof["status"] not in STATUSES):
        raise ValueError("invalid Proof status or shape")
    _validate_proof_fields(proof)
    for field in ("assumptions", "trusted_calls"):
        if type(proof.get(field)) is not list or proof[field] != []:
            raise ValueError("strict Proof requires explicit empty " + field)
    if "entry_assumptions" in proof:
        if type(proof["entry_assumptions"]) is not list or proof["entry_assumptions"] != []:
            raise ValueError("strict Proof requires empty entry_assumptions")
    obligations = proof.get("obligations")
    if type(obligations) is not list:
        raise ValueError("invalid obligations")
    for obligation in obligations:
        if (type(obligation) is not dict or type(obligation.get("status")) is not str
                or obligation["status"] not in STATUSES
                or type(obligation.get("kind")) is not str or obligation["kind"] not in KINDS
                or not _string(obligation.get("function"))
                or type(obligation.get("detail")) is not str
                or type(obligation.get("source")) is not dict):
            raise ValueError("invalid obligation shape")
        _validate_obligation_fields(obligation)
        for field in ("query", "model"):
            if field not in obligation:
                raise ValueError("missing obligation " + field)
            if obligation[field] is not None and not _string(obligation[field]):
                raise ValueError("invalid obligation " + field)
        if obligation["status"] == "refuted":
            if not _string(obligation["query"]) or not _string(obligation["model"]):
                raise ValueError("refuted obligation lacks query/model evidence")
    status = "proved"
    if any(item["status"] == "refuted" for item in obligations):
        status = "refuted"
    elif any(item["status"] == "unknown" for item in obligations):
        status = "unknown"
    if proof["status"] != status:
        raise ValueError("Proof status contradicts obligations")


def selected_proofs(report, entries, numeric_exit):
    """Extract ALL selected Proofs, rejecting duplicates, premises and inconsistent exits.

    Inventory-only functions may remain. No input fields are added or normalized.
    Returned Proof dictionaries are the original objects and must be treated as read-only.
    """
    if (type(entries) is not list or not entries or any(not _string(e) for e in entries)
            or len(entries) != len(set(entries))):
        raise ValueError("expected entries must be a nonempty unique string list")
    _literal(report)
    if type(report) is not dict or type(report.get("functions")) is not list:
        raise ValueError("invalid report shape")
    functions = report["functions"]
    if any(type(f) is not dict or not _string(f.get("name")) for f in functions):
        raise ValueError("invalid function shape")
    selected = [f for f in functions if f.get("proof") is not None]
    names = [f["name"] for f in selected]
    if len(names) != len(set(names)) or set(names) != set(entries):
        raise ValueError("selected Proof set differs from expected entries")
    for entry in entries:
        if sum(function["name"] == entry for function in functions) != 1:
            raise ValueError("duplicate requested root")
    for function in selected:
        _validate_proof(function["proof"])
    result = {function["name"]: function["proof"] for function in selected}
    expected_exit = 0 if all(proof["status"] == "proved" for proof in result.values()) else 1
    if type(numeric_exit) is not int or numeric_exit != expected_exit:
        raise ValueError("numeric exit contradicts selected Proof statuses")
    return result


def queried_obligations(proof):
    """Return complete ordered obligations with nonnull queries, including UNKNOWN partials."""
    _validate_proof(proof)
    return [item for item in proof["obligations"] if item["query"] is not None]


def _fold_context(name, before, after):
    if name != FOLD_ROOT:
        return None
    closure = FOLD_ROOT + "::{closure#0}"
    details = (FOLD_MESSAGE, closure + " bb0: " + FOLD_MESSAGE)
    chains = ([FOLD_ROOT], [FOLD_ROOT, closure])
    for proof in (before, after):
        if proof["status"] != "unknown" or len(proof["obligations"]) != 1:
            return None
        item = proof["obligations"][0]
        if (item["status"] != "unknown" or item["kind"] != "unsupported"
                or item.get("unknown_category") != "resource_limit"
                or item["function"] != FOLD_ROOT or item["query"] is not None
                or item["model"] is not None or item["detail"] not in details
                or item.get("call_chain") not in chains):
            return None
    observed = {}
    residuals = []
    for side, original in (("before", before), ("after", after)):
        residual = copy.deepcopy(original)
        item = residual["obligations"][0]
        observed[side] = {field: item.pop(field) for field in ("detail", "call_chain")}
        residuals.append(residual)
    return observed if _literal(residuals[0]) == _literal(residuals[1]) else None


def compare_proofs(name, before, after, allow_scalar_fold_context=False):
    """Return FULL/resource_context/DIFFERENT diagnostics; never approve a promotion.

    Direct calls validate both Proofs. The opt-in resource allowance is closed to one exact
    query-free fold predicate; extra frames remain DIFFERENT. Inputs are never mutated.
    """
    if not _string(name) or type(allow_scalar_fold_context) is not bool:
        raise ValueError("invalid comparison name or resource policy")
    _validate_proof(before)
    _validate_proof(after)
    left = queried_obligations(before)
    right = queried_obligations(after)
    classification = "DIFFERENT"
    context = None
    if _literal(before) == _literal(after):
        classification = "FULL"
    elif allow_scalar_fold_context:
        context = _fold_context(name, before, after)
        if context is not None:
            classification = "resource_context"
    return {"classification": classification, "baseline_ALL": len(left), "current_ALL": len(right),
            "rich_queries_equal": _literal(left) == _literal(right),
            "rich_query_prefix_equal": len(left) <= len(right)
            and _literal(left) == _literal(right[:len(left)]), "resource_context": context}
