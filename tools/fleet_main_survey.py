#!/usr/bin/env python3
"""Replay every binary Embassy main in separate body, registration and runtime scopes."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import sys

import fleet_survey as survey
import fleet_survey_export as exporter

FACTORY = "____embassy_main_task::____embassy_main_task_inner_function"
SCOPES = {
    "async_body": (FACTORY, True,
                   "Fresh future construction and reached polls with arbitrary valid shared state; "
                   "no executor scheduling, "
                   "startup history, cancellation, output drops or infinite-loop induction."),
    "task_registration": ("__embassy_main", False,
                          "Task registration from arbitrary root inputs; no deferred polls "
                          "or startup history."),
    "runtime_entry": ("__cortex_m_rt_main", False,
                      "Runtime wrapper from arbitrary root state; a counterexample does not "
                      "establish a reachable boot panic."),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def normalized_contract_config(value):
    require(isinstance(value, dict) and set(value) == {"schema_version", "functions"}
            and type(value["schema_version"]) is int and value["schema_version"] == 1,
            "invalid contract configuration schema")
    require(isinstance(value["functions"], list), "missing configured functions")
    defaults = {"instance": None, "arguments": [], "requires": [], "ensures": [],
                "trusted": False, "no_panic": False, "modifies": None, "reason": None}
    functions, selectors = [], set()
    for raw in value["functions"]:
        require(isinstance(raw, dict) and "function" in raw
                and set(raw) <= {"function", "returns_alias", *defaults},
                "invalid configured function fields")
        spec = {**defaults, **raw}
        name = spec["function"]
        require(isinstance(name, str) and "::" in name and name.strip() == name
                and not any(c in name for c in "*?"), "contracts need exact qualified selectors")
        require(spec["instance"] is None or isinstance(spec["instance"], str),
                "invalid configured instance")
        selector = (name, spec["instance"])
        require(selector not in selectors, "duplicate configured selector")
        selectors.add(selector)
        for key in ("arguments", "requires", "ensures"):
            require(isinstance(spec[key], list)
                    and all(isinstance(v, str) for v in spec[key]), "invalid " + key)
        for key in ("trusted", "no_panic"):
            require(type(spec[key]) is bool, "invalid " + key)
        require(spec["modifies"] is None or (isinstance(spec["modifies"], list)
                and all(isinstance(v, str) for v in spec["modifies"])), "invalid modifies")
        require(spec["reason"] is None or isinstance(spec["reason"], str), "invalid reason")
        if spec.get("returns_alias") is None:
            spec.pop("returns_alias", None)
        else:
            require(isinstance(spec["returns_alias"], str), "invalid returns_alias")
        if spec["trusted"]:
            require(spec["no_panic"] and spec["reason"] and spec["reason"].strip(),
                    "trusted contracts require no_panic and a reason")
        functions.append(spec)
    return {"schema_version": 1, "functions": functions}


def conditional_proof(proof):
    return bool(proof.get("assumptions") or proof.get("trusted_calls")
                or proof.get("entry_assumptions")
                or proof.get("status") == "proved_with_assumptions")


def counterexample_evidence(proof):
    """Describe solver evidence without upgrading it to boot or native reachability."""
    return [{"classification": "abstract_model_counterexample" if obligation.get(
                "abstraction_reasons") else "solver_counterexample",
             "abstraction_reasons": obligation.get("abstraction_reasons", []),
             "function": obligation.get("function"), "source": obligation.get("source"),
             "boot_reachability": "unverified", "native_confirmation": "not_collected"}
            for obligation in proof.get("obligations", [])
            if obligation.get("status") == "refuted"]


def valid_body_entry(entry):
    if not isinstance(entry, dict):
        return False
    source, chain = entry.get("source"), entry.get("call_chain")
    return (all(isinstance(entry.get(key), str) and entry[key]
                for key in ("function", "instance"))
            and type(entry.get("coroutine_poll")) is bool
            and isinstance(source, dict) and isinstance(source.get("file"), str)
            and bool(source["file"])
            and all(type(source.get(key)) is int and source[key] > 0
                    for key in ("line", "column"))
            and isinstance(chain, list) and bool(chain)
            and all(isinstance(name, str) and name for name in chain)
            and chain[-1] == entry["function"])


def application_body_reached(proof):
    """Require a feasible entry into this root's coroutine poll, not its constructor."""
    entries = proof.get("body_entries", [])
    if (proof.get("async_entry") is not True or not isinstance(entries, list)
            or proof.get("body_entries_truncated", False) is not False):
        return False
    return any(valid_body_entry(entry) and entry["coroutine_poll"]
               and entry["function"] == FACTORY + "::{closure#0}"
               and entry["call_chain"][0] == FACTORY for entry in entries)


def annotate_evidence(result):
    result["milestone_scope"] = "async body analyzer outcomes under recorded root domains"
    result["boot_reachability"] = "unverified"
    for unit in result["units"]:
        for root in unit["roots"]:
            root["analysis_domain"] = SCOPES[root["scope"]][2]
            root["boot_reachability"] = "unverified"
            root["counterexample_evidence"] = counterexample_evidence(root.get("proof", {})) \
                if root.get("status") == "complete" else []
            if root["scope"] == "async_body":
                root["application_body_reached"] = (root.get("status") == "complete"
                                                    and application_body_reached(
                                                        root.get("proof", {})))


def contract_selector(spec):
    return spec["function"] + (" " + spec["instance"] if spec["instance"] is not None else "")


def validate_proof_policy(proof, report, unit, name, config, allow_assumptions):
    require(all(isinstance(proof.get(key, []), list) for key in
                ("assumptions", "entry_assumptions", "trusted_calls", "invariants")),
            "invalid proof policy metadata")
    require(not proof.get("entry_assumptions") and not proof.get("invariants"),
            "unexpected startup assumptions or induction")
    if not allow_assumptions:
        require(not conditional_proof(proof), "unexpected assumptions or trusted calls")
        require(report.get("contract_config") is None, "unexpected contract configuration")
        return
    require(config is not None, "missing explicit contract configuration")
    normalized_contract_config(report.get("contract_config"))
    require(report.get("contract_config") == config, "contract configuration mismatch")
    matched = proof.get("matched_contracts", [])
    require(isinstance(matched, list)
            and all(selector in {contract_selector(s) for s in config["functions"]}
                    for selector in matched), "unexpected matched contract selector")
    approved = [spec for spec in config["functions"]
                if spec["function"] == unit["crate_name"] + "::" + name
                and contract_selector(spec) in matched]
    assumptions = proof.get("assumptions", [])
    require(isinstance(assumptions, list) and (not assumptions or any(
            assumptions == spec["requires"] for spec in approved)),
            "unexpected root preconditions")
    trusted = proof.get("trusted_calls", [])
    require(isinstance(trusted, list), "invalid trusted calls")
    for call in trusted:
        require(isinstance(call, dict) and isinstance(call.get("contract"), dict)
                and call["contract"] in config["functions"] and call["contract"]["trusted"],
                "unauthorized trusted call contract")
        spec = call["contract"]
        normalized_contract_config({"schema_version": 1, "functions": [spec]})
        require(contract_selector(spec) in matched
                and isinstance(call.get("instance"), str)
                and (spec["instance"] is None or spec["instance"] == call["instance"]),
                "unauthorized trusted call instance")
    if proof["status"] == "proved_with_assumptions":
        require(bool(assumptions or trusted), "conditional proof has no recorded assumptions")


def captured_environment(provenance, inventory):
    captured = inventory.get("compiler_environment")
    require(isinstance(captured, dict)
            and all(isinstance(k, str) and isinstance(v, str) for k, v in captured.items()),
            "missing or invalid captured compiler environment")
    recorded = provenance.get("environment")
    require(isinstance(recorded, dict)
            and set(recorded) <= {"MIREN_Z3", "RUSTUP_TOOLCHAIN"},
            "unexpected survey environment policies")
    require(not any(k.startswith("MIREN_") for k in captured),
            "unexpected compiler environment policies")
    env = {key: value for key, value in os.environ.items()
           if not key.startswith(("CARGO_", "DEP_", "MIREN_")) and key != "OUT_DIR"}
    env.update(recorded)
    env.update(captured)
    return env


def inventories(summary, directory):
    records = []
    for workspace in summary["workspaces"]:
        invocation = workspace["inventory"]
        arguments = invocation["command"]
        require(arguments.count("--jsonl") == 1, "missing inventory report argument")
        path = directory / Path(arguments[arguments.index("--jsonl") + 1]).name
        parsed, errors = survey.reports(path.read_bytes())
        require(not errors, "malformed inventory " + str(path))
        records.extend((report, survey.compiler_cwd(report, Path(invocation["cwd"])))
                       for report in parsed)
    selected = []
    excluded = []
    for unit in sorted(summary["units"], key=lambda u: u["id"]):
        if "bin" not in unit["kinds"]:
            continue
        matches = [(record, cwd) for record, cwd in records
                   if survey.unit_matches(unit, record, cwd)]
        require(len(matches) == 1, "missing or duplicate inventory " + unit["id"])
        record, cwd = matches[0]
        names = {function["name"] for function in record["functions"]}
        captured_names = {root["name"] for root in summary["roots"]
                          if root["id"] == unit["id"] + "::" + root["name"]}
        require(names == captured_names, "inventory root set mismatch " + unit["id"])
        if FACTORY in names:
            selected.append((unit, record, cwd))
        else:
            excluded.append({"id": unit["id"], "reason": "no exact Embassy main factory"})
    require(selected, "no Embassy main factories found")
    return selected, excluded


def checked_proof(unit, inventory, report, cwd, scope, limits, returncode,
                  config=None, allow_assumptions=False):
    require(returncode in (0, 1), "compiler process failed")
    require(survey.unit_matches(unit, report, cwd), "compilation unit mismatch")
    for key in ("compiler", "target", "panic_strategy", "overflow_checks", "mir_phase",
                "rustc_arguments", "compiler_environment", "working_directory"):
        require(report.get(key) == inventory.get(key), "configuration mismatch: " + key)
    require(report.get("analysis_limits") == limits, "analysis limits mismatch")
    name, asynchronous, _ = SCOPES[scope]
    proofs = [f for f in report["functions"] if f.get("proof") is not None]
    require(len(proofs) == 1 and proofs[0]["name"] == name,
            "missing, duplicate or unexpected selected root")
    original = next((f for f in inventory["functions"] if f["name"] == name), None)
    require(original is not None and proofs[0]["source"] == original["source"],
            "selected root source mismatch")
    proof = proofs[0]["proof"]
    require(proof.get("status") in survey.STATUSES, "invalid proof status")
    require(proof.get("async_entry") is asynchronous, "proof scope mismatch")
    entries = proof.get("body_entries", [])
    require(isinstance(entries, list) and len(entries) <= 512
            and all(valid_body_entry(entry) for entry in entries),
            "invalid executed body entry evidence")
    require(type(proof.get("body_entries_truncated", False)) is bool,
            "invalid executed body entry truncation metadata")
    validate_proof_policy(proof, report, unit, name, config, allow_assumptions)
    obligations = proof.get("obligations")
    require(isinstance(obligations, list), "missing obligations")
    require(all(o.get("status") in {"proved", "refuted", "unknown"} for o in obligations),
            "invalid obligation status")
    if proof["status"] in {"proved", "proved_with_assumptions"}:
        require(returncode == 0 and all(o["status"] == "proved" for o in obligations),
                "failed or unfinished proof")
    if proof["status"] == "refuted":
        require(any(o["status"] == "refuted" for o in obligations),
                "refuted root has no counterexample obligation")
    return proof


def invalidate(item, reason):
    item.update(status="failed", proof_status="unknown", failure=reason)


def run(args):
    contract_path = getattr(args, "contracts", None)
    profile_path = getattr(args, "assumptions_profile", None)
    allow_assumptions = getattr(args, "allow_assumptions", False)
    require(not (contract_path and profile_path),
            "--contracts and --assumptions-profile are mutually exclusive")
    policy_path = contract_path or profile_path
    require(bool(policy_path) == allow_assumptions,
            "an explicit contract file and --allow-assumptions must be supplied together")
    contract_bytes = policy_path.read_bytes() if policy_path else None
    raw_policy = json.loads(contract_bytes) if contract_bytes is not None else None
    config = normalized_contract_config(raw_policy) if contract_path else None
    profiles = {}
    if profile_path:
        require(isinstance(raw_policy, dict) and set(raw_policy) == {"schema_version", "units"}
                and type(raw_policy["schema_version"]) is int and raw_policy["schema_version"] == 1
                and isinstance(raw_policy["units"], dict), "invalid assumptions profile schema")
        profiles = {identity: normalized_contract_config(value)
                    for identity, value in raw_policy["units"].items()}
    summary = json.loads(args.survey.read_text())
    exporter.validate(summary)
    selected, excluded = inventories(summary, args.survey.parent)
    expected = [unit["id"] for unit, _, _ in selected]
    require(set(profiles) <= set(expected), "assumptions profile has unknown unit selectors")
    requested = set(args.unit or expected)
    require(requested <= set(expected), "unknown --unit selector")
    selected = [entry for entry in selected if entry[0]["id"] in requested]
    roots = [Path(w["inventory"]["cwd"]) for w in summary["workspaces"] if w["id"] == "."]
    require(len(roots) == 1, "missing fleet root workspace")
    fleet = roots[0].resolve()
    provenance = summary["provenance"]
    limits = dict(provenance["limits"])
    require(set(limits) == set(survey.LIMITS)
            and all(type(v) is int and v > 0 for v in limits.values()), "invalid limits")
    for key in survey.LIMITS:
        override = getattr(args, key)
        if override is not None:
            limits[key] = override
    output = args.output.resolve()
    output.mkdir(exist_ok=False)
    result = {"schema_version": 1, "status": "partial", "errors": [], "units": [],
              "survey": str(args.survey.resolve()), "survey_sha256": survey.digest(args.survey),
              "expected_units": expected, "selected_units": sorted(requested),
              "coverage_scope": "all_embassy_binary_mains" if requested == set(expected)
              else "selected_embassy_binary_mains", "excluded_binaries": excluded,
              "scopes": {k: {"entry": v[0], "async_entry": v[1], "scope": v[2]}
                         for k, v in SCOPES.items()}, "limits": limits,
              "analyzer_source": survey.revision(Path(__file__).resolve().parents[1]),
              "allow_assumptions": allow_assumptions, "contract_config": config,
              "contract_profiles": profiles, "contracts_scope": "async_body_only"}
    survey.save(output / "summary.json", result)
    frozen_contract = None
    try:
        if contract_bytes is not None:
            frozen_contract = output / "contracts.json"
            frozen_contract.write_bytes(contract_bytes)
            result["contracts"] = {"source": str(policy_path.resolve()),
                                   "snapshot": str(frozen_contract),
                                   "sha256": hashlib.sha256(contract_bytes).hexdigest()}
        analyzer, binaries = survey.freeze_analyzer(args.analyzer.resolve(), output)
        require(analyzer.is_file(), "missing analyzer executable")
        result["analyzer_binaries"] = binaries
        before_source = survey.source_hashes(fleet, output)
        result["source_files_before"] = before_source
        require(before_source == provenance["source_files_after"],
                "source files changed since captured survey")
        for unit, inventory, cwd in selected:
            unit_config = config if contract_path else profiles.get(unit["id"])
            unit_contract = None
            if unit_config is not None:
                token = hashlib.sha256(unit["id"].encode()).hexdigest()[:16]
                unit_contract = output / ("contracts-" + token + ".json")
                survey.save(unit_contract, unit_config)
            entry = {"id": unit["id"], "status": "partial", "roots": [],
                     "contract_config": unit_config,
                     "contract_snapshot": str(unit_contract) if unit_contract else None,
                     "contract_sha256": survey.digest(unit_contract) if unit_contract else None}
            result["units"].append(entry)
            try:
                env = captured_environment(provenance, inventory)
                inputs = survey.artifact_inputs(inventory, cwd)
                entry["artifact_inputs"] = inputs
                entry["artifact_hashes_before"] = survey.artifact_hashes(inputs)
                require(entry["artifact_hashes_before"]
                        == unit.get("artifact_hashes_at_completion"),
                        "dependency/generated inputs changed since captured survey")
                for scope, (name, asynchronous, _) in SCOPES.items():
                    item = {"scope": scope, "name": name, "status": "failed",
                            "proof_status": "unknown", "failure": None}
                    entry["roots"].append(item)
                    try:
                        require(any(f["name"] == name for f in inventory["functions"]),
                                "selected wrapper body missing from inventory")
                        identity = (unit["id"] + "::" + scope).encode()
                        token = hashlib.sha256(identity).hexdigest()[:16]
                        prefix = output / ("verify-" + token)
                        path = prefix.with_suffix(".jsonl")
                        command = [str(analyzer), "rustc", "--verify", "--quiet",
                                   "--async-entry" if asynchronous else "--entry", name,
                                   "--jsonl", str(path)]
                        for key, value in limits.items():
                            command.extend(["--" + key.replace("_", "-"), str(value)])
                        use_contract = unit_contract is not None and scope == "async_body"
                        if frozen_contract is not None:
                            require(survey.digest(frozen_contract) == result["contracts"]["sha256"]
                                    and survey.digest(policy_path) == result["contracts"]["sha256"],
                                    "contract configuration changed before root")
                        if use_contract:
                            require(survey.digest(unit_contract) == entry["contract_sha256"],
                                    "unit contract snapshot changed before root")
                            command.extend(["--contracts", str(unit_contract),
                                            "--allow-assumptions"])
                        command.extend(["--", *inventory["rustc_arguments"]])
                        before = survey.artifact_hashes(inputs)
                        require(before == entry["artifact_hashes_before"],
                                "dependency/generated inputs changed before root")
                        invocation, _ = survey.execute(command, cwd, env, prefix, args.unit_timeout)
                        item["verification"] = invocation
                        item["report"] = str(path)
                        if frozen_contract is not None:
                            require(survey.digest(frozen_contract) == result["contracts"]["sha256"]
                                    and survey.digest(policy_path) == result["contracts"]["sha256"],
                                    "contract configuration changed during root")
                        if use_contract:
                            require(survey.digest(unit_contract) == entry["contract_sha256"],
                                    "unit contract snapshot changed during root")
                        after = survey.artifact_hashes(inputs)
                        require(before == after, "dependency/generated inputs changed during root")
                        require(path.is_file(), "missing proof report")
                        reports, errors = survey.reports(path.read_bytes())
                        require(not errors and len(reports) == 1,
                                "malformed or duplicate proof report")
                        proof = checked_proof(unit, inventory, reports[0], cwd, scope, limits,
                                              invocation.get("returncode"),
                                              unit_config if use_contract else None,
                                              use_contract)
                        item.update(status="complete", proof_status=proof["status"], proof=proof,
                                    conditional=conditional_proof(proof))
                    except (ValueError, OSError, KeyError, TypeError) as error:
                        invalidate(item, str(error))
                    survey.save(output / "summary.json", result)
                entry["artifact_hashes_after"] = survey.artifact_hashes(inputs)
                require(entry["artifact_hashes_before"] == entry["artifact_hashes_after"],
                        "dependency/generated inputs changed during unit")
                entry["status"] = "complete" if all(r["status"] == "complete"
                                                   for r in entry["roots"]) else "partial"
            except (ValueError, OSError, KeyError, TypeError) as error:
                entry["error"] = str(error)
                for scope, (name, _, _) in SCOPES.items():
                    if not any(r["scope"] == scope for r in entry["roots"]):
                        entry["roots"].append({"scope": scope, "name": name})
                for item in entry["roots"]:
                    invalidate(item, str(error))
            survey.save(output / "summary.json", result)
        if frozen_contract is not None:
            result["contracts"]["source_sha256_at_completion"] = survey.digest(policy_path)
            result["contracts"]["snapshot_sha256_at_completion"] = survey.digest(frozen_contract)
            require(result["contracts"]["source_sha256_at_completion"]
                    == result["contracts"]["snapshot_sha256_at_completion"]
                    == result["contracts"]["sha256"],
                    "contract configuration changed during survey")
        result["source_files_after"] = survey.source_hashes(fleet, output)
        if before_source != result["source_files_after"]:
            result["errors"].append("source files changed during main survey")
            for entry in result["units"]:
                entry["status"] = "partial"
                for item in entry["roots"]:
                    invalidate(item, "source files changed during main survey")
        for entry in result["units"]:
            if entry.get("contract_snapshot"):
                final = survey.digest(Path(entry["contract_snapshot"]))
                entry["contract_sha256_at_completion"] = final
                require(final == entry["contract_sha256"], "unit contract snapshot changed")
            if "artifact_inputs" not in entry:
                continue
            final = survey.artifact_hashes(entry["artifact_inputs"])
            entry["artifact_hashes_at_completion"] = final
            if final != entry["artifact_hashes_before"]:
                entry["status"] = "partial"
                for item in entry["roots"]:
                    invalidate(item, "dependency/generated inputs changed before completion")
        if not result["errors"] and all(u["status"] == "complete" for u in result["units"]):
            result["status"] = "complete"
    except (ValueError, OSError, KeyError, TypeError) as error:
        result["errors"].append(str(error))
    result["missing_units"] = sorted(requested - {u["id"] for u in result["units"]})
    for identity in result["missing_units"]:
        result["units"].append({"id": identity, "status": "partial", "roots": [
            {"scope": scope, "name": values[0], "status": "failed", "proof_status": "unknown",
             "failure": "unit not collected"} for scope, values in SCOPES.items()]})
    if result["errors"]:
        for entry in result["units"]:
            entry["status"] = "partial"
            for item in entry["roots"]:
                invalidate(item, "; ".join(result["errors"]))
    annotate_evidence(result)
    result["milestone_reached"] = milestone_reached(result)
    result["conditional_milestone_reached"] = conditional_milestone_reached(result)
    result["fresh_future_entry_milestone_reached"] = fresh_future_entry_milestone_reached(result)
    result["counts"] = {scope: {status: sum(r.get("proof_status") == status
                                           for u in result["units"] for r in u["roots"]
                                           if r["scope"] == scope)
                               for status in sorted(survey.STATUSES)} for scope in SCOPES}
    survey.save(output / "summary.json", result)
    print(json.dumps({"status": result["status"], "coverage_scope": result["coverage_scope"],
                      "units": len(result["units"]), "counts": result["counts"],
                      "milestone_reached": result["milestone_reached"],
                      "conditional_milestone_reached": result["conditional_milestone_reached"],
                      "fresh_future_entry_milestone_reached":
                          result["fresh_future_entry_milestone_reached"]},
                     sort_keys=True))
    return 0 if result["status"] == "complete" else 1



def milestone_reached(result):
    """Only complete body coverage can satisfy the supported-outcome milestone."""
    if result["status"] != "complete" or result["coverage_scope"] != "all_embassy_binary_mains":
        return False
    if not result["expected_units"] or (
            set(result["expected_units"]) != {u["id"] for u in result["units"]}):
        return False
    for unit in result["units"]:
        bodies = [r for r in unit["roots"] if r["scope"] == "async_body"]
        if (len(bodies) != 1 or bodies[0]["status"] != "complete"
                or bodies[0]["proof_status"] not in {"proved", "refuted"}
                or bodies[0].get("conditional") or conditional_proof(bodies[0].get("proof", {}))):
            return False
    return True


def conditional_milestone_reached(result):
    if (not result.get("allow_assumptions") or result["status"] != "complete"
            or result["coverage_scope"] != "all_embassy_binary_mains"
            or not result["expected_units"]
            or set(result["expected_units"]) != {u["id"] for u in result["units"]}):
        return False
    for unit in result["units"]:
        bodies = [r for r in unit["roots"] if r["scope"] == "async_body"]
        if (len(bodies) != 1 or bodies[0]["status"] != "complete"
                or bodies[0]["proof_status"] not in {"proved", "proved_with_assumptions", "refuted"}
                or type(bodies[0].get("conditional")) is not bool):
            return False
    return True


def fresh_future_entry_milestone_reached(result):
    """Entry coverage is independent of proof completion, but requires a complete capture."""
    units, expected = result.get("units", []), result.get("expected_units", [])
    sources = result.get("source_files_before")
    if (result.get("status") != "complete" or result.get("errors")
            or result.get("coverage_scope") != "all_embassy_binary_mains"
            or not expected or len(set(expected)) != len(expected)
            or len(units) != len(expected) or {u["id"] for u in units} != set(expected)
            or not isinstance(sources, dict) or sources != result.get("source_files_after")):
        return False
    for unit in units:
        artifacts = unit.get("artifact_hashes_before")
        bodies = [root for root in unit["roots"] if root["scope"] == "async_body"]
        if (unit.get("status") != "complete" or not isinstance(artifacts, dict)
                or artifacts != unit.get("artifact_hashes_after")
                or artifacts != unit.get("artifact_hashes_at_completion")
                or len(bodies) != 1 or bodies[0].get("status") != "complete"
                or not application_body_reached(bodies[0].get("proof", {}))):
            return False
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--survey", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--analyzer", type=Path,
                        default=Path(__file__).resolve().parents[1] / "target/release/miren")
    parser.add_argument("--contracts", type=Path, help="explicit contract profile; snapshotted")
    parser.add_argument("--assumptions-profile", type=Path,
                        help="schema-1 exact unit-to-contract map; async bodies only")
    parser.add_argument("--allow-assumptions", action="store_true",
                        help="accept separately labeled conditional results with --contracts")
    parser.add_argument("--unit", action="append", help="exact unit identity; repeatable")
    parser.add_argument("--unit-timeout", type=survey.positive, default=120)
    for key in survey.LIMITS:
        parser.add_argument("--" + key.replace("_", "-"), type=survey.positive)
    args = parser.parse_args()
    try:
        return run(args)
    except (ValueError, OSError, KeyError, TypeError) as error:
        print("main survey failed: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
