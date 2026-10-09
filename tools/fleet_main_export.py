#!/usr/bin/env python3
"""Validate and compact complete strict and optional conditional Embassy main captures."""

import argparse
from collections import Counter
import json
from pathlib import Path
import sys

import fleet_main_survey as main_survey
import fleet_survey as survey
import fleet_survey_export as base_export

EXPECTED_MAIN_COUNT = 12
ARTIFACT_CHECKPOINTS = ("artifact_hashes_before", "artifact_hashes_after",
                        "artifact_hashes_at_completion")
MAX_OUTPUT_BYTES = 500 * 1024


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(value):
    return (isinstance(value, str) and len(value) == 64
            and all(char in "0123456789abcdef" for char in value))


def hashes(value, optional=False):
    require(isinstance(value, dict) and value, "missing fingerprint map")
    for name, digest in value.items():
        require(isinstance(name, str) and name, "invalid fingerprint identity")
        require(sha256(digest) or (optional and (digest is None or type(digest) is bool)),
                "invalid fingerprint")


def validate(summary, conditional=False):
    require(type(summary.get("schema_version")) is int and summary["schema_version"] == 1,
            "unsupported main summary schema")
    require(summary.get("status") == "complete" and summary.get("errors") == []
            and summary.get("missing_units") == [], "incomplete main collection")
    require(summary.get("coverage_scope") == "all_embassy_binary_mains",
            "subset collections cannot be published as full main coverage")
    expected, selected, units = (summary.get(key) for key in
                                 ("expected_units", "selected_units", "units"))
    require(isinstance(expected, list) and len(expected) == EXPECTED_MAIN_COUNT
            and all(isinstance(value, str) and value for value in expected)
            and len(set(expected)) == len(expected), "invalid expected main identities")
    require(isinstance(selected, list) and len(selected) == len(expected)
            and set(selected) == set(expected), "selected main identities mismatch")
    require(isinstance(units, list) and len(units) == len(expected)
            and {unit["id"] for unit in units} == set(expected), "main unit coverage mismatch")
    require(summary.get("scopes") == {
        key: {"entry": value[0], "async_entry": value[1], "scope": value[2]}
        for key, value in main_survey.SCOPES.items()}, "main proof scope mismatch")
    require(type(summary.get("allow_assumptions")) is bool
            and summary["allow_assumptions"] is conditional
            and summary.get("contracts_scope") == "async_body_only", "policy scope mismatch")
    limits = summary.get("limits")
    require(isinstance(limits, dict) and set(limits) == set(survey.LIMITS)
            and all(type(value) is int and value > 0 for value in limits.values()),
            "invalid analysis limits")
    hashes(summary.get("source_files_before"))
    require(summary["source_files_before"] == summary.get("source_files_after"),
            "source inputs changed")
    binaries = summary.get("analyzer_binaries")
    require(isinstance(binaries, dict) and "miren" in binaries
            and set(binaries) <= {"miren", "miren-rustc", "cargo-miren"},
            "missing analyzer identity")
    for value in binaries.values():
        require(isinstance(value, dict) and sha256(value.get("original_sha256"))
                and value.get("frozen_sha256") == value["original_sha256"],
                "analyzer changed during freezing")
    revision = summary.get("analyzer_source")
    require(isinstance(revision, dict) and isinstance(revision.get("commit"), str)
            and type(revision.get("dirty")) is bool, "missing analyzer source identity")
    require(isinstance(summary.get("survey"), str) and sha256(summary.get("survey_sha256")),
            "missing captured survey identity")
    if not conditional:
        require(summary.get("contract_config") is None
                and summary.get("contract_profiles") == {} and "contracts" not in summary,
                "strict capture has a policy")
    else:
        policy = summary.get("contracts")
        require(isinstance(policy, dict) and sha256(policy.get("sha256"))
                and policy.get("source_sha256_at_completion") == policy["sha256"]
                and policy.get("snapshot_sha256_at_completion") == policy["sha256"],
                "missing or changed policy snapshot")
    counts = {scope: Counter() for scope in main_survey.SCOPES}
    for unit in units:
        require(unit.get("status") == "complete" and not unit.get("error"),
                "incomplete main unit")
        roots = unit.get("roots")
        require(isinstance(roots, list) and len(roots) == len(main_survey.SCOPES)
                and {root["scope"] for root in roots} == set(main_survey.SCOPES),
                "missing or duplicate root scopes")
        original = unit.get(ARTIFACT_CHECKPOINTS[0])
        hashes(original, optional=True)
        require(all(unit.get(key) == original for key in ARTIFACT_CHECKPOINTS),
                "artifact inputs changed or checkpoint missing")
        config = unit.get("contract_config")
        if config is not None:
            require(conditional, "strict unit has contracts")
            main_survey.normalized_contract_config(config)
            require(sha256(unit.get("contract_sha256"))
                    and unit.get("contract_sha256_at_completion") == unit["contract_sha256"],
                    "unit policy snapshot changed")
        else:
            require(unit.get("contract_snapshot") is None and unit.get("contract_sha256") is None,
                    "unit policy snapshot has no configuration")
        for root in roots:
            scope = root["scope"]
            require(root.get("status") == "complete" and root.get("failure") is None,
                    "failed root collection")
            require(root.get("name") == main_survey.SCOPES[scope][0], "root name mismatch")
            proof = root.get("proof")
            require(isinstance(proof, dict) and root.get("proof_status") in survey.STATUSES
                    and root["proof_status"] == proof.get("status")
                    and proof.get("async_entry") is main_survey.SCOPES[scope][1],
                    "missing or inconsistent root proof")
            actual_conditional = main_survey.conditional_proof(proof)
            if "analysis_domain" in root:
                require(root["analysis_domain"] == main_survey.SCOPES[scope][2]
                        and root.get("boot_reachability") == "unverified"
                        and root.get("counterexample_evidence") ==
                            main_survey.counterexample_evidence(proof),
                        "counterexample evidence/domain label mismatch")
            require(type(root.get("conditional")) is bool
                    and root["conditional"] is actual_conditional,
                    "conditional label mismatch")
            require(not actual_conditional or (conditional and scope == "async_body"),
                    "assumptions escaped the conditional body scope")
            require(isinstance(proof.get("obligations"), list), "missing obligations")
            require(all(obligation.get("status") in {"proved", "refuted", "unknown"}
                        for obligation in proof["obligations"]), "invalid obligation status")
            status = proof["status"]
            if status in {"proved", "proved_with_assumptions"}:
                require(all(o["status"] == "proved" for o in proof["obligations"]),
                        "unfinished proof cannot establish success")
            elif status == "refuted":
                require(any(o["status"] == "refuted" for o in proof["obligations"]),
                        "refuted proof has no failed obligation")
            else:
                require(any(o["status"] == "unknown" for o in proof["obligations"]),
                        "unknown proof has no recorded blocker")
            counts[scope][status] += 1
    counts = {scope: {status: counts[scope][status] for status in sorted(survey.STATUSES)}
              for scope in main_survey.SCOPES}
    declared = summary.get("counts")
    require(isinstance(declared, dict) and set(declared) == set(counts)
            and all(isinstance(row, dict) and all(type(value) is int and value >= 0
                    for value in row.values()) for row in declared.values())
            and declared == counts, "main counts mismatch")
    for key, predicate in (("milestone_reached", main_survey.milestone_reached),
                           ("conditional_milestone_reached",
                            main_survey.conditional_milestone_reached)):
        require(type(summary.get(key)) is bool and summary[key] is predicate(summary),
                "unsupported milestone claim")
    return counts


def local_record(path, value):
    require(isinstance(value, str) and value, "missing captured record path")
    return path.parent / Path(value).name


def capture(path, conditional=False):
    summary = json.loads(path.read_text())
    counts = validate(summary, conditional)
    for name, identity in summary["analyzer_binaries"].items():
        require(survey.digest(path.parent / "analyzer" / name) == identity["frozen_sha256"],
                "frozen analyzer bytes changed")
    base_path = Path(summary["survey"])
    require(survey.digest(base_path) == summary["survey_sha256"], "captured survey changed")
    base = json.loads(base_path.read_text())
    base_export.validate(base)
    inventories, excluded = main_survey.inventories(base, base_path.parent)
    expected = {unit["id"] for unit, _, _ in inventories}
    require(expected == set(summary["expected_units"])
            and excluded == summary.get("excluded_binaries"), "captured main inventory mismatch")
    require(base["provenance"]["source_files_after"] == summary["source_files_before"],
            "source inputs changed since survey")
    by_id = {unit["id"]: (unit, inventory, cwd) for unit, inventory, cwd in inventories}
    policies = summary.get("contract_profiles")
    require(isinstance(policies, dict) and set(policies) <= expected,
            "invalid unit policy selectors")
    common = summary.get("contract_config")
    if conditional:
        snapshot = local_record(path, summary["contracts"].get("snapshot"))
        require(survey.digest(snapshot) == summary["contracts"]["sha256"],
                "policy snapshot bytes changed")
        raw = json.loads(snapshot.read_text())
        if common is not None:
            require(main_survey.normalized_contract_config(raw) == common and policies == {},
                    "common policy snapshot mismatch")
        else:
            require(isinstance(raw, dict) and set(raw) == {"schema_version", "units"}
                    and type(raw["schema_version"]) is int and raw["schema_version"] == 1
                    and isinstance(raw["units"], dict), "invalid policy profile snapshot")
            require({identity: main_survey.normalized_contract_config(config)
                     for identity, config in raw["units"].items()} == policies,
                    "unit profile snapshot mismatch")
    compact_units = []
    for unit in sorted(summary["units"], key=lambda value: value["id"]):
        original, inventory, cwd = by_id[unit["id"]]
        require(unit["artifact_hashes_before"] == original.get("artifact_hashes_at_completion"),
                "artifact inputs changed since survey")
        config = common if common is not None else policies.get(unit["id"])
        require(config == unit.get("contract_config"), "unit policy configuration mismatch")
        if config is not None:
            snapshot = local_record(path, unit.get("contract_snapshot"))
            require(survey.digest(snapshot) == unit["contract_sha256"]
                    and json.loads(snapshot.read_text()) == config, "unit policy bytes changed")
        roots = []
        for root in sorted(unit["roots"], key=lambda value: value["scope"]):
            report_path = local_record(path, root.get("report"))
            reports, errors = survey.reports(report_path.read_bytes())
            require(not errors and len(reports) == 1, "malformed captured proof report")
            invocation = root.get("verification")
            require(isinstance(invocation, dict)
                    and invocation.get("status") in {"complete", "failed"}
                    and type(invocation.get("returncode")) is int,
                    "missing compiler completion evidence")
            use_config = config if root["scope"] == "async_body" else None
            proof = main_survey.checked_proof(original, inventory, reports[0], cwd,
                root["scope"], summary["limits"], invocation["returncode"], use_config,
                use_config is not None)
            require(proof == root["proof"], "summary proof does not match captured report")
            function = next(f for f in reports[0]["functions"] if f.get("proof") is not None)
            roots.append(compact_root(root, function["source"], survey.digest(report_path)))
        compact_units.append({"id": unit["id"], "roots": roots,
                              "contract_config": config,
                              "contract_snapshot_sha256": unit.get("contract_sha256")})
    artifacts = {unit["id"]: unit["artifact_hashes_before"] for unit in summary["units"]}
    return {"collection_status": "complete", "coverage_scope": summary["coverage_scope"],
            "summary_sha256": survey.digest(path), "survey_sha256": summary["survey_sha256"],
            "analyzer_source": summary["analyzer_source"],
            "analyzer_binaries": summary["analyzer_binaries"], "limits": summary["limits"],
            "counts": counts, "allow_assumptions": conditional,
            "milestone_reached": summary["milestone_reached"],
            "conditional_milestone_reached": summary["conditional_milestone_reached"],
            "contracts": summary.get("contracts"), "units": compact_units,
            "source_files_sha256": base_export.fingerprint(summary["source_files_before"]),
            "source_inputs_unchanged": True,
            "artifact_inputs_sha256": base_export.fingerprint(artifacts),
            "artifact_inputs_unchanged": True,
            "artifact_checkpoint_coverage": list(ARTIFACT_CHECKPOINTS),
            "artifact_unit_count": len(artifacts),
            "captured_provenance": {key: base["provenance"][key]
                                    for key in base_export.PROVENANCE},
            "source_files": summary["source_files_before"]}


def compact_root(root, source, report_digest):
    proof = root["proof"]
    blockers = []
    for obligation in proof["obligations"]:
        if obligation["status"] == "proved":
            continue
        compact = {key: obligation.get(key) for key in
                   ("function", "source", "kind", "detail", "status", "call_chain",
                    "abstraction_reasons")}
        compact["counterexample_sha256"] = (base_export.fingerprint(obligation["model"])
                                             if obligation.get("model") is not None else None)
        compact["query_sha256"] = (base_export.fingerprint(obligation["query"])
                                   if obligation.get("query") is not None else None)
        blockers.append(compact)
    return {"scope": root["scope"], "name": root["name"], "source": source,
            "proof_status": root["proof_status"], "conditional": root["conditional"],
            "analysis_domain": main_survey.SCOPES[root["scope"]][2],
            "boot_reachability": "unverified",
            "counterexample_evidence": main_survey.counterexample_evidence(proof),
            "report_sha256": report_digest, "assumptions": proof.get("assumptions", []),
            "entry_assumptions": proof.get("entry_assumptions", []),
            "trusted_calls": proof.get("trusted_calls", []),
            "matched_contracts": proof.get("matched_contracts", []),
            "analyzed_body_count": len(proof.get("analyzed_bodies", [])), "blockers": blockers}


def export(strict_path, conditional_path=None):
    strict = capture(strict_path)
    conditional = capture(conditional_path, True) if conditional_path else None
    if conditional is not None:
        for key in ("survey_sha256", "analyzer_binaries", "limits", "source_files_sha256",
                    "artifact_inputs_sha256"):
            require(strict[key] == conditional[key], "strict/conditional identity mismatch: " + key)
        require(strict["analyzer_source"]["commit"] == conditional["analyzer_source"]["commit"],
                "strict/conditional analyzer source revision mismatch")
    source_files = strict.pop("source_files")
    if conditional is not None:
        conditional.pop("source_files")
    result = {"schema_version": 1, "expected_main_count": EXPECTED_MAIN_COUNT,
              "scopes": {key: {"entry": value[0], "async_entry": value[1], "scope": value[2]}
                         for key, value in main_survey.SCOPES.items()},
              "source_files": source_files, "strict": strict, "conditional": conditional,
              "export_tools_sha256": {name: survey.digest(Path(__file__).with_name(name))
                  for name in ("fleet_main_export.py", "fleet_main_survey.py",
                               "fleet_survey_export.py", "fleet_survey.py")}}
    require(len(encoded(result)) <= MAX_OUTPUT_BYTES, "compact main evidence exceeds 500 KiB")
    return result


def encoded(result):
    return (json.dumps(result, sort_keys=True, separators=(",", ":")) + "\n").encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--strict", required=True, type=Path)
    parser.add_argument("--conditional", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    try:
        result = export(args.strict, args.conditional)
        temporary = args.output.with_suffix(args.output.suffix + ".tmp")
        temporary.write_bytes(encoded(result))
        temporary.replace(args.output)
        return 0
    except (OSError, ValueError, KeyError, TypeError, AttributeError, StopIteration) as error:
        print(f"fleet main export: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
