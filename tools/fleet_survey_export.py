#!/usr/bin/env python3
"""Validate and compact a completed fleet survey for documentation publication."""

import argparse
from collections import Counter
from datetime import date
import hashlib
import json
from pathlib import Path
import sys

from fleet_survey import STATUSES, compare

ROOT_COLUMNS = ["unit_index", "function", "source_function_heuristic", "status", "file_index",
                "line", "column", "blocker_index"]
CATEGORIES = {"source_function_heuristic", "generated_or_other"}
CHECKPOINTS = ["artifact_hashes", "artifact_hashes_before_verify", "artifact_hashes_after_verify",
               "artifact_hashes_at_completion"]
PROVENANCE = ["fleet", "analyzer_source", "analyzer_sha256", "analyzer_binaries", "toolchain",
              "compiler", "solver", "target", "profile", "features", "limits", "scope"]


def fingerprint(value):
    data = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def tally(roots):
    return {status: sum(root["status"] == status for root in roots) for status in sorted(STATUSES)}


def validate(summary, complete=True):
    require(type(summary.get("schema_version")) is int and summary["schema_version"] == 1,
            "unsupported summary schema")
    require(summary.get("status") in {"complete", "partial"}, "invalid collection status")
    if complete:
        require(summary["status"] == "complete", "partial collections cannot be published")
        require(summary.get("errors") == [], "collection contains errors")
    units, roots = summary.get("units"), summary.get("roots")
    require(isinstance(units, list) and units, "missing units")
    require(isinstance(roots, list), "missing roots")
    unit_ids = [unit["id"] for unit in units]
    require(all(isinstance(value, str) and value for value in unit_ids), "invalid unit identity")
    require(len(unit_ids) == len(set(unit_ids)), "duplicate unit identity")
    root_ids = set()
    for root in roots:
        require(isinstance(root.get("id"), str), "missing root identity")
        require(isinstance(root.get("name"), str) and root["name"], "missing root name")
        require(root["id"] not in root_ids, "duplicate root identity")
        root_ids.add(root["id"])
        unit = root["id"].removesuffix("::" + root["name"])
        require(unit in unit_ids and root["id"] == unit + "::" + root["name"],
                "root identity does not match a unit")
        require(root.get("status") in STATUSES, "missing or invalid root status")
        require(root.get("classification") in CATEGORIES, "invalid root classification")
        source = root.get("source")
        require(isinstance(source, dict) and isinstance(source.get("file"), str),
                "invalid root source")
        require(all(type(source.get(key)) is int and source[key] > 0
                    for key in ["line", "column"]), "invalid source coordinates")
        require("first_blocker" in root and "failure" in root, "missing root collection evidence")
        blocker = root.get("first_blocker")
        require(blocker is None or isinstance(blocker, str), "invalid blocker")
        require(root["failure"] is None or root["status"] == "unknown",
                "collection failure cannot establish a proof")
        if complete:
            require(root["failure"] is None, "root has collection failure")
    counts = tally(roots)
    declared = summary.get("counts")
    require(isinstance(declared, dict)
            and all(type(value) is int and value >= 0 for value in declared.values()),
            "invalid root counts")
    require(declared == counts, "root counts do not match summary")
    classified = {category: tally([r for r in roots if r["classification"] == category])
                  for category in sorted(CATEGORIES)}
    declared_classes = summary.get("classified_counts")
    require(isinstance(declared_classes, dict)
            and all(isinstance(counts, dict)
                    and all(type(value) is int and value >= 0 for value in counts.values())
                    for counts in declared_classes.values()), "invalid classification counts")
    require(declared_classes == classified, "classification counts mismatch")
    provenance = summary.get("provenance")
    require(isinstance(provenance, dict), "missing provenance")
    require(all(key in provenance for key in PROVENANCE), "incomplete provenance")
    for key in ["compiler", "solver", "target", "profile", "toolchain"]:
        require(isinstance(provenance[key], str) and provenance[key], "invalid " + key)
    if complete:
        require(all(unit.get("status") == "complete" and "error" in unit and unit["error"] is None
                    for unit in units), "incomplete unit")
        workspaces = summary.get("workspaces")
        require(isinstance(workspaces, list) and workspaces, "missing workspace inventory")
        require(all(w.get("errors") == [] and w.get("inventory", {}).get("status") == "complete"
                    and type(w["inventory"].get("returncode")) is int
                    and w["inventory"]["returncode"] == 0 for w in workspaces),
                "failed workspace inventory")
        require(all(type(w.get("expected_units")) is int and w["expected_units"] >= 0
                    for w in workspaces), "invalid expected unit counts")
        require(sum(w["expected_units"] for w in workspaces) == len(units),
                "workspace expected unit counts mismatch")
        require(isinstance(provenance.get("source_files"), dict)
                and provenance["source_files"]
                and provenance.get("source_files_after") == provenance["source_files"],
                "source fingerprint evidence missing or changed")
        for name, digest in provenance["source_files"].items():
            require(isinstance(name, str) and isinstance(digest, str) and len(digest) == 64
                    and all(c in "0123456789abcdef" for c in digest),
                    "invalid source fingerprint")
        if "fleet_after" in provenance:
            require(provenance["fleet"] == provenance["fleet_after"], "fleet revision changed")
    return counts, classified


def artifact_provenance(units):
    evidence, coverage = {}, {}
    for unit in units:
        present = [key for key in CHECKPOINTS if key in unit]
        require(not present or (CHECKPOINTS[0] in present and CHECKPOINTS[-1] in present
                               and "artifact_hashes_after_verify" in present),
                "incomplete artifact checkpoints")
        if not present:
            continue
        original = unit[CHECKPOINTS[0]]
        require(isinstance(original, dict), "invalid artifact fingerprints")
        for name, value in original.items():
            require(isinstance(name, str), "invalid artifact path")
            require(value is None or type(value) is bool
                    or (isinstance(value, str) and len(value) == 64
                        and all(c in "0123456789abcdef" for c in value)),
                    "invalid artifact fingerprint")
        require(all(unit[key] == original for key in present), "artifact inputs changed")
        evidence[unit["id"]] = original
        coverage[unit["id"]] = present
    require(not evidence or len(evidence) == len(units), "mixed artifact checkpoint availability")
    return {"artifact_inputs_sha256": fingerprint(evidence) if evidence else None,
            "artifact_inputs_unchanged": True if evidence else None,
            "artifact_checkpoint_coverage": sorted(set(tuple(v) for v in coverage.values())),
            "artifact_unit_count": len(evidence)}


def comparison(summary, previous):
    counts, _ = validate(previous, complete=False)
    changes = compare(summary, previous)
    if summary["provenance"].get("environment") != previous["provenance"].get("environment"):
        changes["incompatible_provenance"].append("environment")
    before = {r["id"]: r for r in previous["roots"]}
    after = {r["id"]: r for r in summary["roots"]}
    transitions = Counter((before[key]["status"], after[key]["status"])
                          for key in before.keys() & after)
    classified_transitions = Counter(
        (before[key]["classification"], after[key]["classification"],
         before[key]["status"], after[key]["status"])
        for key in before.keys() & after)
    blocker_transitions = Counter(
        (before[key]["first_blocker"], after[key]["first_blocker"])
        for key in before.keys() & after
        if before[key]["status"] == after[key]["status"] == "unknown"
        and before[key]["first_blocker"] != after[key]["first_blocker"])
    return {"baseline_collection_status": previous["status"],
            "baseline_failed_units": sum(u["status"] != "complete" for u in previous["units"]),
            "baseline_counts": counts,
            "incompatible_provenance": changes["incompatible_provenance"],
            "evidence_changes": changes["evidence_changes"],
            "added_roots": len(changes["added"]), "removed_roots": len(changes["removed"]),
            "changed_roots": len(changes["changed"]),
            "previously_proved_regressions": sum(
                before[key]["status"] == "proved" and after[key]["status"] != "proved"
                for key in before.keys() & after),
            "classified_transitions": [
                {"before_classification": ca, "after_classification": cb,
                 "before": a, "after": b, "count": count}
                for (ca, cb, a, b), count in sorted(classified_transitions.items())],
            "unknown_blocker_transitions": [
                {"before": a, "after": b, "count": count}
                for (a, b), count in sorted(blocker_transitions.items(),
                                          key=lambda item: (item[0][0] or "", item[0][1] or ""))],
            "transitions": [{"before": a, "after": b, "count": count}
                            for (a, b), count in sorted(transitions.items())]}


def export(summary, measured_on, previous=None):
    require(date.fromisoformat(measured_on).isoformat() == measured_on,
            "invalid measurement date")
    counts, classified = validate(summary)
    units = sorted(summary["units"], key=lambda unit: unit["id"])
    indices = {unit["id"]: index for index, unit in enumerate(units)}
    roots = sorted(summary["roots"], key=lambda root: root["id"])
    files = sorted({root["source"]["file"] for root in roots})
    blockers = sorted({root["first_blocker"] for root in roots
                       if root["first_blocker"] is not None})
    file_index = {value: index for index, value in enumerate(files)}
    blocker_index = {value: index for index, value in enumerate(blockers)}
    rows, compact_units = [], []
    for unit in units:
        selected = [root for root in roots
                    if root["id"] == unit["id"] + "::" + root["name"]]
        functions = [r for r in selected if r["classification"] == "source_function_heuristic"]
        compact_units.append({"id": unit["id"], "collection_status": "complete",
                              "counts": tally(selected),
                              "source_function_counts": tally(functions)})
    for root in roots:
        unit = root["id"].removesuffix("::" + root["name"])
        source = root["source"]
        rows.append([indices[unit], root["name"],
                     root["classification"] == "source_function_heuristic", root["status"],
                     file_index[source["file"]], source["line"], source["column"],
                     blocker_index.get(root["first_blocker"])])
    provenance = summary["provenance"]
    result = {"schema_version": 1, "measured_on": measured_on, "collection_status": "complete",
              "provenance": {key: provenance[key] for key in PROVENANCE},
              "source_files_sha256": fingerprint(provenance["source_files"]),
              "source_inputs_unchanged": True, "build_files": provenance.get("build_files", {}),
              "counts": counts, "classified_counts": classified, "units": compact_units,
              "root_columns": ROOT_COLUMNS, "files": files, "blockers": blockers, "roots": rows,
              **artifact_provenance(units)}
    if previous is not None:
        result["comparison"] = comparison(summary, previous)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("summary", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--measured-on", required=True)
    parser.add_argument("--previous", type=Path)
    args = parser.parse_args()
    try:
        previous = json.loads(args.previous.read_text()) if args.previous else None
        result = export(json.loads(args.summary.read_text()), args.measured_on, previous)
        temporary = args.output.with_suffix(args.output.suffix + ".tmp")
        temporary.write_text(json.dumps(result, sort_keys=True, separators=(",", ":")) + "\n")
        temporary.replace(args.output)
        return 0
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as error:
        print(f"fleet survey export: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
