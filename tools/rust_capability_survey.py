#!/usr/bin/env python3
"""Check the declared Rust capability baseline without a firmware checkout."""

import argparse
from collections import Counter
import json
import os
from pathlib import Path
import sys

from fleet_survey import digest, execute, freeze_analyzer, revision, save


STATUSES = {"proved", "refuted", "unknown"}
UNKNOWN_CATEGORIES = {"semantics", "missing_compiler_evidence", "solver", "resource_limit",
                      "external_environment", "unclassified"}


def load_manifest(path, repository):
    manifest = json.loads(path.read_text())
    if (not isinstance(manifest, dict) or type(manifest.get("schema_version")) is not int
            or manifest.get("schema_version") != 1
            or set(manifest) != {"schema_version", "fixture", "cases"}
            or not isinstance(manifest.get("fixture"), str)):
        raise ValueError("capability manifest requires schema 1")
    fixture = (repository / manifest["fixture"]).resolve()
    if not fixture.is_relative_to(repository.resolve()) or not fixture.is_file():
        raise ValueError("fixture must be a repository file")
    cases = manifest.get("cases")
    if not isinstance(cases, list) or not cases:
        raise ValueError("manifest needs nonempty cases")
    entries = set()
    for case in cases:
        if (not isinstance(case, dict) or not isinstance(case.get("entry"), str)
                or not case["entry"] or case["entry"] in entries
                or not isinstance(case.get("expected"), str)
                or case.get("expected") not in STATUSES
                or not isinstance(case.get("family"), str) or not case["family"]):
            raise ValueError("invalid or duplicate capability case")
        if set(case) - {"entry", "family", "expected", "unknown_reason", "unknown_category"}:
            raise ValueError("unrecognized capability case field")
        reason = case.get("unknown_reason")
        if case["expected"] == "unknown" and (not isinstance(reason, str) or not reason):
            raise ValueError("UNKNOWN capability needs its documented frontier")
        if case["expected"] != "unknown" and reason is not None:
            raise ValueError("supported capability cannot declare an UNKNOWN frontier")
        if "unknown_category" in case:
            category = case["unknown_category"]
            if (case["expected"] != "unknown" or not isinstance(category, str)
                    or category not in UNKNOWN_CATEGORIES):
                raise ValueError("UNKNOWN category must name a supported producer cause")
        entries.add(case["entry"])
    return manifest, fixture


def check_report(report, cases):
    """Demand actual proofs, exact roots, strict premises and retained failure evidence."""
    errors = []
    results = []
    if not isinstance(report, dict) or not isinstance(report.get("functions"), list):
        return [], ["invalid report shape"]
    functions = report.get("functions", [])
    if any(not isinstance(f, dict) or not isinstance(f.get("name"), str) for f in functions):
        return [], ["invalid function shape"]
    for case in cases:
        matches = [f for f in functions if f.get("name") == case["entry"]]
        if len(matches) != 1 or not isinstance(matches[0].get("proof"), dict):
            errors.append(case["entry"] + ": missing or duplicate verified root")
            continue
        proof = matches[0]["proof"]
        status = proof.get("status")
        if not isinstance(status, str) or status not in STATUSES:
            errors.append(case["entry"] + ": invalid proof status")
            continue
        obligations = proof.get("obligations")
        if (not isinstance(obligations, list)
                or any(not isinstance(o, dict) or not isinstance(o.get("detail"), str)
                       for o in obligations)):
            errors.append(case["entry"] + ": invalid obligation shape")
            continue
        if status != case["expected"]:
            errors.append(f"{case['entry']}: expected {case['expected']}, got {status}")
        # entry_assumptions is explicitly omitted by the DTO when empty.
        if (any(proof.get(field) != [] for field in ["assumptions", "trusted_calls"])
                or proof.get("entry_assumptions", []) != []):
            errors.append(case["entry"] + ": strict capability needs explicit empty premises")
        if status == "refuted" and not any(
                o.get("status") == "refuted"
                and isinstance(o.get("query"), str) and o["query"]
                and isinstance(o.get("model"), str) and o["model"]
                for o in obligations):
            errors.append(case["entry"] + ": missing counterexample query/model")
        if status == "unknown" and not any(
                o.get("status") == "unknown"
                and case.get("unknown_reason", "") in o.get("detail", "")
                and ("unknown_category" not in case
                     or o.get("unknown_category") == case["unknown_category"])
                for o in obligations):
            errors.append(case["entry"] + ": missing expected UNKNOWN frontier")
        results.append({"entry": case["entry"], "family": case["family"],
                        "expected": case["expected"], "actual": status,
                        "gaps": [{"category": o.get("unknown_category", "unclassified"),
                                  "detail": o.get("detail")}
                                 for o in obligations if o.get("status") == "unknown"]})
    selected = [f.get("name") for f in functions if f.get("proof") is not None]
    if sorted(selected) != sorted(c["entry"] for c in cases):
        errors.append("selected root set differs from capability manifest")
    return results, errors


def check_configuration(report, arguments, target, compiler):
    captured = report.get("rustc_arguments")
    if (report.get("crate_name") != "rust_capabilities"
            or report.get("overflow_checks") is not True
            or report.get("panic_strategy") != "abort"
            or report.get("target") != target
            or report.get("compiler") != compiler
            or not isinstance(captured, list)
            or captured[:len(arguments)] != arguments):
        raise ValueError("report compiler configuration differs from requested run")


def run(args):
    repository = Path(__file__).resolve().parent.parent
    manifest_path = args.manifest.resolve()
    manifest, fixture = load_manifest(manifest_path, repository)
    source_hashes = {str(p): digest(p) for p in [manifest_path, fixture]}
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    analyzer, binaries = freeze_analyzer(args.analyzer.resolve(), output)
    env = {k: v for k, v in os.environ.items() if not k.startswith("MIREN_")}
    if args.solver:
        env["MIREN_Z3"] = str(args.solver.resolve())
    summary = {"schema_version": 1, "status": "partial", "source": revision(repository),
               "input_hashes": source_hashes, "analyzer_binaries": binaries,
               "scope": "declared_rust_capabilities", "runs": [], "errors": []}
    save(output / "summary.json", summary)
    record, stdout = execute(["rustc", "-vV"], repository, env, output / "compiler", 30)
    version = stdout.decode().splitlines()
    host = next((line.removeprefix("host: ") for line in version
                 if line.startswith("host: ")), None)
    if record.get("returncode") != 0 or not version or host is None:
        raise ValueError("cannot establish pinned compiler host/version")
    summary["compiler"] = {"version": version[0], "host": host}
    for target in [None, "thumbv7em-none-eabihf"]:
        for optimized in [False, True]:
            name = (target or "host") + ("-optimized" if optimized else "-debug")
            directory = output / name
            directory.mkdir()
            command = [str(analyzer), "--verify", "--json", "--quiet"]
            for case in manifest["cases"]:
                command.extend(["--entry", case["entry"]])
            command.extend(["--", "--crate-type=lib", "--crate-name=rust_capabilities",
                            "--edition=2024", str(fixture), "--out-dir", str(directory),
                            "-Cpanic=abort", "-Coverflow-checks=yes"])
            if target:
                command.extend(["--target", target])
            if optimized:
                command.append("-Copt-level=2")
            arguments = command[command.index("--") + 1:]
            record, stdout = execute(command, repository, env, directory / "analysis",
                                     args.timeout)
            try:
                if record["status"] == "timeout" or "returncode" not in record:
                    raise ValueError("analyzer invocation did not finish")
                report = json.loads(stdout)
                if not isinstance(report, dict):
                    raise ValueError("invalid report object")
                if report.get("contract_config") is not None:
                    raise ValueError("unexpected contract configuration")
                check_configuration(report, arguments, target or host, version[0])
                results, errors = check_report(report, manifest["cases"])
                # REFUTED/UNKNOWN selected roots intentionally produce a nonzero CLI exit.
                expected_exit = 0 if all(c["expected"] == "proved"
                                         for c in manifest["cases"]) else 1
                if record["returncode"] != expected_exit:
                    errors.append(f"unexpected analyzer exit: {record['returncode']}")
            except (ValueError, TypeError, KeyError) as error:
                results, errors = [], [str(error)]
            summary["runs"].append({"configuration": name, "results": results,
                                    "errors": errors})
            summary["errors"].extend(name + ": " + e for e in errors)
            save(output / "summary.json", summary)
    for path, before in source_hashes.items():
        if digest(Path(path)) != before:
            summary["errors"].append("capability input changed: " + path)
    summary["analyzer_unchanged"] = all(
        digest(output / "analyzer" / name) == record["frozen_sha256"]
        for name, record in binaries.items())
    if not summary["analyzer_unchanged"]:
        summary["errors"].append("frozen analyzer changed during collection")
    summary["counts"] = dict(Counter(r["actual"] for run in summary["runs"]
                                     for r in run["results"]))
    summary["status"] = "complete" if not summary["errors"] else "partial"
    save(output / "summary.json", summary)
    print(json.dumps({"status": summary["status"], "counts": summary["counts"],
                      "errors": summary["errors"]}))
    return 0 if summary["status"] == "complete" else 1


def main():
    repository = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path,
                        default=repository / "tests/capabilities/rust.json")
    parser.add_argument("--analyzer", type=Path, default=repository / "target/release/miren")
    parser.add_argument("--solver", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=180)
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("timeout must be positive")
    try:
        return run(args)
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
