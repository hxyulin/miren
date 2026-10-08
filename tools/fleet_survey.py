#!/usr/bin/env python3
"""Inventory all fleet compilation units before independently checking their MIR roots."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import signal
import shutil

SCHEMA = 1
STATUSES = {"proved", "proved_with_assumptions", "refuted", "unknown"}
LIMITS = {"max_steps": 8192, "max_call_depth": 16, "max_query_bytes": 200000,
          "root_timeout_secs": 30, "solver_timeout_ms": 5000}
SKIP = {"target", ".git", ".venv", "node_modules"}


def save(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def execute(command, cwd, env, prefix, timeout):
    record = {"command": command, "cwd": str(cwd), "status": "failed"}
    try:
        process = subprocess.Popen(command, cwd=cwd, env=env, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, start_new_session=True)
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            stdout, stderr = process.communicate()
            record["status"] = "timeout"
        else:
            record.update(returncode=process.returncode,
                          status="complete" if process.returncode == 0 else "failed")
    except subprocess.TimeoutExpired as error:
        record["status"] = "timeout"
        stdout, stderr = error.stdout or b"", error.stderr or b""
    except OSError as error:
        stdout, stderr = b"", str(error).encode()
    prefix.with_suffix(".stdout").write_bytes(stdout)
    prefix.with_suffix(".stderr").write_bytes(stderr)
    save(prefix.with_suffix(".command.json"), record)
    return record, stdout


def revision(path):
    def git(*args):
        result = subprocess.run(["git", "-C", str(path), *args], capture_output=True)
        return result.stdout.decode().strip() if result.returncode == 0 else None
    status = git("status", "--porcelain", "--untracked-files=normal")
    return {"commit": git("rev-parse", "HEAD"), "dirty": bool(status), "changes": status}


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def freeze_analyzer(analyzer, output):
    destination = output / "analyzer"
    destination.mkdir()
    hashes = {}
    for source in [analyzer, analyzer.with_name("miren-rustc"),
                   analyzer.with_name("cargo-miren")]:
        if not source.is_file():
            continue
        original = digest(source)
        frozen = destination / source.name
        shutil.copy2(source, frozen)
        copied = digest(frozen)
        hashes[source.name] = {"original_sha256": original, "frozen_sha256": copied}
        if copied != original:
            raise ValueError("analyzer changed while copying: " + str(source))
    return destination / analyzer.name, hashes


def source_hashes(fleet, output):
    result = {}
    for directory, subdirs, files in os.walk(fleet):
        subdirs[:] = sorted(name for name in subdirs if name not in SKIP
                            and (Path(directory) / name).resolve() != output)
        for name in sorted(files):
            path = Path(directory) / name
            if path.is_file():
                result[str(path.relative_to(fleet))] = digest(path)
    return result


ARTIFACT_SUFFIXES = (".rmeta", ".rlib", ".so", ".dylib", ".dll", ".miren-origins.json")
MAX_INPUT_FILES = 100000


def artifact_inputs(report, cwd):
    files, directories = set(), {}
    arguments = iter(report["rustc_arguments"])
    for argument in arguments:
        option, value = None, None
        if argument in ("--extern", "-L"):
            option, value = argument, next(arguments, None)
        elif argument.startswith("--extern="):
            option, value = "--extern", argument[len("--extern="):]
        elif argument.startswith("-L") and argument != "-L":
            option, value = "-L", argument[2:].lstrip("=")
        if not value:
            continue
        if option == "--extern" and "=" in value:
            path = Path(os.path.abspath(cwd / value.split("=", 1)[1]))
            files.add(str(path))
            if path.suffix == ".rmeta":
                files.add(str(path) + ".miren-origins.json")
        elif option == "-L":
            kind, path = value.split("=", 1) if "=" in value else ("all", value)
            if kind in {"dependency", "all", "native"}:
                directory = str(Path(os.path.abspath(cwd / path)))
                mode = "artifacts" if kind == "dependency" else "build"
                if directories.get(directory) != "build":
                    directories[directory] = mode
    out = (report.get("compiler_environment") or {}).get("OUT_DIR")
    if out:
        directories[str(Path(os.path.abspath(cwd / out)))] = "build"
    return {"files": sorted(files), "directories": dict(sorted(directories.items()))}


def artifact_hashes(inputs, cache=None):
    result = {}
    paths = set(inputs["files"])
    visited_files = 0
    for directory, mode in inputs["directories"].items():
        root = Path(directory)
        result["directory:" + directory] = root.is_dir()
        if not root.is_dir():
            continue
        for parent, subdirs, files in os.walk(root):
            subdirs[:] = sorted(set(subdirs) - SKIP)
            for name in sorted(files):
                visited_files += 1
                if visited_files > MAX_INPUT_FILES:
                    raise ValueError("dependency/build traversal exceeds file limit")
                if mode == "build" or name.endswith(ARTIFACT_SUFFIXES):
                    path = str(Path(parent) / name)
                    paths.add(path)
                    if name.endswith(".rmeta"):
                        paths.add(path + ".miren-origins.json")
                if len(paths) > MAX_INPUT_FILES:
                    raise ValueError("dependency/build input inventory exceeds file limit")
    if len(paths) > MAX_INPUT_FILES:
        raise ValueError("dependency/build input inventory exceeds file limit")
    for name in sorted(paths):
        path = Path(name)
        if cache is not None and name in cache:
            result[name] = cache[name]
        else:
            result[name] = digest(path) if path.is_file() else None
            if cache is not None:
                cache[name] = result[name]
    return result


def invalidate_unit(summary, unit, reason):
    unit.update(status="failed", error=reason)
    for root in summary["roots"]:
        if root["id"].startswith(unit["id"] + "::"):
            root.update(status="unknown", failure=reason, first_blocker=reason)


def reports(data):
    result, errors = [], []
    for number, line in enumerate(data.decode(errors="replace").splitlines(), 1):
        if not line.strip():
            continue
        try:
            report = json.loads(line)
            version = report.get("schema_version")
            if type(version) is not int or version not in range(7, 10):
                raise ValueError("unsupported report schema")
            for key in ("compiler", "target", "crate_name", "panic_strategy", "mir_phase"):
                if not isinstance(report.get(key), str) or not report[key]:
                    raise ValueError("missing or invalid " + key)
            if type(report.get("overflow_checks")) is not bool:
                raise ValueError("missing or invalid overflow_checks")
            arguments = report.get("rustc_arguments")
            if not isinstance(arguments, list) or any(not isinstance(a, str) for a in arguments):
                raise ValueError("missing or invalid rustc_arguments")
            if not isinstance(report.get("functions"), list):
                raise ValueError("missing functions")
            names = [f.get("name") for f in report["functions"]]
            if len(names) != len(set(names)):
                raise ValueError("duplicate root names")
            for function in report["functions"]:
                if not isinstance(function.get("name"), str):
                    raise ValueError("missing function name")
                source = function["source"]
                if not isinstance(source["file"], str) or not isinstance(source["line"], int):
                    raise ValueError("invalid source")
                proof = function.get("proof")
                if proof is not None:
                    if not isinstance(proof, dict) or not isinstance(proof.get("status"), str):
                        raise ValueError("invalid proof")
                    if not isinstance(proof.get("obligations", []), list):
                        raise ValueError("invalid obligations")
                    if any(not isinstance(o, dict) for o in proof.get("obligations", [])):
                        raise ValueError("invalid obligation")
            result.append(report)
        except (ValueError, KeyError, TypeError, AttributeError) as error:
            errors.append(f"line {number}: {error}")
    return result, errors


def rustc_option(arguments, flag):
    for index, argument in enumerate(arguments):
        if argument == flag and index + 1 < len(arguments):
            return arguments[index + 1]
        if argument.startswith(flag + "="):
            return argument[len(flag) + 1:]
    return None


def compiler_cwd(report, workspace):
    directory = Path(report.get("working_directory") or workspace)
    return directory if directory.is_absolute() else workspace / directory


def unit_matches(unit, report, cwd):
    arguments = report.get("rustc_arguments", [])
    sources = [str((cwd / arg).resolve()) for arg in arguments if arg.endswith(".rs")]
    kinds = (rustc_option(arguments, "--crate-type") or "").split(",")
    return (report.get("crate_name") == unit["crate_name"]
            and str(Path(unit["source"]).resolve()) in sources
            and bool(set(unit["kinds"]) & set(kinds)))


def root_records(unit, inventory, verified, error, fleet, cwd):
    roots = []
    expected = [(f["name"], f["source"]) for f in inventory["functions"]]
    actual = [(f["name"], f["source"]) for f in verified.get("functions", [])]
    if actual != expected:
        error = error or "verification roots/source spans differ from inventory"
    for function in inventory["functions"]:
        name = function["name"]
        source = function["source"]
        path = (cwd / source["file"]).resolve()
        try:
            file = str(path.relative_to(fleet))
        except ValueError:
            file = str(path)
        # Names, unlike source line numbers, survive ordinary insertions before a declaration.
        identity = f'{unit["id"]}::{name}'
        classification = "generated_or_other"
        try:
            line = path.read_text().splitlines()[source["line"] - 1]
            if "{closure#" not in name and re.search(r"\bfn\s+", line):
                classification = "source_function_heuristic"
        except (OSError, IndexError, UnicodeError):
            pass
        match = next((f for f in verified.get("functions", [])
                      if f["name"] == name), {})
        proof = match.get("proof") or {}
        status = proof.get("status")
        failure = error
        if status not in STATUSES:
            failure = failure or "missing or invalid proof status"
        if status == "proved" and (proof.get("assumptions") or proof.get("trusted_calls")
                                   or proof.get("entry_assumptions")):
            failure = failure or "unconditional proof contains assumptions or trusted calls"
        if status == "proved" and any(o.get("status") != "proved"
                                      for o in proof.get("obligations", [])):
            failure = failure or "proved root contains unfinished or failed obligations"
        blockers = [o.get("detail", "unspecified") for o in proof.get("obligations", [])
                    if o.get("status") == "unknown"]
        roots.append({"id": identity, "name": name,
                      "source": {**source, "file": file}, "classification": classification,
                      "status": "unknown" if failure else status,
                      "failure": failure, "first_blocker": failure or next(iter(blockers), None)})
    return roots


def compare(current, previous):
    before = {root["id"]: root for root in previous["roots"]}
    after = {root["id"]: root for root in current["roots"]}
    configuration = ["compiler", "solver", "target", "profile", "features", "limits",
                     "toolchain", "scope"]
    incompatible = [key for key in configuration
                    if current["provenance"].get(key) != previous["provenance"].get(key)]
    return {"incompatible_provenance": incompatible,
            "evidence_changes": [key for key in ["fleet", "analyzer_source", "analyzer_sha256",
                                                "analyzer_binaries", "build_files", "source_files"]
                                 if current["provenance"].get(key)
                                 != previous["provenance"].get(key)],
            "added": sorted(after.keys() - before.keys()),
            "removed": sorted(before.keys() - after.keys()),
            "changed": [{"id": key, "before": before[key]["status"],
                         "after": after[key]["status"]} for key in sorted(before.keys() & after)
                        if (before[key]["status"], before[key].get("failure"))
                        != (after[key]["status"], after[key].get("failure"))]}


def survey(args):
    fleet = args.fleet.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    save(output / "summary.json", {"schema_version": SCHEMA, "status": "partial",
                                   "errors": ["survey preparation has not completed"]})
    original_analyzer = args.analyzer.resolve()
    analyzer, analyzer_hashes = freeze_analyzer(original_analyzer, output)
    repo = Path(__file__).resolve().parent.parent
    toolchain = re.search(r'^channel = "([^"]+)"',
                          (repo / "rust-toolchain.toml").read_text(), re.MULTILINE)[1]
    env = {key: value for key, value in os.environ.items() if not key.startswith("MIREN_")}
    env["RUSTUP_TOOLCHAIN"] = toolchain
    if args.solver:
        env["MIREN_Z3"] = str(args.solver.resolve())
    cargo = args.cargo
    summary = {"schema_version": SCHEMA, "status": "partial", "workspaces": [],
               "units": [], "roots": [], "errors": [], "provenance": {
                   "fleet": revision(fleet), "analyzer_source": revision(repo),
                   "analyzer_sha256": digest(analyzer), "analyzer_binaries": analyzer_hashes,
                   "source_files": source_hashes(fleet, output), "toolchain": toolchain,
                   "target": args.target, "profile": args.profile, "features": args.features,
                   "limits": {key: getattr(args, key) for key in LIMITS},
                   "scope": "workspace lib/bin targets; excludes host-only xtask",
                   "environment": {key: value for key, value in env.items()
                                   if key in {"RUSTUP_TOOLCHAIN", "RUSTFLAGS",
                                              "CARGO_ENCODED_RUSTFLAGS",
                                              "CARGO_BUILD_TARGET", "MIREN_Z3"}}}}
    for key, command in [("compiler", ["rustc", "-vV"]),
                         ("solver", [env.get("MIREN_Z3", "z3"), "--version"])]:
        record, data = execute(command, repo, env, output / key, args.build_timeout)
        summary["provenance"][key] = data.decode(errors="replace").strip()
        if record["status"] != "complete":
            summary["errors"].append(f"cannot identify {key}")
    save(output / "summary.json", summary)
    roots = {}
    manifests = []
    for directory, subdirs, files in os.walk(fleet):
        subdirs[:] = sorted(set(subdirs) - SKIP)
        if "Cargo.toml" in files:
            manifests.append(Path(directory) / "Cargo.toml")
    for index, manifest in enumerate(sorted(manifests)):
        command = [cargo, "metadata", "--no-deps", "--format-version=1", "--locked",
                   "--manifest-path", str(manifest)]
        record, data = execute(command, manifest.parent, env,
                               output / f"metadata-{index:03}", args.build_timeout)
        try:
            if record["status"] != "complete":
                raise ValueError("metadata command failed")
            metadata = json.loads(data)
            workspace = Path(metadata["workspace_root"]).resolve()
            workspace.relative_to(fleet)
            roots[str(workspace)] = metadata
        except (ValueError, KeyError) as error:
            summary["errors"].append(f"{manifest}: {error}")
    summary["provenance"]["build_files"] = {}
    for manifest in manifests:
        for path in (manifest, manifest.with_name("Cargo.lock"),
                     manifest.parent / ".cargo/config.toml", manifest.parent / ".cargo/config"):
            if path.is_file():
                summary["provenance"]["build_files"][str(path.relative_to(fleet))] = digest(path)
    pending = []
    # Finish every inventory before any verification process starts.
    for index, (workspace_path, metadata) in enumerate(sorted(roots.items())):
        workspace = Path(workspace_path)
        name = str(workspace.relative_to(fleet))
        members = [p for p in metadata["packages"] if p["id"] in metadata["workspace_members"]]
        units = []
        build_scripts = []
        for package in members:
            if package["name"] == "xtask":
                continue
            for target in package["targets"]:
                if "custom-build" in target["kind"]:
                    build_scripts.append({"crate_name": "build_script_build",
                                          "source": str(Path(target["src_path"]).resolve()),
                                          "kinds": ["bin"]})
                if not set(target["kind"]) & {"lib", "bin", "rlib", "staticlib", "cdylib"}:
                    continue
                kind = ",".join(sorted(target["kind"]))
                identifier = f'{name}/{package["name"]}/{kind}/{target["name"]}'
                units.append({"id": identifier, "crate_name": target["name"].replace("-", "_"),
                              "source": str(Path(target["src_path"]).resolve()),
                              "kinds": target["crate_types"], "status": "missing_inventory"})
        prefix = output / f"inventory-{index:03}"
        jsonl = prefix.with_suffix(".jsonl")
        command = [str(analyzer), "inventory", "--no-config", "--quiet", "--jsonl", str(jsonl),
                   "--workspace", "--lib", "--bins", "--target", args.target,
                   "--profile", args.profile, "--locked"]
        if any(p["name"] == "xtask" for p in members):
            command += ["--exclude", "xtask"]
        if args.features:
            command += ["--features", args.features]
        print(f"Inventory {name}: {len(units)} expected units", file=sys.stderr, flush=True)
        record, _ = execute(command, workspace, env, prefix, args.build_timeout)
        inventories, errors = reports(jsonl.read_bytes() if jsonl.exists() else b"")
        item = {"id": name, "inventory": record, "errors": errors, "expected_units": len(units)}
        summary["workspaces"].append(item)
        for unit in units:
            matched = [r for r in inventories if unit_matches(unit, r, compiler_cwd(r, workspace))]
            summary["units"].append(unit)
            if len(matched) != 1 or errors:
                unit["error"] = "missing, duplicate or malformed inventory"
                continue
            unit["status"] = "inventoried"
            inventory_cwd = compiler_cwd(matched[0], workspace)
            unit["artifact_inputs"] = artifact_inputs(matched[0], inventory_cwd)
            try:
                unit["artifact_hashes"] = artifact_hashes(unit["artifact_inputs"])
            except (OSError, ValueError) as error:
                unit.update(status="failed", error="cannot fingerprint artifacts: " + str(error))
                continue
            pending.append((unit, matched[0], workspace))
        excluded = [r for r in inventories
                    if r.get("target") != args.target
                    and any(unit_matches(u, r, compiler_cwd(r, workspace)) for u in build_scripts)]
        item["excluded_host_build_scripts"] = [
            {"crate_name": r["crate_name"], "arguments": r["rustc_arguments"]} for r in excluded]
        unmatched = [r.get("crate_name") for r in inventories
                     if r not in excluded
                     and not any(unit_matches(u, r, compiler_cwd(r, workspace)) for u in units)]
        if any(r.get("target") != args.target for r in inventories if r not in excluded):
            item["errors"].append("inventory target differs from requested target")
        if unmatched:
            item["errors"].append(f"unexpected inventory units: {unmatched}")
        save(output / "summary.json", summary)

    def verify(item):
        unit, inventory, workspace = item
        prefix = output / ("verify-" + hashlib.sha256(unit["id"].encode()).hexdigest()[:16])
        jsonl = prefix.with_suffix(".jsonl")
        cwd = compiler_cwd(inventory, workspace)
        recorded = inventory.get("compiler_environment")
        replay_env = {key: value for key, value in env.items()
                      if not key.startswith(("CARGO_", "DEP_")) and key != "OUT_DIR"}
        if recorded is not None:
            replay_env.update(recorded)
        else:
            replay_env["CARGO_CRATE_NAME"] = inventory["crate_name"]
        for key in list(replay_env):
            if key.startswith("MIREN_") and key != "MIREN_Z3":
                del replay_env[key]
        command = [str(analyzer), "rustc", "--verify", "--quiet", "--jsonl", str(jsonl)]
        for key in LIMITS:
            command += ["--" + key.replace("_", "-"), str(getattr(args, key))]
        command += ["--", *inventory["rustc_arguments"]]
        integrity_error = None
        try:
            before = artifact_hashes(unit["artifact_inputs"])
            if before != unit["artifact_hashes"]:
                integrity_error = "dependency/build inputs changed before verification"
        except (OSError, ValueError) as error:
            integrity_error = "cannot fingerprint artifacts: " + str(error)
        record, _ = execute(command, cwd, replay_env, prefix, args.unit_timeout)
        try:
            after = artifact_hashes(unit["artifact_inputs"])
            unit["artifact_hashes_after_verify"] = after
            if after != unit["artifact_hashes"]:
                integrity_error = "dependency/build inputs changed during verification"
        except (OSError, ValueError) as error:
            integrity_error = "cannot fingerprint artifacts: " + str(error)
        verified, errors = reports(jsonl.read_bytes() if jsonl.exists() else b"")
        failure = integrity_error
        if record.get("returncode") not in (0, 1) or record["status"] == "timeout":
            failure = "verification crashed, failed to launch or timed out"
        if errors or len(verified) != 1:
            failure = "missing, malformed or duplicate verification report"
        report = verified[0] if len(verified) == 1 else {}
        if report and not unit_matches(unit, report, cwd):
            failure = "verification compilation unit mismatch"
        for key in ("target", "compiler", "panic_strategy", "overflow_checks", "mir_phase"):
            if report and report.get(key) != inventory.get(key):
                failure = "verification build configuration mismatch: " + key
        if (record.get("returncode") == 1 and report.get("functions")
                and all((f.get("proof") or {}).get("status") == "proved"
                        for f in report["functions"])):
            failure = "failed verification process contains only proved roots"
        if report.get("analysis_limits") not in (
                None, {key: getattr(args, key) for key in LIMITS}):
            failure = "verification analysis limits mismatch"
        if recorded is None or not inventory.get("working_directory"):
            failure = failure or "inventory lacks captured compiler environment"
        unit["verification"] = record
        checked = root_records(unit, inventory, report, failure, fleet, cwd)
        failure = failure or next((r["failure"] for r in checked if r["failure"]), None)
        unit["status"] = "complete" if not failure else "failed"
        unit["error"] = failure
        print(f'Verified {unit["id"]}: {unit["status"]}', file=sys.stderr, flush=True)
        return checked

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(verify, item) for item in pending]
        for future in as_completed(futures):
            summary["roots"].extend(future.result())
            summary["roots"].sort(key=lambda root: root["id"])
            save(output / "summary.json", summary)
    final_artifact_cache = {}
    for unit in summary["units"]:
        if "artifact_hashes" not in unit:
            continue
        try:
            final_inputs = artifact_hashes(unit["artifact_inputs"], final_artifact_cache)
            unit["artifact_hashes_at_completion"] = final_inputs
            if final_inputs != unit["artifact_hashes"]:
                invalidate_unit(summary, unit, "dependency/build inputs changed before completion")
        except (OSError, ValueError) as error:
            invalidate_unit(summary, unit, "cannot fingerprint artifacts: " + str(error))
    final_hashes = source_hashes(fleet, output)
    if final_hashes != summary["provenance"]["source_files"]:
        summary["errors"].append("fleet source/build contents changed during the survey")
        for root in summary["roots"]:
            root.update(status="unknown", failure="source changed during survey",
                        first_blocker="source changed during survey")
        for unit in summary["units"]:
            unit.update(status="failed", error="source changed during survey")
    summary["provenance"]["source_files_after"] = final_hashes
    final_source = revision(fleet)
    if final_source != summary["provenance"]["fleet"]:
        summary["errors"].append("fleet revision or dirty state changed during the survey")
    summary["provenance"]["fleet_after"] = final_source
    summary["status"] = "complete" if (
        summary["units"] and not summary["errors"]
        and all(u["status"] == "complete" for u in summary["units"])
        and all(w["inventory"]["status"] == "complete" and not w["errors"]
                for w in summary["workspaces"])) else "partial"
    summary["first_blockers"] = {}
    for root in summary["roots"]:
        if root["status"] == "unknown":
            reason = root["first_blocker"] or "unspecified"
            summary["first_blockers"][reason] = summary["first_blockers"].get(reason, 0) + 1
    summary["classified_counts"] = {
        category: {status: sum(r["status"] == status and r["classification"] == category
                               for r in summary["roots"]) for status in sorted(STATUSES)}
        for category in ["source_function_heuristic", "generated_or_other"]}
    summary["counts"] = {status: sum(r["status"] == status for r in summary["roots"])
                         for status in sorted(STATUSES)}
    if args.previous:
        summary["diff"] = compare(summary, json.loads(args.previous.read_text()))
    save(output / "summary.json", summary)
    return 0 if summary["status"] == "complete" else 1


def positive(value):
    number = int(value)
    if number <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return number


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fleet", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--analyzer", type=Path,
                        default=Path(__file__).resolve().parent.parent / "target/release/miren")
    parser.add_argument("--cargo", default="cargo")
    parser.add_argument("--solver", type=Path)
    parser.add_argument("--target", default="thumbv7em-none-eabihf")
    parser.add_argument("--profile", default="dev")
    parser.add_argument("--features", default="")
    parser.add_argument("--jobs", type=positive, default=4)
    parser.add_argument("--build-timeout", type=positive, default=600)
    parser.add_argument("--unit-timeout", type=positive, default=1800)
    parser.add_argument("--previous", type=Path)
    for key, default in LIMITS.items():
        parser.add_argument("--" + key.replace("_", "-"), type=positive, default=default)
    args = parser.parse_args()
    try:
        return survey(args)
    except (OSError, ValueError, KeyError) as error:
        print(f"fleet survey: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
