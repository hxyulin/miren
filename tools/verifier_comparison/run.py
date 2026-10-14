#!/usr/bin/env python3
"""Collect raw, bounded verifier runs over identical small Rust case bodies."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import signal
import subprocess
import time


CASES = {
    "guarded_index": ("safe", ["[u8; 4]", "u8"]),
    "unguarded_index": ("panic", ["[u8; 4]", "u8"]),
    "checked_add": ("safe", ["u8", "u8"]),
    "overflow_add": ("panic", ["u8", "u8"]),
    "nonzero_match": ("safe", ["u8"]),
    "nonzero_unwrap": ("panic", ["u8"]),
    "mutable_preserve": ("safe", ["[u8; 4]", "u8", "u8"]),
    "mutable_wrong_claim": ("panic", ["[u8; 4]", "u8", "u8"]),
    "bounded_iterator": ("safe", ["[u8; 4]"]),
    "trait_dispatch": ("safe", ["bool", "u8"]),
    "vec_roundtrip": ("safe", ["[u8; 4]"]),
    "vec_wrong_length": ("panic", ["[u8; 4]"]),
    "async_two_polls": ("safe", ["u8"]),
    "async_late_panic": ("panic", ["u8"]),
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def collect(command, directory, timeout, environment):
    started = time.monotonic()
    with (directory / "stdout").open("wb") as stdout:
        with (directory / "stderr").open("wb") as stderr:
            process = subprocess.Popen(
                command, cwd=directory, env=environment, stdout=stdout, stderr=stderr,
                start_new_session=True,
            )
            timed_out = False
            try:
                process.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
    return {
        "command": command,
        "returncode": process.returncode,
        "timed_out": timed_out,
        "elapsed_seconds": time.monotonic() - started,
        "stdout_sha256": digest(directory / "stdout"),
        "stderr_sha256": digest(directory / "stderr"),
    }


def harness(tool, name, types):
    if tool == "kani":
        prefix = '#![forbid(unsafe_code)]\nmod cases;\n#[kani::proof]\n'
        arguments = [f"kani::any::<{ty}>()" for ty in types]
    else:
        prefix = (
            '#![feature(register_tool)]\n#![register_tool(crux)]\n'
            '#![forbid(unsafe_code)]\nextern crate crucible;\n'
            'use crucible::Symbolic;\nmod cases;\n#[crux::test]\n'
        )
        arguments = [f'<{ty}>::symbolic("arg{index}")' for index, ty in enumerate(types)]
    return prefix + f"fn bench_{name}() {{ cases::{name}({', '.join(arguments)}); }}\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--tools", nargs="+", choices=["miren", "kani", "mirai", "crux"],
                        required=True)
    parser.add_argument("--miren", default="miren")
    parser.add_argument("--kani", default="kani")
    parser.add_argument("--mirai", default="mirai")
    parser.add_argument("--crux", default="crux-mir")
    parser.add_argument("--mirai-library-path",
                        help="macOS rustc-driver and Z3 library directories")
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--case", action="append", choices=list(CASES))
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    source = Path(__file__).with_name("cases.rs")
    environment = os.environ.copy()
    records = []
    summary = {
        "schema_version": 1,
        "scope": "14 synthetic host cases; fixed four-element arrays; no hardware model",
        "cases_sha256": digest(source),
        "host": platform.platform(),
        "selected_cases": args.case or list(CASES),
        "complete": False,
        "runs": records,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    for tool in args.tools:
        tool_environment = environment.copy()
        if tool == "kani":
            tool_environment["RUSTFLAGS"] = "--edition=2021 -Coverflow-checks=yes -Copt-level=0"
        if tool == "mirai" and args.mirai_library_path:
            tool_environment["DYLD_LIBRARY_PATH"] = args.mirai_library_path
        binary = shutil.which(getattr(args, tool))
        if binary is None:
            records.append({"tool": tool, "collection": "binary_unavailable"})
            continue
        binary = str(Path(binary).resolve())
        version_directory = output / tool / "version"
        version_directory.mkdir(parents=True)
        version = collect([binary, "--version"], version_directory, args.timeout,
                          tool_environment)
        (version_directory / "receipt.json").write_text(json.dumps(version, indent=2) + "\n")
        for name in args.case or CASES:
            expected, types = CASES[name]
            directory = output / tool / name
            directory.mkdir(parents=True)
            shutil.copyfile(source, directory / "cases.rs")
            options = ["--crate-type=lib", "--edition=2021", "-Coverflow-checks=yes",
                       "-Copt-level=0"]
            if tool == "miren":
                command = [binary, "--verify", "--json", "--entry", name,
                           "cases.rs", *options]
            elif tool == "mirai":
                command = [binary, "--diag=paranoid", "--single_func", name,
                           "--", "cases.rs", *options]
            else:
                (directory / "harness.rs").write_text(harness(tool, name, types))
                if tool == "kani":
                    command = [binary, "harness.rs", "--harness", f"bench_{name}",
                               "--default-unwind", "12", "-Z", "concrete-playback",
                               "--concrete-playback", "print"]
                else:
                    command = [binary, "harness.rs", "--solver", "z3", "--path-sat",
                               "-m", "--mir-json-arg=--crate-type=lib",
                               "--mir-json-arg=-Coverflow-checks=yes",
                               "--mir-json-arg=-Copt-level=0"]
            record = {"tool": tool, "case": name, "expected": expected,
                      "binary_sha256": digest(Path(binary)),
                      "environment": {key: tool_environment[key] for key in [
                          "RUSTFLAGS", "RUSTUP_TOOLCHAIN", "MIREN_Z3",
                          "CRUX_RUST_LIBRARY_PATH", "DYLD_LIBRARY_PATH"
                      ] if key in tool_environment}}
            record.update(collect(command, directory, args.timeout, tool_environment))
            record["source_unchanged"] = digest(directory / "cases.rs") == digest(source)
            record["binary_unchanged"] = digest(Path(binary)) == record["binary_sha256"]
            records.append(record)
            (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
            print(tool, name, record["returncode"],
                  round(record["elapsed_seconds"], 2), flush=True)
    summary["complete"] = True
    summary["source_unchanged"] = digest(source) == summary["cases_sha256"]
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")


if __name__ == "__main__":
    main()
