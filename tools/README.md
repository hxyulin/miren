# Fleet survey runner

`fleet_survey.py` inventories every workspace library and binary target discovered beneath a fleet
checkout, excluding the host-only `xtask`. It skips `target`, `.git`, virtual environments and
Node dependencies. Pinned Cargo metadata supplies workspace membership and expected units;
metadata failures and missing units remain visible. Dependency and build-script roots are outside
this scope. Counts describe independently selected MIR roots, not line or firmware safety
coverage.

Build miren's release binaries first, with its pinned compiler and solver available. The runner
copies the analyzer and available sibling binaries into the output directory before inventory;
concurrent release rebuilds cannot replace queued verification binaries. From this checkout, use a
new output directory for every run:

```sh
python3 tools/fleet_survey.py /path/to/fleet-2027 --output /tmp/fleet-survey-001 \
  --solver "$PWD/.venv/bin/z3"
python3 tools/fleet_survey.py /path/to/fleet-2027 --output /tmp/fleet-survey-002 \
  --previous /tmp/fleet-survey-001/summary.json
```

The runner completes sequential Cargo inventories before starting bounded parallel direct-driver
verification. Verification failure in one unit cannot stop another unit. `--jobs` defaults to
four. Use `--analyzer`, `--cargo`, `--target`, `--profile`, `--features`, `--build-timeout`,
`--unit-timeout` and the five miren analysis-limit flags to select a configuration. Defaults use
ARM, dev, Cargo's default features and miren's conservative execution limits. Startup assumptions,
trusted contracts, induction and native counterexample execution are disabled. Inventory passes
`--no-config` so a fleet `miren.json` cannot change survey selectors or verification settings.

`summary.json` starts as partial and is replaced atomically as results arrive. A complete survey
means every expected unit was inventoried and its results collected, even if some roots refute or
remain unknown. Exit zero means complete collection, not a complete proof. A partial run exits
one; missing units are listed even when no roots could be recovered. Crashed, missing, malformed
or mismatched reports never count as proved. Raw inventories, verification JSONL, command records,
stdout and stderr remain in the output directory. Existing output directories are rejected.

Replay restores the report's captured compiler working directory and Cargo compiler environment.
Older inventories without environment capture are rejected for proof counting. The compiler
capture covers Cargo package/features/configuration variables, manifest and crate identity,
`OUT_DIR` and `DEP_*`; arbitrary custom environment inputs outside that capture are not guaranteed
reproducible. The runner fingerprints explicit compiler dependencies, transitive metadata and
proc-macro candidates in dependency search directories, adjacent `.rmeta.miren-origins.json`
sidecars (including their absence), generated `OUT_DIR` files and native search-directory inputs.
It checks these immediately before and after each unit's verification and again at completion.
Changed, added or missing inputs invalidate that unit's proof counts and leave collection partial.
Dependency/build traversal is limited to 100,000 files per unit. These are integrity checks on
live Cargo artifacts; the artifacts are not copied into the survey output. No application source
is rewritten. Cargo may download dependencies and refresh its analysis cache.

Provenance includes source revisions and dirty paths, analyzer binary hash, compiler/solver
versions, original/frozen binary hashes, source/build file hashes, target, profile, feature
request, limits and command logs. Source contents are hashed again at completion; changes
invalidate every collected proof even when Git's dirty paths remain the same. Diffs list added,
removed and changed root outcomes, using workspace/package/target/function identity so source line
shifts do not rename roots. They flag incompatible analysis configurations; compiler/environment
changes and generated-name changes still need review. Source function counts use a source-line
`fn` heuristic excluding closures; other generated roots remain separate. This classification is
not an AST coverage claim.

Run the standalone tests without compiling Rust:

```sh
python3 -m unittest discover -s tools -p 'test_*.py'
```

To publish a completed measurement, export its validated full summary:

```sh
python3 tools/fleet_survey_export.py /tmp/fleet-survey-002/summary.json \
  --output /tmp/fleet-survey-compact.json --measured-on 2026-10-09 \
  --previous /tmp/fleet-survey-001/summary.json
```

The exporter rejects partial or inconsistent current collections, missing roots, duplicate
identities, count mismatches, failed unit/workspace collection and changed source/artifact
evidence. It preserves every root through the existing schema-1 `root_columns`, sorted unit, file
and blocker tables, plus counts and source classification. The explicit measurement date is
required; it is not inferred from file timestamps. An optional previous full summary records
baseline counts, unit failures, outcome transitions, added/removed roots, previously proved
regressions and incompatible configurations. The previous collection may be partial, with its
status preserved in the comparison.

Compact provenance stores source and artifact aggregate SHA256 fingerprints instead of all
artifact paths. Artifact checkpoint coverage is explicit: older surveys have no artifact evidence
and report null for its fingerprint/unchanged flag; surveys recorded before pre-verification maps
were retained can report inventory, post-verification and completion checkpoints only. Unrecorded
compiler settings are not inferred from the target name. Export uses a deterministic atomic
replacement and changes no application code or documentation data automatically.
