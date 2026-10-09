# Upstream compiler fixtures

These directories are exact unpacked crates.io archives, not workspace members or trusted models:

- portable-atomic 1.15.0, MIT OR Apache-2.0.
- static_cell 2.1.1, MIT OR Apache-2.0.

Original sources, manifests and licenses remain unchanged. `manifest.json` records registry archive
SHA256 values checked against the workspace Cargo.lock and SHA256 for every unpacked file.
`python3 -m unittest discover -s tools -p 'test_vendor_sources.py'` checks the snapshot.

`crates/miren/tests/portable_atomic_views.rs` uses these sources as path dependencies. Mutation
controls change a temporary copy only. They do not execute invalid custom MIR or hardware paths.
The host workspace continues to forbid unsafe code; these upstream analyzed inputs include unsafe
Rust and remain outside it. Cargo dependencies other than these fixtures still need the normal
cache, and optional upstream features are outside this fixture's selected build configuration.
