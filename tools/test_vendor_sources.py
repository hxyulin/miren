"""Verify immutable upstream compiler fixtures, outside miren's host implementation."""

import hashlib
import json
from pathlib import Path
import unittest


class VendoredSources(unittest.TestCase):
    def test_exact_upstream_package_contents_and_pinned_archive_checksums(self):
        repository = Path(__file__).resolve().parent.parent
        manifest = json.loads((repository / "tests/vendor/manifest.json").read_text())
        self.assertEqual(manifest["schema_version"], 1)
        lock = (repository / "Cargo.lock").read_text().split("[[package]]")
        for package in manifest["packages"]:
            root = repository / package["directory"]
            block = next(b for b in lock if f'name = "{package["name"]}"' in b)
            self.assertIn(f'version = "{package["version"]}"', block)
            self.assertIn(f'checksum = "{package["archive_sha256"]}"', block)
            files = {str(p.relative_to(root)) for p in root.rglob("*") if p.is_file()}
            self.assertEqual(files, set(package["files"]))
            for name, expected in package["files"].items():
                self.assertEqual(hashlib.sha256((root / name).read_bytes()).hexdigest(), expected,
                                 str(root / name))
            self.assertTrue((root / "LICENSE-APACHE").is_file())
            self.assertTrue((root / "LICENSE-MIT").is_file())


if __name__ == "__main__":
    unittest.main()
