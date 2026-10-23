"""Regression checks for archive paths and pruned source inventories."""

import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
import zipfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from project import extract_source_archive, files  # noqa: E402


class ArchivePaths(unittest.TestCase):
    def test_inventory_never_visits_ignored_subtrees_or_stats_ignored_files(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            for name in ("top.txt", ".gitignore", "included/nested.txt"):
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("included")
            for name in ("build/runtime/lib64", ".git/objects/item", "included/dist/item"):
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("must never inspect")
            (root / ".venv").write_text("ignored filename")

            real_scandir = os.scandir
            real_is_file = Path.is_file
            ignored = {"build", ".git", "dist", ".venv"}

            def assert_included(path):
                self.assertFalse(set(Path(path).relative_to(root).parts) & ignored)

            def guarded_scandir(path):
                assert_included(path)
                return real_scandir(path)

            def guarded_is_file(path):
                assert_included(path)
                return real_is_file(path)

            with (
                patch("os.scandir", side_effect=guarded_scandir),
                patch.object(Path, "is_file", autospec=True, side_effect=guarded_is_file),
            ):
                inventory = files(root)
            self.assertEqual(
                inventory,
                {name: root / name for name in ("top.txt", ".gitignore", "included/nested.txt")},
            )

    def test_noncanonical_root_accepts_safe_member(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "alias-parent").mkdir()
            archive = root / "source.zip"
            with zipfile.ZipFile(archive, "w") as output:
                output.writestr("homometric-photon-counts/example.txt", "verified payload")
            destination = root / "alias-parent" / ".." / "extracted"
            canonical = extract_source_archive(archive, destination)
            self.assertEqual(canonical, (root / "extracted").resolve())
            self.assertEqual(
                (canonical / "homometric-photon-counts/example.txt").read_text(), "verified payload"
            )

    def test_escape_rejected_before_any_member_is_written(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            archive = root / "source.zip"
            with zipfile.ZipFile(archive, "w") as output:
                output.writestr("safe.txt", "must not extract before validation finishes")
                output.writestr("../escaped.txt", "outside")
            destination = root / "extracted"
            with self.assertRaisesRegex(ValueError, "Unsafe ZIP member"):
                extract_source_archive(archive, destination)
            self.assertFalse((root / "escaped.txt").exists())
            self.assertFalse((destination / "safe.txt").exists())


if __name__ == "__main__":
    unittest.main()
