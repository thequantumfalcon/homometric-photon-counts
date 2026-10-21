"""Regression checks for canonical extraction roots and traversal rejection."""

from pathlib import Path
import sys
import tempfile
import unittest
import zipfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from project import extract_source_archive  # noqa: E402


class ArchivePaths(unittest.TestCase):
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
