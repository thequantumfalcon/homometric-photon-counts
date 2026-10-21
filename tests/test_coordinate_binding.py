"""Detect changes at the file-to-formal-coordinate boundary."""

import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from check_coordinate_binding import LITERALS, MODEL, bind, certificate  # noqa: E402


class CoordinateBinding(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.model = (ROOT / MODEL).read_bytes()
        cls.literals = (ROOT / LITERALS).read_bytes()

    def test_saved_binding(self):
        actual = certificate()
        saved = json.loads((ROOT / "docs/validation/coordinate_byte_binding.json").read_bytes())
        self.assertEqual(actual, saved)
        self.assertEqual([r["coordinate_count"] for r in actual["fragments"]], [63, 63])

    def test_changed_model_byte_fails(self):
        with self.assertRaisesRegex(ValueError, "model hash"):
            bind(self.model + b"\n", self.literals)

    def test_changed_literal_and_ambiguous_escape_fail(self):
        for before, after, error in [(b"\\n", b" ", "differs"), (b"['['", b"['\\u005b'", "Unsafe")]:
            mutated = self.literals.replace(before, after, 1)
            self.assertNotEqual(mutated, self.literals)
            with self.subTest(error=error), self.assertRaisesRegex(ValueError, error):
                bind(self.model, mutated)

    def test_missing_duplicate_and_swapped_arrays_fail(self):
        a = next(line for line in self.literals.splitlines() if line.startswith(b"def rawCoordinatesA :"))
        b = next(line for line in self.literals.splitlines() if line.startswith(b"def rawCoordinatesB :"))
        for mutated in [self.literals.replace(a, b""), self.literals + a + b"\n"]:
            with self.assertRaisesRegex(ValueError, "literal declaration"):
                bind(self.model, mutated)
        swapped = self.literals.replace(a, b.replace(b"rawCoordinatesB", b"rawCoordinatesA", 1))
        with self.assertRaisesRegex(ValueError, "differs"):
            bind(self.model, swapped)


if __name__ == "__main__":
    unittest.main()
