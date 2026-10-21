"""Guard the external boundary between archived bytes and quoted proof inputs."""

import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from check_archive_binding import LITERALS, MODEL, bind, certificate, unique_pairs  # noqa: E402


class ArchiveBinding(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.model = (ROOT / MODEL).read_bytes()
        cls.literals = (ROOT / LITERALS).read_bytes()

    def test_saved_binding_and_original_whitespace(self):
        actual = certificate()
        saved = json.loads((ROOT / "docs/validation/archive_byte_binding.json").read_bytes())
        self.assertEqual(actual, saved)
        self.assertEqual([r["phase_count"] for r in actual["fragments"]], [63, 63])

    def test_changed_model_byte_fails(self):
        with self.assertRaisesRegex(ValueError, "model hash"):
            bind(self.model + b"\n", self.literals)

    def test_wrong_literal_whitespace_fails(self):
        mutated = self.literals.replace(b"\\n", b" ", 1)
        self.assertNotEqual(mutated, self.literals)
        with self.assertRaisesRegex(ValueError, "differs"):
            bind(self.model, mutated)

    def test_missing_and_duplicate_literals_fail(self):
        line = next(line for line in self.literals.splitlines() if line.startswith(b"def rawA :"))
        for mutated in [self.literals.replace(line, b""), self.literals + line + b"\n"]:
            with self.subTest(size=len(mutated)), self.assertRaisesRegex(ValueError, "literal declaration"):
                bind(self.model, mutated)

    def test_ambiguous_escape_and_duplicate_keys_fail(self):
        # JSON accepts \u005b for '['; this bridge deliberately forbids it.
        mutated = self.literals.replace(b"['['", b"['\\u005b'", 1)
        self.assertNotEqual(mutated, self.literals)
        with self.assertRaisesRegex(ValueError, "Unsafe literal escape"):
            bind(self.model, mutated)
        with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
            json.loads('{"re": [], "re": []}', object_pairs_hook=unique_pairs)


if __name__ == "__main__":
    unittest.main()
