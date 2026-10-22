"""Check published data bindings and keep replay outputs outside preserved evidence."""

from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import optical_validation as study  # noqa: E402


class OpticalValidation(unittest.TestCase):
    def test_distributed_inputs_and_nested_manifests(self):
        result = study.verify()
        self.assertEqual(result["archived_files"], 115)
        self.assertEqual(result["measured_table_bins"], 75658)

    def test_output_cannot_enter_preserved_studies(self):
        with self.assertRaises(ValueError):
            study.fresh_output(study.STUDY / "new-output")
        with tempfile.TemporaryDirectory() as folder:
            with self.assertRaises(ValueError):
                study.fresh_output(Path(folder))


if __name__ == "__main__":
    unittest.main()
