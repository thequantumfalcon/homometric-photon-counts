"""Check published data bindings and keep replay outputs outside preserved evidence."""

from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import optical_validation as study  # noqa: E402


class OpticalValidation(unittest.TestCase):
    def test_certificate_replay_accepts_linux_newlines_without_changing_archive(self):
        archived = (study.ARCHIVE / "optical-transfer-certificate/certificate.json").read_bytes()
        linux_output = archived.replace(b"\r\n", b"\n")
        self.assertIn(b"\r\n", archived)
        self.assertNotEqual(linux_output, archived)
        result = study.compare_certificate(linux_output, archived)
        self.assertFalse(result["certificate_reproduced_byte_for_byte"])
        self.assertTrue(result["certificate_reproduced_after_line_ending_normalization"])
        self.assertTrue(study.compare_certificate(archived, archived)["certificate_reproduced_byte_for_byte"])

    def test_certificate_replay_rejects_changes_below_float_precision(self):
        archived = b'{"lower": 0.1234567890123456789012345678901}\r\n'
        changed = b'{"lower": 0.1234567890123456789012345678902}\n'
        with self.assertRaisesRegex(ValueError, "beyond line endings"):
            study.compare_certificate(changed, archived)

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
