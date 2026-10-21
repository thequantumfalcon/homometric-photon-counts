"""Reject corrupted risk claims and unsafe publication outputs without Arb."""

from copy import deepcopy
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import optical_study as study


class OpticalStudyChecks(unittest.TestCase):
    def setUp(self):
        self.data = study.read(study.ARCHIVE / "calibration-study/run-checked/calibration.json")

    def test_retained_files_inputs_and_risk_bounds(self):
        self.assertEqual(study.verify()["archived_files"], 36)

    def test_tampered_risk_is_rejected(self):
        self.data["box_checks"][3]["results"]["B"]["risk_upper_exact"] = "0"
        with self.assertRaises(ValueError):
            study.audit_calibration(self.data)

    def test_wrong_side_of_threshold_is_not_a_small_error(self):
        self.assertEqual(study.risk(study.F(1), study.F(-1), 5000), 1)

    def test_missing_or_changed_box_is_rejected(self):
        for field in ("gain_radius", "background_radius", "variance_radius"):
            data = deepcopy(self.data)
            data["box_checks"][3][field] = "0"
            with self.subTest(field=field), self.assertRaises(ValueError):
                study.audit_calibration(data)

    def test_incorrect_sample_count_is_rejected(self):
        self.data["box_checks"][3]["results"]["A"]["sufficient_samples_for_5pct"] = 1
        with self.assertRaises(ValueError):
            study.audit_calibration(self.data)

    def test_fresh_output_and_archive_protection(self):
        with tempfile.TemporaryDirectory() as folder:
            with self.assertRaises(ValueError):
                study.stage(Path(folder))
        with self.assertRaises(ValueError):
            study.stage(study.STUDY / "forbidden-output")


if __name__ == "__main__":
    unittest.main()
