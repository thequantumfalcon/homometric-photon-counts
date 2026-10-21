"""Reject gaps and invalid margins in the global four-root perturbation budget."""

from copy import deepcopy
from fractions import Fraction as Q
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from check_root_stability import certificate, cover_margin, envelope_integral, load_inputs  # noqa: E402


class RootStability(unittest.TestCase):
    def test_retained_receipt_is_reproduced(self):
        saved = json.loads((ROOT / "docs/validation/root_stability.json").read_bytes())
        self.assertEqual(certificate(), saved)
        self.assertEqual(Q(saved["rectangle"]["absolute_t_radius"]), Q(1, 10**23))
        self.assertEqual(Q(saved["rectangle"]["background_upper"]), Q(1, 10**20))

    def test_large_or_nonphysical_rectangles_fail(self):
        for t, b in [
            (Q(1, 10**20), Q(1, 10**20)),
            (Q(1, 10**23), Q(1, 10**16)),
            (Q(1, 5), Q(0)),
            (Q(-1), Q(1)),
        ]:
            with self.subTest(t=t, b=b), self.assertRaises(ValueError):
                certificate(t, b)

    def test_missing_tail_leaf_and_endpoint_fail(self):
        saved = load_inputs()
        for case in ("finite-tail-gap", "inverse-tail-gap", "missing-infinite-endpoint", "wrong-sign"):
            data = deepcopy(saved)
            if case == "finite-tail-gap":
                data[3]["negative_covers"].pop(1)
            elif case == "inverse-tail-gap":
                data[4]["derivative_cover"].pop(0)
            elif case == "missing-infinite-endpoint":
                data[4]["values"] = [v for v in data[4]["values"] if v["inverse_gain"] != "0"]
            else:
                data[4]["derivative_cover"][0]["rational_bounds"] = ["-1", "0"]
            with self.subTest(case=case), patch("check_root_stability.load_inputs", return_value=data):
                with self.assertRaises(ValueError):
                    certificate()

    def test_cover_requires_ordered_contiguous_signed_enclosures(self):
        leaves = [
            {"left": "0", "right": "1", "bound": {"lower": "-3", "upper": "-1"}},
            {"left": "1", "right": "2", "bound": {"lower": "-2", "upper": "-1/2"}},
        ]
        self.assertEqual(cover_margin(leaves, Q(0), Q(2), -1), Q(1, 2))
        for altered in [leaves[::-1], leaves[:1], leaves + leaves, []]:
            with self.subTest(altered=altered), self.assertRaises(ValueError):
                cover_margin(altered, Q(0), Q(2), -1)
        for bounds in [{"lower": "1", "upper": "-1"}, {"lower": "-1", "upper": "1"}]:
            with self.subTest(bounds=bounds), self.assertRaises(ValueError):
                cover_margin([{"left": "0", "right": "2", "bound": bounds}], Q(0), Q(2), -1)

    def test_envelope_integrals_match_separate_antiderivative(self):
        # Substitute r=u^2, split at u=7, then integrate integer powers.
        for p, m in [(1, 62), (1, 63), (3, 62), (3, 63)]:
            below = Q(2 * 7 ** (2 * p + 2), 2 * p + 2)
            above = Q(2 * 7**m, (m - 2 * p - 2) * 7 ** (m - 2 * p - 2))
            self.assertEqual(envelope_integral(p, m), below + above)
        with self.assertRaises(ValueError):
            envelope_integral(3, 8)


if __name__ == "__main__":
    unittest.main()
