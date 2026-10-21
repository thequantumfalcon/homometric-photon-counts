"""Independent identities and limiting cases for the feasibility calculations."""

import math
import unittest
from fractions import Fraction

import numpy as np
import study


class StudyChecks(unittest.TestCase):
    def test_rational_square_root_rounds_outward(self):
        for value in (Fraction(0), Fraction(1, 7), Fraction(4), Fraction(1234567, 123)):
            root = study.rational_sqrt_upper(value)
            self.assertGreaterEqual(root**2, value)
            if root:
                self.assertLess((root - Fraction(1, 10**15)) ** 2, value)

    def test_budget_limits_and_monotonicity(self):
        loss = Fraction(1, 10**12)
        risks = [
            Fraction(study.budget_bound(n, loss)["equal_prior_error_lower_exact"])
            for n in (0, 10, 1000, 10**15)
        ]
        self.assertEqual(risks[0], Fraction(1, 2))
        self.assertEqual(risks[-1], 0)
        self.assertEqual(risks, sorted(risks, reverse=True))
        with self.assertRaises(ValueError):
            study.budget_bound(-1, loss)

    def test_coherent_fourier_normalization(self):
        power, total = study.projected_power(np.zeros((1, 63)), np.ones(63))
        self.assertAlmostEqual(power[0], 63**2 / 4096, places=14)
        self.assertAlmostEqual(total[0], 63 / 64, places=14)
        self.assertLessEqual(power[0], total[0])

    def test_uniform_quantizer_fourier_identity(self):
        phases = np.linspace(-4, 7, 11)
        s = 2 * math.log(2)
        # The first Fourier coefficient is sinc(pi/L). All aliases are suppressed
        # by at least exp(-(L-1)^2*s/2), below 1e-60 for L=16 here.
        actual = study.phase_mean(phases, s, 16)
        expected = np.exp(-s / 2 + 1j * phases) * np.sinc(1 / 16)
        np.testing.assert_allclose(actual, expected, rtol=0, atol=1e-14)

    def test_single_site_intensity_has_no_phase_dependence(self):
        for levels in (None, 16, 256):
            value = study.mean_intensity(np.array([0.71]), np.array([2.0]), 1.7, levels)
            self.assertAlmostEqual(value, 4, places=14)

    def test_opposite_pair_second_intensity_moment(self):
        for s in (0, 0.3, 2, 20):
            actual = study.zero_sum_second_intensity(np.array([0, np.pi]), s)
            self.assertAlmostEqual(
                actual, 6 - 8 * math.exp(-s) + 2 * math.exp(-4 * s), places=13
            )

    def test_detector_identity_and_deterministic_afterpulse(self):
        np.testing.assert_allclose(study.additive_detector_channel(0, 0), np.eye(13))
        kernel = study.additive_detector_channel(0, 1)
        self.assertEqual(kernel[2, 1], 1)
        self.assertEqual(kernel[12, 6], 1)
        self.assertEqual(kernel[12, 12], 1)

    def test_dark_count_kernel_and_variation_contraction(self):
        b = 0.125
        kernel = study.additive_detector_channel(b, 0)
        expected = np.array(
            [math.exp(-b) * b**k / math.factorial(k) for k in range(12)]
        )
        np.testing.assert_allclose(kernel[:12, 0], expected, rtol=1e-14)
        delta = np.array([1, -1] + [0] * 11, dtype=float)
        self.assertLessEqual(np.abs(kernel @ delta).sum(), np.abs(delta).sum())
        np.testing.assert_allclose(kernel.sum(axis=0), 1, rtol=0, atol=1e-14)


if __name__ == "__main__":
    unittest.main()
