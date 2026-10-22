"""Independent optical and detector checks for this bounded bench model."""

import unittest

import bench as b
import numpy as np
from scipy.special import gammainc


class BenchTests(unittest.TestCase):
    def test_geometry_binding(self):
        self.assertEqual(
            {g: len(x) for g, x in b.coordinates().items()}, {"A": 63, "B": 63}
        )

    def test_gaussian_integral_against_error_function(self):
        config = b.Bench()
        exact = b.closed_form_centered(config)
        quad = b.quadrature_coefficients(config)
        self.assertLess(float(np.max(abs(quad / exact - 1))), 1e-13)

    def test_calibration_is_attenuation_only_and_uniform(self):
        config = b.Bench()
        attenuation, common = b.calibration(config)
        self.assertTrue(np.all((attenuation > 0) & (attenuation <= 1)))
        np.testing.assert_allclose(
            attenuation * b.closed_form_centered(config), common, rtol=1e-14
        )

    def test_poppy_against_numpy_unitary_transform(self):
        rng = np.random.default_rng(155)
        field = rng.normal(size=(32, 32)) + 1j * rng.normal(size=(32, 32))
        actual = b.MatrixFourierTransform(centering="FFTSTYLE").perform(field, 32, 32)
        expected = np.fft.fftshift(np.fft.ifft2(np.fft.ifftshift(field), norm="ortho"))
        np.testing.assert_allclose(actual, expected, atol=2e-13)
        self.assertAlmostEqual(
            float(np.sum(abs(actual) ** 2) / np.sum(abs(field) ** 2)), 1.0, places=12
        )

    def test_optical_convergence_and_forward_projection(self):
        self.assertEqual(
            b.numerical_checks(b.Bench())["status"], "PASS_NUMERICAL_CHECKS"
        )

    def test_zero_dead_time_is_poisson(self):
        rate = np.linspace(0, 100, 2000)
        np.testing.assert_array_equal(
            b.detector_counts(rate, np.random.default_rng(12)),
            np.random.default_rng(12).poisson(rate),
        )

    def test_zero_rate_has_zero_detections(self):
        np.testing.assert_array_equal(
            b.detector_counts(np.zeros(100), np.random.default_rng(13), 0.1), 0
        )

    def test_dead_time_against_renewal_gamma_distribution(self):
        # P(K >= k) = P(Gamma(k, rate) <= gate-(k-1)*dead_time).
        rate, dead, n = 20.0, 0.01, 100000
        counts = b.detector_counts(np.full(n, rate), np.random.default_rng(14), dead)
        for k in (12, 16, 20, 24):
            expected = gammainc(k, rate * (1 - (k - 1) * dead))
            self.assertLess(abs(float(np.mean(counts >= k)) - expected), 0.007)

    def test_invalid_inputs_rejected(self):
        for rate, dead in [([-1], 0), ([np.nan], 0), ([1], -0.1)]:
            with self.assertRaises(ValueError):
                b.detector_counts(rate, np.random.default_rng(1), dead)

    def test_zero_observed_errors_does_not_certify_five_percent(self):
        self.assertGreater(b.binomial_interval(0, 40)[1], 0.05)


if __name__ == "__main__":
    unittest.main()
