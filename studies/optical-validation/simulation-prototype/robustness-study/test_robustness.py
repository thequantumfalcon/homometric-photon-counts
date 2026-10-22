"""Independent checks for the added optics and moment-screen calculations."""

import unittest

import numpy as np
import study as s


class RobustnessTests(unittest.TestCase):
    def test_original_one_dimensional_integral_reproduced(self):
        for x, d in [(0, 0), (5, 30), (-5, -30)]:
            np.testing.assert_allclose(
                s.coefficients(x, 0, d),
                s.b.quadrature_coefficients(s.CONFIG, x, d),
                rtol=3e-14,
                atol=1e-19,
            )

    def test_poppy_2d_and_refinement(self):
        self.assertEqual(len(s.numerical_checks()), 4)

    def test_single_phasor_intensity_is_constant(self):
        z = np.array([[1.2 + 0.7j]])
        expected = (abs(z[0, 0]) ** 2 / 63) ** np.arange(5)
        np.testing.assert_allclose(
            s.intensity_moments(z, [0.3])[0], expected, rtol=1e-12
        )

    def test_two_phasors_against_gauss_hermite_integral(self):
        # Relative phase is Gaussian with variance 2*s; integrate its cosine law.
        z = np.array([[1.2 + 0.7j, -0.3 + 0.9j]])
        nodes, weights = np.polynomial.hermite.hermgauss(64)
        variance = 0.08
        relative = 2 * np.sqrt(variance) * nodes
        intensity = abs(z[0, 0] + z[0, 1] * np.exp(1j * relative)) ** 2 / 63
        expected = [
            float(np.dot(weights, intensity**k) / np.sqrt(np.pi)) for k in range(5)
        ]
        np.testing.assert_allclose(
            s.intensity_moments(z, [variance])[0], expected, rtol=2e-12
        )

    def test_first_moment_against_gaussian_pair_formula(self):
        rng = np.random.default_rng(899)
        z = rng.normal(size=(3, 63)) + 1j * rng.normal(size=(3, 63))
        variances = np.array([0.04, 0.05, 0.06])
        expected = (
            (1 - np.exp(-variances)) * (abs(z) ** 2).sum(axis=1)
            + np.exp(-variances) * abs(z.sum(axis=1)) ** 2
        ) / 63
        np.testing.assert_allclose(
            s.intensity_moments(z, variances, 1)[:, 1], expected, rtol=3e-13
        )

    def test_phase_correction_preserves_amplitudes(self):
        case = s.Case("check", x_um=5, y_um=-5, opd_nm=30)
        actual, phase = s.transfer(case)
        corrected = actual * np.exp(1j * phase)
        np.testing.assert_allclose(corrected, abs(actual), atol=5e-16)
        self.assertGreater(float(np.max(abs(actual.imag))), 0.01)

    def test_quantized_lookup_matches_original_rounding(self):
        phases = np.linspace(-42, 91, 3000)
        expected = np.exp(1j * np.rint(phases * 256 / (2 * np.pi)) * 2 * np.pi / 256)
        np.testing.assert_allclose(s.quantized_field(phases), expected, atol=3e-14)


if __name__ == "__main__":
    unittest.main()
