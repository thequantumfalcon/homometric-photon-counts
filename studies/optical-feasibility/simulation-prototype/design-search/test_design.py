"""Independent identities and boundary checks for the changed-frequency design."""

import itertools
import math
import unittest
from fractions import Fraction

import certify as c
import numpy as np
import search
from scipy.special import ndtr


class DesignChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        c.ctx.prec = 256

    def test_single_site_all_moments_equal_one(self):
        values = c.mixed_moments([c.arb("0.71")], c.arb("0.8"), 5)
        self.assertTrue(all(v.contains(1) for v in values))

    def test_two_site_closed_forms(self):
        s = c.arb("0.3")
        values = c.mixed_moments([c.arb(0), c.arb.pi()], s, 4)
        self.assertTrue((values[1] - (1 - (-s).exp())).contains(0))
        exact = (6 - 8 * (-s).exp() + 2 * (-4 * s).exp()) / 4
        self.assertTrue((values[2] - exact).contains(0))

    def test_zero_noise_coherent_limit(self):
        values = c.mixed_moments([c.arb(0)] * 3, c.arb(0), 4)
        self.assertTrue(all(v.contains(3**k) for k, v in enumerate(values)))

    def test_exhaustive_characteristic_expansion(self):
        theta = [c.arb("0.2"), c.arb("1.1")]
        s = c.arb("0.7")
        actual = c.mixed_moments(theta, s, 3)
        for k in range(1, 4):
            total = c.acb(0)
            for positive in itertools.product(range(2), repeat=k):
                for negative in itertools.product(range(2), repeat=k):
                    d = [positive.count(j) - negative.count(j) for j in range(2)]
                    total += (
                        c.acb(
                            -s * sum(x * x for x in d) / 2,
                            sum((theta[j] * d[j] for j in range(2)), c.arb(0)),
                        ).exp()
                        / 2**k
                    )
            self.assertTrue((actual[k] - total.real).contains(0))

    def test_original_fourth_gap_identity(self):
        _, model, _ = search.inputs()
        phases = c.phase_lists(model, Fraction(1, 3))
        s = 2 * c.arb(2).log()
        a, b = [c.mixed_moments(phases[g], s, 4) for g in "AB"]
        for k in range(4):
            self.assertTrue((a[k] - b[k]).contains(0))
        x = Fraction(1, 4)
        exact = (
            Fraction(455015761, 20000)
            * x**4
            * (1 - x) ** 5
            * (x**3 + 3 * x * x + 6 * x + 6)
            / 63**4
        )
        self.assertTrue((a[4] - b[4] - c.ball(exact)).contains(0))
        self.assertGreater(c.lo(a[4] - b[4]), 0)

    def test_two_independent_moment_implementations(self):
        phases = np.array([[0.2, 1.1, -0.4]])
        actual = search.intensity_moments(phases, np.array([0.7]), 4)[0]
        expected = c.mixed_moments([c.arb(str(x)) for x in phases[0]], c.arb(".7"), 4)
        np.testing.assert_allclose(
            actual, [float(v.mid()) for v in expected], rtol=2e-13, atol=1e-13
        )

    def test_deterministic_count_score_moments(self):
        for n in range(9):
            factorials = [c.arb(math.prod(n - j for j in range(k))) for k in range(5)]
            mu, second, var = c.score_statistics(factorials)
            value = Fraction(n * (n - 1), 3969) - c.BETA * Fraction(n, 63)
            self.assertTrue((mu - c.ball(value)).contains(0))
            self.assertTrue((second - c.ball(value * value)).contains(0))
            self.assertTrue(var.contains(0))

    def test_compound_poisson_double_jump(self):
        lam = c.arb("3/4")
        rates = [lam**k for k in range(6)]
        doubled = c.count_factorials(rates, c.arb(1))
        self.assertTrue((doubled[1] - 2 * lam).contains(0))
        self.assertTrue((doubled[2] - 4 * lam * lam - 2 * lam).contains(0))
        identity = c.count_factorials(rates, c.arb(0))
        self.assertTrue(all((a - b).contains(0) for a, b in zip(identity, rates)))

    def test_dead_time_pathwise_inequalities(self):
        base, _, _ = search.inputs()
        dead = Fraction(1, 5)
        for arrivals in itertools.combinations_with_replacement(
            [0, 0.1, 0.3, 0.7, 0.9], 4
        ):
            n = len(arrivals)
            accepted = base.accepted_count(list(arrivals), float(dead))
            pairs = sum(
                b - a < float(dead) for a, b in itertools.combinations(arrivals, 2)
            )
            self.assertLessEqual(n - accepted, pairs)

            def score(k):
                return Fraction(k * (k - 1), 3969) - c.BETA * Fraction(k, 63)

            derivative = Fraction(2 * n, 3969) + c.BETA / 63
            magnitude = Fraction(n * n, 3969) + c.BETA * Fraction(n, 63)
            self.assertLessEqual(abs(score(n) - score(accepted)), pairs * derivative)
            self.assertLessEqual(
                abs(score(n) ** 2 - score(accepted) ** 2),
                pairs * 2 * magnitude * derivative,
            )

    def test_dead_time_zero_limit(self):
        first, second = c.dead_time_budgets([c.arb(2) ** k for k in range(6)], c.arb(0))
        self.assertTrue(first.is_zero() and second.is_zero())

    def test_quantizer_against_wrapped_normal_cells(self):
        # Independent cell integration, including an L=8 case with visible aliases.
        for levels, s, d in [(8, 0.2, 3), (256, 0.05, 1), (256, 0.05, 5)]:
            theta = 0.71
            edges = 2 * np.pi * (np.arange(levels + 1) - 0.5) / levels
            probabilities = sum(
                (
                    np.diff(ndtr((edges + 2 * np.pi * k - theta) / np.sqrt(s)))
                    for k in range(-4, 5)
                ),
                np.zeros(levels),
            )
            direct = probabilities @ np.exp(
                1j * d * 2 * np.pi * np.arange(levels) / levels
            )
            enclosed = c.quantized_characteristic(
                c.arb(str(theta)), c.arb(str(s)), d, levels
            )
            # The CDF integration is floating-point: allow its numerical error.
            for exact, value in [
                (enclosed.real, direct.real),
                (enclosed.imag, direct.imag),
            ]:
                self.assertLessEqual(float(c.lo(exact)) - 1e-13, value)
                self.assertGreaterEqual(float(c.hi(exact)) + 1e-13, value)

    def test_quantizer_single_site_intensity(self):
        values = c.mixed_moments([c.arb(".71")], c.arb("1/20"), 4, levels=256)
        self.assertTrue(all(value.contains(1) for value in values))


if __name__ == "__main__":
    unittest.main()
