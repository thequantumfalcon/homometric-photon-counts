"""Independent point formulas, interval containment and regression checks."""

import itertools
import json
import unittest

import calibrate as k


class CalibrationChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        k.c.ctx.prec = 256
        cls.phases = k.c.phase_lists(json.loads(k.c.MODEL.read_text()))
        cls.moments = {g: k.moment_polynomials(cls.phases[g]) for g in "AB"}
        cls.shifted = {
            g: {
                name: k.translate(poly)
                for name, poly in k.score_polynomials(cls.moments[g]).items()
            }
            for g in "AB"
        }

    def test_integer_powers_across_zero(self):
        interval = k.interval(k.F(0), k.F(1, 200))
        for n in range(6):
            value = k.integer_power(interval, n)
            self.assertTrue(value.is_finite())
            for point in [-k.F(1, 200), k.F(0), k.F(1, 200)]:
                self.assertTrue(value.contains(k.c.ball(point**n)))
        with self.assertRaises(ValueError):
            k.integer_power(interval, -1)

    def test_single_site_unit_intensity(self):
        polys = k.moment_polynomials([k.arb(".71")], order=4)
        for s in [".04", ".05", ".2"]:
            t = (-k.arb(s) / 2).exp()
            self.assertTrue(all(p(t).contains(1) for p in polys))

    def test_moment_degrees(self):
        for values in self.moments.values():
            for i, p in enumerate(values):
                self.assertLessEqual(p.degree(), 2 * i * i)

    def test_translation_identity(self):
        poly = {
            (2, 1): k.arb_poly([3, -4, 2]),
            (0, 2): k.arb_poly([2, 7]),
            (1, 0): k.arb_poly([-5]),
        }
        shifted = k.translate(poly)
        for gain, bg, s in [
            ("1", ".125", ".05"),
            ("1.02", ".15", ".051"),
            (".98", ".1", ".049"),
        ]:
            g, b, v = map(k.arb, [gain, bg, s])
            t = (-v / 2).exp()
            direct = sum((p(t) * g**a * b**j for (a, j), p in poly.items()), k.arb(0))
            self.assertTrue((k.evaluate(shifted, g, b, v) - direct).contains(0))

    def test_polynomial_moments_against_raw_recurrence(self):
        for s in [".04", ".05", ".051"]:
            variance = k.arb(s)
            t = (-variance / 2).exp()
            for g in "AB":
                direct = k.c.mixed_moments(self.phases[g], variance, 5, levels=256)
                for p, value in zip(self.moments[g], direct):
                    self.assertTrue((p(t) - value).contains(0))

    def test_gain_changes_rate_not_score_normalization(self):
        deterministic = [k.arb_poly([k.c.ball(k.F(3, 4) ** j)]) for j in range(6)]
        poly = k.translate(k.score_polynomials(deterministic)["mean"])
        actual = k.evaluate(poly, k.arb(2), k.arb(0), k.c.ball(k.S0))
        self.assertTrue((actual - k.arb("-3/10")).contains(0))

    def test_variance_polynomial_against_count_identities(self):
        for g in "AB":
            gain, bg, s = map(k.arb, ["1.02", ".15", ".051"])
            moments = k.c.mixed_moments(self.phases[g], s, 5, levels=256)
            rates = k.c.rate_moments(moments, gain, bg)
            mu, _, var = k.c.score_statistics(rates)
            self.assertTrue(
                (k.evaluate(self.shifted[g]["mean"], gain, bg, s) - mu).contains(0)
            )
            self.assertTrue(
                (k.evaluate(self.shifted[g]["variance"], gain, bg, s) - var).contains(0)
            )

    def test_continuous_box_contains_independent_corner_values(self):
        box = [
            k.interval(k.G0, k.F(1, 50)),
            k.interval(k.B0, k.F(1, 40)),
            k.interval(k.S0, k.F(1, 1000)),
        ]
        enclosures = {
            g: {name: k.evaluate(poly, *box) for name, poly in self.shifted[g].items()}
            for g in "AB"
        }
        for gain, bg, s in itertools.product(
            [".98", "1.02"], [".1", ".15"], [".049", ".051"]
        ):
            gain, bg, s = map(k.arb, [gain, bg, s])
            for g in "AB":
                moments = k.c.mixed_moments(self.phases[g], s, 5, levels=256)
                rates = k.c.rate_moments(moments, gain, bg)
                mu, _, var = k.c.score_statistics(rates)
                eps1, eps2 = k.c.dead_time_budgets(rates, k.c.ball(k.DEAD_MAX))
                for name, point in [
                    ("mean", mu),
                    ("variance", var),
                    ("dead_mean_change", eps1),
                    ("dead_second_change", eps2),
                ]:
                    self.assertLessEqual(k.c.lo(enclosures[g][name]), k.c.lo(point))
                    self.assertGreaterEqual(k.c.hi(enclosures[g][name]), k.c.hi(point))

    def test_fixed_threshold_risk_formula(self):
        shifted = {
            g: {
                "mean": {
                    (0, 0): k.arb_poly([k.c.ball(k.THRESHOLD + sign * k.F(1, 100))])
                },
                "variance": {(0, 0): k.arb_poly([k.arb("1/100")])},
                "dead_mean_change": {(0, 0): k.arb_poly()},
                "dead_second_change": {(0, 0): k.arb_poly()},
            }
            for g, sign in [("A", -1), ("B", 1)]
        }
        result = k.check_box(shifted, k.F(0), k.F(0), k.F(0), dead=False)
        self.assertEqual(result["status"], "PASS")
        for row in result["results"].values():
            risk = k.F(row["risk_upper_exact"])
            self.assertGreaterEqual(risk, k.F(1, 51))
            self.assertLess(risk, k.F(1, 50))

    def test_unsupported_boxes_rejected(self):
        for radii in [
            (k.F(-1), k.F(0), k.F(0)),
            (k.F(0), k.F(1), k.F(0)),
            (k.F(0), k.F(0), k.F(1, 50)),
        ]:
            with self.assertRaises(ValueError):
                k.check_box(self.shifted, *radii)


if __name__ == "__main__":
    unittest.main()
