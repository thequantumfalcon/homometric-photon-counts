"""Check the simulator against analytic laws and independent exact-field inputs."""

import cmath
import math
import random
import unittest
from fractions import Fraction
from pathlib import Path

import simulate as sim


class SimulationChecks(unittest.TestCase):
    def test_coordinate_phases_against_archived_number_field(self):
        model, _, _ = sim.read_inputs(
            Path(__file__).resolve().parents[1] / "public-repo"
        )
        roots = [
            math.sqrt(
                math.prod(r for bit, r in enumerate((3, 74, 191)) if mask & (1 << bit))
            )
            for mask in range(8)
        ]
        for label in "AB":
            actual = sim.coordinate_phases(model, label)
            records = model["graphs"][label]["phases_exact"]
            for phase, record in zip(actual, records, strict=True):
                z = complex(
                    *(
                        math.fsum(
                            float(Fraction(c)) * r
                            for c, r in zip(record[k], roots, strict=True)
                        )
                        for k in ("re", "im")
                    )
                )
                self.assertLess(abs(cmath.exp(1j * phase) - z), 2e-14)

    def test_common_phase_and_coherent_limit(self):
        phases = [0.1, 0.8, -0.2, 1.2]
        self.assertAlmostEqual(
            sim.intensity(phases), sim.intensity([p + 0.7 for p in phases]), places=12
        )
        self.assertEqual(sim.intensity([0.0] * 63), 3969)

    def test_poisson_zero_and_invalid_rates(self):
        self.assertEqual(sim.poisson(random.Random(1), 0), 0)
        for value in (-1, float("nan"), float("inf"), 1001):
            with self.assertRaises(ValueError):
                sim.poisson(random.Random(1), value)

    def test_poisson_mean_and_variance_including_chunked_sampler(self):
        for rate in (3.0, 60.0):
            rng = random.Random(5479)
            stats = sim.Stats()
            for _ in range(40000):
                stats.add(sim.poisson(rng, rate))
            self.assertLess(abs(stats.mean - rate), 6 * math.sqrt(rate / stats.n))
            variance = stats.m2 / (stats.n - 1)
            # Asymptotic SE of sample variance for a Poisson law; diagnostic only.
            self.assertLess(
                abs(variance - rate), 6 * math.sqrt((rate + 2 * rate**2) / stats.n)
            )

    def test_poisson_fourth_factorial_identity(self):
        rng, stats, rate = random.Random(8117), sim.Stats(), 2.5
        for _ in range(50000):
            n = sim.poisson(rng, rate)
            stats.add(math.prod(n - k for k in range(4)))
        self.assertLess(
            abs(stats.mean - rate**4), 6 * stats.report()["estimated_standard_error"]
        )

    def test_nonparalyzable_boundary(self):
        arrivals = [0.0, 0.25, 0.375, 0.5, 0.75]
        self.assertEqual(sim.accepted_count(arrivals, 0), 5)
        self.assertEqual(sim.accepted_count(arrivals, 0.5), 2)
        self.assertEqual(sim.accepted_count(arrivals, 1), 1)
        self.assertEqual(sim.accepted_count([], 0.5), 0)

    def test_long_dead_time_matches_bernoulli_response(self):
        rng, stats, rate = random.Random(649), sim.Stats(), 3.0
        for _ in range(30000):
            n = sim.poisson(rng, rate)
            stats.add(sim.accepted_count([rng.random() for _ in range(n)], 1))
        expected = 1 - math.exp(-rate)
        self.assertLess(
            abs(stats.mean - expected),
            6 * math.sqrt(expected * (1 - expected) / stats.n),
        )

    def test_one_site_removes_all_phase_noise_from_intensity(self):
        result = sim.simulate("control", [0.7], 10000, 984, 20, 3, 1, 0, [0.0] * 13)
        self.assertAlmostEqual(result["statistics"]["intensity"]["mean"], 1, places=14)
        self.assertEqual(result["ideal_histogram"], result["dead_time_histogram"])
        self.assertLess(
            abs(result["statistics"]["ideal_counts"]["mean"] - 4),
            6 * math.sqrt(4 / 10000),
        )


if __name__ == "__main__":
    unittest.main()
