"""Distributional checks against analytic laws and a separate event-list sampler."""
import heapq
import math
import unittest
from concurrent.futures import ThreadPoolExecutor

import numpy as np
from scipy.special import gammainc, gammaln
from scipy.stats import poisson

from detector import simulate


def empirical_cdf(samples, n=150):
    return np.cumsum(np.bincount(samples, minlength=n + 1))[:n + 1] / len(samples)


def independent_reference(n, seed):
    """Conditional-Poisson uniform timestamps, with all candidates in one heap."""
    rng = np.random.default_rng(seed)
    result = np.zeros(n, dtype=np.int64)
    for i in range(n):
        queue = list(rng.uniform(size=rng.poisson(5.0)))
        heapq.heapify(queue)
        ready = 0.0
        while queue:
            t = heapq.heappop(queue)
            if t < ready:
                continue
            result[i] += 1
            ready = t + 0.02
            for _ in range(rng.poisson(0.2)):
                k = rng.choice(3, p=[0.2, 0.5, 0.3])
                arrival = ready + (k + rng.uniform()) * 0.03
                if arrival < 1:
                    heapq.heappush(queue, arrival)
    return result


class DetectorTests(unittest.TestCase):
    def test_zero_input_and_invalid_arguments(self):
        self.assertFalse(simulate(np.zeros(20), [1.0], 0.3).any())
        for args in [([-1.0],[1.0],0.1), ([1.0],[0.8],0.1),
                     ([1.0],[1.0],1.0), ([float('nan')],[1.0],0.1)]:
            with self.assertRaises(ValueError):
                simulate(*args)

    def test_poisson_limit(self):
        counts = simulate(np.full(100000, 8.0), [1.0], 0, seed=410)[..., 0]
        distance = np.max(abs(empirical_cdf(counts) - poisson.cdf(np.arange(151), 8)))
        self.assertLess(distance, math.sqrt(math.log(2e6) / 200000))

    def test_exact_initially_live_recovery_law(self):
        counts = simulate(np.full(100000, 20.0), [1.0], 0, recovery=0.02, seed=411)[..., 0]
        k = np.arange(151)
        exact = 1 - gammainc(k + 1, 20 * np.maximum(1 - k * 0.02, 0))
        self.assertLess(np.max(abs(empirical_cdf(counts) - exact)), math.sqrt(math.log(2e6) / 200000))

    def test_compound_poisson_branching_limit(self):
        counts = simulate(np.full(100000, 5.0), [1.0], 0.2, seed=412)[..., 0]
        k = np.arange(1, 151)
        pmf = np.r_[np.exp(-5), np.exp(np.log(5) + (k - 1)*np.log(5 + 0.2*k) - 5 - 0.2*k - gammaln(k + 1))]
        self.assertAlmostEqual(float(pmf.sum()), 1.0, places=12)
        self.assertLess(np.max(abs(empirical_cdf(counts) - np.cumsum(pmf))), math.sqrt(math.log(2e6) / 200000))

    def test_independent_uniform_timestamp_reference(self):
        n = 20000
        actual = simulate(np.full(n, 5.0), [0.2,0.7,1.0], 0.2, 0.02, 0.03, 413)
        reference = independent_reference(n, 414)
        self.assertGreater(int(actual[:, 3].sum()), 0)
        self.assertLess(np.max(abs(empirical_cdf(actual[:, 0]) - empirical_cdf(reference))),
                        2*math.sqrt(math.log(4e6) / (2*n)))
        self.assertTrue(np.all(actual[:, 4] == actual[:, 1] + actual[:, 3]))

    def test_out_of_gate_daughters_are_excluded(self):
        actual = simulate(np.full(1000, 10.0), [0.0,0.0,1.0], 0.4, 0.001, 1.0, 415)
        self.assertFalse(actual[:, 1].any())
        self.assertGreater(int(actual[:, 5].sum()), 0)

    def test_thread_scheduling_does_not_change_seeded_results(self):
        def run(seed):
            return simulate(np.full(500, 15.0), [0.2,0.7,1.0], 0.2, 0.01, 0.02, seed)
        seeds = [416,417,418,419]
        serial = [run(s) for s in seeds]
        with ThreadPoolExecutor(max_workers=4) as pool:
            parallel = list(pool.map(run, seeds))
        for a,b in zip(serial, parallel):
            np.testing.assert_array_equal(a, b)


if __name__ == '__main__':
    unittest.main(verbosity=2)
