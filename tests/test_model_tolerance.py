"""Check the robust certificate and its probability-box optimization boundary."""

from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from check_model_tolerance import certificate, simplex_max  # noqa: E402


class ModelTolerance(unittest.TestCase):
    def test_retained_experiment_has_the_documented_budget(self):
        result = certificate()
        self.assertEqual(Q(result["conditional_tv_tolerance"]), Q(3, 10**9))
        self.assertEqual(result["observations_sufficient"], 204799753446338)

    def test_optimizer_matches_independent_vertex_enumeration(self):
        bounds = [(Q(1, 10), Q(1, 2)), (Q(1, 5), Q(3, 5)), (Q(0), Q(1, 2))]
        values = [Q(-7), Q(2), Q(-1)]
        vertices = []
        for free in range(3):
            fixed = [i for i in range(3) if i != free]
            for endpoints in product(*[bounds[i] for i in fixed]):
                point = dict(zip(fixed, endpoints))
                point[free] = 1 - sum(endpoints)
                if bounds[free][0] <= point[free] <= bounds[free][1]:
                    vertices.append(sum(point[i] * values[i] for i in range(3)))
        self.assertEqual(simplex_max(bounds, values), max(vertices))

    def test_infeasible_and_reversed_boxes_are_rejected(self):
        for bounds in [[(Q(3, 4), Q(1))] * 2, [(Q(0), Q(1, 4))] * 2, [(Q(1), Q(0))] * 2]:
            with self.subTest(bounds=bounds), self.assertRaises(ValueError):
                simplex_max(bounds, [Q(1), Q(-1)])


if __name__ == "__main__":
    unittest.main()
