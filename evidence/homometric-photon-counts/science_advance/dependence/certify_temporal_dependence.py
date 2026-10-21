#!/usr/bin/env python3
"""Exact arithmetic certificates for the specified Gaussian AR(1) extension.

This program uses no simulation and does not generate physical observations.
The analytic path-KL and Hermite proofs are in temporal_dependence_proofs.txt.
Run from any working directory; output is beside this script by default.
"""

from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
from fractions import Fraction as F
from hashlib import sha256
from math import comb, factorial, isqrt
from pathlib import Path
import json
import sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
INPUT = ROOT / "science_frontier/tighter_testing/tighter_testing_certificate.json"
INPUT_SHA = "33d9ba4b07a859d6d84a28e3c8b47884c6e266b7098447f19840b634b43fc3e1"
DIM = 62
TARGET = F(19, 20)
BITS = 220


def rat(value: F | int) -> str:
    return str(F(value))


def decimal(value: F, digits: int = 40) -> str:
    with localcontext() as ctx:
        ctx.prec = digits
        return str(Decimal(value.numerator) / Decimal(value.denominator))


def sqrt_bounds(value: F) -> tuple[F, F]:
    assert value >= 0
    scale = 1 << BITS
    low_int = isqrt((value.numerator * scale * scale) // value.denominator)
    low, high = F(low_int, scale), F(low_int + 1, scale)
    assert low * low <= value <= high * high
    return low, high


def tv_square_upper(m: int, a_max: F, spacing: int) -> F:
    """Pinsker plus -log(1-u)<=u/(1-u), all exact rationals."""
    assert m >= 1 and 0 <= a_max < 1 and spacing >= 1
    r2 = a_max ** (2 * spacing)
    return F(DIM * (m - 1), 4) * r2 / (1 - r2)


def determinant(matrix: list[list[F]]) -> F:
    work = [list(row) for row in matrix]
    answer = F(1)
    for j in range(len(work)):
        pivot = next((i for i in range(j, len(work)) if work[i][j]), None)
        if pivot is None:
            return F(0)
        if pivot != j:
            work[pivot], work[j] = work[j], work[pivot]
            answer = -answer
        diag = work[j][j]
        answer *= diag
        for i in range(j + 1, len(work)):
            ratio = work[i][j] / diag
            for k in range(j + 1, len(work)):
                work[i][k] -= ratio * work[j][k]
            work[i][j] = F(0)
    return answer


def normal_moment(order: int) -> int:
    if order % 2:
        return 0
    return factorial(order) // (2 ** (order // 2) * factorial(order // 2))


def joint_normal_moment(p: int, q: int, rho: F) -> F:
    # Wick pairings: choose k cross-pairs, then pair the remaining X and Y.
    return sum(
        (F(comb(p, k) * comb(q, k) * factorial(k)
           * normal_moment(p - k) * normal_moment(q - k)) * rho ** k
         for k in range(min(p, q) + 1)),
        F(0),
    )


def hermite_coeffs(order: int) -> dict[int, F]:
    # Probabilists' Hermite polynomial.
    return {
        order - 2 * k: F((-1) ** k * factorial(order),
                        factorial(k) * factorial(order - 2 * k) * 2 ** k)
        for k in range(order // 2 + 1)
    }


def checks() -> dict:
    det_checks = 0
    for rho in (F(0), F(1, 2), F(-2, 3), F(4, 5)):
        for m in range(1, 11):
            matrix = [[rho ** abs(i - j) for j in range(m)] for i in range(m)]
            assert determinant(matrix) == (1 - rho * rho) ** (m - 1)
            det_checks += 1
    hermite_checks = 0
    for rho in (F(0), F(1, 2), F(-2, 3), F(4, 5)):
        for p in range(9):
            for q in range(9):
                actual = sum(
                    (u * v * joint_normal_moment(i, j, rho)
                     for i, u in hermite_coeffs(p).items()
                     for j, v in hermite_coeffs(q).items()),
                    F(0),
                )
                expected = F(factorial(p)) * rho ** p if p == q else F(0)
                assert actual == expected
                hermite_checks += 1
    # The exact finite-m variance inflation is bounded by the geometric sum.
    inflation_checks = 0
    for a in (F(0), F(1, 4), F(1, 2), F(3, 4), F(9, 10)):
        for m in (1, 2, 3, 10, 51):
            actual = 1 + 2 * sum((F(m - k, m) * a ** k
                                  for k in range(1, m)), F(0))
            assert actual <= (1 + a) / (1 - a)
            inflation_checks += 1
    return {
        "exact_AR1_determinant_checks": det_checks,
        "exact_Hermite_covariance_checks": hermite_checks,
        "finite_variance_inflation_checks": inflation_checks,
        "scope": "Finite checks supplement the symbolic proofs; they are not proofs for all dimensions or degrees.",
    }


def consecutive_score_certificate(old: dict, a_max: F) -> dict:
    """A second design: no thinning, separate 95% under each geometry."""
    weights = {int(k): F(v) for k, v in old["explicit_rational_score_test"]["weights"].items()}
    assert set(weights) == set(range(25))
    stats = {}
    for geometry in ("A", "B"):
        tail = F(old["individual_tail_bounds"][geometry])
        mean_lo, mean_hi, second_hi = F(0), F(0), F(0)
        for k in range(25):
            conditional = old["conditional_probability_intervals"][geometry][str(k)]
            # p(k)=R(k)*(1-tau); 0<=tau<=tail. The tail score itself is zero.
            lower = F(conditional["lower"]) * (1 - tail)
            upper = F(conditional["upper"])
            terms = (lower * weights[k], upper * weights[k])
            mean_lo += min(terms)
            mean_hi += max(terms)
            second_hi += upper * weights[k] ** 2
        square_lower = (F(0) if mean_lo <= 0 <= mean_hi
                        else min(mean_lo * mean_lo, mean_hi * mean_hi))
        variance_upper = second_hi - square_lower
        assert variance_upper > 0
        stats[geometry] = {
            "mean_lower": mean_lo, "mean_upper": mean_hi,
            "second_moment_upper": second_hi, "variance_upper": variance_upper,
        }
    threshold = (stats["A"]["mean_lower"] + stats["B"]["mean_upper"]) / 2
    drift = (stats["A"]["mean_lower"] - stats["B"]["mean_upper"]) / 2
    assert drift > 0
    kappa = (1 + a_max) / (1 - a_max)
    ratios = {g: 19 * kappa * stats[g]["variance_upper"] / (drift * drift)
              for g in stats}
    required = {g: -(-value.numerator // value.denominator) for g, value in ratios.items()}
    m = max(required.values())
    result_stats = {}
    for geometry, values in stats.items():
        v = kappa * values["variance_upper"]
        error = v / (v + m * drift * drift)
        assert error <= F(1, 20)
        result_stats[geometry] = {
            **{name: rat(value) for name, value in values.items()},
            "mean_lower_decimal": decimal(values["mean_lower"]),
            "mean_upper_decimal": decimal(values["mean_upper"]),
            "variance_upper_decimal": decimal(values["variance_upper"]),
            "sufficient_integer_for_this_hypothesis": str(required[geometry]),
            "failure_probability_upper": rat(error),
            "success_probability_lower_decimal": decimal(1 - error),
        }
    return {
        "AR_coefficient_absolute_upper_bound": rat(a_max),
        "variance_inflation": rat(kappa),
        "sufficient_consecutive_observations": str(m),
        "base_grid_span_inclusive": str(m),
        "count_score": "Use the 25 rational weights in the pinned iid certificate for N<=24; define score zero for N>24.",
        "per_observation_threshold": rat(threshold),
        "common_certified_drift_lower": rat(drift),
        "decision": "Choose A if the sum of all m scores is >=m*threshold; otherwise choose B.",
        "statistics_and_per_geometry_success": result_stats,
        "meaning": "At least 95% success under EACH geometry, uniformly over the stated AR coefficient range.",
        "not_claimed_optimal": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "temporal_dependence_certificate.json")
    args = parser.parse_args()
    raw = INPUT.read_bytes()
    assert sha256(raw).hexdigest() == INPUT_SHA, "Preserved iid input hash mismatch"
    old = json.loads(raw)
    bounds = old["optimal_full_count_sample_bounds"]
    score = old["explicit_rational_score_test"]
    m0 = int(bounds["impossible_through"])
    m1 = int(score["sufficient_snapshots"])
    upper_iid = F(bounds["necessary_endpoint_certificate"]["success"]["upper"])
    lower_iid = F(score["success_certificate"]["success"]["lower"])
    assert upper_iid < TARGET < lower_iid
    margin0, margin1 = TARGET - upper_iid, lower_iid - TARGET

    def passes(a: F, spacing: int) -> bool:
        return (tv_square_upper(m0, a, spacing) < margin0 * margin0
                and tv_square_upper(m1, a, spacing) < margin1 * margin1)

    rows = []
    for a in (F(1, 4), F(1, 2), F(3, 4), F(9, 10), F(99, 100)):
        high = 1
        while not passes(a, high):
            high *= 2
        low = 0
        while high - low > 1:
            mid = (high + low) // 2
            if passes(a, mid):
                high = mid
            else:
                low = mid
        ell = high
        assert passes(a, ell)
        if ell > 1:
            assert not passes(a, ell - 1)
        deltas = [sqrt_bounds(tv_square_upper(m, a, ell))[1] for m in (m0, m1)]
        upper_dep, lower_dep = upper_iid + deltas[0], lower_iid - deltas[1]
        assert upper_dep < TARGET < lower_dep
        rows.append({
            "AR_coefficient_absolute_upper_bound": rat(a),
            "spacing_base_time_steps": ell,
            "smallest_spacing_for_this_two_endpoint_bound": True,
            "not_claimed_minimal_physical_spacing": True,
            "retained_sufficient_observations": str(m1),
            "raw_grid_span_inclusive": str(ell * (m1 - 1) + 1),
            "unobserved_intermediate_slots_need_not_be_recorded": True,
            "path_TV_upper_at_m0": rat(deltas[0]),
            "path_TV_upper_at_m1": rat(deltas[1]),
            "path_TV_upper_at_m1_decimal": decimal(deltas[1]),
            "optimal_success_upper_at_m0": rat(upper_dep),
            "optimal_success_upper_at_m0_decimal": decimal(upper_dep),
            "specified_score_success_lower_at_m1": rat(lower_dep),
            "specified_score_success_lower_at_m1_decimal": decimal(lower_dep),
            "all_observation_variance_inflation": rat((1 + a) / (1 - a)),
        })

    result = {
        "schema": "specified-gaussian-temporal-dependence-v1",
        "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "input_path": str(INPUT.relative_to(ROOT)),
        "input_sha256": INPUT_SHA,
        "model": {
            "sites": 63, "effective_contrast_dimension": DIM,
            "phase_process": "theta[t+1]=a*theta[t]+sqrt(s*(1-a^2))*epsilon[t+1], stationary N(0,s Id63)",
            "innovation_independence": "independent standard Gaussian coordinates and times",
            "detector": "conditionally independent Poisson(b+eta I[t]) given the entire phase path",
            "coefficient": "common across sites, fixed over time, |a|<=a_max<1",
            "known_testing_point": {"s": "2 log 2", "eta": "1/512", "b": "0"},
        },
        "path_comparison": {
            "exact_KL": "-62*(m-1)*log(1-a^(2 ell))/2",
            "TV_upper": "min(1, sqrt(62*(m-1)*[-log(1-a^(2 ell))])/2)",
            "rational_TV_square_upper": "62*(m-1)*a_max^(2 ell)/(4*(1-a_max^(2 ell)))",
            "distances_compare": "one geometry's dependent full count record versus its iid full count record",
            "full_count_tails": "already included in the pinned iid endpoint input; no counts discarded by this transfer",
        },
        "sample_interval_for_each_listed_thinned_experiment": {
            "target_equal_prior_average_success": rat(TARGET),
            "necessary_at_least": str(m0 + 1),
            "sufficient": str(m1),
            "lower_bound_scope": "fixed same AR coefficient under A/B; even a rule that knows it cannot succeed at m0",
            "upper_bound_scope": "existing rational iid score works uniformly over |a|<=a_max at stated spacing",
            "iid_necessary_margin": rat(margin0),
            "iid_sufficient_margin": rat(margin1),
            "exact_optimal_integer_determined": False,
        },
        "schedule_table": rows,
        "variance_transfer": {
            "factor": "kappa=(1+a_max)/(1-a_max)",
            "general_bound": "Var(m^-1 sum Z[t]) <= kappa Var(Z[1])/m",
            "conditional_mean_refinement": "Var(mean Z) <= [E Var(Z|theta)+kappa Var(E[Z|theta])]/m",
            "first_count_at_common_null": "Var(mean N) <= [E Lambda+((1+a_max^2)/(1-a_max^2))*Var Lambda]/m",
            "at_a_max_half": "3",
            "fixed_group_Chebyshev_transfer": "Multiplying each prespecified group's iid size by 3, and using inflation=3 in its confidence radii, preserves every iid radius and unconditional union bound. Independence between the groups is not required.",
        },
        "consecutive_known_calibration_score": consecutive_score_certificate(old, F(1, 2)),
        "finite_exact_checks": checks(),
        "limits": [
            "No physical data or simulated observations are used.",
            "These results require a specified stationary Gaussian AR process and independent conditional detector emissions.",
            "An empirical autocorrelation point estimate does not establish the required upper bound on |a|.",
            "The spacing is sufficient for this transfer certificate, not proved globally optimal.",
            "No guarantee for arbitrary temporal dependence is asserted.",
            "The appended no-thinning moment transfer is a variance inequality, not a Berry-Esseen theorem for unthinned scores.",
        ],
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"output": str(args.output), "status": "all exact checks passed",
                      "consecutive_95_percent_each_geometry": result["consecutive_known_calibration_score"]["sufficient_consecutive_observations"],
                      "schedules": [{k: row[k] for k in ("AR_coefficient_absolute_upper_bound", "spacing_base_time_steps", "path_TV_upper_at_m1_decimal", "specified_score_success_lower_at_m1_decimal")} for row in rows]}, indent=2))


if __name__ == "__main__":
    main()
