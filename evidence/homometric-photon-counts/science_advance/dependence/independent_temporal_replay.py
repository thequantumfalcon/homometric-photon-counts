"""Independent arithmetic replay of the temporal-dependence certificate.

No producer module is imported. This checks the retained inputs, all schedule
bounds, the full-space score moments and Cantelli sample integer. Independent
finite determinant/Hermite computations supplement the accompanying review.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import comb, factorial
import hashlib
import json
import sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OLD = ROOT/"science_frontier/tighter_testing/tighter_testing_certificate.json"
NEW = HERE/"temporal_dependence_certificate.json"
SOURCE = HERE/"certify_temporal_dependence.py"


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def moment(k):
    return 0 if k % 2 else factorial(k)//(2**(k//2)*factorial(k//2))


def mixed(p, q, rho):
    # Independent construction Y=rho X+sqrt(1-rho^2)Z; only even Z powers survive.
    return sum((Q(comb(q, 2*j))*rho**(q-2*j)*(1-rho*rho)**j
                *moment(p+q-2*j)*moment(2*j) for j in range(q//2+1)), Q(0))


def hermites(maximum):
    values = [{0: Q(1)}, {1: Q(1)}]
    for n in range(1, maximum):
        nxt = {k+1: v for k, v in values[n].items()}
        for k, v in values[n-1].items():
            nxt[k] = nxt.get(k, Q(0))-n*v
        values.append({k: v for k, v in nxt.items() if v})
    return values[:maximum+1]


def bareiss(matrix):
    # Fraction-free determinant recurrence, different from the producer's elimination.
    a = [list(row) for row in matrix]
    if len(a) == 1:
        return a[0][0]
    previous = Q(1)
    for k in range(len(a)-1):
        pivot = a[k][k]
        assert pivot != 0  # Positive-definite correlation matrices need no pivoting.
        for i in range(k+1, len(a)):
            for j in range(k+1, len(a)):
                a[i][j] = (a[i][j]*pivot-a[i][k]*a[k][j])/previous
        for i in range(k+1, len(a)):
            a[i][k] = 0
        previous = pivot
    return a[-1][-1]


def tv_squared(m, a, spacing):
    # Rewritten denominator avoids importing/copying the producer helper.
    return Q(31*(m-1), 2)/(a**(-2*spacing)-1)


def main():
    old, new = json.loads(OLD.read_text()), json.loads(NEW.read_text())
    assert new["input_sha256"] == digest(OLD) == "33d9ba4b07a859d6d84a28e3c8b47884c6e266b7098447f19840b634b43fc3e1"
    assert new["source_sha256"] == digest(SOURCE)
    assert new["model"]["effective_contrast_dimension"] == 62
    m0 = int(old["optimal_full_count_sample_bounds"]["impossible_through"])
    m1 = int(old["explicit_rational_score_test"]["sufficient_snapshots"])
    upper = Q(old["optimal_full_count_sample_bounds"]["necessary_endpoint_certificate"]["success"]["upper"])
    lower = Q(old["explicit_rational_score_test"]["success_certificate"]["success"]["lower"])
    goal, quantum = Q(19, 20), Q(1, 2**220)
    assert upper < goal < lower
    schedules = []
    for row in new["schedule_table"]:
        a, ell = Q(row["AR_coefficient_absolute_upper_bound"]), row["spacing_base_time_steps"]
        assert (1+a)/(1-a) == Q(row["all_observation_variance_inflation"])
        for m, field, margin in ((m0, "path_TV_upper_at_m0", goal-upper),
                                 (m1, "path_TV_upper_at_m1", lower-goal)):
            bound, exact_square = Q(row[field]), tv_squared(m, a, ell)
            assert bound >= 0 and bound*bound >= exact_square
            assert (bound-quantum)**2 <= exact_square
            assert exact_square < margin*margin and bound < margin
        if ell > 1:
            previous_works = (tv_squared(m0, a, ell-1) < (goal-upper)**2
                              and tv_squared(m1, a, ell-1) < (lower-goal)**2)
            assert not previous_works
        assert Q(row["optimal_success_upper_at_m0"]) == upper+Q(row["path_TV_upper_at_m0"]) < goal
        assert Q(row["specified_score_success_lower_at_m1"]) == lower-Q(row["path_TV_upper_at_m1"]) > goal
        assert int(row["raw_grid_span_inclusive"]) == ell*(m1-1)+1
        schedules.append({"a_max": str(a), "spacing": ell, "both_endpoints_pass": True,
                          "previous_spacing_fails_same_bound": True})
    # Recompute the complete unconditioned score moments with signed weights.
    score = new["consecutive_known_calibration_score"]
    weights = {int(k): Q(v) for k, v in old["explicit_rational_score_test"]["weights"].items()}
    means, variances = {}, {}
    for g in ("A", "B"):
        tail = Q(old["individual_tail_bounds"][g])
        p = old["conditional_probability_intervals"][g]
        low_terms, high_terms, square_terms = [], [], []
        for k in range(25):
            lo, hi = Q(p[str(k)]["lower"])*(1-tail), Q(p[str(k)]["upper"])
            assert 0 <= lo <= hi <= 1
            endpoints = sorted([lo*weights[k], hi*weights[k]])
            low_terms.append(endpoints[0]); high_terms.append(endpoints[1])
            square_terms.append(hi*weights[k]*weights[k])
        mu = sum(low_terms, Q(0)), sum(high_terms, Q(0))
        mu2low = Q(0) if mu[0] <= 0 <= mu[1] else min(q*q for q in mu)
        variance = sum(square_terms, Q(0))-mu2low
        record = score["statistics_and_per_geometry_success"][g]
        assert Q(record["mean_lower"]) == mu[0] and Q(record["mean_upper"]) == mu[1]
        assert Q(record["second_moment_upper"]) == sum(square_terms, Q(0))
        assert Q(record["variance_upper"]) == variance > 0
        means[g], variances[g] = mu, variance
    drift = (means["A"][0]-means["B"][1])/2
    threshold = (means["A"][0]+means["B"][1])/2
    assert drift > 0 and drift == Q(score["common_certified_drift_lower"])
    assert threshold == Q(score["per_observation_threshold"])
    n = int(score["sufficient_consecutive_observations"])
    kappa = Q(score["variance_inflation"])
    assert kappa == 3
    required = {}
    for g in ("A", "B"):
        x = 19*kappa*variances[g]/(drift*drift)
        needed = (x.numerator+x.denominator-1)//x.denominator
        required[g] = needed
        record = score["statistics_and_per_geometry_success"][g]
        assert int(record["sufficient_integer_for_this_hypothesis"]) == needed
        error = kappa*variances[g]/(kappa*variances[g]+n*drift*drift)
        assert error == Q(record["failure_probability_upper"]) <= Q(1, 20)
    assert n == max(required.values()) == 2372403589637318817
    # Independent finite checks of the identities used in the symbolic proof.
    det_checks = hermite_checks = inflation_checks = 0
    hs = hermites(8)
    for rho in (Q(0), Q(1, 2), Q(-2, 3), Q(4, 5)):
        for size in range(1, 11):
            matrix = [[rho**abs(i-j) for j in range(size)] for i in range(size)]
            assert bareiss(matrix) == (1-rho*rho)**(size-1)
            det_checks += 1
        for p in range(9):
            for q in range(9):
                value = sum((a*b*mixed(i, j, rho) for i, a in hs[p].items()
                             for j, b in hs[q].items()), Q(0))
                assert value == (factorial(p)*rho**p if p == q else 0)
                hermite_checks += 1
    for a in (Q(0), Q(1, 4), Q(1, 2), Q(3, 4), Q(9, 10)):
        for size in (1, 2, 3, 10, 51):
            weighted_sum = ((size-1)*a-size*a*a+a**(size+1))/(size*(1-a)**2)
            assert 1+2*weighted_sum <= (1+a)/(1-a)
            inflation_checks += 1
    result = {"status": "PASS", "scope": "Independent exact arithmetic replay; no producer imports, no observations, no simulation.",
              "schedules": schedules, "consecutive_each_geometry_95_percent_count": str(n),
              "independent_determinants": det_checks, "independent_Hermite_checks": hermite_checks,
              "independent_variance_inflation_checks": inflation_checks,
              "input_sha256": digest(OLD), "certificate_sha256": digest(NEW),
              "producer_sha256": digest(SOURCE), "replay_sha256": digest(Path(__file__))}
    target = HERE/"independent_temporal_replay.json"
    target.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"status": result["status"], "output": str(target),
                      "consecutive_count": str(n), "finite_identity_checks": det_checks+hermite_checks+inflation_checks}, indent=2))


if __name__ == "__main__":
    main()
