"""Exact inversion and finite-sample joint calibration/structure certificates.

No observed measurements are supplied to the certificate mode. Its finite
example is a worst-case confidence-set calculation at stated model parameters.
All proof calculations use the standard library and exact rational arithmetic.
"""
from __future__ import annotations

from fractions import Fraction as F
from pathlib import Path
from math import comb, factorial, isqrt
from decimal import Decimal, localcontext
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
WORKSPACE = ROOT.parent.parent
SOURCE = WORKSPACE / "science_completion/homogeneous_control/homogeneous_control_results.json"
SITE_COUNT = 63
INTENSITY_MAX = SITE_COUNT**2
SQRT_BITS = 220


def add(a, b, scale=F(1)):
    result = dict(a)
    for k, value in b.items():
        result[k] = result.get(k, F(0)) + scale*value
    return {k: v for k, v in result.items() if v}


def mul(a, b):
    result = {}
    for k, x in a.items():
        for j, y in b.items():
            result[k+j] = result.get(k+j, F(0)) + x*y
    return {k: v for k, v in result.items() if v}


def derivative(a):
    return {k-1: k*v for k, v in a.items() if k}


def evaluate(a, x):
    result = F(0)
    for k in range(max(a, default=0), -1, -1):
        result = result*x + a.get(k, F(0))
    return result


def divide_one_minus_x(a):
    result, last = {}, F(0)
    for k in range(max(a)):
        last += a.get(k, F(0))
        result[k] = last
    assert a[max(a)] == -last
    return {k: v for k, v in result.items() if v}


def interval(value):
    if isinstance(value, tuple):
        return value
    return F(value), F(value)


def ia(a, b):
    a, b = interval(a), interval(b)
    return a[0]+b[0], a[1]+b[1]


def im(a, b):
    a, b = interval(a), interval(b)
    products = [x*y for x in a for y in b]
    return min(products), max(products)


def iss(a, b):
    b = interval(b)
    return ia(a, (-b[1], -b[0]))


def ip(a, exponent):
    a = interval(a)
    assert a[0] >= 0 and exponent >= 0
    return a[0]**exponent, a[1]**exponent


def polynomial_interval(a, domain):
    result = (F(0), F(0))
    for k in range(max(a, default=0), -1, -1):
        result = ia(im(result, domain), a.get(k, F(0)))
    return result


def sqrt_bounds(q):
    q = F(q)
    assert q >= 0
    scale = 1 << SQRT_BITS
    integer = isqrt((q.numerator*scale*scale)//q.denominator)
    lo, hi = F(integer, scale), F(integer+1, scale)
    assert lo*lo <= q <= hi*hi
    return lo, hi


def falling(k, r):
    if k < r:
        return 0
    result = 1
    for j in range(r):
        result *= k-j
    return result


def nonnegative_integer(value, label):
    """Accept exact JSON integers or canonical decimal strings, never floats."""
    if type(value) is int and value >= 0:
        return value
    if isinstance(value, str) and re.fullmatch(r"0|[1-9][0-9]*", value):
        return int(value)
    raise ValueError(f"{label} must be a nonnegative integer or canonical decimal string.")


def load_moments():
    raw = json.loads(SOURCE.read_text())["intensity_moment_polynomials"]
    moments = {}
    for label in ("A", "B"):
        moments[label] = {}
        for order in range(5):
            row = raw[label][str(order)]
            assert all(int(k) % 2 == 0 for k in row)
            moments[label][order] = {int(k)//2: F(v) for k, v in row.items()}
    assert all(moments["A"][r] == moments["B"][r] for r in range(4))
    return moments


MOMENTS = load_moments()
M = MOMENTS["A"]
VARIANCE_POLY = add(M[2], mul(M[1], M[1]), -1)
THIRD_POLY = add(add(M[3], mul(M[2], M[1]), -3), mul(mul(M[1], M[1]), M[1]), 2)
V = divide_one_minus_x(divide_one_minus_x(VARIANCE_POLY))
C = divide_one_minus_x(divide_one_minus_x(divide_one_minus_x(THIRD_POLY)))
H = add({k: 2*v for k, v in mul(derivative(C), V).items()}, mul(C, derivative(V)), -3)


def q_ratio(x):
    return evaluate(C, x)**2/evaluate(V, x)**3


def inverse_q(target, iterations=160):
    if target <= q_ratio(F(0)):
        return F(0), F(0)
    if target >= q_ratio(F(1)):
        return F(1), F(1)
    lo, hi = F(0), F(1)
    for _ in range(iterations):
        mid = (lo+hi)/2
        if q_ratio(mid) < target:
            lo = mid
        else:
            hi = mid
    assert q_ratio(lo) <= target <= q_ratio(hi)
    return lo, hi


def factorial_moment(label, r, x, eta, background):
    return sum(F(comb(r, k))*background**(r-k)*eta**k*evaluate(MOMENTS[label][k], x)
               for k in range(r+1))


def factorial_moment_interval(label, r, x, eta, background):
    result = (F(0), F(0))
    for k in range(r+1):
        mu = polynomial_interval(MOMENTS[label][k], x)
        mu = max(F(0), mu[0]), min(F(INTENSITY_MAX**k), mu[1])
        assert mu[0] <= mu[1]
        term = im(ip(background, r-k), im(ip(eta, k), mu))
        result = ia(result, im(comb(r, k), term))
    return result


def infer(moment_intervals, rate_bound):
    """Return a conservative outer calibration set and surviving structures."""
    f1, f2, f3, f4 = [moment_intervals[r] for r in range(1, 5)]
    k2 = iss(f2, ip(f1, 2))
    k3 = ia(iss(f3, im(3, im(f2, f1))), im(2, ip(f1, 3)))
    base = {"factorial_cumulant_2": k2, "factorial_cumulant_3": k3}
    if k2[1] <= 0 or k3[1] <= 0:
        return {"status": "model_inconsistent", **base}
    if k2[0] <= 0:
        return {"status": "unresolved", "reason": "Second factorial cumulant lower bound is not positive.", **base}
    q = max(F(0), k3[0])**2/k2[1]**3, k3[1]**2/k2[0]**3
    if q[1] < q_ratio(F(0)) or q[0] > q_ratio(F(1)):
        return {"status": "model_inconsistent", "q": q, **base}
    x = inverse_q(q[0])[0], inverse_q(q[1])[1]
    v = evaluate(VARIANCE_POLY, x[1]), evaluate(VARIANCE_POLY, x[0])
    if v[1] <= 0:
        return {"status": "model_inconsistent", "x": x, **base}
    eta_lo = sqrt_bounds(k2[0]/v[1])[0]
    eta_hi = rate_bound/INTENSITY_MAX
    if v[0] > 0:
        eta_hi = min(eta_hi, sqrt_bounds(k2[1]/v[0])[1])
    if eta_lo > eta_hi:
        return {"status": "model_inconsistent", "x": x, **base}
    eta = eta_lo, eta_hi
    mu1 = evaluate(M[1], x[1]), evaluate(M[1], x[0])
    braw = iss(f1, im(eta, mu1))
    b = max(F(0), braw[0]), min(rate_bound, braw[1])
    if b[0] > b[1]:
        return {"status": "model_inconsistent", "x": x, "eta": eta, **base}
    predicted = {g: factorial_moment_interval(g, 4, x, eta, b) for g in ("A", "B")}
    survivors = [g for g, row in predicted.items() if max(row[0], f4[0]) <= min(row[1], f4[1])]
    return {"status": "identified" if len(survivors) == 1 else ("unresolved" if survivors else "model_inconsistent"),
            "structures": survivors, "x": x, "eta": eta, "background": b, "q": q,
            "predicted_factorial_fourth": predicted, **base}


def concentration_bounds(n_observations, rate_bound, cutoff=64, tail_order=32):
    assert n_observations > 0 and rate_bound > 0
    assert tail_order > 0
    assert cutoff >= 4+tail_order-1
    epsilon = sqrt_bounds(F(51, 20*n_observations))[1]
    tails = {r: rate_bound**(r+tail_order)/falling(cutoff+1-r, tail_order)
             for r in range(1, 5)}
    errors = {r: F(falling(cutoff, r))*epsilon for r in range(1, 5)}
    return epsilon, errors, tails


def confidence_intervals_from_histogram(histogram, rate_bound, cutoff=64, tail_order=32):
    histogram = {nonnegative_integer(k, "Count"): nonnegative_integer(v, "Multiplicity")
                 for k, v in histogram.items()}
    n_observations = sum(histogram.values())
    epsilon, errors, tails = concentration_bounds(n_observations, rate_bound, cutoff, tail_order)
    means = {r: F(sum(v*falling(k, r) for k, v in histogram.items() if k <= cutoff), n_observations)
             for r in range(1, 5)}
    intervals = {r: (max(F(0), means[r]-errors[r]),
                     min(rate_bound**r, means[r]+errors[r]+tails[r])) for r in range(1, 5)}
    if any(a > b for a, b in intervals.values()):
        return {"status": "model_inconsistent", "n": n_observations, "moment_intervals": intervals}
    return {"n": n_observations, "rate_bound": rate_bound, "cutoff": cutoff, "tail_order": tail_order,
            "epsilon": epsilon, "truncation_tail_bounds": tails,
            "moment_intervals": intervals, "inference": infer(intervals, rate_bound)}


def decimal(q, places=24):
    with localcontext() as ctx:
        ctx.prec = places
        return str(Decimal(q.numerator)/Decimal(q.denominator))


def jsonable(v):
    if isinstance(v, F):
        return str(v)
    if isinstance(v, dict):
        return {str(k): jsonable(x) for k, x in v.items()}
    if isinstance(v, (tuple, list)):
        return [jsonable(x) for x in v]
    return v


def finite_example():
    x, eta, background, bound = F(1, 4), F(1, 512), F(1, 100), F(8)
    assert background+eta*INTENSITY_MAX < bound
    records = {}
    for label in ("A", "B"):
        actual = {r: factorial_moment(label, r, x, eta, background) for r in range(1, 5)}
        attempts = []
        for exponent in range(30, 51, 2):
            observations = 10**exponent
            epsilon, errors, tails = concentration_bounds(observations, bound)
            # On the simultaneous concentration event, every data-derived
            # interval is contained in this population-centered envelope.
            envelope = {r: (max(F(0), actual[r]-2*errors[r]-tails[r]),
                            min(bound**r, actual[r]+2*errors[r]+tails[r])) for r in range(1, 5)}
            output = infer(envelope, bound)
            attempts.append({"power_of_ten_n": exponent, "status": output["status"],
                             "surviving_structures": output.get("structures", ["A", "B"])})
            if output["status"] == "identified" and output["structures"] == [label]:
                assert output["x"][0] <= x <= output["x"][1]
                assert output["eta"][0] <= eta <= output["eta"][1]
                assert output["background"][0] <= background <= output["background"][1]
                records[label] = {"sufficient_observations": str(observations),
                                  "exact_factorial_moments": actual,
                                  "worst_case_confidence_envelope": envelope,
                                  "inference_from_envelope": output,
                                  "parameter_interval_widths": {k: output[k][1]-output[k][0] for k in ("x", "eta", "background")},
                                  "width_decimals": {k: decimal(output[k][1]-output[k][0]) for k in ("x", "eta", "background")},
                                  "attempts": attempts, "tail_bounds": tails}
                break
        assert label in records, "No certified finite example in the searched powers."
    return {"x": x, "phase_variance": "2*log(2)", "eta": eta, "background": background,
            "known_rate_upper_bound": bound, "cutoff": 64, "tail_order": 32,
            "confidence": "At least 19/20 jointly for calibration intervals and the structural decision.",
            "data_status": "Analytic worst-case guarantee; no physical or simulated observed data are claimed.",
            "scope": "Unknown Gaussian-phase width, gain and background; only the specified phase family, geometry candidates, independence and rate upper bound are supplied to the procedure.",
            "models": records}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--histogram", type=Path,
                        help="JSON with histogram (count: multiplicity), lambda_max, optional cutoff and tail_order.")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.histogram:
        raw = json.loads(args.histogram.read_text())
        if type(raw["lambda_max"]) is not int and not isinstance(raw["lambda_max"], str):
            raise ValueError("lambda_max must be an exact integer or rational/decimal string.")
        result = confidence_intervals_from_histogram(raw["histogram"], F(raw["lambda_max"]),
                                                    nonnegative_integer(raw.get("cutoff", 64), "Cutoff"),
                                                    nonnegative_integer(raw.get("tail_order", 32), "Tail order"))
        result["coverage_scope"] = "At least 95% simultaneous coverage under the stated Gaussian-phase mixed-Poisson model, independent observations, and valid rate upper bound. An unresolved result is not a structural identification."
    else:
        expected_v = {0: F(3906), 1: F(126), 2: F(103987, 400)}
        expected_c = {0: F(476532), 1: F(46305), 2: F(945333, 10), 3: F(124102867, 40000),
                      4: F(311961, 200), 5: F(17164599, 160000), 6: F(5721533, 160000)}
        assert V == expected_v and C == expected_c
        assert set(H) == set(range(8)) and all(v > 0 for v in H.values())
        # V_I'(x)=(1-x)*[-2V+(1-x)V']; a power-coefficient upper bound is negative.
        variance_derivative_factor = add({k: -2*v for k, v in V.items()}, mul({0: F(1), 1: F(-1)}, derivative(V)))
        variance_derivative_upper = variance_derivative_factor[0] + sum(
            max(F(0), v) for k, v in variance_derivative_factor.items() if k)
        assert variance_derivative_upper < 0
        # The exact confidence constant: exp(51/10)>160 by a positive partial sum.
        exp_lower = sum(F(51, 10)**k/factorial(k) for k in range(20))
        assert exp_lower > 160
        gap = add(MOMENTS["A"][4], MOMENTS["B"][4], -1)
        expected_gap = {4: F(455015761, 20000)}
        for _ in range(5):
            expected_gap = mul(expected_gap, {0: F(1), 1: F(-1)})
        expected_gap = mul(expected_gap, {0: F(6), 1: F(6), 2: F(3), 3: F(1)})
        assert gap == expected_gap
        result = {"status": "PASS", "variance_reduced_polynomial": V,
                  "third_cumulant_reduced_polynomial": C,
                  "strict_monotonicity_polynomial_2CprimeV_minus_3CVprime": H,
                  "all_monotonicity_coefficients_strictly_positive": True,
                  "variance_derivative_reduced_factor": variance_derivative_factor,
                  "variance_derivative_reduced_factor_upper_bound_on_0_1": variance_derivative_upper,
                  "ratio_range_squared": [q_ratio(F(0)), q_ratio(F(1))],
                  "source_moment_file": str(SOURCE.relative_to(WORKSPACE)),
                  "source_moment_file_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                  "confidence_exp_lower_partial_sum": exp_lower,
                  "finite_example": finite_example(),
                  "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    output = args.output or ROOT/"calibration_certificate.json"
    output.write_text(json.dumps(jsonable(result), indent=2)+"\n")
    print(json.dumps({"status": result.get("status", "completed"), "output": str(output),
                      "finite_example_summary": {k: {"sufficient_observations": v["sufficient_observations"],
                                                       "width_decimals": v["width_decimals"]}
                                                 for k, v in result.get("finite_example", {}).get("models", {}).items()}}, indent=2))


if __name__ == "__main__":
    main()
