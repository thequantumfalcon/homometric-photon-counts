"""Variance-based, guarded joint calibration and structural identification.

All certificates use exact rational arithmetic. The default run certifies an
analytic finite-sample guarantee; it is not an observed or simulated dataset.
The histogram mode accepts three prespecified groups of observed counts.
"""
from __future__ import annotations

from fractions import Fraction as F
from pathlib import Path
from math import comb, factorial
import argparse
import hashlib
import importlib.util
import json

HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parent.parent
BASE_PATH = WORKSPACE / "science_frontier/calibration/certify_calibration.py"
FIXED_PATH = WORKSPACE / "science_extension/finite_detection/fixed_t_moments.json"
BASE_SHA = "d6c22ba84f56826a0c9d9783d2df6221ac37e2adc2132d1605c21ef11fa46de7"
FIXED_SHA = "538aee114c16e712496fe526486e6ac96ef344d2ff92e6d3014f7f47223feb32"
assert hashlib.sha256(BASE_PATH.read_bytes()).hexdigest() == BASE_SHA
assert hashlib.sha256(FIXED_PATH.read_bytes()).hexdigest() == FIXED_SHA
spec = importlib.util.spec_from_file_location("retained_calibration", BASE_PATH)
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)

N_SITES, M = 63, 3969
BACKGROUND_CAP = F(1, 8)
LOCAL = {"x": (F(249, 1000), F(251, 1000)),
         "eta": (F(195, 100000), F(196, 100000)),
         "background": (F(9, 1000), F(11, 1000))}
ALPHA_PILOT = F(1, 200)
ALPHA_CALIBRATION_PER_MOMENT = F(1, 200)
ALPHA_MAIN_PER_MOMENT = F(3, 400)
TOTAL_FAILURE = ALPHA_PILOT + 3*ALPHA_CALIBRATION_PER_MOMENT + 4*ALPHA_MAIN_PER_MOMENT
assert TOTAL_FAILURE == F(1, 20)


def divide(a, b):
    a, b = old.interval(a), old.interval(b)
    assert b[0] > 0
    return old.im(a, (1/b[1], 1/b[0]))


def abs_upper(a):
    return max(abs(v) for v in a)


def subset(a, b):
    return b[0] <= a[0] <= a[1] <= b[1]


def nth_root_upper(q, power, scale=10**6):
    """Small rational upper root, certified by an integer-power comparison."""
    q = F(q)
    assert q >= 0 and power > 0
    lo, hi = 0, scale
    while F(hi, scale)**power < q:
        hi *= 2
    while hi-lo > 1:
        mid = (lo+hi)//2
        if F(mid, scale)**power >= q:
            hi = mid
        else:
            lo = mid
    result = F(hi, scale)
    assert result**power >= q
    return result


def uniform_intensity_bounds():
    """No-singleton set partitions for centered independent site phasors."""
    partitions = {(0, 0): 1}
    for a in range(1, 17):
        for k in range(a//2+1):
            partitions[a, k] = (k*partitions.get((a-1, k), 0)
                                +(a-1)*partitions.get((a-2, k-1), 0))
    result = {0: F(1)}
    for r in range(1, 9):
        result[r] = sum(F(old.falling(N_SITES, k)*partitions.get((2*r, k), 0)
                          *2**(2*r-2*k)) for k in range(1, r+1))
    return result, {f"{a},{k}": value for (a, k), value in partitions.items()}


def local_intensity_bounds():
    """Couple to x0=1/4; bound L^(2r) norms by Minkowski and Gaussian moments."""
    fixed = json.loads(FIXED_PATH.read_text())["moments"]
    raw = json.loads(old.SOURCE.read_text())["intensity_moment_polynomials"]
    x0 = F(1, 4)
    # exp(1) < this rational upper bound < 3, so -log(x)>1 on LOCAL[x].
    exp_one_upper = sum(F(1, factorial(k)) for k in range(10)) + F(11, 10*factorial(10))
    assert exp_one_upper < 3 and LOCAL["x"][1] < F(1, 3)
    sigma_difference = max(abs(t-x0) for t in LOCAL["x"])/(2*LOCAL["x"][0])
    assert sigma_difference == F(1, 498)
    result, details = {0: F(1)}, {}
    for r in range(1, 9):
        reference = max(F(fixed[g][str(r)]) for g in ("A", "B"))
        gaussian_even = F(factorial(2*r), 2**r*factorial(r))
        amplitude_norm = nth_root_upper(reference, 2*r)
        gaussian_norm = nth_root_upper(gaussian_even, 2*r)
        minkowski = (amplitude_norm+N_SITES*sigma_difference*gaussian_norm)**(2*r)
        options = [minkowski]
        polynomial_upper = None
        if r <= 5:
            polynomials = [{int(k)//2: F(v) for k, v in raw[g][str(r)].items()}
                           for g in ("A", "B")]
            assert all(int(k) % 2 == 0 for g in ("A", "B") for k in raw[g][str(r)])
            polynomial_upper = max(old.polynomial_interval(p, LOCAL["x"])[1] for p in polynomials)
            options.append(polynomial_upper)
        result[r] = min(options)
        details[r] = {"maximum_reference_intensity_moment": reference,
                      "normal_even_moment": gaussian_even,
                      "reference_amplitude_norm_upper": amplitude_norm,
                      "normal_norm_upper": gaussian_norm,
                      "minkowski_intensity_moment_upper": minkowski,
                      "retained_polynomial_upper": polynomial_upper,
                      "chosen_upper": result[r]}
    return result, {"exp_one_upper": exp_one_upper,
                    "phase_standard_deviation_difference_upper": sigma_difference,
                    "moments": details}


def count_variance_bounds(intensity_bounds, b_upper, eta_upper):
    factorial_upper = {r: sum(F(comb(r, k))*b_upper**(r-k)*eta_upper**k*intensity_bounds[k]
                              for k in range(r+1)) for r in range(9)}
    # (n)_r^2 = sum_j binom(r,j)^2 j! (n)_(2r-j).
    variances = {r: sum(F(comb(r, j)**2*factorial(j))*factorial_upper[2*r-j]
                        for j in range(r+1)) for r in range(1, 5)}
    return variances, factorial_upper


UNIFORM, PARTITIONS = uniform_intensity_bounds()
LOCAL_MOMENTS, LOCAL_DETAILS = local_intensity_bounds()
LOCAL_VARIANCE, LOCAL_FACTORIAL = count_variance_bounds(
    LOCAL_MOMENTS, LOCAL["background"][1], LOCAL["eta"][1])


def fourth_reduced_polynomials():
    result, derivative_numerators = {}, {}
    for g in ("A", "B"):
        p = old.MOMENTS[g]
        raw = old.add(old.add(old.add(old.add(p[4], old.mul(p[3], p[1]), -4),
                                      old.mul(p[2], p[2]), -3),
                              old.mul(p[2], old.mul(p[1], p[1])), 12),
                      old.mul(old.mul(p[1], p[1]), old.mul(p[1], p[1])), -6)
        for _ in range(4):
            raw = old.divide_one_minus_x(raw)
        result[g] = raw
        derivative_numerators[g] = old.mul(old.V, old.add(
            old.mul(old.derivative(raw), old.V), old.mul(raw, old.derivative(old.V)), -2))
    return result, derivative_numerators


S4, J_NUMERATOR = fourth_reduced_polynomials()


def calibration_box(first_three, rate_bound):
    intervals = dict(first_three)
    intervals[4] = (F(0), rate_bound**4)
    result = old.infer(intervals, rate_bound)
    required = ("x", "eta", "background", "factorial_cumulant_2", "factorial_cumulant_3", "q")
    if any(k not in result for k in required):
        return None
    return {k: result[k] for k in required}


def derivative_bounds(label, first_three, box):
    """Bound the gradient of the profiled raw fourth factorial moment."""
    f1, f2, f3 = (first_three[r] for r in range(1, 4))
    c2, c3, x = box["factorial_cumulant_2"], box["factorial_cumulant_3"], box["x"]
    if c2[0] <= 0 or c3[0] <= 0:
        return None
    if not (old.q_ratio(F(0)) < box["q"][0] <= box["q"][1] < old.q_ratio(F(1))):
        return None
    v = old.polynomial_interval(old.V, x)
    r4 = divide(old.polynomial_interval(S4[label], x), old.ip(v, 2))
    jacobian_ratio = divide(old.polynomial_interval(J_NUMERATOR[label], x),
                            old.im(old.polynomial_interval(old.C, x), old.polynomial_interval(old.H, x)))
    c_ratio = divide(c3, c2)
    aa = old.iss(old.im(2, old.im(c2, r4)),
                 old.im(3, old.im(old.ip(c_ratio, 2), jacobian_ratio)))
    bb = old.im(2, old.im(c_ratio, jacobian_ratio))
    d1 = old.ia(old.iss(old.ia(old.im(4, f3), old.im(24, old.ip(f1, 3))),
                         old.im(24, old.im(f2, f1))),
                old.ia(old.im(-2, old.im(f1, aa)),
                       old.im(bb, old.ia(old.im(-3, f2), old.im(6, old.ip(f1, 2))))))
    d2 = old.ia(old.iss(old.im(6, f2), old.im(12, old.ip(f1, 2))),
                old.iss(aa, old.im(3, old.im(f1, bb))))
    d3 = old.ia(old.im(4, f1), bb)
    return {"derivative_intervals": {1: d1, 2: d2, 3: d3},
            "absolute_derivative_bounds": {r: abs_upper(v) for r, v in enumerate((d1, d2, d3), 1)}}


def center_rounding_bound(label, rate_bound):
    """Uniform width of the finite-bisection center evaluation, <=160-bit formula."""
    p = S4[label]
    l_s = sum(k*abs(v) for k, v in p.items())
    a_s = sum(abs(v) for v in p.values())
    v_min, v_max = old.evaluate(old.V, F(0)), old.evaluate(old.V, F(1))
    l_v = sum(k*abs(v) for k, v in old.V.items())
    return rate_bound**4*(l_s/v_min**2+2*a_s*v_max*l_v/v_min**4)/2**160


def profiled_fourth_prediction(label, first_three, box):
    derivative = derivative_bounds(label, first_three, box)
    if derivative is None:
        return None
    mids = {r: sum(first_three[r])/2 for r in range(1, 4)}
    radii = {r: (first_three[r][1]-first_three[r][0])/2 for r in range(1, 4)}
    f1, f2, f3 = (mids[r] for r in range(1, 4))
    c2, c3 = f2-f1**2, f3-3*f2*f1+2*f1**3
    x_mid = old.inverse_q(c3**2/c2**3)
    r_mid = divide(old.polynomial_interval(S4[label], x_mid),
                   old.ip(old.polynomial_interval(old.V, x_mid), 2))
    center = old.ia(old.im(c2**2, r_mid), 4*f3*f1+3*f2**2-12*f2*f1**2+6*f1**4)
    enlargement = sum(derivative["absolute_derivative_bounds"][r]*radii[r] for r in range(1, 4))
    return {"interval": (center[0]-enlargement, center[1]+enlargement),
            "center_interval": center, "enlargement": enlargement, **derivative}


def final_inference(moment_intervals, rate_bound):
    box = calibration_box({r: moment_intervals[r] for r in range(1, 4)}, rate_bound)
    if box is None:
        return {"status": "unresolved", "reason": "Calibration rectangle does not yet give an interior inverse."}
    predictions = {g: profiled_fourth_prediction(g, moment_intervals, box) for g in ("A", "B")}
    if any(v is None for v in predictions.values()):
        return {"status": "unresolved", "reason": "Moment rectangle is not wholly inside the smooth inverse domain.",
                "calibration_box": box}
    f4 = moment_intervals[4]
    survivors = [g for g in ("A", "B")
                 if max(predictions[g]["interval"][0], f4[0]) <= min(predictions[g]["interval"][1], f4[1])]
    return {"status": "identified" if len(survivors) == 1 else ("unresolved" if survivors else "model_inconsistent"),
            "structures": survivors, "calibration_box": box, "profiled_fourth_predictions": predictions}


def radius(variance_upper, alpha, n, inflation=F(1)):
    assert variance_upper >= 0 and 0 < alpha < 1 and n > 0 and inflation >= 1
    return old.sqrt_bounds(inflation*variance_upper/(alpha*n))[1]


def histogram_means(histogram, orders):
    h = {old.nonnegative_integer(k, "Count"): old.nonnegative_integer(v, "Multiplicity")
         for k, v in histogram.items()}
    n = sum(h.values())
    if n <= 0:
        raise ValueError("Each prespecified group must contain at least one observation.")
    return n, {r: F(sum(v*old.falling(k, r) for k, v in h.items()), n) for r in orders}


def confidence_intervals(means, errors, rate_bound):
    result = {r: (max(F(0), means[r]-errors[r]), min(rate_bound**r, means[r]+errors[r])) for r in means}
    return None if any(a > b for a, b in result.values()) else result


def infer_histograms(raw):
    def rational(value, label):
        if type(value) is not int and not isinstance(value, str):
            raise ValueError(f"{label} must be an exact integer or rational/decimal string.")
        return F(value)
    bound = rational(raw["lambda_max"], "lambda_max")
    if bound <= 0:
        raise ValueError("lambda_max must be positive.")
    a0 = raw.get("ar1_abs_bound")
    inflation = F(1)
    if a0 is not None:
        a0 = rational(a0, "ar1_abs_bound")
        if not 0 <= a0 < 1:
            raise ValueError("ar1_abs_bound must be in [0,1).")
        inflation = (1+a0)/(1-a0)
    n0, mean0 = histogram_means(raw["pilot_histogram"], [1])
    n1, mean1 = histogram_means(raw["calibration_histogram"], [1, 2, 3])
    n2, mean2 = histogram_means(raw["main_histogram"], [1, 2, 3, 4])
    e0 = radius(bound+bound**2/4, ALPHA_PILOT, n0, inflation)
    out = {"group_sizes": [n0, n1, n2], "variance_inflation": inflation,
           "ar1_abs_bound": a0, "rate_upper_bound": bound,
           "pilot_mean_upper": mean0[1]+e0, "pilot_radius": e0,
           "coverage": "At least 95% unconditional joint coverage/decision control under the stated model and prespecified groups."}
    if mean0[1]+e0 > BACKGROUND_CAP:
        return {**out, "status": "unresolved", "reason": "Pilot did not certify the internal background cap; no parameter values are excluded."}
    coarse_v, _ = count_variance_bounds(UNIFORM, BACKGROUND_CAP, bound/M)
    e1 = {r: radius(coarse_v[r], ALPHA_CALIBRATION_PER_MOMENT, n1, inflation) for r in range(1, 4)}
    ci1 = confidence_intervals(mean1, e1, bound)
    box1 = calibration_box(ci1, bound) if ci1 is not None else None
    out.update({"calibration_moment_intervals": ci1, "calibration_radii": e1, "pilot_calibration_box": box1})
    if box1 is None or not all(subset(box1[k], LOCAL[k]) for k in LOCAL):
        return {**out, "status": "unresolved", "reason": "Pilot calibration did not certify the fixed local design box; no final parameter exclusions are reported."}
    e2 = {r: radius(LOCAL_VARIANCE[r], ALPHA_MAIN_PER_MOMENT, n2, inflation) for r in range(1, 5)}
    ci2 = confidence_intervals(mean2, e2, bound)
    out.update({"main_moment_intervals": ci2, "main_radii": e2})
    if ci2 is None:
        return {**out, "status": "model_inconsistent"}
    return {**out, **final_inference(ci2, bound)}


def finite_certificate():
    bound, x, eta, b = F(8), F(1, 4), F(1, 512), F(1, 100)
    n0, n1, n2 = 10**10, 10**18, 10**20
    assert b+eta*M < bound and all(LOCAL[k][0] < v < LOCAL[k][1]
                                 for k, v in (("x", x), ("eta", eta), ("background", b)))
    actual = {g: {r: old.factorial_moment(g, r, x, eta, b) for r in range(1, 5)} for g in ("A", "B")}
    assert all(actual["A"][r] == actual["B"][r] for r in range(1, 4))
    e0 = radius(bound+bound**2/4, ALPHA_PILOT, n0)
    pilot_margin = BACKGROUND_CAP-actual["A"][1]-2*e0
    assert pilot_margin > 0
    coarse_v, coarse_factorial = count_variance_bounds(UNIFORM, BACKGROUND_CAP, bound/M)
    e1 = {r: radius(coarse_v[r], ALPHA_CALIBRATION_PER_MOMENT, n1) for r in range(1, 4)}
    envelope1 = {r: (actual["A"][r]-2*e1[r], actual["A"][r]+2*e1[r]) for r in range(1, 4)}
    assert all(a > 0 and z < bound**r for r, (a, z) in envelope1.items())
    box1 = calibration_box(envelope1, bound)
    assert box1 is not None and all(subset(box1[k], LOCAL[k]) for k in LOCAL)
    e2 = {r: radius(LOCAL_VARIANCE[r], ALPHA_MAIN_PER_MOMENT, n2) for r in range(1, 5)}
    envelope2 = {r: (actual["A"][r]-2*e2[r], actual["A"][r]+2*e2[r]) for r in range(1, 4)}
    assert all(a > 0 and z < bound**r for r, (a, z) in envelope2.items())
    box2 = calibration_box(envelope2, bound)
    assert box2 is not None
    gap = actual["A"][4]-actual["B"][4]
    records = {}
    for true, wrong in (("A", "B"), ("B", "A")):
        derivative = derivative_bounds(wrong, envelope2, box2)
        assert derivative is not None
        rho = center_rounding_bound(wrong, bound)
        profile_error = 2*sum(derivative["absolute_derivative_bounds"][r]*e2[r] for r in range(1, 4)) + rho
        margin = gap-2*e2[4]-profile_error
        assert margin > 0
        assert box2["x"][0] <= x <= box2["x"][1]
        assert box2["eta"][0] <= eta <= box2["eta"][1]
        assert box2["background"][0] <= b <= box2["background"][1]
        records[true] = {"wrong_structure": wrong, "wrong_structure_exclusion_margin": margin,
                         "wrong_structure_exclusion_margin_decimal": old.decimal(margin),
                         "wrong_profile_derivative_bounds": derivative,
                         "center_rounding_width_upper": rho,
                         "all_good_event_data_identify_true_structure": True}
    # In the specified AR(1) extension, tripling every group gives identical radii.
    for a, n, v in ((ALPHA_PILOT, n0, bound+bound**2/4),
                    *[(ALPHA_CALIBRATION_PER_MOMENT, n1, coarse_v[r]) for r in range(1, 4)],
                    *[(ALPHA_MAIN_PER_MOMENT, n2, LOCAL_VARIANCE[r]) for r in range(1, 5)]):
        assert radius(v, a, 3*n, F(3)) == radius(v, a, n)
    return {"status": "PASS", "data_status": "Analytic worst-case certificate; no observed or simulated data.",
            "true_reference_for_guarantee_only": {"x": x, "eta": eta, "background": b},
            "known_rate_bound": bound, "internal_background_cap": BACKGROUND_CAP,
            "internal_local_design_box": LOCAL, "group_sizes_iid": [n0, n1, n2],
            "total_observations_iid": n0+n1+n2, "group_sizes_ar1_abs_bound_half": [3*n0, 3*n1, 3*n2],
            "total_observations_ar1_abs_bound_half": 3*(n0+n1+n2),
            "previous_sufficient_observations": 10**36,
            "reduction_factor_against_previous_bound": F(10**36, n0+n1+n2),
            "failure_budget": {"pilot": ALPHA_PILOT, "calibration_each": ALPHA_CALIBRATION_PER_MOMENT,
                               "main_each": ALPHA_MAIN_PER_MOMENT, "total": TOTAL_FAILURE},
            "uniform_intensity_moment_bounds": UNIFORM, "no_singleton_partition_table": PARTITIONS,
            "coarse_factorial_moment_bounds": coarse_factorial, "coarse_variance_bounds": coarse_v,
            "local_intensity_moment_bounds": LOCAL_MOMENTS, "local_moment_derivation": LOCAL_DETAILS,
            "local_factorial_moment_bounds": LOCAL_FACTORIAL, "local_variance_bounds": LOCAL_VARIANCE,
            "local_variance_bound_decimals": {r: old.decimal(v) for r, v in LOCAL_VARIANCE.items()},
            "fourth_reduced_cumulant_polynomials": S4, "profile_derivative_ratio_numerators": J_NUMERATOR,
            "actual_reference_factorial_moments": actual, "reference_fourth_gap": gap,
            "pilot_radius": e0, "pilot_guard_margin": pilot_margin,
            "calibration_group_radii": e1, "calibration_population_envelope": envelope1,
            "calibration_envelope_box": box1, "main_group_radii": e2,
            "main_population_first_three_envelope": envelope2, "main_calibration_envelope_box": box2,
            "main_calibration_width_decimals": {k: old.decimal(box2[k][1]-box2[k][0]) for k in LOCAL},
            "structural_certificates": records,
            "input_hashes": {str(BASE_PATH.relative_to(WORKSPACE)): BASE_SHA,
                             str(FIXED_PATH.relative_to(WORKSPACE)): FIXED_SHA,
                             str(old.SOURCE.relative_to(WORKSPACE)): hashlib.sha256(old.SOURCE.read_bytes()).hexdigest()},
            "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--histograms", type=Path, help="JSON with three prespecified count histograms and lambda_max.")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = infer_histograms(json.loads(args.histograms.read_text())) if args.histograms else finite_certificate()
    output = args.output or HERE/"efficient_calibration_certificate.json"
    output.write_text(json.dumps(old.jsonable(result), indent=2)+"\n")
    print(json.dumps({"status": result["status"], "output": str(output),
                      "total_observations_iid": result.get("total_observations_iid"),
                      "main_calibration_width_decimals": result.get("main_calibration_width_decimals"),
                      "exclusion_margins": {g: d["wrong_structure_exclusion_margin_decimal"]
                                            for g, d in result.get("structural_certificates", {}).items()}}, indent=2))


if __name__ == "__main__":
    main()
