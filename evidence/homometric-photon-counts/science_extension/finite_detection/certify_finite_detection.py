#!/usr/bin/env python3
"""Finite photon-count and sample guarantees, using exact rational arithmetic.

Default: rebuild all fixed-t moments from the geometric phases (about a minute).
Optional --reuse-moments: audit an existing moment file instead of rebuilding it.
The probability, sign, derivative, Hellinger, and sample certificates are always
recomputed. Only the standard library and the adjacent unchanged moment engine
are required. No floating-point value is used to establish a scientific claim.
"""
from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from hashlib import sha256
from math import factorial, isqrt
from pathlib import Path
import json

import homogeneous_moment_engine as engine

ROOT = Path(__file__).resolve().parent
N = 63
ORDER = 32
GRID = 10**90
ROOT_GRID = 2**200
QZERO, QONE = Q(0), Q(1)
SHIFTS = {"A": (0, 31, 63), "B": (0, 32, 63)}


def ceilq(x):
    return -(-x.numerator // x.denominator)


def outward(lo, hi):
    assert lo <= hi
    return Q((lo*GRID).numerator // (lo*GRID).denominator, GRID), Q(ceilq(hi*GRID), GRID)


def sqrt_box(x):
    assert x >= 0
    j = isqrt((x.numerator*ROOT_GRID**2)//x.denominator)
    lo, hi = Q(j, ROOT_GRID), Q(j+1, ROOT_GRID)
    assert lo*lo <= x <= hi*hi
    return lo, hi


def decimal(x):
    with localcontext() as c:
        c.prec = 38
        return str(Decimal(x.numerator)/Decimal(x.denominator))


def box_record(box):
    lo, hi = outward(*box)
    return {"lower": str(lo), "upper": str(hi),
            "decimal_lower_approximation": decimal(lo),
            "decimal_upper_approximation": decimal(hi)}


def moment_table(t, order):
    return {g: engine.point_moments_from_cumulants(engine.phases(sh), t, order)
            for g, sh in SHIFTS.items()}


def check_moments(m, t, order):
    assert all(m["A"][k] == m["B"][k] for k in range(4))
    assert m["A"][0] == 1 and m["A"][1] == N*(1-t*t)
    gap = Q(455015761, 20000)*t**8*(1-t*t)**5*(t**6+3*t**4+6*t*t+6)
    assert m["A"][4]-m["B"][4] == gap > 0
    for g in m:
        for k in range(order):
            assert 0 < m[g][k+1] <= N*N*m[g][k]
        for k in range(1, order):
            assert m[g][k]**2 <= m[g][k-1]*m[g][k+1]
    return gap


def raw_laplace_box(m, k, eta):
    """Enclose E[I^k exp(-eta I)] by odd/even Taylor partial sums."""
    p = max(m)
    lo, hi, partial = QZERO, m[k], QZERO
    for j in range(p-k+1):
        partial += (-eta)**j*m[k+j]/factorial(j)
        if j % 2:
            lo = max(lo, partial)
        else:
            hi = min(hi, partial)
    assert 0 <= lo <= hi
    return outward(lo, hi)


def probability_box(m, k, eta):
    lo, hi = raw_laplace_box(m, k, eta)
    scale = eta**k/factorial(k)
    lo, hi = outward(scale*lo, scale*hi)
    lo, hi = max(QZERO, lo), min(QONE, hi)
    assert 0 <= lo <= hi <= 1
    return lo, hi


def gap_box(a, b):
    return a[0]-b[1], a[1]-b[0]


def abs_gap_box(a, b):
    lo, hi = gap_box(a, b)
    return max(QZERO, lo, -hi), max(abs(lo), abs(hi))


def hellinger_component_box(a, b):
    """Enclose (sqrt(p)-sqrt(q))^2 from rigorous probability boxes."""
    dl, du = abs_gap_box(a, b)
    denlo = a[0]+b[0]+2*sqrt_box(a[0]*b[0])[0]
    denhi = a[1]+b[1]+2*sqrt_box(a[1]*b[1])[1]
    lo = dl*dl/denhi if denhi else QZERO
    hi = min(a[1]+b[1], du*du/denlo) if denlo else a[1]+b[1]
    return outward(lo, hi)


def exp_box(x, degree=40):
    assert 0 <= x < degree+2
    partial = sum((x**j/factorial(j) for j in range(degree+1)), QZERO)
    remainder = x**(degree+1)/factorial(degree+1)/(1-x/Q(degree+2))
    return partial, partial+remainder


# These rational inequalities replace any numerical logarithm in sample counts.
LOG10_UPPER = Q(230259, 100000)
LOG100_19_LOWER = Q(830365, 500000)
assert exp_box(LOG10_UPPER)[0] > 10
assert exp_box(LOG100_19_LOWER)[1] < Q(100, 19)
assert exp_box(Q(3))[0] > 20


def samples_95(hbox):
    lo, hi = hbox
    assert 0 < lo <= hi < 2
    # If success >= .95, rho^(2m) <= .19 is necessary. Use
    # -log(1-x) <= x/(1-x) to obtain the rational lower threshold.
    necessary = ceilq(LOG100_19_LOWER*(1-hi/2)/hi)
    # rho^m <= exp(-m*h^2/2); exp(LOG10_UPPER)>10.
    sufficient = ceilq(2*LOG10_UPPER/lo)
    return {"target_success": "19/20", "priors": "equal",
            "necessary_observations_at_least": necessary,
            "sufficient_observations_for_optimal_likelihood_ratio": sufficient,
            "scope": "Known competing models; independent count snapshots. Necessary and sufficient bounds enclose, but do not determine, the exact optimal sample count."}


def finite_count_certificate(m, eta, cut=24):
    probs = {g: {k: probability_box(m[g], k, eta) for k in range(cut+1)} for g in m}
    hlow = hhigh = tvlow = tvhigh = QZERO
    components = {}
    for k in range(cut+1):
        a, b = probs["A"][k], probs["B"][k]
        component = hellinger_component_box(a, b)
        components[str(k)] = box_record(component)
        hlow += component[0]
        hhigh += component[1]
        dlo, dhi = abs_gap_box(a, b)
        tvlow += dlo/2
        tvhigh += dhi/2
    tail = eta**(cut+1)*(m["A"][cut+1]+m["B"][cut+1])/factorial(cut+1)
    hhigh += tail
    tvhigh += tail/2
    hbox, tvbox = outward(hlow, hhigh), outward(tvlow, tvhigh)
    a, b = probs["A"][4], probs["B"][4]
    h4 = hellinger_component_box(a, b)
    complement = hellinger_component_box((1-a[1], 1-a[0]), (1-b[1], 1-b[0]))
    four_hbox = outward(h4[0]+complement[0], h4[1]+complement[1])
    four_gap = gap_box(a, b)
    assert four_gap[1] < 0
    dlow = -four_gap[1]
    threshold = (a[1]+b[0])/2
    pupper = max(a[1], b[1])
    bernstein_n = ceilq(3*(8*pupper+Q(4, 3)*dlow)/dlow**2)
    return {"parameters": {"phase_attenuation_t": "1/2", "phase_variance_s": "2 log(2)",
                           "centered_MSD_v": "124 log(2)/(7 pi^2)", "background_b": "0", "gain_eta": str(eta),
                           "intensity_normalization": "I=|sum of 63 unit-weight phasors|^2; 0<=I<=3969",
                           "interpretation": "An exact mathematical operating point, not a physical detector calibration or recommended experiment."},
            "count_probabilities": {g: {str(k): box_record(v) for k,v in table.items()} for g,table in probs.items()},
            "Hellinger_components": components, "count_tail_cutoff": cut,
            "sum_of_two_tail_probability_upper_bounds": str(tail),
            "full_count_squared_Hellinger": box_record(hbox),
            "full_count_TV": box_record(tvbox), "full_count_samples_95": samples_95(hbox),
            "four_count_probability_gap_A_minus_B": box_record(four_gap),
            "four_count_squared_Hellinger": box_record(four_hbox),
            "four_count_samples_95": samples_95(four_hbox),
            "full_to_four_Hellinger_ratio": box_record((hbox[0]/four_hbox[1], hbox[1]/four_hbox[0])),
            "explicit_four_count_threshold_rule": {
                "rule": "For m independent snapshots, choose B if the fraction with N=4 exceeds the threshold; choose A otherwise.",
                "threshold": str(threshold), "threshold_decimal_approximation": decimal(threshold),
                "sufficient_m_for_each_conditional_error_below_1_over_20": bernstein_n,
                "derivation": "Bernstein: error <= exp[-m*d_lower^2/(8*p_upper+4*d_lower/3)]; exp(3)>20."}}


def blind_gain_certificate(m):
    lo, hi = Q(1, 640), Q(1, 512)
    def raw_gap(eta):
        return gap_box(raw_laplace_box(m["A"], 4, eta), raw_laplace_box(m["B"], 4, eta))
    initial = {"eta_lower": str(lo), "eta_upper": str(hi),
               "unscaled_gap_at_lower": box_record(raw_gap(lo)), "unscaled_gap_at_upper": box_record(raw_gap(hi))}
    assert raw_gap(lo)[0] > 0 > raw_gap(hi)[1]
    iterations = 0
    while hi-lo > Q(1, 10**20):
        mid = (lo+hi)/2
        gl, gu = raw_gap(mid)
        if gl > 0:
            lo = mid
        elif gu < 0:
            hi = mid
        else:
            raise AssertionError("Moment order insufficient for requested root bracket.")
        iterations += 1
    # Each R_G,5(eta)=E[I^5 e^-eta I] decreases in eta.
    # This gives a uniform derivative enclosure for F=R_A,4-R_B,4.
    a_lo, a_hi = raw_laplace_box(m["A"], 5, lo), raw_laplace_box(m["A"], 5, hi)
    b_lo, b_hi = raw_laplace_box(m["B"], 5, lo), raw_laplace_box(m["B"], 5, hi)
    derivative = (-a_lo[1]+b_hi[0], -a_hi[0]+b_lo[1])
    assert derivative[1] < 0
    assert raw_gap(lo)[0] > 0 > raw_gap(hi)[1]
    return {"phase_attenuation_t": "1/2", "phase_variance_s": "2 log(2)", "background_b": "0",
            "function": "F(eta)=E_A[I^4 exp(-eta I)]-E_B[I^4 exp(-eta I)]; count-four gap=eta^4 F(eta)/24",
            "initial_sign_change": initial, "isolated_gain_interval": box_record((lo, hi)),
            "interval_width": str(hi-lo), "bisections": iterations,
            "F_at_lower": box_record(raw_gap(lo)), "F_at_upper": box_record(raw_gap(hi)),
            "F_derivative_throughout_interval": box_record(derivative),
            "conclusion": "Exactly one simple four-count blind gain in this interval. At this gain the Bernoulli four-count indicator has identical laws for A and B. Full photon-count laws remain different by their fourth factorial moments.",
            "scope": "Local uniqueness only; no global count of blind gains or full-detector optimum is claimed."}


def finite_small_noise_certificate():
    t, eta = Q(999, 1000), Q(1, 512)
    m = moment_table(t, 6)
    check_moments(m, t, 6)
    d4, d5 = m["A"][4]-m["B"][4], m["A"][5]-m["B"][5]
    lower = eta**4*(d4-eta*d5-eta**2*m["B"][6]/2)/24
    upper = eta**4*max(m["A"][4], m["B"][4])/24
    assert lower > 0 and 0 < upper < 1
    a, b = probability_box(m["A"], 4, eta), probability_box(m["B"], 4, eta)
    assert a[0] > b[1]
    hlow = lower**2/(4*upper)
    return {"parameters": {"t": str(t), "s": "-2 log(999/1000)", "eta": str(eta), "b": "0"},
            "moments_through_six": {g: {str(k): str(v) for k,v in d.items()} for g,d in m.items()},
            "four_count_probability_gap_lower": str(lower),
            "four_count_probability_gap_lower_decimal": decimal(lower),
            "both_four_count_probabilities_upper": str(upper),
            "both_four_count_probabilities_upper_decimal": decimal(upper),
            "four_count_squared_Hellinger_lower": str(hlow),
            "four_count_squared_Hellinger_lower_decimal": decimal(hlow),
            "sufficient_independent_samples_for_95_percent_optimal_success": ceilq(2*LOG10_UPPER/hlow),
            "four_count_A_probability": box_record(a), "four_count_B_probability": box_record(b),
            "scope": "A nonasymptotic demonstration of the six-moment bound, not a practical sample-size recommendation."}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--reuse-moments", action="store_true")
    args = parser.parse_args()
    cache = ROOT/"fixed_t_moments.json"
    engine_hash = sha256((ROOT/"homogeneous_moment_engine.py").read_bytes()).hexdigest()
    if args.reuse_moments:
        raw = json.loads(cache.read_text())
        assert raw["attenuation_t"] == "1/2" and raw["maximum_moment"] == ORDER
        m = {g: {int(k): Q(v) for k,v in d.items()} for g,d in raw["moments"].items()}
    else:
        m = moment_table(Q(1, 2), ORDER)
        raw = {"attenuation_t": "1/2", "maximum_moment": ORDER,
               "moment_engine_sha256": engine_hash,
               "moments": {g: {str(k): str(v) for k,v in d.items()} for g,d in m.items()}}
        cache.write_text(json.dumps(raw, indent=2)+"\n")
    gap = check_moments(m, Q(1, 2), ORDER)
    # The computationally distinct site-convolution route checks low orders.
    for g, sh in SHIFTS.items():
        direct = engine.direct_site_moments(engine.phases(sh), Q(1, 2), 5)
        assert all(direct[k] == m[g][k] for k in range(6))
    finite = finite_count_certificate(m, Q(1, 512))
    blind = blind_gain_certificate(m)
    small = finite_small_noise_certificate()
    result = {"schema": "finite-photon-detection-certificate-v1", "date": "2026-10-20",
              "definitions": {"s": "raw Gaussian phase variance", "t": "exp(-s/2)",
                              "N_given_I": "Poisson(eta I), zero background",
                              "h_squared": "sum_k (sqrt(p_A(k))-sqrt(p_B(k)))^2", "TV": "one half the l1 probability difference"},
              "method": "Exact fixed-t bivariate cumulant recurrence, odd/even exponential Taylor bounds, rational square-root enclosures, factorial-moment tail bound, and product-affinity inequalities.",
              "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
              "moment_engine_sha256": engine_hash,
              "fixed_moments_sha256": sha256(cache.read_bytes()).hexdigest(),
              "fourth_moment_gap_at_t_half": str(gap),
              "certified_finite_operating_point": finite,
              "four_count_blind_gain": blind,
              "finite_small_noise_bound_example": small,
              "logarithm_certificates": {"log_10_upper": str(LOG10_UPPER), "exp_of_bound_lower": str(exp_box(LOG10_UPPER)[0]),
                                         "log_100_over_19_lower": str(LOG100_19_LOWER), "exp_of_bound_upper": str(exp_box(LOG100_19_LOWER)[1])},
              "checks": {"first_three_intensity_moments_equal": True, "exact_fourth_gap_matches_saved_theorem": True,
                         "direct_site_convolution_agrees_through_order_five": True,
                         "all_moments_positive_log_convex_and_bounded": True,
                         "probability_intervals_consistent": True, "positive_lower_Hellinger_bounds": True,
                         "blind_gain_opposite_sign_endpoints_and_uniform_negative_derivative": True,
                         "six_moment_finite_noise_bound_positive": True},
              "limitations": ["No external peer review or experimental calibration.", "Sample bounds do not give exact optimal sample counts or acquisition times.",
                              "Four-count blind gain is locally unique; global uniqueness is not established.",
                              "The numeric operating points are mathematical examples, not proposed laboratory settings.",
                              "Every snapshot must be independent conditional on the unknown structure, with the stated common parameters."]}
    dest = ROOT/"finite_detection_certificate.json"
    dest.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"status": "PASS", "certificate": str(dest),
                      "full_count_h_squared": finite["full_count_squared_Hellinger"],
                      "full_count_sample_bounds": finite["full_count_samples_95"],
                      "four_count_sample_bounds": finite["four_count_samples_95"],
                      "blind_gain": blind["isolated_gain_interval"],
                      "blind_gain_derivative": blind["F_derivative_throughout_interval"],
                      "small_noise_sufficient_samples": small["sufficient_independent_samples_for_95_percent_optimal_success"]}, indent=2))


if __name__ == "__main__":
    main()
