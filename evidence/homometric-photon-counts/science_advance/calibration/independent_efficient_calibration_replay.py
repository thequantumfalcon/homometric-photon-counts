#!/usr/bin/env python3
"""Independent exact replay; imports neither calibration producer.

Uses exponential generating coefficients for no-singleton partitions,
formal logarithms for cumulants, and direct endpoint checks for inverses.
The retained geometric moment tables remain input dependencies.
"""
from fractions import Fraction as F
from pathlib import Path
from hashlib import sha256
from math import comb, factorial, prod
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
CERT_PATH = HERE / "efficient_calibration_certificate.json"
CERT_SHA = "43a52ff1da49eef528b4ab54a59d2a6eb77c891a67ff8bec11c9d5c373ad7521"
POLY_PATH = ROOT / "science_completion/homogeneous_control/homogeneous_control_results.json"
POLY_SHA = "aba1d6e9cabb804eae61d4734308b0e7dda470a0ea1ac7f49bfe7935bf536142"
FIXED_PATH = ROOT / "science_extension/finite_detection/fixed_t_moments.json"
FIXED_SHA = "538aee114c16e712496fe526486e6ac96ef344d2ff92e6d3014f7f47223feb32"
checks = []


def verify(condition, name):
    if not condition:
        raise AssertionError(name)
    checks.append(name)


def read_pinned(path, expected):
    raw = path.read_bytes()
    verify(sha256(raw).hexdigest() == expected, f"Pinned input {path.name}")
    return json.loads(raw)


def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def add(p, q):
    n = max(len(p), len(q))
    return trim([(p[i] if i < len(p) else F(0)) +
                 (q[i] if i < len(q) else F(0)) for i in range(n)])


def scale(p, c):
    return trim([F(c) * z for z in p])


def mul(p, q):
    out = [F(0)] * (len(p) + len(q) - 1)
    for i, u in enumerate(p):
        for j, v in enumerate(q):
            out[i + j] += u * v
    return trim(out)


def diff(p):
    return trim([i * p[i] for i in range(1, len(p))] or [F(0)])


def power(p, n):
    out = [F(1)]
    for _ in range(n):
        out = mul(out, p)
    return out


def divide_exact(numerator, denominator):
    work = list(numerator)
    quotient = [F(0)] * (len(work) - len(denominator) + 1)
    for i in range(len(quotient) - 1, -1, -1):
        q = work[i + len(denominator) - 1] / denominator[-1]
        quotient[i] = q
        for j, a in enumerate(denominator):
            work[i + j] -= q * a
    assert all(z == 0 for z in work)
    return trim(quotient)


def dictionary(p):
    return {str(k): str(c) for k, c in enumerate(p) if c}


def from_dict(row, halve=False):
    data = {}
    for key, value in row.items():
        k = int(key)
        assert not halve or k % 2 == 0
        data[k // 2 if halve else k] = F(value)
    out = [F(0)] * (max(data, default=0) + 1)
    for k, value in data.items():
        out[k] = value
    return trim(out)


def evaluate(p, x):
    # Monomial summation, independent of the producer's scalar Horner loop.
    return sum((c * x ** i for i, c in enumerate(p)), F(0))


def I(value):
    return value if isinstance(value, tuple) else (F(value), F(value))


def plus(a, b):
    a, b = I(a), I(b)
    return a[0] + b[0], a[1] + b[1]


def minus(a, b):
    a, b = I(a), I(b)
    return a[0] - b[1], a[1] - b[0]


def times(a, b):
    a, b = I(a), I(b)
    values = tuple(u * v for u in a for v in b)
    return min(values), max(values)


def quotient(a, b):
    b = I(b)
    assert b[0] > 0
    return times(a, (1 / b[1], 1 / b[0]))


def positive_power(a, k):
    a = I(a)
    assert a[0] >= 0
    return a[0] ** k, a[1] ** k


def polynomial_interval(p, domain):
    # Horner intervals are reconstructed locally; no external helper imports.
    answer = I(0)
    for c in reversed(p):
        answer = plus(times(answer, domain), c)
    return answer


def interval_from(row):
    return F(row[0]), F(row[1])


def cumulants_via_log(moments):
    # [z^r] log(1+sum_{j>=1} mu_j z^j/j!) times r!.
    a = {r: scale(moments[r], F(1, factorial(r))) for r in range(1, 5)}
    kth = {0: [F(1)]}
    result = {r: [F(0)] for r in range(1, 5)}
    for k in range(1, 5):
        new = {}
        for r, p in kth.items():
            for j, q in a.items():
                if r + j <= 4:
                    new[r + j] = add(new.get(r + j, [F(0)]), mul(p, q))
        kth = new
        for r, p in kth.items():
            result[r] = add(result[r], scale(p, F((-1) ** (k + 1), k)))
    return {r: scale(p, factorial(r)) for r, p in result.items()}


def no_singleton_partitions():
    # EGF: S_{>=2}(n,k)=n! [z^n](exp(z)-1-z)^k/k!.
    base = [F(0), F(0)] + [F(1, factorial(j)) for j in range(2, 17)]
    current = [F(1)]
    values = {(0, 0): 1}
    for k in range(1, 9):
        current = mul(current, base)[:17]
        for n in range(2 * k, 17):
            value = F(factorial(n), factorial(k)) * current[n]
            assert value.denominator == 1
            values[n, k] = value.numerator
    return values


def variance_bounds(intensity, background, gain):
    f = {r: sum((F(comb(r, k)) * background ** (r - k) * gain ** k * intensity[k]
                 for k in range(r + 1)), F(0)) for r in range(9)}
    v = {r: sum((F(comb(r, j) ** 2 * factorial(j)) * f[2 * r - j]
                 for j in range(r + 1)), F(0)) for r in range(1, 5)}
    return f, v


def main():
    cert = read_pinned(CERT_PATH, CERT_SHA)
    raw = read_pinned(POLY_PATH, POLY_SHA)["intensity_moment_polynomials"]
    fixed = read_pinned(FIXED_PATH, FIXED_SHA)["moments"]
    producer = HERE / "certify_efficient_calibration.py"
    verify(sha256(producer.read_bytes()).hexdigest() == cert["source_sha256"], "Producer hash matches certificate")
    moments = {g: {r: from_dict(raw[g][str(r)], halve=True) for r in range(6)} for g in ("A", "B")}
    cumulants = {g: cumulants_via_log(moments[g]) for g in moments}
    v_poly = divide_exact(cumulants["A"][2], [F(1), F(-2), F(1)])
    c_poly = divide_exact(cumulants["A"][3], [F(1), F(-3), F(3), F(-1)])
    h_poly = add(scale(mul(diff(c_poly), v_poly), 2), scale(mul(c_poly, diff(v_poly)), -3))
    verify(all(c > 0 for c in v_poly + c_poly + h_poly), "Strict monotone calibration inverse")
    s4 = {g: divide_exact(cumulants[g][4], [F(1), F(-4), F(6), F(-4), F(1)]) for g in moments}
    j_num = {g: mul(v_poly, add(mul(diff(s4[g]), v_poly), scale(mul(s4[g], diff(v_poly)), -2))) for g in moments}
    for g in moments:
        verify(dictionary(s4[g]) == cert["fourth_reduced_cumulant_polynomials"][g], f"Formal-log fourth cumulant {g}")
        verify(dictionary(j_num[g]) == cert["profile_derivative_ratio_numerators"][g], f"Profile Jacobian polynomial {g}")
    partition = no_singleton_partitions()
    for key, value in cert["no_singleton_partition_table"].items():
        a, k = map(int, key.split(","))
        verify(partition.get((a, k), 0) == value, f"EGF nonsingleton partition {key}")
    uniform = {0: F(1)}
    for r in range(1, 9):
        uniform[r] = sum((F(prod(range(64 - k, 64)) * partition[2 * r, k] * 2 ** (2 * r - 2 * k))
                          for k in range(1, r + 1)), F(0))
        verify(uniform[r] == F(cert["uniform_intensity_moment_bounds"][str(r)]), f"Uniform intensity bound {r}")
    for r in range(1, 5):
        # Both sides are degree 2r polynomials. Checking 2r+1 distinct values
        # establishes the factorial-product identity as a polynomial identity.
        for n in range(2 * r + 1):
            falling = lambda order: prod(range(n - order + 1, n + 1)) if n >= order else 0
            verify(falling(r) ** 2 == sum(comb(r, j) ** 2 * factorial(j) * falling(2 * r - j) for j in range(r + 1)), f"Factorial polynomial {r}, point {n}")

    local = {k: interval_from(v) for k, v in cert["internal_local_design_box"].items()}
    x_box = local["x"]
    dx_sigma = max(abs(u - F(1, 4)) for u in x_box) / (2 * x_box[0])
    verify(dx_sigma == F(cert["local_moment_derivation"]["phase_standard_deviation_difference_upper"]), "Local phase standard-deviation modulus")
    exp_upper = sum((F(1, factorial(k)) for k in range(10)), F(0)) + F(11, 10 * factorial(10))
    verify(exp_upper == F(cert["local_moment_derivation"]["exp_one_upper"]) < 3 and x_box[1] < F(1, 3), "Local log derivative domain")
    local_moments = {0: F(1)}
    for r in range(1, 9):
        info = cert["local_moment_derivation"]["moments"][str(r)]
        reference = max(F(fixed[g][str(r)]) for g in moments)
        normal = F(prod(range(1, 2 * r, 2)))
        amp_root, normal_root = F(info["reference_amplitude_norm_upper"]), F(info["normal_norm_upper"])
        verify(amp_root ** (2 * r) >= reference and (amp_root - F(1, 10**6)) ** (2 * r) < reference, f"Reference moment root {r}")
        verify(normal_root ** (2 * r) >= normal and (normal_root - F(1, 10**6)) ** (2 * r) < normal, f"Gaussian moment root {r}")
        minkowski = (amp_root + 63 * dx_sigma * normal_root) ** (2 * r)
        verify(minkowski == F(info["minkowski_intensity_moment_upper"]), f"Minkowski intensity bound {r}")
        chosen = minkowski
        if r <= 5:
            poly_upper = max(polynomial_interval(moments[g][r], x_box)[1] for g in moments)
            verify(poly_upper == F(info["retained_polynomial_upper"]), f"Local polynomial bound {r}")
            chosen = min(chosen, poly_upper)
        local_moments[r] = chosen
        verify(chosen == F(cert["local_intensity_moment_bounds"][str(r)]), f"Selected local intensity bound {r}")
    B = F(cert["known_rate_bound"])
    b_cap = F(cert["internal_background_cap"])
    coarse_f, coarse_v = variance_bounds(uniform, b_cap, B / 3969)
    local_f, local_v = variance_bounds(local_moments, local["background"][1], local["eta"][1])
    for prefix, fs, vs in (("coarse", coarse_f, coarse_v), ("local", local_f, local_v)):
        for r, value in fs.items():
            verify(value == F(cert[f"{prefix}_factorial_moment_bounds"][str(r)]), f"{prefix} factorial bound {r}")
        for r, value in vs.items():
            verify(value == F(cert[f"{prefix}_variance_bounds"][str(r)]), f"{prefix} variance bound {r}")

    n0, n1, n2 = cert["group_sizes_iid"]
    alpha0, alpha1, alpha2 = (F(cert["failure_budget"][k]) for k in ("pilot", "calibration_each", "main_each"))
    verify(alpha0 + 3 * alpha1 + 4 * alpha2 == F(1, 20), "Total failure budget")
    e0 = F(cert["pilot_radius"])
    e1 = {r: F(cert["calibration_group_radii"][str(r)]) for r in range(1, 4)}
    e2 = {r: F(cert["main_group_radii"][str(r)]) for r in range(1, 5)}
    ulp = F(1, 2**220)
    for name, value, variance, alpha, count in ([('pilot', e0, B + B * B / 4, alpha0, n0)]
            + [(f'coarse{r}', e1[r], coarse_v[r], alpha1, n1) for r in e1]
            + [(f'main{r}', e2[r], local_v[r], alpha2, n2) for r in e2]):
        q = variance / (alpha * count)
        verify((value - ulp) ** 2 <= q <= value ** 2, f"Exact radius enclosure {name}")
        verify(q == 3 * variance / (alpha * 3 * count), f"AR triple-radius invariance {name}")

    true = {k: F(v) for k, v in cert["true_reference_for_guarantee_only"].items()}
    x, eta, background = true["x"], true["eta"], true["background"]
    actual = {g: {r: sum((F(comb(r, k)) * background ** (r - k) * eta ** k * evaluate(moments[g][k], x) for k in range(r + 1)), F(0)) for r in range(1, 5)} for g in moments}
    for g in moments:
        for r, value in actual[g].items():
            verify(value == F(cert["actual_reference_factorial_moments"][g][str(r)]), f"Reference photon moment {g},{r}")
            verify(evaluate(moments[g][r], x) == F(fixed[g][str(r)]), f"Cross-input moment agreement {g},{r}")
    pilot_margin = b_cap - actual["A"][1] - 2 * e0
    verify(pilot_margin == F(cert["pilot_guard_margin"]) > 0, "Every good-event pilot passes")

    def q_value(u):
        return evaluate(c_poly, u) ** 2 / evaluate(v_poly, u) ** 3

    variance_poly = cumulants["A"][2]
    d_factor = add(scale(v_poly, -2), mul([F(1), F(-1)], diff(v_poly)))
    verify(d_factor[0] + sum(max(F(0), z) for z in d_factor[1:]) < 0, "Intensity variance strictly decreasing")

    def verify_box(envelope, record, label):
        u1, u2, u3 = (envelope[r] for r in range(1, 4))
        c2 = minus(u2, positive_power(u1, 2))
        c3 = plus(minus(u3, times(3, times(u2, u1))), times(2, positive_power(u1, 3)))
        verify(c2 == interval_from(record["factorial_cumulant_2"]) and c2[0] > 0, f"{label} second cumulant rectangle")
        verify(c3 == interval_from(record["factorial_cumulant_3"]) and c3[0] > 0, f"{label} third cumulant rectangle")
        qq = c3[0]**2 / c2[1]**3, c3[1]**2 / c2[0]**3
        verify(qq == interval_from(record["q"]) and q_value(F(0)) < qq[0] <= qq[1] < q_value(F(1)), f"{label} smooth inverse domain")
        xx = interval_from(record["x"])
        step = F(1, 2**160)
        verify(q_value(xx[0]) <= qq[0] <= q_value(xx[0] + step) and q_value(xx[1] - step) <= qq[1] <= q_value(xx[1]), f"{label} independent inverse endpoint brackets")
        lowvar, highvar = evaluate(variance_poly, xx[1]), evaluate(variance_poly, xx[0])
        gain = interval_from(record["eta"])
        verify(gain[0]**2 <= c2[0] / highvar <= (gain[0] + ulp)**2, f"{label} lower gain root")
        verify(gain[1] < B / 3969 and (gain[1] - ulp)**2 <= c2[1] / lowvar <= gain[1]**2, f"{label} upper gain root")
        back = (max(F(0), u1[0] - gain[1] * 63 * (1 - xx[0])), min(B, u1[1] - gain[0] * 63 * (1 - xx[1])))
        verify(back == interval_from(record["background"]), f"{label} background interval")
        return c2, c3, xx

    envelopes = {}
    boxes = {}
    for label, radii, key, boxkey in (("coarse", e1, "calibration_population_envelope", "calibration_envelope_box"), ("main", e2, "main_population_first_three_envelope", "main_calibration_envelope_box")):
        envelope = {r: (actual["A"][r] - 2 * radii[r], actual["A"][r] + 2 * radii[r]) for r in range(1, 4)}
        for r, interval in envelope.items():
            verify(interval == interval_from(cert[key][str(r)]) and 0 < interval[0] <= interval[1] < B**r, f"{label} population envelope {r}")
        boxes[label] = verify_box(envelope, cert[boxkey], label)
        envelopes[label] = envelope
    for key in local:
        box = interval_from(cert["calibration_envelope_box"][key])
        verify(local[key][0] <= box[0] <= box[1] <= local[key][1], f"Every good-event coarse guard passes {key}")
        box_main = interval_from(cert["main_calibration_envelope_box"][key])
        value = true[key]
        verify(box_main[0] <= value <= box_main[1], f"True calibration covered {key}")

    u1, u2, u3 = (envelopes["main"][r] for r in range(1, 4))
    c2, c3, xx = boxes["main"]
    gap = actual["A"][4] - actual["B"][4]
    verify(gap == F(cert["reference_fourth_gap"]) > 0, "Positive shared fourth gap")
    for true_g, wrong_g in (("A", "B"), ("B", "A")):
        entry = cert["structural_certificates"][true_g]
        vp = polynomial_interval(v_poly, xx)
        rr = quotient(polynomial_interval(s4[wrong_g], xx), positive_power(vp, 2))
        jj = quotient(polynomial_interval(j_num[wrong_g], xx), times(polynomial_interval(c_poly, xx), polynomial_interval(h_poly, xx)))
        cc = quotient(c3, c2)
        aa = minus(times(2, times(c2, rr)), times(3, times(positive_power(cc, 2), jj)))
        dd = times(2, times(cc, jj))
        # Independently differentiate through (c2,c3) plus the raw-cumulant
        # correction. This ordering reconstructs the saved enclosure exactly.
        grad = {
            1: plus(minus(plus(times(4, u3), times(24, positive_power(u1, 3))), times(24, times(u2, u1))), plus(times(-2, times(u1, aa)), times(dd, plus(times(-3, u2), times(6, positive_power(u1, 2)))))),
            2: plus(minus(times(6, u2), times(12, positive_power(u1, 2))), minus(aa, times(3, times(u1, dd)))),
            3: plus(times(4, u1), dd),
        }
        derivative_record = entry["wrong_profile_derivative_bounds"]
        lipschitz = {}
        for r, bounds in grad.items():
            verify(bounds == interval_from(derivative_record["derivative_intervals"][str(r)]), f"Profile derivative enclosure {wrong_g},{r}")
            lipschitz[r] = max(abs(z) for z in bounds)
            verify(lipschitz[r] == F(derivative_record["absolute_derivative_bounds"][str(r)]), f"Profile derivative norm {wrong_g},{r}")
        vvmin, vvmax = evaluate(v_poly, F(0)), evaluate(v_poly, F(1))
        ss = s4[wrong_g]
        ls, ass = sum(i * abs(c) for i, c in enumerate(ss)), sum(abs(c) for c in ss)
        lv = sum(i * abs(c) for i, c in enumerate(v_poly))
        rho = B**4 * (ls / vvmin**2 + 2 * ass * vvmax * lv / vvmin**4) / 2**160
        verify(rho == F(entry["center_rounding_width_upper"]), f"Finite inverse rounding width {wrong_g}")
        margin = gap - 2 * e2[4] - 2 * sum(lipschitz[r] * e2[r] for r in range(1, 4)) - rho
        verify(margin == F(entry["wrong_structure_exclusion_margin"]) > 0, f"Every good-event dataset excludes {wrong_g}")

    verify(n0 + n1 + n2 == cert["total_observations_iid"] == 101000000010000000000, "Exact iid total")
    verify([3 * n0, 3 * n1, 3 * n2] == cert["group_sizes_ar1_abs_bound_half"] and 3 * (n0 + n1 + n2) == cert["total_observations_ar1_abs_bound_half"] == 303000000030000000000, "Exact AR total")
    output = {
        "status": "PASS", "number_of_exact_checks": len(checks), "checks": checks,
        "certificate_sha256": CERT_SHA, "producer_sha256": cert["source_sha256"],
        "reviewed_proof_sha256": sha256((HERE / "efficient_calibration_proof.txt").read_bytes()).hexdigest(),
        "replay_source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "independence_scope": "Imports neither new producer nor old calibration producer. EGF partition enumeration, formal-log cumulants, fresh interval arithmetic, inverse endpoint brackets, and exact radius checks are implemented independently. Both replay and producer depend on the preserved geometry moment polynomials and fixed-point moments; those tables are not independently regenerated here.",
        "theoretical_review": "Three fixed guards, unconditional error-budget branches, variance bounds, profiled derivative chain rule, finite center width, and all-good-data rejection argument separately audited in independent_efficient_calibration_review.txt.",
    }
    target = HERE / "independent_efficient_calibration_replay.json"
    target.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({"status": output["status"], "number_of_exact_checks": len(checks), "output": str(target)}, indent=2))


if __name__ == "__main__":
    main()
