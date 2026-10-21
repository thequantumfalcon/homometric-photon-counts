#!/usr/bin/env python3
"""Exact rational four-count root exclusion on a macroscopic gain interval.

Inputs are the previously verified fixed-t moment table (moments 0,...,32).
No old artifact is changed.  Every sign decision uses fractions, not floats.
The --rebuild-input option also recomputes all input moments from the original
geometric phase engine before building the new certificate.

Run from any directory:
  python certify_global_blind_interval.py
  python certify_global_blind_interval.py --verify-only
  python certify_global_blind_interval.py --rebuild-input
"""
from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from hashlib import sha256
from math import comb, factorial
from pathlib import Path
import json
import sys

sys.set_int_max_str_digits(0)
ROOT = Path(__file__).resolve().parent
INPUT = ROOT.parents[1] / "science_extension/finite_detection/fixed_t_moments.json"
ENGINE = INPUT.parent / "homogeneous_moment_engine.py"
OUTPUT = ROOT / "blind_interval_certificate.json"


def decimal(q):
    with localcontext() as context:
        context.prec = 30
        return str(Decimal(q.numerator) / Decimal(q.denominator))


def polynomial_value(coefficients, x):
    value = Q(0)
    for coefficient in reversed(coefficients):
        value = value*x + coefficient
    return value


def bernstein_coefficients(coefficients, a, b):
    """Exact power-to-Bernstein conversion on [a,b]."""
    degree = len(coefficients)-1
    q = [
        (b-a)**k * sum(
            (coefficients[j]*comb(j,k)*a**(j-k)
             for j in range(k, degree+1)), Q(0))
        for k in range(degree+1)
    ]
    return [
        sum((q[k]*Q(comb(i,k), comb(degree,k)) for k in range(i+1)), Q(0))
        for i in range(degree+1)
    ]


def certify_negative(coefficients, a, b, depth=0):
    bernstein = bernstein_coefficients(coefficients, a, b)
    upper = max(bernstein)
    if upper < 0:
        return [{
            "left": str(a),
            "right": str(b),
            "bernstein_upper": str(upper),
            "bernstein_upper_decimal_approximation": decimal(upper),
            "depth": depth,
        }]
    if depth >= 24:
        raise AssertionError(f"Could not certify polynomial negative on [{a},{b}]")
    mid = (a+b)/2
    return (certify_negative(coefficients, a, mid, depth+1)
            + certify_negative(coefficients, mid, b, depth+1))


def check_cover(coefficients, leaves, a, b):
    assert leaves and Q(leaves[0]["left"]) == a
    previous = a
    for leaf in leaves:
        left, right = Q(leaf["left"]), Q(leaf["right"])
        assert left == previous and left < right
        upper = max(bernstein_coefficients(coefficients, left, right))
        assert upper == Q(leaf["bernstein_upper"]) < 0
        previous = right
    assert previous == b


def raw_laplace_box(moment, order, eta):
    """Odd/even global Taylor bounds, valid for every nonnegative eta*I."""
    lower, upper, partial = Q(0), moment[order], Q(0)
    for j in range(max(moment)-order+1):
        partial += (-eta)**j * moment[order+j]/factorial(j)
        if j % 2:
            lower = max(lower, partial)
        else:
            upper = min(upper, partial)
    assert 0 <= lower <= upper
    return lower, upper


def difference_box(moments, eta):
    a = raw_laplace_box(moments["A"], 4, eta)
    b = raw_laplace_box(moments["B"], 4, eta)
    return a[0]-b[1], a[1]-b[0]


def box_record(box):
    return {
        "lower": str(box[0]), "upper": str(box[1]),
        "lower_decimal_approximation": decimal(box[0]),
        "upper_decimal_approximation": decimal(box[1]),
    }


def make_polynomials(moments):
    delta = {k: moments["A"][k]-moments["B"][k] for k in range(33)}
    assert all(delta[k] == 0 for k in range(4))
    t = Q(1,2)
    expected = Q(455015761,20000)*t**8*(1-t*t)**5*(t**6+3*t**4+6*t*t+6)
    assert delta[4] == expected > 0
    # P_27 <= R_G,4 <= P_27 + eta^28 mu_G,32/28!.
    f_upper = [(-1)**j*delta[4+j]/factorial(j) for j in range(28)]
    f_upper.append(moments["A"][32]/factorial(28))
    # The degree-26 even truncation bounds R_G,5 from above, with
    # lower remainder >= -eta^27 mu_G,32/27!.  F'=-R_A,5+R_B,5.
    derivative_upper = [
        -(-1)**j*delta[5+j]/factorial(j) for j in range(27)]
    derivative_upper.append(moments["A"][32]/factorial(27))
    return f_upper, derivative_upper


def rebuild_input(moments):
    sys.path.insert(0, str(INPUT.parent))
    import homogeneous_moment_engine as engine
    for label, shifts in {"A": (0,31,63), "B": (0,32,63)}.items():
        rebuilt = engine.point_moments_from_cumulants(
            engine.phases(shifts), Q(1,2), 32)
        assert rebuilt == moments[label]


def build(moments, source):
    f_upper, derivative_upper = make_polynomials(moments)
    split, end = Q(1,512), Q(1,128)
    derivative_leaves = certify_negative(derivative_upper, Q(0), split)
    negative_leaves = certify_negative(f_upper, split, end)
    lo = Q(61217055127150107,36893488147419103232)
    hi = Q(38260659454468817,23058430092136939520)
    lo_box, hi_box = difference_box(moments, lo), difference_box(moments, hi)
    assert 0 < lo < hi < split and lo_box[0] > 0 > hi_box[1]
    certificate = {
        "title": "Exactly one four-count blind gain on (0,1/128]",
        "phase_attenuation_t": "1/2",
        "phase_variance_s": "2 log(2)",
        "background_b": "0",
        "F_definition": "E_A[I^4 exp(-eta I)] - E_B[I^4 exp(-eta I)]",
        "count_four_gap": "eta^4 F(eta)/24",
        "input_moments_path": str(INPUT.relative_to(ROOT.parents[1])),
        "input_moments_sha256": sha256(source).hexdigest(),
        "input_moment_engine_sha256": sha256(ENGINE.read_bytes()).hexdigest(),
        "arithmetic": "Python standard-library Fraction; all signs exact rational",
        "moment_maximum": 32,
        "F_at_zero": str(moments["A"][4]-moments["B"][4]),
        "monotonic_interval": ["0", str(split)],
        "F_derivative_strictly_negative_certificate": derivative_leaves,
        "negative_interval": [str(split), str(end)],
        "F_strictly_negative_certificate": negative_leaves,
        "unique_simple_root_bracket": {
            "left": str(lo), "right": str(hi),
            "left_decimal_approximation": decimal(lo),
            "right_decimal_approximation": decimal(hi),
            "F_at_left": box_record(lo_box),
            "F_at_right": box_record(hi_box),
        },
        "conclusion": (
            "F has exactly one zero in (0,1/128], and that zero is simple. "
            "F is positive below that root and negative from that root "
            "through 1/128. No conclusion about zeros above 1/128."),
        "scope": (
            "Conditional on the independently verified input moment table. "
            "Use --rebuild-input to recompute that table from the original "
            "geometry. This is not an exact global positive-axis root count."),
    }
    verify(certificate, moments, source)
    return certificate


def verify(certificate, moments, source):
    assert certificate["input_moments_sha256"] == sha256(source).hexdigest()
    assert certificate["input_moment_engine_sha256"] == sha256(ENGINE.read_bytes()).hexdigest()
    f_upper, derivative_upper = make_polynomials(moments)
    check_cover(derivative_upper,
                certificate["F_derivative_strictly_negative_certificate"],
                Q(0), Q(1,512))
    check_cover(f_upper, certificate["F_strictly_negative_certificate"],
                Q(1,512), Q(1,128))
    bracket = certificate["unique_simple_root_bracket"]
    lo, hi = Q(bracket["left"]), Q(bracket["right"])
    assert 0 < lo < hi < Q(1,512)
    assert difference_box(moments, lo)[0] > 0
    assert difference_box(moments, hi)[1] < 0
    assert moments["A"][4]-moments["B"][4] == Q(certificate["F_at_zero"]) > 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-only", action="store_true")
    parser.add_argument("--rebuild-input", action="store_true")
    arguments = parser.parse_args()
    source = INPUT.read_bytes()
    input_object = json.loads(source)
    assert input_object["attenuation_t"] == "1/2"
    assert input_object["maximum_moment"] == 32
    moments = {label: {int(k): Q(v) for k,v in table.items()}
               for label,table in input_object["moments"].items()}
    assert input_object["moment_engine_sha256"] == sha256(ENGINE.read_bytes()).hexdigest()
    if arguments.rebuild_input:
        rebuild_input(moments)
    if arguments.verify_only:
        certificate = json.loads(OUTPUT.read_text())
        verify(certificate, moments, source)
    else:
        certificate = build(moments, source)
        OUTPUT.write_text(json.dumps(certificate, indent=2)+"\n")
    print(json.dumps({
        "verified": True,
        "input_moments_rebuilt": arguments.rebuild_input,
        "derivative_certificate_leaves": len(certificate["F_derivative_strictly_negative_certificate"]),
        "negative_certificate_leaves": len(certificate["F_strictly_negative_certificate"]),
        "conclusion": certificate["conclusion"],
        "output": str(OUTPUT),
    }, indent=2))


if __name__ == "__main__":
    main()
