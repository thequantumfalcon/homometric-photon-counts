#!/usr/bin/env python3
"""Replay the new root certificate with a different Bernstein conversion.

This script does not import the certificate builder.  It multiplies
Bernstein polynomials in a Horner scheme, avoiding the builder's
affine-power conversion formula.
"""
from decimal import Decimal, localcontext
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import json
import sys

sys.set_int_max_str_digits(0)
Q = Fraction
HERE = Path(__file__).resolve().parent
BASE = HERE.parents[1]
SOURCE = BASE / "science_extension/finite_detection/fixed_t_moments.json"
CERTIFICATE = HERE / "blind_interval_certificate.json"


def bernstein_horner(power, left, right):
    """Evaluate the polynomial's Horner scheme directly in Bernstein bases."""
    coefficients = [power[-1]]
    for constant in power[-2::-1]:
        degree = len(coefficients)
        following = []
        for i in range(degree+1):
            value = constant
            if i < degree:
                value += left * Q(degree-i, degree) * coefficients[i]
            if i:
                value += right * Q(i, degree) * coefficients[i-1]
            following.append(value)
        coefficients = following
    return coefficients


def factorial(order):
    result = 1
    for k in range(2, order+1):
        result *= k
    return result


def replay():
    source = SOURCE.read_bytes()
    data = json.loads(source)
    certificate = json.loads(CERTIFICATE.read_text())
    assert sha256(source).hexdigest() == certificate["input_moments_sha256"]
    moments = {
        name: [Q(values[str(k)]) for k in range(33)]
        for name, values in data["moments"].items()
    }
    difference = [a-b for a,b in zip(moments["A"], moments["B"])]
    assert difference[:4] == [0,0,0,0]
    assert difference[4] == Q(certificate["F_at_zero"]) > 0
    bound_f = [Q((-1)**j, factorial(j))*difference[4+j] for j in range(28)]
    bound_f += [moments["A"][32]/factorial(28)]
    bound_df = [Q((-1)**(j+1), factorial(j))*difference[5+j] for j in range(27)]
    bound_df += [moments["A"][32]/factorial(27)]

    for polynomial, key, outer in [
        (bound_df, "F_derivative_strictly_negative_certificate", (Q(0),Q(1,512))),
        (bound_f, "F_strictly_negative_certificate", (Q(1,512),Q(1,128))),
    ]:
        leaves = certificate[key]
        covered = outer[0]
        for leaf in leaves:
            left, right = Q(leaf["left"]), Q(leaf["right"])
            assert left == covered and right > left
            coefficients = bernstein_horner(polynomial,left,right)
            assert all(value < 0 for value in coefficients)
            assert max(coefficients) == Q(leaf["bernstein_upper"])
            covered = right
        assert covered == outer[1]

    bracket = certificate["unique_simple_root_bracket"]
    left, right = Q(bracket["left"]), Q(bracket["right"])
    assert 0 < left < right < Q(1,512)
    for eta, desired in [(left,1),(right,-1)]:
        intervals = []
        for name in ["A","B"]:
            terms = [(-eta)**j*moments[name][4+j]/factorial(j) for j in range(29)]
            even = sum(terms,Q(0))
            odd = sum(terms[:-1],Q(0))
            intervals.append((odd,even))
        lower = intervals[0][0]-intervals[1][1]
        upper = intervals[0][1]-intervals[1][0]
        assert lower <= upper
        assert lower > 0 if desired > 0 else upper < 0

    files = [
        SOURCE, CERTIFICATE,
        HERE/"certify_global_blind_interval.py",
        HERE/"global_blind_gain_proofs.txt",
        HERE/"global_detector_and_width_proofs.txt",
        Path(__file__).resolve(),
    ]
    report = {
        "result": "All exact rational replay checks passed.",
        "independence": (
            "Does not import the builder; uses Bernstein-product Horner "
            "conversion rather than affine power conversion."),
        "input_moment_status": (
            "The builder was also run with --rebuild-input in this session "
            "and matched all 0..32 moments to the original geometry engine. "
            "This replay verifies the saved table by its recorded hash."),
        "root_count_scope": "Exactly one simple root on (0,1/128]; no root-count claim above 1/128.",
        "files_sha256": {
            str(path.relative_to(BASE)): sha256(path.read_bytes()).hexdigest()
            for path in files
        },
    }
    output = HERE/"independent_blind_interval_replay.json"
    output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,indent=2))


if __name__ == "__main__":
    replay()
