"""Continuous calibration-box certificate with a fixed count score and threshold."""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import sys
from fractions import Fraction
from hashlib import sha256
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
PREVIOUS = HERE.parent / "design-search"
BASE_SHA = "4e24dc4c9615237c7c384ff47e8fb30a78222ca33b57a4908beb1f5da16d6992"
CERT_SHA = "35b377ca00f58b93e7d0dc1eb657a3d00b82fc130c478723f6019e3646d3be8a"
path = PREVIOUS / "certify.py"
if sha256(path.read_bytes()).hexdigest() != BASE_SHA:
    raise ValueError("Previous evaluator identity changed")
spec = importlib.util.spec_from_file_location("prior_certificate", path)
c = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = c
spec.loader.exec_module(c)
from flint import acb, acb_poly, arb, arb_poly

F = Fraction
G0, B0, S0 = F(1), F(1, 8), F(1, 20)
THRESHOLD = F(-3200551, 5000000)
MIN_S = F(1, 25)
DEAD_MAX = F(22, 5000000)
SAMPLES = 5000


def interval(center, radius):
    return c.ball(center) + arb(0, c.ball(radius).upper())


def moment_polynomials(phases, order=5, levels=256):
    """Moments of J=I/n as real ball-coefficient polynomials in t=exp(-s/2).

    Quantizer aliases are coefficient enclosures uniform for s>=MIN_S. Thus
    every actual moment at each s has a representing polynomial in this family;
    the same alias coefficients need not represent all s simultaneously.
    """
    n, width = len(phases), order + 1
    table = [[acb_poly() for _ in range(width)] for _ in range(width)]
    table[0][0] = acb_poly([1])
    quantizer = {}
    for d in range(-order, order + 1):
        if d == 0 or levels is None:
            quantizer[d] = (arb(1), arb(0))
        else:
            if abs(d) >= levels:
                raise ValueError("Moment order must be below number of levels")
            angle = arb.pi() * d / levels
            a = levels - abs(d)
            tail = (
                2
                * (-c.ball(MIN_S) * a * a / 2).exp()
                / (1 - (-c.ball(MIN_S) * a * levels).exp())
            )
            quantizer[d] = (angle.sin() / angle, arb(0, tail.upper()))
    for theta in phases:
        phase = acb(0, theta).exp()
        site = []
        for a in range(width):
            row = []
            for b in range(width):
                d = a - b
                sinc, error = quantizer[d]
                normalization = arb(n).sqrt() ** (a + b)
                coefficient = phase**a * phase.conjugate() ** b * sinc / normalization
                polynomial = acb_poly([coefficient]).left_shift(d * d)
                if d and levels is not None:
                    polynomial += acb_poly([acb(error, error) / normalization])
                row.append(polynomial)
            site.append(row)
        new = [[acb_poly() for _ in range(width)] for _ in range(width)]
        for p in range(width):
            for q in range(width):
                new[p][q] = sum(
                    (
                        math.comb(p, a)
                        * math.comb(q, b)
                        * table[p - a][q - b]
                        * site[a][b]
                        for a in range(p + 1)
                        for b in range(q + 1)
                    ),
                    acb_poly(),
                )
        table = new
    result = []
    for k in range(width):
        coefficients = table[k][k].coeffs()
        if not all(value.imag.contains(0) for value in coefficients):
            raise ValueError("Nonreal diagonal moment coefficients")
        result.append(arb_poly([value.real for value in coefficients]))
        if result[-1].degree() > 2 * k * k:
            raise ValueError("Moment degree bound exceeded")
    return result


# Polynomials in gain/background with arb_poly(t) coefficients.
def add(*polynomials):
    result = {}
    for polynomial in polynomials:
        for key, value in polynomial.items():
            result[key] = result.get(key, arb_poly()) + value
    return result


def scale(polynomial, scalar):
    return {key: value * c.ball(scalar) for key, value in polynomial.items()}


def multiply(left, right):
    result = {}
    for (a, b), p in left.items():
        for (j, k), q in right.items():
            key = a + j, b + k
            result[key] = result.get(key, arb_poly()) + p * q
    return result


def score_polynomials(moments):
    rates = [
        {(j, k - j): moments[j] * (math.comb(k, j) * 63**j) for j in range(k + 1)}
        for k in range(6)
    ]
    mean = add(scale(rates[2], F(1, 3969)), scale(rates[1], -c.BETA / 63))
    second = add(
        scale(rates[4], F(1, 63**4)),
        scale(rates[3], F(4, 63**4) - 2 * c.BETA / 63**3),
        scale(rates[2], F(2, 63**4) - 4 * c.BETA / 63**3 + c.BETA**2 / 63**2),
        scale(rates[1], c.BETA**2 / 63**2),
    )
    variance = add(second, scale(multiply(mean, mean), -1))
    # E[N^j C] for Poisson primaries, with the geometric pair factor omitted.
    weighted = [
        rates[2],
        add(rates[3], scale(rates[2], 2)),
        add(rates[4], scale(rates[3], 5), scale(rates[2], 4)),
        add(rates[5], scale(rates[4], 9), scale(rates[3], 19), scale(rates[2], 8)),
    ]
    factor = DEAD_MAX - DEAD_MAX**2 / 2
    eps1 = scale(
        add(scale(weighted[1], F(2, 63**2)), scale(weighted[0], c.BETA / 63)), factor
    )
    eps2 = scale(
        add(
            scale(weighted[3], F(4, 63**4)),
            scale(weighted[2], 6 * c.BETA / 63**3),
            scale(weighted[1], 2 * c.BETA**2 / 63**2),
        ),
        factor,
    )
    return {
        "mean": mean,
        "variance": variance,
        "dead_mean_change": eps1,
        "dead_second_change": eps2,
    }


def shift_t(polynomial, center):
    coefficients = polynomial.coeffs()
    return arb_poly(
        [
            sum(
                (
                    coefficients[j] * math.comb(j, k) * center ** (j - k)
                    for j in range(k, len(coefficients))
                ),
                arb(0),
            )
            for k in range(len(coefficients))
        ]
    )


def translate(polynomial):
    center = (-c.ball(S0) / 2).exp()
    result = {}
    for (a, b), value in polynomial.items():
        shifted = shift_t(value, center)
        for i in range(a + 1):
            for j in range(b + 1):
                term = shifted * c.ball(
                    math.comb(a, i) * math.comb(b, j) * G0 ** (a - i) * B0 ** (b - j)
                )
                result[i, j] = result.get((i, j), arb_poly()) + term
    return result


def integer_power(value, exponent):
    # Generic real powers may be undefined for intervals crossing zero.
    if not isinstance(exponent, int) or exponent < 0:
        raise ValueError("Nonnegative integer exponent required")
    result = arb(1)
    for _ in range(exponent):
        result *= value
    return result


def evaluate(shifted, gain, background, variance):
    dt = (-variance / 2).exp() - (-c.ball(S0) / 2).exp()
    dg, db = gain - c.ball(G0), background - c.ball(B0)
    return sum(
        (
            value(dt) * integer_power(dg, a) * integer_power(db, b)
            for (a, b), value in shifted.items()
        ),
        arb(0),
    )


def check_box(shifted, gain_radius, background_radius, variance_radius, dead=True):
    if (
        min(gain_radius, background_radius, variance_radius) < 0
        or S0 - variance_radius < MIN_S
        or G0 - gain_radius <= 0
        or B0 - background_radius < 0
    ):
        raise ValueError("Unsupported parameter box")
    arguments = [
        interval(G0, gain_radius),
        interval(B0, background_radius),
        interval(S0, variance_radius),
    ]
    records = {}
    for label in "AB":
        values = {
            key: evaluate(poly, *arguments) for key, poly in shifted[label].items()
        }
        mu = values["mean"]
        variance_upper = c.hi(values["variance"])
        epsilon1 = epsilon2 = F(0)
        if dead:
            epsilon1 = max(F(0), c.hi(values["dead_mean_change"]))
            epsilon2 = max(F(0), c.hi(values["dead_second_change"]))
            magnitude = max(abs(c.lo(mu)), abs(c.hi(mu)))
            # Var(Y') <= Var(Y)+eps2+2*|E Y|*eps1.
            variance_upper += epsilon2 + 2 * magnitude * epsilon1
            mu += arb(0, c.ball(epsilon1).upper())
        distance = THRESHOLD - c.hi(mu) if label == "A" else c.lo(mu) - THRESHOLD
        risk = (
            variance_upper / (variance_upper + SAMPLES * distance**2)
            if distance > 0 and variance_upper > 0
            else F(1)
        )
        records[label] = {
            "mean_enclosure": c.record(mu),
            "variance_upper_exact": str(variance_upper),
            "distance_lower_exact": str(distance),
            "risk_upper_exact": str(risk),
            "risk_upper_float": float(risk),
            "dead_mean_change_upper": str(epsilon1),
            "dead_second_change_upper": str(epsilon2),
            "sufficient_samples_for_5pct": (
                math.floor(19 * variance_upper / distance**2) + 1
                if distance > 0 and variance_upper > 0
                else None
            ),
        }
    return {
        "gain_radius": str(gain_radius),
        "background_radius": str(background_radius),
        "variance_radius": str(variance_radius),
        "dead_time_up_to_22ns": dead,
        "status": "PASS"
        if all(F(r["risk_upper_exact"]) < F(1, 20) for r in records.values())
        else "NOT_CERTIFIED",
        "results": records,
        "sufficient_samples_for_5pct": (
            max(r["sufficient_samples_for_5pct"] for r in records.values())
            if all(
                r["sufficient_samples_for_5pct"] is not None for r in records.values()
            )
            else None
        ),
    }


def run(output):
    if output.exists() or output.is_relative_to(ROOT / "public-repo"):
        raise ValueError("Use a fresh local output directory")
    if c.flint.__version__ != "0.9.0":
        raise ValueError("Expected python-flint 0.9.0")
    c.ctx.prec = 256
    prior = (PREVIOUS / "interval-final/certificate.json").read_bytes()
    if sha256(prior).hexdigest() != CERT_SHA:
        raise ValueError("Previous certificate changed")
    model_raw = c.MODEL.read_bytes()
    if sha256(model_raw).hexdigest() != c.MODEL_SHA:
        raise ValueError("Geometry changed")
    phases = c.phase_lists(json.loads(model_raw))
    polynomials = {g: moment_polynomials(phases[g]) for g in "AB"}
    shifted = {
        g: {
            name: translate(poly)
            for name, poly in score_polynomials(polynomials[g]).items()
        }
        for g in "AB"
    }
    rows = []
    for factor in [F(0), F(1, 4), F(1, 2), F(1), F(2), F(4)]:
        row = check_box(shifted, factor / 50, factor / 40, factor / 1000)
        rows.append(row)
        print(
            json.dumps(
                {
                    "factor": str(factor),
                    "status": row["status"],
                    "risks": {
                        g: r["risk_upper_float"] for g, r in row["results"].items()
                    },
                }
            ),
            flush=True,
        )
    result = {
        "status": "CALIBRATION_BOX_STUDY_COMPLETE",
        "fixed_score": "N*(N-1)/3969-(17/10)*N/63",
        "fixed_threshold": str(THRESHOLD),
        "snapshots": SAMPLES,
        "centers": {"gain": str(G0), "background": str(B0), "phase_variance": str(S0)},
        "q_over_pi": "201/200",
        "uniform_phase_levels": 256,
        "box_checks": rows,
        "moment_polynomial_degrees": {
            g: [p.degree() for p in values] for g, values in polynomials.items()
        },
        "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "previous_evaluator_sha256": BASE_SHA,
        "previous_certificate_sha256": CERT_SHA,
        "input_model_sha256": c.MODEL_SHA,
        "runtime": {
            "python": sys.version.split()[0],
            "python_flint": c.flint.__version__,
            "precision_bits": c.ctx.prec,
        },
        "scope": "Uniform interval bounds over each continuous gain/background/phase-variance box. Fixed score and threshold, fixed exact spatial frequency and equal field amplitudes; independent identically distributed snapshots with fixed unknown parameters inside the box. Uniform ideal 256-level quantizer, Poisson background and initially-live nonparalyzable dead time at most 22 ns per 5 ms gate. No afterpulsing, optical transfer error, temporal dependence, new Lean theorem or hardware validation.",
    }
    output.mkdir(parents=True)
    (output / "calibration.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    run(parser.parse_args().output.resolve())
