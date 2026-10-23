"""Independent Arb recurrence and rational Cantelli certificates for a new design."""

from __future__ import annotations

import argparse
import json
import math
import sys
from fractions import Fraction
from hashlib import sha256
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(ROOT / "tool-runtime/python-flint-0.9.0"))
import flint
from flint import acb, arb, ctx

MODEL = (
    ROOT
    / "public-repo/evidence/homometric-photon-counts/science_completion/harmonic_certificate/input_model.json"
)
MODEL_SHA = "f4f3462b6aac8b56b152f63817cbf5de6848b3226f7dfe26cd29be87490c236f"
BETA = Fraction(17, 10)
RATIO = Fraction(201, 200)
VARIANCE = Fraction(1, 20)
SAMPLES = 5000


def ball(q):
    return arb(str(q))


def lo(value):
    if not value.is_finite():
        raise ValueError("Nonfinite enclosure")
    return Fraction(str(value.lower().fmpq()))


def hi(value):
    if not value.is_finite():
        raise ValueError("Nonfinite enclosure")
    return Fraction(str(value.upper().fmpq()))


def record(value):
    return {"lower": str(lo(value)), "upper": str(hi(value)), "display": str(value)}


def phase_lists(model, ratio=RATIO):
    # Use exact symbolic coordinate metadata. Rounded decimal positions are unused.
    offsets = {
        "none": arb(0),
        "theta": 3 / arb.pi() * (1 / (5 * arb(3).sqrt())).asin(),
        "phi": -3 / arb.pi() * (1 / (8 * arb(3).sqrt())).asin(),
    }
    return {
        g: [
            ball(ratio)
            * arb.pi()
            * (r["base_integer"] + r["offset_sign"] * offsets[r["offset_kind"]])
            for r in model["graphs"][g]["coordinates"]
        ]
        for g in "AB"
    }


def quantized_characteristic(theta, variance, difference, levels):
    """Wrapped-normal mean of exp(i*d*nearest_level(theta+Z)).

    Fourier modes are n=d+k*L with coefficient sinc(n*pi/L). Keep k=0
    and enclose every other mode with a geometric Gaussian tail bound.
    """
    d = abs(difference)
    if d == 0:
        return acb(1)
    if d >= levels or not variance > 0:
        raise ValueError("Require |d| < levels and positive variance")
    angle = arb.pi() * difference / levels
    main = acb(-variance * d * d / 2, difference * theta).exp() * angle.sin() / angle
    a = levels - d
    tail = 2 * (-variance * a * a / 2).exp() / (1 - (-variance * a * levels).exp())
    error = arb(0, tail.upper())
    return main + acb(error, error)


def mixed_moments(phases, variance, order, normalized_sites=None, levels=None):
    """Raw binomial site-append recurrence; independent of the NumPy EGF code."""
    n = len(phases) if normalized_sites is None else normalized_sites
    width = order + 1
    table = [[acb(0) for _ in range(width)] for _ in range(width)]
    table[0][0] = acb(1)
    damping = {
        (a, b): (-variance * (a - b) ** 2 / 2).exp()
        for a in range(width)
        for b in range(width)
    }
    for theta in phases:
        z = acb(0, theta).exp() / arb(n).sqrt()
        if levels is None:
            site = [
                [z**a * z.conjugate() ** b * damping[a, b] for b in range(width)]
                for a in range(width)
            ]
        else:
            harmonics = {
                d: quantized_characteristic(theta, variance, d, levels)
                for d in range(-order, order + 1)
            }
            site = [
                [harmonics[a - b] / arb(n).sqrt() ** (a + b) for b in range(width)]
                for a in range(width)
            ]
        new = [[acb(0) for _ in range(width)] for _ in range(width)]
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
                    acb(0),
                )
        table = new
    for k in range(width):
        if not table[k][k].imag.contains(0):
            raise ValueError("Diagonal mixed moment not real")
    return [table[k][k].real for k in range(width)]


def rate_moments(intensity, gain, background):
    # intensity[k] = E[(I/63)^k].
    return [
        sum(
            (
                math.comb(k, j)
                * background ** (k - j)
                * (63 * gain) ** j
                * intensity[j]
                for j in range(k + 1)
            ),
            arb(0),
        )
        for k in range(len(intensity))
    ]


def count_factorials(rates, afterpulse):
    # Poisson primaries, each followed by one Bernoulli child. No delay/cascade.
    return [
        sum(
            (
                math.factorial(k)
                * ((1 + afterpulse) ** (k - 2 * j))
                * afterpulse**j
                * rates[k - j]
                / (math.factorial(k - 2 * j) * math.factorial(j))
                for j in range(k // 2 + 1)
            ),
            arb(0),
        )
        for k in range(len(rates))
    ]


def score_statistics(factorials, gain=None):
    gain = arb(1) if gain is None else gain
    h = 63 * gain
    beta = ball(BETA)
    mean = factorials[2] / h**2 - beta * factorials[1] / h
    # (N)_2^2=(N)_4+4(N)_3+2(N)_2;
    # N*(N)_2=(N)_3+2(N)_2; N^2=(N)_2+N.
    second = (
        (factorials[4] + 4 * factorials[3] + 2 * factorials[2]) / h**4
        - 2 * beta * (factorials[3] + 2 * factorials[2]) / h**3
        + beta**2 * (factorials[2] + factorials[1]) / h**2
    )
    return mean, second, second - mean**2


def poisson_raw(rates):
    stirling = [[0] * len(rates) for _ in rates]
    stirling[0][0] = 1
    for n in range(1, len(rates)):
        for k in range(1, n + 1):
            stirling[n][k] = stirling[n - 1][k - 1] + k * stirling[n - 1][k]
    return [
        sum((stirling[n][k] * rates[k] for k in range(n + 1)), arb(0))
        for n in range(len(rates))
    ]


def dead_time_budgets(rates, d, gain=None):
    """Mean and raw-second-moment changes under initially-live dead-time thinning.

    Lost primaries <= C, the number of unordered primary pairs within d.
    E[f(N) C | lambda] = lambda^2*(d-d^2/2)*E[f(K+2)] with K~Poisson(lambda).
    |Y(N)-Y(N')| <= C*(2*N/h^2+beta/h), for 0<=N'<=N.
    |Y(N)^2-Y(N')^2| <= C*2*(N^2/h^2+beta*N/h)*(2*N/h^2+beta/h).
    """
    gain = arb(1) if gain is None else gain
    h, beta = 63 * gain, ball(BETA)
    # E[K^j | lambda] expressed in powers of lambda, for j <= 3.
    raw_polys = [[1], [0, 1], [0, 1, 1], [0, 1, 3, 1]]

    def pair_weighted(power):
        value = arb(0)
        for j in range(power + 1):
            for k, coefficient in enumerate(raw_polys[j]):
                value += (
                    math.comb(power, j) * 2 ** (power - j) * coefficient * rates[k + 2]
                )
        return (d - d * d / 2) * value

    first = 2 / h**2 * pair_weighted(1) + beta / h * pair_weighted(0)
    second = (
        4 / h**4 * pair_weighted(3)
        + 6 * beta / h**3 * pair_weighted(2)
        + 2 * beta**2 / h**2 * pair_weighted(1)
    )
    return first, second


def risk_record(mean, variance, threshold, is_low):
    distance = threshold - hi(mean) if is_low else lo(mean) - threshold
    if distance <= 0 or lo(variance) <= 0:
        raise ValueError("Invalid score separation or variance")
    upper = hi(variance)
    risk = upper / (upper + SAMPLES * distance**2)
    if risk >= Fraction(1, 20):
        raise ValueError("Five-percent target failed")
    return {
        "mean": record(mean),
        "variance_upper_bound_exact": str(upper),
        "variance_or_upper_bound_expression": record(variance),
        "threshold_distance_lower": str(distance),
        "each_error_upper_exact": str(risk),
        "each_error_upper_float": float(risk),
    }


def run(output):
    if output.exists() or output.is_relative_to(ROOT / "public-repo"):
        raise ValueError("Use a fresh local output directory")
    if flint.__version__ != "0.9.0":
        raise ValueError("Expected existing python-flint 0.9.0 runtime")
    ctx.prec = 256
    ctx.threads = 1
    raw = MODEL.read_bytes()
    if sha256(raw).hexdigest() != MODEL_SHA:
        raise ValueError("Geometry input identity changed")
    phases = phase_lists(json.loads(raw))
    intensity = {g: mixed_moments(phases[g], ball(VARIANCE), 5) for g in "AB"}
    quantized = {
        g: mixed_moments(phases[g], ball(VARIANCE), 5, levels=256) for g in "AB"
    }
    mean_gap = intensity["A"][1] - intensity["B"][1]
    if not mean_gap.contains(0):
        raise ValueError("Homometric mean check failed")
    scenarios = []
    for name, b, ap, dead, levels in [
        ("ideal", Fraction(0), Fraction(0), False, None),
        ("known_dark_counts", Fraction(1, 8), Fraction(0), False, None),
        (
            "known_dark_and_first_generation_afterpulse",
            Fraction(1, 8),
            Fraction(1, 200),
            False,
            None,
        ),
        ("known_dark_and_dead_time", Fraction(1, 8), Fraction(0), True, None),
        ("uniform_256_phase_levels_and_dark", Fraction(1, 8), Fraction(0), False, 256),
        (
            "uniform_256_phase_levels_dark_and_dead_time",
            Fraction(1, 8),
            Fraction(0),
            True,
            256,
        ),
    ]:
        stats, corrections = {}, {}
        for g in "AB":
            rates = rate_moments(
                (intensity if levels is None else quantized)[g], arb(1), ball(b)
            )
            mu, second, var = score_statistics(count_factorials(rates, ball(ap)))
            if dead:
                epsilon1, epsilon2 = dead_time_budgets(
                    rates, ball(Fraction(22, 5000000))
                )
                corrections[g] = {
                    "absolute_mean_change_upper": str(hi(epsilon1)),
                    "absolute_second_moment_change_upper": str(hi(epsilon2)),
                }
                mu = mu + arb(0, epsilon1.upper())
                # All means here are negative, so the square minimum is explicit.
                if hi(mu) >= 0:
                    raise ValueError("Mean interval crosses zero")
                var = second + epsilon2 - ball(hi(mu) ** 2)
            stats[g] = (mu, var)
        threshold = Fraction(
            str(round(float((stats["A"][0].mid() + stats["B"][0].mid()) / 2), 8))
        )
        risks = {g: risk_record(*stats[g], threshold, g == "A") for g in "AB"}
        scenarios.append(
            {
                "name": name,
                "background": str(b),
                "afterpulse_probability": str(ap),
                "dead_time_bound_applied": dead,
                "uniform_phase_levels": levels,
                "threshold_exact": str(threshold),
                "rule": "Choose A if sample mean score < threshold; otherwise B",
                "results": risks,
                "dead_time_corrections": corrections,
            }
        )
    result = {
        "status": "PASS_CONDITIONAL_INTERVAL_CERTIFICATES",
        "parameters": {
            "q_over_pi": str(RATIO),
            "site_phase_variance": str(VARIANCE),
            "gain": "1",
            "sites": 63,
            "snapshots": SAMPLES,
            "score": "N*(N-1)/3969 - (17/10)*N/63",
            "planning_hz": 10,
            "acquisition_seconds_at_planning_rate": SAMPLES / 10,
        },
        "scenarios": scenarios,
        "intensity_moments_normalized": {
            g: [record(x) for x in values] for g, values in intensity.items()
        },
        "quantized_intensity_moments_normalized": {
            g: [record(x) for x in values] for g, values in quantized.items()
        },
        "mean_homometry_residual": record(mean_gap),
        "second_intensity_moment_gap": record(
            (intensity["B"][2] - intensity["A"][2]) * 63**2
        ),
        "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "model_sha256": MODEL_SHA,
        "runtime": {
            "python": sys.version.split()[0],
            "python_flint": flint.__version__,
            "arb_precision_bits": ctx.prec,
        },
        "scope": "New frequency and unbinned second-factorial score, iid snapshots, known parameters and scenario-specific threshold. Arb plus analytic recurrence/Cantelli argument; not a Lean theorem or hardware validation. Afterpulse and dead-time scenarios are separate, not a joint detector model.",
    }
    output.mkdir(parents=True)
    (output / "certificate.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )
    print(
        json.dumps(
            {
                "status": result["status"],
                "parameters": result["parameters"],
                "scenarios": [
                    {
                        "name": r["name"],
                        "threshold": r["threshold_exact"],
                        "risks": {
                            g: x["each_error_upper_float"]
                            for g, x in r["results"].items()
                        },
                    }
                    for r in scenarios
                ],
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    run(parser.parse_args().output.resolve())
