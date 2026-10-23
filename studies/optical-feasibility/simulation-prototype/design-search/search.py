"""Bounded design screen; floating-point rankings are not certificates."""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import sys
from fractions import Fraction
from hashlib import sha256
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE_SHA = "86e8ab0f8ba754ba7751e2e3cfdcb22a154212dbde49c2e96345d504f38dfa9d"


def inputs():
    path = HERE.parent / "simulate.py"
    if sha256(path.read_bytes()).hexdigest() != BASE_SHA:
        raise ValueError("Base simulator identity changed")
    spec = importlib.util.spec_from_file_location("photon_base", path)
    base = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = base
    spec.loader.exec_module(base)
    model, _, _ = base.read_inputs(ROOT / "public-repo")
    offsets = {
        "none": 0,
        "theta": 3 / np.pi * np.arcsin(1 / (5 * np.sqrt(3))),
        "phi": -3 / np.pi * np.arcsin(1 / (8 * np.sqrt(3))),
    }
    coordinates = {
        g: np.array(
            [
                r["base_integer"] + r["offset_sign"] * offsets[r["offset_kind"]]
                for r in model["graphs"][g]["coordinates"]
            ]
        )
        for g in "AB"
    }
    return base, model, coordinates


def intensity_moments(phases, variances, order):
    """E[(I/n)^k], via truncated exponential-generating-function convolution.

    Each site's (a,b) coefficient is
    z^a conjugate(z)^b exp(-s*(a-b)^2/2)/(a! b!), z=exp(i*theta)/sqrt(n).
    Independence multiplies generating functions. The (k,k) coefficient times
    (k!)^2 is the normalized intensity moment. All sites are processed.
    """
    phases = np.atleast_2d(phases)
    variances = np.broadcast_to(variances, (len(phases),))
    width, n = order + 1, phases.shape[1]
    current = np.zeros((len(phases), width, width), dtype=complex)
    current[:, 0, 0] = 1
    gaussian = {
        (a, b): np.exp(-variances * (a - b) ** 2 / 2)
        / (math.factorial(a) * math.factorial(b) * n ** ((a + b) / 2))
        for a in range(width)
        for b in range(width)
    }
    for site in range(n):
        new = np.zeros_like(current)
        for a in range(width):
            for b in range(width):
                factor = gaussian[a, b] * np.exp(1j * (a - b) * phases[:, site])
                new[:, a:, b:] += (
                    current[:, : width - a, : width - b] * factor[:, None, None]
                )
        current = new
    moments = np.stack(
        [current[:, k, k] * math.factorial(k) ** 2 for k in range(width)], axis=1
    )
    if np.max(np.abs(moments.imag) / np.maximum(1, np.abs(moments.real))) > 1e-7:
        raise ValueError("Moment calculation has excessive imaginary residue")
    return moments.real


def score_covariance(moments, effective_gain, degree):
    """Covariance of (N)_j/(eta*n)^j; infinity denotes ideal I/n powers."""
    out = np.zeros((degree, degree))
    for j in range(1, degree + 1):
        for k in range(1, degree + 1):
            raw = sum(
                math.comb(j, r)
                * math.comb(k, r)
                * math.factorial(r)
                * moments[j + k - r]
                * (1 if r == 0 else effective_gain ** (-r))
                for r in range(min(j, k) + 1)
            )
            out[j - 1, k - 1] = raw - moments[j] * moments[k]
    return out


def screen_score(a, b, gain, degree, prescribed_gap=None):
    covs = [score_covariance(m, gain * 63, degree) for m in (a, b)]
    pooled = (covs[0] + covs[1]) / 2
    coefficients = np.r_[-np.linalg.solve(pooled[:-1, :-1], pooled[:-1, -1]), 1.0]
    delta = (
        float(coefficients @ (a[1 : degree + 1] - b[1 : degree + 1]))
        if prescribed_gap is None
        else prescribed_gap
    )
    variances = [float(coefficients @ cov @ coefficients) for cov in covs]
    if min(variances) <= 0 or delta == 0:
        return None
    sufficient = math.floor(76 * max(variances) / delta**2) + 1
    return {
        "gain": None if math.isinf(gain) else gain,
        "measurement": "ideal_intensity" if math.isinf(gain) else "unbinned_count",
        "degree": degree,
        "coefficients": coefficients.tolist(),
        "score_gap_A_minus_B_float": delta,
        "score_variances_float": variances,
        "cantelli_sufficient_snapshots_float": sufficient,
    }


def run(output):
    if output.exists() or output.is_relative_to(ROOT / "public-repo"):
        raise ValueError("Use a fresh local output directory")
    _, _, coords = inputs()
    gains = [0.05, 0.2, 1.0, 5.0, 20.0, math.inf]
    specs = [
        (Fraction(r, 200), s)
        for r in range(30, 391)
        for s in (0.05, 0.1, 0.25, 0.5, 1, 2)
    ]
    ratios = np.array([float(q) for q, _ in specs])
    variances = np.array([s for _, s in specs])
    moments = {
        g: intensity_moments(np.pi * ratios[:, None] * coords[g], variances, 4)
        for g in "AB"
    }
    rows = []
    for i, (ratio, s) in enumerate(specs):
        for gain in gains:
            result = screen_score(moments["A"][i], moments["B"][i], gain, 2)
            if result:
                rows.append(dict(q_over_pi=str(ratio), variance=s, **result))
    rows.sort(key=lambda r: r["cantelli_sufficient_snapshots_float"])
    print("Changed-frequency screen complete", flush=True)
    original_s = np.array([0.05, 0.1, 0.25, 0.5, 1, 2 * np.log(2), 2, 4])
    original_m = {
        g: intensity_moments(
            np.tile(np.pi / 3 * coords[g], (len(original_s), 1)), original_s, 8
        )
        for g in "AB"
    }
    original = []
    for i, s in enumerate(original_s):
        x = np.exp(-s)
        delta = (
            455015761
            / 20000
            * x**4
            * (1 - x) ** 5
            * (x**3 + 3 * x * x + 6 * x + 6)
            / 63**4
        )
        for gain in gains:
            result = screen_score(
                original_m["A"][i], original_m["B"][i], gain, 4, delta
            )
            if result:
                original.append(dict(q_over_pi="1/3", variance=float(s), **result))
    original.sort(key=lambda r: r["cantelli_sufficient_snapshots_float"])
    count_rows = [r for r in rows if r["measurement"] == "unbinned_count"]
    # Freeze a reasonably bright count design if it passes the existing budget.
    moderate = [
        r
        for r in count_rows
        if r["gain"] <= 1 and r["cantelli_sufficient_snapshots_float"] < 288000
    ]
    selected = moderate[0] if moderate else count_rows[0]
    result = {
        "status": "EXPLORATORY_RANKING_REQUIRES_INTERVAL_REPLAY",
        "candidate_count": len(rows),
        "frequency_grid": {"q_over_pi_min": "3/20", "max": "39/20", "step": "1/200"},
        "variance_grid": [0.05, 0.1, 0.25, 0.5, 1, 2],
        "gain_grid": [0.05, 0.2, 1, 5, 20, "ideal_intensity"],
        "selected": selected,
        "best_20": rows[:20],
        "best_per_count_gain": {
            str(g): next(r for r in rows if r["gain"] == g) for g in gains[:-1]
        },
        "original_frequency_screen": original,
        "mean_homometry_max_float_residual": float(
            np.max(np.abs(moments["A"][:, 1] - moments["B"][:, 1]))
        ),
        "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": "Finite-grid second-moment screen at changed frequency, plus fourth-moment controls at original frequency. No global optimization, physical claim, or simulated detection result.",
    }
    output.mkdir(parents=True)
    (output / "search.json").write_text(
        json.dumps(result, indent=2, allow_nan=False) + "\n", encoding="utf-8"
    )
    print(
        json.dumps(
            {
                "selected": selected,
                "best_original": original[0],
                "candidates": len(rows),
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    run(parser.parse_args().output.resolve())
