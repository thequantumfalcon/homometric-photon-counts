"""Bounded optical robustness screen and independently seeded validation."""

from __future__ import annotations

import argparse
import itertools
import json
import math
from dataclasses import asdict, dataclass
from functools import lru_cache
from hashlib import sha256
from pathlib import Path

import baseline as b
import numpy as np
from scipy.stats import beta

HERE = Path(__file__).resolve().parent
BASE_SHA = "8dd6334a1866245d1b10e64c71d3d0b34e68a24c6d72e9ae95d756de9f48680a"
CONFIG = b.Bench()
Q = 201 * np.pi / 200
TRIALS = 200
SNAPSHOTS = 5000
VALIDATION_SEED = 2026102317


@dataclass(frozen=True)
class Case:
    name: str
    x_um: float = 0
    y_um: float = 0
    opd_nm: float = 0
    gain: float = 1
    variance: float = 0.05
    background: float = 0.125
    error_x_um: float = 0
    error_y_um: float = 0
    error_opd_nm: float = 0
    control: bool = False


def bindings():
    if sha256((HERE / "baseline.py").read_bytes()).hexdigest() != BASE_SHA:
        raise ValueError("Frozen baseline changed")
    b.coordinates()
    return {
        name: sha256((HERE / name).read_bytes()).hexdigest()
        for name in ("study.py", "baseline.py", "input_model.json")
    }


@lru_cache(maxsize=4096)
def coefficients(x_um=0, y_um=0, opd_nm=0, order=16):
    """Separable continuum Gaussian integral over each finite square cell."""
    nodes, weights = np.polynomial.legendre.leggauss(order)
    centers = (np.arange(8) - 3.5) * CONFIG.cell_pitch_m
    x = centers[:, None] + nodes * CONFIG.cell_pitch_m / 2
    alpha = (
        1 / CONFIG.pupil_mode_radius**2
        + 1 / CONFIG.illumination_radius_m**2
        - 2j * np.pi * opd_nm * 1e-9 / (CONFIG.wavelength_m * (CONFIG.width / 2) ** 2)
    )
    axes = []
    for delta in (x_um, y_um):
        tilt = 2 * np.pi * delta * 1e-6 / (CONFIG.wavelength_m * CONFIG.focal_length_m)
        axes.append(
            np.sum(np.exp(-alpha * x * x + 1j * tilt * x) * weights, axis=1)
            * CONFIG.cell_pitch_m
            / 2
        )
    return (
        np.sqrt(2 / np.pi) / CONFIG.pupil_mode_radius * np.outer(axes[1], axes[0])
    ).ravel()[:63]


def poppy_2d(x_um, y_um, opd_nm, n=256):
    """Independent sampled POPPY adjoint with a two-dimensional displaced mode."""
    field, cells = b.pupil(CONFIG, n, opd_nm)
    x, y = np.meshgrid(
        b.axis(CONFIG.image_width_m, 256), b.axis(CONFIG.image_width_m, 256)
    )
    mode = (
        np.sqrt(2 / np.pi)
        / CONFIG.fiber_radius_m
        * np.exp(
            -((x - x_um * 1e-6) ** 2 + (y - y_um * 1e-6) ** 2)
            / CONFIG.fiber_radius_m**2
        )
        * CONFIG.image_width_m
        / 256
    )
    nlamd = (
        CONFIG.image_width_m
        * CONFIG.width
        / (CONFIG.wavelength_m * CONFIG.focal_length_m)
    )
    back = b.MatrixFourierTransform(centering="SYMMETRIC").inverse(mode, nlamd, n)
    terms = back.conj() * field * CONFIG.width / n
    return np.array([terms[cells == j].sum() for j in range(63)])


def transfer(case):
    attenuation, common = b.calibration(CONFIG)
    actual = coefficients(case.x_um, case.y_um, case.opd_nm) * attenuation / common
    estimate = coefficients(
        case.x_um - case.error_x_um,
        case.y_um - case.error_y_um,
        case.opd_nm - case.error_opd_nm,
    )
    # One correction rule, using only the presumed separate optical calibration.
    return actual, -np.angle(estimate)


def intensity_moments(z, variances, order=4):
    """Finite independent-phasor recurrence, normalized by 63^k; no quantizer."""
    z = np.atleast_2d(z) / np.sqrt(63)
    variances = np.broadcast_to(variances, (len(z),))
    width = order + 1
    current = np.zeros((len(z), width, width), complex)
    current[:, 0, 0] = 1
    factors = {
        (a, c): np.exp(-variances * (a - c) ** 2 / 2)
        / (math.factorial(a) * math.factorial(c))
        for a in range(width)
        for c in range(width)
    }
    for site in range(z.shape[1]):
        powers = [z[:, site] ** a for a in range(width)]
        new = np.zeros_like(current)
        for a in range(width):
            for c in range(width):
                factor = factors[a, c] * powers[a] * powers[c].conj()
                new[:, a:, c:] += (
                    current[:, : width - a, : width - c] * factor[:, None, None]
                )
        current = new
    diagonal = np.stack(
        [current[:, k, k] * math.factorial(k) ** 2 for k in range(width)], axis=1
    )
    if np.max(abs(diagonal.imag) / np.maximum(1, abs(diagonal.real))) > 1e-9:
        raise ValueError("Excessive imaginary residue")
    return diagonal.real


def screen_cases(cases):
    coords = b.coordinates()
    transfers = [transfer(c) for c in cases]
    actual = np.stack([t[0] for t in transfers])
    correction = np.stack([t[1] for t in transfers])
    gains = np.array([c.gain for c in cases])
    backgrounds = np.array([c.background for c in cases])
    variances = np.array([c.variance for c in cases])
    output = [{"case": asdict(c), "uncorrected": {}, "corrected": {}} for c in cases]
    for method in ("uncorrected", "corrected"):
        for label in "AB":
            phases = np.stack([Q * coords["A" if c.control else label] for c in cases])
            if method == "corrected":
                phases += correction
            moments = intensity_moments(actual * np.exp(1j * phases), variances)
            rates = [
                sum(
                    math.comb(k, j)
                    * gains**j
                    * backgrounds ** (k - j)
                    * 63**j
                    * moments[:, j]
                    for j in range(k + 1)
                )
                for k in range(5)
            ]
            mean = rates[2] / 3969 - 1.7 * rates[1] / 63
            second = (
                rates[4] / 63**4
                + (4 / 63**4 - 3.4 / 63**3) * rates[3]
                + (2 / 63**4 - 6.8 / 63**3 + 1.7**2 / 63**2) * rates[2]
                + 1.7**2 / 63**2 * rates[1]
            )
            variance = second - mean**2
            if np.any(variance < -1e-10):
                raise ValueError("Negative variance")
            margin = b.THRESHOLD - mean if label == "A" else mean - b.THRESHOLD
            z = margin / np.sqrt(np.maximum(variance, 1e-20) / SNAPSHOTS)
            for i, row in enumerate(output):
                row[method][label] = {
                    "mean": float(mean[i]),
                    "variance": float(variance[i]),
                    "signed_margin": float(margin[i]),
                    "standardized_margin": float(z[i]),
                }
    return output


def numerical_checks():
    attenuation, common = b.calibration(CONFIG)
    records = []
    for x, y, d in [(0, 0, 0), (5, -5, 30), (-5, 5, -30), (5.5, 5.5, 35)]:
        exact = coefficients(x, y, d)
        refined = coefficients(x, y, d, 32)
        quadrature_error = float(np.max(abs(exact - refined) / common))
        errors = [
            float(np.max(abs((poppy_2d(x, y, d, n) - exact) * attenuation / common)))
            for n in (128, 256, 512)
        ]
        if (
            quadrature_error > 1e-12
            or errors[-1] > 3e-6
            or not errors[2] < errors[1] / 2 < errors[0] / 4
        ):
            raise ValueError("Two-dimensional optical check failed")
        records.append(
            {
                "x_um": x,
                "y_um": y,
                "opd_nm": d,
                "quadrature_16_32_difference": quadrature_error,
                "poppy_field_errors_128_256_512": errors,
            }
        )
    return records


def run_screen(output):
    hashes = bindings()
    output.mkdir(parents=True, exist_ok=False)
    checks = numerical_checks()
    line = [Case(f"x={x:g}", x_um=float(x)) for x in np.arange(-6, 6.001, 0.25)]
    plane = [
        Case(f"xy={x:g},{y:g}", x_um=float(x), y_um=float(y))
        for x, y in itertools.product(np.arange(-6, 6.001, 0.5), repeat=2)
    ]
    wave = [Case(f"opd={d:g}", opd_nm=float(d)) for d in np.arange(-40, 40.001, 2.5)]
    joint = [
        Case(f"joint-{i:03d}", *values)
        for i, values in enumerate(
            itertools.product(
                (-5.0, 5.0),
                (-5.0, 5.0),
                (-30.0, 30.0),
                (0.98, 1.02),
                (0.049, 0.051),
                (0.10, 0.15),
                (-0.5, 0.5),
                (-0.5, 0.5),
                (-5.0, 5.0),
            )
        )
    ]
    groups = {}
    for name, cases in [
        ("alignment_line", line),
        ("alignment_plane", plane),
        ("wavefront_line", wave),
        ("joint_corners", joint),
    ]:
        groups[name] = screen_cases(cases)
        print("Screened", name, len(cases), "points", flush=True)
    # Deterministic worst-case selection from the pre-validation proxy only.
    selected = [
        Case("centered"),
        Case("x-plus5", x_um=5),
        Case("x-minus5", x_um=-5),
        Case("y-plus5", y_um=5),
        Case("y-minus5", y_um=-5),
    ]
    for method, label in itertools.product(("uncorrected", "corrected"), "AB"):
        rows = sorted(
            groups["joint_corners"],
            key=lambda row: row[method][label]["standardized_margin"],
        )
        for row in rows[:2]:
            candidate = Case(**row["case"])
            if candidate not in selected:
                selected.append(candidate)
    # Bracket the signed-mean crossing on each side, without claiming a risk boundary.
    for sign in (-1, 1):
        rows = sorted(
            [r for r in groups["alignment_line"] if r["case"]["x_um"] * sign > 0],
            key=lambda r: abs(r["case"]["x_um"]),
        )
        crossing = next(
            (
                i
                for i, r in enumerate(rows)
                if min(r["uncorrected"][g]["signed_margin"] for g in "AB") <= 0
            ),
            None,
        )
        if crossing is not None:
            for row in rows[max(0, crossing - 1) : crossing + 1]:
                selected.append(Case(**row["case"]))
    selected.append(
        Case(
            "identical-mask-control",
            x_um=5,
            y_um=-5,
            opd_nm=30,
            error_x_um=0.5,
            error_y_um=-0.5,
            error_opd_nm=5,
            control=True,
        )
    )
    report = {
        "status": "FLOATING_POINT_SCREEN_ONLY",
        "source_hashes": hashes,
        "numerical_checks": checks,
        "groups": groups,
        "scope": "Finite grids and corners, unquantized Gaussian phases and Poisson primaries without dead time. No continuous tolerance certificate or risk estimate follows from a standardized margin.",
    }
    (output / "screen.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8"
    )
    plan = {
        "status": "FROZEN_BEFORE_VALIDATION",
        "source_hashes": hashes,
        "screen_sha256": sha256((output / "screen.json").read_bytes()).hexdigest(),
        "trials": TRIALS,
        "snapshots": SNAPSHOTS,
        "seed": VALIDATION_SEED,
        "threshold": b.THRESHOLD,
        "cases": [asdict(c) for c in selected],
        "correction": "Subtract arg of modeled separately estimated per-cell coefficient BEFORE uniform 256-level phase quantization. Keep original static amplitude mask, photon scale and classifier. Estimate = actual minus specified calibration error. No label/outcome used.",
        "decision_rule": "Promising at tested settings only if every corrected non-control A/B one-sided Bonferroni 95% upper error limit is below 5%. Identical-mask control reported separately. No adaptive reruns or pooled trials.",
        "family_size": 2 * sum(not c.control for c in selected),
    }
    (output / "validation-plan.json").write_text(
        json.dumps(plan, indent=2) + "\n", encoding="utf-8"
    )
    print("Frozen", len(selected), "validation settings", flush=True)


def quantized_field(phases):
    indices = np.remainder(np.rint(phases * 256 / (2 * np.pi)), 256).astype(np.int64)
    return np.exp(2j * np.pi * np.arange(256) / 256)[indices]


def run_validation(plan_path, output):
    hashes = bindings()
    plan = json.loads(plan_path.read_bytes())
    if plan["source_hashes"] != hashes or plan["threshold"] != b.THRESHOLD:
        raise ValueError("Plan/source/threshold mismatch")
    if (
        sha256((plan_path.parent / "screen.json").read_bytes()).hexdigest()
        != plan["screen_sha256"]
    ):
        raise ValueError("Screen binding mismatch")
    output.mkdir(parents=True, exist_ok=False)
    cases = [Case(**item) for item in plan["cases"]]
    transfers = [transfer(c) for c in cases]
    coords = b.coordinates()
    rows = [
        {
            "case": asdict(c),
            "uncorrected": {g: [] for g in "AB"},
            "corrected": {g: [] for g in "AB"},
        }
        for c in cases
    ]
    for li, label in enumerate("AB"):
        for trial in range(plan["trials"]):
            rng = np.random.default_rng(
                np.random.SeedSequence([plan["seed"], 0, li, trial])
            )
            standard_noise = rng.normal(size=(plan["snapshots"], 63))
            for ci, (case, row, (actual, correction)) in enumerate(
                zip(cases, rows, transfers)
            ):
                phases = (
                    Q * coords["A" if case.control else label]
                    + np.sqrt(case.variance) * standard_noise
                )
                for mi, method in enumerate(("uncorrected", "corrected")):
                    field = quantized_field(phases + (correction if mi else 0))
                    rates = case.gain * abs(field @ actual) ** 2 + case.background
                    detector_rng = np.random.default_rng(
                        np.random.SeedSequence([plan["seed"], 1, li, trial, ci, mi])
                    )
                    counts = b.detector_counts(
                        rates, detector_rng, CONFIG.dead_time_s / CONFIG.gate_s
                    )
                    row[method][label].append(float(b.score(counts).mean()))
            if (trial + 1) % 10 == 0:
                print(
                    f"Validation {label}: {trial + 1}/{plan['trials']} trials per setting",
                    flush=True,
                )
    passed = True
    for row in rows:
        row["classification"] = {}
        for method in ("uncorrected", "corrected"):
            row["classification"][method] = {}
            for label in "AB":
                values = np.array(row[method][label])
                errors = int(
                    np.count_nonzero(
                        values >= b.THRESHOLD if label == "A" else values < b.THRESHOLD
                    )
                )
                n = len(values)
                upper = (
                    1.0
                    if errors == n
                    else float(
                        beta.ppf(1 - 0.05 / plan["family_size"], errors + 1, n - errors)
                    )
                )
                stats = {
                    "errors": errors,
                    "trials": n,
                    "empirical_error": errors / n,
                    "binomial_95_interval": b.binomial_interval(errors, n),
                }
                if method == "corrected" and not row["case"]["control"]:
                    stats["simultaneous_one_sided_95_upper"] = upper
                    passed = passed and upper < 0.05
                row["classification"][method][label] = stats
    result = {
        "status": "PROMISING_AT_TESTED_SETTINGS"
        if passed
        else "REDESIGN_OR_TIGHTER_CALIBRATION_NEEDED",
        "plan_sha256": sha256(plan_path.read_bytes()).hexdigest(),
        "source_hashes": hashes,
        "configuration": asdict(CONFIG),
        "trials": plan["trials"],
        "snapshots": plan["snapshots"],
        "threshold": b.THRESHOLD,
        "family_size": plan["family_size"],
        "scenarios": rows,
        "scope": "Synthetic held-out trials, with phase quantization and exact renewal dead time. Independent trials within each setting/label; phase draws shared across settings and methods. Bonferroni does not require independence across settings. Fixed calibration residuals, no calibration data acquired. No continuous-box, physical-validation or novelty claim.",
    }
    (output / "validation.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )
    print(result["status"], flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage", choices=("screen", "validate"))
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--plan", type=Path)
    args = parser.parse_args()
    if args.stage == "screen":
        run_screen(args.output.resolve())
    else:
        if args.plan is None:
            parser.error("validate requires --plan")
        run_validation(args.plan.resolve(), args.output.resolve())
