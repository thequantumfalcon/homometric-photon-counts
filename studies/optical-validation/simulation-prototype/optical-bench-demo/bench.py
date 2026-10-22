"""POPPY optical-bench emulator; floating-point simulation, not physical validation."""

from __future__ import annotations

import argparse
import json
import platform
from dataclasses import asdict, dataclass
from hashlib import sha256
from pathlib import Path

import numpy as np
import poppy
from poppy.matrixDFT import MatrixFourierTransform
from scipy.special import erf
from scipy.stats import beta

HERE = Path(__file__).resolve().parent
MODEL_SHA = "4b9b37a013347b2bd8a273bd2e1be2c867986f2287e1012d6ea9488ed515b288"
THRESHOLD = -0.6401102


@dataclass(frozen=True)
class Bench:
    wavelength_m: float = 633e-9
    focal_length_m: float = 0.100
    cell_pitch_m: float = 200e-6
    illumination_radius_m: float = 3e-3
    fiber_radius_m: float = 10e-6
    image_width_m: float = 160e-6
    phase_variance: float = 0.05
    background_per_gate: float = 0.125
    gate_s: float = 0.005
    dead_time_s: float = 22e-9
    phase_levels: int = 256

    @property
    def width(self):
        return 8 * self.cell_pitch_m

    @property
    def pupil_mode_radius(self):
        return self.wavelength_m * self.focal_length_m / (np.pi * self.fiber_radius_m)


def coordinates():
    raw = (HERE / "input_model.json").read_bytes()
    if sha256(raw).hexdigest() != MODEL_SHA:
        raise ValueError("Geometry input changed")
    data = json.loads(raw)
    offsets = {
        "none": 0,
        "theta": 3 / np.pi * np.arcsin(1 / (5 * np.sqrt(3))),
        "phi": -3 / np.pi * np.arcsin(1 / (8 * np.sqrt(3))),
    }
    return {
        g: np.array(
            [
                r["base_integer"] + r["offset_sign"] * offsets[r["offset_kind"]]
                for r in data["graphs"][g]["coordinates"]
            ]
        )
        for g in "AB"
    }


def axis(width, n):
    return (np.arange(n) - n / 2 + 0.5) * width / n


def pupil(config, npup, defocus_nm=0):
    if npup % 8:
        raise ValueError("Pupil grid must resolve eight complete cells per side")
    x, y = np.meshgrid(axis(config.width, npup), axis(config.width, npup))
    ids = np.arange(npup) // (npup // 8)
    cells = ids[:, None] * 8 + ids[None, :]
    illumination = np.exp(-(x * x + y * y) / config.illumination_radius_m**2)
    # Declared quadratic optical-path screen, not a claim about a particular lens.
    opd = defocus_nm * 1e-9 * (x * x + y * y) / (config.width / 2) ** 2
    field = illumination * np.exp(2j * np.pi * opd / config.wavelength_m)
    field[cells == 63] = 0
    return field, cells


def fiber_mode(config, nimage, offset_um=0):
    x, y = np.meshgrid(
        axis(config.image_width_m, nimage), axis(config.image_width_m, nimage)
    )
    g = (
        np.sqrt(2 / np.pi)
        / config.fiber_radius_m
        * np.exp(-((x - offset_um * 1e-6) ** 2 + y * y) / config.fiber_radius_m**2)
    )
    # Pixel-integrated-amplitude convention: squared Euclidean norm is power.
    return g * config.image_width_m / nimage


def poppy_coefficients(config, npup=256, nimage=256, offset_um=0, defocus_nm=0):
    field, cells = pupil(config, npup, defocus_nm)
    nlamd = (
        config.image_width_m
        * config.width
        / (config.wavelength_m * config.focal_length_m)
    )
    mft = MatrixFourierTransform(centering="SYMMETRIC")
    back = mft.inverse(fiber_mode(config, nimage, offset_um), nlamd, npup)
    terms = back.conj() * field * config.width / npup
    return (
        np.bincount(cells.ravel(), weights=terms.real.ravel(), minlength=64)
        + 1j * np.bincount(cells.ravel(), weights=terms.imag.ravel(), minlength=64)
    )[:63]


def quadrature_coefficients(config, offset_um=0, defocus_nm=0, order=16):
    """Independent continuum integral of the analytic back-propagated Gaussian mode."""
    nodes, weights = np.polynomial.legendre.leggauss(order)
    centers = (np.arange(8) - 3.5) * config.cell_pitch_m
    result = []
    wp = config.pupil_mode_radius
    for row in range(8):
        for col in range(8):
            if row * 8 + col == 63:
                continue
            x, y = np.meshgrid(
                centers[col] + nodes * config.cell_pitch_m / 2,
                centers[row] + nodes * config.cell_pitch_m / 2,
            )
            r2 = x * x + y * y
            envelope = (
                np.sqrt(2 / np.pi)
                / wp
                * np.exp(-r2 / wp**2 - r2 / config.illumination_radius_m**2)
            )
            # POPPY 1.2 uses a positive Fourier exponent for forward propagation.
            tilt = (
                2
                * np.pi
                * x
                * offset_um
                * 1e-6
                / (config.wavelength_m * config.focal_length_m)
            )
            aberration = (
                2
                * np.pi
                * defocus_nm
                * 1e-9
                * r2
                / (config.wavelength_m * (config.width / 2) ** 2)
            )
            result.append(
                np.sum(
                    envelope
                    * np.exp(1j * (tilt + aberration))
                    * np.outer(weights, weights)
                )
                * (config.cell_pitch_m / 2) ** 2
            )
    return np.array(result)


def closed_form_centered(config):
    a = 1 / config.pupil_mode_radius**2 + 1 / config.illumination_radius_m**2
    edges = (np.arange(9) - 4) * config.cell_pitch_m
    one = np.sqrt(np.pi) / (2 * np.sqrt(a)) * np.diff(erf(np.sqrt(a) * edges))
    return (np.sqrt(2 / np.pi) / config.pupil_mode_radius * np.outer(one, one)).ravel()[
        :63
    ]


def calibration(config):
    c = closed_form_centered(config)
    common = float(c.min())
    # Attenuation only, fixed from the modeled centered transfer before any trial.
    attenuation = common / c
    return attenuation, common


def forward_image(config, phases, attenuation, npup=256, nimage=256, defocus_nm=0):
    field, cells = pupil(config, npup, defocus_nm)
    factors = np.r_[attenuation * np.exp(1j * phases), 0]
    plane = field * factors[cells] * config.width / npup
    nlamd = (
        config.image_width_m
        * config.width
        / (config.wavelength_m * config.focal_length_m)
    )
    return MatrixFourierTransform(centering="SYMMETRIC").perform(
        plane, nlamd, nimage
    ), plane


def detector_counts(rates, rng, dead_fraction=0):
    """Exact renewal sampling for initially-live nonparalyzable Poisson detection.

    Rates are expected primary counts in one gate. Every accepted event is
    followed by dead_fraction plus an independent exponential waiting time.
    Rejected Poisson arrivals cannot extend the dead period. No afterpulsing.
    """
    rates = np.asarray(rates, dtype=float)
    if np.any(rates < 0) or not np.all(np.isfinite(rates)) or dead_fraction < 0:
        raise ValueError("Invalid detector inputs")
    if dead_fraction == 0:
        return rng.poisson(rates)
    scale = np.divide(1.0, rates, out=np.full_like(rates, np.inf), where=rates > 0)
    arrival = rng.exponential(scale)
    counts = np.zeros(rates.shape, dtype=np.int64)
    alive = arrival < 1
    while alive.any():
        counts[alive] += 1
        arrival[alive] += dead_fraction + rng.exponential(scale[alive])
        alive = arrival < 1
    return counts


def score(counts):
    return counts * (counts - 1) / 3969 - 1.7 * counts / 63


def binomial_interval(errors, trials):
    return [
        0.0 if errors == 0 else float(beta.ppf(0.025, errors, trials - errors + 1)),
        1.0
        if errors == trials
        else float(beta.ppf(0.975, errors + 1, trials - errors)),
    ]


def numerical_checks(config):
    attenuation, common = calibration(config)
    checks = []
    for shift, defocus in [
        (0, 0),
        (0.5, 0),
        (1, 0),
        (2, 0),
        (5, 0),
        (-5, 0),
        (0, 30),
        (0, -30),
    ]:
        exact = quadrature_coefficients(config, shift, defocus)
        previous = None
        for n in (64, 128, 256, 512):
            c = poppy_coefficients(config, n, 256, shift, defocus)
            error = float(np.max(np.abs((c - exact) * attenuation / common)))
            checks.append(
                {
                    "offset_um": shift,
                    "defocus_nm": defocus,
                    "npup": n,
                    "maximum_effective_field_error": error,
                }
            )
            if previous is not None and error >= previous / 2:
                raise ValueError("Pupil refinement failed to reduce transfer error")
            previous = error
        if previous > 5e-6:
            raise ValueError("Finest-grid transfer discrepancy is too large")
    c128 = poppy_coefficients(config, 256, 128, 2)
    c256 = poppy_coefficients(config, 256, 256, 2)
    focal_error = float(np.max(np.abs((c128 - c256) * attenuation / common)))
    if focal_error > 1e-10:
        raise ValueError("Focal-plane sampling is insufficient")
    rng = np.random.default_rng(819)
    phases = rng.uniform(-np.pi, np.pi, 63)
    image, plane = forward_image(config, phases, attenuation, defocus_nm=30)
    direct = np.vdot(fiber_mode(config, 256, 2), image)
    reduced = np.sum(
        poppy_coefficients(config, 256, 256, 2, 30) * attenuation * np.exp(1j * phases)
    )
    adjoint_error = float(abs(direct - reduced) / common)
    if adjoint_error > 1e-11:
        raise ValueError("Forward propagation and reduced count model disagree")
    norm = float(np.sum(abs(fiber_mode(config, 256)) ** 2))
    if abs(norm - 1) > 1e-12:
        raise ValueError("Fiber mode is not normalized")
    return {
        "status": "PASS_NUMERICAL_CHECKS",
        "refinement": checks,
        "focal_refinement_error": focal_error,
        "forward_adjoint_error": adjoint_error,
        "fiber_norm": norm,
        "calibrated_pupil_power_units": float(np.sum(abs(plane) ** 2)),
        "primary_budget_per_gate_at_gain_one": float(
            np.sum(abs(plane) ** 2) / common**2
        ),
    }


def run(output, trials=100, snapshots=5000):
    if output.exists() or trials < 2 or snapshots < 2:
        raise ValueError("Use a fresh output folder and at least two trials/snapshots")
    if poppy.__version__ != "1.2.0":
        raise ValueError("This checkpoint requires POPPY 1.2.0")
    output.mkdir(parents=True)
    config = Bench()
    checks = numerical_checks(config)
    attenuation, common = calibration(config)
    cases = [
        ("Centered, modeled calibration", 0.0, 0.0, False),
        ("Fiber shifted 0.5 um", 0.5, 0.0, False),
        ("Fiber shifted 1 um", 1.0, 0.0, False),
        ("Fiber shifted 2 um", 2.0, 0.0, False),
        ("Fiber shifted 5 um", 5.0, 0.0, False),
        ("Fiber shifted -5 um", -5.0, 0.0, False),
        ("Quadratic phase coefficient +30 nm", 0.0, 30.0, False),
        ("Quadratic phase coefficient -30 nm", 0.0, -30.0, False),
        ("Identical-mask negative control", 0.0, 0.0, True),
    ]
    weights = np.stack(
        [
            poppy_coefficients(config, 256, 256, shift, defocus) * attenuation / common
            for _, shift, defocus, _ in cases
        ]
    )
    coords = coordinates()
    results = [
        {
            "name": name,
            "offset_um": shift,
            "defocus_nm": defocus,
            "identical_masks": control,
            "weight_magnitude": abs(w).tolist(),
            "weight_phase_rad": np.angle(w).tolist(),
            "trial_score_means": {g: [] for g in "AB"},
            "mean_counts": {g: [] for g in "AB"},
        }
        for (name, shift, defocus, control), w in zip(cases, weights)
    ]
    q = 201 * np.pi / 200
    for li, label in enumerate("AB"):
        for trial in range(trials):
            phase_rng = np.random.default_rng(
                np.random.SeedSequence([2026102301, li, trial])
            )
            noise = phase_rng.normal(0, np.sqrt(config.phase_variance), (snapshots, 63))
            phases = q * coords[label] + noise
            quantized = (
                np.rint(phases * config.phase_levels / (2 * np.pi))
                * 2
                * np.pi
                / config.phase_levels
            )
            fields = np.exp(1j * quantized)
            intensities = abs(fields @ weights.T) ** 2
            if label == "B":
                control_phase = q * coords["A"] + noise
                control_phase = (
                    np.rint(control_phase * 256 / (2 * np.pi)) * 2 * np.pi / 256
                )
                intensities[:, -1] = abs(np.exp(1j * control_phase) @ weights[-1]) ** 2
            for ci, row in enumerate(results):
                rng = np.random.default_rng(
                    np.random.SeedSequence([2026102302, li, trial, ci])
                )
                counts = detector_counts(
                    intensities[:, ci] + config.background_per_gate,
                    rng,
                    config.dead_time_s / config.gate_s,
                )
                row["trial_score_means"][label].append(float(score(counts).mean()))
                row["mean_counts"][label].append(float(counts.mean()))
        print(
            "Completed",
            label,
            trials,
            "independent simulated trials per scenario",
            flush=True,
        )
    for row in results:
        row["classification"] = {}
        for label in "AB":
            values = np.array(row["trial_score_means"][label])
            errors = int(
                np.count_nonzero(
                    values >= THRESHOLD if label == "A" else values < THRESHOLD
                )
            )
            row["classification"][label] = {
                "errors": errors,
                "trials": trials,
                "empirical_error": errors / trials,
                "binomial_95_interval": binomial_interval(errors, trials),
            }
    report = {
        "status": "SYNTHETIC_BENCH_DEMO",
        "configuration": asdict(config),
        "engine": {
            "poppy": poppy.__version__,
            "numpy": np.__version__,
            "python": platform.python_version(),
        },
        "snapshots_per_trial": snapshots,
        "trials_per_structure": trials,
        "threshold": THRESHOLD,
        "score": "N*(N-1)/3969-(17/10)*N/63",
        "checks": checks,
        "scenarios": results,
        "attenuation_amplitudes": attenuation.tolist(),
        "model_sha256": MODEL_SHA,
        "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": "Monochromatic scalar Fraunhofer phase-mask emulator with finite square cells, Gaussian illumination and single-mode collection. Ideal per-cell amplitude calibration is assumed. Initially-live nonparalyzable Poisson detector; no afterpulsing, phase transfer error, relay aberrations, polarization, temporal dependence or measured input data. Fixed classifier; no threshold refitting. Scenarios share phase draws and must not be pooled. Numerical and Monte Carlo checks are not Arb certificates or physical validation.",
    }
    (output / "results.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8"
    )
    from render import render

    render(report, output, config, coords, attenuation)
    return report


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--trials", type=int, default=100)
    p.add_argument("--snapshots", type=int, default=5000)
    args = p.parse_args()
    run(args.output.resolve(), args.trials, args.snapshots)
