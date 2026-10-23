"""One-layout feasibility screen. No hardware control or Finesse execution."""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import sys
from fractions import Fraction
from hashlib import sha256
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import scipy
from matplotlib.patches import FancyBboxPatch
from scipy.special import ndtr

HERE = Path(__file__).resolve().parent
PROTO = HERE.parent
ROOT = PROTO.parent
BASE_SHA = "86e8ab0f8ba754ba7751e2e3cfdcb22a154212dbde49c2e96345d504f38dfa9d"


def base_module():
    path = PROTO / "simulate.py"
    if sha256(path.read_bytes()).hexdigest() != BASE_SHA:
        raise ValueError("The previously checked prototype changed")
    spec = importlib.util.spec_from_file_location("photon_base", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def rational_sqrt_upper(value: Fraction, scale: int = 10**15) -> Fraction:
    if value < 0:
        raise ValueError("Negative square root")
    n = math.isqrt(value.numerator * scale**2 // value.denominator)
    if Fraction(n, scale) ** 2 < value:
        n += 1
    result = Fraction(n, scale)
    assert result**2 >= value
    return result


def budget_bound(snapshots: int, loss: Fraction) -> dict:
    """TV(P^m,Q^m) <= sqrt(2*m*loss); Bayes error >= (1-TV)/2."""
    if snapshots < 0 or not 0 <= loss <= 1:
        raise ValueError("Invalid budget or affinity loss")
    tv = min(Fraction(1), rational_sqrt_upper(2 * snapshots * loss))
    error = (1 - tv) / 2
    return {
        "snapshots": snapshots,
        "tv_upper_exact": str(tv),
        "equal_prior_error_lower_exact": str(error),
        "equal_prior_error_lower_percent": 100 * float(error),
    }


def projected_power(
    phases: np.ndarray, weights: np.ndarray
) -> tuple[np.ndarray, np.ndarray]:
    """Ideal 8x8 unitary Fourier mixer: 63 illuminated modes, one blocked."""
    fields = np.zeros((len(phases), 64), dtype=complex)
    fields[:, :63] = weights * np.exp(1j * phases) / 8
    outputs = np.fft.fft2(fields.reshape(-1, 8, 8), norm="ortho")
    dc = np.abs(outputs[:, 0, 0]) ** 2
    total = np.sum(np.abs(outputs) ** 2, axis=(1, 2))
    return dc, total


def phase_mean(phases: np.ndarray, variance: float, levels: int | None) -> np.ndarray:
    if levels is None:
        return np.exp(-variance / 2 + 1j * phases)
    if levels < 2 or variance <= 0:
        raise ValueError("Quantized study needs levels >=2 and positive variance")
    centers = 2 * np.pi * np.arange(levels) / levels
    edges = 2 * np.pi * (np.arange(levels + 1) - 0.5) / levels
    location = phases[:, None] % (2 * np.pi)
    probabilities = np.zeros((len(phases), levels))
    for winding in range(-4, 5):
        cdf = ndtr((edges + 2 * np.pi * winding - location) / np.sqrt(variance))
        probabilities += np.diff(cdf, axis=1)
    if np.max(np.abs(probabilities.sum(axis=1) - 1)) > 2e-14:
        raise ValueError("Wrapped-normal integration lost mass")
    return probabilities @ np.exp(1j * centers)


def mean_intensity(
    phases: np.ndarray, weights: np.ndarray, variance: float, levels: int | None = None
) -> float:
    means = phase_mean(phases, variance, levels)
    return float(
        np.sum(weights**2 * (1 - np.abs(means) ** 2))
        + abs(np.sum(weights * means)) ** 2
    )


def zero_sum_second_intensity(phases: np.ndarray, variance: float) -> float:
    z = np.exp(1j * phases)
    if abs(z.sum()) > 1e-10:
        raise ValueError("Formula requires a zero coherent field")
    n, x = len(z), math.exp(-variance)
    return float(
        2 * n * n * (1 - x) ** 2
        + abs((z * z).sum()) ** 2 * (x * x - x) ** 2
        - n * (1 - x) ** 4
    )


def additive_detector_channel(background: float, afterpulse: float) -> np.ndarray:
    """13-bin channel: Poisson background then one Bernoulli child per primary.

    Counts only increase, so the >=12 bin is absorbing. This is a simplified
    first-generation count model; it contains no delays, recursion or dead time.
    """
    if background < 0 or not 0 <= afterpulse <= 1:
        raise ValueError("Invalid detector parameters")
    matrix = np.zeros((13, 13))
    for incoming in range(12):
        for dark in range(12 - incoming):
            primary = incoming + dark
            probability = (
                math.exp(-background) * background**dark / math.factorial(dark)
            )
            for child in range(min(primary, 11 - primary) + 1):
                matrix[primary + child, incoming] += (
                    probability
                    * math.comb(primary, child)
                    * afterpulse**child
                    * (1 - afterpulse) ** (primary - child)
                )
        matrix[12, incoming] = 1 - matrix[:12, incoming].sum()
    matrix[12, 12] = 1
    if np.min(matrix) < -1e-14 or np.max(np.abs(matrix.sum(axis=0) - 1)) > 1e-14:
        raise ValueError("Invalid stochastic count channel")
    return matrix


def plot_summary(report: dict, output: Path) -> None:
    fig = plt.figure(figsize=(11, 7.2), layout="constrained")
    grid = fig.add_gridspec(2, 1, height_ratios=[1, 1.7])
    ax = fig.add_subplot(grid[0])
    ax.axis("off")
    labels = [
        "633 nm laser\npolarization\nbeam shaping",
        "63 phase regions\n8 x 8 grid; one blocked",
        "Fourier lens\nselected fibre mode",
        "attenuation + counter\n5 ms acquisition gate",
    ]
    for i, label in enumerate(labels):
        x = 0.01 + i * 0.25
        ax.add_patch(
            FancyBboxPatch(
                (x, 0.28),
                0.22,
                0.42,
                boxstyle="round,pad=0.01",
                facecolor="#eaf0fa",
                edgecolor="#305b8d",
            )
        )
        ax.text(x + 0.11, 0.49, label, ha="center", va="center", fontsize=10)
        if i < 3:
            ax.annotate(
                "",
                xy=(x + 0.245, 0.49),
                xytext=(x + 0.225, 0.49),
                arrowprops={"arrowstyle": "->"},
            )
    ax.set_title(
        "Proposed optical emulator — no apparatus has been tested", fontsize=14
    )
    ax.text(
        0.5,
        0.06,
        "One new independent phase pattern per gate; 10 Hz planning rate; 8 hours",
        ha="center",
        fontsize=11,
    )
    ax = fig.add_subplot(grid[1])
    values = [
        report["budget"]["snapshots"],
        report["reference"]["necessary_snapshots"],
        report["reference"]["sufficient_snapshots"],
    ]
    ax.barh(
        [
            "Eight-hour budget",
            "Necessary reference count",
            "Certified sufficient count",
        ],
        values,
        color=["#327da8", "#a34141", "#d48943"],
    )
    ax.set_xscale("log")
    ax.invert_yaxis()
    ax.set_xlim(1e4, 1e15)
    ax.set_xlabel("Independent snapshots (logarithmic scale)")
    for i, v in enumerate(values):
        if i == 0:
            ax.text(v * 1.2, i, f"{v:,}", va="center", fontsize=10)
        else:
            ax.text(
                v / 1.2,
                i,
                f"{v:,}",
                ha="right",
                va="center",
                fontsize=10,
                color="white",
            )
    ax.set_title(
        "Reference protocol: the acquisition budget fails even in the ideal model",
        fontsize=12,
    )
    ax.grid(axis="x", alpha=0.2)
    ax.set_axisbelow(True)
    fig.suptitle("Bounded feasibility screen", fontsize=18)
    fig.savefig(output / "feasibility.png", dpi=180)
    fig.savefig(output / "feasibility.pdf")
    plt.close(fig)


def run(output: Path) -> dict:
    base = base_module()
    model, cert, lower = base.read_inputs(ROOT / "public-repo")
    reference, _scores = base.reference_summary(cert, lower, 100000)
    s, gain, gate, dark_rate, dead_time, afterpulse = (
        2 * math.log(2),
        0.05,
        0.005,
        25.0,
        22e-9,
        0.005,
    )
    phases = {g: np.array(base.coordinate_phases(model, g)) for g in "AB"}
    columns = np.arange(63) % 8
    gradient = (columns - columns.mean()) / np.std(columns)
    weights = 1 + 0.01 * gradient
    weights /= np.sqrt(np.mean(weights**2))
    ripple = np.sin(np.arange(63) * 1.731)
    ripple -= ripple.mean()
    ripple /= np.sqrt(np.mean(ripple**2))
    cases = [
        ("ideal", np.ones(63), 0, None),
        ("field_amplitude_1pct_rms", weights, 0, None),
        ("static_phase_1mrad_rms", np.ones(63), 0.001, None),
        ("uniform_256_level_phase", np.ones(63), 0, 256),
        ("combined_optical_stress", weights, 0.001, 256),
    ]
    optical = []
    for name, w, phase_error, levels in cases:
        means = {
            g: mean_intensity(phases[g] + phase_error * ripple, w, s, levels)
            for g in "AB"
        }
        clean = {
            g: float(
                abs(np.sum(w * np.exp(1j * (phases[g] + phase_error * ripple)))) ** 2
            )
            for g in "AB"
        }
        optical.append(
            {
                "case": name,
                "mean_intensity": means,
                "mean_count_difference_A_minus_B": gain * (means["A"] - means["B"]),
                "clean_intensity_before_dynamic_quantization": clean,
                "field_weight_rms": float(np.sqrt(np.mean(w * w))),
            }
        )
    rng = np.random.default_rng(20261021)
    maximum_power_error, maximum_sum_error, maximum_common_phase_error = 0.0, 0.0, 0.0
    for g in "AB":
        sample = phases[g] + rng.normal(0, np.sqrt(s), (1024, 63))
        power, total = projected_power(sample, np.ones(63))
        direct = np.abs(np.exp(1j * sample).sum(axis=1) / 64) ** 2
        shifted, _ = projected_power(sample + 0.731, np.ones(63))
        maximum_sum_error = max(
            maximum_sum_error, float(np.max(np.abs(power - direct)))
        )
        maximum_power_error = max(
            maximum_power_error, float(np.max(np.abs(total - 63 / 64)))
        )
        maximum_common_phase_error = max(
            maximum_common_phase_error, float(np.max(np.abs(power - shifted)))
        )
    assert (
        max(maximum_power_error, maximum_sum_error, maximum_common_phase_error) < 2e-14
    )
    loss = Fraction(lower["affinity_bound"]["one_minus_affinity_upper"])
    budget = budget_bound(10 * 8 * 3600, loss)
    rates = [
        dict(independent_hz=r, **budget_bound(r * 8 * 3600, loss))
        for r in (10, 60, 1000, 1000000)
    ]
    p_a = np.array([r["A_midpoint"] for r in reference["bins"]])
    p_b = np.array([r["B_midpoint"] for r in reference["bins"]])
    # Subtract exact endpoint rationals before converting, preserving the tiny difference.
    delta = np.array(
        [
            float(sum(map(Fraction, r["gap_interval_exact"])) / 2)
            for r in reference["bins"]
        ]
    )
    detector = []
    for name, b, ap in [
        ("ideal", 0, 0),
        ("dark_counts", dark_rate * gate, 0),
        ("dark_and_first_generation_afterpulse", dark_rate * gate, afterpulse),
    ]:
        kernel = additive_detector_channel(b, ap)
        gap = kernel @ delta
        a, bprob = kernel @ p_a, kernel @ p_b
        detector.append(
            {
                "case": name,
                "background_per_gate": b,
                "afterpulse_probability": ap,
                "bin_probabilities_A": a.tolist(),
                "bin_probabilities_B": bprob.tolist(),
                "gap_A_minus_B": gap.tolist(),
                "midpoint_total_variation": float(np.abs(gap).sum() / 2),
                "probability_shift_A_tv": float(np.abs(a - p_a).sum() / 2),
                "probability_shift_B_tv": float(np.abs(bprob - p_b).sum() / 2),
            }
        )
    assert all(
        row["midpoint_total_variation"]
        <= detector[0]["midpoint_total_variation"] + 1e-20
        for row in detector
    )
    mean_i, second_i = (
        optical[0]["mean_intensity"]["A"],
        zero_sum_second_intensity(phases["A"], s),
    )
    b = dark_rate * gate
    mean_lambda = b + gain * mean_i
    second_lambda = b * b + 2 * b * gain * mean_i + gain * gain * second_i
    d = dead_time / gate
    # Any rejection implies a primary pair within d; expected unordered close
    # pairs for a unit homogeneous Poisson gate is lambda^2*(d-d^2/2).
    dead_bound = second_lambda * (d - d * d / 2)
    parameters = {
        "wavelength_nm": 633,
        "active_phase_regions": 63,
        "grid": [8, 8],
        "phase_update_hz_planning": 10,
        "gate_seconds": gate,
        "settling_and_guard_seconds": 0.095,
        "wall_hours_budget": 8,
        "variance": s,
        "gain": gain,
        "reference_background": 0,
        "illustrative_dark_rate_cps": dark_rate,
        "illustrative_dead_time_seconds": dead_time,
        "illustrative_afterpulse_probability": afterpulse,
        "illustrative_detection_efficiency": 0.5,
        "illustrative_optical_throughput": 0.5,
    }
    result = {
        "status": "NO_GO_REFERENCE_SEPARATION_WITHIN_BUDGET",
        "parameters": parameters,
        "budget": budget,
        "alternative_rate_bounds": rates,
        "reference": reference,
        "affinity_loss_upper_exact": str(loss),
        "optical_stresses": optical,
        "detector_stresses": detector,
        "dead_time_estimate": {
            "normalized_dead_time": d,
            "mean_primary_counts": mean_lambda,
            "second_primary_rate_moment": second_lambda,
            "probability_of_any_dead_time_loss_upper_float": dead_bound,
            "scope": "Analytic union bound evaluated in floating point; baseline optics plus Poisson dark counts, no afterpulsing. Not a measured loss or interval certificate.",
        },
        "power_normalization": {
            "dc_power_fraction": "I/4096",
            "total_power_fraction": "63/64",
            "effective_input_photons_per_gate": gain * 4096 / (0.5 * 0.5),
        },
        "checks": {
            "fourier_states": 2048,
            "max_direct_field_power_disagreement": maximum_sum_error,
            "max_total_power_disagreement": maximum_power_error,
            "max_global_phase_disagreement": maximum_common_phase_error,
        },
        "runtime": {
            "python": sys.version.split()[0],
            "numpy": np.__version__,
            "scipy": scipy.__version__,
            "matplotlib": matplotlib.__version__,
            "finesse_installed": False,
            "finesse_executed": False,
        },
        "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "base_source_sha256": BASE_SHA,
        "input_sha256": base.INPUTS,
        "scope": "Exact-rational consequence of retained ideal 13-bin affinity bounds, plus floating-point optical and detector stress calculations. No new Lean theorem, hardware test, full diffraction solver or Finesse run.",
        "limits": [
            "The error lower bound concerns equal priors, iid snapshots, known reference parameters and only the 13 specified bins. It is not a bound on unbinned counts, other gains/variances, intensity monitoring or different measurements.",
            "The same bound survives the modeled common additive dark/afterpulse channel by data processing. It is not automatically transferred to phase/amplitude errors or dead-time thinning.",
            "The 8x8 discrete unitary Fourier mixer assumes equal illumination and equal mode projection. It does not validate a real SLM, lens, fibre, continuous diffraction or material structure.",
            "Ten settled independent patterns per second is a planning assumption. A datasheet rise/fall time is not a guarantee of the required phase accuracy or independence.",
            "Optical stresses can introduce lower-order differences. Easy discrimination in an imperfect emulator need not demonstrate the intended fourth-order mechanism.",
            "Uniform 256-level phase quantization is an idealized transfer curve; calibrated device phase levels and pixel crosstalk are unknown.",
            "Afterpulsing uses one independent Bernoulli child per primary, without delay or cascades. Detector memory and drift require measurements.",
            "No hardware purchase, installation, account access, external messaging or instrument control was performed.",
        ],
    }
    if output.exists() or output.is_relative_to(ROOT / "public-repo"):
        raise ValueError(
            "Output must be fresh and outside the preserved public repository"
        )
    output.mkdir(parents=True)
    (output / "results.json").write_text(
        json.dumps(result, indent=2, allow_nan=False) + "\n", encoding="utf-8"
    )
    plot_summary(result, output)
    print(
        json.dumps(
            {
                "status": result["status"],
                "budget": budget,
                "optical_stresses": optical,
                "dead_time_estimate": result["dead_time_estimate"],
                "checks": result["checks"],
            },
            indent=2,
        )
    )
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    run(parser.parse_args().output.resolve())
