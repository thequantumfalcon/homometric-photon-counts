"""Bounded numerical feasibility prototype; Python 3.11+, standard library only."""

from __future__ import annotations

import argparse
import json
import math
import random
import sys
import time
from dataclasses import dataclass
from fractions import Fraction
from hashlib import sha256
from pathlib import Path

HERE = Path(__file__).resolve().parent
INPUTS = {
    "homometric-photon-counts/science_completion/harmonic_certificate/input_model.json": "4b9b37a013347b2bd8a273bd2e1be2c867986f2287e1012d6ea9488ed515b288",
    "continuation-2026-10-20/multibin/certificate.json": "1e0be4aecb7818a5b9c832f627ad7a955d7fbeee23f77989fab8cc20b6a3e29b",
    "followup-2026-10-20/lowerbounds/binned_lower_bound.json": "cca4c8ed55a0b7e61f9e8bd599c7c5188f4fc680b1f45c1276d6d1a498575fb0",
}


@dataclass
class Stats:
    n: int = 0
    mean: float = 0.0
    m2: float = 0.0

    def add(self, value: float) -> None:
        self.n += 1
        delta = value - self.mean
        self.mean += delta / self.n
        self.m2 += delta * (value - self.mean)

    def report(self) -> dict:
        se = (
            math.sqrt(max(0.0, self.m2) / (self.n * (self.n - 1)))
            if self.n > 1
            else None
        )
        return {"n": self.n, "mean": self.mean, "estimated_standard_error": se}


def read_inputs(repo: Path) -> tuple[dict, dict, dict]:
    values = []
    for name, expected in INPUTS.items():
        data = (repo / "evidence" / name).read_bytes()
        if sha256(data).hexdigest() != expected:
            raise ValueError("Input identity changed: " + name)
        values.append(json.loads(data))
    return tuple(values)


def coordinate_phases(model: dict, label: str) -> list[float]:
    offsets = {
        "none": 0.0,
        "theta": math.asin(1 / (5 * math.sqrt(3))),
        "phi": -math.asin(1 / (8 * math.sqrt(3))),
    }
    rows = model["graphs"][label]["coordinates"]
    if [r["ordinal"] for r in rows] != list(range(63)):
        raise ValueError("Unexpected coordinate inventory")
    # Periodic reduction avoids adding a small offset to a large phase.
    return [
        math.pi * (r["base_integer"] % 6) / 3
        + r["offset_sign"] * offsets[r["offset_kind"]]
        for r in rows
    ]


def intensity(phases: list[float]) -> float:
    re = math.fsum(math.cos(x) for x in phases)
    im = math.fsum(math.sin(x) for x in phases)
    return re * re + im * im


def poisson(rng: random.Random, rate: float) -> int:
    """Sum independent Poisson chunks <=20 to avoid exp(-large rate) underflow."""
    if not math.isfinite(rate) or not 0 <= rate <= 1000:
        raise ValueError("Prototype Poisson rate must be finite and in [0, 1000]")
    if rate == 0:
        return 0
    chunks = math.ceil(rate / 20)
    threshold = math.exp(-rate / chunks)
    total = 0
    for _ in range(chunks):
        product, k = 1.0, 0
        while product > threshold:
            product *= rng.random()
            k += 1
        total += k - 1
    return total


def accepted_count(arrivals: list[float], dead_time: float) -> int:
    """Initially live, nonparalyzable detector in one unit-length gate.

    Rejected arrivals do not extend the dead period. Each gate resets; this
    does not model detector memory across gates or afterpulsing.
    """
    if not math.isfinite(dead_time) or dead_time < 0:
        raise ValueError("Dead time must be finite and nonnegative")
    ready, accepted = 0.0, 0
    for arrival in sorted(arrivals):
        if not 0 <= arrival < 1:
            raise ValueError("Arrival outside gate")
        if arrival >= ready:
            accepted += 1
            ready = arrival + dead_time
    return accepted


def stream(seed: int, label: str, purpose: str) -> random.Random:
    return random.Random(
        int.from_bytes(sha256(f"{seed}:{label}:{purpose}".encode()).digest(), "big")
    )


def reference_summary(
    cert: dict, lower: dict, samples: int
) -> tuple[dict, list[float]]:
    row = next(
        r for r in cert["candidates"] if r["eta"] == "1/20" and r["cutoff"] == 12
    )
    scores = [Fraction(x) for x in row["scores"]]
    bounds = {
        label: [
            (Fraction(x["lower"]), Fraction(x["upper"]))
            for x in row["probability_bounds"][label]
        ]
        for label in "AB"
    }
    bins = []
    for k, (a, b) in enumerate(zip(bounds["A"], bounds["B"], strict=True)):
        pa, pb = float(sum(a) / 2), float(sum(b) / 2)
        gap = (a[0] - b[1], a[1] - b[0])
        bins.append(
            {
                "bin": str(k) if k < 12 else ">=12",
                "A_midpoint": pa,
                "B_midpoint": pb,
                "gap_interval_exact": list(map(str, gap)),
                "gap_midpoint": float(sum(gap) / 2),
                "ideal_two_run_mc_standard_error": math.sqrt(
                    (pa * (1 - pa) + pb * (1 - pb)) / samples
                ),
            }
        )
    means = {}
    for label in "AB":
        terms = [
            (min(s * lo, s * hi), max(s * lo, s * hi))
            for s, (lo, hi) in zip(scores, bounds[label], strict=True)
        ]
        means[label] = list(
            map(str, (sum(x[0] for x in terms), sum(x[1] for x in terms)))
        )
    duration = [
        {
            "independent_snapshots_per_second_assumed": rate,
            "necessary_years": lower["necessary_m_at_least"] / rate / (365.25 * 86400),
            "sufficient_years": row["m_sufficient"] / rate / (365.25 * 86400),
        }
        for rate in (1000, 1000000)
    ]
    return {
        "scope": "s=2 log(2), gain=1/20, background=0; iid 13-bin observations, known calibration, each error <5%.",
        "necessary_snapshots": lower["necessary_m_at_least"],
        "sufficient_snapshots": row["m_sufficient"],
        "fixed_score_mean_intervals_exact": means,
        "bins": bins,
        "hypothetical_duration": duration,
        "duration_warning": "Rates are illustrative assumptions, not measured hardware throughput. Counts are independent snapshots, not individual photons.",
    }, list(map(float, scores))


def simulate(
    label: str,
    phases: list[float],
    samples: int,
    seed: int,
    variance: float,
    gain: float,
    background: float,
    dead_time: float,
    scores: list[float],
) -> dict:
    phase_rng, count_rng, time_rng = [
        stream(seed, label, purpose) for purpose in ("phase", "count", "arrival")
    ]
    sigma = math.sqrt(variance)
    stats = {
        name: Stats()
        for name in (
            "intensity",
            "intensity_fourth_power",
            "ideal_counts",
            "dead_time_counts",
            "ideal_factorial4",
            "dead_time_factorial4",
            "ideal_score",
            "dead_time_score",
            "paired_score_shift",
            "lost_counts",
        )
    }
    ideal_hist, dead_hist = [0] * 13, [0] * 13
    for _ in range(samples):
        value = intensity([p + phase_rng.gauss(0, sigma) for p in phases])
        count = poisson(count_rng, background + gain * value)
        # Conditional on N and a constant rate, Poisson arrival times are iid uniform.
        detected = accepted_count([time_rng.random() for _ in range(count)], dead_time)
        a, d = min(count, 12), min(detected, 12)
        ideal_hist[a] += 1
        dead_hist[d] += 1
        values = (
            value,
            value**4,
            count,
            detected,
            math.prod(count - k for k in range(4)),
            math.prod(detected - k for k in range(4)),
            scores[a],
            scores[d],
            scores[d] - scores[a],
            count - detected,
        )
        for item, observed in zip(stats.values(), values, strict=True):
            item.add(observed)
    expected_i = len(phases) + math.exp(-variance) * (intensity(phases) - len(phases))
    return {
        "samples": samples,
        "clean_intensity_float": intensity(phases),
        "analytic_mean_intensity_float": expected_i,
        "analytic_mean_ideal_counts_float": background + gain * expected_i,
        "statistics": {k: v.report() for k, v in stats.items()},
        "ideal_histogram": ideal_hist,
        "dead_time_histogram": dead_hist,
    }


def write_report(report: dict, output: Path) -> None:
    ref, results = report["certified_reference"], report["simulation"]
    lines = [
        "PHOTON EXPERIMENT: NUMERICAL FEASIBILITY PROTOTYPE",
        "",
        "Synthetic observations only. No detector measurements or physical validation.",
        "The simulation follows the specified snapshot model using floating-point arithmetic.",
        "Dead time is an illustrative extension; gates start live and reset independently.",
        "",
        f"Parameters: {report['parameters']}",
        f"Reference certificate applies to the ideal run: {report['reference_matches_ideal_run']}",
        "",
    ]
    for label, item in results.items():
        lines.append(f"{label}:")
        for name in (
            "intensity",
            "ideal_counts",
            "dead_time_counts",
            "ideal_factorial4",
            "paired_score_shift",
        ):
            s = item["statistics"][name]
            lines.append(
                f"  {name}: {s['mean']:.9g}; estimated MC SE {s['estimated_standard_error']:.4g}"
            )
        lines.append(
            f"  analytic mean ideal counts: {item['analytic_mean_ideal_counts_float']:.9g}"
        )
    lines += [
        "",
        "Reference probabilities versus finite-sample resolution:",
        "bin       certified midpoint gap A-B    observed MC gap       expected MC SE",
    ]
    for k, row in enumerate(ref["bins"]):
        observed = (
            results["A"]["ideal_histogram"][k] / results["A"]["samples"]
            - results["B"]["ideal_histogram"][k] / results["B"]["samples"]
        )
        lines.append(
            f"{row['bin']:>4}      {row['gap_midpoint']: .8e}          {observed: .8e}       {row['ideal_two_run_mc_standard_error']:.8e}"
        )
    lines += [
        "",
        f"Necessary reference snapshots: {ref['necessary_snapshots']:,}",
        f"Certified sufficient reference snapshots: {ref['sufficient_snapshots']:,}",
    ]
    for row in ref["hypothetical_duration"]:
        lines.append(
            f"At an ASSUMED {row['independent_snapshots_per_second_assumed']:,} independent snapshots/s: "
            f"necessary {row['necessary_years']:.3f} years; sufficient {row['sufficient_years']:.3f} years."
        )
    lines += ["", ref["duration_warning"], "", "Limits and interpretation:"]
    lines += ["- " + s for s in report["limits"]]
    (output / "report.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
    (output / "report.json").write_text(
        json.dumps(report, indent=2, allow_nan=False) + "\n", encoding="utf-8"
    )


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, default=HERE.parent / "public-repo")
    p.add_argument("--output", type=Path, required=True)
    p.add_argument(
        "--samples", type=int, default=100000, help="Independent snapshots per geometry"
    )
    p.add_argument("--seed", type=int, default=20261021)
    p.add_argument("--variance", type=float, default=2 * math.log(2))
    p.add_argument("--gain", type=float, default=0.05)
    p.add_argument("--background", type=float, default=0.0)
    p.add_argument(
        "--dead-time-fraction",
        type=float,
        default=0.01,
        help="Illustrative dead time / gate duration",
    )
    args = p.parse_args()
    for key in ("variance", "gain", "background", "dead_time_fraction"):
        value = getattr(args, key)
        if not math.isfinite(value) or value < 0:
            p.error(key + " must be finite and nonnegative")
    if not 2 <= args.samples <= 1000000 or args.background + 3969 * args.gain > 1000:
        p.error(
            "Use 2..1,000,000 samples and background+3969*gain <=1000 for this bounded prototype"
        )
    output, repo = args.output.resolve(), args.repo.resolve()
    if output.exists() or output.is_relative_to(repo):
        p.error("Output must be fresh and outside the preserved public repository")
    model, cert, lower = read_inputs(repo)
    reference, scores = reference_summary(cert, lower, args.samples)
    matches = (
        args.variance == 2 * math.log(2) and args.gain == 0.05 and args.background == 0
    )
    started = time.perf_counter()
    results = {}
    for label in "AB":
        results[label] = simulate(
            label,
            coordinate_phases(model, label),
            args.samples,
            args.seed,
            args.variance,
            args.gain,
            args.background,
            args.dead_time_fraction,
            scores,
        )
        print(f"Completed {label}: {args.samples:,} independent snapshots", flush=True)
    t = math.exp(-args.variance / 2)
    delta4 = (
        (455015761 / 20000)
        * t**8
        * (1 - t * t) ** 5
        * (t**6 + 3 * t**4 + 6 * t * t + 6)
    )
    report = {
        "status": "EXPLORATORY_SIMULATION_ONLY",
        "python": sys.version.split()[0],
        "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "input_sha256": INPUTS,
        "parameters": {
            k: getattr(args, k)
            for k in (
                "samples",
                "seed",
                "variance",
                "gain",
                "background",
                "dead_time_fraction",
            )
        },
        "reference_matches_ideal_run": matches,
        "certified_reference": reference,
        "analytic_ideal_fourth_intensity_gap_float": delta4,
        "analytic_ideal_fourth_factorial_count_gap_float": args.gain**4 * delta4,
        "simulation": results,
        "elapsed_seconds": time.perf_counter() - started,
        "limits": [
            "A and B use separate random streams. Only ideal/dead-time observations within each structure are paired.",
            "Small Monte Carlo differences do not establish the tiny A/B separation. Use the existing certified probability intervals for that claim.",
            "Reported standard errors are numerical diagnostics, not rigorous confidence certificates or measured detector uncertainties.",
            "The fixed reference score observes only the count bin; latent phases and intensities are simulator diagnostics, not extra classifier inputs.",
            "The detector extension assumes a constant rate during each gate, uniform conditional arrival times, nonparalyzable dead time and independent resets. No cross-gate memory, afterpulsing or optical propagation is simulated.",
            "No physical gate length, detector efficiency or attainable independent sample rate has been measured. Gain and background are effective per-gate parameters.",
            "The graph covariance in the archived file is not used; phase fluctuations are independent Gaussian draws.",
            "Changing gain, variance, background or detector response invalidates applying the retained reference risk/sample guarantees to that changed experiment.",
            "No parameter search, experimental validation, novelty result or universal feasibility conclusion is obtained.",
        ],
    }
    output.mkdir(parents=True, exist_ok=False)
    write_report(report, output)
    print("Report:", output / "report.txt")


if __name__ == "__main__":
    main()
