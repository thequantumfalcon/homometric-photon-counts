"""Independent held-out sampling check; no classifier fitting or phase access."""

from __future__ import annotations

import argparse
import json
import math
from hashlib import sha256
from pathlib import Path

import numpy as np
import search


def run(certificate_path, output, trials=200):
    if output.exists() or output.is_relative_to(search.ROOT / "public-repo"):
        raise ValueError("Use a fresh local output directory")
    raw = certificate_path.read_bytes()
    certificate = json.loads(raw)
    params = certificate["parameters"]
    _, _, coords = search.inputs()
    q = np.pi * float(search.Fraction(params["q_over_pi"]))
    s = float(search.Fraction(params["site_phase_variance"]))
    m = params["snapshots"]
    scenarios = [
        r for r in certificate["scenarios"] if not r["dead_time_bound_applied"]
    ]
    rows = []
    for label in "AB":
        # Held-out, distinct streams; the deterministic search used no random data.
        rng = np.random.default_rng(2026102201 + (label == "B"))
        totals = {
            r["name"]: {"sum": 0.0, "sum2": 0.0, "misclassified_trials": 0}
            for r in scenarios
        }
        for trial in range(trials):
            phase = q * coords[label] + rng.normal(0, math.sqrt(s), (m, 63))
            intensity = abs(np.exp(1j * phase).sum(axis=1)) ** 2
            quantized_phase = np.rint(phase * 256 / (2 * np.pi)) * 2 * np.pi / 256
            quantized_intensity = abs(np.exp(1j * quantized_phase).sum(axis=1)) ** 2
            for row in scenarios:
                b = float(search.Fraction(row["background"]))
                ap = float(search.Fraction(row["afterpulse_probability"]))
                value = (
                    quantized_intensity
                    if row.get("uniform_phase_levels") == 256
                    else intensity
                )
                count = rng.poisson(value + b)
                if ap:
                    count = count + rng.binomial(count, ap)
                # Only observed counts enter this fixed classifier.
                scores = count * (count - 1) / 3969 - 1.7 * count / 63
                chosen = (
                    "A"
                    if scores.mean() < float(search.Fraction(row["threshold_exact"]))
                    else "B"
                )
                acc = totals[row["name"]]
                acc["sum"] += float(scores.sum())
                acc["sum2"] += float(scores @ scores)
                acc["misclassified_trials"] += chosen != label
        for row in scenarios:
            acc = totals[row["name"]]
            n = m * trials
            mean = acc["sum"] / n
            variance = (acc["sum2"] - n * mean**2) / (n - 1)
            exact = row["results"][label]["mean"]
            predicted = float(
                (search.Fraction(exact["lower"]) + search.Fraction(exact["upper"])) / 2
            )
            z = (mean - predicted) / math.sqrt(variance / n)
            if abs(z) > 6:
                raise ValueError("Moment diagnostic exceeds six standard errors")
            rows.append(
                {
                    "structure": label,
                    "scenario": row["name"],
                    "independent_trials": trials,
                    "snapshots_per_trial": m,
                    "misclassified_trials": acc["misclassified_trials"],
                    "empirical_score_mean": mean,
                    "predicted_score_mean": predicted,
                    "mean_diagnostic_z": z,
                }
            )
        print("Completed held-out structure " + label, flush=True)
    result = {
        "status": "PASS_SIMULATION_DIAGNOSTICS",
        "results": rows,
        "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "certificate_sha256": sha256(raw).hexdigest(),
        "scope": "Synthetic held-out diagnostic of four simplified count laws, with independent A/B streams. Scenarios share phase samples within a structure. No physical observations; zero observed failures would not prove zero risk. Dead-time bound is not simulated here.",
    }
    output.mkdir(parents=True)
    (output / "simulation.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    run(args.certificate.resolve(), args.output.resolve())
