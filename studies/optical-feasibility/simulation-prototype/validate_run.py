"""Read-only diagnostics against certified probabilities; no A/B detection claim."""

import json
import math
import sys
from hashlib import sha256
from pathlib import Path

folder = Path(sys.argv[1]).resolve()
report = json.loads((folder / "report.json").read_bytes())
assert (
    report["source_sha256"]
    == sha256(Path(__file__).with_name("simulate.py").read_bytes()).hexdigest()
)
assert report["reference_matches_ideal_run"]
diagnostics = {}
for label, row in report["simulation"].items():
    n = row["samples"]
    assert sum(row["ideal_histogram"]) == sum(row["dead_time_histogram"]) == n
    assert row["ideal_histogram"][0] == row["dead_time_histogram"][0]
    scores = []
    for k, bin_ref in enumerate(report["certified_reference"]["bins"]):
        probability = bin_ref[label + "_midpoint"]
        se = math.sqrt(probability * (1 - probability) / n)
        z = (row["ideal_histogram"][k] / n - probability) / se
        scores.append(z)
    assert max(map(abs, scores)) < 6
    mean_z = {}
    for stat, expected in [
        ("intensity", "analytic_mean_intensity_float"),
        ("ideal_counts", "analytic_mean_ideal_counts_float"),
    ]:
        mean_z[stat] = (row["statistics"][stat]["mean"] - row[expected]) / row[
            "statistics"
        ][stat]["estimated_standard_error"]
        assert abs(mean_z[stat]) < 6
    lost = row["statistics"]["lost_counts"]
    diagnostics[label] = {
        "max_abs_bin_z": max(map(abs, scores)),
        "mean_z": mean_z,
        "paired_mean_lost_counts": lost,
        "fraction_of_ideal_counts_lost": lost["mean"]
        / row["statistics"]["ideal_counts"]["mean"],
    }
out = {
    "status": "PASS_DIAGNOSTICS_ONLY",
    "samples_per_geometry": n,
    "diagnostics": diagnostics,
    "scope": "Fixed-seed software consistency diagnostics with conservative six-standard-error thresholds; no calibrated hypothesis test, formal theorem or experimental validation.",
}
(folder / "validation.json").write_text(
    json.dumps(out, indent=2) + "\n", encoding="utf-8"
)
print(json.dumps(out, indent=2))
