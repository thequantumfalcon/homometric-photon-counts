"""Render the conditional risk bounds; does not recompute the certificate."""

import argparse
import json
import math
from fractions import Fraction
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


def run(certificate, output):
    if output.exists():
        raise ValueError("Use a fresh plot output directory")
    data = json.loads(certificate.read_text())
    labels = [
        "Ideal optics and counts",
        "Known dark counts",
        "Dark counts + toy afterpulsing",
        "Dark counts + dead time",
        "256 phase levels + dark counts",
        "256 levels + dark counts + dead time",
    ]
    upper_bounds = [
        max(Fraction(x["each_error_upper_exact"]) for x in row["results"].values())
        for row in data["scenarios"]
    ]
    values = [100 * float(value) for value in upper_bounds]
    fig, ax = plt.subplots(figsize=(10, 5.4), layout="constrained")
    ax.barh(labels, values, color=["#347ca5"] * 3 + ["#a76b33", "#347ca5", "#a76b33"])
    ax.invert_yaxis()
    ax.axvline(5, color="#a93838", linestyle="--", label="5% target")
    ax.set_xlim(0, 5.6)
    ax.set_xlabel("Upper bound on each classification error (%)")
    ax.set_title("Changed-frequency candidate: 5,000 independent snapshots", pad=15)
    for i, value in enumerate(values):
        outward_percent = math.ceil(upper_bounds[i] * 100000) / 1000
        ax.text(value + 0.08, i, f"{outward_percent:.3f}%", va="center")
    ax.legend(loc="lower right")
    ax.spines[["top", "right"]].set_visible(False)
    fig.suptitle(
        "Conditional mathematical feasibility — no apparatus tested", fontsize=14
    )
    fig.supxlabel(
        "10 Hz planning rate: 8 min 20 s acquisition; calibration and setup excluded",
        fontsize=10,
    )
    output.mkdir(parents=True)
    fig.savefig(output / "candidate.png", dpi=180)
    fig.savefig(output / "candidate.pdf")
    plt.close(fig)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    run(args.certificate, args.output)
