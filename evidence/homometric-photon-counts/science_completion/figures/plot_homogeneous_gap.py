#!/usr/bin/env python3
"""Render an analytic scientific figure for the homogeneous-noise result.

Run from any directory:
    python /absolute/path/to/plot_homogeneous_gap.py

Dependencies: Python 3.10+, NumPy, Matplotlib. No simulation is used.
The neighboring measurement_and_optimization_results.json supplies the exact
optimizer bracket and the verified asymptotic sample orders. All outputs are
written beside this script unless --output-dir is supplied.

The plotted floating-point curve illustrates an exact analytic identity; the
proof/certificate is in the source artifacts, not in rasterized pixels.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import FixedLocator, FuncFormatter, LogLocator, ScalarFormatter
import numpy as np


N = 63
C = Fraction(455015761, 20000)
SMALL_S_COEFFICIENT = Fraction(455015761, 1250)
LARGE_S_COEFFICIENT = Fraction(1365047283, 10000)
TV_FACTOR = Fraction(64, N**8)
STEM = "homogeneous_fourth_moment_and_sampling"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def H(x: Fraction) -> Fraction:
    """Strictly decreasing optimizer polynomial on 0 < x < 1."""
    return 12 - 12*x - 21*x**2 - 13*x**3 - 6*x**4


def fourth_moment_gap(s):
    """Exact formula evaluated in double precision, stably near s = 0."""
    s = np.asarray(s, dtype=float)
    x = np.exp(-s)
    one_minus_x = -np.expm1(-s)
    return float(C) * x**4 * one_minus_x**5 * (x**3 + 3*x**2 + 6*x + 6)


def make_figure(results: dict):
    opt = results["bounded_fourth_degree_witness_optimization"]
    x_lo, x_hi = (Fraction(opt["x_star"][k]) for k in ("lower", "upper"))
    if not (0 < x_lo < x_hi < 1 and H(x_lo) > 0 > H(x_hi)):
        raise ValueError("The optimizer bracket does not have the required exact signs.")
    x_star = float((x_lo + x_hi) / 2)
    s_star = -math.log(x_star)
    d4_star = float(fourth_moment_gap(s_star))
    tv_star = d4_star * float(TV_FACTOR)
    reported_peak = float(opt["maximum_fourth_moment_gap"]["decimal_lower"])
    if not math.isclose(d4_star, reported_peak, rel_tol=5e-14):
        raise ValueError("Plotted analytic peak disagrees with the supplied certificate.")

    sample = results["sharp_sampling_results"]
    expected_orders = {
        "Gaussian_readout": "Theta(s^-10)",
        "Poisson_positive_background": "Theta(s^-10)",
        "Poisson_zero_background": "Theta(s^-6)",
    }
    for key, order in expected_orders.items():
        if sample[key]["minimum_independent_sample_order"] != order:
            raise ValueError(f"Unexpected sample-order input for {key}.")

    ink, muted = "#152B3A", "#526674"
    teal, orange = "#007F87", "#C46827"
    grid = "#DCE4E9"
    plt.rcParams.update({
        "font.family": "DejaVu Sans",
        "font.size": 11,
        "axes.labelsize": 11,
        "axes.titlesize": 12,
        "axes.titleweight": "bold",
        "axes.edgecolor": "#80919D",
        "axes.labelcolor": ink,
        "text.color": ink,
        "xtick.color": muted,
        "ytick.color": muted,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.linewidth": 0.8,
        "mathtext.fontset": "dejavusans",
        "svg.fonttype": "none",
        "pdf.fonttype": 42,
        "savefig.facecolor": "white",
        "figure.facecolor": "white",
    })

    fig = plt.figure(figsize=(14.6, 7.5))
    gs = fig.add_gridspec(1, 2, left=0.075, right=0.967, bottom=0.305,
                          top=0.765, wspace=0.68, width_ratios=(1.12, 1))
    ax = fig.add_subplot(gs[0, 0])
    ax_power = fig.add_subplot(gs[0, 1])

    fig.text(0.075, 0.947, "Higher-order discrimination under identical Gaussian site noise",
             fontsize=19, weight="bold", ha="left", va="top")
    fig.text(0.075, 0.893,
             r"63-site homometric pair at the common amplitude null $q=\pi/3$; "
             r"$s$ is the raw Gaussian phase variance.",
             fontsize=11.3, color=muted, ha="left", va="top")
    fig.text(0.075, 0.851,
             r"The first three intensity moments coincide. The fourth moment separates the laws "
             r"for every finite $s>0$.",
             fontsize=11.3, color=muted, ha="left", va="top")

    # Panel (a): a direct evaluation of the exact identity, including the origin.
    s_grid = np.unique(np.r_[np.linspace(0, 4.0, 1601), s_star])
    gap = fourth_moment_gap(s_grid)
    ax.plot(s_grid, gap, color=teal, lw=2.8, zorder=3)
    ax.fill_between(s_grid, 0, gap, color=teal, alpha=0.07, linewidth=0)
    ax.plot([s_star, s_star], [0, d4_star], color=teal, lw=1,
             linestyle=(0, (3, 3)), alpha=0.65)
    ax.scatter([s_star], [d4_star], color=teal, s=48, edgecolor="white",
               linewidth=1.0, zorder=4)
    ax.set(xlim=(0, 4), ylim=(0, 520),
           xlabel=r"Raw phase variance $s$",
           ylabel=r"Fourth-moment gap $D_4(s)=\mathbb{E}I_A^4-\mathbb{E}I_B^4$")
    ax.set_title("(a) Exact positive gap and its unique maximum", loc="left", pad=16)
    ax.set_xticks([0, 1, 2, 3, 4])
    ax.set_yticks([0, 100, 200, 300, 400, 500])
    ax.grid(axis="y", color=grid, linewidth=0.7)
    ax.set_axisbelow(True)
    ax.annotate(r"$s_*\approx0.751134$" + "\n" + r"$D_4(s_*)\approx445.097$",
                xy=(s_star, d4_star), xytext=(1.56, 432), fontsize=10.7,
                linespacing=1.5, va="center",
                arrowprops={"arrowstyle": "-", "color": muted, "lw": 0.9,
                            "connectionstyle": "angle,angleA=0,angleB=85,rad=4"})
    ax.text(2.00, 245, r"$D_4(s)>0$" + "\n" + r"for all $0<s<\infty$",
             fontsize=11.4, color=teal, linespacing=1.55, ha="center")

    # The second axis is only a unit conversion of the same analytic curve.
    factor = float(TV_FACTOR)
    sec = ax.secondary_yaxis("right", functions=(lambda y: factor*y,
                                                lambda y: y/factor))
    sec.spines["right"].set_visible(True)
    sec.spines["top"].set_visible(False)
    sec.set_ylabel(r"TV lower bound $64D_4(s)/63^8$", fontsize=10.7, labelpad=11)
    sec.set_yticks(np.arange(0, 1.26, 0.25)*1e-10)
    sec_format = ScalarFormatter(useMathText=True)
    sec_format.set_scientific(True)
    sec_format.set_powerlimits((-10, -10))
    sec.yaxis.set_major_formatter(sec_format)
    sec.tick_params(labelsize=10)

    # Panel (b): normalized powers illustrate proved asymptotic orders only.
    # Constants are normalized separately; this is not a performance ratio
    # between detectors or a finite-s calculation of minimum sample counts.
    ratio = np.geomspace(0.1, 1.0, 301)
    ax_power.loglog(ratio, ratio**-10, color=ink, lw=2.8,
                    label="Gaussian or positive-background Poisson\n" + r"$\propto s^{-10}$")
    ax_power.loglog(ratio, ratio**-6, color=orange, lw=2.8,
                    linestyle=(0, (6, 2.5)),
                    label="Zero-background Poisson\n" + r"$\propto s^{-6}$")
    ax_power.scatter([1], [1], s=32, color=muted, zorder=4, clip_on=False)
    ax_power.set(xlim=(0.1, 1), ylim=(0.7, 2e10),
                 xlabel=r"Phase variance relative to a reference, $s/s_{\rm ref}$",
                 ylabel="Normalized asymptotic sample scale")
    ax_power.set_title("(b) Sharp small-noise sample orders", loc="left", pad=16)
    ax_power.xaxis.set_major_locator(FixedLocator([0.1, 0.2, 0.5, 1]))
    ax_power.xaxis.set_major_formatter(FuncFormatter(lambda x, pos: f"{x:g}"))
    ax_power.xaxis.set_minor_locator(FixedLocator([]))
    ax_power.yaxis.set_major_locator(LogLocator(base=10, subs=(1,), numticks=7))
    ax_power.grid(which="major", color=grid, linewidth=0.7)
    ax_power.set_axisbelow(True)
    ax_power.legend(loc="upper right", frameon=True, facecolor="white",
                    edgecolor="none", framealpha=0.96, fontsize=9.7,
                    handlelength=2.7, labelspacing=1.1, borderpad=0.6)
    ax_power.text(0.12, 3.8,
                   "Each power is normalized separately\n"
                   r"to 1 at $s=s_{\rm ref}$.",
                   fontsize=9.7, linespacing=1.6, color=muted)

    # Figure notes keep all scope restrictions visible in the exported image.
    fig.text(0.075, 0.206,
             r"$D_4(s)=\dfrac{455015761}{20000}\," 
             r"e^{-4s}(1-e^{-s})^5(e^{-3s}+3e^{-2s}+6e^{-s}+6)$",
             fontsize=11.4, va="top")
    fig.text(0.075, 0.131,
             r"Both endpoint limits are zero: $D_4(s)\sim\dfrac{455015761}{1250}s^5$ "
             r"as $s\downarrow0$; "
             r"$D_4(s)\sim\dfrac{1365047283}{10000}e^{-4s}$ as $s\to\infty$.",
             fontsize=10.7, va="top")
    fig.text(0.075, 0.067,
             "Panel (a): the right axis is a conservative lower bound, not the actual total variation. "
             "The maximum optimizes this moment witness.\n"
             "Panel (b): independent observations, fixed calibrated detector parameters, and fixed success above chance. "
             "Asymptotic powers, not finite sample forecasts.",
             fontsize=9.7, color=muted, linespacing=1.6, va="top")

    metadata = {
        "schema": "homogeneous-fourth-moment-scientific-figure-v1",
        "analytic_not_Monte_Carlo": True,
        "n": N,
        "s": "Raw iid Gaussian phase variance at q=pi/3.",
        "centered_MSD_conversion": "v=62*s/(7*pi^2)",
        "fourth_moment_gap":
            "(455015761/20000)*exp(-4*s)*(1-exp(-s))^5*"
            "(exp(-3*s)+3*exp(-2*s)+6*exp(-s)+6)",
        "strict_positivity": "D4(s)>0 for every finite s>0; each factor is positive.",
        "small_s_asymptotic_coefficient": str(SMALL_S_COEFFICIENT),
        "large_s_exp_minus_4s_coefficient": str(LARGE_S_COEFFICIENT),
        "s_star_approximate": s_star,
        "x_star_exact_bracket": {"lower": str(x_lo), "upper": str(x_hi)},
        "optimizer_exact_bracket_signs_rechecked": True,
        "D4_star_approximate": d4_star,
        "TV_bound_star_approximate": tv_star,
        "TV_bound_factor": str(TV_FACTOR),
        "TV_bound_scope": "Lower bound on latent intensity-law TV, not the TV itself.",
        "maximizer_scope": opt["scope"],
        "panel_A_s_range": [0, 4],
        "panel_A_evaluation_points": len(s_grid),
        "panel_B": {
            "horizontal_variable": "r=s/s_ref in [0.1,1]; s_ref is a conceptual small-noise reference.",
            "curves": ["r^-10", "r^-6"],
            "normalization": "Each power separately equals 1 at r=1; unknown prefactors are suppressed.",
            "meaning": "Illustration of the sharp asymptotic powers only, not exact ratios m(s)/m(s_ref).",
            "Gaussian": "sigma>0 fixed, independent additive N(0,sigma^2) readout noise; Theta(s^-10).",
            "positive_background_Poisson": "b>0, eta>0 fixed, N|I~Poisson(b+eta I); Theta(s^-10).",
            "zero_background_Poisson": "b=0, eta>0 fixed, full count retained; Theta(s^-6).",
            "conditions": sample["conditions"],
            "limitations": sample["not_claimed"],
        },
        "rendering": {"matplotlib": matplotlib.__version__, "numpy": np.__version__,
                      "figure_inches": [14.6, 7.5], "png_dpi": 300},
    }
    return fig, metadata


CAPTION = r"""Higher-order discrimination under identical Gaussian site noise

Panel (a) plots the exact difference D4(s)=E[I_A^4]-E[I_B^4] for the
63-site clean-homometric pair at q=pi/3. Every site of both structures has
the same iid centered Gaussian phase perturbation with raw variance s.
An optional common-centering operation leaves intensity unchanged. The
corresponding centered displacement mean-square deviation is
v=62*s/(7*pi^2). The clean amplitude is zero at this frequency, and the
first three raw intensity moments agree for every s. The fourth difference
is exactly

 D4(s)=(455015761/20000)*exp(-4s)*(1-exp(-s))^5
       *(exp(-3s)+3exp(-2s)+6exp(-s)+6).

All factors are positive for every finite s>0. At the endpoints,
D4(s)~(455015761/1250)s^5 as s decreases to zero and
D4(s)~(1365047283/10000)exp(-4s) as s tends to infinity.
The unique maximizer is s*=0.751133970502722876... (the displayed decimal
is approximate); its uniqueness follows from the strictly decreasing
polynomial H(x)=12-12x-21x^2-13x^3-6x^4 for x=exp(-s), with opposite
signs at 0 and 1. Its exact rational bracket is supplied by the accompanying
optimization certificate. The peak gap is about 445.096853241853.

The right axis is the rigorous lower bound 64D4(s)/63^8 on the total
variation distance between the latent intensity distributions. It uses
the bounded polynomial (1+T4(2I/63^2-1))/2, whose lower-degree terms cancel
between the structures. The peak lower bound is about 1.14791598152e-10.
This is a conservative certificate, not an estimate of the actual TV.
The plotted maximizer optimizes this fourth-moment witness; it does not
establish the optimal full-distribution or detector operating point.

Panel (b) illustrates the proved asymptotic powers of the minimum number
of independent observations needed for any fixed classification success
a in (1/2,1), under equal priors and the stated known, calibrated models.
The powers are Theta(s^-10) for additive Gaussian readout with fixed
sigma>0, and for Poisson counting with fixed b>0 and eta>0. They are
Theta(s^-6) for Poisson counting with b=0 and fixed eta>0 when count
magnitudes are retained. Every observation is an independent snapshot.
The curves r^-10 and r^-6, r=s/s_ref, are each normalized separately to
one at r=1. Their prefactors have been suppressed. These curves illustrate
asymptotic powers, not finite-noise sample counts, exact ratios of sample
counts, or a comparison of the absolute efficiency of the detectors.
The reference is conceptual and lies in the small-noise regime; no
universal finite regime of asymptotic accuracy is asserted. Joint limits
in detector parameters require a separate argument.

The figure uses direct analytic evaluation with no Monte Carlo simulation.
It is a visualization of the accompanying proofs, not an additional
independent proof. Input proofs and certificates are:
  ../homogeneous_control/homogeneous_control_proof.txt
  ../homogeneous_control/homogeneous_control_results.json
  ../measurement_and_optimization_results.json
  ../detector_proofs.tex
  ../sample_complexity_proofs.tex

Reproduction:
  python plot_homogeneous_gap.py
Requires Python 3.10+, numpy, and matplotlib. By default all output files
are written beside the script; --output-dir changes that destination.
"""


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path,
                        default=here.parent / "measurement_and_optimization_results.json")
    parser.add_argument("--output-dir", type=Path, default=here)
    args = parser.parse_args()
    results = json.loads(args.input.read_text())
    fig, metadata = make_figure(results)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    outputs = []
    for ext in ("png", "svg", "pdf"):
        destination = args.output_dir / f"{STEM}.{ext}"
        common = {"dpi": 300} if ext == "png" else {}
        fig.savefig(destination, **common)
        outputs.append(destination)
    plt.close(fig)
    caption = args.output_dir / f"{STEM}_caption.txt"
    caption.write_text(CAPTION)
    outputs.append(caption)
    metadata["input_sha256"] = sha256(args.input)
    metadata["script_sha256"] = sha256(Path(__file__))
    proof_path = here.parent / "sample_complexity_proofs.tex"
    if proof_path.is_file():
        metadata["sample_complexity_proof_sha256"] = sha256(proof_path)
    metadata["outputs"] = {path.name: {"bytes": path.stat().st_size,
                                        "sha256": sha256(path)} for path in outputs}
    metadata_path = args.output_dir / f"{STEM}_metadata.json"
    metadata_path.write_text(json.dumps(metadata, indent=2) + "\n")
    for path in outputs + [metadata_path]:
        print(path.resolve())
    print(f"s_star={metadata['s_star_approximate']:.16g}; "
          f"D4_star={metadata['D4_star_approximate']:.16g}; "
          f"TV_lower_bound_star={metadata['TV_bound_star_approximate']:.16g}")


if __name__ == "__main__":
    main()
