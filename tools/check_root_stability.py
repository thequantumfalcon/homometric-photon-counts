"""Exact perturbation budget preserving four simple roots; see docs/root-stability.md."""

from __future__ import annotations

import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from math import comb, factorial
from pathlib import Path

from project import EVIDENCE, require, verify


INPUTS = {
    "homometric-photon-counts/science_frontier/global_separation/blind_interval_certificate.json": "60f7ab263be537be208db15ebbad1eac37fd8d4a1f59fae7ceb828acd7b30548",
    "homometric-photon-counts/science_advance/global/additional_blind_gains_certificate.json": "a6c86b9f8116d47a270a87c125168fe89f7d3120f97a9de31d6b114917005bf6",
    "continuation-2026-10-20/gain/third_root_certificate.json": "9307fd02b3c17fe7be45c0c0a2a8d4011bcaf562ef0b4245b8e9f52470eda5de",
    "continuation-2026-10-20/gain/order96_extension_certificate.json": "526ca5f17281fcf433b74fbc8413f7692ed58674912de4f3eadca9f0f42f844b",
    "scientist-review-2026-10-20/global/compact_gain_certificate.json": "ed4eb69fa068eff3adce534998d4f20ce8d854c63a0ca0d360e62752c6c9f706",
}


def load_inputs() -> list[dict]:
    result = []
    for name, expected in INPUTS.items():
        data = (EVIDENCE / name).read_bytes()
        require(sha256(data).hexdigest() == expected, "Reference certificate changed: " + name)
        result.append(json.loads(data))
    return result


def cover_margin(leaves: list[dict], left: Q, right: Q, sign: int) -> Q:
    """Validate a contiguous closed cover and return its uniform strict sign margin."""
    require(sign in (-1, 1) and bool(leaves) and left < right, "Invalid cover")
    previous, margins = left, []
    for leaf in leaves:
        a, b = Q(leaf["left"]), Q(leaf["right"])
        require(a == previous and a < b <= right, "Broken interval cover")
        if "bernstein_upper" in leaf:
            require(sign == -1, "Bernstein upper bound cannot prove positivity")
            margin = -Q(leaf["bernstein_upper"])
        else:
            lo, hi = Q(leaf["bound"]["lower"]), Q(leaf["bound"]["upper"])
            require(lo <= hi, "Reversed enclosure")
            margin = lo if sign == 1 else -hi
        require(margin > 0, "Non-strict or wrong sign")
        margins.append(margin)
        previous = b
    require(previous == right, "Incomplete interval cover")
    return min(margins)


def envelope_integral(power: int, sites: int) -> Q:
    """Integral r^power min(1, 7^sites r^(-sites/2)) dr on [0,infinity)."""
    require(power >= 0 and sites > 2 * power + 2, "Nonintegrable envelope")
    return 7 ** (2 * power + 2) * (Q(1, power + 1) + Q(2, sites - 2 * power - 2))


def perturbation_constants() -> dict[str, tuple[Q, Q]]:
    # Recheck the inherited uniform characteristic and phase-density bounds.
    q = Q(3, 5)
    x = q * q
    w = (1 + 2 * (q + x * x / (1 - x))) / 6
    v = 2 * (q + x * x * (2 - x) / (1 - x) ** 2)
    require((64 * w + 3 * v) / 5 < 7, "Characteristic decay bound failed")
    require(
        2 * (1 + (x * (1 + x) / (1 - x) ** 3 - x) / q) < 8, "Single-site parameter derivative bound failed"
    )

    # Uniform q_b derivatives: b<=1/8 and exp(-z)(b+z)^m <= (8/7)m!.
    def q_bound(order: int, background_derivative: bool) -> Q:
        degree = 3 if background_derivative else 4
        return Q(8, 7) * factorial(4) * sum(comb(order, j) for j in range(degree + 1))

    m = Q(3969)
    # Integral Taylor weights are 1/24 and 1/120, including the 1/3! factor.
    h = (1008 * m**4 * q_bound(4, False) / 24, 2 * m**4 * q_bound(4, True) / 24)
    dh = (1008 * m**5 * q_bound(5, False) / 120, 2 * m**5 * q_bound(5, True) / 120)
    # Sum (b/2)^j/j! <= exp(b/2) <= 16/15 for b<=1/8.
    w0, wy, wb, wyb = (Q(n, 15) for n in (256, 512, 128, 256))
    g = (504 * w0 * envelope_integral(1, 62), wb * envelope_integral(1, 63))
    dg = (126 * wy * envelope_integral(3, 62), wyb * envelope_integral(3, 63) / 4)
    return {"H": h, "H_eta": dh, "G": g, "G_y": dg}


def certificate(t_radius: Q = Q(1, 10**23), b_radius: Q = Q(1, 10**20)) -> dict:
    require(0 < t_radius <= Q(1, 10) and 0 < b_radius <= Q(1, 8), "Unsupported parameter rectangle")
    first, second, third, fourth, compact = load_inputs()
    constants = perturbation_constants()
    errors = {name: lt * t_radius + lb * b_radius for name, (lt, lb) in constants.items()}
    records = []

    def record(name: str, function: str, interval: list[str], sign: int, margin: Q) -> None:
        error = errors[function]
        require(margin > 0 and 2 * error <= margin, "Perturbation exceeds half the margin: " + name)
        records.append(
            {
                "name": name,
                "function": function,
                "interval": interval,
                "sign": sign,
                "reference_margin": str(margin),
                "perturbation_bound": str(error),
                "remaining_margin": str(margin - error),
            }
        )

    def cover(name: str, function: str, leaves: list[dict], a: str, b: str, sign: int) -> None:
        record(name, function, [a, b], sign, cover_margin(leaves, Q(a), Q(b), sign))

    t = Q(1, 2)
    d4 = Q(455015761, 20000) * t**8 * (1 - t * t) ** 5 * (t**6 + 3 * t**4 + 6 * t * t + 6)
    require(Q(first["F_at_zero"]) == d4, "Reference fourth moment mismatch")
    record("finite-left-endpoint", "H", ["0", "0"], 1, d4)
    cover("first-root", "H_eta", first["F_derivative_strictly_negative_certificate"], "0", "1/512", -1)
    cover("after-first-root", "H", first["F_strictly_negative_certificate"], "1/512", "1/128", -1)
    cover(
        "before-second-root", "H", second["F_negative_cover_1_over_128_to_1_over_100"], "1/128", "1/100", -1
    )
    cover(
        "second-root", "H_eta", second["F_prime_positive_cover_1_over_100_to_1_over_90"], "1/100", "1/90", 1
    )
    cover("after-second-root", "H", second["F_positive_cover_1_over_90_to_1_over_32"], "1/90", "1/32", 1)
    for key, function, a, b, sign in [
        ("positive", "H", "1/32", "1/23", 1),
        ("decreasing", "H_eta", "1/23", "1/22", -1),
        ("negative", "H", "1/22", "1/12", -1),
    ]:
        cover("third-" + key, function, third["covers"][key]["leaves"], a, b, sign)
    # Flatten all subcovers so gaps between the archived top-level records also fail.
    leaves = [leaf for group in fourth["negative_covers"] for leaf in group["leaves"]]
    cover("finite-negative-tail", "H", leaves, "1/12", "1/6", -1)
    leaves = [
        {
            "left": row["a"],
            "right": row["b"],
            "bound": dict(zip(("lower", "upper"), row["rational_bounds"], strict=True)),
        }
        for row in compact["derivative_cover"]
    ]
    cover("entire-inverse-gain-cover", "G_y", leaves, "0", "6", -1)
    for y, sign in [("0", 1), ("6", -1)]:
        values = [row for row in compact["values"] if row["inverse_gain"] == y]
        require(len(values) == 1 and values[0]["sign"] == sign, "Missing inverse-gain endpoint")
        lo, hi = map(Q, values[0]["rational_bounds"])
        require(lo <= hi, "Reversed endpoint enclosure")
        record("inverse-endpoint-" + y, "G", [y, y], sign, lo if sign == 1 else -hi)
    return {
        "status": "PASS_EXACT_PERTURBATION_BUDGET",
        "model": "Fixed 63-site pair; iid Gaussian site phases; N|I is Poisson(b+eta I)",
        "rectangle": {
            "center_t": "1/2",
            "absolute_t_radius": str(t_radius),
            "background_lower": "0",
            "background_upper": str(b_radius),
        },
        "simple_root_gain_intervals": [
            ["0", "1/512"],
            ["1/100", "1/90"],
            ["1/23", "1/22"],
            ["1/6", "infinity"],
        ],
        "parameter_derivative_bounds": {
            name: {"t": str(lt), "b": str(lb)} for name, (lt, lb) in constants.items()
        },
        "checks": records,
        "input_sha256": INPUTS,
        "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "proof_sha256": sha256(
            (Path(__file__).resolve().parents[1] / "docs/root-stability.md").read_bytes()
        ).hexdigest(),
        "scope": "Exact rational budget supporting the analytic argument in docs/root-stability.md, "
        "conditional on the retained reference enclosures and the proved moment identities. "
        "Not a Lean theorem, optimized radius, measured tolerance, or all-parameter root count.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    require(
        not output.exists() and not output.is_relative_to(EVIDENCE),
        "Output must be fresh and outside evidence",
    )
    verify()
    result = certificate()
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("x", encoding="utf-8") as stream:
        json.dump(result, stream, indent=2)
        stream.write("\n")
    print("PASS: exact four-root perturbation budget; see", output)


if __name__ == "__main__":
    main()
