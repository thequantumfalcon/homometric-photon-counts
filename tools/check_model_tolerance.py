"""Check a conservative model-error budget for the fixed 13-bin score test."""

from __future__ import annotations

import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from math import factorial
from pathlib import Path

from project import EVIDENCE, require, verify


def exp_upper(x: Q, order: int = 20) -> Q:
    """Taylor polynomial plus a geometric bound for the absolute tail."""
    require(abs(x) <= 1 and order >= 1, "Unsupported exponential bound")
    total = sum((x**k / factorial(k) for k in range(order + 1)), Q(0))
    tail = abs(x) ** (order + 1) / factorial(order + 1)
    return total + tail / (1 - abs(x) / (order + 2))


def simplex_max(bounds: list[tuple[Q, Q]], values: list[Q]) -> Q:
    """Maximize a linear expectation on a box intersected with the probability simplex."""
    require(len(bounds) == len(values) and bool(bounds), "Mismatched probability bins")
    require(all(0 <= lo <= hi <= 1 for lo, hi in bounds), "Invalid probability interval")
    require(sum(lo for lo, _ in bounds) <= 1 <= sum(hi for _, hi in bounds), "Empty simplex")
    remaining = 1 - sum(lo for lo, _ in bounds)
    result = sum((lo * value for (lo, _), value in zip(bounds, values)), Q(0))
    for i in sorted(range(len(values)), key=lambda i: values[i], reverse=True):
        add = min(remaining, bounds[i][1] - bounds[i][0])
        result += add * values[i]
        remaining -= add
    require(remaining == 0, "Unallocated probability mass")
    return result


def certificate() -> dict:
    source = EVIDENCE / "continuation-2026-10-20/multibin/certificate.json"
    source_hash = sha256(source.read_bytes()).hexdigest()
    require(
        source_hash == "1e0be4aecb7818a5b9c832f627ad7a955d7fbeee23f77989fab8cc20b6a3e29b",
        "Reference certificate changed",
    )
    saved = json.loads(source.read_bytes())
    require(saved["status"] == "PASS", "Failed reference certificate")
    selected = saved["selected"]
    require(selected["eta"] == "1/20" and selected["cutoff"] == 12, "Different experiment")
    weights = list(map(Q, selected["scores"]))
    require(len(weights) == 13 and max(map(abs, weights)) <= 1, "Unsupported score")
    span = max(weights) - min(weights)
    require(span > 0, "Constant score")
    contraction = Q(selected["contraction_lower"])
    require(0 < contraction < 1, "Invalid contraction")
    expectations = {}
    for geometry, sign in [("A", -1), ("B", 1)]:
        bounds = [(Q(row["lower"]), Q(row["upper"])) for row in selected["probability_bounds"][geometry]]
        value = simplex_max(bounds, [exp_upper(sign * w) for w in weights])
        require(value <= 1 - contraction, "Reference score contraction failed")
        expectations[geometry] = str(value)
    # On [-1,1], the exponential is Lipschitz with constant e < 3.
    tolerance = Q(3, 10**9)
    remaining_contraction = contraction - 3 * span * tolerance
    require(remaining_contraction >= contraction / 2, "Model-error allowance is too large")
    original_samples = selected["m_sufficient"]
    samples = 2 * original_samples
    require(original_samples * contraction >= 3, "Reference sample count failed")
    require(samples * remaining_contraction >= 3, "Robust sample count failed")
    # The separate coupling argument in the proof converts parameter errors to TV.
    sites, gain = 63, Q(selected["eta"])
    coefficients = {
        "background": Q(1),
        "gain": Q(sites**2),
        "max_site_phasor_chord_error": 2 * sites**2 * gain,
        "phase_standard_deviation": 2 * sites**2 * gain,
    }
    radii = {name: tolerance / coefficient for name, coefficient in coefficients.items()}
    require(all(coefficients[name] * radius == tolerance for name, radius in radii.items()), "Radius failed")
    # A finite positive partial sum proves exp(3) > 20, hence exp(-3) < 1/20.
    require(sum((Q(3) ** k / factorial(k) for k in range(9)), Q(0)) > 20, "Risk bound failed")
    return {
        "status": "PASS",
        "input_sha256": source_hash,
        "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "model": "t=1/2, s=2 log(2), eta=1/20, b=0; fixed 13-bin score",
        "tv_convention": "sup over events, equal to one half the finite L1 distance",
        "conditional_tv_tolerance": str(tolerance),
        "sufficient_tolerance_at_half_contraction": str(contraction / (6 * span)),
        "score_range": str(span),
        "score_mgf_upper": expectations,
        "reference_contraction_lower": str(contraction),
        "perturbed_contraction_lower": str(remaining_contraction),
        "observations_sufficient": samples,
        "parameter_tv_bound_coefficients": {name: str(value) for name, value in coefficients.items()},
        "one_parameter_at_a_time_sufficient_radii": {name: str(value) for name, value in radii.items()},
        "each_error_upper": "exp(-3) < 1/20",
        "scope": "Conditional on the retained probability enclosures and, under each hypothesis, "
        "every next-bin conditional law given its past being within the stated TV tolerance of "
        "that hypothesis's reference law, almost surely. See docs/model-tolerance.md. "
        "This is not a measured tolerance, an optimized bound, a Lean theorem, or a proof "
        "that marginal closeness alone permits temporal dependence.",
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
    print("PASS: exact conditional model-error budget; see", output)


if __name__ == "__main__":
    main()
