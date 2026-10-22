"""Stdlib-only artifact, classification and independent binomial-bound checks."""

import json
import math
from hashlib import sha256
from pathlib import Path

HERE = Path(__file__).resolve().parent


def read(name):
    return json.loads((HERE / name).read_text(encoding="utf-8"))


def digest(name):
    return sha256((HERE / name).read_bytes()).hexdigest()


def upper_limit(k, n, alpha):
    """Invert the binomial CDF by bisection, independently of scipy.stats.beta."""
    if k == n:
        return 1.0
    if k == 0:
        return -math.expm1(math.log(alpha) / n)
    log_combs = [
        math.lgamma(n + 1) - math.lgamma(j + 1) - math.lgamma(n - j + 1)
        for j in range(k + 1)
    ]
    low, high = 0.0, 1.0
    for _ in range(100):
        p = (low + high) / 2
        logs = [
            a + j * math.log(p) + (n - j) * math.log1p(-p)
            for j, a in enumerate(log_combs)
        ]
        peak = max(logs)
        cdf = math.exp(peak) * math.fsum(math.exp(a - peak) for a in logs)
        if cdf > alpha:
            low = p
        else:
            high = p
    return (low + high) / 2


def verify():
    manifest = read("MANIFEST.json")
    for name, expected in manifest["sha256"].items():
        path = (HERE / name).resolve()
        if not path.is_relative_to(HERE) or digest(name) != expected:
            raise ValueError(f"Artifact changed: {name}")
    records = 0
    upper_checks = 0
    seeds = []
    for plan_dir, result_dir in [
        ("screen-frozen", "validation-heldout"),
        ("tolerance-frozen", "tolerance-heldout"),
    ]:
        plan = read(f"{plan_dir}/validation-plan.json")
        result = read(f"{result_dir}/validation.json")
        screen = read(f"{plan_dir}/screen.json")
        if plan["screen_sha256"] != digest(f"{plan_dir}/screen.json") or result[
            "plan_sha256"
        ] != digest(f"{plan_dir}/validation-plan.json"):
            raise ValueError("Plan/result binding mismatch")
        for name, expected in plan["source_hashes"].items():
            if digest(name) != expected:
                raise ValueError("Frozen source mismatch")
        if not (
            plan["source_hashes"] == result["source_hashes"] == screen["source_hashes"]
        ):
            raise ValueError("Provenance disagreement")
        if "selector_sha256" in plan and plan["selector_sha256"] != digest(
            "select_tolerance.py"
        ):
            raise ValueError("Selector mismatch")
        seeds.append(plan["seed"])
        if [r["case"] for r in result["scenarios"]] != plan["cases"]:
            raise ValueError("Validation cases changed")
        family = 2 * sum(not c["control"] for c in plan["cases"])
        if family != plan["family_size"] or family != result["family_size"]:
            raise ValueError("Family size mismatch")
        passes = True
        for row in result["scenarios"]:
            for method in ("uncorrected", "corrected"):
                for label in "AB":
                    values = row[method][label]
                    stats = row["classification"][method][label]
                    if len(values) != plan["trials"] or not all(
                        math.isfinite(v) for v in values
                    ):
                        raise ValueError("Invalid trial values")
                    k = sum(
                        v >= plan["threshold"]
                        if label == "A"
                        else v < plan["threshold"]
                        for v in values
                    )
                    n = len(values)
                    if (
                        stats["errors"] != k
                        or stats["trials"] != n
                        or stats["empirical_error"] != k / n
                    ):
                        raise ValueError("Classification mismatch")
                    interval = [
                        0 if k == 0 else 1 - upper_limit(n - k, n, 0.025),
                        upper_limit(k, n, 0.025),
                    ]
                    if (
                        max(
                            abs(a - b)
                            for a, b in zip(interval, stats["binomial_95_interval"])
                        )
                        > 2e-12
                    ):
                        raise ValueError("Binomial interval mismatch")
                    if method == "corrected" and not row["case"]["control"]:
                        limit = upper_limit(k, n, 0.05 / family)
                        if (
                            abs(limit - stats["simultaneous_one_sided_95_upper"])
                            > 2e-12
                        ):
                            raise ValueError("Simultaneous upper limit mismatch")
                        passes = passes and limit < 0.05
                        upper_checks += 1
                    records += 1
        expected = (
            "PROMISING_AT_TESTED_SETTINGS"
            if passes
            else "REDESIGN_OR_TIGHTER_CALIBRATION_NEEDED"
        )
        if result["status"] != expected:
            raise ValueError("Conclusion differs from declared gate")
    if len(set(seeds)) != 2:
        raise ValueError("Validation seeds are not distinct")
    # Confirm the illustrative physical acquisition calculation independently.
    if not upper_limit(0, 72, 0.025) < 0.05 < upper_limit(0, 71, 0.025):
        raise ValueError("Laboratory sample-size calculation failed")
    record = {
        "status": "PASS",
        "payload_hashes": len(manifest["sha256"]),
        "classification_records": records,
        "independent_simultaneous_bound_checks": upper_checks,
        "two_sided_interval_checks": records,
        "lab_zero_error_minimum_trials_per_label": 72,
    }
    print(json.dumps(record))
    return record


if __name__ == "__main__":
    verify()
