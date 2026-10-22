"""One bounded calibration-budget selection using development moments only."""

import itertools
import json
from dataclasses import asdict
from hashlib import sha256
from pathlib import Path

import study as s

HERE = Path(__file__).resolve().parent


def run():
    output = HERE / "tolerance-frozen"
    output.mkdir(exist_ok=False)
    budgets = [(0.25, 2.0), (0.1, 1.0)]
    groups = {}
    summaries = []
    for position, opd in budgets:
        cases = [
            s.Case(f"residual-{position:g}-{opd:g}-{i:03d}", *values)
            for i, values in enumerate(
                itertools.product(
                    (-5.0, 5.0),
                    (-5.0, 5.0),
                    (-30.0, 30.0),
                    (0.98, 1.02),
                    (0.049, 0.051),
                    (0.10, 0.15),
                    (-position, position),
                    (-position, position),
                    (-opd, opd),
                )
            )
        ]
        key = f"{position:g}um-{opd:g}nm"
        groups[key] = s.screen_cases(cases)
        minimum = min(
            row["corrected"][g]["standardized_margin"]
            for row in groups[key]
            for g in "AB"
        )
        summaries.append(
            {
                "key": key,
                "position_error_um": position,
                "opd_coefficient_error_nm": opd,
                "minimum_standardized_margin": minimum,
            }
        )
        print(key, "minimum development margin:", minimum, flush=True)
    # This is a design heuristic, not a certified probability threshold.
    chosen = next(
        (item for item in summaries if item["minimum_standardized_margin"] >= 4),
        summaries[-1],
    )
    rows = groups[chosen["key"]]
    selected = []
    for label in "AB":
        for row in sorted(
            rows, key=lambda r: r["corrected"][label]["standardized_margin"]
        )[:4]:
            case = s.Case(**row["case"])
            if case not in selected:
                selected.append(case)
    screen = {
        "status": "DEVELOPMENT_CALIBRATION_BUDGET_SCREEN",
        "source_hashes": s.bindings(),
        "selector_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "summaries": summaries,
        "chosen": chosen,
        "groups": groups,
        "rule": "Evaluate exactly two declared residual budgets. Choose first with minimum standardized margin >=4, otherwise tighter budget. Take four worst corrected A and four worst corrected B settings. No Monte Carlo validation file is read; no further adaptive budget is authorized by this script.",
        "scope": "Unquantized no-dead-time floating-point finite-corner screen, not continuous tolerance proof.",
    }
    (output / "screen.json").write_text(
        json.dumps(screen, indent=2) + "\n", encoding="utf-8"
    )
    plan = {
        "status": "FROZEN_BEFORE_ITS_VALIDATION",
        "source_hashes": s.bindings(),
        "selector_sha256": screen["selector_sha256"],
        "screen_sha256": sha256((output / "screen.json").read_bytes()).hexdigest(),
        "trials": 200,
        "snapshots": 5000,
        "seed": 2026102318,
        "threshold": s.b.THRESHOLD,
        "cases": [asdict(c) for c in selected],
        "chosen_calibration_budget": chosen,
        "correction": "Same phase-only precompensation as the initial study; no classifier or photon-scale change.",
        "decision_rule": "All corrected non-control A/B one-sided Bonferroni 95% upper error limits below 5% at these tested settings only. No adaptive reruns.",
        "family_size": 2 * len(selected),
        "relation_to_initial_validation": "A separate, tighter calibration requirement selected solely from development moments; retain the initial broad-budget outcome even if it fails. Independent validation seed. This is not a rescue or relabeling of the broad-budget test.",
    }
    (output / "validation-plan.json").write_text(
        json.dumps(plan, indent=2) + "\n", encoding="utf-8"
    )
    print("Frozen tighter-budget validation:", len(selected), "settings", flush=True)


if __name__ == "__main__":
    run()
