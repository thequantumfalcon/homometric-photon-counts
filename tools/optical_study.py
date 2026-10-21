"""Verify or replay the separately archived optical feasibility study offline."""

from __future__ import annotations

import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
STUDY = ROOT / "studies/optical-feasibility"
ARCHIVE = STUDY / "simulation-prototype"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def read(path: Path) -> dict:
    return json.loads(path.read_bytes())


def risk(variance: F, distance: F, samples: int) -> F:
    require(variance >= 0 and samples > 0, "Invalid variance or snapshot count")
    return variance / (variance + samples * distance**2) if distance > 0 else F(1)


def distance_from_mean(mean: dict, threshold: F, label: str) -> F:
    lower, upper = F(mean["lower"]), F(mean["upper"])
    require(lower <= upper, "Reversed mean interval")
    return threshold - upper if label == "A" else lower - threshold


def audit_calibration(data: dict) -> list[dict]:
    require(data["fixed_threshold"] == "-3200551/5000000", "Changed fixed threshold")
    require(data["snapshots"] == 5000 and data["q_over_pi"] == "201/200", "Changed experiment")
    require(data["uniform_phase_levels"] == 256, "Changed quantizer")
    require(
        data["centers"] == {"gain": "1", "background": "1/8", "phase_variance": "1/20"},
        "Changed calibration centers",
    )
    rows = data["box_checks"]
    require(
        [F(r["gain_radius"]) for r in rows] == [F(0), F(1, 200), F(1, 100), F(1, 50), F(1, 25), F(2, 25)],
        "Missing or reordered calibration boxes",
    )
    budgets = []
    for box in rows:
        radius = F(box["gain_radius"])
        require(
            F(box["background_radius"]) == radius * F(5, 4)
            and F(box["variance_radius"]) == radius / 20
            and box["dead_time_up_to_22ns"],
            "Changed simultaneous box",
        )
        require(set(box["results"]) == {"A", "B"}, "Missing hypothesis")
        counts, risks = [], []
        for label, record in box["results"].items():
            d = distance_from_mean(record["mean_enclosure"], F(data["fixed_threshold"]), label)
            v = F(record["variance_upper_exact"])
            require(d == F(record["distance_lower_exact"]), "Incorrect threshold distance")
            value = risk(v, d, data["snapshots"])
            require(value == F(record["risk_upper_exact"]), "Incorrect calibration risk")
            count = (19 * v // d**2 + 1) if d > 0 and v > 0 else None
            require(count == record["sufficient_samples_for_5pct"], "Incorrect sufficient count")
            counts.append(count)
            risks.append(value)
        require(
            box["status"] == ("PASS" if max(risks) < F(1, 20) else "NOT_CERTIFIED"), "Incorrect box status"
        )
        count = max(counts) if None not in counts else None
        require(count == box["sufficient_samples_for_5pct"], "Incorrect combined count")
        if radius in (F(1, 50), F(1, 25)):
            samples = 5000 if radius == F(1, 50) else 11000
            ceiling = F(453, 10000) if samples == 5000 else F(49, 1000)
            bound = {
                g: risk(F(r["variance_upper_exact"]), F(r["distance_lower_exact"]), samples)
                for g, r in box["results"].items()
            }
            require(all(v < ceiling for v in bound.values()), "Published budget not certified")
            budgets.append(
                {
                    "gain_radius": str(radius),
                    "snapshots": samples,
                    "error_upper_exact": {g: str(v) for g, v in bound.items()},
                }
            )
    return budgets


def audit_candidate(data: dict) -> None:
    require(data["parameters"]["snapshots"] == 5000, "Changed candidate count")
    require(len(data["scenarios"]) == 6, "Missing detector scenarios")
    for scenario in data["scenarios"]:
        require(set(scenario["results"]) == {"A", "B"}, "Missing hypothesis")
        for label, record in scenario["results"].items():
            d = distance_from_mean(record["mean"], F(scenario["threshold_exact"]), label)
            require(d > 0 and d == F(record["threshold_distance_lower"]), "Invalid candidate separation")
            v = F(record["variance_upper_bound_exact"])
            value = risk(v, d, 5000)
            require(
                value == F(record["each_error_upper_exact"]) and value < F(263, 10000),
                "Incorrect candidate risk",
            )


def verify() -> dict:
    raw = (STUDY / "manifest.json").read_bytes()
    require(
        sha256(raw).hexdigest() == (STUDY / "manifest.sha256").read_text().split()[0],
        "Study manifest anchor mismatch",
    )
    rows = json.loads(raw)["files"]
    expected = {r["path"] for r in rows}
    require(len(expected) == len(rows), "Duplicate study paths")
    actual = {
        p.relative_to(STUDY).as_posix()
        for p in ARCHIVE.rglob("*")
        if p.is_file() and "__pycache__" not in p.parts
    }
    require(actual == expected, "Study inventory changed")
    for row in rows:
        path = (STUDY / row["path"]).resolve()
        require(path.is_relative_to(ARCHIVE.resolve()), "Unsafe study path")
        raw = path.read_bytes()
        require(
            len(raw) == row["size"] and sha256(raw).hexdigest() == row["sha256"],
            "Changed study file: " + row["path"],
        )
    for relative in (
        "RUN_MANIFEST.json",
        "feasibility-study/MANIFEST.json",
        "design-search/MANIFEST.json",
        "calibration-study/MANIFEST.json",
    ):
        path = ARCHIVE / relative
        for name, digest in read(path)["sha256"].items():
            require(
                sha256((path.parent / name).read_bytes()).hexdigest() == digest,
                "Historical study binding changed",
            )
    inputs = read(ARCHIVE / "feasibility-study/MANIFEST.json")["input_sha256"]
    for name, digest in inputs.items():
        require(
            sha256((ROOT / "evidence" / name).read_bytes()).hexdigest() == digest,
            "Changed study input: " + name,
        )
    lower = read(ROOT / "evidence/followup-2026-10-20/lowerbounds/binned_lower_bound.json")
    budget = read(ARCHIVE / "feasibility-study/run-checked/results.json")["budget"]
    tv, loss = F(budget["tv_upper_exact"]), F(lower["affinity_bound"]["one_minus_affinity_upper"])
    require(
        budget["snapshots"] == 288000 and 0 <= tv <= 1 and tv**2 >= 2 * 288000 * loss,
        "Invalid reference budget bound",
    )
    require(F(budget["equal_prior_error_lower_exact"]) == (1 - tv) / 2, "Invalid reference error bound")
    audit_candidate(read(ARCHIVE / "design-search/interval-final/certificate.json"))
    budgets = audit_calibration(read(ARCHIVE / "calibration-study/run-checked/calibration.json"))
    return {
        "status": "PASS",
        "archived_files": len(rows),
        "inputs": inputs,
        "candidate_risk_records": 12,
        "calibration_risk_records": 12,
        "budgets": budgets,
        "scope": "Byte identity and rational arithmetic conditional on retained moment enclosures; no hardware or Lean check.",
    }


def stage(output: Path) -> Path:
    verify()
    output = output.resolve()
    require(not output.exists(), "Output must be fresh")
    require(
        not any(output.is_relative_to(ROOT / p) for p in ("evidence", "formal", "studies")),
        "Output must be outside retained evidence and sources",
    )
    output.mkdir(parents=True)
    workspace = output / "workspace"
    shutil.copytree(ARCHIVE, workspace / "simulation-prototype", ignore=shutil.ignore_patterns("__pycache__"))
    for name in read(ARCHIVE / "feasibility-study/MANIFEST.json")["input_sha256"]:
        destination = workspace / "public-repo/evidence" / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / "evidence" / name, destination)
    return workspace


def replay(output: Path, exploratory_tests: bool = False) -> None:
    workspace = stage(output)
    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    if env.get("PHOTON_FLINT_RUNTIME"):
        env["PYTHONPATH"] = (
            str(Path(env["PHOTON_FLINT_RUNTIME"]).resolve()) + os.pathsep + env.get("PYTHONPATH", "")
        )
    jobs = [
        ("prototype-tests", ["simulation-prototype/test_simulation.py"]),
        ("calibration-tests", ["simulation-prototype/calibration-study/test_calibration.py"]),
        ("candidate", ["simulation-prototype/design-search/certify.py", "--output", "results/candidate"]),
        (
            "calibration",
            ["simulation-prototype/calibration-study/calibrate.py", "--output", "results/calibration"],
        ),
    ]
    if exploratory_tests:
        jobs += [
            ("optical-tests", ["simulation-prototype/feasibility-study/test_study.py"]),
            ("design-tests", ["simulation-prototype/design-search/test_design.py"]),
        ]
    summary = {"passed": False, "steps": [], "exploratory_tests": exploratory_tests}
    destination = output.resolve() / "summary.json"
    for name, args in jobs:
        print("RUN", name, flush=True)
        with (output / (name + ".log")).open("x", encoding="utf-8") as stream:
            result = subprocess.run(
                [sys.executable, "-B", *args],
                cwd=workspace,
                env=env,
                stdout=stream,
                stderr=subprocess.STDOUT,
                check=False,
            )
        summary["steps"].append({"name": name, "returncode": result.returncode})
        destination.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
        require(result.returncode == 0, "Study replay failed; see " + str(output / (name + ".log")))
    for fresh, retained in [
        ("candidate/certificate.json", "design-search/interval-final/certificate.json"),
        ("calibration/calibration.json", "calibration-study/run-checked/calibration.json"),
    ]:
        new, old = read(workspace / "results" / fresh), read(ARCHIVE / retained)
        # Python patch-version metadata can differ; every mathematical field must match.
        new.pop("runtime")
        old.pop("runtime")
        require(new == old, "Recomputed study differs from retained result: " + fresh)
    summary.update(passed=True, exact_certificate_reproduction=True, archive_preserved=verify()["status"])
    destination.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print("PASS: fresh study replay and unchanged archived evidence", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["verify", "stage", "replay"])
    parser.add_argument("--output", type=Path)
    parser.add_argument("--exploratory-tests", action="store_true")
    args = parser.parse_args()
    if args.command == "verify":
        print(json.dumps(verify(), indent=2))
    else:
        if args.output is None:
            parser.error("--output is required")
        if args.command == "stage":
            print(stage(args.output))
        else:
            replay(args.output, args.exploratory_tests)


if __name__ == "__main__":
    main()
