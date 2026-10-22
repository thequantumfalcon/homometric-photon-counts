"""Audit preserved optical/detector supplements and replay the finite Arb certificate."""

import argparse
import csv
from hashlib import sha256
import json
import math
from pathlib import Path
import shutil
import subprocess
import sys

from replay_environment import replay_environment

ROOT = Path(__file__).resolve().parents[1]
STUDY = ROOT / "studies/optical-validation"
ARCHIVE = STUDY / "simulation-prototype"
FOLDERS = ("optical-bench-demo", "robustness-study", "afterpulse-study", "optical-transfer-certificate")


def require(value: bool, message: str) -> None:
    if not value:
        raise ValueError(message)


def read(path: Path) -> dict:
    return json.loads(path.read_bytes())


def verify() -> dict:
    raw = (STUDY / "manifest.json").read_bytes()
    require(sha256(raw).hexdigest() == (STUDY / "manifest.sha256").read_text().split()[0], "Manifest anchor")
    rows = json.loads(raw)["files"]
    names = {r["path"] for r in rows}
    actual = {
        p.relative_to(STUDY).as_posix()
        for p in ARCHIVE.rglob("*")
        if p.is_file() and "__pycache__" not in p.parts
    }
    require(len(names) == len(rows) and names == actual, "Supplement inventory changed")
    for row in rows:
        path = (STUDY / row["path"]).resolve()
        require(path.is_relative_to(ARCHIVE.resolve()), "Unsafe supplement path")
        raw = path.read_bytes()
        require(
            len(raw) == row["size"] and sha256(raw).hexdigest() == row["sha256"],
            "Supplement changed: " + row["path"],
        )
    for folder in FOLDERS:
        for name, expected in read(ARCHIVE / folder / "MANIFEST.json")["sha256"].items():
            path = (ARCHIVE / folder / name).resolve()
            require(path.is_relative_to((ARCHIVE / folder).resolve()), "Unsafe retained manifest path")
            require(sha256(path.read_bytes()).hexdigest() == expected, "Retained manifest changed")
    data = ARCHIVE / "measured-data-review"
    table_rows = list(csv.DictReader((data / "audit/spad-summary.csv").read_text().splitlines()))
    require(len(table_rows) == 3, "Missing detector tables")
    bins = 0
    for row in table_rows:
        path = data / "data/spad" / row["file"]
        require(path.resolve().parent == (data / "data/spad").resolve(), "Unsafe detector path")
        raw = path.read_bytes()
        require(sha256(raw).hexdigest() == row["sha256"], "Detector table binding changed")
        require(
            raw == (ARCHIVE / "afterpulse-study/data" / row["file"]).read_bytes(), "Detector copy differs"
        )
        values = [float(v) for v in raw.split()]
        require(len(values) == int(row["bins"]), "Detector bin count changed")
        require(all(math.isfinite(v) and v >= 0 for v in values), "Invalid detector mass")
        require(abs(math.fsum(values) - 1) < 1e-12, "Detector table not normalized")
        bins += len(values)
    require(bins == 75658, "Incomplete measured distributions")
    require(
        (data / "data/spad/LICENSE.upstream.txt").read_bytes()
        == (ARCHIVE / "afterpulse-study/data/LICENSE.upstream.txt").read_bytes(),
        "GPL notice differs",
    )
    require(
        (ARCHIVE / "afterpulse-study/inputs.json").read_bytes()
        == (ARCHIVE / "optical-transfer-certificate/afterpulse-inputs.json").read_bytes(),
        "Frozen optical inputs differ",
    )
    require(
        (ARCHIVE / "robustness-study/input_model.json").read_bytes()
        == (ARCHIVE / "optical-transfer-certificate/geometry.json").read_bytes(),
        "Geometry differs",
    )
    # Check bindings whose targets are distributed; omitted local acquisition
    # material remains identified historically, not silently claimed replayed.
    available = 0
    for name, expected in read(ARCHIVE / "optical-transfer-certificate/source-bindings.json")[
        "sha256"
    ].items():
        path = (STUDY / name).resolve()
        if path.is_relative_to(ARCHIVE.resolve()) and path.is_file():
            require(sha256(path.read_bytes()).hexdigest() == expected, "Cross-study binding changed")
            available += 1
    return {
        "status": "PASS",
        "archived_files": len(rows),
        "measured_table_bins": bins,
        "available_original_workspace_bindings": available,
        "scope": "Selected byte identities and external processed-data checks; no physical validation.",
    }


def audit() -> dict:
    result = verify()
    env = replay_environment()
    checks = []
    for folder in FOLDERS:
        command = [sys.executable, "-B", str(ARCHIVE / folder / "verify.py")]
        run = subprocess.run(command, cwd=STUDY, env=env, capture_output=True, text=True, check=False)
        require(run.returncode == 0, folder + " audit failed:\n" + run.stdout + run.stderr)
        checks.append({"study": folder, "returncode": run.returncode, "output": run.stdout.strip()})
    result["checks"] = checks
    return result


def fresh_output(output: Path) -> Path:
    output = output.resolve()
    require(not output.exists(), "Output must be fresh")
    require(
        not any(output.is_relative_to((ROOT / p).resolve()) for p in ("evidence", "formal", "studies")),
        "Output must be outside preserved evidence",
    )
    return output


def replay(output: Path) -> dict:
    output = fresh_output(output)
    result = audit()
    output.mkdir(parents=True)
    source = ARCHIVE / "optical-transfer-certificate"
    staged = output / "optical-transfer-certificate"
    shutil.copytree(source, staged, ignore=shutil.ignore_patterns("__pycache__"))
    env = replay_environment()
    certificate = output / "certificate.json"
    for name, command in [
        ("arb", [sys.executable, "-B", str(staged / "certify.py"), "--output", str(certificate)]),
        ("exact-audit", [sys.executable, "-B", str(staged / "verify.py"), "--certificate", str(certificate)]),
    ]:
        run = subprocess.run(command, cwd=output, env=env, capture_output=True, text=True, check=False)
        (output / (name + ".log")).write_text(run.stdout + run.stderr, encoding="utf-8")
        require(run.returncode == 0, name + " replay failed; see log")
    require(certificate.read_bytes() == (source / "certificate.json").read_bytes(), "Arb certificate differs")
    result.update(
        status="PASS", certificate_reproduced_byte_for_byte=True, archive_preserved=verify()["status"]
    )
    (output / "summary.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["verify", "audit", "replay"])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.command == "replay":
        if args.output is None:
            parser.error("--output is required")
        result = replay(args.output)
    else:
        result = {"verify": verify, "audit": audit}[args.command]()
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
