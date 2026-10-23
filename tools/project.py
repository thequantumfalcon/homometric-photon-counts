"""Command catalog for the public scientific research capsule (Python 3.11+)."""

from __future__ import annotations

import argparse
import ast
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
import zipfile

from check_archive_binding import certificate as archive_binding
from check_coordinate_binding import certificate as coordinate_binding
from check_demo import verify as demo_binding
from optical_study import verify as optical_study_binding
from optical_validation import verify as optical_validation_binding
from replay_environment import replay_environment

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / "evidence"
IGNORED = {".git", ".venv", "build", "dist", "__pycache__", ".ruff_cache", ".pytest_cache"}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def files(root: Path = ROOT) -> dict[str, Path]:
    result = {}
    for directory, directories, filenames in os.walk(root, topdown=True):
        directories[:] = [name for name in directories if name not in IGNORED]
        for name in filenames:
            if name in IGNORED:
                continue
            path = Path(directory) / name
            if path.is_file():
                result[path.relative_to(root).as_posix()] = path
    return result


def formal_manifest() -> dict:
    directory = ROOT / "formal"
    raw = (directory / "manifest.json").read_bytes()
    require(
        sha256(raw).hexdigest() == (directory / "manifest.sha256").read_text().split()[0],
        "Formal extension manifest anchor mismatch",
    )
    manifest = json.loads(raw)
    names = set()
    for row in manifest["modules"]:
        name = row["source"]
        require(name == row["name"] + ".lean" and Path(name).name == name, "Unsafe formal source path")
        require(name not in names, "Duplicate formal source")
        names.add(name)
        require(sha256((directory / name).read_bytes()).hexdigest() == row["sha256"], "Changed formal source")
    require(names == {p.name for p in directory.glob("*.lean")}, "Formal extension inventory changed")
    roots = [manifest["fresh_kernel_module"], *manifest.get("additional_fresh_kernel_modules", [])]
    require(len(roots) == len(set(roots)), "Duplicate fresh-kernel root")
    require(all(root + ".lean" in names for root in roots), "Missing fresh-kernel root")
    return manifest


def verify() -> None:
    raw = (EVIDENCE / "public_manifest.json").read_bytes()
    require(
        sha256(raw).hexdigest() == (EVIDENCE / "public_manifest.sha256").read_text().split()[0],
        "Evidence manifest anchor mismatch",
    )
    manifest = json.loads(raw)
    rows = {row["path"]: row for row in manifest["files"]}
    require(len(rows) == len(manifest["files"]), "Duplicate manifest paths")
    actual = files(EVIDENCE)
    require(
        set(actual) - {"public_manifest.json", "public_manifest.sha256"} == set(rows),
        "Evidence inventory changed",
    )
    for name, row in rows.items():
        path = actual[name].resolve()
        require(path.is_relative_to(EVIDENCE), "Unsafe evidence path")
        data = path.read_bytes()
        require(
            len(data) == row["size"] and sha256(data).hexdigest() == row["sha256"],
            "Changed evidence: " + name,
        )
        if path.suffix == ".py":
            ast.parse(data, filename=name)
    # The public derivative has its own input manifest. Its entries must exist.
    continuation = EVIDENCE / "continuation-2026-10-20"
    for row in json.loads((continuation / "continuation_manifest.json").read_text())["files"]:
        data = (continuation / row["path"]).read_bytes()
        require(
            len(data) == row["size"] and sha256(data).hexdigest() == row["sha256"],
            "Stale continuation binding",
        )
    lower = json.loads((EVIDENCE / "followup-2026-10-20/lowerbounds/binned_lower_bound.json").read_text())
    require(lower["necessary_m_at_least"] == 28091647285174, "Unexpected necessary sample claim")
    require(lower["certified_m_sufficient"] == 102399876723169, "Unexpected sufficient sample claim")
    formal_manifest()
    archive_binding()
    coordinate_binding()
    optical_study_binding()
    optical_validation_binding()
    demo_binding()
    vendor = ROOT / "demo/vendor"
    for name, row in json.loads((vendor / "manifest.json").read_text())["artifacts"].items():
        require(Path(name).name == name, "Unsafe demo vendor artifact path")
        data = (vendor / name).read_bytes()
        require(
            len(data) == row["bytes"] and sha256(data).hexdigest() == row["sha256"],
            "Changed demo vendor artifact: " + name,
        )
    print(f"PASS: {len(rows)} public scientific files and input bindings. Integrity is not proof truth.")
    print("PASS: demo source bindings and vendored renderer integrity.")


def check() -> None:
    verify()
    forbidden = re.compile(
        rb"(?i)(?:[a-z]:\\\\?Users\\\\?|[/]Users[/]|@gmail\.com|@outlook\.com|BEGIN [A-Z ]*PRIVATE KEY)"
    )
    for name, path in files().items():
        if path.suffix in {".png", ".jpg", ".pdf"}:
            continue
        data = path.read_bytes()
        require(not forbidden.search(data), "Unreviewed local identity/secret marker: " + name)
        if path.suffix == ".py":
            ast.parse(data, filename=name)
    # Current navigation is checked separately from archived scientific prose.
    docs = [
        ROOT / "README.md",
        *list((ROOT / "demo").rglob("*.md")),
        *list((ROOT / "docs").rglob("*.md")),
        *list((ROOT / ".github").rglob("*.md")),
        *list((ROOT / "formal").rglob("*.md")),
        *list((ROOT / "studies").rglob("*.md")),
    ]
    for path in docs:
        for target in re.findall(r"!?\[[^\]]*\]\(([^)]+)\)", path.read_text(encoding="utf-8")):
            target = target.split("#", 1)[0]
            if not target or "://" in target or target.startswith("mailto:"):
                continue
            require(
                (path.parent / target).resolve().exists(),
                "Broken local link in " + str(path.relative_to(ROOT)) + ": " + target,
            )
    print("PASS: Python syntax, current local documentation links, and bounded privacy markers.")


def run_checks(output: Path, extended: bool) -> None:
    output = output.resolve()
    require(not output.exists(), "Replay output must be fresh")
    require(not output.is_relative_to(EVIDENCE), "Replay output must be outside evidence")
    output.mkdir(parents=True)
    commands = [
        ("endpoint-constants", "followup-2026-10-20/stability/check_constants.py"),
        ("necessary-samples", "followup-2026-10-20/lowerbounds/certify_binned_lower_bound.py"),
        ("independent-exclusion", "followup-2026-10-20/independent_lowerbounds/check_direct_exclusion.py"),
        ("exact-phasors", "scientist-review-2026-10-20/review/verify_density_phasors.py"),
    ]
    if extended:
        commands += [
            ("independent-arb", "followup-2026-10-20/lowerbounds/verify_lower_bound_arb.py"),
            ("arb-probabilities-and-bounded-roots", "scientist-review-2026-10-20/arb/verify_arb.py"),
            ("independent-fourier-tails", "scientist-review-2026-10-20/review/verify_compact_tail_cover.py"),
            ("density-at-zero", "scientist-review-2026-10-20/global/certify_density_zero.py"),
            ("global-four-roots", "scientist-review-2026-10-20/global/certify_compact_gain.py"),
            (
                "independent-global-four-roots",
                "scientist-review-2026-10-20/review/independent_compact_gain.py",
            ),
        ]
    env = replay_environment()
    report = {
        "passed": False,
        "extended": extended,
        "steps": [],
        "evidence_manifest_sha256": sha256((EVIDENCE / "public_manifest.json").read_bytes()).hexdigest(),
    }
    for name, relative in commands:
        source = EVIDENCE / relative
        log = output / (name + ".log")
        print("RUN", name, flush=True)
        started = time.monotonic()
        with log.open("x", encoding="utf-8") as stream:
            result = subprocess.run(
                [sys.executable, "-B", str(source), "--output", str(output / (name + ".json"))],
                cwd=EVIDENCE,
                env=env,
                stdout=stream,
                stderr=subprocess.STDOUT,
                check=False,
            )
        report["steps"].append(
            {
                "name": name,
                "returncode": result.returncode,
                "seconds": time.monotonic() - started,
                "source": relative,
                "source_sha256": sha256(source.read_bytes()).hexdigest(),
            }
        )
        (output / "summary.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        require(result.returncode == 0, "Replay failed; see " + str(log))
        print("PASS", name, flush=True)
    report["passed"] = True
    (output / "summary.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("PASS: mathematical replay", output, flush=True)


def build(output: Path) -> None:
    check()
    output = output.resolve()
    require(not output.exists(), "Archive output must be fresh")
    require(not output.is_relative_to(EVIDENCE), "Archive must be outside evidence")
    payload = files()
    require(
        not any(name.endswith((".zip", ".whl", ".exe", ".dll")) for name in payload),
        "Unexpected packaged binary",
    )
    output.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(output, "x", compression=zipfile.ZIP_DEFLATED, compresslevel=6) as archive:
        for name, path in sorted(payload.items()):
            entry = zipfile.ZipInfo("homometric-photon-counts/" + name, date_time=(2026, 10, 20, 0, 0, 0))
            entry.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(entry, path.read_bytes())
    with zipfile.ZipFile(output) as archive:
        require(archive.testzip() is None, "Archive CRC failure")
        require(len(archive.namelist()) == len(payload), "Archive member count differs")
        for name, path in payload.items():
            require(
                archive.read("homometric-photon-counts/" + name) == path.read_bytes(),
                "Archive changed a file",
            )
    output.with_suffix(output.suffix + ".sha256").write_text(
        sha256(output.read_bytes()).hexdigest() + "  " + output.name + "\n"
    )
    print("PASS: byte-verified source archive", output)


def extract_source_archive(output: Path, destination: Path) -> Path:
    # Windows temporary paths may use short names or junction aliases. Compare
    # canonical paths on both sides without weakening the containment check.
    destination = destination.resolve()
    with zipfile.ZipFile(output) as archive:
        for member in archive.infolist():
            require(
                (destination / member.filename).resolve().is_relative_to(destination), "Unsafe ZIP member"
            )
        archive.extractall(destination)
    return destination


def release(output: Path) -> None:
    build(output)
    with tempfile.TemporaryDirectory(prefix="photon-artifact-") as temp:
        destination = extract_source_archive(output, Path(temp))
        extracted = destination / "homometric-photon-counts"
        subprocess.run(
            [sys.executable, "-B", str(extracted / "tools/project.py"), "check"], cwd=destination, check=True
        )
        subprocess.run(
            [sys.executable, "-B", str(extracted / "tools/optical_validation.py"), "audit"],
            cwd=destination,
            check=True,
            env=replay_environment(),
        )
        subprocess.run(
            [
                sys.executable,
                "-B",
                str(extracted / "tools/project.py"),
                "test",
                "--output",
                str(destination / "replay"),
            ],
            cwd=destination,
            check=True,
        )
    print("PASS: distributed source archive executed outside the checkout. Nothing was published.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["verify", "check", "test", "replay", "build", "release"])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.command in {"verify", "check"}:
        {"verify": verify, "check": check}[args.command]()
    else:
        if args.output is None:
            parser.error("--output is required and must name a fresh destination")
        if args.command in {"test", "replay"}:
            verify()
            run_checks(args.output, args.command == "replay")
        else:
            {"build": build, "release": release}[args.command](args.output)


if __name__ == "__main__":
    main()
