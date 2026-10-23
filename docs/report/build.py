"""Verify recovered report inputs and typeset a copy in a fresh directory."""

from __future__ import annotations

import argparse
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parent


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--output", type=Path)
    mode.add_argument("--verify-only", action="store_true", help="Check recovered bytes without LaTeX.")
    args = parser.parse_args()

    manifest = json.loads((ROOT / "recovery.json").read_text(encoding="utf-8"))
    for row in manifest["files"]:
        source = (ROOT / row["path"]).resolve()
        if not source.is_relative_to(ROOT / "historical"):
            raise ValueError("Unsafe report input path")
        data = source.read_bytes()
        if len(data) != row["size"] or sha256(data).hexdigest() != row["sha256"]:
            raise ValueError("Changed recovered report input: " + row["path"])

    if args.verify_only:
        print(f"PASS: {len(manifest['files'])} recovered report files match the recorded hashes and sizes.")
        return 0

    output = args.output.resolve()
    if output.exists():
        parser.error("Output must be a fresh directory.")
    if output.is_relative_to(ROOT):
        parser.error("Output must be outside the preserved report directory.")

    engine = shutil.which("pdflatex")
    if engine is None:
        parser.error("pdfLaTeX is required; install the packages listed in docs/report/README.md.")
    version = subprocess.run(
        [engine, "--version"], capture_output=True, text=True, errors="replace", timeout=30
    )
    version_text = version.stdout + version.stderr
    if version.returncode:
        raise RuntimeError("Could not inspect the installed pdfLaTeX version")

    output.mkdir(parents=True)
    for row in manifest["files"]:
        relative = Path(row["path"]).relative_to("historical")
        if relative.as_posix() == "science_completion_report.pdf":
            continue
        target = output / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / row["path"], target)

    command = [engine]
    if "miktex" in version_text.lower():
        command.append("-disable-installer")
    command += [
        "-no-shell-escape",
        "-recorder",
        "-interaction=nonstopmode",
        "-halt-on-error",
        "science_completion_report.tex",
    ]
    for number in range(1, 4):
        result = subprocess.run(
            command,
            cwd=output,
            capture_output=True,
            text=True,
            errors="replace",
            timeout=180,
        )
        log = output / f"pass-{number}.txt"
        log.write_text(result.stdout + result.stderr, encoding="utf-8")
        if result.returncode:
            print(f"pdfLaTeX stopped; inspect {log}. The historical PDF is unchanged.", file=sys.stderr)
            return result.returncode

    pdf = output / "science_completion_report.pdf"
    result = {
        "scope": "New rendering of unchanged historical source; original recovered PDF preserved.",
        "pdf_sha256": sha256(pdf.read_bytes()).hexdigest(),
        "engine_version": version_text.splitlines()[0],
        "engine_sha256": sha256(Path(engine).read_bytes()).hexdigest(),
        "builder_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "source_manifest_sha256": sha256((ROOT / "recovery.json").read_bytes()).hexdigest(),
        "passes": 3,
        "shell_escape": False,
    }
    (output / "rebuild.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(pdf)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
