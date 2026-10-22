"""Replay in a fresh copy without modifying preserved sources or results."""

import argparse
import os
import shutil
import subprocess
import sys
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", type=Path, required=True)
parser.add_argument("--checks-only", action="store_true")
args = parser.parse_args()
source = Path(__file__).resolve().parent
target = args.output.resolve()
target.mkdir(parents=True, exist_ok=False)
for path in [
    *source.glob("*.py"),
    source / "input_model.json",
    *source.glob("*.txt"),
]:
    shutil.copyfile(path, target / path.name)
env = dict(os.environ, OPENBLAS_NUM_THREADS="1", MPLCONFIGDIR=str(target / "mpl-cache"))
commands = [["-m", "unittest", "discover", "-p", "test_robustness.py", "-v"]]
if not args.checks_only:
    commands += [
        ["study.py", "screen", "--output", "screen-frozen"],
        ["select_tolerance.py"],
        [
            "study.py",
            "validate",
            "--plan",
            "screen-frozen/validation-plan.json",
            "--output",
            "validation-heldout",
        ],
        [
            "study.py",
            "validate",
            "--plan",
            "tolerance-frozen/validation-plan.json",
            "--output",
            "tolerance-heldout",
        ],
        ["make_report.py"],
    ]
for command in commands:
    subprocess.run([sys.executable, *command], cwd=target, env=env, check=True)
print("Fresh replay complete:", target)
