"""Replay the new Lean moment bridge against explicitly supplied pinned local assets."""

from __future__ import annotations

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

from project import EVIDENCE, require, verify


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        value = sha256()
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime", type=Path, required=True)
    parser.add_argument("--mathlib", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--fresh-kernel", action="store_true")
    args = parser.parse_args()
    runtime, mathlib, output = (p.resolve() for p in (args.runtime, args.mathlib, args.output))
    require(not output.exists(), "Formal output must be fresh")
    require(not any(output.is_relative_to(p) for p in (EVIDENCE, runtime, mathlib)), "Unsafe output location")
    verify()
    source_manifest = EVIDENCE / "followup-2026-10-20/lean/proof_manifest.json"
    manifest = json.loads(source_manifest.read_text())
    runtime_prefix = manifest["runtime_relative_path"] + "/"
    mathlib_prefix = manifest["mathlib_relative_path"] + "/"
    checked_runtime = {}
    for name, expected in manifest["input_sha256"].items():
        if name.startswith(runtime_prefix):
            path = runtime / name.removeprefix(runtime_prefix)
        elif name.startswith(mathlib_prefix):
            path = mathlib / name.removeprefix(mathlib_prefix)
        else:
            continue
        require(digest(path) == expected, "Pinned runtime/library input mismatch: " + name)
        checked_runtime[name] = expected
    env = os.environ.copy()
    env.pop("GIT_CONFIG_PARAMETERS", None)
    dependencies = []
    for row in manifest["git_dependencies"]:
        relative = Path(row["path"]).relative_to(manifest["mathlib_relative_path"])
        checkout = (mathlib / relative).resolve()
        require(
            checkout == mathlib or checkout.parent == mathlib / ".lake/packages", "Unsafe dependency path"
        )
        dependencies.append((checkout, row))
    env["GIT_CONFIG_COUNT"] = str(len(dependencies) + 1)
    for i, (checkout, _) in enumerate(dependencies):
        env[f"GIT_CONFIG_KEY_{i}"] = "safe.directory"
        env[f"GIT_CONFIG_VALUE_{i}"] = str(checkout)
    env[f"GIT_CONFIG_KEY_{len(dependencies)}"] = "core.excludesFile"
    env[f"GIT_CONFIG_VALUE_{len(dependencies)}"] = os.devnull
    for checkout, row in dependencies:
        head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=checkout, env=env, text=True).strip()
        dirty = subprocess.check_output(
            ["git", "diff", "--name-only", "HEAD"], cwd=checkout, env=env, text=True
        ).strip()
        require(head == row["commit"] and not dirty, "Dependency commit/source mismatch: " + row["path"])
    env["PATH"] = str(runtime / "bin") + os.pathsep + env.get("PATH", "")
    env["LEAN_PATH"] = str(output)
    env["MATHLIB_CACHE_DIR"] = str(mathlib.parent / "mathlib-cache")
    output.mkdir(parents=True)
    steps = []
    summary = {
        "passed": False,
        "fresh_kernel_performed": args.fresh_kernel,
        "proof_manifest_sha256": digest(source_manifest),
        "runtime_inputs": checked_runtime,
        "steps": steps,
        "scope": manifest["scope"],
    }
    for row in manifest["modules"]:
        name = row["name"]
        source = EVIDENCE / row["source"]
        require(digest(source) == manifest["input_sha256"][row["source"]], "Formal source pin mismatch")
        target = output / (name + ".lean")
        shutil.copyfile(source, target)
        commands = [
            (
                "compile",
                [
                    str(runtime / "bin/lake.exe"),
                    "--no-cache",
                    "env",
                    "lean",
                    "-R",
                    str(output),
                    "-o",
                    str(output / (name + ".olean")),
                    str(target),
                ],
            )
        ]
        if args.fresh_kernel and name == manifest["fresh_kernel_module"]:
            commands.append(
                (
                    "fresh_kernel",
                    [
                        str(runtime / "bin/lake.exe"),
                        "--no-cache",
                        "env",
                        "leanchecker",
                        "--fresh",
                        "--verbose",
                        name,
                    ],
                )
            )
        for kind, command in commands:
            print("RUN", kind, name, flush=True)
            started = time.monotonic()
            result = subprocess.run(
                command,
                cwd=mathlib,
                env=env,
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                check=False,
            )
            log = output / (name + "_" + kind + ".log")
            log.write_text(result.stdout + result.stderr, encoding="utf-8")
            step = {
                "module": name,
                "kind": kind,
                "returncode": result.returncode,
                "seconds": time.monotonic() - started,
                "source_sha256": digest(source),
                "log_sha256": digest(log),
            }
            steps.append(step)
            (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
            require(result.returncode == 0, "Formal check failed; inspect " + str(log))
            if kind == "compile":
                audits = re.findall(r"depends on axioms:\s*\[([^]]*)\]", result.stdout)
                require(len(audits) == row["axiom_audit_count"], "Missing axiom audits")
                for audit in audits:
                    names = {v.strip() for v in audit.split(",") if v.strip()}
                    require(
                        names <= {"propext", "Classical.choice", "Quot.sound"}, "Unexpected theorem axiom"
                    )
                step["axiom_audits"] = len(audits)
            print("PASS", kind, name, flush=True)
    summary["passed"] = True
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print("PASS: pinned public formal replay; inspect the exact theorem premises.", flush=True)


if __name__ == "__main__":
    main()
