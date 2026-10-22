"""Freeze caller-relative runtime paths before subprocess working directories change."""

import os
from pathlib import Path


def replay_environment() -> dict[str, str]:
    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    # Retained verifiers use assertions; never disable them in child processes.
    env.pop("PYTHONOPTIMIZE", None)
    if env.get("PHOTON_FLINT_RUNTIME"):
        runtime = str(Path(env["PHOTON_FLINT_RUNTIME"]).resolve())
        env["PHOTON_FLINT_RUNTIME"] = runtime
        env["PYTHONPATH"] = runtime + os.pathsep + env.get("PYTHONPATH", "")
    return env
