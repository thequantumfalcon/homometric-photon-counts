"""Exercise actual subprocess imports after a caller-relative runtime is selected."""

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from replay_environment import replay_environment  # noqa: E402


class ReplayEnvironment(unittest.TestCase):
    def test_relative_runtime_survives_working_directory_change(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            runtime = root / "runtime"
            runtime.mkdir()
            (runtime / "runtime_probe.py").write_text("VALUE = 78231\n")
            child = root / "unrelated-child-directory"
            child.mkdir()
            relative = os.path.relpath(runtime, Path.cwd())
            with patch.dict(os.environ, {"PHOTON_FLINT_RUNTIME": relative, "PYTHONOPTIMIZE": "1"}):
                env = replay_environment()
            self.assertEqual(Path(env["PHOTON_FLINT_RUNTIME"]), runtime.resolve())
            self.assertNotIn("PYTHONOPTIMIZE", env)
            run = subprocess.run(
                [
                    sys.executable,
                    "-c",
                    "import runtime_probe; assert __debug__; assert runtime_probe.VALUE == 78231",
                ],
                cwd=child,
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(run.returncode, 0, run.stderr)


if __name__ == "__main__":
    unittest.main()
