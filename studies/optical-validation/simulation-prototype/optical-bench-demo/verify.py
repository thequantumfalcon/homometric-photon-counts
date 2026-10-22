"""Verify distributed bytes and saved classifications using only Python's stdlib."""

import json
from hashlib import sha256
from pathlib import Path

root = Path(__file__).resolve().parent
manifest = json.loads((root / "MANIFEST.json").read_text(encoding="utf-8"))
for name, expected in manifest["sha256"].items():
    path = (root / name).resolve()
    if (
        not path.is_relative_to(root)
        or sha256(path.read_bytes()).hexdigest() != expected
    ):
        raise ValueError(f"Artifact mismatch: {name}")
report = json.loads((root / "run-demo/results.json").read_text(encoding="utf-8"))
if report["source_sha256"] != manifest["sha256"]["bench.py"]:
    raise ValueError("Source binding mismatch")
if report["model_sha256"] != manifest["sha256"]["input_model.json"]:
    raise ValueError("Model binding mismatch")
for scenario in report["scenarios"]:
    for label in "AB":
        values = scenario["trial_score_means"][label]
        stats = scenario["classification"][label]
        if (
            len(values) != stats["trials"]
            or len(values) != report["trials_per_structure"]
        ):
            raise ValueError("Trial count mismatch")
        errors = sum(
            value >= report["threshold"]
            if label == "A"
            else value < report["threshold"]
            for value in values
        )
        if (
            errors != stats["errors"]
            or errors / len(values) != stats["empirical_error"]
        ):
            raise ValueError("Saved classification mismatch")
print(
    f"PASS: {len(manifest['sha256'])} artifact hashes and "
    f"{2 * len(report['scenarios'])} saved classification records."
)
print("Hashes and replayed classifications do not establish physical validity.")
