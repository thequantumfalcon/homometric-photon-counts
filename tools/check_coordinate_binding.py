"""Bind exact symbolic-coordinate proof inputs to the unchanged archived JSON."""

from __future__ import annotations

from hashlib import sha256
import json
from pathlib import Path
import re

from check_archive_binding import MODEL, MODEL_SHA256, literal_characters, require, unique_pairs

ROOT = Path(__file__).resolve().parents[1]
LITERALS = "formal/PhotonCoordinateData.lean"


def bind(model_bytes: bytes, literal_bytes: bytes) -> dict:
    """Check byte origin; mathematical interpretation is checked separately by Lean."""
    require(sha256(model_bytes).hexdigest() == MODEL_SHA256, "Archived model hash mismatch")
    text = model_bytes.decode("ascii")
    model = json.loads(text, object_pairs_hook=unique_pairs)
    matches = list(re.finditer(r'"coordinates"\s*:\s*', text))
    require(len(matches) == 2, "Unexpected coordinate field inventory")
    source = literal_bytes.decode("ascii")
    records = []
    for label, match in zip(("A", "B"), matches, strict=True):
        start = match.end()
        value, end = json.JSONDecoder(object_pairs_hook=unique_pairs).raw_decode(text, start)
        require(value == model["graphs"][label]["coordinates"], "Wrong JSON field selection")
        require(len(value) == 63, "Wrong coordinate record count")
        require([row["ordinal"] for row in value] == list(range(63)), "Wrong coordinate order")
        fragment = text[start:end]
        require(
            literal_characters(source, f"rawCoordinates{label}") == fragment,
            "Lean literal differs from archived bytes",
        )
        records.append(
            {
                "structure": label,
                "json_pointer": f"/graphs/{label}/coordinates",
                "start_byte": start,
                "end_byte_exclusive": end,
                "bytes": end - start,
                "sha256": sha256(fragment.encode("ascii")).hexdigest(),
                "coordinate_count": len(value),
            }
        )
    return {
        "passed": True,
        "model": MODEL,
        "model_sha256": MODEL_SHA256,
        "literal_module": LITERALS,
        "literal_module_sha256": sha256(literal_bytes).hexdigest(),
        "fragments": records,
        "scope": "External byte and JSON-field binding. Lean interprets base_integer, offset_kind and offset_sign as exact symbolic coordinates; coordinate_decimal is display text, not an exact real input.",
    }


def certificate(root: Path = ROOT) -> dict:
    return bind((root / MODEL).read_bytes(), (root / LITERALS).read_bytes())


if __name__ == "__main__":
    print(json.dumps(certificate(), indent=2))
