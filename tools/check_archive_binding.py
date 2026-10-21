"""Bind the quoted Lean phase inputs to exact substrings of the retained JSON."""

from __future__ import annotations

import ast
from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
MODEL = "evidence/homometric-photon-counts/science_completion/harmonic_certificate/input_model.json"
MODEL_SHA256 = "4b9b37a013347b2bd8a273bd2e1be2c867986f2287e1012d6ea9488ed515b288"
LITERALS = "formal/PhotonArchiveParsed.lean"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def unique_pairs(pairs: list[tuple]) -> dict:
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON key")
        result[key] = value
    return result


def bind(model_bytes: bytes, literal_bytes: bytes) -> dict:
    """Check byte origin, not Lean theorem truth or physical interpretation."""
    require(sha256(model_bytes).hexdigest() == MODEL_SHA256, "Archived model hash mismatch")
    text = model_bytes.decode("ascii")
    model = json.loads(text, object_pairs_hook=unique_pairs)
    require(model["n"] == 63, "Unexpected site count")
    require(model["number_field"]["radicands"] == [3, 74, 191], "Unexpected field basis")
    require(
        model["number_field"]["basis_index"] == "bit mask product of sqrt(radicands); indices 0..7",
        "Unexpected field basis order",
    )
    matches = list(re.finditer(r'"phases_exact"\s*:\s*', text))
    require(len(matches) == 2, "Unexpected phase field inventory")
    source = literal_bytes.decode("ascii")
    records = []
    for label, match in zip(("A", "B"), matches, strict=True):
        start = match.end()
        value, end = json.JSONDecoder(object_pairs_hook=unique_pairs).raw_decode(text, start)
        require(value == model["graphs"][label]["phases_exact"], "Wrong JSON field selection")
        require(len(value) == 63, "Wrong phase record count")
        fragment = text[start:end]
        # Only explicit character literals with the shared Python/Lean ASCII
        # escape subset are admitted. No expressions or Unicode escapes.
        # The full formal source is pinned separately by the source manifest.
        declarations = re.findall(rf"^def raw{label} : List Char := (.*)$", source, flags=re.MULTILINE)
        require(len(declarations) == 1, "Missing or duplicate Lean literal declaration")
        quoted = declarations[0]
        character = r"'(?:[^'\\\x00-\x1f]|\\['\"\\nrt])'"
        require(
            re.fullmatch(rf"\[{character}(?:, {character})*\]", quoted) is not None, "Unsafe literal escape"
        )
        chars = ast.literal_eval(quoted)
        require(all(isinstance(c, str) and len(c) == 1 for c in chars), "Invalid character literal")
        require("".join(chars) == fragment, "Lean literal differs from archived bytes")
        records.append(
            {
                "structure": label,
                "json_pointer": f"/graphs/{label}/phases_exact",
                "start_byte": start,
                "end_byte_exclusive": end,
                "bytes": end - start,
                "sha256": sha256(fragment.encode("ascii")).hexdigest(),
                "phase_count": len(value),
            }
        )
    return {
        "passed": True,
        "model": MODEL,
        "model_sha256": MODEL_SHA256,
        "literal_module": LITERALS,
        "literal_module_sha256": sha256(literal_bytes).hexdigest(),
        "fragments": records,
        "scope": "External byte and JSON-field binding only; Lean checks parsing and exact phase geometry separately.",
    }


def certificate(root: Path = ROOT) -> dict:
    return bind((root / MODEL).read_bytes(), (root / LITERALS).read_bytes())


if __name__ == "__main__":
    print(json.dumps(certificate(), indent=2))
