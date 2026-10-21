"""Reject AI attribution trailers/credits without suppressing methods disclosure."""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess

TOOLS = r"(?:claude|codex|chatgpt|openai|copilot|gemini|anthropic|gpt[- ]?\d|ai[ -]?(?:agent|assistant))"
CREDIT = re.compile(r"(?im)^(?:co-authored-by|generated[- ](?:by|with)|assisted[- ]by)\s*:?[^\n]*" + TOOLS)


def check_text(text: str) -> None:
    if CREDIT.search(text):
        raise ValueError("AI attribution is not allowed in Git contributor/credit metadata")


def check_identity(text: str) -> None:
    if re.search(TOOLS, text, re.IGNORECASE):
        raise ValueError("AI identities must not be Git authors or committers")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--message-file", type=Path)
    args = parser.parse_args()
    if args.message_file:
        check_text(args.message_file.read_text(encoding="utf-8"))
    else:
        result = subprocess.run(
            ["git", "log", "--all", "--format=%B"], capture_output=True, text=True, check=False
        )
        if result.returncode:
            raise SystemExit("Could not inspect Git history; this is not a passing attribution check")
        check_text(result.stdout)
        identities = subprocess.check_output(
            ["git", "log", "--all", "--format=%an%n%ae%n%cn%n%ce"], text=True
        )
        check_identity(identities)
    print("PASS: no AI attribution trailers or generated-by credits in inspected commit messages")


if __name__ == "__main__":
    main()
