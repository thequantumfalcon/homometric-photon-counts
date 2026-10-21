"""Keep contributor metadata distinct from legitimate methods discussion."""

import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location(
    "credits", Path(__file__).resolve().parents[1] / "tools/check_commit_credits.py"
)
credits = importlib.util.module_from_spec(spec)
spec.loader.exec_module(credits)


class CommitCreditTests(unittest.TestCase):
    def test_reject_tool_author_identity(self):
        with self.assertRaises(ValueError):
            credits.check_identity("Codex <tool@example.invalid>")
        credits.check_identity("The Quantum Falcon <thequantumfalcon@users.noreply.github.com>")

    def test_reject_tool_credit(self):
        for text in ("Co-Authored-By: Codex <tool@example.invalid>", "Generated with Claude Code"):
            with self.assertRaises(ValueError):
                credits.check_text(text)

    def test_allow_human_credit_and_methods_discussion(self):
        credits.check_text(
            "docs: clarify AI assistance limitations\n\nCo-Authored-By: Researcher <human@example.invalid>"
        )


if __name__ == "__main__":
    unittest.main()
