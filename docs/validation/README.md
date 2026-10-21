# Recorded local validation

Executed on Windows with Python 3.11.9, during 20–21 October 2026.

| Check | Recorded result |
| --- | --- |
| Public evidence derivation | [327 files checked](public_derivation.json); all 45 transformed files differ only by declared provenance edits |
| Arithmetic replay | [All ten stages passed](arithmetic_replay.json), including the separate global Fourier reconstruction |
| Public formal replay | [Five modules recompiled](formal_replay.json), with thirteen standard-axiom audits; no fresh-kernel rerun in this particular public replay |
| Maintained tooling and source | [Local quality checks passed](local_quality.json), including workflow audits, three attribution-policy tests, pre-commit and staged secret scanning |

The preserved original formal records separately contain successful fresh-kernel checks. The new moment-transfer check took about 412 seconds and covers eight new theorem audits plus five reused algebra audits. The public source statements are byte-identical to their original formal sources; only surrounding provenance records require path/hash transformations.

The source ZIP was compared member-by-member with the working tree, extracted to a new temporary directory, and its standard-library checks executed outside the checkout. The local Markdown layout and illustrative figure were visually inspected. GitHub's actual math rendering, remote CI, repository protections and publication state remain separate checks.

These are internal executed checks, not external human review, an experiment, or proof of every scientific claim. The receipts identify tested source hashes so later source changes cannot inherit these results silently.
