# Recorded validation

Executed on Windows with Python 3.11.9, during 20–21 October 2026.

| Check | Recorded result |
| --- | --- |
| Public evidence derivation | [327 files checked](public_derivation.json); all 45 transformed files differ only by declared provenance edits |
| Arithmetic replay | [All ten stages passed](arithmetic_replay.json), including the separate global Fourier reconstruction |
| Public formal replay | [Five modules recompiled](formal_replay.json), with thirteen standard-axiom audits; no fresh-kernel rerun in this particular public replay |
| Measurable-mixture extension | [Six modules and eighteen audits passed](mixture_formal_replay.json), including a fresh-kernel check of the extension and its imported environment |
| Concrete geometry extension | [Seven modules and 38 audits passed](geometry_formal_replay.json), including a fresh-kernel check of the concrete geometry and its imported environment |
| Gaussian intensity and model extension | [Twelve modules and 73 audits passed](gaussian_formal_replay.json), including a fresh-kernel check of `PhotonGaussianModel` and all imported proof modules |
| Recurrence source compilation | [Two added modules and nine standard-axiom audits passed](recurrence_compile.json); this historical compile-only receipt is supplemented by the completed full replay below |
| Mixed-moment recurrence extension | [Fourteen modules and 82 audits passed](recurrence_formal_replay.json), including a fresh-kernel check of `PhotonMixedRecurrence` and all preceding proof modules |
| Polynomial representation and interpolation | [Fifteen modules and 92 audits passed](polynomial_formal_replay.json), including a fresh-kernel check of `PhotonMomentPolynomial` and all imported proof modules |
| Maintained tooling and source | [Local quality checks passed](local_quality.json), including workflow audits, three attribution-policy tests, two extraction-path regressions, pre-commit and staged secret scanning |
| Initial GitHub publication | [Executed remote checks and settings](github_initial.json): Windows/Ubuntu packaged checks, all ten Arb stages and combined `ci` passed at the named commit; CodeQL Python/Actions setup passed |
| Lean4Lean compatibility | [Local probe failed on the installed object format](lean4lean_compatibility.json); no project-proof check was performed |

The preserved original formal records separately contain successful fresh-kernel checks. The new moment-transfer check took about 412 seconds and covers eight new theorem audits plus five reused algebra audits. The public source statements are byte-identical to their original formal sources; only surrounding provenance records require path/hash transformations.

The source ZIP was compared member-by-member with the working tree, extracted to a new temporary directory, and its standard-library checks executed outside the checkout. The local Markdown layout and illustrative figure were visually inspected. The first remote Windows run exposed a noncanonical temporary-path comparison; the signed fix passed on both Windows and Ubuntu. Actual GitHub math rendering is not covered by the local layout preview.

These are internal executed checks, not external human review, an experiment, or proof of every scientific claim. The receipts identify tested source hashes so later source changes cannot inherit these results silently.
