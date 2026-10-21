# Working on this research capsule

Read README.md, docs/model.md, docs/claims.md and docs/provenance.md before changing a scientific assertion. The primary model has iid Gaussian site phases and conditional Poisson counts. Historical exposure/dependence models have different assumptions.

## Commands

Use `python tools/project.py check`, then `python tools/project.py test --output <fresh-dir>`. The extended Arb checks are `python tools/project.py replay --output <fresh-dir>`. The distribution check is `python tools/project.py release --output <fresh-zip>`. See docs/reproduction.md and .github/CONTRIBUTING.md.

## Evidence and code

The evidence inventory is byte-pinned. Do not format, normalize, or silently edit archived scientific payloads to make checks pass. Add reviewed results and update the explicit public provenance inventory as a separate change. New tooling is standard-library Python unless a dependency is documented and pinned. Use fresh output destinations.

## Claims and review

State the observation model, calibration knowledge, risk criterion and dependence assumptions beside quantitative claims. Do not equate passing tests with full formal proof, novelty, peer review, physical validation, or practical feasibility. PRs must explain the exact resulting behavior and tests. Read docs/decisions/0001-research-capsule.md.

## Identity and security

Use the maintainer's repo-local pseudonymous Git identity and signed local commits. Never add AI co-author trailers, generated-by commit credits, or AI contributor/citation entries. Keep the honest research-methods disclosure. Do not use web/API merges, publish, change account settings, expose private sources, or grant a license from a template alone. Review the concrete artifact before any remote release.
