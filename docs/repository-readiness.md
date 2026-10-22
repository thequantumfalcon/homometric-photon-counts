# Repository readiness

The supplied gold-standard guide is used as a Tier 2 checklist, tailored to a scientific source capsule. Repository quality and proof completeness are assessed separately.

The latest optical/detector addition preserves 115 supplemental payloads, adds a portable audit and exact Arb replay, and fixes caller-relative runtime selection. It does not change earlier scientific payloads. Its [development specification](../studies/optical-validation/DEVELOPMENT-SPEC.md) separates local acceptance criteria from remote publication status; previous CI receipts below remain tied to their recorded commits.

| Area | Current state |
| --- | --- |
| Scientific claims | Explicit model, claim ledger, evidence links, formal scope, and remaining gaps |
| Public provenance | Selected source inventory, original/distributed hashes, bounded path redaction and hash rebinding |
| Local checks | Standard-library and Arb replays, scoped Lean checks, lint, workflow audits, source secret scan, and extracted-package checks; see the validation records |
| Identity | Pseudonymous signed commits verified locally and by GitHub; the existing attribution guard is retained |
| Attribution | No AI contributor, co-author, or citation entries; research-methods disclosure retained |
| License | MIT adopted by the owner on 2026-10-21; third-party terms and notices retained |
| Remote repository | Public at [thequantumfalcon/homometric-photon-counts](https://github.com/thequantumfalcon/homometric-photon-counts); the [published joint-proof commit](validation/github_joint.json) passed PR and main-branch Windows/Ubuntu packaging, Arb replay and combined `ci`, plus main-branch CodeQL Python/Actions checks |
| Protection | Current rules are visible in [GitHub rules](https://github.com/thequantumfalcon/homometric-photon-counts/rules). Required checks are configured only after their real contexts have reported; local merges and signing preserve the persona |
| Security settings | Secret scanning/push protection and private reporting enabled; default CodeQL for Python/Actions passed with no open findings at the recorded inspection; read-only Actions, GitHub-owned action restriction, SHA pinning and external-fork approval enabled; dependency security updates enabled |
| Community | Issue forms and contribution/support/security guidance available; no invented enforcement contact or active Discussions channel |
| Distribution | Source ZIP with checksum and out-of-checkout execution; no package-registry or service deployment |

The owner explicitly approved MIT after reviewing the recommendation. The guide's ban on AI credit lines applies to Git attribution and contributor identity; the user explicitly requested that the honest methods disclaimer remain.

This project does not need empty application/package scaffolding, launch automation, a star-growth campaign, or performance claims. No Codecov, Scorecard, CodeQL, CI, license, or peer-review badge is shown as passing before its actual state is verified.

Workflow action pins were resolved from the official release tags: checkout v7.0.1 and setup-python v7.0.0. The read-only workflow and disabled credential persistence follow [GitHub's security guidance](https://docs.github.com/en/actions/reference/security/secure-use). The guide's examples were treated as starting points, not copied as verified current configuration.

The [initial GitHub record](validation/github_initial.json) binds the reported first passing CI and settings to an inspected commit. The [joint-proof publication record](validation/github_joint.json) adds the signed proof commit, its successful PR and main-branch checks, and zero open code-scanning findings at that inspection. Later commits need their own checks; the README links the live main-branch CI status. Code scanning and repository protection are software-maintenance controls, not mathematical peer review. Account-wide two-factor authentication and vigilant mode were not verified or modified. No tag, package-registry release, or outreach to scientists has been made.
