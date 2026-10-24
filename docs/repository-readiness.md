# Repository readiness

This page records publication and maintenance checks for the scientific source capsule. Repository quality and proof completeness are assessed separately. Remote settings and CI outcomes describe the linked historical inspections; they have not been reverified as the current remote state by this page.

The optical/detector addition preserves 115 supplemental payloads, adds a portable audit and exact Arb replay, and fixes caller-relative runtime selection. It does not change earlier scientific payloads. Its [development specification](../studies/optical-validation/DEVELOPMENT-SPEC.md) separates local acceptance criteria from remote publication status; previous CI receipts below remain tied to their recorded commits.

| Area | Recorded state |
| --- | --- |
| Scientific claims | Explicit model, claim ledger, evidence links, formal scope, and remaining gaps |
| Public provenance | Selected source inventory, original/distributed hashes, bounded path redaction and hash rebinding |
| Local checks | Standard-library and Arb replays, scoped Lean checks, lint, workflow audits, source secret scan, and extracted-package checks; see the validation records |
| Identity | At the 22 October inspection, all 19 main-branch signatures were GitHub-verified; three feature-branch commits were unsigned. The [22-commit history audit](validation/git_history_20261022.json) records that snapshot's identities and signature scope; the attribution guard is retained. |
| Attribution | No AI contributor, co-author, or citation entries; research-methods disclosure retained |
| License | MIT adopted by the owner on 2026-10-21; third-party terms and notices retained |
| Remote repository | Public at [thequantumfalcon/homometric-photon-counts](https://github.com/thequantumfalcon/homometric-photon-counts); the [published joint-proof commit](validation/github_joint.json) passed PR and main-branch Windows/Ubuntu packaging, Arb replay and combined `ci`, plus main-branch CodeQL Python/Actions checks |
| Protection | The recorded configuration used checks that had already reported and retained local merging and signing. Consult [GitHub rules](https://github.com/thequantumfalcon/homometric-photon-counts/rules) for the current configuration |
| Security settings | Secret scanning/push protection and private reporting enabled; default CodeQL for Python/Actions passed with no open findings at the recorded inspection; read-only Actions, GitHub-owned action restriction, SHA pinning and external-fork approval enabled; dependency security updates enabled |
| Community | Issue forms and contribution/support/security guidance available; no invented enforcement contact or active Discussions channel |
| Distribution | Source ZIP with checksum and out-of-checkout execution; no package-registry or service deployment |

Project-owned code and documentation use the owner-approved MIT license. AI co-author trailers and contributor/citation credits are prohibited; the [research-methods disclosure](research-disclosure.md) remains part of the scientific record.

Badges and publication claims must correspond to their verified scope and recorded state.

Workflow action pins were resolved from the official release tags: checkout v7.0.1 and setup-python v7.0.0. The read-only workflow and disabled credential persistence follow [GitHub's security guidance](https://docs.github.com/en/actions/reference/security/secure-use).

The [initial GitHub record](validation/github_initial.json) binds the reported first passing CI and settings to an inspected commit. The [joint-proof publication record](validation/github_joint.json) adds the signed proof commit, its successful PR and main-branch checks, and zero open code-scanning findings at that inspection. Later commits need their own checks; the README links the live main-branch CI status. Code scanning and repository protection are software-maintenance controls, not mathematical peer review.
