# Repository readiness

The supplied gold-standard guide is used as a Tier 2 checklist, tailored to a scientific source capsule. Repository quality and proof completeness are assessed separately.

| Area | Current state |
| --- | --- |
| Scientific claims | Explicit model, claim ledger, evidence links, formal scope, and remaining gaps |
| Public provenance | Selected source inventory, original/distributed hashes, bounded path redaction and hash rebinding |
| Local checks | Standard-library and Arb replays; lint, workflow audits, source secret scan, and packaged-artifact checks recorded when completed |
| Identity | Repo-local pseudonymous name/email and SSH signing configuration; the existing attribution guard is retained |
| Attribution | No AI contributor, co-author, or citation entries; research-methods disclosure retained |
| License | MIT adopted by the owner on 2026-10-21; third-party terms and notices retained |
| Remote repository | No creation, push, release, account change, or remote CI result is claimed |
| Protection | Required checks/rulesets must be enabled only after the real CI contexts report; local merges and signing must preserve the persona |
| Security settings | Secret scanning/push protection, default CodeQL, private reporting, Actions restrictions and Dependabot alerts require actual remote configuration/verification |
| Community | Issue forms and contribution/support/security guidance prepared; no invented enforcement contact or active Discussions channel |
| Distribution | Source ZIP with checksum and out-of-checkout execution; no package-registry or service deployment |

The owner explicitly approved MIT after reviewing the recommendation. The guide's ban on AI credit lines applies to Git attribution and contributor identity; the user explicitly requested that the honest methods disclaimer remain.

This project does not need empty application/package scaffolding, launch automation, a star-growth campaign, or performance claims. No Codecov, Scorecard, CodeQL, CI, license, or peer-review badge is shown as passing before its actual state is verified.

Workflow action pins were resolved from the official release tags: checkout v7.0.1 and setup-python v7.0.0. The read-only workflow and disabled credential persistence follow [GitHub's security guidance](https://docs.github.com/en/actions/reference/security/secure-use). The guide's examples were treated as starting points, not copied as verified current configuration.
