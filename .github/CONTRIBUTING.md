# Contributing

Read the [model](../docs/model.md) and [claim ledger](../docs/claims.md). A proof correction should identify the exact statement, assumptions, failed step, and proposed repair. A software correction should include a minimal reproduction and the effect on a certificate.

Run `python tools/project.py check` and `python tools/project.py test --output <fresh-dir>`. Changes affecting rigorous numerics also require the extended replay described in [reproduction](../docs/reproduction.md). Distribution changes require executing the source ZIP using `release`.

Do not edit a certificate simply to make a checker pass. Preserve prior evidence and explain source/hash changes. Distinguish a logical proof, arithmetic certificate, exploratory numerical observation, and external empirical measurement.

AI assistance may be used, but submitters must be able to explain and defend their changes. Disclose material use in the PR's methods/testing discussion. Unverified generated proofs or bug reports without a concrete argument are not evidence. AI tools must not be added as Git co-authors or citation authors.

Use concise commit subjects and explain what changed and why in the PR. The maintainer, Thomas Albrecht, uses signed local commits and local merges. Submit project-owned contributions under the [MIT license](../LICENSE.txt). Identify third-party material and preserve its applicable terms and notices.
