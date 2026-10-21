# Reproduction

Python 3.11 or later is required. The public command catalog is `python tools/project.py --help`; the Makefile delegates to the same implementation.

```sh
python tools/project.py verify
python tools/project.py check
python tools/project.py test --output build/quick-check
```

These checks require only the standard library. Outputs must be fresh and outside the evidence tree. `check` adds syntax, current local-link, and bounded privacy-marker checks. This is not a full secret scanner or a proof of scientific correctness.

## Arb reconstruction

The retained setting uses python-flint 0.9.0 on Windows/Python 3.11. The hash-locked requirements file currently covers the verified Windows x86-64 wheel. In an isolated Windows environment:

```sh
python -m pip install --require-hashes -r requirements-replay.txt
python tools/project.py replay --output build/arb-replay
```

Installation obtains a dependency; the replay itself is offline. An existing isolated python-flint 0.9.0 installation may instead be selected with `PHOTON_FLINT_RUNTIME`. No replay command installs software. Other platforms need their own reviewed wheel hashes and an actual execution record before equivalent platform support is claimed.

The extended replay runs ten checks: exact endpoint constants, two sample-bound implementations, exact phasors, an Arb lower-bound check, probability/bounded-root reconstruction, independent Fourier tails, density at zero, the global root cover, and its separate full-product implementation. It can take several minutes. It does not regenerate every inherited moment from geometry or replace review of the analytic arguments.

## Formal evidence

The Lean sources and scoped successful local receipts are included in the evidence tree. They were checked with Lean 4.35.0 and pinned mathlib dependencies identified by their proof manifests. The receipts record fresh-kernel checks and standard axiom audits; their local command paths are explicitly redacted in this public derivative.

Compiled objects and the large toolchain are not distributed. With the already built pinned Windows runtime and mathlib checkout, run:

```sh
python tools/replay_formal.py --runtime PATH_TO_LEAN_4_35_WINDOWS --mathlib PATH_TO_PINNED_MATHLIB --output build/formal-check
```

This helper verifies runtime binary hashes, dependency commits, tracked source cleanliness, scientific source hashes and all thirteen axiom audits before reporting success. It recompiles the five modules for the new moment bridge. Add `--fresh-kernel` to repeat the longer combined imported-environment check. No dependency is downloaded and no global Git setting is changed. The historical `SCOPE.txt` paths describe the earlier local workflow; this helper is the public entry point. It is a pinned Windows replay, not a claim of cross-platform formal CI or a complete end-to-end Lean theorem.

## Validate the distributed artifact

```sh
python tools/project.py release --output dist/homometric-photon-counts-source.zip
```

This builds a deterministic source ZIP, compares every member with the checkout, extracts into a fresh temporary directory, and runs the packaged checks there. It writes a SHA256 sidecar and publishes nothing. The package contains the source proofs and public provenance inventory, without requiring private research documents.

Local test results and remote Actions results must be reported separately. A workflow file or an unexecuted matrix is not evidence of a passing CI run.
