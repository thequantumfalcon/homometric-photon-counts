# Reproduction

Python 3.11 or later is required. The public command catalog is `python tools/project.py --help`; the Makefile delegates to the same implementation.

```sh
python tools/project.py verify
python tools/project.py check
python tools/project.py test --output build/quick-check
```

These checks require only the standard library. Outputs must be fresh and outside the evidence tree. `check` adds syntax, current local-link, and bounded privacy-marker checks. This is not a full secret scanner or a proof of scientific correctness.

The core checks and extracted source-package checks have passed on Windows and Ubuntu Linux at the commits identified in the [retained CI record](validation/github_joint.json). A [fresh Linux execution](validation/linux_replay_20261022.json) also covers the full Arb replay and both optical replays, as described below. Lean uses a separately pinned toolchain.

The [quantitative root-stability budget](root-stability.md) has a separate standard-library command:

```sh
python tools/check_root_stability.py --output build/root-stability.json
python -m unittest discover -s tests
```

The tests reproduce its retained receipt and reject missing cover intervals, incorrect endpoint signs and oversized parameter rectangles. This checks arithmetic and certificate handling, not the analytic derivation itself.

## Arb reconstruction

The original retained setting uses python-flint 0.9.0 on Windows/Python 3.11. The Windows requirements file covers the verified Windows x86-64 wheel. In an isolated Windows environment:

```sh
python -m pip install --require-hashes -r requirements-replay.txt
python tools/project.py replay --output build/arb-replay
```

The [Linux requirements file](../requirements-replay-linux.txt) pins the separately verified CPython 3.13 Linux x86-64 wheel. A fresh run on Ubuntu 22.04.5 under WSL2, with CPython 3.13.14, passed all ten Arb stages, both optical replays, the 33 maintained tests in that source snapshot, and extracted-package checks. The [execution receipt](validation/linux_replay_20261022.json) records the source ZIP, scientific inventories, commands, runtime and wheel hashes. To prepare the same Python/platform combination:

```sh
python3.13 -m venv .venv
. .venv/bin/activate
python -m pip install --require-hashes -r requirements-replay-linux.txt
python tools/project.py replay --output build/arb-replay-linux
python tools/optical_study.py replay --output build/optical-replay-linux
python tools/optical_validation.py replay --output build/optical-validation-linux
```

The [updated-package Linux check](validation/linux_updated_package_20261022.json) also passed all 34 tests after the ignored-directory traversal fix, the core replay, recovered-report input checks, and packaging/extraction checks. It compared 545 scientific payloads, formal sources and replay helpers byte for byte with the successful numerical-replay snapshot. The receipt names the tested archive; subsequent changes, including report-rendering metadata, proof receipts and documentation, are outside that snapshot.

Installation obtains a dependency; the replays themselves are offline. An existing isolated python-flint 0.9.0 installation may instead be selected with `PHOTON_FLINT_RUNTIME`. No replay command installs software. Other Python/platform combinations need their own reviewed wheel hashes and an execution record before equivalent support is claimed. This Linux run does not establish Linux Lean compatibility.

The extended replay runs ten checks: exact endpoint constants, two sample-bound implementations, exact phasors, an Arb lower-bound check, probability/bounded-root reconstruction, independent Fourier tails, density at zero, the global root cover, and its separate full-product implementation. It can take several minutes. It does not regenerate every inherited moment from geometry or replace review of the analytic arguments.

## Optical feasibility extension

The separate [study guide](../studies/optical-feasibility/README.md) describes its observation model, conditional guarantees, archived evidence and optional exploration dependencies.

```sh
python tools/optical_study.py verify
python tools/optical_study.py replay --output build/optical-replay
```

The first command uses only the standard library. The second uses the same pinned python-flint environment as the Arb reconstruction above, stages copies into a fresh output directory, runs 18 prototype/calibration tests, and reconstructs both new certificates. Every non-runtime result field must match the archive. It does not edit retained inputs or prove the analytic derivations in Lean. The Windows Arb CI job executes this additional replay.

## Optical transfer and detector supplements

The newer optical/detector supplement can be checked independently:

```sh
python tools/optical_validation.py audit
python tools/optical_validation.py replay --output build/optical-validation
```

The first command is standard-library only: it verifies 115 retained files, external processed detector tables, saved simulation histograms/confidence bounds and the exact enclosure audit. The second uses the existing pinned Python-FLINT 0.9.0 runtime and reproduces the finite optical-transfer certificate exactly, permitting only platform-dependent CRLF/LF line endings. Every other byte, including all enclosure digits, must match; the replay reports byte identity separately and preserves the archived certificate. Neither regenerates the Monte Carlo simulations. Caller-relative `PHOTON_FLINT_RUNTIME` paths are resolved before subprocess directories change. The [study guide](../studies/optical-validation/README.md) identifies optional simulation dependencies, historical nonportable audit flags and separate GPL data terms. The packaged release also runs these standard-library audits after extraction.

## Formal evidence

Archived Lean sources and scoped successful local receipts are included in the evidence tree. They were checked with Lean 4.35.0 and pinned mathlib dependencies identified by their proof manifests. Those receipts record historical fresh-kernel checks and standard axiom audits; their local command paths are explicitly redacted in this public derivative. Current extensions live under `formal/`, with execution coverage recorded separately in the validation directory.

On 22 October, a [full fresh Windows source rebuild](validation/formal_replay_20261022.json) passed all 61 modules and all 722 required theorem-axiom audits in 39 minutes 38 seconds. The [exact executed driver](validation/formal_replay_20261022/executed_driver.py.txt) ran at most two modules concurrently, gated by their project imports, with the same compiler command and input checks as the maintained helper below. Every project proof object was newly compiled; only pinned imported library artifacts came from the official mathlib cache. The receipt retains all compiler logs, source and output hashes, and the declared replacement of absolute repository prefixes in public logs. This was ordinary Lean kernel compilation, without an additional `leanchecker --fresh` or Nanoda run. The root-count and testing arguments retain their separate analytic and numerical scope.

Compiled objects and the large toolchain are not distributed. The mathlib build must include `Mathlib.Probability.Distributions.Gaussian.Real`, `Mathlib.Probability.HasCondDistrib` and their dependencies; the replay command does not fetch missing compiled imports. With the already built pinned Windows runtime and mathlib checkout, run:

```sh
python tools/replay_formal.py --runtime PATH_TO_LEAN_4_35_WINDOWS --mathlib PATH_TO_PINNED_MATHLIB --output build/formal-check
```

This helper verifies runtime binary hashes, dependency commits, tracked source cleanliness, scientific source hashes and all 722 axiom audits before reporting success. It recompiles 61 modules: the five archived moment-bridge modules, the [measurable-mixture extension](../formal/SCOPE.md), the [concrete geometry extension](../formal/GEOMETRY.md), eight [Gaussian/intensity/recurrence/polynomial modules](../formal/GAUSSIAN.md), 29 [concrete certificate and linking modules](../formal/CERTIFICATES.md), the [joint snapshot module](../formal/JOINT_MODEL.md), four [archive-input modules](../formal/ARCHIVE_INPUT.md), seven [coordinate/reindexing modules](../formal/COORDINATES.md), and five [spatial homometry modules](../formal/HOMOMETRY.md). The extensions have a separate source hash manifest. Add `--fresh-kernel` to check `PhotonJointModel`, `PhotonArchiveBridge`, `PhotonCountReindex`, `PhotonCoordinateGeometry` and `PhotonHomometry`, each with its imported environment. These roots cover separate branches; concrete linking modules are kernel-checked during compilation. Earlier receipts do not silently acquire new proofs. No dependency is downloaded and no global Git setting is changed. The historical `SCOPE.txt` paths describe the earlier local workflow; this helper is the public entry point. See the [validation record](validation/README.md) for completed execution coverage. It is a pinned Windows replay, not a claim of cross-platform formal CI or formal coverage of every scientific result. The large concrete certificate blocks require substantial memory and several gigabytes of object storage. The retained concrete receipt stages previously successful compilations into an isolated directory and fresh-checks the full environment; this command performs a full source rebuild.

## Optional independent exported-proof check

The retained Lean 4.35.0 Windows distribution also contains `leanexport.exe` and Nanoda 0.4.19 (`nanoda_bin.exe`). Their selected bytes are recorded in [checker_artifacts.json](validation/checker_artifacts.json). This project does not install or upgrade a checker automatically.

After the formal build, use the pinned mathlib checkout as the working directory, put that runtime's `bin` directory on `PATH`, and set `LEAN_PATH` to the absolute formal-build output directory. Export only `PhotonConcreteSeparation.count_laws_distinct` with the argument list `leanexport PhotonConcreteSeparation -- PhotonConcreteSeparation.count_laws_distinct`, through `lake --no-cache env`. Capture stdout directly to a binary file, for example with Python's `subprocess.run(..., stdout=opened_binary_file, check=True)`, so shell text encoding does not change the newline-delimited JSON. The selected export includes the theorem's transitive dependencies and is several gigabytes; it is not part of the source capsule.

Run `nanoda_bin PATH_TO_CONFIG.json` with this configuration, replacing the export path:

```json
{
  "use_stdin": false,
  "export_file_path": "ABSOLUTE_PATH_TO_EXPORTED_NDJSON",
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "unpermitted_axiom_hard_error": true,
  "num_threads": 4,
  "nat_extension": true,
  "string_extension": true,
  "print_success_message": true
}
```

Retain the exit status, checker/export hashes and complete diagnostic log. This is a direct exported-proof check, not the sandboxed Lean comparator workflow. It does not independently establish the intended meaning of the theorem. Consult the [validation record](validation/README.md) for actual executed coverage.

The joint-law check exports `PhotonJointModel` with the three names `PhotonJointModel.count_given_phases`, `PhotonJointModel.count_given_intensity`, and `PhotonJointModel.count_marginal` after `--`. This selects their dependency closures; it does not recheck the concrete coefficient theorem, which has its separate export above.

The [model-error bound](model-tolerance.md) has a standard-library replay: `python tools/check_model_tolerance.py --output build/model-tolerance.json`. This exact rational check is also exercised by the unit suite.

## Validate the distributed artifact

```sh
python tools/project.py release --output dist/homometric-photon-counts-source.zip
```

This builds a deterministic source ZIP, compares every member with the checkout, extracts into a fresh temporary directory, and runs the packaged checks there. It writes a SHA256 sidecar and publishes nothing. The package contains the source proofs and public provenance inventory, without requiring private research documents.

Local test results and remote Actions results must be reported separately. A workflow file or an unexecuted matrix is not evidence of a passing CI run.
