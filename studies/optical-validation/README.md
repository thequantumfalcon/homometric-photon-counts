# Optical transfer and detector checks

These supplements extend the [earlier feasibility study](../optical-feasibility/README.md)
with a scalar optical model, calibration-error simulations, external processed
SPAD data, an afterpulsing simulation and rigorous finite-setting numerical
checks. **They do not physically validate the proposed apparatus.**

The [manifest](manifest.json) preserves 115 selected files byte for byte. Earlier
proofs, certificates, and unsuccessful outcomes remain intact. Historical
README/status fields describe their original local execution; this page and
the public runner below describe the supported distribution.

| Evidence | What it establishes | What remains open |
| --- | --- | --- |
| [Optical bench model](simulation-prototype/optical-bench-demo/METHOD.txt) | A 63-cell Gaussian/Fraunhofer model with finite square cells, selected-mode collection, displacement and signed quadratic OPD; comparison with sampled POPPY propagation | Measured complex transfer and whether the proposed hardware realizes this model |
| [Calibration robustness](simulation-prototype/robustness-study/METHOD.txt) | The wider residual budget failed: a selected case had 110/200 A errors. At eight tighter selected settings, each label had 0/200 errors; simultaneous 95% upper bound 0.028429655815507066 | No continuous optical-tolerance certificate. The proposed 0.25 micrometre per-axis and 2 nm quadratic-OPD residual targets are unmeasured |
| [External detector distributions](simulation-prototype/measured-data-review/audit/spad-summary.csv) | Three published, processed afterpulse delay tables, 75,658 bins, retained identities and license | Raw timestamps, per-bin uncertainty, and calibration at the proposed wavelength/flux are unavailable |
| [Afterpulsing study](simulation-prototype/afterpulse-study/README.txt) | Three selected optical settings and eight detector profiles; all 48 label/case/profile comparisons had 0/200 simulation errors, each trial using 5,000 gates. Simultaneous one-sided 95% upper bound 0.03375192026711007 | A conditional finite simulation study, not a continuous-box or measured performance guarantee |
| [Arb transfer certificate](simulation-prototype/optical-transfer-certificate/METHOD.txt) | 26 selected settings plus three frozen transfers, 224 integral pairs, 1,827 coefficients, 12,096 finite phase commands and 192 saved rate witnesses checked | Full stochastic numerical-error propagation, continuous tolerances and physical model validity |

The homometric prototype runs use known programmed structures at `q=201*pi/200`. This changed
frequency exposes a second-order signal. It is not an experimental demonstration
of the original fourth-order-only effect or recovery of an unknown structure.
The original sample bound and earlier ideal-model continuous-box certificates
are unchanged; their guarantees do not automatically extend to these new optics
or detector effects.

## Arithmetic result

At 256-bit precision, the exact declared model and the saved binary64 transfers
differ by at most **1.20e-15 per coefficient** in real/imaginary L1 distance and
**3.43e-16 radians** in phase correction. Holding unit phasors fixed, coefficient
errors contribute at most **3.90e-12** to dimensionless intensity. The 192 saved
photon-rate witnesses differ by at most **2.26e-12 photons/gate**.

The complex Gaussian integral is evaluated using both an error-function closed
form and validated integration. Both algorithms share Arb. Exact dyadic
endpoints are retained and audited with rational arithmetic. Quantization is
discontinuous: all 12,096 saved commands have strict rounding-bin inclusion,
but that finite check does not prove a bound for every future random draw.
This is an arithmetic certificate and written derivation, not a new Lean theorem.

## External data and detector assumptions

The source is Straka, Grygar, Hlousek and Jezek,
[Counting Statistics of Actively Quenched SPADs Under Continuous Illumination](https://doi.org/10.1109/JLT.2020.2994654),
with data from [SPAD-counting-model at commit 4ed0903](https://github.com/ivo-s/SPAD-counting-model/tree/4ed0903200b59b7f94715c38ca2668bb832e80d8).
The three tables are processed measurement-derived normalized distributions,
not raw time tags or our own experiment. They have 81 ps bins relative to
recovery, measured with 850 nm pulsed illumination. Our optical model assumes
633 nm; these curves do not calibrate the proposed device at that wavelength.
Normalized delay shape does not determine afterpulse strength.

The detector study separately declares published scalar anchors and an assumed
stress strength. Its event queue models nonparalyzable recovery, surviving
afterpulse candidates and descendant afterpulses. Gates start live with no prior
traps. Twilight counts, unknown long tails, drift and cross-gate memory remain
excluded. Shared phase draws across cases/profiles prevent pooling their trials.
Zero observed errors do not prove zero true error.

The original [GPL-3.0 license](simulation-prototype/measured-data-review/data/spad/LICENSE.upstream.txt)
is retained beside the tables and their afterpulse-study copies. The project's
MIT grant does not replace those terms. No upstream executable source, article
PDF, viewer JavaScript, SLM figure archive or raw REA path log is included.
The retained acquisition notes refer to some omitted local materials. Numerical
SLM calibration data remain unavailable; the retrieved SLM archive held figures
only. REA supplied artifact-identity evidence, not a physics or security proof.

## Reproduce

From the repository root, using Python 3.11 or later:

```sh
python tools/optical_validation.py verify
python tools/optical_validation.py audit
```

Both commands need only the standard library. `verify` checks the 115-file
inventory, original nested manifests, detector tables and available cross-study
bindings. `audit` also reruns all four preserved verifiers, including exact
histogram scores, binomial limits, numerical enclosure bounds and deliberately
invalid certificate controls. It does not regenerate Monte Carlo draws.

With the [pinned Python-FLINT 0.9.0 environment](../../docs/reproduction.md):

```sh
python tools/optical_validation.py replay --output build/optical-validation
```

This stages the transfer certificate in a fresh directory, repeats the audits,
and regenerates the entire certificate byte for byte. It fetches and installs
nothing. `PHOTON_FLINT_RUNTIME` may select an existing target installation;
relative paths are resolved against the caller's working directory. Windows
Arb CI includes this replay. Packaged standard-library audits run on both CI
platforms. Current remote run outcomes must be checked separately.

The preserved original-workspace `--workspace-audit` flags require omitted
acquisition/development material and are not the public reproduction commands.
POPPY, NumPy, SciPy and Numba are optional for fresh simulation generation;
their recorded versions/requirements are in the archived study READMEs. They
are not required for the public audit or new Arb replay. The HTML reports in
the study folders can be opened locally after downloading the source capsule;
GitHub's file viewer displays their source.

## Next scientific gate

Obtain numerical per-cell complex transfer and SLM phase/amplitude calibration,
check detector response and exposure independence, then run a measured pilot
before a preregistered performance experiment. The [laboratory plan](simulation-prototype/robustness-study/LAB_PLAN.txt)
records the assumed acquisition rate and trial costs. No apparatus, measured
pilot, novel-physics result or external peer-review endorsement is claimed.
The [development specification](DEVELOPMENT-SPEC.md) records acceptance criteria
and remaining work. The repository's [AI-assistance disclosure](../../docs/research-disclosure.md)
applies; AI tools receive no Git authorship or contributor credit.
