Optical robustness: a bounded calibration study
==============================================

Open report/report.html. All graphs/data are embedded and work offline.

Decision: promising at eight selected tighter-calibration settings, conditional
on the simulator. Physical optical transfer and calibration must be measured
next. This is not a continuous tolerance certificate or hardware validation.

Findings
--------
The uncorrected fixed classifier is sensitive to collection alignment.
At x=-2.25/+2.25 um it misclassified A in 47/200 and 42/200 fresh trials.
At x=-2.5/+2.5 um these rose to 165/200 and 166/200. Each trial used 5,000
independent synthetic snapshots. No physical observations were obtained.

One correction rule subtracts the estimated optical-transfer phase per cell
BEFORE ideal uniform phase quantization. The original static amplitude mask,
photon scale, score and threshold remain fixed. Calibration is label-independent.

The initial combined calibration allowance (0.5 um residual per position axis,
5 nm residual in the quadratic OPD coefficient) failed: one corrected A error
rate was 110/200 = 55%. Those failures are retained, with all other outcomes.

A development-only screen selected a tighter residual budget of 0.25 um per
axis and 2 nm in that coefficient. At its eight selected adverse settings,
corrected A and B each had zero errors in 200 fresh trials per setting. All
16 error probabilities have Bonferroni one-sided 95% simultaneous upper limits
of approximately 2.843%, under this simulator. The uncorrected method failed
completely for one true label in each of those settings. Do not pool trials
across settings or turn zero observed errors into a claim of zero true error.

Screened actual values included x/y offsets +/-5 um, signed quadratic OPD
coefficients +/-30 nm, gain 0.98/1.02, phase variance 0.049/0.051 rad^2 and
background 0.10/0.15 per gate, simultaneously. The OPD coefficient is not RMS
wavefront error. Finite corners and selected stress tests do not establish
every point in the associated box. The identical-mask control behaved as
expected: 50% balanced error, reported outside the success gate.

Evidence and limits
-------------------
1,219 initial development settings and 1,024 tighter-budget corner settings
were screened using finite floating-point Gaussian moment recurrences.
Those development proxies omit phase quantization and detector dead time.
Two plans were then frozen before their respective validation trials; the
tighter selector never reads validation results. Distinct seeds are used.
There are 18 initial settings and eight tighter settings, both methods and
both true labels, 200 trials per label/setting/method and 5,000 snapshots per
trial. The 104 classification records are not 104 independent datasets:
phase draws are shared across settings/methods within a label and trial.

Validation includes 256-level phase quantization and exact renewal simulation
of a 22 ns nonparalyzable detector within 5 ms gates. It uses converged continuum
Gaussian overlap coefficients, separately checked against actual POPPY matrix
Fourier propagation in the existing isolated POPPY 1.2.0 environment.
Seven new tests check the 2D optical reduction, convergence, phasor moments,
phase compensation and quantization. The frozen baseline retains earlier tests.

The old REA package identity evidence is reused; no new decompilation is useful
for this source-level physics calculation. REA does not validate the optical
model. No calibration measurement or calibration estimator was simulated.
Static amplitude compensation, real phase response, pixel gaps/crosstalk,
polarization, afterpulsing, drift and temporal independence remain unvalidated.
The layout emulates known masks; it does not recover an unknown specimen.

The next gate is in LAB_PLAN.txt. Measure transfer/calibration first. A physical
performance confirmation is much slower than simulation: 72 error-free trials
per label at one setting/method would require 20 hours of acquisition at an
assumed 10 Hz, excluding calibration, for simultaneous 95% upper limits below
5%. The selected correction is not evidence that such an apparatus is feasible.

Verify and reproduce
--------------------
With ordinary Python (no scientific packages needed):
  python verify.py
This checks all manifest hashes, both frozen plans, 104 saved classifications,
two-sided intervals and 50 simultaneous upper bounds. It independently inverts
binomial probabilities using stdlib rather than scipy.stats.beta.

With the isolated Windows x86-64 Python 3.12 environment:
  python -m venv .venv
  .venv\Scripts\python -m pip install --require-hashes -r requirements-windows-py312.txt
  .venv\Scripts\python reproduce.py --output fresh-check --checks-only
  .venv\Scripts\python reproduce.py --output fresh-full-replay

The full replay copies sources into a fresh directory, runs checks, regenerates
both screens/plans and independently seeded trials, then exports the report.
No existing directory is overwritten; no package installation is performed by
the replay itself. Output bytes can vary with numerical-library/platform changes;
the supplied dependency lock records the wheels used for this checkpoint.
Other operating systems need their own reviewed dependency lock and checks.

Sources/results and all earlier proof/study artifacts remain preserved. This
checkpoint is local; the GitHub repository is unchanged. No new Lean proof,
Arb risk certificate, physical experiment or novelty assessment is claimed.
Project code is MIT licensed; dependencies retain their own terms. Development
used AI assistance under human direction; no external peer review is claimed.
