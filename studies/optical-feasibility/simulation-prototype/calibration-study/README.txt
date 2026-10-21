CONTINUOUS CALIBRATION TOLERANCE STUDY — 2026-10-21

Result

The changed-frequency candidate does not require exact knowledge of its gain,
background or Gaussian phase-variance parameter. A single fixed count statistic
and decision threshold retain an error guarantee across a nonzero simultaneous
range of all three parameters.

Parameter                  Nominal       Certified range at 5,000 snapshots
Gain eta                   1             0.98 to 1.02
Gaussian command variance  0.05 rad^2    0.049 to 0.051 rad^2
Background per 5 ms gate    0.125         0.10 to 0.15

Across this entire continuous box, each classification error is below 4.53%:
the outward-rounded bounds are 2.222% for A and 4.525% for B. The certificate
includes ideal uniform 256-level phase quantization and initially-live
nonparalyzable dead time anywhere from zero to 22 ns. It assumes iid snapshots
with unknown but fixed parameters inside the stated box. No threshold refitting
or knowledge of the actual parameter values within the box is required.

The Gaussian variance is the variance before quantizing the commanded phase,
not the variance of the resulting wrapped, quantized optical phase. A +/-2%
variance tolerance corresponds to approximately +/-1% in its standard deviation.
The background range corresponds to 20–30 counts/s for the 5 ms gate.

Tradeoff with acquisition budget

Gain tolerance    Variance tolerance   Background/gate   Sufficient snapshots
Exact nominal     Exact nominal        0.125             2,566
+/-0.5%           +/-0.5%               0.11875–0.13125    2,896
+/-1%             +/-1%                 0.1125–0.1375      3,308
+/-2%             +/-2%                 0.10–0.15          4,502
+/-4%             +/-4%                 0.075–0.175        10,769

These are conservative sufficient counts for this fixed statistic, not optimal
sample requirements. Practical round numbers are 5,000 snapshots for the 2%
box and 11,000 for the 4% box. At the assumed 10 independent patterns/second,
these take 8 min 20 s and 18 min 20 s respectively, excluding calibration,
setup, rejected acquisitions and controls. Actual independent throughput is
not established. The earlier eight-hour budget can accommodate either nominal
acquisition duration if its physical assumptions can be realized.

A tested 8% box was not certified with this fixed threshold. This means the
calculated mean enclosures did not supply the required separation; it is not
proof of physical impossibility or optimality of the bound.

Fixed protocol

Keep q=201*pi/200 and the same two exact 63-site coordinate lists. Retain the
full count N from each acquisition. Compute

  Y(N) = N*(N-1)/3969 - (17/10)*N/63.

Choose A if the sample mean is below -0.6401102, otherwise choose B. The score
normalization remains fixed even when the actual gain is unknown. Substituting
an estimated gain into this formula would define a different procedure and
would not be the rule certified here.

What was proved computationally

calibrate.py constructs the intensity moments as ball-coefficient polynomials
in t=exp(-s/2), retaining a uniform bound on the quantization Fourier tail.
It constructs score mean and variance polynomials in gain, background and t,
shifts them about the nominal parameters before interval evaluation, and
encloses their values over the entire box. The shift preserves the polynomial
identities while avoiding unnecessarily loose bounds from cancellation.

Dead-time perturbation bounds from the previous derivation are evaluated over
the same box. Exact rational Cantelli calculations then give the per-hypothesis
error and sufficient sample bounds. This covers the continuum of parameters,
not just tested endpoints. METHOD.txt gives the argument and scope.

This is an analytic argument supported by Arb enclosures and exact rational
checks, not a new Lean theorem or external peer review. The explicit Gaussian
phase law is assumed; merely observing a variance in this range does not prove
that law or site independence.

Validation

Ten tests passed. They cover single-site invariance, the moment degree bound,
polynomial translation, independent point recurrences, fixed score normalization
at a changed gain, count-moment variance identities, containment of all eight
box corners under both structures, an independent fixed-threshold risk example,
invalid boxes and integer interval powers across zero. The corner tests check
implementation behavior; the interval derivation supplies continuous coverage.

During development, generic real powers in the installed Arb wrapper returned
undefined intervals when a centered interval crossed zero. Integer powers are
now evaluated by repeated interval multiplication, with a regression test.
No nonfinite result was accepted as a certificate. Ruff lint/format checks pass.

No new Monte Carlo trial was needed to establish this interval guarantee. The
earlier candidate simulations remain supplementary checks of their specified
point models; they are not relabeled as empirical calibration evidence.

Remaining physical requirements

Exact encoded spatial frequency, equal field amplitudes and the intended output
projection are still assumed. Arbitrary static phase errors, nonuniform phase
levels, field imbalance, spatial crosstalk, detector afterpulsing, gain-dependent
detector memory and temporal dependence are not covered. Afterpulsing is not
included jointly with dead time. The tolerances above are target conditions,
not confidence intervals inferred from measured calibration data.

The next useful step is to determine whether a concrete optical transfer model
and measured calibration can meet these conditions, particularly field and
phase-level uniformity. This result supports that review; it does not authorize
a claim of laboratory validation or justify a hardware purchase on its own.
The original fourth-order-only result is unchanged: this remains the different
second-order candidate documented in ../design-search/README.txt.

Reproduction

From the workspace root with the previous local study and runtime retained:

  python simulation-prototype/calibration-study/calibrate.py --output simulation-prototype/calibration-study/new-run
  python -m unittest discover -s simulation-prototype/calibration-study -p test_calibration.py -v

Use a fresh output directory. Python 3.11.9 and existing python-flint 0.9.0
at 256-bit precision were used. No packages were installed. The previous
evaluator, previous certificate and geometry input are SHA256 checked.
Final output: run-checked/calibration.json. The earlier run-01 output is a
development checkpoint. MANIFEST.json pins the current sources and artifacts.
Prior study artifacts and the public checkout remain unchanged.

Arithmetic documentation:
https://python-flint.readthedocs.io/en/latest/acb_poly.html
https://python-flint.readthedocs.io/en/latest/arb_poly.html
