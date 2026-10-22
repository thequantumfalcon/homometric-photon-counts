AFTERPULSING STRESS STUDY — 2026-10-21

Result: no observed classification failures in the frozen finite experiment.
Every one of 48 A/B error probabilities has 0 failures in 200 trials and a
one-sided Bonferroni 95% simultaneous upper limit of 0.03375192026711007.
This is a conditional simulation result, not a zero-error guarantee or physical
validation. Start with report/report.html; the figure also exports as PDF.

WHAT WAS FROZEN

Three optical cases: centered, and the worst corrected A and B cases selected
by the PREVIOUS tighter-budget development calculation. The selection did not
use any new classification outcomes. Corrected optical transfer, ideal static
amplitude compensation, 633 nm model, 256-level quantization, phase law, photon
scale, 5 ms gate, 5,000 gates/trial, score and threshold are unchanged.
The score is N(N-1)/3969 - 1.7N/63, with threshold -0.6401102.

Eight detector profiles: the prior 22 ns recovery-only baseline; three
published parameter anchors, each with a matching afterpulsing-off comparison;
and one assumed stronger afterpulsing stress case. Anchor settings are:
  CD3432H: recovery 29.1 ns, mean candidate offspring 0.0020
  CD3605H: recovery 24.1 ns, mean candidate offspring 0.0171
  Count20C: recovery 56.3 ns, mean candidate offspring 0.0035
The stress case uses the CD3605H shape and 24.1 ns recovery, with mean 0.05.
Mean offspring is NOT the probability of any afterpulse: a Poisson mean m
gives 1-exp(-m) probability of one or more candidates before recovery losses.

Measurement source: Straka, Grygar, Hlousek and Jezek (2020),
Counting Statistics of Actively Quenched SPADs Under Continuous Illumination.
https://doi.org/10.1109/JLT.2020.2994654
https://arxiv.org/abs/2001.10036
https://github.com/ivo-s/SPAD-counting-model/tree/4ed0903200b59b7f94715c38ca2668bb832e80d8
The three normalized delay histograms are processed measurement-derived
inputs. Recovery/offspring anchors come from the paper's low-rate examples;
the experiment used different wavelengths and acquisition conditions. In
particular, CD3605H showed a pulsed/continuous change in afterpulse strength.
These anchors do not recreate or certify those physical detectors in our setup.

DETECTOR MODEL

For each gate, hold the sampled optical intensity constant and generate a
homogeneous primary Poisson process including background. Start live at t=0,
with no past detections or trapped carriers. An accepted avalanche causes a
nonparalyzable recovery interval tau. Events within that interval are rejected,
do not extend it and do not generate daughters.

Each accepted avalanche independently proposes K~Poisson(m) daughter events.
A daughter's time is parent time + tau + (histogram bin index + U)*81 ps,
where U is uniform on [0,1). Thus data provide bin probabilities; uniform
within-bin timing is an explicit modeling assumption. A chronological queue
retains older proposed daughters across intervening detections. Accepted
daughters can generate their own daughters. Daughters inside another recovery
interval or outside the gate are excluded. No rescaling to hide added counts.

This is an own implementation of a branching event model motivated by the
paper, not execution of the downloaded research code. All means are below one.
An event-count guard aborts on overflow instead of silently truncating.
Twilight pulses are set to zero. The stored histogram ends near 2 microseconds;
an unknown tail is not reconstructed. Gates have no carry-in memory, no
intergate illumination history and no detector drift. Stationarity/independence
and these omitted effects still need actual apparatus measurements.

NUMERICAL AND STATISTICAL CHECKS

Seven tests passed: zero/invalid inputs, Poisson limit, exact initially-live
recovery count law, compound-Poisson branching limit, a separately implemented
conditional-Poisson/uniform-timestamp sampler, exclusion outside the gate and
identical seeded results under serial versus four-thread scheduling.

For the recovery-only analytic check,
  P(N >= n) = GammaCDF(rate * (1-(n-1)*tau); shape=n)
in normalized gate units, zero when the available time is nonpositive.
For zero recovery/delay and offspring mean m, branching clusters have PGF
T(z)=z*exp(m*(T(z)-1)); Poisson primaries of mean lambda give
exp(lambda*(T(z)-1)). Coefficient extraction yields P(0)=exp(-lambda) and
P(n)=lambda*(lambda+m*n)^(n-1)*exp(-lambda-m*n)/n! for n>=1.
These analytic distributions and a separate timestamp sampler test the engine
without relying only on tests that duplicate its implementation.

The optical inputs were exported by the previously checked quadrature code.
Stored witness rates from that environment agree with this runtime within
2e-11 for every case/label. plan.json precedes classification generation.
run/execution-plan.json binds all executed source files. No adaptive rerun,
threshold change, discarded trial or changed photon scale was used.

There are 200 trials per label/case/profile, each with 5,000 independent fresh
gate histories: 48 million simulated gates, not laboratory exposures. Trials
are independent within each error-rate estimate. Cases/profiles share phase
draws, so their outcomes are dependent and must not be pooled. Bonferroni
coverage does not require independence among the 48 estimates.

The standard-library verifier reconstructs every trial score from its retained
integer count histogram, uses an exact rational threshold comparison, and
independently inverts the binomial CDF to check all 48 upper bounds. It also
checks afterpulse bookkeeping and source/data bindings. Its workspace audit
checked preservation of 120 files from earlier studies and data acquisition.
Monte Carlo confidence statements remain conditional on the specified model
and pseudorandom simulation; they are not Lean proofs or Arb certificates.

RUNNING AND LICENSING

The existing runtime was used without installing packages:
Python 3.11.9, NumPy 2.2.6, SciPy 1.16.3, Numba 0.61.2, llvmlite 0.44.0.
Optical export used the earlier isolated NumPy 2.5.4/POPPY 1.2.0 environment.
Numba compiles our own detector code; its legacy NumPy RNG is seeded inside
each compiled call. All 9,600 detector-call seeds were checked for collisions.
Four worker threads passed the explicit serial/parallel reproducibility check.

From this folder:
  python test_detector.py
  python verify.py
  python make_report.py
In the original workspace, python verify.py --workspace-audit additionally
requires and checks prior sibling studies and source files. The default check
works on the standalone packet and does not claim to recheck absent siblings.
To reproduce the full Monte Carlo run, copy this folder to a fresh directory
omitting run/ and MANIFEST.json, then run python run_study.py --workers 4.
The runner refuses to overwrite retained outcomes. Set OPENBLAS_NUM_THREADS=1
and OMP_NUM_THREADS=1 to avoid unnecessary nested numerical threading.

Project-owned source uses the supplied MIT license. The external SPAD tables
retain the upstream GPL-3.0 license at data/LICENSE.upstream.txt and their
attribution above; no MIT grant is asserted for them. Archived REA bindings
are retained at data/archive-bindings.json. REA established package identity,
not detector-model correctness. This checkpoint is local and was not pushed.

INTERPRETATION AND NEXT GATE

Afterpulsing at these tested shapes/strengths did not defeat the fixed decision
rule. This removes one particular concern from the current simulation tests.
It does not certify all eight previously tested optical corners, intermediate
settings, arbitrary detectors, the original fourth-order-only experiment or
unknown-specimen imaging. The more immediate unresolved physical gate remains
measured optical transfer, feasible amplitude compensation and phase-response
calibration. The prior laboratory plan still applies; its acquisition rate and
calibration precision remain assumptions until measured.
