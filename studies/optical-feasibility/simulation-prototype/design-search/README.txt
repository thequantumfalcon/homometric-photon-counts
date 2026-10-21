CHANGED-FREQUENCY OPTICAL CANDIDATE — 2026-10-21

Outcome

A bounded design search found a substantially easier mathematical experiment.
For the same two 63-site geometries, changing the encoded spatial frequency,
phase variance and gain exposes a second-intensity-moment difference. A fixed
statistic of unbinned photon counts distinguishes the two specified hypotheses
with certified conditional error bounds below 5% using 5,000 iid snapshots.

The most detailed scenario checked here includes ideal uniform 256-level phase
quantization, known Poisson dark counts and initially-live nonparalyzable dead
time. Its error upper bounds are 1.503% for A and 2.630% for B (rounded outward).
At the earlier assumed 10 Hz rate, acquisition alone takes 8 minutes 20 seconds.
This is a candidate for optical design/calibration review, not a tested apparatus
or a hardware purchase recommendation.

What changed

                          Earlier reference          New candidate
Encoded wave number q     pi/3                       201*pi/200
Site phase variance s     2*log(2)                    1/20 rad^2
Gain eta                  1/20                       1
Observation               13 count bins              Unbinned count N
Distinguishing mechanism  Fourth intensity moment     Second intensity moment

The original 13-bin lower bound remains valid for its original experiment.
The new result neither contradicts it nor supplies an easier demonstration of
the original fourth-order-only effect. No novelty claim is made.

For a phase-modulator emulator, q changes the programmed phases q*x_j using the
same exact coordinate metadata. The physical 633 nm laser need not change. This
is not automatically an angular scan of the previously sketched 8 x 8 grid,
whose physical macrocell positions differ from the abstract coordinates x_j.
The random phase variance remains independently programmed; changing q while
holding actual mechanical displacement fixed would be a different model.

The ideal mean counts are equal, about 47.57965 per gate. The second intensity
moments differ by approximately 118.44645 (B minus A). Mean count separation is
not the mechanism. At 5,000 snapshots the ideal expected total is about 238,000
photons, illustrating why photons and independent snapshots must be distinguished.

Fixed decision rule

For each snapshot, compute

  Y(N) = N*(N-1)/3969 - (17/10)*N/63.

Average Y over 5,000 snapshots. Choose A below the relevant threshold, otherwise
choose B. The gain, phase law and noise scenario must be known as specified.
These are fixed thresholds, not estimates fitted to the test data.

Scenario                         Threshold      Error A upper   Error B upper
Ideal                            -0.63980718     1.004%          1.952%
Known dark counts                -0.64017930     1.003%          1.954%
Dark + toy afterpulses            -0.64000838     1.003%          1.960%
Dark + dead time                  -0.64017930     1.503%          2.630%
256 levels + dark                -0.64011020     1.003%          1.954%
256 levels + dark + dead time     -0.64011020     1.503%          2.630%

The displayed percentages are rounded upward. Exact rational bounds and
thresholds are in interval-final/certificate.json. Each error is bounded under
its own hypothesis; no equal-prior assumption is needed for these upper bounds.

Noise assumptions

Dark counts: independent Poisson background b=1/8 per 5 ms gate (25 counts/s).
Afterpulsing: one independent Bernoulli child per primary with probability 1/200;
no delays, cascades or detector recovery interaction. This is a toy count model.
Dead time: 22 ns, homogeneous conditional Poisson primaries within a 5 ms gate,
initially live detector, independent snapshots and no cross-gate memory.
Quantization: nearest of 256 exactly uniform optical phase levels, applied after
adding the Gaussian phase. An 8-bit control input does not guarantee that transfer
curve; it must be calibrated. The afterpulse and dead-time certificates are
separate; no combined afterpulse/dead-time guarantee is supplied.

Evidence and limits

The floating-point search evaluated 12,990 nondegenerate settings/scores over a
finite q/s/gain grid. It also examined 48 fourth-order scores at q=pi/3. The best
of those original-frequency sufficient bounds was about 37.5 billion snapshots,
even with ideal intensity observation. A large sufficient bound is not a lower
bound and does not exclude better tests. No global optimization was attempted.

The selected candidate was checked with an independent raw mixed-moment
recurrence using python-flint/Arb at 256-bit precision. Directed interval
endpoints feed exact rational Cantelli calculations. METHOD.txt derives the
recurrence, decision bound, quantization tail bound and dead-time perturbation
bounds. This is a conditional analytic/computational certificate, not a new
Lean theorem or proof of physical fidelity. Existing formal sources are intact.

Twelve tests passed, including exhaustive small-system moment expansion, the
previous exact fourth-gap identity, independent quantizer cell integration and
pathwise dead-time inequalities. Lint and format checks passed.

A held-out simulation used 200 independent trials per structure per non-dead-time
scenario, with 5,000 snapshots per trial. All four simulated scenarios had zero
misclassifications, and all mean diagnostics were within 2.12 standard errors of
the prediction. Scenarios share phase samples within each structure; their
results must not be pooled as fully independent trials. Dead-time bounds were
not simulated. Zero observed errors does not establish zero true error; the
mathematical certificate supplies the finite guarantees above.

What remains before hardware

The scalar optical transfer and equal field amplitudes remain assumptions.
Actual phase-level calibration, field uniformity, fibre projection, settled
pattern independence, gain/background uncertainty, phase drift and a combined
detector-memory model have not been validated. No numerical tolerance for those
unknown errors is claimed. Setup, calibration and independent controls are not
included in the acquisition duration. Known programmed masks do not demonstrate
recovery of unknown materials, and this experiment would not establish general
imaging performance or historical novelty.

The useful next gate is an optical/calibration review of this specific candidate:
can a proposed apparatus implement its prescribed phase distribution and scalar
projection, and can measured deviations be propagated into the score bounds?
Finesse could help with transfer and mode overlap. It has not been run here.

Reproduction

From the workspace root, with the retained input and existing local runtimes:

  python -m unittest discover -s simulation-prototype/design-search -p test_design.py -v
  python simulation-prototype/design-search/search.py --output simulation-prototype/design-search/new-scan
  python simulation-prototype/design-search/certify.py --output simulation-prototype/design-search/new-certificate
  python simulation-prototype/design-search/simulate_candidate.py --certificate simulation-prototype/design-search/new-certificate/certificate.json --output simulation-prototype/design-search/new-simulation

Output directories must be fresh. Runtime: Python 3.11.9, NumPy 2.2.6,
SciPy 1.16.3 for tests, Matplotlib 3.10.8 for plots, python-flint 0.9.0 from
tool-runtime/python-flint-0.9.0. No dependencies were installed. The sources
and input bindings are pinned by MANIFEST.json; this folder relies on retained
workspace inputs and is not a standalone distribution.

Final artifacts: scan-01/search.json, interval-final/certificate.json,
heldout-final/simulation.json, figures-final/candidate.png and figures-final/candidate.pdf.
Earlier interval/heldout directories are developmental checkpoints. The earlier
feasibility reports and public repository remain unchanged.

References

Arb real/complex ball arithmetic, official python-flint documentation:
https://python-flint.readthedocs.io/en/latest/arb.html
https://python-flint.readthedocs.io/en/latest/acb.html

Optical planning and dated detector-specification sources are recorded in
../feasibility-study/README.txt. They motivate illustrative values, not device
validation. Finesse overview: https://finesse.ifosim.org/
