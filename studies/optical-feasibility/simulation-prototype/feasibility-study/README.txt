BOUNDED OPTICAL FEASIBILITY STUDY — 2026-10-21

Decision

Do not invest in hardware to demonstrate the existing reference separation
protocol within the eight-hour acquisition budget assessed here. At 10 independent
snapshots per second, the budget is 288,000 snapshots. The retained probability
certificates imply that even the optimal classifier has equal-prior average error
at least 49.9934757992162% for the reference 13-bin observations.

This is a decision about one protocol. It does not rule out other gains, phase
variances, observables, unbinned counts, or experimental designs. Optical errors
can change the distributions, so the ideal bound is not automatically a bound
for every imperfect apparatus. Those changes can also produce confounding signals.

Proposed layout and budget

633 nm coherent laser -> polarization and beam shaping -> 63 illuminated phase
regions on an 8 x 8 grid (one blocked) -> Fourier lens -> selected single-mode
fibre projection -> attenuation -> photon counter with a 5 ms acquisition gate.

Each snapshot uses a newly randomized phase pattern. For structure G in {A,B},
the intended phase at site j is theta_G,j + Z_j, with independent Gaussian Z_j
of variance s = 2 log(2). The coordinate-derived theta values come from the
preserved input model. Intended count law: N | I ~ Poisson(eta*I + b), where
I = |sum_j exp(i(theta_G,j + Z_j))|^2, eta = 1/20, and reference b = 0.
Only bins 0,...,11,>=12 are retained for the certified discrimination result.

The planning schedule is a 5 ms gate plus 95 ms settling/guard, repeated at
10 Hz for eight hours per unknown structure, optimistically with no overhead.
Settled phases and independence are assumptions, not measured specifications.
Multiple gates of the same random phase pattern do not supply independent
snapshots from the marginal law used in this calculation.

The SLM product page [1] lists a 60 Hz input frame rate, 256 input levels, and
5 ms rise/25 ms fall times at the stated measurement conditions. These motivate
a slower planning rate, but do not guarantee the required accuracy at 10 Hz.

This would be an optical emulator of the prescribed phasor model. Programming
known masks and comparing their outputs does not establish imaging of unknown
materials, physical crystal equivalence, or experimental validity of the model.

Why the budget fails

Let P and Q be the certified reference 13-bin laws and rho = sum_k sqrt(P_k Q_k)
their affinity. The retained certificate gives

  1 - rho <= ell = 14779581898158231 / 500000000000000000000000000000.

For m independent snapshots, affinity is rho^m. The total variation inequality
and Bernoulli's inequality give

  TV(P^m,Q^m) <= sqrt(1-rho^(2m)) <= sqrt(2*m*ell).
  optimal equal-prior average error = (1-TV(P^m,Q^m))/2.

study.py computes an upper rational enclosure of the square root, then a lower
rational enclosure of the error. At m = 288,000 this gives exactly

  TV upper:    32621003919 / 250000000000000
  error lower: 249967378996081 / 500000000000000.

Consequently both classification errors cannot be below 5% within this budget.
The pre-existing, sharper reference certificate gives a necessary count of
28,091,647,285,174 snapshots; a separate certified test has sufficient count
102,399,876,723,169. These bracket a sample-complexity question; neither number
is asserted to be the exact optimum. They count independent snapshots, not
individual photons. The necessary count is about 97.5 million times this budget.

For perspective, applying the same bound to other assumed eight-hour rates gives:

  Assumed independent rate    Snapshots          Average error lower bound
  10 / second                 288,000            49.9934757992%
  60 / second                 1,728,000          49.9840190371%
  1,000 / second              28,800,000         49.9347579922%
  1,000,000 / second          28,800,000,000      47.9368665611%

The higher rates are hypothetical, not capabilities of the proposed SLM layout.
The new bound is an exact-arithmetic consequence of retained certificates. No
new Lean theorem or physical validation was performed in this study.

Optical model and imperfections

The optical calculation uses an ideal discrete unitary 8 x 8 Fourier mixer,
equal incident field amplitudes, and equal projection weights for the selected
output. Its selected output power is I/4096 times the reference input power;
total output power is 63/64. This is not a continuous diffraction calculation.
With assumed detector efficiency 0.5 and optical throughput 0.5, eta=0.05
corresponds to 819.2 effective incident photons per gate in this normalization.
Actual losses, laser attenuation, mode overlap and efficiency need measurement.

Numerical expectation calculations used the same fixed error profiles for both
structures, with sites assigned to the grid in stored order. Field amplitudes
were normalized to preserve total power. Results are mean count differences A-B:

  Ideal                                  0
  1% RMS field-amplitude gradient        -1.57094e-5
  1 mrad RMS static phase ripple        +1.56764e-6
  Uniform 256-level phase quantization  +3.55e-16 (roundoff; no resolved gap)
  Combined optical stress               +1.27596e-5

These are floating-point model predictions, not interval certificates or measured
device tolerances. They are not estimates of detection power at this budget.
The mean gaps show how unequal illumination or phase offsets can break low-order
matching. An apparent separation would then need controls to establish whether
it demonstrates the intended higher-order mechanism. Uniform quantization is an
ideal transfer curve; real phase calibration and pixel crosstalk are unmodeled.

Detector stresses

Illustrative values were informed by the accessible 2020 manufacturer datasheet
[2]: dark rate 25 counts/s, dead time 22 ns, and afterpulse probability 0.005.
These are planning values, not a current device quotation or per-unit guarantee.
The fibre mode selection above is a separate optical component; the datasheet's
stock FC adapter is not assumed to implement that single-mode projection.

The 5 ms gate converts the dark rate to b=0.125. The additive model then gives
each primary one independent Bernoulli afterpulse, without delay or cascading.
On the 13 bins this is a common stochastic channel with >=12 absorbing. Data
processing means that this particular noise channel cannot improve separation;
the ideal error lower bound remains valid for it. This argument does not cover
general detector memory, dead-time thinning, or optical perturbations.

Using midpoint probability diagnostics, the one-snapshot total variation is
2.13587e-7 ideally, 1.97985e-7 with dark counts, and 1.97460e-7 with both additive
effects. These are floating-point diagnostics, not new probability enclosures.

For baseline optics plus dark counts, a separate union bound for any within-gate
dead-time loss is E[lambda^2]*(d-d^2/2), with d=22 ns / 5 ms. Evaluated in floating
point it is 5.16894e-5 per gate. This assumes an initially live detector and a
conditionally homogeneous Poisson process, and excludes afterpulses. It is an
upper bound, not a measured loss rate or a resolved discrimination-risk change.

Finesse assessment

Finesse's official overview [3] describes frequency-domain interferometer
simulation, including paraxial higher-order spatial modes. It could help assess
linear transfer, mode overlap, alignment, and losses if a promising protocol
justifies a detailed optical model. It would still need explicit modeling of the
random phase patterns, SLM response, and discrete photon-counting electronics.

Finesse was assessed from documentation; it was not installed or executed. The
current study uses NumPy, SciPy and Matplotlib. A Qiskit circuit or PyTorch model
is not required for the present classical phasor/Poisson calculation. More complex
software alone would not change the certified reference information bound.

Reproduction and checks

Run from the workspace root with the existing evidence files preserved:

  python -m unittest discover -s simulation-prototype/feasibility-study -p test_study.py -v
  python simulation-prototype/feasibility-study/study.py --output simulation-prototype/feasibility-study/run-reproduction

The output directory must be new. Runtime: Python 3.11.9, NumPy 2.2.6, SciPy
1.16.3, Matplotlib 3.10.8. No additional packages were installed for this work.
The script checks the earlier simulator's SHA-256 and its three evidence inputs.
This directory relies on those retained workspace inputs; it is not standalone.

Eight tests passed: outward square-root enclosure; budget limits/monotonicity;
coherent Fourier normalization; an independent quantizer Fourier identity;
single-site invariance; an independent two-site second-moment identity;
detector limiting cases; and dark-count kernel/variation contraction.
Ruff lint and formatting checks passed.

Across 2,048 random optical states, direct phasor and Fourier output powers
agreed within 9.72e-17; total power within 6.67e-16; global-phase invariance
within 5.56e-17. The diagram was visually checked. These checks validate specific
identities and implementation behavior, not an entire apparatus.

The final retained outputs are run-checked/results.json and
run-checked/feasibility.png/.pdf. Earlier run-01 and run-final directories are
development outputs. MANIFEST.json pins the final source, tests and artifacts.
The public repository and the earlier simulation checkpoint remain unchanged.

What would justify further work

A separate, bounded parameter/observable study would need to demonstrate a
practical acquisition budget before detailed hardware design. Any candidate
would need fresh probability/risk calculations, controls for low-order leakage,
and then measured phase transfer, mode overlap, detector response and dependence.
This study supplies a stopping decision for the reference protocol; it does not
close physical validation, novelty, or unrelated formalization gaps.

Sources consulted (2026-10-21)

[1] Hamamatsu, X15213-01 product specifications, measurement conditions at 633 nm:
https://www.hamamatsu.com/us/en/product/optical-components/lcos-slm/wide_wavelength_bandwidth_type/X15213-01.html

[2] Excelitas, SPCM-AQRH datasheet, revision 2020-10, specification tables pp.2-3
and fibre coupling note p.4. Dated parameter reference, not a current price/spec quote:
https://prod.excelitas.com/sites/default/files/assets/product/document/24369.pdf

[3] Finesse official overview:
https://finesse.ifosim.org/
