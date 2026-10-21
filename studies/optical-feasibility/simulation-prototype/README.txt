PHOTON EXPERIMENT FEASIBILITY PROTOTYPE

Purpose
-------
A bounded numerical experiment for the proved iid Gaussian-phase/Poisson model.
It helps inspect the measurement assumptions and the scale of detector effects.
It does not certify an apparatus, prove experimental feasibility, or add a new
formal theorem. The public scientific repository remains at its signed milestone.

Run from the parent workspace with Python 3.11 or later (no extra dependencies):

  python simulation-prototype/simulate.py --output simulation-prototype/my-run
  python simulation-prototype/validate_run.py simulation-prototype/my-run
  python -m unittest discover -s simulation-prototype -v

The output directory must be fresh and outside public-repo. The default is
100,000 independent snapshots per structure. The default seed is 20261021.
The three retained scientific JSON inputs are read-only and SHA256 checked.
The final recorded run is run-validated/report.txt and report.json, with
run-validated/validation.json. Earlier run-reference output predates formatting
and the additional observed-gap report column; use run-validated for current code.

What is simulated
-----------------
1. Reconstruct all 63 phases for A/B from exact integer/offset metadata.
   Floating-point phasors are separately compared with the archived exact
   number-field representation. The archived graph covariance is not used.
2. Draw independent Gaussian phases with variance s at each site and snapshot.
3. Compute I = |sum exp(i*(structural phase + random phase))|^2.
4. Draw N from Poisson(background + gain*I). Gain includes effective optical
   normalization/loss and detection efficiency; no physical values are supplied.
5. Place N arrivals uniformly in a unit gate, conditional on the same fixed rate.
   Apply a nonparalyzable dead time: only accepted events start a dead period.
   Each gate begins live. Cross-gate detector memory is excluded.
6. Keep the 13 count bins and the fixed reference score. The classifier has
   no access to hidden simulated phases, intensities or structure labels.

A/B random streams are independent. The ideal and dead-time observations are
paired within each structure, allowing direct estimation of lost counts.
This comparison is not evidence that A and B were experimentally distinguished.

The CLI exposes --variance, --gain, --background and --dead-time-fraction.
Changing these parameters invalidates applying the retained reference
sample/risk guarantees to the changed experiment. Reference guarantees concern
s=2*log(2), gain=1/20, background=0 and iid observations in the 13 fixed bins.
The validator deliberately accepts only that reference ideal run.

Findings from the recorded run
-----------------------------
100,000 snapshots per structure completed in about 13 seconds on this machine.
Both ideal count means agree with the analytic 2.3625 within sampling error.
All 26 ideal bin frequencies are within two predicted standard errors of the
certified probability midpoints. These are software diagnostics, not a formal
statistical certification or a successful separation experiment.

The largest certified bin-probability gap is about 1.15e-7. For that bin,
the standard error of an A-minus-B estimate from these two runs is about
0.00204: roughly 17,700 times the signal. A visible Monte Carlo difference
at this scale would usually be sampling noise, not the predicted effect.

Illustrative dead time of 0.01 gate lengths loses about 4.4% of ideal counts.
This parameter was chosen as a stress case, not taken from a detector datasheet.
The simulation does not resolve the much smaller change in classification risk.

At an ASSUMED one million independent snapshots/second, the retained necessary
and sufficient counts correspond to approximately 0.89 and 3.24 years. These
are simple conversions of existing certified bounds for the fixed binned
experiment. They are not hardware throughput estimates, a universal lower
bound, or a requirement on all alternative experimental designs. One million
detected photons/second does not imply one million independent snapshots/second.

Validation
----------
Eight tests check the phase reconstruction against a separate representation,
global-phase invariance, coherent intensity, Poisson mean/variance and fourth
factorial moment, the dead-time rule, its one-click Bernoulli limit, and a
single-site control whose intensity cannot fluctuate. Seeded stochastic checks
use conservative diagnostic tolerances. Lint passes. No new Lean proof or
physical measurement is claimed.

Which tools could help next?
---------------------------
PyTorch: batch Gaussian/Poisson sampling and parameter studies. No neural
network is needed; acceleration does not remove the small-signal problem.
https://docs.pytorch.org/docs/stable/distributions.html

Finesse: a candidate for a concrete interferometer layout, optical fields,
detector outputs and misalignment. This is a quasi-static optical simulation;
our count/time-response layer would still need explicit integration and tests.
https://finesse.ifosim.org/

Meep: Maxwell-equation propagation/scattering if a physical geometry or material
response must be modeled. It would need physical dimensions, wavelength,
materials, boundary conditions and numerical convergence checks. It is not an
automatic photon-counting validation of the present stochastic model.
https://meep.readthedocs.io/en/latest/

Qiskit Aer: quantum-circuit/noise simulation. Encoding these classical random
phasors in qubits is possible in principle but adds a modeling problem; no
benefit for this specific optical feasibility question has been established.
https://quantum.cloud.ibm.com/docs/en/guides/simulate-with-qiskit-aer

PyVISA or instrument-vendor software: control compatible actual measurement
hardware and record results. It supplies the connection, not the apparatus
or a detector calibration. No instrument was connected or controlled here.
https://pyvisa.readthedocs.io/en/latest/

Physical route and stopping criterion
------------------------------------
A candidate controlled demonstration would combine 63 equal-amplitude optical
contributions with programmed structural phases and independent Gaussian phase
updates, then record a selected output mode with a characterized counter.
Whether this can meet the required stability and acquisition conditions is
unknown. Loss normalization, finite acceptance, phase accuracy, unequal
amplitudes, gate integration and detector response need explicit models.
Such a demonstration would test that optical realization, not arbitrary
crystals, molecules or clinical imaging.

NIST documents the importance of dead time, background and afterpulsing in
photon-counter calibration:
https://www.nist.gov/publications/calibrating-photon-counting-detectors-high-accuracy-background-and-deadtime-issues-0

An earlier controlled two-source phase-statistics experiment is relevant
background, not validation of our 63-site construction or detector model:
Hong et al., Scientific Reports 6, 23614 (2016), DOI 10.1038/srep23614.
https://www.nature.com/articles/srep23614

Recommended next decision: specify one optical layout and a realistic budget
of independent snapshots and calibration uncertainty. Continue only if a
validated parameter/design study predicts detectable separation inside that
budget. A large brute-force Monte Carlo at the current reference point is
not a promising way to establish practical feasibility.
