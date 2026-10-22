Virtual optical bench: POPPY prototype
====================================

Open run-demo/demo.html in a browser. It is self-contained, runs offline, and
lets you inspect nine precomputed experiments. Results are synthetic. This is
a phase-mask emulator of the changed-frequency design, not physical validation
and not an image reconstruction of an unknown structure.

Engine and scope
---------------
POPPY 1.2.0 supplies the forward and adjoint matrix Fourier propagation.
The optical model is a monochromatic, scalar Fraunhofer system: a pupil mask
relayed to an ideal focusing lens, followed by Gaussian single-mode collection.
An independently coded continuum Gaussian-overlap integral checks the result.
Grid refinement and an independent NumPy transform check numerical consistency.

Layout (illustrative design parameters, not measured component specifications):
  wavelength                 633 nm
  ideal lens focal length    100 mm
  pupil cells                8 x 8, 200 um square, 63 active and one blocked
  illumination               Gaussian, 1/e field radius 3 mm
  collected Gaussian mode    1/e field radius 10 um at focus
  focal integration window   160 um square, 256 x 256 samples
  pupil integration grid     256 x 256; checks also use 64, 128 and 512
  phase commands             q=201*pi/200 times saved symbolic coordinates
  independent phase noise    Gaussian variance 0.05 rad^2 per cell per snapshot
  phase quantization         nearest of 256 ideal uniform optical levels
  gate and background        5 ms, 0.125 Poisson background counts per gate
  detector dead time         22 ns, nonparalyzable and initially live each gate

The positions of the optical cells form a regular grid. The two research
coordinate sets determine their programmed phases; their real-space atomic
positions are not physically reproduced by this model.

An ideal static amplitude mask equalizes the nominal centered collection
coefficients. Its transmission is computed once from the assumed model and
held fixed for every trial and perturbation. This additional amplitude mask
is a design requirement, not an established capability of a phase-only SLM.
The simulator does not establish how an actual modulator/relay would realize it.
The overall photon scale is also fixed after that nominal model calibration.
No classifier threshold or calibration is fitted to the synthetic trial results.

What can be learned
-------------------
Compare the centered case, x displacements +0.5, +1, +2, +5 and -5 um,
quadratic phase coefficients +30 and -30 nm, and an identical-mask control.
The quadratic screen is exp(+2*pi*i*W/lambda) with
W = coefficient * (x^2+y^2)/(0.8 mm)^2. The coefficient is not RMS wavefront
error; W approaches twice the coefficient at the square's corners.

Each case has 100 independent trials per structure, each with 5,000 snapshots.
The score is N*(N-1)/3969-(17/10)*N/63; choose A below -0.6401102, B otherwise.
The negative control programs A for both labels; a valid discriminator should
not separate those identical distributions. Its near-50% balanced error is
therefore the expected control behavior, not a successful A/B experiment.

Each displayed 95% Clopper-Pearson interval quantifies binomial sampling
uncertainty for one scenario and hypothesis under this simulator. They are not
simultaneous intervals over the whole sweep, physical guarantees, or Arb
certificates. Scenarios share phase draws within each trial and must not be
pooled as independent observations. Static focal images omit phase fluctuations
for legibility; the trial data include them.

Missing physics and measurements
--------------------------------
No afterpulsing, polarization, actual phase/amplitude transfer, pixel gaps,
crosstalk, relay aberrations, lens dispersion, temporal drift or correlated
snapshots are included. The nominal amplitude mask is assumed perfect. A
Gaussian variance alone does not validate the full phase distribution.
The source is monochromatic and phase-stable during each gate. No instrument
has been operated and no empirical data are included. Passing these checks
does not prove practical feasibility, novelty or the correctness of all optics.

Reproduce
---------
Run `python verify.py` with standard Python to check the artifact hashes and
saved classifications without installing the scientific dependencies.

Use Python 3.12 on Windows x86-64 with an isolated environment. The hash-locked
requirements file identifies the exact wheels used here. For example:

  python -m venv .venv
  .venv\Scripts\python -m pip install --require-hashes -r requirements-windows-py312.txt
  .venv\Scripts\python -m unittest discover -p test_bench.py -v
  .venv\Scripts\python bench.py --output fresh-run

The last command never overwrites an existing output directory. It performs
numerical checks, runs all trials, and produces JSON, PNG/PDF figures and a
self-contained HTML viewer. It installs nothing. The saved results and earlier
research artifacts remain unchanged. Other platforms require their own reviewed
dependency hashes and execution records.

To render saved trials without generating new Monte Carlo results:
  .venv\Scripts\python render.py --input run-demo/results.json --output fresh-view
The renderer checks the bench source and geometry binding, and copies the
results byte-for-byte. See FINDINGS.txt for this checkpoint's measured-in-the-
simulator results. MANIFEST.json binds the distributed files; hashes identify
bytes, not scientific correctness.

REA's actual contribution
-------------------------
The existing local REA 6.7.0 CLI inspected a byte-identical ZIP carrier of the
downloaded POPPY wheel. Its complete 53-member inventory was reconciled against
the original wheel; all 52 RECORD hashes and 45 installed Python source files
were checked. The POPPY digest also matched the checksum on its PyPI release
page. All 18 dependency wheels are hash-pinned. See package-audit/assessment.json
and package-audit/wheels.json. REA did not run the diffraction calculation,
prove software correctness, audit every dependency or establish physical truth.

Development used AI assistance under human direction. No external peer review
is claimed. Project-owned demo code is covered by the accompanying MIT license;
third-party packages retain their own terms and are not bundled in this demo.

Sources checked 2026-10-21
--------------------------
POPPY capabilities and limitations:
https://poppy-optics.readthedocs.io/en/latest/
POPPY 1.2.0 release and wheel identity:
https://pypi.org/project/poppy/1.2.0/
LightPipes, another scalar wave-optics option (not executed):
https://opticspy.github.io/lightpipes/manual.html
Finesse, frequency-domain interferometer modeling (not executed):
https://finesse.ifosim.org/

The preserved original proof and calibration study remain at:
https://github.com/thequantumfalcon/homometric-photon-counts
