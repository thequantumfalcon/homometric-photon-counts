# Homometric photon counts

[![Main branch CI](https://github.com/thequantumfalcon/homometric-photon-counts/actions/workflows/ci.yml/badge.svg?branch=main&event=push)](https://github.com/thequantumfalcon/homometric-photon-counts/actions/workflows/ci.yml?query=branch%3Amain)

Proofs and reproducible certificates for distinguishing two fixed 63-site homometric structures under independent Gaussian phase motion and conditional Poisson photon counting.

This is conditional mathematical research. The repository includes processed detector data from an external published study. It contains no measurements of the proposed apparatus, does not establish novelty, and makes no practical acquisition recommendation. Its exact assumptions and remaining gaps are part of the results.

## Construction and result

Let $\theta=\arcsin(1/(5\sqrt3))$, $\phi=-\arcsin(1/(8\sqrt3))$, and let $\epsilon_0=\epsilon_1=0$, $\epsilon_j=(-1)^j\phi$ for $2\le j<10$. Define the 21-site motif

$$C=\{30\}\cup\{3j+1+3(-1)^j\theta/\pi:0\le j<10\}\cup\{3j+3\epsilon_j/\pi:0\le j<10\}.$$

The two sets are $A=C+\{0,31,63\}$ and $B=C+\{0,32,63\}$, where set addition means all pairwise sums. Each has 63 distinct real sites; their directed pair differences agree with multiplicities, although no translation or reflection maps one set onto the other. Use spatial angular frequency $q=\pi/3$ and phasors $z_{G,j}=e^{iqx_{G,j}}$ for positions $x_{G,j}$ in $G=A,B$.

With independent Gaussian site phases of variance $s>0$, write $t=e^{-s/2}$ and $D_k(t)=\mathbb E[I_A^k]-\mathbb E[I_B^k]$ for the intensity moments defined below. Then $D_1=D_2=D_3=0$ and

$$D_4(t)=\frac{455015761}{20000}t^8(1-t^2)^5(t^6+3t^4+6t^2+6)>0\qquad(0<t<1).$$

The mechanism is that the clean amplitude $M_{G,1}$ vanishes, while homometry gives equal magnitudes of the harmonic sums $M_{G,r}=\sum_j z_{G,j}^r$. The first three intensity moments depend only on shared quantities; order four introduces the unequal invariant $\operatorname{Re}(M_{G,4}\overline{M_{G,2}}^{\,2})$. The [coordinate construction](formal/COORDINATES.md), [moment derivation](evidence/homometric-photon-counts/science_completion/homogeneous_control/homogeneous_control_proof.txt), and [formal certificates](formal/CERTIFICATES.md) give the details.

The [original 18-page report](docs/report/historical/science_completion_report.pdf) and its [complete LaTeX sources](docs/report/README.md) are included. Recovered files match the historical archive hashes. The report gives the foundational derivations; its 20 October scope predates the later four-root certificates, fixed-bin sample bounds, completed concrete formal proof and optical supplements described below.

## Explore the result

The [interactive demo](demo/index.html) follows the geometry, identical clean diffraction, fourth-moment separation and four certified blind gains. Download the repository and open `demo/index.html`, or follow the [local preview instructions](demo/README.md). The controls evaluate source-bound formulas and expose the exact certificate endpoints; the demo itself is an explanation, not a proof.

The default view is 2D because the structures are one-dimensional. Optional 3D inspection shows their positions and complex phase vectors, with manual orbit, zoom and a seeded Gaussian snapshot. Display rows and phase-vector directions are illustrative, not a physical apparatus. All browser assets are included locally. See the [numerical and browser validation guide](docs/demo-testing.md) for reproducible checks.

![Interactive fourth-moment plot with phase variance and photon gain controls.](docs/validation/demo_20261022/desktop-noise.png)

## Reproduce the basic checks

With Python 3.11 or later, run from this directory:

```sh
python tools/project.py verify
python tools/project.py test --output build/first-check
```

These commands use the standard library, run offline, and preserve the evidence. `verify` checks bytes and input bindings. `test` reruns exact endpoint constants, a necessary sample bound, an independently coded sample exclusion, and the exact phasor reconstruction. Neither command proves every analytic step.

For the longer Arb reconstruction, follow the [reproduction guide](docs/reproduction.md). The [reviewer guide](docs/reviewer-guide.md) provides a short route through the proofs.

A [fresh Ubuntu Linux run](docs/validation/linux_replay_20261022.json) passed the full numerical and optical replays as well as the core and packaged-source checks. The reproduction guide includes separate hash-locked Windows and Linux dependencies.

## Results and their scope

Write $t=\exp(-s/2)$, where $s>0$ is the phase variance. For fixed unit phasors $z_{G,j}$, independent standard normal variables $Z_j$, gain $\eta>0$, and common background $b\geq0$,

$$I_G=\left|\sum_{j=1}^{63}z_{G,j}e^{i\sqrt{s}Z_j}\right|^2,\qquad N\mid I_G\sim\mathrm{Poisson}(b+\eta I_G).$$

A **blind gain** is a positive gain $\eta$ at which the single event $N=4$ has equal probability under the two structures. It does not mean that the full count laws are equal.

| Result | Precise scope |
| --- | --- |
| Exact noncongruent homometric sets | Lean proves that the saved symbolic coordinates define two sets of 63 distinct real positions, with the same 3,969 directed pair differences including multiplicities, and excludes every translation and reflection between them. See the [geometric theorem](formal/HOMOMETRY.md). |
| Full count laws differ | The first three intensity moments match; the fourth differs positively for every $0<t<1$. The fourth factorial-count moment gap is $\eta^4D_4(t)$ under the stated detector model. |
| Exactly four positive blind gains | At $t=1/2$ and $b=0$, the event $N=4$ has equal probability under the two structures at exactly four simple positive gains. The final root lies in $(0.2934841,0.2934842)$. The proof includes every arbitrarily large gain. |
| Four roots persist on an explicit rectangle | Exactly four simple roots persist for $\lvert t-1/2\rvert\le10^{-23}$ and $0\le b\le10^{-20}$. The [analytic proof and exact rational budget](docs/root-stability.md) cover every positive gain. These conservative radii do not establish practical experimental tolerance; this result is not Lean-formalized. |
| Necessary and sufficient counts | At $s=2\log2,\eta=1/20,b=0$, with iid observations of the fixed bins $0,\ldots,11,\geq12$, any test with each error below 5% needs at least **28,091,647,285,174** observations. A certified score succeeds with **102,399,876,723,169**. The ratio is below 3.646; the optimum is unknown. |
| Formal count-law distinction | Lean proves the concrete first-three-moment matches, fourth-gap identity, and inequality of the two constructed count laws for every positive variance and gain and every common nonnegative background. The proof connects the explicit 63-site phase lists, Gaussian integrals and Poisson mixtures without assuming the concrete moment values. See the [certificate scope](formal/CERTIFICATES.md) and [executed checks](docs/validation/README.md). |

The sample counts require tens of trillions of independent observations for this fixed reference experiment; they do not establish a practical acquisition plan. The lower bound applies to the specified gain, variance, background and 13-bin iid observation, not to all measurements at this frequency. Arbitrary detectors, temporal dependence, unknown calibration and optimized designs need separate analysis.

![Inverse-gain illustration showing one remaining root above gain 1/6 and the 24 certified derivative intervals.](docs/assets/compact_gain_certified.png)

The curve is illustrative numerical quadrature. The endpoint signs and interval coverage come from the separately linked certificate; the first three roots are outside this plot's gain range.

The [claim ledger](docs/claims.md) links each result to its actual proof, certificate, replay, and remaining assumptions. The [model guide](docs/model.md) separates this homogeneous phase model from the archived historical extensions.

A [fresh Lean 4.35.0 source rebuild](docs/validation/formal_replay_20261022.json) passed **all 61 modules and 722 theorem-axiom audits** on Windows. Every project module was compiled anew with pinned dependencies; no theorem changes were needed. The [spatial separation theorem](formal/HOMOMETRY.md) connects exact coordinates, homometry and noncongruence to count-law distinction. The [validation record](docs/validation/README.md) distinguishes this compilation from historical Lean/Nanoda checks and the optional fresh reindexing timeout. Root-count and testing arguments are not fully formalized in Lean. The [verification-tool status](docs/verification-tools.md) records the scope of each checker.

The [Gaussian formalization](formal/GAUSSIAN.md) derives the general expectation formula and proves a site-by-site moment recurrence for any finite complex geometry. [Checked exact certificates](formal/CERTIFICATES.md) evaluate that recurrence for this particular pair. The separating conclusion is specific to these two structures. The [joint snapshot model](formal/JOINT_MODEL.md) now proves the stated conditional Poisson law on one probability space. A separate [model-error bound](docs/model-tolerance.md) quantifies a conservative tolerance for the fixed-bin test; it does not demonstrate physical feasibility.

## Bounded optical feasibility study

A separate [optical feasibility extension](studies/optical-feasibility/README.md) preserves the original results and explores a different measurement frequency with unbinned counts. Under its explicit iid Gaussian, ideal phase-quantization and detector assumptions, a fixed score and threshold have each error below **4.53% at 5,000 independent snapshots**, uniformly over specified simultaneous gain, background and phase-variance uncertainty. A wider box needs 11,000 snapshots for each error below 4.90%. Arb certificates, exact risk checks, simulation and reproducible sources are included.

This candidate uses a **second-order signal at a different frequency**. It does not demonstrate the original fourth-order-only effect or contradict the original binned sample bound. Acquisition rates, optical transfer, real phase levels and detector behavior remain unvalidated. The study is conditional feasibility evidence, not a physical experiment or acquisition recommendation.

The newer [optical transfer and detector checks](studies/optical-validation/README.md) preserve five further stages: an optical bench model, calibration robustness, three external processed SPAD delay distributions, an afterpulsing simulation, and an Arb transfer certificate. The broader optical calibration budget failed; eight selected tighter settings passed their simulation criterion. The afterpulsing study had 0/200 errors in each of 48 selected comparisons, with simultaneous one-sided 95% upper bound **0.03375192026711007**. These are finite conditional simulations, not continuous optical-tolerance or measured performance guarantees.

Arb bounds the per-cell numerical transfer error by **1.20e-15** at the selected settings and checks 12,096 saved phase commands. It does not certify physical calibration or the full stochastic classifier. Run `python tools/optical_validation.py audit` for the offline standard-library audit; the [reproduction guide](docs/reproduction.md) also documents the exact Arb replay and retained data licenses.

## Research provenance

Substantial parts of the arguments, code, checks, and documentation were developed with AI assistance under human direction. The maintainer did not independently derive or manually verify every step. Internal alternative implementations provide useful evidence but are not external human review. Read the [methods and limitations disclosure](docs/research-disclosure.md).

AI tools are not listed as authors or Git contributors. Git identity and scientific-methods disclosure serve different purposes.

## Reproduce and challenge

The research capsule preserves explicit assumptions, exact rational inputs, analytic arguments, interval certificates, source code, and formal statements. Its [public provenance record](docs/provenance.md) describes the removal of machine-specific paths and the resulting hash updates. Mathematical inputs are not silently replaced.

Report a proof gap with its statement, model, evidence path, and a concrete counterexample or failed implication. Report a reproduction failure with the command, Python version, and output. See [contribution guidance](.github/CONTRIBUTING.md).

Open work includes temporal/exposure extensions, formalization of the root and testing certificates, useful larger stability neighborhoods, root counts over the full parameter domain, optimal testing/design, primary-literature comparison, and physical validation. See the [research roadmap](docs/roadmap.md).

Maintained under the pseudonym **The Quantum Falcon**. Project-owned code and documentation are [MIT licensed](LICENSE.txt); [third-party terms remain intact](LICENSE_STATUS.md). The [public repository](https://github.com/thequantumfalcon/homometric-photon-counts) is available for inspection. It has no tagged scientific release or external peer-review endorsement. See the [repository status](docs/repository-readiness.md) for verified settings and checks.
