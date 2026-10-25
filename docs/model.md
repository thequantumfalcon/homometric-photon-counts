# Model and notation

This page describes the original fourth-order separation model. The later [optical feasibility extension](../studies/optical-feasibility/README.md) explicitly changes spatial frequency, observation, phase variance and calibration assumptions. Its second-order score and simplified detector models have their own certificates; the first-three-moment matching statement below does not apply to that changed frequency.

The primary model has two fixed lists of 63 unit phasors, independent centered Gaussian site phases, a time-local conditional Poisson detector, common background, and known parameters for the stated testing result. The intensity satisfies $0\le I\le3969$.

Use $s$ for phase variance, $t=e^{-s/2}$, and $x=t^2=e^{-s}$. The reference point is $s=2\log2,t=1/2,x=1/4$. The [geometry extension](../formal/GEOMETRY.md) proves the exponential substitution and the resulting polynomial identity. The [Gaussian extension](../formal/GAUSSIAN.md) derives an exact finite-sum expression for every intensity moment. The [concrete certificates](../formal/CERTIFICATES.md) evaluate the proved recurrence to establish the specific 63-site moment identities below.

The intensity moment differences $D_k=E_A[I^k]-E_B[I^k]$ obey $D_0=\cdots=D_3=0$ and

$$D_4(t)=\frac{455015761}{20000}t^8(1-t^2)^5(t^6+3t^4+6t^2+6)>0\qquad(0<t<1).$$

For $N\mid I\sim\mathrm{Poisson}(b+\eta I)$ with $\eta>0$ and common $b\ge0$, the fourth falling-factorial moment difference equals $\eta^4D_4(t)$. It is strictly positive for finite phase variance $s>0$, equivalently $0<t<1$. Common background cancels because the first three intensity moments match. Arbitrary preprocessing, detector saturation, dead time, dependent site phases, unequal backgrounds, or drifting parameters require additional arguments.

## Moments, cumulants and count probabilities

Write $(N)_r=N(N-1)\cdots(N-r+1)$ for the falling factorial. Conditional Poisson counting gives

$$\mathbb E[(N)_r]=\mathbb E[(b+\eta I)^r].$$

Thus the common intensity moments through order three imply common count factorial moments through order three, and the fourth factorial-moment gap is $\eta^4D_4(t)$. These are weighted sums over all count values. They do not imply equality of any particular probabilities $P(N=n)$. Equality for the single event $N=4$ at a blind gain is compatible with unequal full count laws.

For clarity, define ordinary intensity cumulants by $K_I(v)=\log\mathbb E[e^{vI}]$ and count factorial cumulants by $K_N^{F}(u)=\log\mathbb E[(1+u)^N]$, taking derivatives at zero. The bounded intensity makes these identities well defined near zero, and

$$K_N^{F}(u)=bu+K_I(\eta u),\qquad
\kappa_1^{F}(N)=b+\eta\mathbb E[I],\qquad
\kappa_r^{F}(N)=\eta^r\kappa_r(I)\quad(r\ge2).$$

Fixed Poisson background therefore cancels from higher **factorial** cumulants. Ordinary count cumulants have different formulas: for example, $\operatorname{Var}(N)=b+\eta\mathbb E[I]+\eta^2\operatorname{Var}(I)$, whereas $\kappa_2^{F}(N)=\operatorname{Var}(N)-\mathbb E[N]=\eta^2\operatorname{Var}(I)$. The fourth factorial-cumulant gap also equals $\eta^4D_4(t)$ here, because the lower intensity moments match. These generating-function identities explain the notation; the formal theorem's documented scope remains the moment gap and count-law distinction. Count-law distinction within this Poisson-mixture model is not evidence of nonclassical light or a particle-identity measurement.

## Formal construction and finite records

The formal construction uses a finite product of centered Gaussian laws with variance $s$, the explicit phase lists, and a measurable Poisson mixture with rate $b+\eta I$. It proves $0\le I\le3969$ for both geometries and integrability of every intensity power. The final theorem `PhotonConcreteSeparation.count_laws_distinct` proves the concrete low-order moment matches and fourth-gap identity and uses them to establish count-law distinction; these moment values are no longer hypotheses. The [joint snapshot extension](../formal/JOINT_MODEL.md) constructs phases and counts on one probability space, proves the conditional Poisson law given intensity, and identifies its count marginal with this mixture. The [archive-input bridge](../formal/ARCHIVE_INPUT.md) now parses the saved exact phase arrays and proves that their evaluations are permutations of the formal lists. External file selection and byte binding are checked separately. The [coordinate and reindexing extension](../formal/COORDINATES.md) derives the exact coordinate exponentials and transports the full count law to the saved ordering. It uses symbolic integer/offset metadata, not the rounded decimal strings. The input archive also contains a separate graph covariance; the new theorem reuses its deterministic geometry under the explicitly defined iid phase law, without asserting that the entire archived model is iid. The [spatial extension](../formal/HOMOMETRY.md) proves strict ordering, 63 distinct real sites, identical directed-difference multisets, and exclusion of every translation and reflection between these exact coordinates. Its combined theorem supplies the fourth factorial-count moment gap and unequal full count laws for those positions. This is not a derivation of an instrument response or a physical calibration result.

The fixed testing experiment pools counts at least 12 into one bin. It assumes iid snapshots and known $s,\eta,b$. Its lower bound does not apply to the richer unbinned observation, and its sufficient count does not establish a feasible measurement duration.

The population theorem compares the two geometries at the same fixed parameters. It does not by itself identify unknown nuisance parameters or give confidence coverage from estimated moments. A finite-record guarantee must specify the observation, parameter knowledge or allowed parameter set, independence or dependence assumptions, and error criterion. In particular, the reference 13-bin sample bounds do not supply a uniform guarantee for an unknown-calibration estimator. The changed-frequency feasibility study has its own explicit fixed-parameter uncertainty boxes and does not inherit the original first-three-moment equality.

The later [optical transfer/detector supplement](../studies/optical-validation/README.md) keeps the changed frequency and models unequal complex cell weights, estimated phase correction before quantization, and a separate finite-gate afterpulse event queue. Its data are external processed delay distributions, with afterpulse strengths separately specified. Initially-live gates, absent prehistory and excluded twilight/drift effects are modeling assumptions. Its simulations and finite arithmetic checks do not change the original Gaussian/Poisson theorem or establish the instrument response.

Archived exposure, calibration and dependence extensions retain their own hypotheses. In particular, the public `homometric-motion` project studies a different spring/OU exposure model. Neither its sample counts nor its formal declarations are automatically premises of this repository.

## Relation to bounded-count identification

The related [bounded-count identification theorem](https://github.com/thequantumfalcon/bounded-count-identifiability/blob/main/docs/theorem.md) assumes an integer-valued source $X\in\{0,\ldots,D\}$ and observation $Y=X+Z$, where $Z$ is an independent Poisson variable with fixed rate. It identifies the source law from exact population factorial cumulants of orders $2,\ldots,D+1$ when the support bound is known; including the mean identifies the background rate.

Here $I\in[0,3969]$ is real-valued and $N\mid I$ is Poisson with rate $b+\eta I$. A bound on intensity or rate is not a finite support bound on the observed count. Although both channels remove fixed Poisson background from higher factorial cumulants, their source laws and identification problems differ. Neither the bounded-count theorem nor this fixed-pair separation theorem establishes finite-moment reconstruction of an arbitrary intensity distribution, an unknown detector model, or a calibrated physical experiment.
