# Gaussian intensity moments and the count model

The Gaussian extension proves a general finite intensity-moment formula, a correct site-by-site recurrence, and the Gaussian/Poisson count-model construction for the two phase lists. The [concrete certificates](CERTIFICATES.md) complete the coefficient calculation: equality of the first three intensity moments and the stated fourth-moment difference. The final theorem assumes neither the integration rule nor these concrete moment values.

## Coverage of the eight modules

| Module | Mathematical content |
| --- | --- |
| [PhotonGaussianPhase.lean](PhotonGaussianPhase.lean) | Defines independent Gaussian phases using a finite product probability measure, proves their mixed monomial and finite-polynomial integrals, and connects a variance-s Gaussian to a scaled standard normal. |
| [PhotonIntensityBounds.lean](PhotonIntensityBounds.lean) | Defines the field and real intensity, expands the intensity as a double sum, proves measurability and the bound from unit phasors, and establishes integrability of every intensity power. For each concrete geometry, the intensity lies between 0 and 3969. |
| [PhotonIntensityExpansion.lean](PhotonIntensityExpansion.lean) | Expands every intensity power into a finite sum of mixed phase monomials using the occupancy of each site in two index sequences. |
| [PhotonGaussianIntensity.lean](PhotonGaussianIntensity.lean) | Integrates that actual intensity expansion, proving the exact Gaussian intensity-moment formula and integrability for every finite complex weight vector and every natural moment order. No unit-modulus hypothesis is needed for this general formula. |
| [PhotonGaussianModel.lean](PhotonGaussianModel.lean) | Constructs measurable nonnegative detector rates and marginal Poisson-mixture count laws. Proves their factorial-moment identity and specializes the previous distinction theorem to the concrete Gaussian intensities. |
| [PhotonGaussianAppend.lean](PhotonGaussianAppend.lean) | Proves the field identity for an appended site and transports the finite Gaussian integral to the previous sites times one independent Gaussian coordinate. |
| [PhotonMixedRecurrence.lean](PhotonMixedRecurrence.lean) | Proves the site-by-site mixed-moment recurrence, its recursive correctness for arbitrary finite complex weights, and equality of its diagonal entries with the real intensity moments. |
| [PhotonMomentPolynomial.lean](PhotonMomentPolynomial.lean) | Represents the recurrence as a polynomial in t, proves equality with the actual intensity integral at t = exp(-s/2), bounds its degree, and proves that 33 distinct evaluations determine each difference through order four. |

## The finite moment formula

Let `z : Fin n -> Complex` be any finite complex weight vector, let `s >= 0`, and let the coordinates `X_j` have the product law of independent centered Gaussians with variance `s`. Define

$$I(X)=\left|\sum_{j=1}^{n} z_j e^{iX_j}\right|^2.$$

For maps `f, g : Fin k -> Fin n`, let `m_f(j)` be the number of positions sent to site `j`, and set

$$C_z(f,g)=\left(\prod_{r=1}^{k}z_{f(r)}\right)\overline{\left(\prod_{r=1}^{k}z_{g(r)}\right)}.$$

The theorem `gaussian_intensity_moment` proves

$$E[I^k]=\sum_{f,g}C_z(f,g)\exp\left(-\frac{s}{2}\sum_{j=1}^{n}(m_f(j)-m_g(j))^2\right).$$

The formal equality embeds the real integral on the left into the complex numbers. Its left side is the integral of the defined real intensity power, and `gaussian_intensity_power_integrable` proves that integral is finite. The right side is therefore real despite its complex coefficient notation. This is not an identity that relies on Lean's zero value for a nonintegrable total integral.

The proof expands the field power, groups repeated site indices into occupancies, uses the Gaussian characteristic function, and applies finite-product integration and finite-sum linearity. It does not assume the desired intensity moments or invoke an external symbolic evaluator as an oracle.

This expression has `n^(2k)` index pairs. It is a mathematical specification, not a fast evaluation algorithm for 63 sites or high orders. The later proved recurrence below avoids requiring this exhaustive expansion as the route to coefficient evaluation. Its exact polynomial and number-field instantiation for the two geometries is supplied by the later certificate modules.

The standard-normal connection is also explicit: `scaled_standard_gaussian_law` proves that mapping `Z ~ N(0,1)` by `sqrt(s) * Z` gives `N(0,s)`. `standard_gaussian_mixed_phase_integral` proves the single-site mixed moment in the original `exp(i sqrt(s) Z)` notation. The finite-site integration theorem uses the product Gaussian measure, so independence is part of its defined model.

## From the model construction to the concrete count-law theorem

For the exact phase lists in [PhotonGeometry.lean](PhotonGeometry.lean), the model module defines the nonnegative rate `eta * I + b` and mixes the proved Poisson measures over the Gaussian phase law. Measurability, normalization, the affine rate representation, the factorial-moment transfer, and intensity integrability are supplied by the construction and the preceding proofs.

The theorem `count_gap_of_intensity_moments` assumes positive variance and gain, with nonnegative common background. Its remaining moment hypotheses are exactly:

1. The concrete intensity integrals agree at orders `k <= 3`, including normalization at order zero.
2. Their fourth-moment difference is `PhotonAlgebra.delta4 (exp(-s))`.

It then proves the fourth factorial-count moment difference and inequality of the two constructed count laws. The later `PhotonConcreteSeparation.intensity_matching` and `intensity_gap` theorems prove both hypotheses. `count_laws_distinct` supplies them to this intermediate theorem, completing the count-law distinction proof for the explicit model.

## The proved recurrence and its concrete evaluation

`gaussian_append_recurrence` proves how the actual Gaussian mixed amplitude moment changes when one independent site is appended. If `R(a,b)` is the moment before adding the site, then

$$R'(a,b)=\sum_{i=0}^{a}\sum_{j=0}^{b}{a\choose i}{b\choose j}R(a-i,b-j)z^i\overline z^{\,j}\exp\left(-\frac{s(i-j)^2}{2}\right).$$

`recurrence_eq_mixedMoment` proves the recursively defined values equal those integrals for every finite complex geometry and every pair of natural orders. `recurrence_eq_real_intensity` identifies the diagonal entry `R(k,k)` with the real kth intensity moment. Integrability is proved separately.

For orders `0 <= a,b <= 4`, the recurrence only references those same 25 entries. Updating such a table across 63 sites entails 14,175 summands before coefficient arithmetic. This describes the mathematical recurrence, not a verified implementation of memoization or the archived Python optimizations. The Lean definition uses complex values and real exponentials and is noncomputable; the later certificate modules prove its required concrete polynomial values through exact identities, without trusting an external evaluator. In particular, the unit-modulus simplifications in the archived [`direct_site_moments`](../evidence/homometric-photon-counts/science_extension/finite_detection/homogeneous_moment_engine.py) implementation are not automatically certified by the recurrence theorem.

The existing [33-node certificate program](../evidence/audit-2026-10-20/moments/symbolic_fourth.py) offers an alternative route to the concrete calculation, and the polynomial module proves its structural prerequisites. The final certificate proof instead establishes polynomial identities directly, so it does not depend on those 33 node evaluations. `momentPoly_degree` bounds mixed order (a,b) by a²+b², hence the fourth diagonal difference has degree at most 32. `difference_eq_of_33_nodes` proves equality to any target of degree at most 32 from equal evaluations at 1,...,33. `eval_momentPoly_intensity` identifies the value at exp(-s/2) with the actual intensity integral. Nodes above one are polynomial evaluations, not Gaussian parameter values. The interpolation theorem itself has 33 evaluation hypotheses; the final concrete proof does not use that route. The archived Python certificate is not treated as a Lean proof.

## Evidence and interpretation boundaries

The geometry definitions are the explicit phase expressions described in [GEOMETRY.md](GEOMETRY.md). A separate exact reconstruction program binds them computationally to the archived phasors. These modules do not formally parse or authenticate the original coordinate data.

The count law is a constructed marginal probability measure. The later [joint snapshot extension](JOINT_MODEL.md) constructs a joint phase/count probability measure and proves the conditional Poisson law given intensity. It does not validate that model for measured detector data or specify temporal dynamics. It does not establish experimental feasibility, novelty, the global root certificate, a quantitative stability neighborhood, or the testing bounds inside Lean.

The [source manifest](manifest.json) identifies the maintained formal sources. Module compilation, axiom audits, and a complete fresh-kernel replay are distinct checks; the [validation record](../docs/validation/README.md) records executed runs. Earlier geometry and mixture receipts describe their earlier source sets and do not certify later additions. The fresh replay uses Lean's kernel. The separately recorded [Nanoda check](../docs/validation/nanoda_concrete.json) covers the final count-law theorem dependency closure with another kernel implementation; neither is external human review.

The earlier [Gaussian replay](../docs/validation/gaussian_formal_replay.json) recompiled twelve modules, passed 73 standard-axiom audits, and completed the fresh-kernel check of `PhotonGaussianModel`. It predates the two recurrence modules. The later joint-snapshot replay covered 45 modules and 654 audits with target `PhotonJointModel`. The [22 October local source rebuild](../docs/validation/formal_replay_20261022.json) compiled 61 modules and passed 722 audits using ordinary Lean kernel compilation; it did not repeat the separate fresh-kernel or Nanoda checks. The fourteen-module receipt below predates the polynomial addition.

The [executed recurrence replay](../docs/validation/recurrence_formal_replay.json) recompiled all fourteen modules, passed 82 standard-axiom audits, and completed the fresh-kernel check of `PhotonMixedRecurrence` and its full imported environment. This extends the earlier twelve-module replay to the proved compression recurrence.

The [executed polynomial replay](../docs/validation/polynomial_formal_replay.json) recompiled all fifteen modules, passed 92 standard-axiom audits, and completed the fresh-kernel check of `PhotonMomentPolynomial` and its imported environment. That historical replay predates the later concrete certificates and final theorem; their execution coverage is recorded separately.

The [completed concrete fresh replay](../docs/validation/concrete_formal_replay.json) rechecked the entire imported environment of `PhotonConcreteSeparation` from an empty kernel environment. Its inputs were staged from 44 successful source-bound compilations, with 641 standard-axiom audits. This is distinct from the selected-theorem Nanoda export check.
