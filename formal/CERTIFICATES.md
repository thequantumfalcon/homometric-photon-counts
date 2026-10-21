# Concrete moment certificates and count-law distinction

`PhotonConcreteSeparation.count_laws_distinct` proves that the two explicitly defined 63-site geometries induce different Gaussian/Poisson marginal count laws for every positive phase variance and gain and any common nonnegative background. Its only parameter hypotheses are those positivity conditions; it does not assume the concrete moment identities.

With `t = exp(-s/2)`, the preceding theorems prove equality of intensity moments at orders zero through three and the exact fourth difference

$$D_4(t)=\frac{455015761}{20000}t^8(1-t^2)^5(t^6+3t^4+6t^2+6).$$

The final theorem proves the fourth factorial-count moment gap is `eta^4 * delta4(exp(-s))` and that the constructed count measures differ. Its proof uses the established positivity theorem and integrability results; it is not an inference from numerical samples.

## How the arithmetic is checked

The [polynomial bridge](PhotonMomentPolynomial.lean) proves that evaluating the site recurrence at `exp(-s/2)` gives the actual Gaussian intensity integral. The concrete proof maintains the 25 mixed entries with orders `0 <= a,b <= 4`.

Each site identity supplies an explicit polynomial value. Exact arithmetic reduces the phase coefficients using `alpha^2 = -3`, `c^2 = 222` and `d^2 = 573`, where `alpha = i sqrt(3)`, `c = sqrt(222)` and `d = sqrt(573)`. Polynomial combinations of these proved relations and Lean's ring normalization verify the supplied identities. A local Python generator prepared the expressions; it is not invoked or trusted by the formal replay. No `native_decide`, custom axiom, or external arithmetic oracle is used in this certificate chain.

The 22 modules `PhotonCertA0` through `PhotonCertA21` establish the shared base. `PhotonCertABlock42` and `PhotonCertABlock63` check A's remaining sites. `PhotonCertBBlock42` reuses the same base and checks B through site 42; `PhotonCertBBlock63` completes B. The block structure reduces repeated import overhead without changing the per-site statements.

[PhotonConcreteVectors](PhotonConcreteVectors.lean) proves that these explicit site sequences equal the original lists in [PhotonGeometry](PhotonGeometry.lean), retaining all multiplicities and rotations. [PhotonConcreteTransfer](PhotonConcreteTransfer.lean) transports the polynomial identities to real intensity integrals. [PhotonConcreteSeparation](PhotonConcreteSeparation.lean) subtracts the final diagonal values, proves the displayed factorization and supplies those facts to the Gaussian/Poisson count theorem.

The 33-node interpolation theorem remains available, but this final proof establishes polynomial identities directly and does not assume its concrete node values.

## Executed checks and reproducibility

The joint snapshot milestone contains 45 modules and 654 explicit theorem-axiom audits. Later additions are counted in the current README. The final theorem's transitive axiom list is exactly `propext`, `Classical.choice`, and `Quot.sound`. Sources are pinned in [manifest.json](manifest.json); the [validation record](../docs/validation/README.md) distinguishes source compilation, fresh-kernel checking and other checks. Generated files can emit harmless unused-tactic warnings; no warning-free compilation claim is made.

The retained concrete compilation receipt collects successful source-bound compilations and copies their objects into a new isolated directory. This is not a second compilation of unchanged files. A subsequent fresh-kernel check rechecks the complete imported proof environment. For a new full rebuild, use the pinned replay command in the [reproduction guide](../docs/reproduction.md), with `--fresh-kernel`.

The [Nanoda check](../docs/validation/nanoda_concrete.json) accepted the exported final theorem and 54,245 declarations with no typechecker errors and only the three standard axioms permitted. Its axiom pretty-printer reported one diagnostic, retained in the receipt. This adds an independent kernel implementation, but is not the sandboxed comparator workflow or an independent review of the statement meaning.

## Scope that remains separate

This closes the concrete geometry-to-moment calculation for the explicit formal phase lists and its transfer to distinct count laws. The later [coordinate extension](COORDINATES.md) adds the formal parser, coordinate exponentials and full count-law reindexing. The later [joint snapshot extension](JOINT_MODEL.md) proves the conditional Poisson interpretation. Temporal/exposure models, the root and testing certificates, and a quantitative stability neighborhood are outside this theorem. No measured detector data, experimental validity, novelty, optimal sample complexity, or universal imaging claim follows from these proof checks.

The [completed concrete fresh replay](../docs/validation/concrete_formal_replay.json) rechecked the entire imported environment of `PhotonConcreteSeparation` from an empty kernel environment. Its inputs were staged from 44 successful source-bound compilations, with 641 standard-axiom audits. This is distinct from the selected-theorem Nanoda export check.
