# Measurable Poisson mixtures

This extension adds a constructed count law to the earlier conditional moment-transfer theorem. It preserves the archived evidence and its historical statements of remaining work.

For a measurable nonnegative rate `rate` on a space with measure `mu`, `countLaw mu rate` is `mu.bind (poissonLaw ∘ rate)`. It mixes the previously constructed single-rate Poisson measures. Five audited declarations establish:

1. The map from a nonnegative rate to its Poisson measure is measurable.
2. The mixture is a probability measure whenever `mu` is a probability measure.
3. Its kth falling-factorial integral equals the integral of the kth rate power.
4. The corresponding iterated-integral tower identity follows from the construction.
5. The prior fourth-moment gap and unequal-count-laws conclusion hold for these constructed mixtures, without taking the tower identities as premises.

The interchange uses mathlib's nonnegative `Measure.lintegral_bind` theorem, the proved single-rate Poisson factorial integrability, and conversion to real integrals. It does not assume the desired rate-moment identity. The general real-integral identity uses mathlib's total integral convention; finite-moment assumptions remain necessary when interpreting these integrals as finite expectations. The final distinction theorem retains integrability of the intensity powers through order four.

This generic mixture theorem takes measurable nonnegative rates, their affine intensity representation, intensity integrability, first-three-moment equality, and the stated fourth-intensity-moment polynomial as premises. Inherited `delta4 (exp (-s))` notation remains exactly as in the original conditional theorem. The [geometry module](GEOMETRY.md) proves its algebraic parameter substitution and concrete phase invariants. The later [Gaussian extension](GAUSSIAN.md) constructs the rates and intensities, supplies their measurability and integrability, and proves a general finite Gaussian intensity-moment formula. Its concrete count-law distinction theorem retains the low-order moment identities as hypotheses, together with the stated parameter conditions.

This constructs and checks the marginal mixture law. It does not separately construct a joint phase/count process or prove a conditional-distribution statement for measured detector data. The five declarations in this module alone do not establish the concrete geometry, Gaussian intensity-moment formula, numerical decision certificates, global root proof, or experimental validity. The linked later modules extend the mathematical coverage. The [concrete certificates](CERTIFICATES.md) discharge the moment coefficient reduction for the explicit phase lists; physical interpretation remains a separate obligation.

The source hash is in [manifest.json](manifest.json). The [earlier executed replay](../docs/validation/mixture_formal_replay.json) passed six modules and eighteen theorem axiom audits, including the fresh-kernel check of the mixture extension and its imports. The later [geometry replay](../docs/validation/geometry_formal_replay.json) covered seven modules and 38 audits. These are historical receipts for their respective source sets. The [reproduction guide](../docs/reproduction.md) and [validation record](../docs/validation/README.md) describe the maintained replay and its executed checks. Audited theorem dependencies are restricted to `propext`, `Classical.choice`, and `Quot.sound`. This uses Lean's original kernel; it is not a Lean4Lean check.
