# Measurable Poisson mixtures

This extension adds a constructed count law to the earlier conditional moment-transfer theorem. It preserves the archived evidence and its historical statements of remaining work.

For a measurable nonnegative rate `rate` on a space with measure `mu`, `countLaw mu rate` is `mu.bind (poissonLaw ∘ rate)`. It mixes the previously constructed single-rate Poisson measures. Five audited declarations establish:

1. The map from a nonnegative rate to its Poisson measure is measurable.
2. The mixture is a probability measure whenever `mu` is a probability measure.
3. Its kth falling-factorial integral equals the integral of the kth rate power.
4. The corresponding iterated-integral tower identity follows from the construction.
5. The prior fourth-moment gap and unequal-count-laws conclusion hold for these constructed mixtures, without taking the tower identities as premises.

The interchange uses mathlib's nonnegative `Measure.lintegral_bind` theorem, the proved single-rate Poisson factorial integrability, and conversion to real integrals. It does not assume the desired rate-moment identity. The general real-integral identity uses mathlib's total integral convention; finite-moment assumptions remain necessary when interpreting these integrals as finite expectations. The final distinction theorem retains integrability of the intensity powers through order four.

The explicit remaining premises include measurable nonnegative rates, their affine intensity representation, intensity integrability, first-three-moment equality, and the stated fourth-intensity-moment polynomial. Inherited `delta4 (exp (-s))` notation remains exactly as in the original conditional theorem. The later [geometry module](GEOMETRY.md) proves its algebraic parameter substitution and concrete phase invariants; the Gaussian expectation identity remains a separate obligation.

This constructs and checks the marginal mixture law. It does not separately construct a joint phase/count process or prove a conditional-distribution statement for measured detector data. Concrete geometry, the Gaussian intensity-moment derivation, numerical decision certificates, the global root proof, and experimental validity are not established by these five declarations.

The source hash is in [manifest.json](manifest.json). The [earlier executed replay](../docs/validation/mixture_formal_replay.json) passed six modules and eighteen theorem axiom audits, including the fresh-kernel check of the mixture extension and its imports. The current [reproduction command](../docs/reproduction.md) also checks the geometry extension: seven modules and 38 audits in total. Audited theorem dependencies contain only `propext`, `Classical.choice`, and `Quot.sound`. This uses Lean's original kernel; it is not a Lean4Lean check.
