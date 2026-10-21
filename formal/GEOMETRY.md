# Concrete phase geometry

[PhotonGeometry.lean](PhotonGeometry.lean) defines the two 63-site complex phase lists and proves their finite algebraic properties. It imports the earlier mixture module so the fresh-kernel replay also covers that proof chain.

Write `alpha = i sqrt(3)` and `r = (1 + alpha)/2`. The 21-site base contains five copies each of `r (sqrt(222) + alpha)/15` and `r (-sqrt(222) + alpha)/15`, four copies each of `(sqrt(573) - alpha)/24` and `(-sqrt(573) - alpha)/24`, and the sites `1, 1, -1`. Structure A concatenates rotations by `1, r, r^3`; B uses `1, r^2, r^3`. Multiplicity is retained: these are lists, not sets.

Twenty audited declarations establish:

- The base has 21 entries and each structure has 63.
- Every phasor in both structures satisfies `z * conjugate(z) = 1`.
- The first five harmonic sums `M_k = sum_j z_j^k` have the explicitly displayed exact complex values, including `M_1 = 0` for both structures.
- `M_k conjugate(M_k)` agrees between the structures for each `k = 1,...,5`.
- The real phase-invariant difference is exactly
  `Re(M_A,4 conjugate(M_A,2)^2) - Re(M_B,4 conjugate(M_B,2)^2) = -455015761/120000`.
- For every real `s`, `exp(-s/2)^2 = exp(-s)`, and substitution into the existing `delta4` definition gives the displayed polynomial in `t = exp(-s/2)`.

The square-root relations and each algebraic certificate are proved inside Lean. Explicit polynomial combinations were prepared with local symbolic algebra; that software is not invoked by the formal replay and is not a trusted oracle. Lean checks the supplied proof terms. No desired harmonic sum or phase-invariant value is assumed as a hypothesis.

The existing [exact reconstruction check](../evidence/scientist-review-2026-10-20/review/verify_density_phasors.py) compares the same six phase types and rotations to all 126 archived phasors using rational field arithmetic. The Lean module defines those expressions directly; it does not parse or formally authenticate the archived JSON. The connection from the original coordinate construction to these phase lists still has that computational evidence boundary.

These harmonic sums are deterministic geometry quantities, not random intensity moments. What remains to formalize is the Gaussian phase characteristic-moment formula, its independent product expansion, and the coefficient calculation connecting this geometry to the first three equal intensity moments and the fourth-moment difference. The parameter-substitution theorem verifies an algebraic identification; it does not supply that missing expectation theorem. Physical measurements, historical novelty, the global root certificate, and the testing bounds are outside this module.

The [source manifest](manifest.json) and [geometry replay receipt](../docs/validation/geometry_formal_replay.json) bind the executed check. The complete replay now has seven modules and 38 theorem axiom audits. The fresh-kernel target imports the earlier modules. This remains a check using Lean's original kernel, not Lean4Lean or external human review.
