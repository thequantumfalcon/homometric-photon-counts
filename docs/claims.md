# Claim and evidence ledger

Status is attached to a statement and its assumptions, not to an entire repository.

| Claim | Evidence | Limits |
| --- | --- | --- |
| Reference four-root count | [Analytic argument](../evidence/scientist-review-2026-10-20/global/compact_gain_proof.txt), [certificate](../evidence/scientist-review-2026-10-20/global/compact_gain_certificate.json), [exact brackets](../evidence/scientist-review-2026-10-20/global/certified_roots.json), [separate implementation](../evidence/scientist-review-2026-10-20/review/independent_compact_gain.py) | $t=1/2,b=0$; interval/Fourier proof, not a Lean theorem |
| Local stability of four roots | [Proof](../evidence/followup-2026-10-20/stability/local_stability_proof.txt), [derivation review](../evidence/followup-2026-10-20/stability/independent_review.txt), [exact endpoint constants](../evidence/followup-2026-10-20/stability/endpoint_constants.json) | Existence of a neighborhood; no computed full radius |
| Necessary 13-bin sample count | [Proof](../evidence/followup-2026-10-20/lowerbounds/proof.txt), [certificate](../evidence/followup-2026-10-20/lowerbounds/binned_lower_bound.json), [independent exact check](../evidence/followup-2026-10-20/independent_lowerbounds/review.txt) | All tests of this fixed binned iid experiment; not unbinned/global optimality |
| Sufficient 13-bin sample count | [Certificate](../evidence/continuation-2026-10-20/multibin/certificate.json), [Arb replay](../evidence/scientist-review-2026-10-20/arb/verify_arb.py) | Fixed score; known calibration; each error strictly below 5% |
| Formal moment transfer | [Scope](../evidence/followup-2026-10-20/lean/SCOPE.txt), [final theorem source](../evidence/followup-2026-10-20/lean/PhotonMixtureBridge.lean), [fresh check receipt](../evidence/followup-2026-10-20/lean/verified_receipt.json) | Tower identities, geometry and concrete intensity moments remain premises |
| Constructed Poisson mixtures | [Extension scope](../formal/SCOPE.md), [source](../formal/PhotonPoissonMixture.lean), [source manifest](../formal/manifest.json) | Derives the tower identities for the constructed marginal count laws. Geometry, concrete intensity moments, and physical interpretation remain premises or separate obligations. |

The reference global root proof combines the bounded-gain certificate through $1/6$ with an inverse-gain cover of the entire remaining half-line. The fourth positive root is strictly between 0.2934841 and 0.2934842. A numerical scan or illustration alone would not establish this result.

The new necessary/sufficient interval is [28,091,647,285,174, 102,399,876,723,169], for error strictly below 1/20 under each structure. The lower endpoint is conservative; it is not asserted to be the exact smallest integer compatible with every intermediate inequality.

Internal checks share some inputs and libraries. The two Fourier implementations use Arb; fresh Lean checks use the same Lean kernel. No external human peer review, experimental validation, complete proof-assistant formalization, or historical novelty is claimed.
