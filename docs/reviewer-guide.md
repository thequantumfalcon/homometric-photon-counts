# A route through the evidence

1. Read the [model](model.md), [claim ledger](claims.md), and [research disclosure](research-disclosure.md).
2. Run `python tools/project.py verify` and `python tools/project.py test --output build/reviewer-check`.
3. For the reference root count, inspect the compact inverse-gain proof and tail cover linked in the ledger. Check how the bounded-gain and large-gain arguments join at $1/6$.
4. For the new local theorem, check Fourier normalization, the uniform small/large-gain bounds, and the compactness/implicit-function argument. The rational checker alone does not prove those analytic implications.
5. For the necessary count, check the affinity bound, product law, total-variation testing inequality, strict error criterion, and integer rounding. The independently coded Taylor and Arb checks address different numerical routes.
6. Inspect each Lean theorem's hypotheses. In particular, identify the conditional-expectation tower premises and the unformalized concrete geometry/intensity identities.

Criticism should identify a specific implication, assumption, certificate entry, or reproduction failure. A successful file hash proves identity, and a successful formal check proves its exact statement; neither validates a physical detector.

The older evidence directories are historical layers. Their status notes can predate the reference four-root result and new lower bound. Current conclusions are stated in the root README and claim ledger; archived historical prose is not silently rewritten to suggest that it always contained later results.
