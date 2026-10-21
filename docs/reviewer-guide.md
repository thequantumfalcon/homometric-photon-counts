# A route through the evidence

1. Read the [model](model.md), [claim ledger](claims.md), and [research disclosure](research-disclosure.md).
2. Run `python tools/project.py verify` and `python tools/project.py test --output build/reviewer-check`.
3. For the reference root count, inspect the compact inverse-gain proof and tail cover linked in the ledger. Check how the bounded-gain and large-gain arguments join at $1/6$.
4. For the new local theorem, check Fourier normalization, the uniform small/large-gain bounds, and the compactness/implicit-function argument. The rational checker alone does not prove those analytic implications.
5. For the necessary count, check the affinity bound, product law, total-variation testing inequality, strict error criterion, and integer rounding. The independently coded Taylor and Arb checks address different numerical routes.
6. Inspect each Lean theorem's hypotheses. The [mixture construction](../formal/SCOPE.md) derives the archived factorial-tower premises. The [geometry extension](../formal/GEOMETRY.md) proves finite phase algebra and parameter substitution. The [Gaussian extension](../formal/GAUSSIAN.md) connects an explicit product probability law to the real intensity moments and constructs the Gaussian/Poisson marginal law. Check the remaining concrete moment-identity premises, the computational archive-coordinate binding, and the distinction between a marginal law and a joint physical model.

The general moment formula sums over pairs of site assignments. Its proof applies to any finite geometry, but direct evaluation has $n^{2k}$ terms at order $k$. The formal finite expansion does not itself certify the compressed coefficient calculations used for the concrete pair. Compare source coverage with the executed replay coverage in the [validation record](validation/README.md).

Criticism should identify a specific implication, assumption, certificate entry, or reproduction failure. A successful file hash proves identity, and a successful formal check proves its exact statement; neither validates a physical detector.

The older evidence directories are historical layers. Their status notes can predate the reference four-root result and new lower bound. Current conclusions are stated in the root README and claim ledger; archived historical prose is not silently rewritten to suggest that it always contained later results.
