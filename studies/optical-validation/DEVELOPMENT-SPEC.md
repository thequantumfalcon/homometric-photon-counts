# Development specification

The deliverable is a reproducible source supplement. Preserve earlier evidence
and the selected 115 original payloads; distinguish measured external data,
finite simulations and rigorous numerical enclosures in every performance claim.

| Requirement | Acceptance check |
| --- | --- |
| Retained evidence identity | Public inventory and all four included original study manifests match; earlier evidence/formal trees remain unchanged |
| Portable numerical audit | Standard-library checks run from a fresh extracted source ZIP without private workspaces |
| Detector provenance | All three tables match their original hashes and afterpulse copies, contain 75,658 nonnegative finite entries, and retain the GPL notice |
| Finite numerical certificate | Arb replay reproduces the saved certificate byte for byte; exact audit checks all enclosure, command and rate bounds |
| Reproduction environment | Caller-relative runtime path remains usable after changing subprocess working directory; assertions stay enabled |
| Publication | Signed additive commit, passing required checks, ordinary fast-forward push; no rewritten prior history |

The finite arithmetic and simulation results are described in the [study guide](README.md).
Recorded local checks do not imply a successful future CI run. The live workflow
and publication receipt identify remote outcomes for the actual commit.

Remaining work is measured optical transfer/SLM calibration, exposure and
detector model validation, a feasible pilot, a full stochastic numerical-error
budget, continuous optical tolerances, remaining root/testing formalization,
and claim-level prior-literature comparison. Repeated identical simulations
cannot replace absent calibration data. The fixed-witness quantizer checks do
not establish a probability bound for unseen draws.
