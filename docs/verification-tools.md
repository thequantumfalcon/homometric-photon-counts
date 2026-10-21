# Verification tools and actual coverage

Status checked against retained local records on 2026-10-21. A tool's capabilities do not establish that this project has run it or verified every claim with it.

| Tool | Actual project status | Further contribution |
| --- | --- | --- |
| SageMath | Exact reconstruction checks passed using the included Python implementations. No retained SageMath execution receipt was identified; a Sage-specific pass is not claimed. | A separately implemented reconstruction could check geometry and polynomial identities. Sage supports exact matrix operations, but shared arithmetic backends would limit independence. |
| Python-FLINT / Arb | The public extended arithmetic replay passed all ten stages, including interval checks supporting the reference root count and probability bounds. | Further certified bounds for new parameters or a quantitative stability neighborhood. Existing checks do not validate the physical detector model. |
| Lean / mathlib | Five modules compiled with thirteen theorem axiom audits, including eight new moment-transfer results. Preserved original records also contain fresh checks using the same Lean kernel. | Formalize the measurable joint counting model and derive the tower identities; connect concrete geometry and Gaussian intensity moments to the conditional theorem. The complete proof chain and global root certificate are not formalized. |
| Lean4Lean | No successful project-proof check is recorded. A local executable's presence is not a verification result. | An additional checker for existing proof terms, subject to compatibility and explicit import coverage. It cannot supply missing model proofs. Its authors state that it derives from Lean's C++ kernel and may share implementation bugs. |

See the [local validation records](validation/README.md), [formal scope](../evidence/followup-2026-10-20/lean/SCOPE.txt), and [claim ledger](claims.md) for evidence and exact limits.

Tool capabilities are documented in the [SageMath linear-algebra tutorial](https://doc.sagemath.org/html/en/tutorial/tour_linalg.html), [Python-FLINT documentation](https://python-flint.readthedocs.io/en/latest/), [Lean/mathlib introduction](https://leanprover-community.github.io/), and [Lean4Lean README](https://github.com/digama0/lean4lean). These references describe tools, not external review of this project.
