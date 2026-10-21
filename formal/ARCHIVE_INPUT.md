# Archived phase input and formal geometry

The archive bridge connects the two saved arrays of exact rational phasors to the explicit phase lists used by the count-law theorem. It preserves every entry and multiplicity. The conclusion is a list permutation, since the archived and formal lists have different orders.

The proof has three parts:

1. [PhotonArchiveBinding.lean](PhotonArchiveBinding.lean) evaluates all 22 distinct saved phase records in the basis `1, sqrt(3), sqrt(74), sqrt(3)*sqrt(74), sqrt(191), sqrt(3)*sqrt(191), sqrt(74)*sqrt(191), sqrt(3)*sqrt(74)*sqrt(191)`. Lean proves the square-root and rotation identities, and that the two lists of 63 evaluated records permute `PhotonGeometry.geometryA` and `geometryB`.
2. [PhotonArchiveParserCore.lean](PhotonArchiveParserCore.lean) defines a total parser for the restricted phase-array grammar: at most 64 records, each containing `re` then `im`, with eight quoted rational coefficients each. Denominators must be positive; escapes, malformed records, trailing commas and unconsumed input are rejected. This is not a general JSON parser.
3. [PhotonArchiveParsed.lean](PhotonArchiveParsed.lean) proves that the two exact archived array fragments parse to the records used in the algebra proof. [PhotonArchiveBridge.lean](PhotonArchiveBridge.lean) combines these results as `decodedA_geometry` and `decodedB_geometry`. Kernel reduction checks the concrete parsing; no native Boolean oracle or additional axiom is used.

The final theorem for A says that there exists a phase-record list `ps` such that the parser returns `some ps` on the archived A fragment, and evaluating `ps` gives a permutation of `geometryA`. The B theorem has the same form. These are the propositions to inspect; they do not assert equality of differently ordered lists.

The [external byte checker](../tools/check_archive_binding.py) verifies that the quoted fragments reproduce the original ASCII input, including whitespace, at the recorded offsets and JSON fields of the pinned [input model](../evidence/homometric-photon-counts/science_completion/harmonic_certificate/input_model.json). Its [receipt](../docs/validation/archive_byte_binding.json) records the hashes and offsets. `project.py check` and packaged verification run this check. Hashing, filesystem/ZIP selection and the correspondence of external bytes to source literals remain external operations.

Local REA inspection identified the preceding source capsule and reconciled its member inventory. A separate [archive identity record](../docs/validation/archive_artifacts.json) confirms that the model input is identical in the supplied v0.1.0 and v0.2.0 archives. REA supplied artifact evidence; Lean supplied the mathematical proof. Neither operation establishes physical validity or historical priority.

## Exact remaining boundary

This closes the exact-phase-array parsing and algebraic geometry correspondence for the pinned input. It does not derive `exp(i*pi*x/3)` from the saved coordinate construction. Decimal coordinate strings are approximations, and their symbolic offset metadata is not a premise of these theorems. That coordinate interpretation still has the separate [computational reconstruction check](../evidence/scientist-review-2026-10-20/review/verify_density_phasors.py).

The count-law theorem uses the canonical formal ordering. Transferring that law directly to a model indexed in the original archive order would require a Gaussian exchangeability/reindexing theorem, or an explicit definition using the verified canonical reordering. The present permutation theorem alone does not perform that probability transfer.

The [validation record](../docs/validation/README.md) separates the new branch's fresh-kernel check from the earlier joint-model check. The earlier Nanoda receipts do not cover these new declarations. No detector data, temporal model, root/testing formalization, or novelty determination is supplied by this bridge.
