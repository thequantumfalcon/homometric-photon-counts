# Symbolic coordinates and the full photon-count law

This extension joins the pinned symbolic coordinate records to the concrete Gaussian/Poisson count-law theorem. It uses the exact offset metadata; the decimal coordinate strings are display approximations.

Let

$$\theta=\arcsin\frac1{5\sqrt3},\qquad \phi=-\arcsin\frac1{8\sqrt3}.$$

A record with integer base $q$, offset kind and sign represents $x=q+3a/\pi$, where $a$ is zero, $\pm\theta$ or $\pm\phi$. Its phasor is $\exp(i\pi x/3)$. [PhotonCoordinates.lean](PhotonCoordinates.lean) proves the arcsine domain and branch identities, the four exact radical exponentials, and the general identity

$$\exp(i\pi(q+3a/\pi)/3)=r^{q\bmod6}\exp(ia),\qquad r=(1+i\sqrt3)/2.$$

The input and geometry connection has three steps:

1. [PhotonCoordinateParser.lean](PhotonCoordinateParser.lean) defines a total restricted parser for the saved record format. It consumes ordinal and decimal display fields, retains the integer base, offset kind and sign, and checks the allowed sign/kind combinations. It is not a general JSON parser. [PhotonCoordinateData.lean](PhotonCoordinateData.lean) proves by kernel reduction that both literal arrays decode to the stated 63-record lists.
2. The same data module proves that the record lists permute a 21-record base construction translated by `[0,31,63]` for A and `[0,32,63]` for B. The base has records for $3j+1+3(-1)^j\theta/\pi$ and $3j+3\epsilon_j/\pi$, $0\le j<10$, with $\epsilon_0=\epsilon_1=0$ and $\epsilon_j=(-1)^j\phi$ thereafter, plus 30.
3. [PhotonCoordinateGeometry.lean](PhotonCoordinateGeometry.lean) proves equality, in the original record order, between those coordinate phasors and all 126 evaluated archived exact phases. The earlier [archive bridge](ARCHIVE_INPUT.md) then supplies the permutation to the canonical formal lists.

[PhotonCountReindex.lean](PhotonCountReindex.lean) constructs an index equivalence for any list permutation, including repeated entries, transports the intensity and Poisson rate, and proves that the product of identical Gaussian site laws is preserved. Its `countLaw_perm` theorem proves equality of the **entire count measure**, for any finite complex phase list and all nonnegative variance, gain and background.

[PhotonArchiveCountLaw.lean](PhotonArchiveCountLaw.lean) applies that theorem to the saved phase order. [PhotonCoordinateCountLaw.lean](PhotonCoordinateCountLaw.lean) applies the coordinate identities and proves the fourth factorial-count moment gap and count-law distinction for positive variance and gain and a common nonnegative background. Its decoded-input theorem starts from the parsed coordinate literals. These conclusions use the proved concrete moments; no additional exchangeability or concrete coefficient premise is introduced.

The [external byte checker](../tools/check_coordinate_binding.py) and [receipt](../docs/validation/coordinate_byte_binding.json) bind the literal characters, including whitespace, to the coordinate fields of the unchanged archived input model. This check also verifies the recorded ordinal sequence. Filesystem selection, hashing and the comparison of external bytes with Lean source remain external operations. The formal parser does not interpret ordinal or decimal fields as mathematical coordinates. No certified decimal-rounding claim is made.

## Validation and remaining scope

The [validation record](../docs/validation/README.md) distinguishes source compilation and standard-axiom audits from additional fresh-kernel checks and earlier Nanoda checks. The earlier Nanoda exports do not cover these new declarations. The reproducible source manifest preserves every earlier Lean module and the archived scientific evidence.

The exact symbolic-coordinate interpretation and count-law reindexing gaps are closed for this fixed iid Gaussian-phase/Poisson model. The later [spatial extension](HOMOMETRY.md) additionally proves real-coordinate ordering, distinctness, directed-difference homometry and exclusion of translations/reflections. These results do not formalize an instrument response, graph/covariance claims, decimal rendering, temporal/exposure-integrated or correlated phase models, the root/testing certificates, detector calibration, physical validation, or historical novelty. The older graph-correlated model is not silently substituted for the independent site law.
