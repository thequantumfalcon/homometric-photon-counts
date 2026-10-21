# Joint Gaussian-phase and photon-count model

[PhotonJointModel.lean](PhotonJointModel.lean) closes the single-snapshot probability-space interpretation. It constructs one probability measure on pairs `(theta, N)`, with the prescribed product Gaussian phase law and conditional Poisson detector law. It connects its count marginal to the previously proved concrete count-law distinction.

For any finite complex phase list `zs`, nonnegative variance `s`, gain `eta` and background `b`, the construction is

$$\mu(d\theta,dn)=\gamma_s(d\theta)\,\operatorname{Poisson}(b+\eta I(\theta))(dn).$$

The phase coordinate has law $\gamma_s$. The count coordinate has exactly the `PhotonGaussianModel.countLaw` mixture already used in the moment proof. `joint_rectangle` proves the corresponding integral formula for measurable rectangles; this is a normalized probability measure, not merely a proposed density.

`count_given_phases` proves a `HasCondDistrib` statement for the count given the entire phase vector. Since the kernel depends on that vector only through its nonnegative intensity, `count_given_intensity` proves

$$N\mid I\sim\operatorname{Poisson}(b+\eta I).$$

Here a conditional distribution is specified by its joint-law identity, using mathlib's `HasCondDistrib`. Conditional laws are understood up to almost-sure equality; the construction supplies a measurable Poisson kernel defined for every nonnegative intensity, including values of zero probability. `count_given_rate` gives the same statement conditioned on the rate. None of these conditional-law proofs assumes a moment-match identity or requires positive parameters.

For the concrete geometries and positive variance/gain, `projected_count_laws_distinct` applies the completed coefficient theorem to the actual count projections. The common background can be any nonnegative value. This theorem inherits the strict positivity assumptions needed for separation; the measure and conditional-law construction itself also covers the boundary cases.

The module compiles with 13 standard-axiom audits and no `sorryAx`. See the [validation record](../docs/validation/README.md) for fresh-kernel and separate-checker execution coverage. The maintained source set now has 45 modules and 654 audits.

This closes a joint **snapshot** model. It does not specify a time-evolving phase process, exposure-integrated intensity, detector dead time, physical calibration, or temporal independence of a real acquisition. The archive-coordinate parsing, root/testing formalization, physical validation and novelty gaps remain separate.

The [completed fresh-kernel replay](../docs/validation/joint_formal_replay.json) checked the complete imported joint-model environment from an empty kernel environment. The [separate Nanoda run](../docs/validation/nanoda_joint.json) checked the three selected conditional/marginal declarations and their 48,262-declaration dependency closure, with no typechecker errors and one recorded axiom-printing diagnostic.
