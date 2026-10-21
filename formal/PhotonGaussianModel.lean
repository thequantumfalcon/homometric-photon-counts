import PhotonGaussianPhase
import PhotonGaussianIntensity

open MeasureTheory
open scoped NNReal

namespace PhotonGaussianModel

set_option maxHeartbeats 2000000

/-- The nonnegative detector rate for the explicitly defined phase intensity. -/
noncomputable def rate (zs : List ℂ) (η b : ℝ≥0)
    (θ : Fin zs.length → ℝ) : ℝ≥0 :=
  ⟨(η : ℝ) * PhotonIntensityBounds.listIntensity zs θ + b, by
    unfold PhotonIntensityBounds.listIntensity PhotonIntensityBounds.intensity
    positivity⟩

theorem rate_measurable (zs : List ℂ) (η b : ℝ≥0) : Measurable (rate zs η b) := by
  have hI := PhotonIntensityBounds.intensity_measurable zs.get
    (fun j (θ : Fin zs.length → ℝ) => θ j) (fun j => measurable_pi_apply j)
  unfold rate PhotonIntensityBounds.listIntensity
  exact ((measurable_const.mul hI).add measurable_const).subtype_mk

/-- Gaussian site phases followed by the already proved Poisson mixture. -/
noncomputable def countLaw (zs : List ℂ) (s η b : ℝ≥0) : Measure ℕ :=
  PhotonPoissonMixture.countLaw (PhotonGaussian.phaseLaw s) (rate zs η b)

instance countLaw_probability (zs : List ℂ) (s η b : ℝ≥0) :
    IsProbabilityMeasure (countLaw zs s η b) := by
  exact PhotonPoissonMixture.countLaw_probability _ _ (rate_measurable zs η b)

theorem factorial_moment (zs : List ℂ) (s η b : ℝ≥0) (k : ℕ) :
    (∫ n, (n.descFactorial k : ℝ) ∂countLaw zs s η b) =
      ∫ θ, ((η : ℝ) * PhotonIntensityBounds.listIntensity zs θ + b) ^ k
        ∂PhotonGaussian.phaseLaw s := by
  exact PhotonPoissonMixture.countLaw_factorial_moment _ _ (rate_measurable zs η b) k

theorem geometryA_moments_integrable (s : ℝ≥0) (k : ℕ) :
    Integrable (fun θ => PhotonIntensityBounds.listIntensity PhotonGeometry.geometryA θ ^ k)
      (PhotonGaussian.phaseLaw s) := by
  exact PhotonIntensityBounds.geometryA_power_integrable (PhotonGaussian.phaseLaw s)
    (fun j (θ : Fin PhotonGeometry.geometryA.length → ℝ) => θ j)
    (fun j => measurable_pi_apply j) k

theorem geometryB_moments_integrable (s : ℝ≥0) (k : ℕ) :
    Integrable (fun θ => PhotonIntensityBounds.listIntensity PhotonGeometry.geometryB θ ^ k)
      (PhotonGaussian.phaseLaw s) := by
  exact PhotonIntensityBounds.geometryB_power_integrable (PhotonGaussian.phaseLaw s)
    (fun j (θ : Fin PhotonGeometry.geometryB.length → ℝ) => θ j)
    (fun j => measurable_pi_apply j) k

/-- For the actual constructed Gaussian/Poisson model, only the specified
intensity-moment identities remain hypotheses of count-law distinction.
This declaration does not claim to have proved those identities. -/
theorem count_gap_of_intensity_moments (s η b : ℝ≥0) (hs : 0 < s) (hη : 0 < η)
    (matching : ∀ k : ℕ, k ≤ 3 →
      (∫ θ, PhotonIntensityBounds.listIntensity PhotonGeometry.geometryA θ ^ k
        ∂PhotonGaussian.phaseLaw s) =
      (∫ θ, PhotonIntensityBounds.listIntensity PhotonGeometry.geometryB θ ^ k
        ∂PhotonGaussian.phaseLaw s))
    (intensity_gap :
      (∫ θ, PhotonIntensityBounds.listIntensity PhotonGeometry.geometryA θ ^ 4
        ∂PhotonGaussian.phaseLaw s) -
      (∫ θ, PhotonIntensityBounds.listIntensity PhotonGeometry.geometryB θ ^ 4
        ∂PhotonGaussian.phaseLaw s) = PhotonAlgebra.delta4 (Real.exp (-(s : ℝ)))) :
    ((∫ n, (n.descFactorial 4 : ℝ) ∂countLaw PhotonGeometry.geometryA s η b) -
      (∫ n, (n.descFactorial 4 : ℝ) ∂countLaw PhotonGeometry.geometryB s η b) =
      (η : ℝ) ^ 4 * PhotonAlgebra.delta4 (Real.exp (-(s : ℝ)))) ∧
      countLaw PhotonGeometry.geometryA s η b ≠ countLaw PhotonGeometry.geometryB s η b := by
  exact PhotonPoissonMixture.count_gap_from_mixtures
    (PhotonGaussian.phaseLaw s) (PhotonGaussian.phaseLaw s)
    (PhotonIntensityBounds.listIntensity PhotonGeometry.geometryA)
    (PhotonIntensityBounds.listIntensity PhotonGeometry.geometryB)
    (rate PhotonGeometry.geometryA η b) (rate PhotonGeometry.geometryB η b)
    (rate_measurable _ η b) (rate_measurable _ η b) hη hs
    (fun _ => rfl) (fun _ => rfl)
    (fun k _ => geometryA_moments_integrable s k)
    (fun k _ => geometryB_moments_integrable s k) matching intensity_gap

#print axioms rate_measurable
#print axioms countLaw_probability
#print axioms factorial_moment
#print axioms geometryA_moments_integrable
#print axioms geometryB_moments_integrable
#print axioms count_gap_of_intensity_moments

end PhotonGaussianModel
