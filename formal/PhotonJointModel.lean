import PhotonConcreteSeparation
import Mathlib.Probability.HasCondDistrib

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PhotonJointModel

noncomputable def poissonKernel : Kernel ℝ≥0 ℕ :=
  ⟨PhotonPoissonMeasure.poissonLaw, PhotonPoissonMixture.poissonLaw_measurable⟩

instance poissonKernel_markov : IsMarkovKernel poissonKernel where
  isProbabilityMeasure r := PhotonPoissonMeasure.poissonLaw_probability r

noncomputable def detectorKernel (zs : List ℂ) (η b : ℝ≥0) :
    Kernel (Fin zs.length → ℝ) ℕ :=
  poissonKernel.comap (PhotonGaussianModel.rate zs η b)
    (PhotonGaussianModel.rate_measurable zs η b)

instance detectorKernel_markov (zs : List ℂ) (η b : ℝ≥0) :
    IsMarkovKernel (detectorKernel zs η b) := by
  unfold detectorKernel
  infer_instance

/-- A single snapshot containing the Gaussian phases and the sampled count. -/
noncomputable def jointLaw (zs : List ℂ) (s η b : ℝ≥0) :
    Measure ((Fin zs.length → ℝ) × ℕ) :=
  PhotonGaussian.phaseLaw s ⊗ₘ detectorKernel zs η b

instance jointLaw_probability (zs : List ℂ) (s η b : ℝ≥0) :
    IsProbabilityMeasure (jointLaw zs s η b) := by
  unfold jointLaw
  infer_instance

theorem phase_marginal (zs : List ℂ) (s η b : ℝ≥0) :
    (jointLaw zs s η b).map Prod.fst = PhotonGaussian.phaseLaw s := by
  exact Measure.fst_compProd _ _

theorem count_marginal (zs : List ℂ) (s η b : ℝ≥0) :
    (jointLaw zs s η b).map Prod.snd = PhotonGaussianModel.countLaw zs s η b := by
  change (PhotonGaussian.phaseLaw s ⊗ₘ detectorKernel zs η b).snd = _
  rw [Measure.snd_compProd]
  rfl

theorem joint_rectangle (zs : List ℂ) (s η b : ℝ≥0)
    (A : Set (Fin zs.length → ℝ)) (B : Set ℕ)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    jointLaw zs s η b (A ×ˢ B) =
      ∫⁻ θ in A, PhotonPoissonMeasure.poissonLaw (PhotonGaussianModel.rate zs η b θ) B
        ∂PhotonGaussian.phaseLaw s := by
  exact Measure.compProd_apply_prod hA hB

theorem count_given_phases (zs : List ℂ) (s η b : ℝ≥0) :
    HasCondDistrib Prod.snd Prod.fst (detectorKernel zs η b) (jointLaw zs s η b) := by
  constructor
  · exact measurable_id.aemeasurable
  · change (jointLaw zs s η b).map id = _
    rw [Measure.map_id, phase_marginal]
    rfl

theorem count_given_rate (zs : List ℂ) (s η b : ℝ≥0) :
    HasCondDistrib Prod.snd (fun ω => PhotonGaussianModel.rate zs η b ω.1)
      poissonKernel (jointLaw zs s η b) := by
  exact HasCondDistrib.comp_right (count_given_phases zs s η b)

noncomputable def intensityValue (zs : List ℂ) (θ : Fin zs.length → ℝ) : ℝ≥0 :=
  ⟨PhotonIntensityBounds.listIntensity zs θ, by
    unfold PhotonIntensityBounds.listIntensity PhotonIntensityBounds.intensity
    positivity⟩

theorem intensityValue_measurable (zs : List ℂ) : Measurable (intensityValue zs) := by
  have h := PhotonIntensityBounds.intensity_measurable zs.get
    (fun j (θ : Fin zs.length → ℝ) => θ j) (fun j => measurable_pi_apply j)
  exact h.subtype_mk

noncomputable def intensityKernel (η b : ℝ≥0) : Kernel ℝ≥0 ℕ :=
  poissonKernel.comap (fun I : ℝ≥0 => η * I + b) (by fun_prop)

instance intensityKernel_markov (η b : ℝ≥0) : IsMarkovKernel (intensityKernel η b) := by
  unfold intensityKernel
  infer_instance

theorem detectorKernel_factor (zs : List ℂ) (η b : ℝ≥0) :
    detectorKernel zs η b =
      (intensityKernel η b).comap (intensityValue zs) (intensityValue_measurable zs) := by
  rfl

theorem count_given_intensity (zs : List ℂ) (s η b : ℝ≥0) :
    HasCondDistrib Prod.snd (fun ω => intensityValue zs ω.1)
      (intensityKernel η b) (jointLaw zs s η b) := by
  have h := count_given_phases zs s η b
  rw [detectorKernel_factor] at h
  exact HasCondDistrib.comp_right h

/-- The earlier count-law separation applies to actual count projections of the joint models. -/
theorem projected_count_laws_distinct (s η b : ℝ≥0) (hs : 0 < s) (hη : 0 < η) :
    (jointLaw PhotonGeometry.geometryA s η b).map Prod.snd ≠
      (jointLaw PhotonGeometry.geometryB s η b).map Prod.snd := by
  rw [count_marginal, count_marginal]
  exact (PhotonConcreteSeparation.count_laws_distinct s η b hs hη).2

#print axioms poissonKernel_markov
#print axioms detectorKernel_markov
#print axioms jointLaw_probability
#print axioms phase_marginal
#print axioms count_marginal
#print axioms joint_rectangle
#print axioms count_given_phases
#print axioms count_given_rate
#print axioms intensityValue_measurable
#print axioms intensityKernel_markov
#print axioms detectorKernel_factor
#print axioms count_given_intensity
#print axioms projected_count_laws_distinct

end PhotonJointModel
