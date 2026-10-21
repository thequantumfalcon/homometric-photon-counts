import PhotonPoissonMeasure
import PhotonMixtureBridge
import Mathlib.MeasureTheory.Measure.GiryMonad

open MeasureTheory
open scoped NNReal

namespace PhotonPoissonMixture

theorem poissonLaw_measurable : Measurable PhotonPoissonMeasure.poissonLaw := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [PhotonPoissonMeasure.poissonLaw, Measure.sum_apply _ hs,
    Measure.smul_apply, smul_eq_mul]
  apply Measurable.tsum
  intro n
  fun_prop

noncomputable def countLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (rate : Ω → ℝ≥0) : Measure ℕ :=
  μ.bind (PhotonPoissonMeasure.poissonLaw ∘ rate)

theorem countLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (rate : Ω → ℝ≥0)
    (hr : Measurable rate) : IsProbabilityMeasure (countLaw μ rate) := by
  constructor
  rw [countLaw, Measure.bind_apply MeasurableSet.univ
    (poissonLaw_measurable.comp hr).aemeasurable]
  simp only [Function.comp_apply]
  have hp : ∀ ω, PhotonPoissonMeasure.poissonLaw (rate ω) Set.univ = 1 := by
    intro ω
    let := PhotonPoissonMeasure.poissonLaw_probability (rate ω)
    exact measure_univ
  simp_rw [hp]
  simp

theorem countLaw_factorial_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (rate : Ω → ℝ≥0) (hr : Measurable rate) (k : ℕ) :
    (∫ n, (n.descFactorial k : ℝ) ∂countLaw μ rate) =
      ∫ ω, (rate ω : ℝ) ^ k ∂μ := by
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun n : ℕ => (n.descFactorial k : ℝ))
    (Filter.Eventually.of_forall fun n => Nat.cast_nonneg (n.descFactorial k))
    (by fun_prop)]
  rw [countLaw, Measure.lintegral_bind (poissonLaw_measurable.comp hr).aemeasurable
    (by fun_prop)]
  simp only [Function.comp_apply]
  have hp : ∀ ω, (∫⁻ n, ENNReal.ofReal (n.descFactorial k : ℝ)
      ∂PhotonPoissonMeasure.poissonLaw (rate ω)) = ENNReal.ofReal ((rate ω : ℝ) ^ k) := by
    intro ω
    rw [← ofReal_integral_eq_lintegral_ofReal (f := fun n : ℕ => (n.descFactorial k : ℝ))
      (PhotonPoissonMeasure.poissonLaw_factorial_integrable (rate ω) k)
      (Filter.Eventually.of_forall fun n => Nat.cast_nonneg (n.descFactorial k))]
    rw [PhotonPoissonMeasure.poissonLaw_factorial_moment]
  simp_rw [hp]
  symm
  apply integral_eq_lintegral_of_nonneg_ae
  · exact Filter.Eventually.of_forall fun ω => pow_nonneg (rate ω).coe_nonneg k
  · exact (hr.coe_nnreal_real.pow_const k).aestronglyMeasurable

theorem countLaw_factorial_tower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (rate : Ω → ℝ≥0) (hr : Measurable rate) (k : ℕ) :
    (∫ n, (n.descFactorial k : ℝ) ∂countLaw μ rate) =
      ∫ ω, (∫ n, (n.descFactorial k : ℝ)
        ∂PhotonPoissonMeasure.poissonLaw (rate ω)) ∂μ := by
  simp_rw [PhotonPoissonMeasure.poissonLaw_factorial_moment]
  exact countLaw_factorial_moment μ rate hr k

/-- The prior count-law distinction theorem for constructed measurable mixtures.
The tower identities are proved above, not supplied as assumptions here. -/
theorem count_gap_from_mixtures
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (I : Ω → ℝ) (J : Ξ → ℝ)
    (rateI : Ω → ℝ≥0) (rateJ : Ξ → ℝ≥0)
    (hri : Measurable rateI) (hrj : Measurable rateJ) {η b s : ℝ}
    (hη : 0 < η) (hs : 0 < s)
    (rateI_eq : ∀ ω, (rateI ω : ℝ) = η * I ω + b)
    (rateJ_eq : ∀ ω, (rateJ ω : ℝ) = η * J ω + b)
    (hI : ∀ k : ℕ, k ≤ 4 → Integrable (fun ω => I ω ^ k) μ)
    (hJ : ∀ k : ℕ, k ≤ 4 → Integrable (fun ω => J ω ^ k) ν)
    (matching : ∀ k : ℕ, k ≤ 3 → (∫ ω, I ω ^ k ∂μ) = ∫ ω, J ω ^ k ∂ν)
    (intensity_gap : (∫ ω, I ω ^ 4 ∂μ) - (∫ ω, J ω ^ 4 ∂ν) =
      PhotonAlgebra.delta4 (Real.exp (-s))) :
    ((∫ n, (n.descFactorial 4 : ℝ) ∂countLaw μ rateI) -
      (∫ n, (n.descFactorial 4 : ℝ) ∂countLaw ν rateJ) =
      η ^ 4 * PhotonAlgebra.delta4 (Real.exp (-s))) ∧
      countLaw μ rateI ≠ countLaw ν rateJ := by
  exact PhotonMixtureBridge.count_gap_and_distinct_laws μ ν I J
    (countLaw μ rateI) (countLaw ν rateJ) rateI rateJ hη hs rateI_eq rateJ_eq
    hI hJ matching intensity_gap
    (countLaw_factorial_tower μ rateI hri 4)
    (countLaw_factorial_tower ν rateJ hrj 4)

#print axioms poissonLaw_measurable
#print axioms countLaw_probability
#print axioms countLaw_factorial_moment
#print axioms countLaw_factorial_tower
#print axioms count_gap_from_mixtures

end PhotonPoissonMixture
