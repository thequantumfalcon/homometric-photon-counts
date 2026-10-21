import PhotonMomentTransfer
import PhotonPoissonMeasure
import PhotonAlgebra
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

open MeasureTheory
open scoped NNReal

namespace PhotonMixtureBridge

/-- Integrating the proved Poisson factorial series gives the rate moment.
This pointwise replacement does not assert a mixture/Tonelli interchange. -/
theorem integrated_factorial_series
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (rate : Ω → ℝ) (k : ℕ) :
    (∫ ω, (∑' n : ℕ, Real.exp (-rate ω) * rate ω ^ n / (n.factorial : ℝ) *
      (n.descFactorial k : ℝ)) ∂μ) = ∫ ω, rate ω ^ k ∂μ := by
  apply integral_congr_ae
  filter_upwards with ω
  exact (PhotonPoissonSeries.factorial_moment_hasSum (rate ω) k).tsum_eq

/-- Starting from the explicit mixture/tower identities and the first three
intensity-moment matches, derive the count fourth-factorial gap and unequal
full count laws. The final gap is a conclusion, not an input hypothesis. -/
theorem count_gap_and_distinct_laws
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (I : Ω → ℝ) (J : Ξ → ℝ) (A B : Measure ℕ)
    (rateI : Ω → ℝ≥0) (rateJ : Ξ → ℝ≥0) {η b s : ℝ}
    (hη : 0 < η) (hs : 0 < s)
    (rateI_eq : ∀ ω, (rateI ω : ℝ) = η * I ω + b)
    (rateJ_eq : ∀ ω, (rateJ ω : ℝ) = η * J ω + b)
    (hI : ∀ k : ℕ, k ≤ 4 → Integrable (fun ω => I ω ^ k) μ)
    (hJ : ∀ k : ℕ, k ≤ 4 → Integrable (fun ω => J ω ^ k) ν)
    (matching : ∀ k : ℕ, k ≤ 3 → (∫ ω, I ω ^ k ∂μ) = ∫ ω, J ω ^ k ∂ν)
    (intensity_gap : (∫ ω, I ω ^ 4 ∂μ) - (∫ ω, J ω ^ 4 ∂ν) =
      PhotonAlgebra.delta4 (Real.exp (-s)))
    (mixture_A : (∫ n, (n.descFactorial 4 : ℝ) ∂A) =
      ∫ ω, (∫ n, (n.descFactorial 4 : ℝ)
        ∂PhotonPoissonMeasure.poissonLaw (rateI ω)) ∂μ)
    (mixture_B : (∫ n, (n.descFactorial 4 : ℝ) ∂B) =
      ∫ ω, (∫ n, (n.descFactorial 4 : ℝ)
        ∂PhotonPoissonMeasure.poissonLaw (rateJ ω)) ∂ν) :
    ((∫ n, (n.descFactorial 4 : ℝ) ∂A) - (∫ n, (n.descFactorial 4 : ℝ) ∂B) =
      η ^ 4 * PhotonAlgebra.delta4 (Real.exp (-s))) ∧ A ≠ B := by
  have hI1 : Integrable I μ := by simpa using hI 1 (by norm_num)
  have hJ1 : Integrable J ν := by simpa using hJ 1 (by norm_num)
  have hm1 : (∫ ω, I ω ∂μ) = ∫ ω, J ω ∂ν := by
    simpa using matching 1 (by norm_num)
  have hgap := PhotonMomentTransfer.common_background_cancellation μ ν I J η b
    hI1 (hI 2 (by norm_num)) (hI 3 (by norm_num)) (hI 4 (by norm_num))
    hJ1 (hJ 2 (by norm_num)) (hJ 3 (by norm_num)) (hJ 4 (by norm_num))
    hm1 (matching 2 (by norm_num)) (matching 3 (by norm_num))
  simp_rw [PhotonPoissonMeasure.poissonLaw_factorial_moment, rateI_eq] at mixture_A
  simp_rw [PhotonPoissonMeasure.poissonLaw_factorial_moment, rateJ_eq] at mixture_B
  rw [← mixture_A, ← mixture_B, intensity_gap] at hgap
  refine ⟨hgap, ?_⟩
  have hpos : 0 < η ^ 4 * PhotonAlgebra.delta4 (Real.exp (-s)) :=
    mul_pos (pow_pos hη _) (PhotonAlgebra.delta4_pos (Real.exp_pos _)
      (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs)))
  intro heq
  rw [heq, sub_self] at hgap
  linarith

#print axioms integrated_factorial_series
#print axioms count_gap_and_distinct_laws

end PhotonMixtureBridge
