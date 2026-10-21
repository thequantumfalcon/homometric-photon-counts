import Mathlib.Probability.Moments.Basic
import PhotonAlgebra
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Linarith

/-!
Focused formal bridges for the homometric photon-counts analysis.
The geometry-to-moment identity and numerical MGF certificates are explicit
hypotheses, not axioms, and their derivation is outside this file's scope.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace PhotonProofs

noncomputable def delta4 (x : ℝ) : ℝ :=
  (455015761 / 20000 : ℝ) * x ^ 4 * (1 - x) ^ 5 *
    (x ^ 3 + 3 * x ^ 2 + 6 * x + 6)

theorem delta4_pos {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    0 < delta4 x := by
  unfold delta4
  have : 0 < 1 - x := sub_pos.mpr hx1
  positivity

theorem delta4_exp_pos {s : ℝ} (hs : 0 < s) :
    0 < delta4 (Real.exp (-s)) := by
  apply delta4_pos (Real.exp_pos _)
  exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs)

def fallingFourth (n : ℕ) : ℝ := (n * (n - 1) * (n - 2) * (n - 3) : ℕ)

/-- A positive fourth factorial-moment difference excludes equality of full
count measures. The assumed identity must be proved from the physical model. -/
theorem count_laws_distinct_of_moment_identity
    (μ ν : Measure ℕ) {η s : ℝ} (hη : 0 < η) (hs : 0 < s)
    (identity : (∫ n, fallingFourth n ∂μ) - (∫ n, fallingFourth n ∂ν) =
      η ^ 4 * delta4 (Real.exp (-s))) : μ ≠ ν := by
  have hpos : 0 < η ^ 4 * delta4 (Real.exp (-s)) :=
    mul_pos (pow_pos hη _) (delta4_exp_pos hs)
  intro heq
  subst ν
  rw [sub_self] at identity
  linarith

theorem exp_neg_three_lt_one_twentieth : Real.exp (-3) < (1 / 20 : ℝ) := by
  have hseries := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 9
  have h20 : (20 : ℝ) < Real.exp 3 := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at hseries
    linarith
  rw [Real.exp_neg]
  simpa only [one_div] using
    (inv_lt_inv₀ (Real.exp_pos 3) (by norm_num : (0 : ℝ) < 20)).mpr h20

/-- Independent, measurable scores with integrable exponential and a common
one-observation MGF contraction have an exponentially small upper-tail error.
The index set need not consist of identically distributed scores. -/
theorem independent_score_error
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (s : Finset ι) {d : ℝ}
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hint : ∀ i ∈ s, Integrable (fun ω => Real.exp (X i ω)) μ)
    (hmgf : ∀ i ∈ s, mgf (X i) μ 1 ≤ 1 - d)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hbudget : 3 ≤ (s.card : ℝ) * d) :
    μ.real {ω | 0 ≤ (∑ i ∈ s, X i) ω} < 1 / 20 := by
  classical
  have hint' : Integrable (fun ω => Real.exp (1 * (∑ i ∈ s, X i) ω)) μ :=
    hindep.integrable_exp_mul_sum hmeas (by simpa using hint)
  have hmark := measure_ge_le_exp_mul_mgf (X := ∑ i ∈ s, X i) (μ := μ)
    (t := 1) 0 (by norm_num) hint'
  have hprod : (∏ i ∈ s, mgf (X i) μ 1) ≤ (1 - d) ^ s.card := by
    calc
      _ ≤ ∏ _i ∈ s, (1 - d) := Finset.prod_le_prod₀
        (fun _ _ => mgf_nonneg) hmgf
      _ = _ := by simp
  have hsingle : 1 - d ≤ Real.exp (-d) := by
    have := Real.add_one_le_exp (-d)
    linarith
  have hpowers : (1 - d) ^ s.card ≤ (Real.exp (-d)) ^ s.card :=
    pow_le_pow_left₀ (sub_nonneg.mpr hd1) hsingle _
  have hexp : (Real.exp (-d)) ^ s.card ≤ Real.exp (-3) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ mgf (∑ i ∈ s, X i) μ 1 := by simpa using hmark
    _ = ∏ i ∈ s, mgf (X i) μ 1 := hindep.mgf_sum hmeas s
    _ ≤ (1 - d) ^ s.card := hprod
    _ ≤ (Real.exp (-d)) ^ s.card := hpowers
    _ ≤ Real.exp (-3) := hexp
    _ < 1 / 20 := exp_neg_three_lt_one_twentieth

/-- The exact sample budget from the selected cutoff-12 certificate, conditional
on its per-observation MGF inequality and the stated observation assumptions. -/
theorem selected_independent_score_error
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Fin PhotonAlgebra.selectedM → Ω → ℝ)
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hint : ∀ i, Integrable (fun ω => Real.exp (X i ω)) μ)
    (hmgf : ∀ i, mgf (X i) μ 1 ≤ 1 - PhotonAlgebra.selectedD) :
    μ.real {ω | 0 ≤ (∑ i, X i) ω} < 1 / 20 := by
  apply independent_score_error X Finset.univ hindep hmeas
    (fun i _ => hint i) (fun i _ => hmgf i)
    PhotonAlgebra.selected_budget.1.le PhotonAlgebra.selected_budget.2.1
  simpa using PhotonAlgebra.selected_budget.2.2

end PhotonProofs

#print axioms PhotonProofs.delta4_pos
#print axioms PhotonProofs.delta4_exp_pos
#print axioms PhotonProofs.count_laws_distinct_of_moment_identity
#print axioms PhotonProofs.exp_neg_three_lt_one_twentieth
#print axioms PhotonProofs.independent_score_error
#print axioms PhotonProofs.selected_independent_score_error
