import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.CauSeqFilter

open scoped BigOperators

namespace PhotonPoissonSeries

set_option maxHeartbeats 800000

/- The following short bridge follows mathlib's
Analysis/SpecialFunctions/Exponential.lean (Apache-2.0), avoiding its unused
calculus imports. All dependencies here are already built locally. -/
private theorem real_exp_eq_series_exp : Real.exp = NormedSpace.exp := by
  have hc : Complex.exp = NormedSpace.exp := by
    funext x
    rw [Complex.exp, NormedSpace.exp_eq_tsum_div]
    exact tendsto_nhds_unique x.exp'.tendsto_limit
      (NormedSpace.expSeries_div_summable x).hasSum.tendsto_sum_nat
  ext x
  exact mod_cast congr_fun hc x

/-- The factorial-moment series of Poisson weights. For r >= 0 these weights
are probabilities. The algebraic identity holds for every real r. -/
theorem factorial_moment_hasSum (r : ℝ) (k : ℕ) :
    HasSum (fun n => Real.exp (-r) * r ^ n / (n.factorial : ℝ) *
      (n.descFactorial k : ℝ)) (r ^ k) := by
  have hterm (n : ℕ) :
      Real.exp (-r) * r ^ (n + k) / ((n + k).factorial : ℝ) *
        ((n + k).descFactorial k : ℝ) =
      (Real.exp (-r) * r ^ k) * (r ^ n / (n.factorial : ℝ)) := by
    have hfacNat : n.factorial * (n + k).descFactorial k = (n + k).factorial := by
      simpa using Nat.factorial_mul_descFactorial (Nat.le_add_left k n)
    have hfac : (n.factorial : ℝ) * ((n + k).descFactorial k : ℝ) =
        ((n + k).factorial : ℝ) := by exact_mod_cast hfacNat
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    have hnk : ((n + k).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    rw [pow_add, ← hfac]
    ring
  have htail : HasSum (fun n => Real.exp (-r) * r ^ (n + k) /
      ((n + k).factorial : ℝ) * ((n + k).descFactorial k : ℝ)) (r ^ k) := by
    simp_rw [hterm]
    convert (NormedSpace.expSeries_div_hasSum_exp r).mul_left
      (Real.exp (-r) * r ^ k) using 1
    rw [← real_exp_eq_series_exp]
    rw [mul_assoc, mul_left_comm (Real.exp (-r)), ← Real.exp_add]
    simp
  have hz : (∑ n ∈ Finset.range k,
      Real.exp (-r) * r ^ n / (n.factorial : ℝ) * (n.descFactorial k : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [Nat.descFactorial_of_lt (Finset.mem_range.mp hn)]
    simp
  have hall := (hasSum_nat_add_iff k (f := fun n => Real.exp (-r) * r ^ n /
    (n.factorial : ℝ) * (n.descFactorial k : ℝ))).mp htail
  simpa only [hz, add_zero] using hall

#print axioms factorial_moment_hasSum

end PhotonPoissonSeries
