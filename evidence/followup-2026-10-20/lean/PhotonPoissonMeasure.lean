import PhotonPoissonSeries
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open MeasureTheory
open scoped NNReal

namespace PhotonPoissonMeasure

/-- The same sum-of-Dirac definition as mathlib's poissonMeasure, stated
locally to avoid importing unrelated characteristic-function/convolution code. -/
noncomputable def poissonLaw (r : ℝ≥0) : Measure ℕ :=
  Measure.sum (fun n => ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n /
    (n.factorial : ℝ)) • Measure.dirac n)

theorem poissonLaw_probability (r : ℝ≥0) : IsProbabilityMeasure (poissonLaw r) := by
  have hsum : HasSum (fun n => Real.exp (-(r : ℝ)) * (r : ℝ) ^ n /
      (n.factorial : ℝ)) 1 := by
    simpa using PhotonPoissonSeries.factorial_moment_hasSum (r : ℝ) 0
  exact HasSum.isProbabilityMeasure_sum_dirac (fun n => by positivity) hsum

theorem poissonLaw_factorial_integrable (r : ℝ≥0) (k : ℕ) :
    Integrable (fun n => (n.descFactorial k : ℝ)) (poissonLaw r) := by
  rw [poissonLaw, integrable_sum_dirac_iff (by simp)]
  convert (PhotonPoissonSeries.factorial_moment_hasSum (r : ℝ) k).summable using 1
  funext n
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp

theorem poissonLaw_factorial_moment (r : ℝ≥0) (k : ℕ) :
    (∫ n, (n.descFactorial k : ℝ) ∂poissonLaw r) = (r : ℝ) ^ k := by
  rw [poissonLaw, integral_sum_dirac (by simp)]
  calc
    _ = ∑' n : ℕ, Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ) *
        (n.descFactorial k : ℝ) := by
      apply tsum_congr
      intro n
      rw [ENNReal.toReal_ofReal (by positivity)]
      rfl
    _ = _ := (PhotonPoissonSeries.factorial_moment_hasSum (r : ℝ) k).tsum_eq

#print axioms poissonLaw_probability
#print axioms poissonLaw_factorial_integrable
#print axioms poissonLaw_factorial_moment

end PhotonPoissonMeasure
