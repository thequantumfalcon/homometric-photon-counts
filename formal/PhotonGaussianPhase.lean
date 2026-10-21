import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate BigOperators NNReal

namespace PhotonGaussian

noncomputable def phase (x : ℝ) : ℂ := Complex.exp (x * Complex.I)

/-- Mixed powers of a phase and its conjugate depend on the integer exponent difference. -/
theorem mixed_phase_eq (x : ℝ) (a b : ℕ) :
    phase x ^ a * (conj (phase x)) ^ b =
      Complex.exp ((((a : ℝ) - (b : ℝ)) * x : ℝ) * Complex.I) := by
  simp only [phase, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    ← Complex.exp_nat_mul, ← Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_natCast]
  congr 1
  ring

/-- Each mixed phase monomial is integrable for every finite measure. -/
theorem mixed_phase_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (a b : ℕ) :
    Integrable (fun x => phase x ^ a * conj (phase x) ^ b) μ := by
  simp_rw [mixed_phase_eq]
  exact (integrable_const (1 : ℝ)).mono (by fun_prop) (by simp [Complex.norm_exp])

/-- The exact mixed moment of a zero-mean Gaussian phase with variance s. -/
theorem gaussian_mixed_phase_integral (s : ℝ≥0) (a b : ℕ) :
    (∫ x, phase x ^ a * conj (phase x) ^ b ∂gaussianReal 0 s) =
      (Real.exp (-(s : ℝ) * ((a : ℝ) - (b : ℝ)) ^ 2 / 2) : ℂ) := by
  simp_rw [mixed_phase_eq]
  simp only [Complex.ofReal_mul]
  rw [← charFun_apply_real, charFun_gaussianReal]
  simp [Complex.ofReal_exp, neg_div]

/-- Scaling a standard normal by the square root of s gives the Gaussian law with variance s. -/
theorem scaled_standard_gaussian_law (s : ℝ≥0) :
    (gaussianReal 0 1).map (fun z => Real.sqrt (s : ℝ) * z) = gaussianReal 0 s := by
  have hs : NNReal.mk ((Real.sqrt (s : ℝ)) ^ 2) (sq_nonneg _) = s := by
    apply Subtype.ext
    exact Real.sq_sqrt s.property
  simpa only [mul_zero, mul_one, hs] using
    (gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt (s : ℝ)))

/-- The same mixed phase moment in the original standard-normal notation exp(i sqrt(s) Z). -/
theorem standard_gaussian_mixed_phase_integral (s : ℝ≥0) (a b : ℕ) :
    (∫ z, phase (Real.sqrt (s : ℝ) * z) ^ a *
      conj (phase (Real.sqrt (s : ℝ) * z)) ^ b ∂gaussianReal 0 1) =
      (Real.exp (-(s : ℝ) * ((a : ℝ) - (b : ℝ)) ^ 2 / 2) : ℂ) := by
  rw [← gaussian_mixed_phase_integral s a b, ← scaled_standard_gaussian_law s]
  rw [integral_map (by fun_prop) (by unfold phase; fun_prop)]

/-- The probability space explicitly used for finitely many independent site phases. -/
noncomputable def phaseLaw {ι : Type*} [Fintype ι] (s : ℝ≥0) : Measure (ι → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 s)

instance phaseLaw_probability {ι : Type*} [Fintype ι] (s : ℝ≥0) :
    IsProbabilityMeasure (phaseLaw (ι := ι) s) := by
  unfold phaseLaw
  infer_instance

theorem phase_product_integrable {ι : Type*} [Fintype ι]
    (s : ℝ≥0) (a b : ι → ℕ) :
    Integrable (fun x : ι → ℝ => ∏ i, phase (x i) ^ a i * conj (phase (x i)) ^ b i)
      (phaseLaw s) := by
  exact Integrable.fintype_prod (fun i => mixed_phase_integrable _ (a i) (b i))

/-- Independent Gaussian phases give the product of the exact single-site moments. -/
theorem gaussian_phase_product_integral {ι : Type*} [Fintype ι]
    (s : ℝ≥0) (a b : ι → ℕ) :
    (∫ x : ι → ℝ, ∏ i, phase (x i) ^ a i * conj (phase (x i)) ^ b i ∂phaseLaw s) =
      ∏ i, (Real.exp (-(s : ℝ) * ((a i : ℝ) - (b i : ℝ)) ^ 2 / 2) : ℂ) := by
  unfold phaseLaw
  rw [integral_fintype_prod_eq_prod (fun i x => phase x ^ a i * conj (phase x) ^ b i)]
  simp_rw [gaussian_mixed_phase_integral]

/-- The complete finite Gaussian monomial rule used by phase-moment reconstruction. -/
theorem gaussian_phase_monomial_integral {ι : Type*} [Fintype ι]
    (s : ℝ≥0) (a b : ι → ℕ) :
    (∫ x : ι → ℝ, ∏ i, phase (x i) ^ a i * conj (phase (x i)) ^ b i ∂phaseLaw s) =
      (Real.exp (-(s : ℝ) / 2 * ∑ i, ((a i : ℝ) - (b i : ℝ)) ^ 2) : ℂ) := by
  rw [gaussian_phase_product_integral]
  push_cast
  rw [← Complex.exp_sum]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Constant complex geometry factors pass through the Gaussian monomial integral. -/
theorem gaussian_weighted_monomial_integral {ι : Type*} [Fintype ι]
    (s : ℝ≥0) (a b : ι → ℕ) (c : ℂ) :
    (∫ x : ι → ℝ, c * ∏ i, phase (x i) ^ a i * conj (phase (x i)) ^ b i ∂phaseLaw s) =
      c * (Real.exp (-(s : ℝ) / 2 * ∑ i, ((a i : ℝ) - (b i : ℝ)) ^ 2) : ℂ) := by
  rw [integral_const_mul, gaussian_phase_monomial_integral]

/-- A finite phase polynomial is integrable without a separate moment hypothesis. -/
theorem phase_polynomial_integrable {ι κ : Type*} [Fintype ι] [Fintype κ]
    (s : ℝ≥0) (a b : κ → ι → ℕ) (c : κ → ℂ) :
    Integrable (fun x : ι → ℝ =>
      ∑ j, c j * ∏ i, phase (x i) ^ a j i * conj (phase (x i)) ^ b j i) (phaseLaw s) := by
  exact integrable_finsetSum _ (fun j _ => (phase_product_integrable s (a j) (b j)).const_mul (c j))

/-- Exact expectation of an arbitrary finite polynomial in independent Gaussian phases and their
conjugates. It can be applied to a separately established finite intensity expansion. -/
theorem gaussian_phase_polynomial_integral {ι κ : Type*} [Fintype ι] [Fintype κ]
    (s : ℝ≥0) (a b : κ → ι → ℕ) (c : κ → ℂ) :
    (∫ x : ι → ℝ, ∑ j, c j * ∏ i,
      phase (x i) ^ a j i * conj (phase (x i)) ^ b j i ∂phaseLaw s) =
      ∑ j, c j * (Real.exp (-(s : ℝ) / 2 *
        ∑ i, ((a j i : ℝ) - (b j i : ℝ)) ^ 2) : ℂ) := by
  rw [integral_finsetSum _ (fun j _ => (phase_product_integrable s (a j) (b j)).const_mul (c j))]
  simp_rw [gaussian_weighted_monomial_integral]

#print axioms mixed_phase_eq
#print axioms mixed_phase_integrable
#print axioms gaussian_mixed_phase_integral
#print axioms scaled_standard_gaussian_law
#print axioms standard_gaussian_mixed_phase_integral
#print axioms phaseLaw_probability
#print axioms phase_product_integrable
#print axioms gaussian_phase_product_integral
#print axioms gaussian_phase_monomial_integral
#print axioms gaussian_weighted_monomial_integral
#print axioms phase_polynomial_integrable
#print axioms gaussian_phase_polynomial_integral

end PhotonGaussian
