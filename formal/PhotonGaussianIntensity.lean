import PhotonIntensityExpansion
import PhotonGaussianPhase

open MeasureTheory
open scoped BigOperators ComplexConjugate NNReal

namespace PhotonGaussianIntensity

open PhotonIntensityExpansion
open PhotonIntensityBounds
open PhotonGaussian

theorem intensity_phase_expansion {n : ℕ} (z : Fin n → ℂ) (x : Fin n → ℝ) (k : ℕ) :
    (intensity z x : ℂ) ^ k =
      ∑ f : Fin k → Fin n, ∑ g : Fin k → Fin n,
        coefficient z f g * ∏ j,
          phase (x j) ^ occupancy f j * conj (phase (x j)) ^ occupancy g j := by
  simpa only [phase, mul_comm, starRingEnd_apply] using intensity_power_expansion z x k

theorem gaussian_intensity_power_integrable {n : ℕ} (z : Fin n → ℂ) (s : ℝ≥0) (k : ℕ) :
    Integrable (fun x : Fin n → ℝ => intensity z x ^ k) (phaseLaw s) := by
  have hint (f g : Fin k → Fin n) : Integrable (fun x : Fin n → ℝ =>
      coefficient z f g * ∏ j, phase (x j) ^ occupancy f j *
        conj (phase (x j)) ^ occupancy g j) (phaseLaw s) :=
    (phase_product_integrable s (occupancy f) (occupancy g)).const_mul (coefficient z f g)
  have hpoly := integrable_finsetSum Finset.univ
    (fun f _ => integrable_finsetSum Finset.univ (fun g _ => hint f g))
  have hcomplex : Integrable (fun x : Fin n → ℝ => ((intensity z x ^ k : ℝ) : ℂ))
      (phaseLaw s) := by
    simpa only [Complex.ofReal_pow, intensity_phase_expansion] using hpoly
  have hreal := hcomplex.re
  change Integrable (fun x : Fin n → ℝ => (((intensity z x ^ k : ℝ) : ℂ)).re)
    (phaseLaw s) at hreal
  simpa only [Complex.ofReal_re] using hreal

theorem gaussian_intensity_moment {n : ℕ} (z : Fin n → ℂ) (s : ℝ≥0) (k : ℕ) :
    ((∫ x : Fin n → ℝ, intensity z x ^ k ∂phaseLaw s : ℝ) : ℂ) =
      ∑ f : Fin k → Fin n, ∑ g : Fin k → Fin n,
        coefficient z f g * (Real.exp (-(s : ℝ) / 2 *
          ∑ j, ((occupancy f j : ℝ) - (occupancy g j : ℝ)) ^ 2) : ℂ) := by
  rw [← integral_complex_ofReal]
  simp only [Complex.ofReal_pow, intensity_phase_expansion]
  have hint (f g : Fin k → Fin n) : Integrable (fun x : Fin n → ℝ =>
      coefficient z f g * ∏ j, phase (x j) ^ occupancy f j *
        conj (phase (x j)) ^ occupancy g j) (phaseLaw s) :=
    (phase_product_integrable s (occupancy f) (occupancy g)).const_mul (coefficient z f g)
  rw [integral_finsetSum _ (fun f _ => integrable_finsetSum _ (fun g _ => hint f g))]
  apply Finset.sum_congr rfl
  intro f hf
  rw [integral_finsetSum _ (fun g _ => hint f g)]
  apply Finset.sum_congr rfl
  intro g hg
  exact gaussian_weighted_monomial_integral s (occupancy f) (occupancy g) (coefficient z f g)

#print axioms intensity_phase_expansion
#print axioms gaussian_intensity_power_integrable
#print axioms gaussian_intensity_moment

end PhotonGaussianIntensity
