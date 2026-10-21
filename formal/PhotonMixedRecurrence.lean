import PhotonGaussianModel
import PhotonGaussianAppend

open MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate NNReal

namespace PhotonMixedRecurrence

open PhotonGaussian PhotonIntensityBounds

theorem field_norm_general {n : ℕ} (z : Fin n → ℂ) (θ : Fin n → ℝ) :
    ‖field z θ‖ ≤ ∑ j, ‖z j‖ := by
  calc
    _ ≤ ∑ j, ‖z j * Complex.exp (Complex.I * (θ j : ℂ))‖ := norm_sum_le _ _
    _ = _ := by simp

theorem mixed_integrable {n : ℕ} (z : Fin n → ℂ)
    (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] (a b : ℕ) :
    Integrable (fun θ => field z θ ^ a * star (field z θ) ^ b) μ := by
  apply (integrable_const ((∑ j, ‖z j‖) ^ (a + b))).mono'
    (by unfold field; fun_prop)
  apply Filter.Eventually.of_forall
  intro θ
  simp only [norm_mul, norm_pow, norm_star, ← pow_add]
  exact pow_le_pow_left₀ (norm_nonneg _) (field_norm_general z θ) (a + b)

theorem mixed_add_expansion (A B : ℂ) (a b : ℕ) :
    (A + B) ^ a * star (A + B) ^ b =
      ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        (a.choose i : ℂ) * (b.choose j : ℂ) *
          (A ^ (a-i) * star A ^ (b-j)) * (B ^ i * star B ^ j) := by
  rw [star_add, add_comm A B, add_pow, add_comm (star A) (star B), add_pow]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

noncomputable def mixedMoment {n : ℕ} (z : Fin n → ℂ) (s : ℝ≥0) (a b : ℕ) : ℂ :=
  ∫ θ, field z θ ^ a * star (field z θ) ^ b ∂phaseLaw s

theorem gaussian_append_product {n : ℕ} (z : Fin n → ℂ) (w : ℂ)
    (s : ℝ≥0) (a b : ℕ) :
    (∫ p : (Fin n → ℝ) × ℝ,
      (field z p.1 + w * phase p.2) ^ a * star (field z p.1 + w * phase p.2) ^ b
        ∂(phaseLaw s).prod (gaussianReal 0 s)) =
      ∑ i ∈ Finset.range (a+1), ∑ j ∈ Finset.range (b+1),
        (a.choose i : ℂ) * (b.choose j : ℂ) * mixedMoment z s (a-i) (b-j) *
          (w ^ i * star w ^ j) *
            (Real.exp (-(s : ℝ) * ((i : ℝ) - (j : ℝ)) ^ 2 / 2) : ℂ) := by
  have heq (p : (Fin n → ℝ) × ℝ) :
      (field z p.1 + w * phase p.2) ^ a * star (field z p.1 + w * phase p.2) ^ b =
        ∑ i ∈ Finset.range (a+1), ∑ j ∈ Finset.range (b+1),
          ((a.choose i : ℂ) * (b.choose j : ℂ) * (w ^ i * star w ^ j)) *
            ((field z p.1 ^ (a-i) * star (field z p.1) ^ (b-j)) *
              (phase p.2 ^ i * conj (phase p.2) ^ j)) := by
    rw [mixed_add_expansion]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp only [mul_pow, star_mul, starRingEnd_apply]
    ring
  simp_rw [heq]
  have hint (i j : ℕ) : Integrable (fun p : (Fin n → ℝ) × ℝ =>
      ((a.choose i : ℂ) * (b.choose j : ℂ) * (w ^ i * star w ^ j)) *
        ((field z p.1 ^ (a-i) * star (field z p.1) ^ (b-j)) *
          (phase p.2 ^ i * conj (phase p.2) ^ j)))
      ((phaseLaw s).prod (gaussianReal 0 s)) :=
    ((mixed_integrable z (phaseLaw s) (a-i) (b-j)).mul_prod
      (mixed_phase_integrable (gaussianReal 0 s) i j)).const_mul _
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul,
    integral_prod_mul (fun θ => field z θ ^ (a-i) * star (field z θ) ^ (b-j))
      (fun y => phase y ^ i * conj (phase y) ^ j),
    gaussian_mixed_phase_integral]
  unfold mixedMoment
  ring

theorem gaussian_append_recurrence {n : ℕ} (z : Fin n → ℂ) (w : ℂ)
    (s : ℝ≥0) (a b : ℕ) :
    mixedMoment (Fin.snoc z w) s a b =
      ∑ i ∈ Finset.range (a+1), ∑ j ∈ Finset.range (b+1),
        (a.choose i : ℂ) * (b.choose j : ℂ) * mixedMoment z s (a-i) (b-j) *
          (w ^ i * star w ^ j) *
            (Real.exp (-(s : ℝ) * ((i : ℝ) - (j : ℝ)) ^ 2 / 2) : ℂ) := by
  unfold mixedMoment
  rw [PhotonGaussianAppend.phaseLaw_integral_snoc]
  simp_rw [PhotonGaussianAppend.field_snoc]
  exact gaussian_append_product z w s a b

noncomputable def recurrence : (n : ℕ) → (Fin n → ℂ) → ℝ≥0 → ℕ → ℕ → ℂ
  | 0, _, _, a, b => 0 ^ a * 0 ^ b
  | n+1, z, s, a, b =>
      ∑ i ∈ Finset.range (a+1), ∑ j ∈ Finset.range (b+1),
        (a.choose i : ℂ) * (b.choose j : ℂ) * recurrence n (Fin.init z) s (a-i) (b-j) *
          (z (Fin.last n) ^ i * star (z (Fin.last n)) ^ j) *
            (Real.exp (-(s : ℝ) * ((i : ℝ) - (j : ℝ)) ^ 2 / 2) : ℂ)

theorem recurrence_eq_mixedMoment (n : ℕ) (z : Fin n → ℂ) (s : ℝ≥0) (a b : ℕ) :
    recurrence n z s a b = mixedMoment z s a b := by
  induction n generalizing a b with
  | zero => simp [recurrence, mixedMoment, field]
  | succ n ih =>
    rw [← Fin.snoc_init_self z, gaussian_append_recurrence]
    simp only [recurrence, Fin.init_snoc, Fin.snoc_last]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih]

theorem recurrence_eq_real_intensity (n : ℕ) (z : Fin n → ℂ) (s : ℝ≥0) (k : ℕ) :
    recurrence n z s k k = ((∫ θ, intensity z θ ^ k ∂phaseLaw s : ℝ) : ℂ) := by
  rw [recurrence_eq_mixedMoment, mixedMoment, ← integral_complex_ofReal]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro θ
  dsimp only
  rw [Complex.ofReal_pow, intensity_complex, mul_pow]

#print axioms field_norm_general
#print axioms mixed_integrable
#print axioms mixed_add_expansion
#print axioms gaussian_append_product
#print axioms gaussian_append_recurrence
#print axioms recurrence_eq_mixedMoment
#print axioms recurrence_eq_real_intensity

end PhotonMixedRecurrence
