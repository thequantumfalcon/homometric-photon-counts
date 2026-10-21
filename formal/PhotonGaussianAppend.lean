import PhotonGaussianModel

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace PhotonGaussianAppend

open PhotonGaussian PhotonIntensityBounds

theorem field_snoc {n : ℕ} (z : Fin n → ℂ) (w : ℂ) (θ : Fin n → ℝ) (y : ℝ) :
    field (Fin.snoc z w) (Fin.snoc θ y) = field z θ + w * phase y := by
  unfold field phase
  rw [Fin.sum_univ_castSucc]
  simp [mul_comm]

theorem phaseLaw_integral_snoc {n : ℕ} (s : ℝ≥0) (F : (Fin (n + 1) → ℝ) → ℂ) :
    (∫ x, F x ∂phaseLaw s) =
      ∫ p : (Fin n → ℝ) × ℝ, F (Fin.snoc p.1 p.2)
        ∂(phaseLaw s).prod (gaussianReal 0 s) := by
  have h := ((measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => gaussianReal 0 s) (Fin.last n)).symm).integral_comp' F
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv_last] at h
  unfold phaseLaw
  rw [← h]
  exact integral_prod_swap (fun p : (Fin n → ℝ) × ℝ => F (Fin.snoc p.1 p.2))

#print axioms field_snoc
#print axioms phaseLaw_integral_snoc

end PhotonGaussianAppend
