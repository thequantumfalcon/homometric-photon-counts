import PhotonMomentPolynomial

open MeasureTheory
open scoped NNReal Polynomial

namespace PhotonConcreteTransfer

open PhotonMomentPolynomial PhotonIntensityBounds PhotonGaussian PhotonGeometry

/-- This generic transfer consumes an exact polynomial evaluation identity.
The concrete certificates must discharge that hypothesis separately. -/
theorem intensity_difference_of_eval (zs ws : List ℂ) (s : ℝ≥0) (k : ℕ) (D : ℝ)
    (h : (momentPoly zs.length zs.get k k).eval (Real.exp (-(s : ℝ) / 2) : ℂ) -
      (momentPoly ws.length ws.get k k).eval (Real.exp (-(s : ℝ) / 2) : ℂ) = (D : ℂ)) :
    (∫ θ, listIntensity zs θ ^ k ∂phaseLaw s) -
      (∫ θ, listIntensity ws θ ^ k ∂phaseLaw s) = D := by
  rw [eval_momentPoly_intensity, eval_momentPoly_intensity] at h
  exact_mod_cast h

theorem fourth_difference_of_eval (s : ℝ≥0)
    (h : ∀ t : ℂ,
      (momentPoly geometryA.length geometryA.get 4 4).eval t -
        (momentPoly geometryB.length geometryB.get 4 4).eval t =
          (455015761 / 20000 : ℂ) * t ^ 8 * (1 - t ^ 2) ^ 5 *
            (t ^ 6 + 3 * t ^ 4 + 6 * t ^ 2 + 6)) :
    (∫ θ, listIntensity geometryA θ ^ 4 ∂phaseLaw s) -
      (∫ θ, listIntensity geometryB θ ^ 4 ∂phaseLaw s) =
        PhotonAlgebra.delta4 (Real.exp (-(s : ℝ))) := by
  apply intensity_difference_of_eval
  rw [gap_parameter_substitution]
  push_cast
  exact h _

#print axioms intensity_difference_of_eval
#print axioms fourth_difference_of_eval

end PhotonConcreteTransfer
