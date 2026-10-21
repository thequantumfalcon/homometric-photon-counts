import PhotonCertABlock63
import PhotonCertBBlock63
import PhotonConcreteTransfer
import PhotonConcreteVectors

open MeasureTheory
open scoped NNReal Polynomial
namespace PhotonConcreteSeparation
open PhotonMomentPolynomial PhotonIntensityBounds PhotonGaussian PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

theorem A_vector : PhotonCertA.z63 = geometryA.get := by
  change PhotonConcreteVectors.A63 = geometryA.get
  exact PhotonConcreteVectors.A_binding

theorem B_vector : PhotonCertB.z63 = geometryB.get := by
  change PhotonConcreteVectors.B63 = geometryB.get
  exact PhotonConcreteVectors.B_binding

theorem difference_0 (t : ℂ) :
    (momentPoly geometryA.length geometryA.get 0 0).eval t -
      (momentPoly geometryB.length geometryB.get 0 0).eval t = 0 := by
  change (momentPoly 63 geometryA.get 0 0).eval t -
    (momentPoly 63 geometryB.get 0 0).eval t = 0
  rw [← A_vector, ← B_vector, PhotonCertA.v63_00, PhotonCertB.v63_00]
  ring

theorem difference_1 (t : ℂ) :
    (momentPoly geometryA.length geometryA.get 1 1).eval t -
      (momentPoly geometryB.length geometryB.get 1 1).eval t = 0 := by
  change (momentPoly 63 geometryA.get 1 1).eval t -
    (momentPoly 63 geometryB.get 1 1).eval t = 0
  rw [← A_vector, ← B_vector, PhotonCertA.v63_11, PhotonCertB.v63_11]
  ring

theorem difference_2 (t : ℂ) :
    (momentPoly geometryA.length geometryA.get 2 2).eval t -
      (momentPoly geometryB.length geometryB.get 2 2).eval t = 0 := by
  change (momentPoly 63 geometryA.get 2 2).eval t -
    (momentPoly 63 geometryB.get 2 2).eval t = 0
  rw [← A_vector, ← B_vector, PhotonCertA.v63_22, PhotonCertB.v63_22]
  ring

theorem difference_3 (t : ℂ) :
    (momentPoly geometryA.length geometryA.get 3 3).eval t -
      (momentPoly geometryB.length geometryB.get 3 3).eval t = 0 := by
  change (momentPoly 63 geometryA.get 3 3).eval t -
    (momentPoly 63 geometryB.get 3 3).eval t = 0
  rw [← A_vector, ← B_vector, PhotonCertA.v63_33, PhotonCertB.v63_33]
  ring

theorem difference_4 (t : ℂ) :
    (momentPoly geometryA.length geometryA.get 4 4).eval t -
      (momentPoly geometryB.length geometryB.get 4 4).eval t = (455015761 / 20000 : ℂ) * t ^ 8 * (1 - t ^ 2) ^ 5 * (t ^ 6 + 3 * t ^ 4 + 6 * t ^ 2 + 6) := by
  change (momentPoly 63 geometryA.get 4 4).eval t -
    (momentPoly 63 geometryB.get 4 4).eval t = (455015761 / 20000 : ℂ) * t ^ 8 * (1 - t ^ 2) ^ 5 * (t ^ 6 + 3 * t ^ 4 + 6 * t ^ 2 + 6)
  rw [← A_vector, ← B_vector, PhotonCertA.v63_44, PhotonCertB.v63_44]
  ring

theorem intensity_matching (s : ℝ≥0) (k : ℕ) (hk : k ≤ 3) :
    (∫ θ, listIntensity geometryA θ ^ k ∂phaseLaw s) =
      (∫ θ, listIntensity geometryB θ ^ k ∂phaseLaw s) := by
  apply sub_eq_zero.mp
  apply PhotonConcreteTransfer.intensity_difference_of_eval
  have hkcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hkcases with rfl | rfl | rfl | rfl
  · exact difference_0 _
  · exact difference_1 _
  · exact difference_2 _
  · exact difference_3 _

theorem intensity_gap (s : ℝ≥0) :
    (∫ θ, listIntensity geometryA θ ^ 4 ∂phaseLaw s) -
      (∫ θ, listIntensity geometryB θ ^ 4 ∂phaseLaw s) =
        PhotonAlgebra.delta4 (Real.exp (-(s : ℝ))) := by
  exact PhotonConcreteTransfer.fourth_difference_of_eval s difference_4

/-- Count-law distinction for the explicit 63-site model, with no assumed
concrete moment values. This is a mathematical model theorem, not an experiment. -/
theorem count_laws_distinct (s η b : ℝ≥0) (hs : 0 < s) (hη : 0 < η) :
    ((∫ n, (n.descFactorial 4 : ℝ)
        ∂PhotonGaussianModel.countLaw geometryA s η b) -
      (∫ n, (n.descFactorial 4 : ℝ)
        ∂PhotonGaussianModel.countLaw geometryB s η b) =
      (η : ℝ) ^ 4 * PhotonAlgebra.delta4 (Real.exp (-(s : ℝ)))) ∧
      PhotonGaussianModel.countLaw geometryA s η b ≠
        PhotonGaussianModel.countLaw geometryB s η b := by
  exact PhotonGaussianModel.count_gap_of_intensity_moments s η b hs hη
    (intensity_matching s) (intensity_gap s)

#print axioms A_vector
#print axioms B_vector
#print axioms difference_0
#print axioms difference_1
#print axioms difference_2
#print axioms difference_3
#print axioms difference_4
#print axioms intensity_matching
#print axioms intensity_gap
#print axioms count_laws_distinct

end PhotonConcreteSeparation
