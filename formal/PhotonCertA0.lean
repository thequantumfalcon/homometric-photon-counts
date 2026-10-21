import PhotonMomentPolynomial
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z0 : Fin 0 → ℂ := Fin.elim0
theorem v0_00 (t : ℂ) : (momentPoly 0 z0 0 0).eval t = (1) := by
  norm_num [momentPoly]
theorem v0_01 (t : ℂ) : (momentPoly 0 z0 0 1).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_02 (t : ℂ) : (momentPoly 0 z0 0 2).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_03 (t : ℂ) : (momentPoly 0 z0 0 3).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_04 (t : ℂ) : (momentPoly 0 z0 0 4).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_10 (t : ℂ) : (momentPoly 0 z0 1 0).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_11 (t : ℂ) : (momentPoly 0 z0 1 1).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_12 (t : ℂ) : (momentPoly 0 z0 1 2).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_13 (t : ℂ) : (momentPoly 0 z0 1 3).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_14 (t : ℂ) : (momentPoly 0 z0 1 4).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_20 (t : ℂ) : (momentPoly 0 z0 2 0).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_21 (t : ℂ) : (momentPoly 0 z0 2 1).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_22 (t : ℂ) : (momentPoly 0 z0 2 2).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_23 (t : ℂ) : (momentPoly 0 z0 2 3).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_24 (t : ℂ) : (momentPoly 0 z0 2 4).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_30 (t : ℂ) : (momentPoly 0 z0 3 0).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_31 (t : ℂ) : (momentPoly 0 z0 3 1).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_32 (t : ℂ) : (momentPoly 0 z0 3 2).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_33 (t : ℂ) : (momentPoly 0 z0 3 3).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_34 (t : ℂ) : (momentPoly 0 z0 3 4).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_40 (t : ℂ) : (momentPoly 0 z0 4 0).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_41 (t : ℂ) : (momentPoly 0 z0 4 1).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_42 (t : ℂ) : (momentPoly 0 z0 4 2).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_43 (t : ℂ) : (momentPoly 0 z0 4 3).eval t = 0 := by
  norm_num [momentPoly]
theorem v0_44 (t : ℂ) : (momentPoly 0 z0 4 4).eval t = 0 := by
  norm_num [momentPoly]
#print axioms v0_00
#print axioms v0_11
#print axioms v0_22
#print axioms v0_33
#print axioms v0_44
end PhotonCertA
