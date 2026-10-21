import PhotonCertA1
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z2 : Fin 2 → ℂ := Fin.snoc z1 thetaPlus
theorem v2_00 (t : ℂ) : (momentPoly 2 z2 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00]
  simp only [phase1_00]
  ring
theorem v2_01 (t : ℂ) : (momentPoly 2 z2 0 1).eval t = ((-1 / 5) * t + (1 / 15) * c * t + (-1 / 15) * alpha * t + (-1 / 15) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_01]
  simp only [phase1_00, phase1_01]
  ring
theorem v2_02 (t : ℂ) : (momentPoly 2 z2 0 2).eval t = ((-73 / 75) * t ^ 2 + (-73 / 75) * t ^ 4 + (-2 / 75) * c * t ^ 2 + (-2 / 75) * c * t ^ 4 + (-73 / 75) * alpha * t ^ 2 + (-73 / 75) * alpha * t ^ 4 + (2 / 225) * alpha * c * t ^ 2 + (2 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_01, v1_02]
  simp only [phase1_00, phase1_01, phase1_02]
  linear_combination ((1 / 450) * t ^ 2 + (1 / 225) * c * t ^ 2 + (1 / 450) * c ^ 2 * t ^ 2) * alpha_sq + ((-1 / 225) * t ^ 2 + (-1 / 225) * alpha * t ^ 2) * c_sq
theorem v2_03 (t : ℂ) : (momentPoly 2 z2 0 3).eval t = ((-142 / 375) * c * t ^ 5 + (-142 / 1125) * c * t ^ 9 + (442 / 375) * alpha * t ^ 5 + (442 / 1125) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_01, v1_02, v1_03]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03]
  linear_combination ((73 / 750) * t ^ 5 + (217 / 2250) * c * t ^ 5 + (-1 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((4 / 1125) * alpha * t ^ 5) * c_sq
theorem v2_04 (t : ℂ) : (momentPoly 2 z2 0 4).eval t = ((-5033 / 1875) * t ^ 8 + (-20132 / 5625) * t ^ 10 + (-5033 / 5625) * t ^ 16 + (292 / 1875) * c * t ^ 8 + (1168 / 5625) * c * t ^ 10 + (292 / 5625) * c * t ^ 16 + (5033 / 1875) * alpha * t ^ 8 + (20132 / 5625) * alpha * t ^ 10 + (5033 / 5625) * alpha * t ^ 16 + (292 / 5625) * alpha * c * t ^ 8 + (1168 / 16875) * alpha * c * t ^ 10 + (292 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_01, v1_02, v1_03, v1_04]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_04]
  linear_combination ((5329 / 3750) * t ^ 8 + (-884 / 16875) * t ^ 10 + (-146 / 5625) * c * t ^ 8 + (-884 / 16875) * c * t ^ 10 + (2 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((4 / 5625) * t ^ 8 + (-284 / 16875) * t ^ 10 + (-4 / 5625) * alpha * t ^ 8 + (284 / 16875) * alpha * t ^ 10) * c_sq
theorem v2_10 (t : ℂ) : (momentPoly 2 z2 1 0).eval t = ((-1 / 5) * t + (1 / 15) * c * t + (1 / 15) * alpha * t + (1 / 15) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_10]
  simp only [phase1_00, phase1_10]
  ring
theorem v2_11 (t : ℂ) : (momentPoly 2 z2 1 1).eval t = (2 + 2 * t ^ 2) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_01, v1_10, v1_11]
  simp only [phase1_00, phase1_01, phase1_10, phase1_11]
  linear_combination ((-1 / 450) * t ^ 2 + (-1 / 225) * c * t ^ 2 + (-1 / 450) * c ^ 2 * t ^ 2) * alpha_sq + ((2 / 225) * t ^ 2) * c_sq
theorem v2_12 (t : ℂ) : (momentPoly 2 z2 1 2).eval t = ((-3 / 5) * t + (-1 / 5) * t ^ 5 + (1 / 5) * c * t + (1 / 15) * c * t ^ 5 + (-1 / 5) * alpha * t + (-1 / 15) * alpha * t ^ 5 + (-1 / 5) * alpha * c * t + (-1 / 15) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_01, v1_02, v1_10, v1_11, v1_12]
  simp only [phase1_00, phase1_01, phase1_02, phase1_10, phase1_11, phase1_12]
  linear_combination ((-73 / 2250) * t ^ 5 + (-217 / 6750) * c * t ^ 5 + (1 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((-2 / 1125) * t ^ 5 + (-2 / 3375) * alpha * t ^ 5) * c_sq
theorem v2_13 (t : ℂ) : (momentPoly 2 z2 1 3).eval t = ((-73 / 25) * t ^ 2 + (-292 / 75) * t ^ 4 + (-73 / 75) * t ^ 10 + (-2 / 25) * c * t ^ 2 + (-8 / 75) * c * t ^ 4 + (-2 / 75) * c * t ^ 10 + (-73 / 25) * alpha * t ^ 2 + (-292 / 75) * alpha * t ^ 4 + (-73 / 75) * alpha * t ^ 10 + (2 / 75) * alpha * c * t ^ 2 + (8 / 225) * alpha * c * t ^ 4 + (2 / 225) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_01, v1_02, v1_03, v1_10, v1_11, v1_12, v1_13]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_10, phase1_11, phase1_12, phase1_13]
  linear_combination ((1 / 150) * t ^ 2 + (221 / 16875) * t ^ 10 + (1 / 75) * c * t ^ 2 + (221 / 16875) * c * t ^ 10 + (1 / 150) * c ^ 2 * t ^ 2) * alpha_sq + ((-1 / 75) * t ^ 2 + (-71 / 16875) * t ^ 10 + (-1 / 75) * alpha * t ^ 2 + (-71 / 16875) * alpha * t ^ 10) * c_sq
theorem v2_14 (t : ℂ) : (momentPoly 2 z2 1 4).eval t = ((-284 / 225) * c * t ^ 5 + (-142 / 225) * c * t ^ 9 + (-142 / 1125) * c * t ^ 17 + (884 / 225) * alpha * t ^ 5 + (442 / 225) * alpha * t ^ 9 + (442 / 1125) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_01, v1_02, v1_03, v1_04, v1_10, v1_11, v1_12, v1_13, v1_14]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_04, phase1_10, phase1_11, phase1_12, phase1_13, phase1_14]
  linear_combination ((73 / 225) * t ^ 5 + (5033 / 168750) * t ^ 17 + (217 / 675) * c * t ^ 5 + (15391 / 506250) * c * t ^ 17 + (-2 / 675) * c ^ 2 * t ^ 5 + (146 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((8 / 675) * alpha * t ^ 5 + (584 / 253125) * alpha * t ^ 17) * c_sq
theorem v2_20 (t : ℂ) : (momentPoly 2 z2 2 0).eval t = ((-73 / 75) * t ^ 2 + (-73 / 75) * t ^ 4 + (-2 / 75) * c * t ^ 2 + (-2 / 75) * c * t ^ 4 + (73 / 75) * alpha * t ^ 2 + (73 / 75) * alpha * t ^ 4 + (-2 / 225) * alpha * c * t ^ 2 + (-2 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_10, v1_20]
  simp only [phase1_00, phase1_10, phase1_20]
  linear_combination ((1 / 450) * t ^ 2 + (1 / 225) * c * t ^ 2 + (1 / 450) * c ^ 2 * t ^ 2) * alpha_sq + ((-1 / 225) * t ^ 2 + (1 / 225) * alpha * t ^ 2) * c_sq
theorem v2_21 (t : ℂ) : (momentPoly 2 z2 2 1).eval t = ((-3 / 5) * t + (-1 / 5) * t ^ 5 + (1 / 5) * c * t + (1 / 15) * c * t ^ 5 + (1 / 5) * alpha * t + (1 / 15) * alpha * t ^ 5 + (1 / 5) * alpha * c * t + (1 / 15) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_01, v1_10, v1_11, v1_20, v1_21]
  simp only [phase1_00, phase1_01, phase1_10, phase1_11, phase1_20, phase1_21]
  linear_combination ((-73 / 2250) * t ^ 5 + (-217 / 6750) * c * t ^ 5 + (1 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((-2 / 1125) * t ^ 5 + (2 / 3375) * alpha * t ^ 5) * c_sq
theorem v2_22 (t : ℂ) : (momentPoly 2 z2 2 2).eval t = (6 + 8 * t ^ 2 + 2 * t ^ 8) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_01, v1_02, v1_10, v1_11, v1_12, v1_20, v1_21, v1_22]
  simp only [phase1_00, phase1_01, phase1_02, phase1_10, phase1_11, phase1_12, phase1_20, phase1_21, phase1_22]
  linear_combination ((-2 / 225) * t ^ 2 + (-5329 / 11250) * t ^ 8 + (-4 / 225) * c * t ^ 2 + (146 / 16875) * c * t ^ 8 + (-2 / 225) * c ^ 2 * t ^ 2 + (-2 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((8 / 225) * t ^ 2 + (8 / 16875) * t ^ 8) * c_sq
theorem v2_23 (t : ℂ) : (momentPoly 2 z2 2 3).eval t = ((-2) * t + (-1) * t ^ 5 + (-1 / 5) * t ^ 13 + (2 / 3) * c * t + (1 / 3) * c * t ^ 5 + (1 / 15) * c * t ^ 13 + (-2 / 3) * alpha * t + (-1 / 3) * alpha * t ^ 5 + (-1 / 15) * alpha * t ^ 13 + (-2 / 3) * alpha * c * t + (-1 / 3) * alpha * c * t ^ 5 + (-1 / 15) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_01, v1_02, v1_03, v1_10, v1_11, v1_12, v1_13, v1_20, v1_21, v1_22, v1_23]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_10, phase1_11, phase1_12, phase1_13, phase1_20, phase1_21, phase1_22, phase1_23]
  linear_combination ((-73 / 450) * t ^ 5 + (16133 / 84375) * t ^ 13 + (-217 / 1350) * c * t ^ 5 + (-442 / 253125) * c * t ^ 13 + (1 / 675) * c ^ 2 * t ^ 5) * alpha_sq + ((-2 / 225) * t ^ 5 + (142 / 84375) * t ^ 13 + (-2 / 675) * alpha * t ^ 5 + (142 / 253125) * alpha * t ^ 13) * c_sq
theorem v2_24 (t : ℂ) : (momentPoly 2 z2 2 4).eval t = ((-146 / 15) * t ^ 2 + (-73 / 5) * t ^ 4 + (-146 / 25) * t ^ 10 + (-73 / 75) * t ^ 20 + (-4 / 15) * c * t ^ 2 + (-2 / 5) * c * t ^ 4 + (-4 / 25) * c * t ^ 10 + (-2 / 75) * c * t ^ 20 + (-146 / 15) * alpha * t ^ 2 + (-73 / 5) * alpha * t ^ 4 + (-146 / 25) * alpha * t ^ 10 + (-73 / 75) * alpha * t ^ 20 + (4 / 45) * alpha * c * t ^ 2 + (2 / 15) * alpha * c * t ^ 4 + (4 / 75) * alpha * c * t ^ 10 + (2 / 225) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_01, v1_02, v1_03, v1_04, v1_10, v1_11, v1_12, v1_13, v1_14, v1_20, v1_21, v1_22, v1_23, v1_24]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_04, phase1_10, phase1_11, phase1_12, phase1_13, phase1_14, phase1_20, phase1_21, phase1_22, phase1_23, phase1_24]
  linear_combination ((1 / 45) * t ^ 2 + (442 / 5625) * t ^ 10 + (367409 / 843750) * t ^ 20 + (2 / 45) * c * t ^ 2 + (442 / 5625) * c * t ^ 10 + (1 / 225) * c * t ^ 20 + (1 / 45) * c ^ 2 * t ^ 2 + (-292 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-2 / 45) * t ^ 2 + (-142 / 5625) * t ^ 10 + (-584 / 1265625) * t ^ 20 + (-2 / 45) * alpha * t ^ 2 + (-142 / 5625) * alpha * t ^ 10 + (-584 / 1265625) * alpha * t ^ 20) * c_sq
theorem v2_30 (t : ℂ) : (momentPoly 2 z2 3 0).eval t = ((-142 / 375) * c * t ^ 5 + (-142 / 1125) * c * t ^ 9 + (-442 / 375) * alpha * t ^ 5 + (-442 / 1125) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_10, v1_20, v1_30]
  simp only [phase1_00, phase1_10, phase1_20, phase1_30]
  linear_combination ((73 / 750) * t ^ 5 + (217 / 2250) * c * t ^ 5 + (-1 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-4 / 1125) * alpha * t ^ 5) * c_sq
theorem v2_31 (t : ℂ) : (momentPoly 2 z2 3 1).eval t = ((-73 / 25) * t ^ 2 + (-292 / 75) * t ^ 4 + (-73 / 75) * t ^ 10 + (-2 / 25) * c * t ^ 2 + (-8 / 75) * c * t ^ 4 + (-2 / 75) * c * t ^ 10 + (73 / 25) * alpha * t ^ 2 + (292 / 75) * alpha * t ^ 4 + (73 / 75) * alpha * t ^ 10 + (-2 / 75) * alpha * c * t ^ 2 + (-8 / 225) * alpha * c * t ^ 4 + (-2 / 225) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_01, v1_10, v1_11, v1_20, v1_21, v1_30, v1_31]
  simp only [phase1_00, phase1_01, phase1_10, phase1_11, phase1_20, phase1_21, phase1_30, phase1_31]
  linear_combination ((1 / 150) * t ^ 2 + (221 / 16875) * t ^ 10 + (1 / 75) * c * t ^ 2 + (221 / 16875) * c * t ^ 10 + (1 / 150) * c ^ 2 * t ^ 2) * alpha_sq + ((-1 / 75) * t ^ 2 + (-71 / 16875) * t ^ 10 + (1 / 75) * alpha * t ^ 2 + (71 / 16875) * alpha * t ^ 10) * c_sq
theorem v2_32 (t : ℂ) : (momentPoly 2 z2 3 2).eval t = ((-2) * t + (-1) * t ^ 5 + (-1 / 5) * t ^ 13 + (2 / 3) * c * t + (1 / 3) * c * t ^ 5 + (1 / 15) * c * t ^ 13 + (2 / 3) * alpha * t + (1 / 3) * alpha * t ^ 5 + (1 / 15) * alpha * t ^ 13 + (2 / 3) * alpha * c * t + (1 / 3) * alpha * c * t ^ 5 + (1 / 15) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_01, v1_02, v1_10, v1_11, v1_12, v1_20, v1_21, v1_22, v1_30, v1_31, v1_32]
  simp only [phase1_00, phase1_01, phase1_02, phase1_10, phase1_11, phase1_12, phase1_20, phase1_21, phase1_22, phase1_30, phase1_31, phase1_32]
  linear_combination ((-73 / 450) * t ^ 5 + (16133 / 84375) * t ^ 13 + (-217 / 1350) * c * t ^ 5 + (-442 / 253125) * c * t ^ 13 + (1 / 675) * c ^ 2 * t ^ 5) * alpha_sq + ((-2 / 225) * t ^ 5 + (142 / 84375) * t ^ 13 + (2 / 675) * alpha * t ^ 5 + (-142 / 253125) * alpha * t ^ 13) * c_sq
theorem v2_33 (t : ℂ) : (momentPoly 2 z2 3 3).eval t = (20 + 30 * t ^ 2 + 12 * t ^ 8 + 2 * t ^ 18) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_01, v1_02, v1_03, v1_10, v1_11, v1_12, v1_13, v1_20, v1_21, v1_22, v1_23, v1_30, v1_31, v1_32, v1_33]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_10, phase1_11, phase1_12, phase1_13, phase1_20, phase1_21, phase1_22, phase1_23, phase1_30, phase1_31, phase1_32, phase1_33]
  linear_combination ((-1 / 30) * t ^ 2 + (-5329 / 1875) * t ^ 8 + (-97682 / 1265625) * t ^ 18 + (-1 / 15) * c * t ^ 2 + (292 / 5625) * c * t ^ 8 + (-1 / 30) * c ^ 2 * t ^ 2 + (-4 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((2 / 15) * t ^ 2 + (16 / 5625) * t ^ 8 + (10082 / 1265625) * t ^ 18) * c_sq
theorem v2_34 (t : ℂ) : (momentPoly 2 z2 3 4).eval t = ((-7) * t + (-21 / 5) * t ^ 5 + (-7 / 5) * t ^ 13 + (-1 / 5) * t ^ 25 + (7 / 3) * c * t + (7 / 5) * c * t ^ 5 + (7 / 15) * c * t ^ 13 + (1 / 15) * c * t ^ 25 + (-7 / 3) * alpha * t + (-7 / 5) * alpha * t ^ 5 + (-7 / 15) * alpha * t ^ 13 + (-1 / 15) * alpha * t ^ 25 + (-7 / 3) * alpha * c * t + (-7 / 5) * alpha * c * t ^ 5 + (-7 / 15) * alpha * c * t ^ 13 + (-1 / 15) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_01, v1_02, v1_03, v1_04, v1_10, v1_11, v1_12, v1_13, v1_14, v1_20, v1_21, v1_22, v1_23, v1_24, v1_30, v1_31, v1_32, v1_33, v1_34]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_04, phase1_10, phase1_11, phase1_12, phase1_13, phase1_14, phase1_20, phase1_21, phase1_22, phase1_23, phase1_24, phase1_30, phase1_31, phase1_32, phase1_33, phase1_34]
  linear_combination ((-511 / 750) * t ^ 5 + (112931 / 84375) * t ^ 13 + (-1112293 / 6328125) * t ^ 25 + (-1519 / 2250) * c * t ^ 5 + (-3094 / 253125) * c * t ^ 13 + (-64532 / 18984375) * c * t ^ 25 + (7 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-14 / 375) * t ^ 5 + (994 / 84375) * t ^ 13 + (-20732 / 6328125) * t ^ 25 + (-14 / 1125) * alpha * t ^ 5 + (994 / 253125) * alpha * t ^ 13 + (-20732 / 18984375) * alpha * t ^ 25) * c_sq
theorem v2_40 (t : ℂ) : (momentPoly 2 z2 4 0).eval t = ((-5033 / 1875) * t ^ 8 + (-20132 / 5625) * t ^ 10 + (-5033 / 5625) * t ^ 16 + (292 / 1875) * c * t ^ 8 + (1168 / 5625) * c * t ^ 10 + (292 / 5625) * c * t ^ 16 + (-5033 / 1875) * alpha * t ^ 8 + (-20132 / 5625) * alpha * t ^ 10 + (-5033 / 5625) * alpha * t ^ 16 + (-292 / 5625) * alpha * c * t ^ 8 + (-1168 / 16875) * alpha * c * t ^ 10 + (-292 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_10, v1_20, v1_30, v1_40]
  simp only [phase1_00, phase1_10, phase1_20, phase1_30, phase1_40]
  linear_combination ((5329 / 3750) * t ^ 8 + (-884 / 16875) * t ^ 10 + (-146 / 5625) * c * t ^ 8 + (-884 / 16875) * c * t ^ 10 + (2 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((4 / 5625) * t ^ 8 + (-284 / 16875) * t ^ 10 + (4 / 5625) * alpha * t ^ 8 + (-284 / 16875) * alpha * t ^ 10) * c_sq
theorem v2_41 (t : ℂ) : (momentPoly 2 z2 4 1).eval t = ((-284 / 225) * c * t ^ 5 + (-142 / 225) * c * t ^ 9 + (-142 / 1125) * c * t ^ 17 + (-884 / 225) * alpha * t ^ 5 + (-442 / 225) * alpha * t ^ 9 + (-442 / 1125) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_01, v1_10, v1_11, v1_20, v1_21, v1_30, v1_31, v1_40, v1_41]
  simp only [phase1_00, phase1_01, phase1_10, phase1_11, phase1_20, phase1_21, phase1_30, phase1_31, phase1_40, phase1_41]
  linear_combination ((73 / 225) * t ^ 5 + (5033 / 168750) * t ^ 17 + (217 / 675) * c * t ^ 5 + (15391 / 506250) * c * t ^ 17 + (-2 / 675) * c ^ 2 * t ^ 5 + (146 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((-8 / 675) * alpha * t ^ 5 + (-584 / 253125) * alpha * t ^ 17) * c_sq
theorem v2_42 (t : ℂ) : (momentPoly 2 z2 4 2).eval t = ((-146 / 15) * t ^ 2 + (-73 / 5) * t ^ 4 + (-146 / 25) * t ^ 10 + (-73 / 75) * t ^ 20 + (-4 / 15) * c * t ^ 2 + (-2 / 5) * c * t ^ 4 + (-4 / 25) * c * t ^ 10 + (-2 / 75) * c * t ^ 20 + (146 / 15) * alpha * t ^ 2 + (73 / 5) * alpha * t ^ 4 + (146 / 25) * alpha * t ^ 10 + (73 / 75) * alpha * t ^ 20 + (-4 / 45) * alpha * c * t ^ 2 + (-2 / 15) * alpha * c * t ^ 4 + (-4 / 75) * alpha * c * t ^ 10 + (-2 / 225) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_01, v1_02, v1_10, v1_11, v1_12, v1_20, v1_21, v1_22, v1_30, v1_31, v1_32, v1_40, v1_41, v1_42]
  simp only [phase1_00, phase1_01, phase1_02, phase1_10, phase1_11, phase1_12, phase1_20, phase1_21, phase1_22, phase1_30, phase1_31, phase1_32, phase1_40, phase1_41, phase1_42]
  linear_combination ((1 / 45) * t ^ 2 + (442 / 5625) * t ^ 10 + (367409 / 843750) * t ^ 20 + (2 / 45) * c * t ^ 2 + (442 / 5625) * c * t ^ 10 + (1 / 225) * c * t ^ 20 + (1 / 45) * c ^ 2 * t ^ 2 + (-292 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-2 / 45) * t ^ 2 + (-142 / 5625) * t ^ 10 + (-584 / 1265625) * t ^ 20 + (2 / 45) * alpha * t ^ 2 + (142 / 5625) * alpha * t ^ 10 + (584 / 1265625) * alpha * t ^ 20) * c_sq
theorem v2_43 (t : ℂ) : (momentPoly 2 z2 4 3).eval t = ((-7) * t + (-21 / 5) * t ^ 5 + (-7 / 5) * t ^ 13 + (-1 / 5) * t ^ 25 + (7 / 3) * c * t + (7 / 5) * c * t ^ 5 + (7 / 15) * c * t ^ 13 + (1 / 15) * c * t ^ 25 + (7 / 3) * alpha * t + (7 / 5) * alpha * t ^ 5 + (7 / 15) * alpha * t ^ 13 + (1 / 15) * alpha * t ^ 25 + (7 / 3) * alpha * c * t + (7 / 5) * alpha * c * t ^ 5 + (7 / 15) * alpha * c * t ^ 13 + (1 / 15) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_01, v1_02, v1_03, v1_10, v1_11, v1_12, v1_13, v1_20, v1_21, v1_22, v1_23, v1_30, v1_31, v1_32, v1_33, v1_40, v1_41, v1_42, v1_43]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_10, phase1_11, phase1_12, phase1_13, phase1_20, phase1_21, phase1_22, phase1_23, phase1_30, phase1_31, phase1_32, phase1_33, phase1_40, phase1_41, phase1_42, phase1_43]
  linear_combination ((-511 / 750) * t ^ 5 + (112931 / 84375) * t ^ 13 + (-1112293 / 6328125) * t ^ 25 + (-1519 / 2250) * c * t ^ 5 + (-3094 / 253125) * c * t ^ 13 + (-64532 / 18984375) * c * t ^ 25 + (7 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-14 / 375) * t ^ 5 + (994 / 84375) * t ^ 13 + (-20732 / 6328125) * t ^ 25 + (14 / 1125) * alpha * t ^ 5 + (-994 / 253125) * alpha * t ^ 13 + (20732 / 18984375) * alpha * t ^ 25) * c_sq
theorem v2_44 (t : ℂ) : (momentPoly 2 z2 4 4).eval t = (70 + 112 * t ^ 2 + 56 * t ^ 8 + 16 * t ^ 18 + 2 * t ^ 32) := by
  rw [momentPoly]
  simp only [z2, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v1_00, v1_01, v1_02, v1_03, v1_04, v1_10, v1_11, v1_12, v1_13, v1_14, v1_20, v1_21, v1_22, v1_23, v1_24, v1_30, v1_31, v1_32, v1_33, v1_34, v1_40, v1_41, v1_42, v1_43, v1_44]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_04, phase1_10, phase1_11, phase1_12, phase1_13, phase1_14, phase1_20, phase1_21, phase1_22, phase1_23, phase1_24, phase1_30, phase1_31, phase1_32, phase1_33, phase1_34, phase1_40, phase1_41, phase1_42, phase1_43, phase1_44]
  linear_combination ((-28 / 225) * t ^ 2 + (-74606 / 5625) * t ^ 8 + (-781456 / 1265625) * t ^ 18 + (-25331089 / 63281250) * t ^ 32 + (-56 / 225) * c * t ^ 2 + (4088 / 16875) * c * t ^ 8 + (-1469636 / 94921875) * c * t ^ 32 + (-28 / 225) * c ^ 2 * t ^ 2 + (-56 / 50625) * c ^ 2 * t ^ 8 + (-42632 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((112 / 225) * t ^ 2 + (224 / 16875) * t ^ 8 + (80656 / 1265625) * t ^ 18 + (170528 / 94921875) * t ^ 32) * c_sq
#print axioms v2_00
#print axioms v2_11
#print axioms v2_22
#print axioms v2_33
#print axioms v2_44
end PhotonCertA
