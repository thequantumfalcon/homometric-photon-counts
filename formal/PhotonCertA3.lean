import PhotonCertA2
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z3 : Fin 3 → ℂ := Fin.snoc z2 thetaPlus
theorem v3_00 (t : ℂ) : (momentPoly 3 z3 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00]
  simp only [phase1_00]
  ring
theorem v3_01 (t : ℂ) : (momentPoly 3 z3 0 1).eval t = ((-3 / 10) * t + (1 / 10) * c * t + (-1 / 10) * alpha * t + (-1 / 10) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_01]
  simp only [phase1_00, phase1_01]
  ring
theorem v3_02 (t : ℂ) : (momentPoly 3 z3 0 2).eval t = ((-73 / 25) * t ^ 2 + (-73 / 50) * t ^ 4 + (-2 / 25) * c * t ^ 2 + (-1 / 25) * c * t ^ 4 + (-73 / 25) * alpha * t ^ 2 + (-73 / 50) * alpha * t ^ 4 + (2 / 75) * alpha * c * t ^ 2 + (1 / 75) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_01, v2_02]
  simp only [phase1_00, phase1_01, phase1_02]
  linear_combination ((1 / 225) * t ^ 2 + (2 / 225) * c * t ^ 2 + (1 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((-2 / 225) * t ^ 2 + (-2 / 225) * alpha * t ^ 2) * c_sq
theorem v3_03 (t : ℂ) : (momentPoly 3 z3 0 3).eval t = ((-142 / 375) * c * t ^ 3 + (-142 / 125) * c * t ^ 5 + (-71 / 375) * c * t ^ 9 + (442 / 375) * alpha * t ^ 3 + (442 / 125) * alpha * t ^ 5 + (221 / 375) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_01, v2_02, v2_03]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03]
  linear_combination ((73 / 750) * t ^ 3 + (73 / 375) * t ^ 5 + (217 / 2250) * c * t ^ 3 + (217 / 1125) * c * t ^ 5 + (-1 / 1125) * c ^ 2 * t ^ 3 + (-2 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((4 / 1125) * alpha * t ^ 3 + (8 / 1125) * alpha * t ^ 5) * c_sq
theorem v3_04 (t : ℂ) : (momentPoly 3 z3 0 4).eval t = ((-10066 / 625) * t ^ 6 + (-5033 / 625) * t ^ 8 + (-20132 / 1875) * t ^ 10 + (-5033 / 3750) * t ^ 16 + (584 / 625) * c * t ^ 6 + (292 / 625) * c * t ^ 8 + (1168 / 1875) * c * t ^ 10 + (146 / 1875) * c * t ^ 16 + (10066 / 625) * alpha * t ^ 6 + (5033 / 625) * alpha * t ^ 8 + (20132 / 1875) * alpha * t ^ 10 + (5033 / 3750) * alpha * t ^ 16 + (584 / 1875) * alpha * c * t ^ 6 + (292 / 1875) * alpha * c * t ^ 8 + (1168 / 5625) * alpha * c * t ^ 10 + (146 / 5625) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_01, v2_02, v2_03, v2_04]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_04]
  linear_combination ((15103 / 5625) * t ^ 6 + (5329 / 1875) * t ^ 8 + (-1768 / 16875) * t ^ 10 + (-392 / 1875) * c * t ^ 6 + (-292 / 5625) * c * t ^ 8 + (-1768 / 16875) * c * t ^ 10 + (4 / 16875) * c ^ 2 * t ^ 6 + (4 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-92 / 1875) * t ^ 6 + (8 / 5625) * t ^ 8 + (-568 / 16875) * t ^ 10 + (92 / 1875) * alpha * t ^ 6 + (-8 / 5625) * alpha * t ^ 8 + (568 / 16875) * alpha * t ^ 10) * c_sq
theorem v3_10 (t : ℂ) : (momentPoly 3 z3 1 0).eval t = ((-3 / 10) * t + (1 / 10) * c * t + (1 / 10) * alpha * t + (1 / 10) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_10]
  simp only [phase1_00, phase1_10]
  ring
theorem v3_11 (t : ℂ) : (momentPoly 3 z3 1 1).eval t = (3 + 6 * t ^ 2) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_01, v2_10, v2_11]
  simp only [phase1_00, phase1_01, phase1_10, phase1_11]
  linear_combination ((-1 / 225) * t ^ 2 + (-2 / 225) * c * t ^ 2 + (-1 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((4 / 225) * t ^ 2) * c_sq
theorem v3_12 (t : ℂ) : (momentPoly 3 z3 1 2).eval t = ((-3 / 2) * t + (-3 / 5) * t ^ 3 + (-3 / 5) * t ^ 5 + (1 / 2) * c * t + (1 / 5) * c * t ^ 3 + (1 / 5) * c * t ^ 5 + (-1 / 2) * alpha * t + (-1 / 5) * alpha * t ^ 3 + (-1 / 5) * alpha * t ^ 5 + (-1 / 2) * alpha * c * t + (-1 / 5) * alpha * c * t ^ 3 + (-1 / 5) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_01, v2_02, v2_10, v2_11, v2_12]
  simp only [phase1_00, phase1_01, phase1_02, phase1_10, phase1_11, phase1_12]
  linear_combination ((-73 / 2250) * t ^ 3 + (-73 / 1125) * t ^ 5 + (-217 / 6750) * c * t ^ 3 + (-217 / 3375) * c * t ^ 5 + (1 / 3375) * c ^ 2 * t ^ 3 + (2 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((-2 / 1125) * t ^ 3 + (-4 / 1125) * t ^ 5 + (-2 / 3375) * alpha * t ^ 3 + (-4 / 3375) * alpha * t ^ 5) * c_sq
theorem v3_13 (t : ℂ) : (momentPoly 3 z3 1 3).eval t = ((-438 / 25) * t ^ 2 + (-511 / 50) * t ^ 4 + (-219 / 25) * t ^ 6 + (-73 / 25) * t ^ 10 + (-12 / 25) * c * t ^ 2 + (-7 / 25) * c * t ^ 4 + (-6 / 25) * c * t ^ 6 + (-2 / 25) * c * t ^ 10 + (-438 / 25) * alpha * t ^ 2 + (-511 / 50) * alpha * t ^ 4 + (-219 / 25) * alpha * t ^ 6 + (-73 / 25) * alpha * t ^ 10 + (4 / 25) * alpha * c * t ^ 2 + (7 / 75) * alpha * c * t ^ 4 + (2 / 25) * alpha * c * t ^ 6 + (2 / 75) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_01, v2_02, v2_03, v2_10, v2_11, v2_12, v2_13]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_10, phase1_11, phase1_12, phase1_13]
  linear_combination ((2 / 75) * t ^ 2 + (517 / 11250) * t ^ 6 + (442 / 16875) * t ^ 10 + (4 / 75) * c * t ^ 2 + (296 / 5625) * c * t ^ 6 + (442 / 16875) * c * t ^ 10 + (2 / 75) * c ^ 2 * t ^ 2 + (1 / 150) * c ^ 2 * t ^ 6) * alpha_sq + ((-4 / 75) * t ^ 2 + (-146 / 5625) * t ^ 6 + (-142 / 16875) * t ^ 10 + (-4 / 75) * alpha * t ^ 2 + (-146 / 5625) * alpha * t ^ 6 + (-142 / 16875) * alpha * t ^ 10) * c_sq
theorem v3_14 (t : ℂ) : (momentPoly 3 z3 1 4).eval t = ((-284 / 125) * c * t ^ 3 + (-3124 / 375) * c * t ^ 5 + (-71 / 25) * c * t ^ 9 + (-568 / 375) * c * t ^ 11 + (-142 / 375) * c * t ^ 17 + (884 / 125) * alpha * t ^ 3 + (9724 / 375) * alpha * t ^ 5 + (221 / 25) * alpha * t ^ 9 + (1768 / 375) * alpha * t ^ 11 + (442 / 375) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_01, v2_02, v2_03, v2_04, v2_10, v2_11, v2_12, v2_13, v2_14]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_04, phase1_10, phase1_11, phase1_12, phase1_13, phase1_14]
  linear_combination ((73 / 125) * t ^ 3 + (1606 / 1125) * t ^ 5 + (15983 / 56250) * t ^ 9 + (21016 / 84375) * t ^ 11 + (5033 / 84375) * t ^ 17 + (217 / 375) * c * t ^ 3 + (4774 / 3375) * c * t ^ 5 + (47941 / 168750) * c * t ^ 9 + (63332 / 253125) * c * t ^ 11 + (15391 / 253125) * c * t ^ 17 + (-2 / 375) * c ^ 2 * t ^ 3 + (-44 / 3375) * c ^ 2 * t ^ 5 + (-4 / 84375) * c ^ 2 * t ^ 9 + (284 / 253125) * c ^ 2 * t ^ 11 + (292 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((8 / 375) * alpha * t ^ 3 + (176 / 3375) * alpha * t ^ 5 + (1184 / 84375) * alpha * t ^ 9 + (3536 / 253125) * alpha * t ^ 11 + (1168 / 253125) * alpha * t ^ 17) * c_sq
theorem v3_20 (t : ℂ) : (momentPoly 3 z3 2 0).eval t = ((-73 / 25) * t ^ 2 + (-73 / 50) * t ^ 4 + (-2 / 25) * c * t ^ 2 + (-1 / 25) * c * t ^ 4 + (73 / 25) * alpha * t ^ 2 + (73 / 50) * alpha * t ^ 4 + (-2 / 75) * alpha * c * t ^ 2 + (-1 / 75) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_10, v2_20]
  simp only [phase1_00, phase1_10, phase1_20]
  linear_combination ((1 / 225) * t ^ 2 + (2 / 225) * c * t ^ 2 + (1 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((-2 / 225) * t ^ 2 + (2 / 225) * alpha * t ^ 2) * c_sq
theorem v3_21 (t : ℂ) : (momentPoly 3 z3 2 1).eval t = ((-3 / 2) * t + (-3 / 5) * t ^ 3 + (-3 / 5) * t ^ 5 + (1 / 2) * c * t + (1 / 5) * c * t ^ 3 + (1 / 5) * c * t ^ 5 + (1 / 2) * alpha * t + (1 / 5) * alpha * t ^ 3 + (1 / 5) * alpha * t ^ 5 + (1 / 2) * alpha * c * t + (1 / 5) * alpha * c * t ^ 3 + (1 / 5) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_01, v2_10, v2_11, v2_20, v2_21]
  simp only [phase1_00, phase1_01, phase1_10, phase1_11, phase1_20, phase1_21]
  linear_combination ((-73 / 2250) * t ^ 3 + (-73 / 1125) * t ^ 5 + (-217 / 6750) * c * t ^ 3 + (-217 / 3375) * c * t ^ 5 + (1 / 3375) * c ^ 2 * t ^ 3 + (2 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((-2 / 1125) * t ^ 3 + (-4 / 1125) * t ^ 5 + (2 / 3375) * alpha * t ^ 3 + (4 / 3375) * alpha * t ^ 5) * c_sq
theorem v3_22 (t : ℂ) : (momentPoly 3 z3 2 2).eval t = (15 + 48 * t ^ 2 + 12 * t ^ 6 + 6 * t ^ 8) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_01, v2_02, v2_10, v2_11, v2_12, v2_20, v2_21, v2_22]
  simp only [phase1_00, phase1_01, phase1_02, phase1_10, phase1_11, phase1_12, phase1_20, phase1_21, phase1_22]
  linear_combination ((-8 / 225) * t ^ 2 + (-1793 / 1875) * t ^ 6 + (-5329 / 5625) * t ^ 8 + (-16 / 225) * c * t ^ 2 + (-8 / 16875) * c * t ^ 6 + (292 / 16875) * c * t ^ 8 + (-8 / 225) * c ^ 2 * t ^ 2 + (-454 / 50625) * c ^ 2 * t ^ 6 + (-4 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((32 / 225) * t ^ 2 + (616 / 16875) * t ^ 6 + (16 / 16875) * t ^ 8) * c_sq
theorem v3_23 (t : ℂ) : (momentPoly 3 z3 2 3).eval t = ((-93 / 10) * t + (-27 / 5) * t ^ 3 + (-33 / 5) * t ^ 5 + (-9 / 5) * t ^ 9 + (-3 / 5) * t ^ 11 + (-3 / 5) * t ^ 13 + (31 / 10) * c * t + (9 / 5) * c * t ^ 3 + (11 / 5) * c * t ^ 5 + (3 / 5) * c * t ^ 9 + (1 / 5) * c * t ^ 11 + (1 / 5) * c * t ^ 13 + (-31 / 10) * alpha * t + (-9 / 5) * alpha * t ^ 3 + (-11 / 5) * alpha * t ^ 5 + (-3 / 5) * alpha * t ^ 9 + (-1 / 5) * alpha * t ^ 11 + (-1 / 5) * alpha * t ^ 13 + (-31 / 10) * alpha * c * t + (-9 / 5) * alpha * c * t ^ 3 + (-11 / 5) * alpha * c * t ^ 5 + (-3 / 5) * alpha * c * t ^ 9 + (-1 / 5) * alpha * c * t ^ 11 + (-1 / 5) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_01, v2_02, v2_03, v2_10, v2_11, v2_12, v2_13, v2_20, v2_21, v2_22, v2_23]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_10, phase1_11, phase1_12, phase1_13, phase1_20, phase1_21, phase1_22, phase1_23]
  linear_combination ((-73 / 250) * t ^ 3 + (-803 / 1125) * t ^ 5 + (26791 / 56250) * t ^ 9 + (10658 / 84375) * t ^ 11 + (32266 / 84375) * t ^ 13 + (-217 / 750) * c * t ^ 3 + (-2387 / 3375) * c * t ^ 5 + (-17159 / 168750) * c * t ^ 9 + (-16717 / 253125) * c * t ^ 11 + (-884 / 253125) * c * t ^ 13 + (1 / 375) * c ^ 2 * t ^ 3 + (22 / 3375) * c ^ 2 * t ^ 5 + (1 / 1125) * c ^ 2 * t ^ 9 + (2 / 3375) * c ^ 2 * t ^ 11) * alpha_sq + ((-2 / 125) * t ^ 3 + (-44 / 1125) * t ^ 5 + (-8 / 28125) * t ^ 9 + (-158 / 84375) * t ^ 11 + (284 / 84375) * t ^ 13 + (-2 / 375) * alpha * t ^ 3 + (-44 / 3375) * alpha * t ^ 5 + (-8 / 84375) * alpha * t ^ 9 + (-158 / 253125) * alpha * t ^ 11 + (284 / 253125) * alpha * t ^ 13) * c_sq
theorem v3_24 (t : ℂ) : (momentPoly 3 z3 2 4).eval t = ((-584 / 5) * t ^ 2 + (-3869 / 50) * t ^ 4 + (-2336 / 25) * t ^ 6 + (-1022 / 25) * t ^ 10 + (-219 / 25) * t ^ 12 + (-292 / 25) * t ^ 14 + (-73 / 25) * t ^ 18 + (-73 / 25) * t ^ 20 + (-16 / 5) * c * t ^ 2 + (-53 / 25) * c * t ^ 4 + (-64 / 25) * c * t ^ 6 + (-28 / 25) * c * t ^ 10 + (-6 / 25) * c * t ^ 12 + (-8 / 25) * c * t ^ 14 + (-2 / 25) * c * t ^ 18 + (-2 / 25) * c * t ^ 20 + (-584 / 5) * alpha * t ^ 2 + (-3869 / 50) * alpha * t ^ 4 + (-2336 / 25) * alpha * t ^ 6 + (-1022 / 25) * alpha * t ^ 10 + (-219 / 25) * alpha * t ^ 12 + (-292 / 25) * alpha * t ^ 14 + (-73 / 25) * alpha * t ^ 18 + (-73 / 25) * alpha * t ^ 20 + (16 / 15) * alpha * c * t ^ 2 + (53 / 75) * alpha * c * t ^ 4 + (64 / 75) * alpha * c * t ^ 6 + (28 / 75) * alpha * c * t ^ 10 + (2 / 25) * alpha * c * t ^ 12 + (8 / 75) * alpha * c * t ^ 14 + (2 / 75) * alpha * c * t ^ 18 + (2 / 75) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_01, v2_02, v2_03, v2_04, v2_10, v2_11, v2_12, v2_13, v2_14, v2_20, v2_21, v2_22, v2_23, v2_24]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_04, phase1_10, phase1_11, phase1_12, phase1_13, phase1_14, phase1_20, phase1_21, phase1_22, phase1_23, phase1_24]
  linear_combination ((8 / 45) * t ^ 2 + (8272 / 16875) * t ^ 6 + (6188 / 16875) * t ^ 10 + (367409 / 281250) * t ^ 12 + (253556 / 140625) * t ^ 14 + (389509 / 843750) * t ^ 18 + (367409 / 421875) * t ^ 20 + (16 / 45) * c * t ^ 2 + (9472 / 16875) * c * t ^ 6 + (6188 / 16875) * c * t ^ 10 + (1 / 75) * c * t ^ 12 + (1484 / 16875) * c * t ^ 14 + (517 / 16875) * c * t ^ 18 + (2 / 225) * c * t ^ 20 + (8 / 45) * c ^ 2 * t ^ 2 + (16 / 225) * c ^ 2 * t ^ 6 + (-292 / 1265625) * c ^ 2 * t ^ 12 + (32582 / 3796875) * c ^ 2 * t ^ 14 + (-292 / 3796875) * c ^ 2 * t ^ 18 + (-584 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-16 / 45) * t ^ 2 + (-4672 / 16875) * t ^ 6 + (-1988 / 16875) * t ^ 10 + (-584 / 421875) * t ^ 12 + (-46136 / 1265625) * t ^ 14 + (-11234 / 1265625) * t ^ 18 + (-1168 / 1265625) * t ^ 20 + (-16 / 45) * alpha * t ^ 2 + (-4672 / 16875) * alpha * t ^ 6 + (-1988 / 16875) * alpha * t ^ 10 + (-584 / 421875) * alpha * t ^ 12 + (-46136 / 1265625) * alpha * t ^ 14 + (-11234 / 1265625) * alpha * t ^ 18 + (-1168 / 1265625) * alpha * t ^ 20) * c_sq
theorem v3_30 (t : ℂ) : (momentPoly 3 z3 3 0).eval t = ((-142 / 375) * c * t ^ 3 + (-142 / 125) * c * t ^ 5 + (-71 / 375) * c * t ^ 9 + (-442 / 375) * alpha * t ^ 3 + (-442 / 125) * alpha * t ^ 5 + (-221 / 375) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_10, v2_20, v2_30]
  simp only [phase1_00, phase1_10, phase1_20, phase1_30]
  linear_combination ((73 / 750) * t ^ 3 + (73 / 375) * t ^ 5 + (217 / 2250) * c * t ^ 3 + (217 / 1125) * c * t ^ 5 + (-1 / 1125) * c ^ 2 * t ^ 3 + (-2 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-4 / 1125) * alpha * t ^ 3 + (-8 / 1125) * alpha * t ^ 5) * c_sq
theorem v3_31 (t : ℂ) : (momentPoly 3 z3 3 1).eval t = ((-438 / 25) * t ^ 2 + (-511 / 50) * t ^ 4 + (-219 / 25) * t ^ 6 + (-73 / 25) * t ^ 10 + (-12 / 25) * c * t ^ 2 + (-7 / 25) * c * t ^ 4 + (-6 / 25) * c * t ^ 6 + (-2 / 25) * c * t ^ 10 + (438 / 25) * alpha * t ^ 2 + (511 / 50) * alpha * t ^ 4 + (219 / 25) * alpha * t ^ 6 + (73 / 25) * alpha * t ^ 10 + (-4 / 25) * alpha * c * t ^ 2 + (-7 / 75) * alpha * c * t ^ 4 + (-2 / 25) * alpha * c * t ^ 6 + (-2 / 75) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_01, v2_10, v2_11, v2_20, v2_21, v2_30, v2_31]
  simp only [phase1_00, phase1_01, phase1_10, phase1_11, phase1_20, phase1_21, phase1_30, phase1_31]
  linear_combination ((2 / 75) * t ^ 2 + (517 / 11250) * t ^ 6 + (442 / 16875) * t ^ 10 + (4 / 75) * c * t ^ 2 + (296 / 5625) * c * t ^ 6 + (442 / 16875) * c * t ^ 10 + (2 / 75) * c ^ 2 * t ^ 2 + (1 / 150) * c ^ 2 * t ^ 6) * alpha_sq + ((-4 / 75) * t ^ 2 + (-146 / 5625) * t ^ 6 + (-142 / 16875) * t ^ 10 + (4 / 75) * alpha * t ^ 2 + (146 / 5625) * alpha * t ^ 6 + (142 / 16875) * alpha * t ^ 10) * c_sq
theorem v3_32 (t : ℂ) : (momentPoly 3 z3 3 2).eval t = ((-93 / 10) * t + (-27 / 5) * t ^ 3 + (-33 / 5) * t ^ 5 + (-9 / 5) * t ^ 9 + (-3 / 5) * t ^ 11 + (-3 / 5) * t ^ 13 + (31 / 10) * c * t + (9 / 5) * c * t ^ 3 + (11 / 5) * c * t ^ 5 + (3 / 5) * c * t ^ 9 + (1 / 5) * c * t ^ 11 + (1 / 5) * c * t ^ 13 + (31 / 10) * alpha * t + (9 / 5) * alpha * t ^ 3 + (11 / 5) * alpha * t ^ 5 + (3 / 5) * alpha * t ^ 9 + (1 / 5) * alpha * t ^ 11 + (1 / 5) * alpha * t ^ 13 + (31 / 10) * alpha * c * t + (9 / 5) * alpha * c * t ^ 3 + (11 / 5) * alpha * c * t ^ 5 + (3 / 5) * alpha * c * t ^ 9 + (1 / 5) * alpha * c * t ^ 11 + (1 / 5) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_01, v2_02, v2_10, v2_11, v2_12, v2_20, v2_21, v2_22, v2_30, v2_31, v2_32]
  simp only [phase1_00, phase1_01, phase1_02, phase1_10, phase1_11, phase1_12, phase1_20, phase1_21, phase1_22, phase1_30, phase1_31, phase1_32]
  linear_combination ((-73 / 250) * t ^ 3 + (-803 / 1125) * t ^ 5 + (26791 / 56250) * t ^ 9 + (10658 / 84375) * t ^ 11 + (32266 / 84375) * t ^ 13 + (-217 / 750) * c * t ^ 3 + (-2387 / 3375) * c * t ^ 5 + (-17159 / 168750) * c * t ^ 9 + (-16717 / 253125) * c * t ^ 11 + (-884 / 253125) * c * t ^ 13 + (1 / 375) * c ^ 2 * t ^ 3 + (22 / 3375) * c ^ 2 * t ^ 5 + (1 / 1125) * c ^ 2 * t ^ 9 + (2 / 3375) * c ^ 2 * t ^ 11) * alpha_sq + ((-2 / 125) * t ^ 3 + (-44 / 1125) * t ^ 5 + (-8 / 28125) * t ^ 9 + (-158 / 84375) * t ^ 11 + (284 / 84375) * t ^ 13 + (2 / 375) * alpha * t ^ 3 + (44 / 3375) * alpha * t ^ 5 + (8 / 84375) * alpha * t ^ 9 + (158 / 253125) * alpha * t ^ 11 + (-284 / 253125) * alpha * t ^ 13) * c_sq
theorem v3_33 (t : ℂ) : (momentPoly 3 z3 3 3).eval t = (93 + 360 * t ^ 2 + 144 * t ^ 6 + 90 * t ^ 8 + 36 * t ^ 14 + 6 * t ^ 18) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_01, v2_02, v2_03, v2_10, v2_11, v2_12, v2_13, v2_20, v2_21, v2_22, v2_23, v2_30, v2_31, v2_32, v2_33]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_10, phase1_11, phase1_12, phase1_13, phase1_20, phase1_21, phase1_22, phase1_23, phase1_30, phase1_31, phase1_32, phase1_33]
  linear_combination ((-4 / 15) * t ^ 2 + (-7172 / 625) * t ^ 6 + (-5329 / 375) * t ^ 8 + (-1400014 / 421875) * t ^ 14 + (-195364 / 1265625) * t ^ 18 + (-8 / 15) * c * t ^ 2 + (-32 / 5625) * c * t ^ 6 + (292 / 1125) * c * t ^ 8 + (142 / 5625) * c * t ^ 14 + (-4 / 15) * c ^ 2 * t ^ 2 + (-1816 / 16875) * c ^ 2 * t ^ 6 + (-4 / 3375) * c ^ 2 * t ^ 8 + (-229 / 16875) * c ^ 2 * t ^ 14) * alpha_sq + ((16 / 15) * t ^ 2 + (2464 / 5625) * t ^ 6 + (16 / 1125) * t ^ 8 + (43864 / 421875) * t ^ 14 + (20164 / 1265625) * t ^ 18) * c_sq
theorem v3_34 (t : ℂ) : (momentPoly 3 z3 3 4).eval t = ((-639 / 10) * t + (-216 / 5) * t ^ 3 + (-297 / 5) * t ^ 5 + (-126 / 5) * t ^ 9 + (-9) * t ^ 11 + (-57 / 5) * t ^ 13 + (-9 / 5) * t ^ 17 + (-12 / 5) * t ^ 19 + (-9 / 5) * t ^ 21 + (-3 / 5) * t ^ 25 + (213 / 10) * c * t + (72 / 5) * c * t ^ 3 + (99 / 5) * c * t ^ 5 + (42 / 5) * c * t ^ 9 + 3 * c * t ^ 11 + (19 / 5) * c * t ^ 13 + (3 / 5) * c * t ^ 17 + (4 / 5) * c * t ^ 19 + (3 / 5) * c * t ^ 21 + (1 / 5) * c * t ^ 25 + (-213 / 10) * alpha * t + (-72 / 5) * alpha * t ^ 3 + (-99 / 5) * alpha * t ^ 5 + (-42 / 5) * alpha * t ^ 9 + (-3) * alpha * t ^ 11 + (-19 / 5) * alpha * t ^ 13 + (-3 / 5) * alpha * t ^ 17 + (-4 / 5) * alpha * t ^ 19 + (-3 / 5) * alpha * t ^ 21 + (-1 / 5) * alpha * t ^ 25 + (-213 / 10) * alpha * c * t + (-72 / 5) * alpha * c * t ^ 3 + (-99 / 5) * alpha * c * t ^ 5 + (-42 / 5) * alpha * c * t ^ 9 + (-3) * alpha * c * t ^ 11 + (-19 / 5) * alpha * c * t ^ 13 + (-3 / 5) * alpha * c * t ^ 17 + (-4 / 5) * alpha * c * t ^ 19 + (-3 / 5) * alpha * c * t ^ 21 + (-1 / 5) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_01, v2_02, v2_03, v2_04, v2_10, v2_11, v2_12, v2_13, v2_14, v2_20, v2_21, v2_22, v2_23, v2_24, v2_30, v2_31, v2_32, v2_33, v2_34]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_04, phase1_10, phase1_11, phase1_12, phase1_13, phase1_14, phase1_20, phase1_21, phase1_22, phase1_23, phase1_24, phase1_30, phase1_31, phase1_32, phase1_33, phase1_34]
  linear_combination ((-292 / 125) * t ^ 3 + (-803 / 125) * t ^ 5 + (187537 / 28125) * t ^ 9 + (10658 / 5625) * t ^ 11 + (613054 / 84375) * t ^ 13 + (-1522918 / 2109375) * t ^ 17 + (390728 / 6328125) * t ^ 19 + (-215261 / 4218750) * t ^ 21 + (-2224586 / 6328125) * t ^ 25 + (-868 / 375) * c * t ^ 3 + (-2387 / 375) * c * t ^ 5 + (-120113 / 84375) * c * t ^ 9 + (-16717 / 16875) * c * t ^ 11 + (-16796 / 253125) * c * t ^ 13 + (-1285157 / 6328125) * c * t ^ 17 + (-390728 / 18984375) * c * t ^ 19 + (-1415989 / 12656250) * c * t ^ 21 + (-129064 / 18984375) * c * t ^ 25 + (8 / 375) * c ^ 2 * t ^ 3 + (22 / 375) * c ^ 2 * t ^ 5 + (14 / 1125) * c ^ 2 * t ^ 9 + (2 / 225) * c ^ 2 * t ^ 11 + (2 / 1125) * c ^ 2 * t ^ 17 + (1 / 1125) * c ^ 2 * t ^ 21) * alpha_sq + ((-16 / 125) * t ^ 3 + (-44 / 125) * t ^ 5 + (-112 / 28125) * t ^ 9 + (-158 / 5625) * t ^ 11 + (5396 / 84375) * t ^ 13 + (-43232 / 2109375) * t ^ 17 + (-40328 / 6328125) * t ^ 19 + (-21332 / 2109375) * t ^ 21 + (-41464 / 6328125) * t ^ 25 + (-16 / 375) * alpha * t ^ 3 + (-44 / 375) * alpha * t ^ 5 + (-112 / 84375) * alpha * t ^ 9 + (-158 / 16875) * alpha * t ^ 11 + (5396 / 253125) * alpha * t ^ 13 + (-43232 / 6328125) * alpha * t ^ 17 + (-40328 / 18984375) * alpha * t ^ 19 + (-21332 / 6328125) * alpha * t ^ 21 + (-41464 / 18984375) * alpha * t ^ 25) * c_sq
theorem v3_40 (t : ℂ) : (momentPoly 3 z3 4 0).eval t = ((-10066 / 625) * t ^ 6 + (-5033 / 625) * t ^ 8 + (-20132 / 1875) * t ^ 10 + (-5033 / 3750) * t ^ 16 + (584 / 625) * c * t ^ 6 + (292 / 625) * c * t ^ 8 + (1168 / 1875) * c * t ^ 10 + (146 / 1875) * c * t ^ 16 + (-10066 / 625) * alpha * t ^ 6 + (-5033 / 625) * alpha * t ^ 8 + (-20132 / 1875) * alpha * t ^ 10 + (-5033 / 3750) * alpha * t ^ 16 + (-584 / 1875) * alpha * c * t ^ 6 + (-292 / 1875) * alpha * c * t ^ 8 + (-1168 / 5625) * alpha * c * t ^ 10 + (-146 / 5625) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_10, v2_20, v2_30, v2_40]
  simp only [phase1_00, phase1_10, phase1_20, phase1_30, phase1_40]
  linear_combination ((15103 / 5625) * t ^ 6 + (5329 / 1875) * t ^ 8 + (-1768 / 16875) * t ^ 10 + (-392 / 1875) * c * t ^ 6 + (-292 / 5625) * c * t ^ 8 + (-1768 / 16875) * c * t ^ 10 + (4 / 16875) * c ^ 2 * t ^ 6 + (4 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-92 / 1875) * t ^ 6 + (8 / 5625) * t ^ 8 + (-568 / 16875) * t ^ 10 + (-92 / 1875) * alpha * t ^ 6 + (8 / 5625) * alpha * t ^ 8 + (-568 / 16875) * alpha * t ^ 10) * c_sq
theorem v3_41 (t : ℂ) : (momentPoly 3 z3 4 1).eval t = ((-284 / 125) * c * t ^ 3 + (-3124 / 375) * c * t ^ 5 + (-71 / 25) * c * t ^ 9 + (-568 / 375) * c * t ^ 11 + (-142 / 375) * c * t ^ 17 + (-884 / 125) * alpha * t ^ 3 + (-9724 / 375) * alpha * t ^ 5 + (-221 / 25) * alpha * t ^ 9 + (-1768 / 375) * alpha * t ^ 11 + (-442 / 375) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_01, v2_10, v2_11, v2_20, v2_21, v2_30, v2_31, v2_40, v2_41]
  simp only [phase1_00, phase1_01, phase1_10, phase1_11, phase1_20, phase1_21, phase1_30, phase1_31, phase1_40, phase1_41]
  linear_combination ((73 / 125) * t ^ 3 + (1606 / 1125) * t ^ 5 + (15983 / 56250) * t ^ 9 + (21016 / 84375) * t ^ 11 + (5033 / 84375) * t ^ 17 + (217 / 375) * c * t ^ 3 + (4774 / 3375) * c * t ^ 5 + (47941 / 168750) * c * t ^ 9 + (63332 / 253125) * c * t ^ 11 + (15391 / 253125) * c * t ^ 17 + (-2 / 375) * c ^ 2 * t ^ 3 + (-44 / 3375) * c ^ 2 * t ^ 5 + (-4 / 84375) * c ^ 2 * t ^ 9 + (284 / 253125) * c ^ 2 * t ^ 11 + (292 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((-8 / 375) * alpha * t ^ 3 + (-176 / 3375) * alpha * t ^ 5 + (-1184 / 84375) * alpha * t ^ 9 + (-3536 / 253125) * alpha * t ^ 11 + (-1168 / 253125) * alpha * t ^ 17) * c_sq
theorem v3_42 (t : ℂ) : (momentPoly 3 z3 4 2).eval t = ((-584 / 5) * t ^ 2 + (-3869 / 50) * t ^ 4 + (-2336 / 25) * t ^ 6 + (-1022 / 25) * t ^ 10 + (-219 / 25) * t ^ 12 + (-292 / 25) * t ^ 14 + (-73 / 25) * t ^ 18 + (-73 / 25) * t ^ 20 + (-16 / 5) * c * t ^ 2 + (-53 / 25) * c * t ^ 4 + (-64 / 25) * c * t ^ 6 + (-28 / 25) * c * t ^ 10 + (-6 / 25) * c * t ^ 12 + (-8 / 25) * c * t ^ 14 + (-2 / 25) * c * t ^ 18 + (-2 / 25) * c * t ^ 20 + (584 / 5) * alpha * t ^ 2 + (3869 / 50) * alpha * t ^ 4 + (2336 / 25) * alpha * t ^ 6 + (1022 / 25) * alpha * t ^ 10 + (219 / 25) * alpha * t ^ 12 + (292 / 25) * alpha * t ^ 14 + (73 / 25) * alpha * t ^ 18 + (73 / 25) * alpha * t ^ 20 + (-16 / 15) * alpha * c * t ^ 2 + (-53 / 75) * alpha * c * t ^ 4 + (-64 / 75) * alpha * c * t ^ 6 + (-28 / 75) * alpha * c * t ^ 10 + (-2 / 25) * alpha * c * t ^ 12 + (-8 / 75) * alpha * c * t ^ 14 + (-2 / 75) * alpha * c * t ^ 18 + (-2 / 75) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_01, v2_02, v2_10, v2_11, v2_12, v2_20, v2_21, v2_22, v2_30, v2_31, v2_32, v2_40, v2_41, v2_42]
  simp only [phase1_00, phase1_01, phase1_02, phase1_10, phase1_11, phase1_12, phase1_20, phase1_21, phase1_22, phase1_30, phase1_31, phase1_32, phase1_40, phase1_41, phase1_42]
  linear_combination ((8 / 45) * t ^ 2 + (8272 / 16875) * t ^ 6 + (6188 / 16875) * t ^ 10 + (367409 / 281250) * t ^ 12 + (253556 / 140625) * t ^ 14 + (389509 / 843750) * t ^ 18 + (367409 / 421875) * t ^ 20 + (16 / 45) * c * t ^ 2 + (9472 / 16875) * c * t ^ 6 + (6188 / 16875) * c * t ^ 10 + (1 / 75) * c * t ^ 12 + (1484 / 16875) * c * t ^ 14 + (517 / 16875) * c * t ^ 18 + (2 / 225) * c * t ^ 20 + (8 / 45) * c ^ 2 * t ^ 2 + (16 / 225) * c ^ 2 * t ^ 6 + (-292 / 1265625) * c ^ 2 * t ^ 12 + (32582 / 3796875) * c ^ 2 * t ^ 14 + (-292 / 3796875) * c ^ 2 * t ^ 18 + (-584 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-16 / 45) * t ^ 2 + (-4672 / 16875) * t ^ 6 + (-1988 / 16875) * t ^ 10 + (-584 / 421875) * t ^ 12 + (-46136 / 1265625) * t ^ 14 + (-11234 / 1265625) * t ^ 18 + (-1168 / 1265625) * t ^ 20 + (16 / 45) * alpha * t ^ 2 + (4672 / 16875) * alpha * t ^ 6 + (1988 / 16875) * alpha * t ^ 10 + (584 / 421875) * alpha * t ^ 12 + (46136 / 1265625) * alpha * t ^ 14 + (11234 / 1265625) * alpha * t ^ 18 + (1168 / 1265625) * alpha * t ^ 20) * c_sq
theorem v3_43 (t : ℂ) : (momentPoly 3 z3 4 3).eval t = ((-639 / 10) * t + (-216 / 5) * t ^ 3 + (-297 / 5) * t ^ 5 + (-126 / 5) * t ^ 9 + (-9) * t ^ 11 + (-57 / 5) * t ^ 13 + (-9 / 5) * t ^ 17 + (-12 / 5) * t ^ 19 + (-9 / 5) * t ^ 21 + (-3 / 5) * t ^ 25 + (213 / 10) * c * t + (72 / 5) * c * t ^ 3 + (99 / 5) * c * t ^ 5 + (42 / 5) * c * t ^ 9 + 3 * c * t ^ 11 + (19 / 5) * c * t ^ 13 + (3 / 5) * c * t ^ 17 + (4 / 5) * c * t ^ 19 + (3 / 5) * c * t ^ 21 + (1 / 5) * c * t ^ 25 + (213 / 10) * alpha * t + (72 / 5) * alpha * t ^ 3 + (99 / 5) * alpha * t ^ 5 + (42 / 5) * alpha * t ^ 9 + 3 * alpha * t ^ 11 + (19 / 5) * alpha * t ^ 13 + (3 / 5) * alpha * t ^ 17 + (4 / 5) * alpha * t ^ 19 + (3 / 5) * alpha * t ^ 21 + (1 / 5) * alpha * t ^ 25 + (213 / 10) * alpha * c * t + (72 / 5) * alpha * c * t ^ 3 + (99 / 5) * alpha * c * t ^ 5 + (42 / 5) * alpha * c * t ^ 9 + 3 * alpha * c * t ^ 11 + (19 / 5) * alpha * c * t ^ 13 + (3 / 5) * alpha * c * t ^ 17 + (4 / 5) * alpha * c * t ^ 19 + (3 / 5) * alpha * c * t ^ 21 + (1 / 5) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_01, v2_02, v2_03, v2_10, v2_11, v2_12, v2_13, v2_20, v2_21, v2_22, v2_23, v2_30, v2_31, v2_32, v2_33, v2_40, v2_41, v2_42, v2_43]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_10, phase1_11, phase1_12, phase1_13, phase1_20, phase1_21, phase1_22, phase1_23, phase1_30, phase1_31, phase1_32, phase1_33, phase1_40, phase1_41, phase1_42, phase1_43]
  linear_combination ((-292 / 125) * t ^ 3 + (-803 / 125) * t ^ 5 + (187537 / 28125) * t ^ 9 + (10658 / 5625) * t ^ 11 + (613054 / 84375) * t ^ 13 + (-1522918 / 2109375) * t ^ 17 + (390728 / 6328125) * t ^ 19 + (-215261 / 4218750) * t ^ 21 + (-2224586 / 6328125) * t ^ 25 + (-868 / 375) * c * t ^ 3 + (-2387 / 375) * c * t ^ 5 + (-120113 / 84375) * c * t ^ 9 + (-16717 / 16875) * c * t ^ 11 + (-16796 / 253125) * c * t ^ 13 + (-1285157 / 6328125) * c * t ^ 17 + (-390728 / 18984375) * c * t ^ 19 + (-1415989 / 12656250) * c * t ^ 21 + (-129064 / 18984375) * c * t ^ 25 + (8 / 375) * c ^ 2 * t ^ 3 + (22 / 375) * c ^ 2 * t ^ 5 + (14 / 1125) * c ^ 2 * t ^ 9 + (2 / 225) * c ^ 2 * t ^ 11 + (2 / 1125) * c ^ 2 * t ^ 17 + (1 / 1125) * c ^ 2 * t ^ 21) * alpha_sq + ((-16 / 125) * t ^ 3 + (-44 / 125) * t ^ 5 + (-112 / 28125) * t ^ 9 + (-158 / 5625) * t ^ 11 + (5396 / 84375) * t ^ 13 + (-43232 / 2109375) * t ^ 17 + (-40328 / 6328125) * t ^ 19 + (-21332 / 2109375) * t ^ 21 + (-41464 / 6328125) * t ^ 25 + (16 / 375) * alpha * t ^ 3 + (44 / 375) * alpha * t ^ 5 + (112 / 84375) * alpha * t ^ 9 + (158 / 16875) * alpha * t ^ 11 + (-5396 / 253125) * alpha * t ^ 13 + (43232 / 6328125) * alpha * t ^ 17 + (40328 / 18984375) * alpha * t ^ 19 + (21332 / 6328125) * alpha * t ^ 21 + (41464 / 18984375) * alpha * t ^ 25) * c_sq
theorem v3_44 (t : ℂ) : (momentPoly 3 z3 4 4).eval t = (639 + 2736 * t ^ 2 + 1368 * t ^ 6 + 960 * t ^ 8 + 624 * t ^ 14 + 144 * t ^ 18 + 36 * t ^ 24 + 48 * t ^ 26 + 6 * t ^ 32) := by
  rw [momentPoly]
  simp only [z3, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v2_00, v2_01, v2_02, v2_03, v2_04, v2_10, v2_11, v2_12, v2_13, v2_14, v2_20, v2_21, v2_22, v2_23, v2_24, v2_30, v2_31, v2_32, v2_33, v2_34, v2_40, v2_41, v2_42, v2_43, v2_44]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_04, phase1_10, phase1_11, phase1_12, phase1_13, phase1_14, phase1_20, phase1_21, phase1_22, phase1_23, phase1_24, phase1_30, phase1_31, phase1_32, phase1_33, phase1_34, phase1_40, phase1_41, phase1_42, phase1_43, phase1_44]
  linear_combination ((-152 / 75) * t ^ 2 + (-68134 / 625) * t ^ 6 + (-170528 / 1125) * t ^ 8 + (-72800728 / 1265625) * t ^ 14 + (-1562912 / 421875) * t ^ 18 + (-85282339 / 10546875) * t ^ 24 + (-121423256 / 31640625) * t ^ 26 + (-25331089 / 31640625) * t ^ 32 + (-304 / 75) * c * t ^ 2 + (-304 / 5625) * c * t ^ 6 + (9344 / 3375) * c * t ^ 8 + (7384 / 16875) * c * t ^ 14 + (345728 / 31640625) * c * t ^ 24 + (-15132088 / 94921875) * c * t ^ 26 + (-2939272 / 94921875) * c * t ^ 32 + (-152 / 75) * c ^ 2 * t ^ 2 + (-17252 / 16875) * c ^ 2 * t ^ 6 + (-128 / 10125) * c ^ 2 * t ^ 8 + (-11908 / 50625) * c ^ 2 * t ^ 14 + (-130264 / 94921875) * c ^ 2 * t ^ 24 + (-5403556 / 284765625) * c ^ 2 * t ^ 26 + (-85264 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((608 / 75) * t ^ 2 + (23408 / 5625) * t ^ 6 + (512 / 3375) * t ^ 8 + (2280928 / 1265625) * t ^ 14 + (161312 / 421875) * t ^ 18 + (521056 / 31640625) * t ^ 24 + (14163424 / 94921875) * t ^ 26 + (341056 / 94921875) * t ^ 32) * c_sq
#print axioms v3_00
#print axioms v3_11
#print axioms v3_22
#print axioms v3_33
#print axioms v3_44
end PhotonCertA
