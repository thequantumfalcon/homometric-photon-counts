import PhotonCertA9
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z10 : Fin 10 → ℂ := Fin.snoc z9 thetaMinus
theorem v10_00 (t : ℂ) : (momentPoly 10 z10 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00]
  simp only [phase6_00]
  ring
theorem v10_01 (t : ℂ) : (momentPoly 10 z10 0 1).eval t = ((-1) * t + (-1 / 3) * alpha * t) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_01]
  simp only [phase6_00, phase6_01]
  ring
theorem v10_02 (t : ℂ) : (momentPoly 10 z10 0 2).eval t = ((83 / 15) * t ^ 2 + (-73 / 15) * t ^ 4 + (83 / 15) * alpha * t ^ 2 + (-73 / 15) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_01, v9_02]
  simp only [phase6_00, phase6_01, phase6_02]
  linear_combination ((1 / 50) * t ^ 2 + (-4 / 225) * c * t ^ 2 + (-1 / 450) * c ^ 2 * t ^ 2) * alpha_sq + ((1 / 225) * t ^ 2 + (1 / 225) * alpha * t ^ 2) * c_sq
theorem v10_03 (t : ℂ) : (momentPoly 10 z10 0 3).eval t = ((-1232 / 75) * alpha * t ^ 3 + (1018 / 75) * alpha * t ^ 5 + (442 / 225) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_01, v9_02, v9_03]
  simp only [phase6_00, phase6_01, phase6_02, phase6_03]
  linear_combination ((-166 / 375) * t ^ 3 + (219 / 250) * t ^ 5 + (494 / 1125) * c * t ^ 3 + (-434 / 1125) * c * t ^ 5 + (4 / 1125) * c ^ 2 * t ^ 3 + (1 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-16 / 1125) * alpha * t ^ 3 + (-4 / 1125) * alpha * t ^ 5) * c_sq
theorem v10_04 (t : ℂ) : (momentPoly 10 z10 0 4).eval t = ((-52264 / 375) * t ^ 4 + (30736 / 125) * t ^ 6 + (-48257 / 375) * t ^ 8 + (28972 / 1125) * t ^ 10 + (-5033 / 1125) * t ^ 16 + (52264 / 375) * alpha * t ^ 4 + (-30736 / 125) * alpha * t ^ 6 + (48257 / 375) * alpha * t ^ 8 + (-28972 / 1125) * alpha * t ^ 10 + (5033 / 1125) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_01, v9_02, v9_03, v9_04]
  simp only [phase6_00, phase6_01, phase6_02, phase6_03, phase6_04]
  linear_combination ((8624 / 5625) * t ^ 4 + (-80852 / 5625) * t ^ 6 + (15987 / 1250) * t ^ 8 + (-884 / 1875) * t ^ 10 + (-8624 / 5625) * c * t ^ 4 + (6896 / 5625) * c * t ^ 6 + (584 / 5625) * c * t ^ 8 + (3536 / 16875) * c * t ^ 10 + (-16 / 16875) * c ^ 2 * t ^ 6 + (-2 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-144 / 625) * t ^ 4 + (368 / 1875) * t ^ 6 + (-4 / 5625) * t ^ 8 + (284 / 16875) * t ^ 10 + (144 / 625) * alpha * t ^ 4 + (-368 / 1875) * alpha * t ^ 6 + (4 / 5625) * alpha * t ^ 8 + (-284 / 16875) * alpha * t ^ 10) * c_sq
theorem v10_10 (t : ℂ) : (momentPoly 10 z10 1 0).eval t = ((-1) * t + (1 / 3) * alpha * t) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_10]
  simp only [phase6_00, phase6_10]
  ring
theorem v10_11 (t : ℂ) : (momentPoly 10 z10 1 1).eval t = (10 + (-26 / 3) * t ^ 2) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_01, v9_10, v9_11]
  simp only [phase6_00, phase6_01, phase6_10, phase6_11]
  linear_combination ((-1 / 50) * t ^ 2 + (4 / 225) * c * t ^ 2 + (1 / 450) * c ^ 2 * t ^ 2) * alpha_sq + ((-2 / 225) * t ^ 2) * c_sq
theorem v10_12 (t : ℂ) : (momentPoly 10 z10 1 2).eval t = ((-19) * t + (104 / 15) * t ^ 3 + (161 / 15) * t ^ 5 + (-19 / 3) * alpha * t + (104 / 45) * alpha * t ^ 3 + (161 / 45) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_01, v9_02, v9_10, v9_11, v9_12]
  simp only [phase6_00, phase6_01, phase6_02, phase6_10, phase6_11, phase6_12]
  linear_combination ((166 / 1125) * t ^ 3 + (-73 / 250) * t ^ 5 + (-494 / 3375) * c * t ^ 3 + (434 / 3375) * c * t ^ 5 + (-4 / 3375) * c ^ 2 * t ^ 3 + (-1 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((8 / 1125) * t ^ 3 + (2 / 1125) * t ^ 5 + (8 / 3375) * alpha * t ^ 3 + (2 / 3375) * alpha * t ^ 5) * c_sq
theorem v10_13 (t : ℂ) : (momentPoly 10 z10 1 3).eval t = ((747 / 5) * t ^ 2 + (-6316 / 25) * t ^ 4 + (7592 / 75) * t ^ 6 + (653 / 225) * t ^ 10 + (747 / 5) * alpha * t ^ 2 + (-6316 / 25) * alpha * t ^ 4 + (7592 / 75) * alpha * t ^ 6 + (653 / 225) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_01, v9_02, v9_03, v9_10, v9_11, v9_12, v9_13]
  simp only [phase6_00, phase6_01, phase6_02, phase6_03, phase6_10, phase6_11, phase6_12, phase6_13]
  linear_combination ((27 / 50) * t ^ 2 + (-1022 / 1875) * t ^ 4 + (142 / 1875) * t ^ 6 + (221 / 1875) * t ^ 10 + (-12 / 25) * c * t ^ 2 + (2636 / 5625) * c * t ^ 4 + (-92 / 1875) * c * t ^ 6 + (-884 / 16875) * c * t ^ 10 + (-3 / 50) * c ^ 2 * t ^ 2 + (86 / 1125) * c ^ 2 * t ^ 4 + (-2 / 75) * c ^ 2 * t ^ 6) * alpha_sq + ((3 / 25) * t ^ 2 + (-1184 / 5625) * t ^ 4 + (584 / 5625) * t ^ 6 + (71 / 16875) * t ^ 10 + (3 / 25) * alpha * t ^ 2 + (-1184 / 5625) * alpha * t ^ 4 + (584 / 5625) * alpha * t ^ 6 + (71 / 16875) * alpha * t ^ 10) * c_sq
theorem v10_14 (t : ℂ) : (momentPoly 10 z10 1 4).eval t = ((-41888 / 75) * alpha * t ^ 3 + (847924 / 1125) * alpha * t ^ 5 + (-992 / 125) * alpha * t ^ 7 + (-47266 / 375) * alpha * t ^ 9 + (-183872 / 3375) * alpha * t ^ 11 + (-26762 / 3375) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_01, v9_02, v9_03, v9_04, v9_10, v9_11, v9_12, v9_13, v9_14]
  simp only [phase6_00, phase6_01, phase6_02, phase6_03, phase6_04, phase6_10, phase6_11, phase6_12, phase6_13, phase6_14]
  linear_combination ((-5644 / 375) * t ^ 3 + (134529 / 3125) * t ^ 5 + (-62216 / 3125) * t ^ 7 + (-15394 / 3125) * t ^ 9 + (-84064 / 84375) * t ^ 11 + (5033 / 18750) * t ^ 17 + (16796 / 1125) * c * t ^ 3 + (-2167592 / 84375) * c * t ^ 5 + (1094968 / 84375) * c * t ^ 7 + (-25522 / 9375) * c * t ^ 9 + (253328 / 253125) * c * t ^ 11 + (-30782 / 253125) * c * t ^ 17 + (136 / 1125) * c ^ 2 * t ^ 3 + (-566 / 84375) * c ^ 2 * t ^ 5 + (-824 / 9375) * c ^ 2 * t ^ 7 + (16 / 84375) * c ^ 2 * t ^ 9 + (-1136 / 253125) * c ^ 2 * t ^ 11 + (-146 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((-544 / 1125) * alpha * t ^ 3 + (31576 / 84375) * alpha * t ^ 5 + (3872 / 28125) * alpha * t ^ 7 + (-4736 / 84375) * alpha * t ^ 9 + (-14144 / 253125) * alpha * t ^ 11 + (-584 / 253125) * alpha * t ^ 17) * c_sq
theorem v10_20 (t : ℂ) : (momentPoly 10 z10 2 0).eval t = ((83 / 15) * t ^ 2 + (-73 / 15) * t ^ 4 + (-83 / 15) * alpha * t ^ 2 + (73 / 15) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_10, v9_20]
  simp only [phase6_00, phase6_10, phase6_20]
  linear_combination ((1 / 50) * t ^ 2 + (-4 / 225) * c * t ^ 2 + (-1 / 450) * c ^ 2 * t ^ 2) * alpha_sq + ((1 / 225) * t ^ 2 + (-1 / 225) * alpha * t ^ 2) * c_sq
theorem v10_21 (t : ℂ) : (momentPoly 10 z10 2 1).eval t = ((-19) * t + (104 / 15) * t ^ 3 + (161 / 15) * t ^ 5 + (19 / 3) * alpha * t + (-104 / 45) * alpha * t ^ 3 + (-161 / 45) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_01, v9_10, v9_11, v9_20, v9_21]
  simp only [phase6_00, phase6_01, phase6_10, phase6_11, phase6_20, phase6_21]
  linear_combination ((166 / 1125) * t ^ 3 + (-73 / 250) * t ^ 5 + (-494 / 3375) * c * t ^ 3 + (434 / 3375) * c * t ^ 5 + (-4 / 3375) * c ^ 2 * t ^ 3 + (-1 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((8 / 1125) * t ^ 3 + (2 / 1125) * t ^ 5 + (-8 / 3375) * alpha * t ^ 3 + (-2 / 3375) * alpha * t ^ 5) * c_sq
theorem v10_22 (t : ℂ) : (momentPoly 10 z10 2 2).eval t = (190 + (-312) * t ^ 2 + (49456 / 225) * t ^ 4 + (-40672 / 225) * t ^ 6 + (19066 / 225) * t ^ 8) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_01, v9_02, v9_10, v9_11, v9_12, v9_20, v9_21, v9_22]
  simp only [phase6_00, phase6_01, phase6_02, phase6_10, phase6_11, phase6_12, phase6_20, phase6_21, phase6_22]
  linear_combination ((-18 / 25) * t ^ 2 + (728 / 3375) * t ^ 4 + (79148 / 16875) * t ^ 6 + (-5329 / 1250) * t ^ 8 + (16 / 25) * c * t ^ 2 + (-128 / 1125) * c * t ^ 4 + (-5792 / 16875) * c * t ^ 6 + (-584 / 16875) * c * t ^ 8 + (2 / 25) * c ^ 2 * t ^ 2 + (-344 / 3375) * c ^ 2 * t ^ 4 + (1816 / 50625) * c ^ 2 * t ^ 6 + (2 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((-8 / 25) * t ^ 2 + (1376 / 3375) * t ^ 4 + (-2464 / 16875) * t ^ 6 + (-8 / 16875) * t ^ 8) * c_sq
theorem v10_23 (t : ℂ) : (momentPoly 10 z10 2 3).eval t = ((-514) * t + (1768 / 5) * t ^ 3 + (54623 / 125) * t ^ 5 + (-4384 / 75) * t ^ 7 + (-76264 / 375) * t ^ 9 + (12536 / 1125) * t ^ 11 + (-31141 / 1125) * t ^ 13 + (-514 / 3) * alpha * t + (1768 / 15) * alpha * t ^ 3 + (54623 / 375) * alpha * t ^ 5 + (-4384 / 225) * alpha * t ^ 7 + (-76264 / 1125) * alpha * t ^ 9 + (12536 / 3375) * alpha * t ^ 11 + (-31141 / 3375) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_01, v9_02, v9_03, v9_10, v9_11, v9_12, v9_13, v9_20, v9_21, v9_22, v9_23]
  simp only [phase6_00, phase6_01, phase6_02, phase6_03, phase6_10, phase6_11, phase6_12, phase6_13, phase6_20, phase6_21, phase6_22, phase6_23]
  linear_combination ((2822 / 375) * t ^ 3 + (-75491 / 3750) * t ^ 5 + (41902 / 28125) * t ^ 7 + (266158 / 28125) * t ^ 9 + (-20104 / 28125) * t ^ 11 + (16133 / 9375) * t ^ 13 + (-8398 / 1125) * c * t ^ 3 + (192874 / 16875) * c * t ^ 5 + (-102874 / 28125) * c * t ^ 7 + (-25558 / 84375) * c * t ^ 9 + (-40348 / 253125) * c * t ^ 11 + (1768 / 253125) * c * t ^ 13 + (-68 / 1125) * c ^ 2 * t ^ 3 + (47 / 1875) * c ^ 2 * t ^ 5 + (172 / 5625) * c ^ 2 * t ^ 7 + (-4 / 1125) * c ^ 2 * t ^ 9 + (-8 / 3375) * c ^ 2 * t ^ 11) * alpha_sq + ((136 / 375) * t ^ 3 + (-94 / 625) * t ^ 5 + (-1504 / 9375) * t ^ 7 + (32 / 28125) * t ^ 9 + (632 / 84375) * t ^ 11 + (-142 / 84375) * t ^ 13 + (136 / 1125) * alpha * t ^ 3 + (-94 / 1875) * alpha * t ^ 5 + (-1504 / 28125) * alpha * t ^ 7 + (32 / 84375) * alpha * t ^ 9 + (632 / 253125) * alpha * t ^ 11 + (-142 / 253125) * alpha * t ^ 13) * c_sq
theorem v10_24 (t : ℂ) : (momentPoly 10 z10 2 4).eval t = ((76526 / 15) * t ^ 2 + (-306769 / 25) * t ^ 4 + (57140624 / 5625) * t ^ 6 + (-26673872 / 5625) * t ^ 8 + (3275966 / 1125) * t ^ 10 + (-23287768 / 16875) * t ^ 12 + (3660512 / 16875) * t ^ 14 + (737528 / 16875) * t ^ 18 + (-652693 / 16875) * t ^ 20 + (76526 / 15) * alpha * t ^ 2 + (-306769 / 25) * alpha * t ^ 4 + (57140624 / 5625) * alpha * t ^ 6 + (-26673872 / 5625) * alpha * t ^ 8 + (3275966 / 1125) * alpha * t ^ 10 + (-23287768 / 16875) * alpha * t ^ 12 + (3660512 / 16875) * alpha * t ^ 14 + (737528 / 16875) * alpha * t ^ 18 + (-652693 / 16875) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_01, v9_02, v9_03, v9_04, v9_10, v9_11, v9_12, v9_13, v9_14, v9_20, v9_21, v9_22, v9_23, v9_24]
  simp only [phase6_00, phase6_01, phase6_02, phase6_03, phase6_04, phase6_10, phase6_11, phase6_12, phase6_13, phase6_14, phase6_20, phase6_21, phase6_22, phase6_23, phase6_24]
  linear_combination ((461 / 25) * t ^ 2 + (-65408 / 1875) * t ^ 4 + (288848 / 16875) * t ^ 6 + (5897468 / 140625) * t ^ 8 + (-11033722 / 140625) * t ^ 10 + (58144298 / 1265625) * t ^ 12 + (-14290576 / 1265625) * t ^ 14 + (-3041674 / 1265625) * t ^ 18 + (367409 / 93750) * t ^ 20 + (-3688 / 225) * c * t ^ 2 + (168704 / 5625) * c * t ^ 4 + (-115376 / 9375) * c * t ^ 6 + (-114248 / 28125) * c * t ^ 8 + (-11368 / 28125) * c * t ^ 10 + (77732 / 28125) * c * t ^ 12 + (-11744 / 16875) * c * t ^ 14 + (12524 / 28125) * c * t ^ 18 + (-4 / 225) * c * t ^ 20 + (-461 / 225) * c ^ 2 * t ^ 2 + (5504 / 1125) * c ^ 2 * t ^ 4 + (-405856 / 84375) * c ^ 2 * t ^ 6 + (3230752 / 1265625) * c ^ 2 * t ^ 8 + (-289816 / 421875) * c ^ 2 * t ^ 10 + (3944 / 46875) * c ^ 2 * t ^ 12 + (-130328 / 3796875) * c ^ 2 * t ^ 14 + (1168 / 3796875) * c ^ 2 * t ^ 18 + (292 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((922 / 225) * t ^ 2 + (-75776 / 5625) * t ^ 4 + (1365328 / 84375) * t ^ 6 + (-3638816 / 421875) * t ^ 8 + (1037794 / 421875) * t ^ 10 + (-936352 / 1265625) * t ^ 12 + (184544 / 1265625) * t ^ 14 + (44936 / 1265625) * t ^ 18 + (584 / 1265625) * t ^ 20 + (922 / 225) * alpha * t ^ 2 + (-75776 / 5625) * alpha * t ^ 4 + (1365328 / 84375) * alpha * t ^ 6 + (-3638816 / 421875) * alpha * t ^ 8 + (1037794 / 421875) * alpha * t ^ 10 + (-936352 / 1265625) * alpha * t ^ 12 + (184544 / 1265625) * alpha * t ^ 14 + (44936 / 1265625) * alpha * t ^ 18 + (584 / 1265625) * alpha * t ^ 20) * c_sq
theorem v10_30 (t : ℂ) : (momentPoly 10 z10 3 0).eval t = ((1232 / 75) * alpha * t ^ 3 + (-1018 / 75) * alpha * t ^ 5 + (-442 / 225) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_10, v9_20, v9_30]
  simp only [phase6_00, phase6_10, phase6_20, phase6_30]
  linear_combination ((-166 / 375) * t ^ 3 + (219 / 250) * t ^ 5 + (494 / 1125) * c * t ^ 3 + (-434 / 1125) * c * t ^ 5 + (4 / 1125) * c ^ 2 * t ^ 3 + (1 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((16 / 1125) * alpha * t ^ 3 + (4 / 1125) * alpha * t ^ 5) * c_sq
theorem v10_31 (t : ℂ) : (momentPoly 10 z10 3 1).eval t = ((747 / 5) * t ^ 2 + (-6316 / 25) * t ^ 4 + (7592 / 75) * t ^ 6 + (653 / 225) * t ^ 10 + (-747 / 5) * alpha * t ^ 2 + (6316 / 25) * alpha * t ^ 4 + (-7592 / 75) * alpha * t ^ 6 + (-653 / 225) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_01, v9_10, v9_11, v9_20, v9_21, v9_30, v9_31]
  simp only [phase6_00, phase6_01, phase6_10, phase6_11, phase6_20, phase6_21, phase6_30, phase6_31]
  linear_combination ((27 / 50) * t ^ 2 + (-1022 / 1875) * t ^ 4 + (142 / 1875) * t ^ 6 + (221 / 1875) * t ^ 10 + (-12 / 25) * c * t ^ 2 + (2636 / 5625) * c * t ^ 4 + (-92 / 1875) * c * t ^ 6 + (-884 / 16875) * c * t ^ 10 + (-3 / 50) * c ^ 2 * t ^ 2 + (86 / 1125) * c ^ 2 * t ^ 4 + (-2 / 75) * c ^ 2 * t ^ 6) * alpha_sq + ((3 / 25) * t ^ 2 + (-1184 / 5625) * t ^ 4 + (584 / 5625) * t ^ 6 + (71 / 16875) * t ^ 10 + (-3 / 25) * alpha * t ^ 2 + (1184 / 5625) * alpha * t ^ 4 + (-584 / 5625) * alpha * t ^ 6 + (-71 / 16875) * alpha * t ^ 10) * c_sq
theorem v10_32 (t : ℂ) : (momentPoly 10 z10 3 2).eval t = ((-514) * t + (1768 / 5) * t ^ 3 + (54623 / 125) * t ^ 5 + (-4384 / 75) * t ^ 7 + (-76264 / 375) * t ^ 9 + (12536 / 1125) * t ^ 11 + (-31141 / 1125) * t ^ 13 + (514 / 3) * alpha * t + (-1768 / 15) * alpha * t ^ 3 + (-54623 / 375) * alpha * t ^ 5 + (4384 / 225) * alpha * t ^ 7 + (76264 / 1125) * alpha * t ^ 9 + (-12536 / 3375) * alpha * t ^ 11 + (31141 / 3375) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_01, v9_02, v9_10, v9_11, v9_12, v9_20, v9_21, v9_22, v9_30, v9_31, v9_32]
  simp only [phase6_00, phase6_01, phase6_02, phase6_10, phase6_11, phase6_12, phase6_20, phase6_21, phase6_22, phase6_30, phase6_31, phase6_32]
  linear_combination ((2822 / 375) * t ^ 3 + (-75491 / 3750) * t ^ 5 + (41902 / 28125) * t ^ 7 + (266158 / 28125) * t ^ 9 + (-20104 / 28125) * t ^ 11 + (16133 / 9375) * t ^ 13 + (-8398 / 1125) * c * t ^ 3 + (192874 / 16875) * c * t ^ 5 + (-102874 / 28125) * c * t ^ 7 + (-25558 / 84375) * c * t ^ 9 + (-40348 / 253125) * c * t ^ 11 + (1768 / 253125) * c * t ^ 13 + (-68 / 1125) * c ^ 2 * t ^ 3 + (47 / 1875) * c ^ 2 * t ^ 5 + (172 / 5625) * c ^ 2 * t ^ 7 + (-4 / 1125) * c ^ 2 * t ^ 9 + (-8 / 3375) * c ^ 2 * t ^ 11) * alpha_sq + ((136 / 375) * t ^ 3 + (-94 / 625) * t ^ 5 + (-1504 / 9375) * t ^ 7 + (32 / 28125) * t ^ 9 + (632 / 84375) * t ^ 11 + (-142 / 84375) * t ^ 13 + (-136 / 1125) * alpha * t ^ 3 + (94 / 1875) * alpha * t ^ 5 + (1504 / 28125) * alpha * t ^ 7 + (-32 / 84375) * alpha * t ^ 9 + (-632 / 253125) * alpha * t ^ 11 + (142 / 253125) * alpha * t ^ 13) * c_sq
theorem v10_33 (t : ℂ) : (momentPoly 10 z10 3 3).eval t = (5140 + (-11986) * t ^ 2 + (395648 / 25) * t ^ 4 + (-12625792 / 625) * t ^ 6 + (28498948 / 1875) * t ^ 8 + (-7555376 / 1875) * t ^ 10 + (1961312 / 5625) * t ^ 12 + (-1667488 / 5625) * t ^ 14 + (26614 / 16875) * t ^ 18) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_01, v9_02, v9_03, v9_10, v9_11, v9_12, v9_13, v9_20, v9_21, v9_22, v9_23, v9_30, v9_31, v9_32, v9_33]
  simp only [phase6_00, phase6_01, phase6_02, phase6_03, phase6_10, phase6_11, phase6_12, phase6_13, phase6_20, phase6_21, phase6_22, phase6_23, phase6_30, phase6_31, phase6_32, phase6_33]
  linear_combination ((-1383 / 50) * t ^ 2 + (5824 / 375) * t ^ 4 + (217108 / 625) * t ^ 6 + (-5050817 / 9375) * t ^ 8 + (5552344 / 28125) * t ^ 10 + (708428 / 140625) * t ^ 12 + (145832 / 140625) * t ^ 14 + (-97682 / 140625) * t ^ 18 + (1844 / 75) * c * t ^ 2 + (-1024 / 125) * c * t ^ 4 + (-728288 / 28125) * c * t ^ 6 + (-4816 / 28125) * c * t ^ 8 + (29536 / 3125) * c * t ^ 10 + (-33344 / 84375) * c * t ^ 12 + (134048 / 84375) * c * t ^ 14 + (461 / 150) * c ^ 2 * t ^ 2 + (-2752 / 375) * c ^ 2 * t ^ 4 + (610784 / 84375) * c ^ 2 * t ^ 6 + (-108308 / 28125) * c ^ 2 * t ^ 8 + (86708 / 84375) * c ^ 2 * t ^ 10 + (-10532 / 84375) * c ^ 2 * t ^ 12 + (916 / 16875) * c ^ 2 * t ^ 14) * alpha_sq + ((-922 / 75) * t ^ 2 + (11008 / 375) * t ^ 4 + (-819712 / 28125) * t ^ 6 + (436208 / 28125) * t ^ 8 + (-113776 / 28125) * t ^ 10 + (302656 / 421875) * t ^ 12 + (-175456 / 421875) * t ^ 14 + (-10082 / 1265625) * t ^ 18) * c_sq
theorem v10_34 (t : ℂ) : (momentPoly 10 z10 3 4).eval t = ((-17587) * t + (85488 / 5) * t ^ 3 + (417299 / 25) * t ^ 5 + (-26597248 / 9375) * t ^ 7 + (-171193792 / 9375) * t ^ 9 + (10660232 / 9375) * t ^ 11 + (8735689 / 5625) * t ^ 13 + (42391568 / 28125) * t ^ 15 + (19518344 / 28125) * t ^ 17 + (-21848392 / 84375) * t ^ 19 + (6553544 / 28125) * t ^ 21 + (2308961 / 84375) * t ^ 25 + (-17587 / 3) * alpha * t + (28496 / 5) * alpha * t ^ 3 + (417299 / 75) * alpha * t ^ 5 + (-26597248 / 28125) * alpha * t ^ 7 + (-171193792 / 28125) * alpha * t ^ 9 + (10660232 / 28125) * alpha * t ^ 11 + (8735689 / 16875) * alpha * t ^ 13 + (42391568 / 84375) * alpha * t ^ 15 + (19518344 / 84375) * alpha * t ^ 17 + (-21848392 / 253125) * alpha * t ^ 19 + (6553544 / 84375) * alpha * t ^ 21 + (2308961 / 253125) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_01, v9_02, v9_03, v9_04, v9_10, v9_11, v9_12, v9_13, v9_14, v9_20, v9_21, v9_22, v9_23, v9_24, v9_30, v9_31, v9_32, v9_33, v9_34]
  simp only [phase6_00, phase6_01, phase6_02, phase6_03, phase6_04, phase6_10, phase6_11, phase6_12, phase6_13, phase6_14, phase6_20, phase6_21, phase6_22, phase6_23, phase6_24, phase6_30, phase6_31, phase6_32, phase6_33, phase6_34]
  linear_combination ((45484 / 125) * t ^ 3 + (-298989 / 250) * t ^ 5 + (4319396 / 15625) * t ^ 7 + (1549192 / 1875) * t ^ 9 + (2375348 / 46875) * t ^ 11 + (-51251663 / 234375) * t ^ 13 + (-115529372 / 2109375) * t ^ 15 + (-9791672 / 234375) * t ^ 17 + (21993254 / 2109375) * t ^ 19 + (-36310378 / 2109375) * t ^ 21 + (-1112293 / 703125) * t ^ 25 + (-135356 / 375) * c * t ^ 3 + (852142 / 1125) * c * t ^ 5 + (-323332 / 675) * c * t ^ 7 + (60369008 / 421875) * c * t ^ 9 + (-17246272 / 140625) * c * t ^ 11 + (17750554 / 234375) * c * t ^ 13 + (-85340932 / 6328125) * c * t ^ 15 + (-2143756 / 2109375) * c * t ^ 17 + (-62355878 / 18984375) * c * t ^ 19 + (19662562 / 6328125) * c * t ^ 21 + (258128 / 18984375) * c * t ^ 25 + (-1096 / 375) * c ^ 2 * t ^ 3 + (3241 / 1125) * c ^ 2 * t ^ 5 + (700888 / 421875) * c ^ 2 * t ^ 7 + (-760816 / 421875) * c ^ 2 * t ^ 9 + (111088 / 421875) * c ^ 2 * t ^ 11 + (1756 / 46875) * c ^ 2 * t ^ 13 + (-273064 / 1265625) * c ^ 2 * t ^ 15 + (-8 / 1125) * c ^ 2 * t ^ 17 + (54932 / 1265625) * c ^ 2 * t ^ 19 + (-4 / 1125) * c ^ 2 * t ^ 21) * alpha_sq + ((2192 / 125) * t ^ 3 + (-6482 / 375) * t ^ 5 + (-1097216 / 140625) * t ^ 7 + (973696 / 140625) * t ^ 9 + (-22808 / 140625) * t ^ 11 + (-1348738 / 2109375) * t ^ 13 + (4027952 / 2109375) * t ^ 15 + (172928 / 2109375) * t ^ 17 + (-1770472 / 6328125) * t ^ 19 + (85328 / 2109375) * t ^ 21 + (20732 / 6328125) * t ^ 25 + (2192 / 375) * alpha * t ^ 3 + (-6482 / 1125) * alpha * t ^ 5 + (-1097216 / 421875) * alpha * t ^ 7 + (973696 / 421875) * alpha * t ^ 9 + (-22808 / 421875) * alpha * t ^ 11 + (-1348738 / 6328125) * alpha * t ^ 13 + (4027952 / 6328125) * alpha * t ^ 15 + (172928 / 6328125) * alpha * t ^ 17 + (-1770472 / 18984375) * alpha * t ^ 19 + (85328 / 6328125) * alpha * t ^ 21 + (20732 / 18984375) * alpha * t ^ 25) * c_sq
theorem v10_40 (t : ℂ) : (momentPoly 10 z10 4 0).eval t = ((-52264 / 375) * t ^ 4 + (30736 / 125) * t ^ 6 + (-48257 / 375) * t ^ 8 + (28972 / 1125) * t ^ 10 + (-5033 / 1125) * t ^ 16 + (-52264 / 375) * alpha * t ^ 4 + (30736 / 125) * alpha * t ^ 6 + (-48257 / 375) * alpha * t ^ 8 + (28972 / 1125) * alpha * t ^ 10 + (-5033 / 1125) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_10, v9_20, v9_30, v9_40]
  simp only [phase6_00, phase6_10, phase6_20, phase6_30, phase6_40]
  linear_combination ((8624 / 5625) * t ^ 4 + (-80852 / 5625) * t ^ 6 + (15987 / 1250) * t ^ 8 + (-884 / 1875) * t ^ 10 + (-8624 / 5625) * c * t ^ 4 + (6896 / 5625) * c * t ^ 6 + (584 / 5625) * c * t ^ 8 + (3536 / 16875) * c * t ^ 10 + (-16 / 16875) * c ^ 2 * t ^ 6 + (-2 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-144 / 625) * t ^ 4 + (368 / 1875) * t ^ 6 + (-4 / 5625) * t ^ 8 + (284 / 16875) * t ^ 10 + (-144 / 625) * alpha * t ^ 4 + (368 / 1875) * alpha * t ^ 6 + (-4 / 5625) * alpha * t ^ 8 + (284 / 16875) * alpha * t ^ 10) * c_sq
theorem v10_41 (t : ℂ) : (momentPoly 10 z10 4 1).eval t = ((41888 / 75) * alpha * t ^ 3 + (-847924 / 1125) * alpha * t ^ 5 + (992 / 125) * alpha * t ^ 7 + (47266 / 375) * alpha * t ^ 9 + (183872 / 3375) * alpha * t ^ 11 + (26762 / 3375) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_01, v9_10, v9_11, v9_20, v9_21, v9_30, v9_31, v9_40, v9_41]
  simp only [phase6_00, phase6_01, phase6_10, phase6_11, phase6_20, phase6_21, phase6_30, phase6_31, phase6_40, phase6_41]
  linear_combination ((-5644 / 375) * t ^ 3 + (134529 / 3125) * t ^ 5 + (-62216 / 3125) * t ^ 7 + (-15394 / 3125) * t ^ 9 + (-84064 / 84375) * t ^ 11 + (5033 / 18750) * t ^ 17 + (16796 / 1125) * c * t ^ 3 + (-2167592 / 84375) * c * t ^ 5 + (1094968 / 84375) * c * t ^ 7 + (-25522 / 9375) * c * t ^ 9 + (253328 / 253125) * c * t ^ 11 + (-30782 / 253125) * c * t ^ 17 + (136 / 1125) * c ^ 2 * t ^ 3 + (-566 / 84375) * c ^ 2 * t ^ 5 + (-824 / 9375) * c ^ 2 * t ^ 7 + (16 / 84375) * c ^ 2 * t ^ 9 + (-1136 / 253125) * c ^ 2 * t ^ 11 + (-146 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((544 / 1125) * alpha * t ^ 3 + (-31576 / 84375) * alpha * t ^ 5 + (-3872 / 28125) * alpha * t ^ 7 + (4736 / 84375) * alpha * t ^ 9 + (14144 / 253125) * alpha * t ^ 11 + (584 / 253125) * alpha * t ^ 17) * c_sq
theorem v10_42 (t : ℂ) : (momentPoly 10 z10 4 2).eval t = ((76526 / 15) * t ^ 2 + (-306769 / 25) * t ^ 4 + (57140624 / 5625) * t ^ 6 + (-26673872 / 5625) * t ^ 8 + (3275966 / 1125) * t ^ 10 + (-23287768 / 16875) * t ^ 12 + (3660512 / 16875) * t ^ 14 + (737528 / 16875) * t ^ 18 + (-652693 / 16875) * t ^ 20 + (-76526 / 15) * alpha * t ^ 2 + (306769 / 25) * alpha * t ^ 4 + (-57140624 / 5625) * alpha * t ^ 6 + (26673872 / 5625) * alpha * t ^ 8 + (-3275966 / 1125) * alpha * t ^ 10 + (23287768 / 16875) * alpha * t ^ 12 + (-3660512 / 16875) * alpha * t ^ 14 + (-737528 / 16875) * alpha * t ^ 18 + (652693 / 16875) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_01, v9_02, v9_10, v9_11, v9_12, v9_20, v9_21, v9_22, v9_30, v9_31, v9_32, v9_40, v9_41, v9_42]
  simp only [phase6_00, phase6_01, phase6_02, phase6_10, phase6_11, phase6_12, phase6_20, phase6_21, phase6_22, phase6_30, phase6_31, phase6_32, phase6_40, phase6_41, phase6_42]
  linear_combination ((461 / 25) * t ^ 2 + (-65408 / 1875) * t ^ 4 + (288848 / 16875) * t ^ 6 + (5897468 / 140625) * t ^ 8 + (-11033722 / 140625) * t ^ 10 + (58144298 / 1265625) * t ^ 12 + (-14290576 / 1265625) * t ^ 14 + (-3041674 / 1265625) * t ^ 18 + (367409 / 93750) * t ^ 20 + (-3688 / 225) * c * t ^ 2 + (168704 / 5625) * c * t ^ 4 + (-115376 / 9375) * c * t ^ 6 + (-114248 / 28125) * c * t ^ 8 + (-11368 / 28125) * c * t ^ 10 + (77732 / 28125) * c * t ^ 12 + (-11744 / 16875) * c * t ^ 14 + (12524 / 28125) * c * t ^ 18 + (-4 / 225) * c * t ^ 20 + (-461 / 225) * c ^ 2 * t ^ 2 + (5504 / 1125) * c ^ 2 * t ^ 4 + (-405856 / 84375) * c ^ 2 * t ^ 6 + (3230752 / 1265625) * c ^ 2 * t ^ 8 + (-289816 / 421875) * c ^ 2 * t ^ 10 + (3944 / 46875) * c ^ 2 * t ^ 12 + (-130328 / 3796875) * c ^ 2 * t ^ 14 + (1168 / 3796875) * c ^ 2 * t ^ 18 + (292 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((922 / 225) * t ^ 2 + (-75776 / 5625) * t ^ 4 + (1365328 / 84375) * t ^ 6 + (-3638816 / 421875) * t ^ 8 + (1037794 / 421875) * t ^ 10 + (-936352 / 1265625) * t ^ 12 + (184544 / 1265625) * t ^ 14 + (44936 / 1265625) * t ^ 18 + (584 / 1265625) * t ^ 20 + (-922 / 225) * alpha * t ^ 2 + (75776 / 5625) * alpha * t ^ 4 + (-1365328 / 84375) * alpha * t ^ 6 + (3638816 / 421875) * alpha * t ^ 8 + (-1037794 / 421875) * alpha * t ^ 10 + (936352 / 1265625) * alpha * t ^ 12 + (-184544 / 1265625) * alpha * t ^ 14 + (-44936 / 1265625) * alpha * t ^ 18 + (-584 / 1265625) * alpha * t ^ 20) * c_sq
theorem v10_43 (t : ℂ) : (momentPoly 10 z10 4 3).eval t = ((-17587) * t + (85488 / 5) * t ^ 3 + (417299 / 25) * t ^ 5 + (-26597248 / 9375) * t ^ 7 + (-171193792 / 9375) * t ^ 9 + (10660232 / 9375) * t ^ 11 + (8735689 / 5625) * t ^ 13 + (42391568 / 28125) * t ^ 15 + (19518344 / 28125) * t ^ 17 + (-21848392 / 84375) * t ^ 19 + (6553544 / 28125) * t ^ 21 + (2308961 / 84375) * t ^ 25 + (17587 / 3) * alpha * t + (-28496 / 5) * alpha * t ^ 3 + (-417299 / 75) * alpha * t ^ 5 + (26597248 / 28125) * alpha * t ^ 7 + (171193792 / 28125) * alpha * t ^ 9 + (-10660232 / 28125) * alpha * t ^ 11 + (-8735689 / 16875) * alpha * t ^ 13 + (-42391568 / 84375) * alpha * t ^ 15 + (-19518344 / 84375) * alpha * t ^ 17 + (21848392 / 253125) * alpha * t ^ 19 + (-6553544 / 84375) * alpha * t ^ 21 + (-2308961 / 253125) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_01, v9_02, v9_03, v9_10, v9_11, v9_12, v9_13, v9_20, v9_21, v9_22, v9_23, v9_30, v9_31, v9_32, v9_33, v9_40, v9_41, v9_42, v9_43]
  simp only [phase6_00, phase6_01, phase6_02, phase6_03, phase6_10, phase6_11, phase6_12, phase6_13, phase6_20, phase6_21, phase6_22, phase6_23, phase6_30, phase6_31, phase6_32, phase6_33, phase6_40, phase6_41, phase6_42, phase6_43]
  linear_combination ((45484 / 125) * t ^ 3 + (-298989 / 250) * t ^ 5 + (4319396 / 15625) * t ^ 7 + (1549192 / 1875) * t ^ 9 + (2375348 / 46875) * t ^ 11 + (-51251663 / 234375) * t ^ 13 + (-115529372 / 2109375) * t ^ 15 + (-9791672 / 234375) * t ^ 17 + (21993254 / 2109375) * t ^ 19 + (-36310378 / 2109375) * t ^ 21 + (-1112293 / 703125) * t ^ 25 + (-135356 / 375) * c * t ^ 3 + (852142 / 1125) * c * t ^ 5 + (-323332 / 675) * c * t ^ 7 + (60369008 / 421875) * c * t ^ 9 + (-17246272 / 140625) * c * t ^ 11 + (17750554 / 234375) * c * t ^ 13 + (-85340932 / 6328125) * c * t ^ 15 + (-2143756 / 2109375) * c * t ^ 17 + (-62355878 / 18984375) * c * t ^ 19 + (19662562 / 6328125) * c * t ^ 21 + (258128 / 18984375) * c * t ^ 25 + (-1096 / 375) * c ^ 2 * t ^ 3 + (3241 / 1125) * c ^ 2 * t ^ 5 + (700888 / 421875) * c ^ 2 * t ^ 7 + (-760816 / 421875) * c ^ 2 * t ^ 9 + (111088 / 421875) * c ^ 2 * t ^ 11 + (1756 / 46875) * c ^ 2 * t ^ 13 + (-273064 / 1265625) * c ^ 2 * t ^ 15 + (-8 / 1125) * c ^ 2 * t ^ 17 + (54932 / 1265625) * c ^ 2 * t ^ 19 + (-4 / 1125) * c ^ 2 * t ^ 21) * alpha_sq + ((2192 / 125) * t ^ 3 + (-6482 / 375) * t ^ 5 + (-1097216 / 140625) * t ^ 7 + (973696 / 140625) * t ^ 9 + (-22808 / 140625) * t ^ 11 + (-1348738 / 2109375) * t ^ 13 + (4027952 / 2109375) * t ^ 15 + (172928 / 2109375) * t ^ 17 + (-1770472 / 6328125) * t ^ 19 + (85328 / 2109375) * t ^ 21 + (20732 / 6328125) * t ^ 25 + (-2192 / 375) * alpha * t ^ 3 + (6482 / 1125) * alpha * t ^ 5 + (1097216 / 421875) * alpha * t ^ 7 + (-973696 / 421875) * alpha * t ^ 9 + (22808 / 421875) * alpha * t ^ 11 + (1348738 / 6328125) * alpha * t ^ 13 + (-4027952 / 6328125) * alpha * t ^ 15 + (-172928 / 6328125) * alpha * t ^ 17 + (1770472 / 18984375) * alpha * t ^ 19 + (-85328 / 6328125) * alpha * t ^ 21 + (-20732 / 18984375) * alpha * t ^ 25) * c_sq
theorem v10_44 (t : ℂ) : (momentPoly 10 z10 4 4).eval t = (175870 + (-1552304 / 3) * t ^ 2 + (72007936 / 75) * t ^ 4 + (-2999736512 / 1875) * t ^ 6 + (228954664984 / 140625) * t ^ 8 + (-116738864896 / 140625) * t ^ 10 + (981694912 / 3125) * t ^ 12 + (-29843879936 / 140625) * t ^ 14 + (13836406832 / 140625) * t ^ 16 + (-2696031344 / 140625) * t ^ 18 + (7516450624 / 1265625) * t ^ 20 + (-306095168 / 46875) * t ^ 22 + (1514034848 / 421875) * t ^ 24 + (-1094747008 / 1265625) * t ^ 26 + (88668106 / 1265625) * t ^ 32) := by
  rw [momentPoly]
  simp only [z10, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v9_00, v9_01, v9_02, v9_03, v9_04, v9_10, v9_11, v9_12, v9_13, v9_14, v9_20, v9_21, v9_22, v9_23, v9_24, v9_30, v9_31, v9_32, v9_33, v9_34, v9_40, v9_41, v9_42, v9_43, v9_44]
  simp only [phase6_00, phase6_01, phase6_02, phase6_03, phase6_04, phase6_10, phase6_11, phase6_12, phase6_13, phase6_14, phase6_20, phase6_21, phase6_22, phase6_23, phase6_24, phase6_30, phase6_31, phase6_32, phase6_33, phase6_34, phase6_40, phase6_41, phase6_42, phase6_43, phase6_44]
  linear_combination ((-29852 / 25) * t ^ 2 + (1059968 / 1125) * t ^ 4 + (122126008 / 5625) * t ^ 6 + (-10766399282 / 234375) * t ^ 8 + (68009015488 / 2109375) * t ^ 10 + (-5577406688 / 421875) * t ^ 12 + (61074483376 / 6328125) * t ^ 14 + (-11233923976 / 2109375) * t ^ 16 + (6670446656 / 6328125) * t ^ 18 + (-2728369304 / 94921875) * t ^ 20 + (10984770272 / 31640625) * t ^ 22 + (-2877373484 / 10546875) * t ^ 24 + (2880814112 / 94921875) * t ^ 26 + (-25331089 / 7031250) * t ^ 32 + (238816 / 225) * c * t ^ 2 + (-186368 / 375) * c * t ^ 4 + (-46179136 / 28125) * c * t ^ 6 + (459615392 / 2109375) * c * t ^ 8 + (143082496 / 140625) * c * t ^ 10 + (-2262272 / 421875) * c * t ^ 12 + (1366528 / 6328125) * c * t ^ 14 + (-251729792 / 2109375) * c * t ^ 16 + (-48748928 / 2109375) * c * t ^ 18 + (583058048 / 31640625) * c * t ^ 20 + (-23874176 / 1171875) * c * t ^ 22 + (4840192 / 31640625) * c * t ^ 24 + (-248820352 / 94921875) * c * t ^ 26 + (5878544 / 94921875) * c * t ^ 32 + (29852 / 225) * c ^ 2 * t ^ 2 + (-500864 / 1125) * c ^ 2 * t ^ 4 + (19104016 / 28125) * c ^ 2 * t ^ 6 + (-3930910312 / 6328125) * c ^ 2 * t ^ 8 + (2232759872 / 6328125) * c ^ 2 * t ^ 10 + (-11565776 / 84375) * c ^ 2 * t ^ 12 + (124247984 / 2109375) * c ^ 2 * t ^ 14 + (-5273696 / 253125) * c ^ 2 * t ^ 16 + (6544112 / 3796875) * c ^ 2 * t ^ 18 + (-188156896 / 94921875) * c ^ 2 * t ^ 20 + (120126544 / 94921875) * c ^ 2 * t ^ 22 + (521056 / 94921875) * c ^ 2 * t ^ 24 + (21614224 / 284765625) * c ^ 2 * t ^ 26 + (42632 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((-119408 / 225) * t ^ 2 + (2003456 / 1125) * t ^ 4 + (-76752704 / 28125) * t ^ 6 + (5270093216 / 2109375) * t ^ 8 + (-2971050752 / 2109375) * t ^ 10 + (241198208 / 421875) * t ^ 12 + (-602389504 / 2109375) * t ^ 14 + (232861312 / 2109375) * t ^ 16 + (-31107824 / 2109375) * t ^ 18 + (1047202432 / 94921875) * t ^ 20 + (-52607552 / 10546875) * t ^ 22 + (-2084224 / 31640625) * t ^ 24 + (-56653696 / 94921875) * t ^ 26 + (-170528 / 94921875) * t ^ 32) * c_sq
#print axioms v10_00
#print axioms v10_11
#print axioms v10_22
#print axioms v10_33
#print axioms v10_44
end PhotonCertA
