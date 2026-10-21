import PhotonCertA17
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z18 : Fin 18 → ℂ := Fin.snoc z17 phiMinus
theorem v18_00 (t : ℂ) : (momentPoly 18 z18 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00]
  simp only [phase15_00]
  ring
theorem v18_01 (t : ℂ) : (momentPoly 18 z18 0 1).eval t = ((-1) * t) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_01]
  simp only [phase15_00, phase15_01]
  ring
theorem v18_02 (t : ℂ) : (momentPoly 18 z18 0 2).eval t = ((-41 / 20) * t ^ 2 + (61 / 20) * t ^ 4 + (73 / 15) * alpha * t ^ 2 + (-73 / 15) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_01, v17_02]
  simp only [phase15_00, phase15_01, phase15_02]
  linear_combination ((-1 / 288) * t ^ 2) * alpha_sq + ((-1 / 288) * t ^ 2) * d_sq
theorem v18_03 (t : ℂ) : (momentPoly 18 z18 0 3).eval t = ((163 / 20) * t ^ 3 + (-183 / 20) * t ^ 5 + (-1737 / 200) * alpha * t ^ 3 + (2291 / 400) * alpha * t ^ 5 + (1183 / 400) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_01, v17_02, v17_03]
  simp only [phase15_00, phase15_01, phase15_02, phase15_03]
  linear_combination ((99 / 160) * t ^ 3 + (-73 / 120) * t ^ 5 + (-1 / 1152) * d * t ^ 3 + (1 / 1152) * d * t ^ 5) * alpha_sq + ((1 / 96) * t ^ 3 + (1 / 1152) * alpha * t ^ 3 + (-1 / 1152) * alpha * t ^ 5) * d_sq
theorem v18_04 (t : ℂ) : (momentPoly 18 z18 0 4).eval t = ((-886881 / 4000) * t ^ 4 + (854281 / 2000) * t ^ 6 + (-1558691 / 8000) * t ^ 8 + (-25557 / 2000) * t ^ 10 + (25557 / 8000) * t ^ 16 + (-41386 / 375) * alpha * t ^ 4 + (357143 / 1500) * alpha * t ^ 6 + (-76861 / 750) * alpha * t ^ 8 + (-133763 / 4500) * alpha * t ^ 10 + (5033 / 1125) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_01, v17_02, v17_03, v17_04]
  simp only [phase15_00, phase15_01, phase15_02, phase15_03, phase15_04]
  linear_combination ((-44033 / 28800) * t ^ 4 + (29237 / 28800) * t ^ 6 + (39013 / 86400) * t ^ 10 + (151 / 1440) * d * t ^ 4 + (-33 / 160) * d * t ^ 6 + (73 / 720) * d * t ^ 8 + (1 / 6912) * d ^ 2 * t ^ 6 + (-1 / 13824) * d ^ 2 * t ^ 8) * alpha_sq + ((11 / 5760) * t ^ 4 + (-89 / 3840) * t ^ 6 + (1 / 4608) * t ^ 8 + (-47 / 3456) * t ^ 10 + (-151 / 1440) * alpha * t ^ 4 + (151 / 1440) * alpha * t ^ 6) * d_sq
theorem v18_10 (t : ℂ) : (momentPoly 18 z18 1 0).eval t = ((-1) * t) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_10]
  simp only [phase15_00, phase15_10]
  ring
theorem v18_11 (t : ℂ) : (momentPoly 18 z18 1 1).eval t = (18 + (-17) * t ^ 2) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_01, v17_10, v17_11]
  simp only [phase15_00, phase15_01, phase15_10, phase15_11]
  linear_combination ((1 / 288) * t ^ 2) * alpha_sq + ((-1 / 288) * t ^ 2) * d_sq
theorem v18_12 (t : ℂ) : (momentPoly 18 z18 1 2).eval t = ((-35) * t + (721 / 20) * t ^ 3 + (-41 / 20) * t ^ 5 + (-73 / 15) * alpha * t ^ 3 + (73 / 15) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_01, v17_02, v17_10, v17_11, v17_12]
  simp only [phase15_00, phase15_01, phase15_02, phase15_10, phase15_11, phase15_12]
  linear_combination ((-33 / 160) * t ^ 3 + (73 / 360) * t ^ 5 + (1 / 3456) * d * t ^ 3 + (-1 / 3456) * d * t ^ 5) * alpha_sq + ((1 / 96) * t ^ 3 + (1 / 3456) * alpha * t ^ 3 + (-1 / 3456) * alpha * t ^ 5) * d_sq
theorem v18_13 (t : ℂ) : (momentPoly 18 z18 1 3).eval t = ((-2091 / 20) * t ^ 2 + (4977 / 20) * t ^ 4 + (-561 / 4) * t ^ 6 + (-61 / 20) * t ^ 10 + (1241 / 5) * alpha * t ^ 2 + (-286789 / 600) * alpha * t ^ 4 + (91149 / 400) * alpha * t ^ 6 + (2291 / 1200) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_01, v17_02, v17_03, v17_10, v17_11, v17_12, v17_13]
  simp only [phase15_00, phase15_01, phase15_02, phase15_03, phase15_10, phase15_11, phase15_12, phase15_13]
  linear_combination ((-17 / 96) * t ^ 2 + (-10477 / 115200) * t ^ 4 + (43873 / 115200) * t ^ 6 + (-39013 / 345600) * t ^ 10) * alpha_sq + ((-17 / 96) * t ^ 2 + (3617 / 23040) * t ^ 4 + (-257 / 23040) * t ^ 6 + (-47 / 13824) * t ^ 10 + (-151 / 2880) * alpha * t ^ 4 + (151 / 2880) * alpha * t ^ 6) * d_sq
theorem v18_14 (t : ℂ) : (momentPoly 18 z18 1 4).eval t = ((5379 / 10) * t ^ 3 + (-3533519 / 4000) * t ^ 5 + (219119 / 2000) * t ^ 7 + (1705091 / 8000) * t ^ 9 + (49957 / 2000) * t ^ 11 + (-25557 / 8000) * t ^ 17 + (-57321 / 100) * alpha * t ^ 3 + (3051343 / 3000) * alpha * t ^ 5 + (-414409 / 750) * alpha * t ^ 7 + (1770563 / 6000) * alpha * t ^ 9 + (-805597 / 4500) * alpha * t ^ 11 + (-133763 / 18000) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_01, v17_02, v17_03, v17_04, v17_10, v17_11, v17_12, v17_13, v17_14]
  simp only [phase15_00, phase15_01, phase15_02, phase15_03, phase15_04, phase15_10, phase15_11, phase15_12, phase15_13, phase15_14]
  linear_combination ((3267 / 80) * t ^ 3 + (-53927 / 750) * t ^ 5 + (3841543 / 144000) * t ^ 7 + (49057 / 16000) * t ^ 9 + (5254 / 3375) * t ^ 11 + (-5033 / 27000) * t ^ 17 + (-11 / 192) * d * t ^ 3 + (127 / 23040) * d * t ^ 5 + (7277 / 46080) * d * t ^ 7 + (-29501 / 276480) * d * t ^ 9 + (47 / 41472) * d * t ^ 11 + (-95 / 165888) * d * t ^ 17 + (-151 / 34560) * d ^ 2 * t ^ 7 + (11 / 2560) * d ^ 2 * t ^ 9) * alpha_sq + ((11 / 16) * t ^ 3 + (-1967 / 2880) * t ^ 5 + (25 / 256) * t ^ 7 + (-589 / 23040) * t ^ 9 + (47 / 1728) * t ^ 11 + (11 / 192) * alpha * t ^ 3 + (42073 / 345600) * alpha * t ^ 5 + (-32023 / 230400) * alpha * t ^ 7 + (-509 / 276480) * alpha * t ^ 9 + (-39013 / 1036800) * alpha * t ^ 11 + (-95 / 165888) * alpha * t ^ 17) * d_sq
theorem v18_20 (t : ℂ) : (momentPoly 18 z18 2 0).eval t = ((-41 / 20) * t ^ 2 + (61 / 20) * t ^ 4 + (-73 / 15) * alpha * t ^ 2 + (73 / 15) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_10, v17_20]
  simp only [phase15_00, phase15_10, phase15_20]
  linear_combination ((-1 / 288) * t ^ 2) * alpha_sq + ((-1 / 288) * t ^ 2) * d_sq
theorem v18_21 (t : ℂ) : (momentPoly 18 z18 2 1).eval t = ((-35) * t + (721 / 20) * t ^ 3 + (-41 / 20) * t ^ 5 + (73 / 15) * alpha * t ^ 3 + (-73 / 15) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_01, v17_10, v17_11, v17_20, v17_21]
  simp only [phase15_00, phase15_01, phase15_10, phase15_11, phase15_20, phase15_21]
  linear_combination ((-33 / 160) * t ^ 3 + (73 / 360) * t ^ 5 + (1 / 3456) * d * t ^ 3 + (-1 / 3456) * d * t ^ 5) * alpha_sq + ((1 / 96) * t ^ 3 + (-1 / 3456) * alpha * t ^ 3 + (1 / 3456) * alpha * t ^ 5) * d_sq
theorem v18_22 (t : ℂ) : (momentPoly 18 z18 2 2).eval t = (630 + (-1156) * t ^ 2 + (661507 / 1200) * t ^ 4 + (-51967 / 600) * t ^ 6 + (74827 / 1200) * t ^ 8) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_01, v17_02, v17_10, v17_11, v17_12, v17_20, v17_21, v17_22]
  simp only [phase15_00, phase15_01, phase15_02, phase15_10, phase15_11, phase15_12, phase15_20, phase15_21, phase15_22]
  linear_combination ((17 / 72) * t ^ 2 + (1817 / 2880) * t ^ 4 + (-2437 / 2880) * t ^ 6 + (-151 / 4320) * d * t ^ 4 + (11 / 160) * d * t ^ 6 + (-73 / 2160) * d * t ^ 8 + (-1 / 20736) * d ^ 2 * t ^ 6 + (1 / 41472) * d ^ 2 * t ^ 8) * alpha_sq + ((-17 / 72) * t ^ 2 + (601 / 2880) * t ^ 4 + (-247 / 34560) * t ^ 6 + (-1 / 13824) * t ^ 8) * d_sq
theorem v18_23 (t : ℂ) : (momentPoly 18 z18 2 3).eval t = ((-1786) * t + (71379 / 20) * t ^ 3 + (-3926117 / 2000) * t ^ 5 + (18271 / 80) * t ^ 7 + (-54379 / 1000) * t ^ 9 + (94559 / 2000) * t ^ 11 + (-84359 / 2000) * t ^ 13 + (-2409 / 5) * alpha * t ^ 3 + (3630697 / 4000) * alpha * t ^ 5 + (-1811699 / 4800) * alpha * t ^ 7 + (-333289 / 8000) * alpha * t ^ 9 + (-379109 / 24000) * alpha * t ^ 11 + (72163 / 8000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_01, v17_02, v17_03, v17_10, v17_11, v17_12, v17_13, v17_20, v17_21, v17_22, v17_23]
  simp only [phase15_00, phase15_01, phase15_02, phase15_03, phase15_10, phase15_11, phase15_12, phase15_13, phase15_20, phase15_21, phase15_22, phase15_23]
  linear_combination ((-3267 / 160) * t ^ 3 + (2131937 / 57600) * t ^ 5 + (-948253 / 57600) * t ^ 7 + (-135457 / 172800) * t ^ 11 + (10439 / 17280) * t ^ 13 + (11 / 384) * d * t ^ 3 + (5021 / 172800) * d * t ^ 5 + (-36583 / 276480) * d * t ^ 7 + (102347 / 1382400) * d * t ^ 9 + (-36613 / 4147200) * d * t ^ 11 + (39013 / 4147200) * d * t ^ 13 + (151 / 34560) * d ^ 2 * t ^ 7 + (-11 / 2560) * d ^ 2 * t ^ 9) * alpha_sq + ((33 / 32) * t ^ 3 + (-3539 / 3840) * t ^ 5 + (-11 / 288) * t ^ 7 + (589 / 23040) * t ^ 9 + (47 / 6912) * t ^ 11 + (11 / 384) * alpha * t ^ 3 + (5021 / 172800) * alpha * t ^ 5 + (-66397 / 1382400) * alpha * t ^ 7 + (1 / 55296) * alpha * t ^ 9 + (-41363 / 4147200) * alpha * t ^ 11 + (47 / 165888) * alpha * t ^ 13) * d_sq
theorem v18_24 (t : ℂ) : (momentPoly 18 z18 2 4).eval t = ((-13817 / 2) * t ^ 2 + (444723 / 20) * t ^ 4 + (-5684824421 / 240000) * t ^ 6 + (780288161 / 80000) * t ^ 8 + (-225391319 / 96000) * t ^ 10 + (767067589 / 1440000) * t ^ 12 + (149548391 / 360000) * t ^ 14 + (93410171 / 1440000) * t ^ 18 + (-84417911 / 1440000) * t ^ 20 + (49202 / 3) * alpha * t ^ 2 + (-3437779 / 75) * alpha * t ^ 4 + (2535306121 / 60000) * alpha * t ^ 6 + (-274251011 / 20000) * alpha * t ^ 8 + (45592319 / 24000) * alpha * t ^ 10 + (-299308769 / 360000) * alpha * t ^ 12 + (-8097913 / 45000) * alpha * t ^ 14 + (-10273231 / 360000) * alpha * t ^ 18 + (12261191 / 360000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_01, v17_02, v17_03, v17_04, v17_10, v17_11, v17_12, v17_13, v17_14, v17_20, v17_21, v17_22, v17_23, v17_24]
  simp only [phase15_00, phase15_01, phase15_02, phase15_03, phase15_04, phase15_10, phase15_11, phase15_12, phase15_13, phase15_14, phase15_20, phase15_21, phase15_22, phase15_23, phase15_24]
  linear_combination ((-1685 / 144) * t ^ 2 + (-10477 / 900) * t ^ 4 + (211831493 / 3456000) * t ^ 6 + (-2691691 / 115200) * t ^ 8 + (-181241041 / 6912000) * t ^ 10 + (21901477 / 1728000) * t ^ 12 + (-5372389 / 3456000) * t ^ 14 + (812149 / 1382400) * t ^ 18 + (155813 / 864000) * d * t ^ 6 + (-519449 / 864000) * d * t ^ 8 + (469889 / 691200) * d * t ^ 10 + (-127051 / 432000) * d * t ^ 12 + (176323 / 5184000) * d * t ^ 14 + (197569 / 10368000) * d * t ^ 18 + (-30949 / 1728000) * d * t ^ 20 + (-21989 / 4147200) * d ^ 2 * t ^ 8 + (367 / 102400) * d ^ 2 * t ^ 10 + (257 / 3317760) * d ^ 2 * t ^ 12 + (18919 / 12441600) * d ^ 2 * t ^ 14 + (-95 / 1990656) * d ^ 2 * t ^ 18 + (95 / 1990656) * d ^ 2 * t ^ 20) * alpha_sq + ((-1685 / 144) * t ^ 2 + (3617 / 180) * t ^ 4 + (-33582947 / 3456000) * t ^ 6 + (10222933 / 6912000) * t ^ 8 + (-12530629 / 13824000) * t ^ 10 + (4288477 / 9216000) * t ^ 12 + (-98233 / 4147200) * t ^ 14 + (-344177 / 82944000) * t ^ 18 + (-95 / 663552) * t ^ 20 + (-302 / 45) * alpha * t ^ 4 + (10916873 / 864000) * alpha * t ^ 6 + (-438473 / 72000) * alpha * t ^ 8 + (156667 / 1152000) * alpha * t ^ 10 + (32099 / 288000) * alpha * t ^ 12 + (-517 / 7680) * alpha * t ^ 14 + (-49727 / 3456000) * alpha * t ^ 18) * d_sq
theorem v18_30 (t : ℂ) : (momentPoly 18 z18 3 0).eval t = ((163 / 20) * t ^ 3 + (-183 / 20) * t ^ 5 + (1737 / 200) * alpha * t ^ 3 + (-2291 / 400) * alpha * t ^ 5 + (-1183 / 400) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_10, v17_20, v17_30]
  simp only [phase15_00, phase15_10, phase15_20, phase15_30]
  linear_combination ((99 / 160) * t ^ 3 + (-73 / 120) * t ^ 5 + (-1 / 1152) * d * t ^ 3 + (1 / 1152) * d * t ^ 5) * alpha_sq + ((1 / 96) * t ^ 3 + (-1 / 1152) * alpha * t ^ 3 + (1 / 1152) * alpha * t ^ 5) * d_sq
theorem v18_31 (t : ℂ) : (momentPoly 18 z18 3 1).eval t = ((-2091 / 20) * t ^ 2 + (4977 / 20) * t ^ 4 + (-561 / 4) * t ^ 6 + (-61 / 20) * t ^ 10 + (-1241 / 5) * alpha * t ^ 2 + (286789 / 600) * alpha * t ^ 4 + (-91149 / 400) * alpha * t ^ 6 + (-2291 / 1200) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_01, v17_10, v17_11, v17_20, v17_21, v17_30, v17_31]
  simp only [phase15_00, phase15_01, phase15_10, phase15_11, phase15_20, phase15_21, phase15_30, phase15_31]
  linear_combination ((-17 / 96) * t ^ 2 + (-10477 / 115200) * t ^ 4 + (43873 / 115200) * t ^ 6 + (-39013 / 345600) * t ^ 10) * alpha_sq + ((-17 / 96) * t ^ 2 + (3617 / 23040) * t ^ 4 + (-257 / 23040) * t ^ 6 + (-47 / 13824) * t ^ 10 + (151 / 2880) * alpha * t ^ 4 + (-151 / 2880) * alpha * t ^ 6) * d_sq
theorem v18_32 (t : ℂ) : (momentPoly 18 z18 3 2).eval t = ((-1786) * t + (71379 / 20) * t ^ 3 + (-3926117 / 2000) * t ^ 5 + (18271 / 80) * t ^ 7 + (-54379 / 1000) * t ^ 9 + (94559 / 2000) * t ^ 11 + (-84359 / 2000) * t ^ 13 + (2409 / 5) * alpha * t ^ 3 + (-3630697 / 4000) * alpha * t ^ 5 + (1811699 / 4800) * alpha * t ^ 7 + (333289 / 8000) * alpha * t ^ 9 + (379109 / 24000) * alpha * t ^ 11 + (-72163 / 8000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_01, v17_02, v17_10, v17_11, v17_12, v17_20, v17_21, v17_22, v17_30, v17_31, v17_32]
  simp only [phase15_00, phase15_01, phase15_02, phase15_10, phase15_11, phase15_12, phase15_20, phase15_21, phase15_22, phase15_30, phase15_31, phase15_32]
  linear_combination ((-3267 / 160) * t ^ 3 + (2131937 / 57600) * t ^ 5 + (-948253 / 57600) * t ^ 7 + (-135457 / 172800) * t ^ 11 + (10439 / 17280) * t ^ 13 + (11 / 384) * d * t ^ 3 + (5021 / 172800) * d * t ^ 5 + (-36583 / 276480) * d * t ^ 7 + (102347 / 1382400) * d * t ^ 9 + (-36613 / 4147200) * d * t ^ 11 + (39013 / 4147200) * d * t ^ 13 + (151 / 34560) * d ^ 2 * t ^ 7 + (-11 / 2560) * d ^ 2 * t ^ 9) * alpha_sq + ((33 / 32) * t ^ 3 + (-3539 / 3840) * t ^ 5 + (-11 / 288) * t ^ 7 + (589 / 23040) * t ^ 9 + (47 / 6912) * t ^ 11 + (-11 / 384) * alpha * t ^ 3 + (-5021 / 172800) * alpha * t ^ 5 + (66397 / 1382400) * alpha * t ^ 7 + (-1 / 55296) * alpha * t ^ 9 + (41363 / 4147200) * alpha * t ^ 11 + (-47 / 165888) * alpha * t ^ 13) * d_sq
theorem v18_33 (t : ℂ) : (momentPoly 18 z18 3 3).eval t = (32148 + (-85935) * t ^ 2 + (1984521 / 25) * t ^ 4 + (-1513337593 / 40000) * t ^ 6 + (818709599 / 40000) * t ^ 8 + (-1307295957 / 160000) * t ^ 10 + (4228787 / 40000) * t ^ 12 + (-13640041 / 80000) * t ^ 14 + (1318467 / 160000) * t ^ 18) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_01, v17_02, v17_03, v17_10, v17_11, v17_12, v17_13, v17_20, v17_21, v17_22, v17_23, v17_30, v17_31, v17_32, v17_33]
  simp only [phase15_00, phase15_01, phase15_02, phase15_03, phase15_10, phase15_11, phase15_12, phase15_13, phase15_20, phase15_21, phase15_22, phase15_23, phase15_30, phase15_31, phase15_32, phase15_33]
  linear_combination ((1685 / 96) * t ^ 2 + (1817 / 20) * t ^ 4 + (-26435361 / 128000) * t ^ 6 + (1116193 / 12800) * t ^ 8 + (7663951 / 768000) * t ^ 10 + (66708941 / 13824000) * t ^ 12 + (-40943771 / 13824000) * t ^ 14 + (-11668943 / 16588800) * t ^ 18 + (-151 / 30) * d * t ^ 4 + (824213 / 57600) * d * t ^ 6 + (-616513 / 46080) * d * t ^ 8 + (946193 / 230400) * d * t ^ 10 + (-103547 / 691200) * d * t ^ 12 + (101147 / 691200) * d * t ^ 14 + (-49 / 6912) * d ^ 2 * t ^ 6 + (-7571 / 691200) * d ^ 2 * t ^ 8 + (7031 / 460800) * d ^ 2 * t ^ 10 + (3349 / 1382400) * d ^ 2 * t ^ 14) * alpha_sq + ((-1685 / 96) * t ^ 2 + (601 / 20) * t ^ 4 + (-3373979 / 230400) * t ^ 6 + (850349 / 230400) * t ^ 8 + (-7133 / 3840) * t ^ 10 + (105863 / 2764800) * t ^ 12 + (-100583 / 2764800) * t ^ 14 + (-2209 / 663552) * t ^ 18) * d_sq
theorem v18_34 (t : ℂ) : (momentPoly 18 z18 3 4).eval t = ((-118083) * t + (3432681 / 10) * t ^ 3 + (-346931031 / 1000) * t ^ 5 + (57512572097 / 400000) * t ^ 7 + (-11890126427 / 400000) * t ^ 9 + (12363455739 / 800000) * t ^ 11 + (-2575150231 / 160000) * t ^ 13 + (5558708639 / 600000) * t ^ 15 + (-89696563 / 100000) * t ^ 17 + (-622523123 / 2400000) * t ^ 19 + (432788083 / 2400000) * t ^ 21 + (6104039 / 150000) * t ^ 25 + (-231702 / 5) * alpha * t ^ 3 + (251252021 / 2000) * alpha * t ^ 5 + (-82131331617 / 800000) * alpha * t ^ 7 + (79722684437 / 4800000) * alpha * t ^ 9 + (13602320773 / 4800000) * alpha * t ^ 11 + (6317354063 / 1152000) * alpha * t ^ 13 + (-629388871 / 300000) * alpha * t ^ 15 + (1750491453 / 3200000) * alpha * t ^ 17 + (1631608499 / 14400000) * alpha * t ^ 19 + (-968576701 / 9600000) * alpha * t ^ 21 + (-30233931 / 3200000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_01, v17_02, v17_03, v17_04, v17_10, v17_11, v17_12, v17_13, v17_14, v17_20, v17_21, v17_22, v17_23, v17_24, v17_30, v17_31, v17_32, v17_33, v17_34]
  simp only [phase15_00, phase15_01, phase15_02, phase15_03, phase15_04, phase15_10, phase15_11, phase15_12, phase15_13, phase15_14, phase15_20, phase15_21, phase15_22, phase15_23, phase15_24, phase15_30, phase15_31, phase15_32, phase15_33, phase15_34]
  linear_combination ((-157113 / 80) * t ^ 3 + (16269829 / 3200) * t ^ 5 + (-24759120787 / 5760000) * t ^ 7 + (815543639 / 640000) * t ^ 9 + (-96132341 / 288000) * t ^ 11 + (3806103991 / 11520000) * t ^ 13 + (-1192509299 / 11520000) * t ^ 15 + (7015151 / 768000) * t ^ 17 + (952018157 / 207360000) * t ^ 19 + (-215712659 / 69120000) * t ^ 21 + (-719719 / 1296000) * t ^ 25 + (529 / 192) * d * t ^ 3 + (12757 / 1600) * d * t ^ 5 + (-99962563 / 2764800) * d * t ^ 7 + (502929367 / 13824000) * d * t ^ 9 + (-169618391 / 13824000) * d * t ^ 11 + (9173009 / 2592000) * d * t ^ 13 + (-41034331 / 18432000) * d * t ^ 15 + (39159857 / 331776000) * d * t ^ 17 + (-100876123 / 995328000) * d * t ^ 19 + (-10598119 / 331776000) * d * t ^ 21 + (741247 / 39813120) * d * t ^ 25 + (2869 / 3456) * d ^ 2 * t ^ 7 + (-398499 / 256000) * d ^ 2 * t ^ 9 + (10356277 / 13824000) * d ^ 2 * t ^ 11 + (-508801 / 27648000) * d ^ 2 * t ^ 13 + (-95983 / 10368000) * d ^ 2 * t ^ 15 + (3431 / 829440) * d ^ 2 * t ^ 17 + (2869 / 663552) * d ^ 2 * t ^ 19 + (-197569 / 82944000) * d ^ 2 * t ^ 21) * alpha_sq + ((1587 / 16) * t ^ 3 + (-109709 / 640) * t ^ 5 + (73605721 / 1152000) * t ^ 7 + (5806039 / 460800) * t ^ 9 + (-9645649 / 4608000) * t ^ 11 + (-105971281 / 27648000) * t ^ 13 + (666913 / 256000) * t ^ 15 + (-3431 / 138240) * t ^ 17 + (1022867 / 82944000) * t ^ 19 + (383263 / 27648000) * t ^ 21 + (529 / 192) * alpha * t ^ 3 + (12757 / 1600) * alpha * t ^ 5 + (-55685723 / 2764800) * alpha * t ^ 7 + (118057739 / 13824000) * alpha * t ^ 9 + (-6266983 / 13824000) * alpha * t ^ 11 + (1072837 / 921600) * alpha * t ^ 13 + (1001539 / 11059200) * alpha * t ^ 15 + (-159803 / 66355200) * alpha * t ^ 17 + (74630957 / 995328000) * alpha * t ^ 19 + (-254323 / 331776000) * alpha * t ^ 21 + (-4465 / 7962624) * alpha * t ^ 25) * d_sq
theorem v18_40 (t : ℂ) : (momentPoly 18 z18 4 0).eval t = ((-886881 / 4000) * t ^ 4 + (854281 / 2000) * t ^ 6 + (-1558691 / 8000) * t ^ 8 + (-25557 / 2000) * t ^ 10 + (25557 / 8000) * t ^ 16 + (41386 / 375) * alpha * t ^ 4 + (-357143 / 1500) * alpha * t ^ 6 + (76861 / 750) * alpha * t ^ 8 + (133763 / 4500) * alpha * t ^ 10 + (-5033 / 1125) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_10, v17_20, v17_30, v17_40]
  simp only [phase15_00, phase15_10, phase15_20, phase15_30, phase15_40]
  linear_combination ((-44033 / 28800) * t ^ 4 + (29237 / 28800) * t ^ 6 + (39013 / 86400) * t ^ 10 + (151 / 1440) * d * t ^ 4 + (-33 / 160) * d * t ^ 6 + (73 / 720) * d * t ^ 8 + (1 / 6912) * d ^ 2 * t ^ 6 + (-1 / 13824) * d ^ 2 * t ^ 8) * alpha_sq + ((11 / 5760) * t ^ 4 + (-89 / 3840) * t ^ 6 + (1 / 4608) * t ^ 8 + (-47 / 3456) * t ^ 10 + (151 / 1440) * alpha * t ^ 4 + (-151 / 1440) * alpha * t ^ 6) * d_sq
theorem v18_41 (t : ℂ) : (momentPoly 18 z18 4 1).eval t = ((5379 / 10) * t ^ 3 + (-3533519 / 4000) * t ^ 5 + (219119 / 2000) * t ^ 7 + (1705091 / 8000) * t ^ 9 + (49957 / 2000) * t ^ 11 + (-25557 / 8000) * t ^ 17 + (57321 / 100) * alpha * t ^ 3 + (-3051343 / 3000) * alpha * t ^ 5 + (414409 / 750) * alpha * t ^ 7 + (-1770563 / 6000) * alpha * t ^ 9 + (805597 / 4500) * alpha * t ^ 11 + (133763 / 18000) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_01, v17_10, v17_11, v17_20, v17_21, v17_30, v17_31, v17_40, v17_41]
  simp only [phase15_00, phase15_01, phase15_10, phase15_11, phase15_20, phase15_21, phase15_30, phase15_31, phase15_40, phase15_41]
  linear_combination ((3267 / 80) * t ^ 3 + (-53927 / 750) * t ^ 5 + (3841543 / 144000) * t ^ 7 + (49057 / 16000) * t ^ 9 + (5254 / 3375) * t ^ 11 + (-5033 / 27000) * t ^ 17 + (-11 / 192) * d * t ^ 3 + (127 / 23040) * d * t ^ 5 + (7277 / 46080) * d * t ^ 7 + (-29501 / 276480) * d * t ^ 9 + (47 / 41472) * d * t ^ 11 + (-95 / 165888) * d * t ^ 17 + (-151 / 34560) * d ^ 2 * t ^ 7 + (11 / 2560) * d ^ 2 * t ^ 9) * alpha_sq + ((11 / 16) * t ^ 3 + (-1967 / 2880) * t ^ 5 + (25 / 256) * t ^ 7 + (-589 / 23040) * t ^ 9 + (47 / 1728) * t ^ 11 + (-11 / 192) * alpha * t ^ 3 + (-42073 / 345600) * alpha * t ^ 5 + (32023 / 230400) * alpha * t ^ 7 + (509 / 276480) * alpha * t ^ 9 + (39013 / 1036800) * alpha * t ^ 11 + (95 / 165888) * alpha * t ^ 17) * d_sq
theorem v18_42 (t : ℂ) : (momentPoly 18 z18 4 2).eval t = ((-13817 / 2) * t ^ 2 + (444723 / 20) * t ^ 4 + (-5684824421 / 240000) * t ^ 6 + (780288161 / 80000) * t ^ 8 + (-225391319 / 96000) * t ^ 10 + (767067589 / 1440000) * t ^ 12 + (149548391 / 360000) * t ^ 14 + (93410171 / 1440000) * t ^ 18 + (-84417911 / 1440000) * t ^ 20 + (-49202 / 3) * alpha * t ^ 2 + (3437779 / 75) * alpha * t ^ 4 + (-2535306121 / 60000) * alpha * t ^ 6 + (274251011 / 20000) * alpha * t ^ 8 + (-45592319 / 24000) * alpha * t ^ 10 + (299308769 / 360000) * alpha * t ^ 12 + (8097913 / 45000) * alpha * t ^ 14 + (10273231 / 360000) * alpha * t ^ 18 + (-12261191 / 360000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_01, v17_02, v17_10, v17_11, v17_12, v17_20, v17_21, v17_22, v17_30, v17_31, v17_32, v17_40, v17_41, v17_42]
  simp only [phase15_00, phase15_01, phase15_02, phase15_10, phase15_11, phase15_12, phase15_20, phase15_21, phase15_22, phase15_30, phase15_31, phase15_32, phase15_40, phase15_41, phase15_42]
  linear_combination ((-1685 / 144) * t ^ 2 + (-10477 / 900) * t ^ 4 + (211831493 / 3456000) * t ^ 6 + (-2691691 / 115200) * t ^ 8 + (-181241041 / 6912000) * t ^ 10 + (21901477 / 1728000) * t ^ 12 + (-5372389 / 3456000) * t ^ 14 + (812149 / 1382400) * t ^ 18 + (155813 / 864000) * d * t ^ 6 + (-519449 / 864000) * d * t ^ 8 + (469889 / 691200) * d * t ^ 10 + (-127051 / 432000) * d * t ^ 12 + (176323 / 5184000) * d * t ^ 14 + (197569 / 10368000) * d * t ^ 18 + (-30949 / 1728000) * d * t ^ 20 + (-21989 / 4147200) * d ^ 2 * t ^ 8 + (367 / 102400) * d ^ 2 * t ^ 10 + (257 / 3317760) * d ^ 2 * t ^ 12 + (18919 / 12441600) * d ^ 2 * t ^ 14 + (-95 / 1990656) * d ^ 2 * t ^ 18 + (95 / 1990656) * d ^ 2 * t ^ 20) * alpha_sq + ((-1685 / 144) * t ^ 2 + (3617 / 180) * t ^ 4 + (-33582947 / 3456000) * t ^ 6 + (10222933 / 6912000) * t ^ 8 + (-12530629 / 13824000) * t ^ 10 + (4288477 / 9216000) * t ^ 12 + (-98233 / 4147200) * t ^ 14 + (-344177 / 82944000) * t ^ 18 + (-95 / 663552) * t ^ 20 + (302 / 45) * alpha * t ^ 4 + (-10916873 / 864000) * alpha * t ^ 6 + (438473 / 72000) * alpha * t ^ 8 + (-156667 / 1152000) * alpha * t ^ 10 + (-32099 / 288000) * alpha * t ^ 12 + (517 / 7680) * alpha * t ^ 14 + (49727 / 3456000) * alpha * t ^ 18) * d_sq
theorem v18_43 (t : ℂ) : (momentPoly 18 z18 4 3).eval t = ((-118083) * t + (3432681 / 10) * t ^ 3 + (-346931031 / 1000) * t ^ 5 + (57512572097 / 400000) * t ^ 7 + (-11890126427 / 400000) * t ^ 9 + (12363455739 / 800000) * t ^ 11 + (-2575150231 / 160000) * t ^ 13 + (5558708639 / 600000) * t ^ 15 + (-89696563 / 100000) * t ^ 17 + (-622523123 / 2400000) * t ^ 19 + (432788083 / 2400000) * t ^ 21 + (6104039 / 150000) * t ^ 25 + (231702 / 5) * alpha * t ^ 3 + (-251252021 / 2000) * alpha * t ^ 5 + (82131331617 / 800000) * alpha * t ^ 7 + (-79722684437 / 4800000) * alpha * t ^ 9 + (-13602320773 / 4800000) * alpha * t ^ 11 + (-6317354063 / 1152000) * alpha * t ^ 13 + (629388871 / 300000) * alpha * t ^ 15 + (-1750491453 / 3200000) * alpha * t ^ 17 + (-1631608499 / 14400000) * alpha * t ^ 19 + (968576701 / 9600000) * alpha * t ^ 21 + (30233931 / 3200000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_01, v17_02, v17_03, v17_10, v17_11, v17_12, v17_13, v17_20, v17_21, v17_22, v17_23, v17_30, v17_31, v17_32, v17_33, v17_40, v17_41, v17_42, v17_43]
  simp only [phase15_00, phase15_01, phase15_02, phase15_03, phase15_10, phase15_11, phase15_12, phase15_13, phase15_20, phase15_21, phase15_22, phase15_23, phase15_30, phase15_31, phase15_32, phase15_33, phase15_40, phase15_41, phase15_42, phase15_43]
  linear_combination ((-157113 / 80) * t ^ 3 + (16269829 / 3200) * t ^ 5 + (-24759120787 / 5760000) * t ^ 7 + (815543639 / 640000) * t ^ 9 + (-96132341 / 288000) * t ^ 11 + (3806103991 / 11520000) * t ^ 13 + (-1192509299 / 11520000) * t ^ 15 + (7015151 / 768000) * t ^ 17 + (952018157 / 207360000) * t ^ 19 + (-215712659 / 69120000) * t ^ 21 + (-719719 / 1296000) * t ^ 25 + (529 / 192) * d * t ^ 3 + (12757 / 1600) * d * t ^ 5 + (-99962563 / 2764800) * d * t ^ 7 + (502929367 / 13824000) * d * t ^ 9 + (-169618391 / 13824000) * d * t ^ 11 + (9173009 / 2592000) * d * t ^ 13 + (-41034331 / 18432000) * d * t ^ 15 + (39159857 / 331776000) * d * t ^ 17 + (-100876123 / 995328000) * d * t ^ 19 + (-10598119 / 331776000) * d * t ^ 21 + (741247 / 39813120) * d * t ^ 25 + (2869 / 3456) * d ^ 2 * t ^ 7 + (-398499 / 256000) * d ^ 2 * t ^ 9 + (10356277 / 13824000) * d ^ 2 * t ^ 11 + (-508801 / 27648000) * d ^ 2 * t ^ 13 + (-95983 / 10368000) * d ^ 2 * t ^ 15 + (3431 / 829440) * d ^ 2 * t ^ 17 + (2869 / 663552) * d ^ 2 * t ^ 19 + (-197569 / 82944000) * d ^ 2 * t ^ 21) * alpha_sq + ((1587 / 16) * t ^ 3 + (-109709 / 640) * t ^ 5 + (73605721 / 1152000) * t ^ 7 + (5806039 / 460800) * t ^ 9 + (-9645649 / 4608000) * t ^ 11 + (-105971281 / 27648000) * t ^ 13 + (666913 / 256000) * t ^ 15 + (-3431 / 138240) * t ^ 17 + (1022867 / 82944000) * t ^ 19 + (383263 / 27648000) * t ^ 21 + (-529 / 192) * alpha * t ^ 3 + (-12757 / 1600) * alpha * t ^ 5 + (55685723 / 2764800) * alpha * t ^ 7 + (-118057739 / 13824000) * alpha * t ^ 9 + (6266983 / 13824000) * alpha * t ^ 11 + (-1072837 / 921600) * alpha * t ^ 13 + (-1001539 / 11059200) * alpha * t ^ 15 + (159803 / 66355200) * alpha * t ^ 17 + (-74630957 / 995328000) * alpha * t ^ 19 + (254323 / 331776000) * alpha * t ^ 21 + (4465 / 7962624) * alpha * t ^ 25) * d_sq
theorem v18_44 (t : ℂ) : (momentPoly 18 z18 4 4).eval t = (2125494 + (-7355832) * t ^ 2 + (246742111 / 25) * t ^ 4 + (-1910004997 / 250) * t ^ 6 + (256328181157187 / 48000000) * t ^ 8 + (-38881671058027 / 12000000) * t ^ 10 + (9550237513297 / 9600000) * t ^ 12 + (-9517261457257 / 72000000) * t ^ 14 + (4739942868337 / 576000000) * t ^ 16 + (2137766544487 / 72000000) * t ^ 18 + (-2043273942923 / 432000000) * t ^ 20 + (743176307317 / 72000000) * t ^ 22 + (-1366272166807 / 288000000) * t ^ 24 + (-174845440147 / 216000000) * t ^ 26 + (90287467267 / 1728000000) * t ^ 32) := by
  rw [momentPoly]
  simp only [z18, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v17_00, v17_01, v17_02, v17_03, v17_04, v17_10, v17_11, v17_12, v17_13, v17_14, v17_20, v17_21, v17_22, v17_23, v17_24, v17_30, v17_31, v17_32, v17_33, v17_34, v17_40, v17_41, v17_42, v17_43, v17_44]
  simp only [phase15_00, phase15_01, phase15_02, phase15_03, phase15_04, phase15_10, phase15_11, phase15_12, phase15_13, phase15_14, phase15_20, phase15_21, phase15_22, phase15_23, phase15_24, phase15_30, phase15_31, phase15_32, phase15_33, phase15_34, phase15_40, phase15_41, phase15_42, phase15_43, phase15_44]
  linear_combination ((18029 / 12) * t ^ 2 + (677741 / 60) * t ^ 4 + (-170388979 / 4800) * t ^ 6 + (1650588265253 / 57600000) * t ^ 8 + (-76637226161 / 19200000) * t ^ 10 + (-56250723989 / 115200000) * t ^ 12 + (-223479833459 / 103680000) * t ^ 14 + (163061480117 / 172800000) * t ^ 16 + (-73326326729 / 172800000) * t ^ 18 + (21746313719 / 172800000) * t ^ 20 + (18783904319 / 691200000) * t ^ 22 + (18756502021 / 2073600000) * t ^ 26 + (-56323 / 90) * d * t ^ 4 + (137471 / 60) * d * t ^ 6 + (-26721574331 / 8640000) * d * t ^ 8 + (7992293737 / 4320000) * d * t ^ 10 + (-8973110101 / 17280000) * d * t ^ 12 + (16436454943 / 103680000) * d * t ^ 14 + (-212590937 / 3456000) * d * t ^ 16 + (-351490061 / 207360000) * d * t ^ 18 + (678589477 / 622080000) * d * t ^ 20 + (51801619 / 69120000) * d * t ^ 22 + (11707 / 405000) * d * t ^ 24 + (-5315497 / 8294400) * d * t ^ 26 + (95627 / 1555200) * d * t ^ 32 + (-3109 / 3456) * d ^ 2 * t ^ 6 + (-805157 / 259200) * d ^ 2 * t ^ 8 + (4145249 / 552960) * d ^ 2 * t ^ 10 + (-90037037 / 27648000) * d ^ 2 * t ^ 12 + (5567423 / 20736000) * d ^ 2 * t ^ 14 + (-77774113 / 165888000) * d ^ 2 * t ^ 16 + (-182377 / 13824000) * d ^ 2 * t ^ 18 + (-417791 / 19906560) * d ^ 2 * t ^ 20 + (-3454123 / 331776000) * d ^ 2 * t ^ 22 + (852823 / 1990656000) * d ^ 2 * t ^ 24 + (359461 / 59719680) * d ^ 2 * t ^ 26 + (9025 / 95551488) * d ^ 2 * t ^ 32) * alpha_sq + ((-18029 / 12) * t ^ 2 + (224173 / 60) * t ^ 4 + (-19559437 / 5760) * t ^ 6 + (13256900887 / 6912000) * t ^ 8 + (-218421263 / 184320) * t ^ 10 + (6840506069 / 15360000) * t ^ 12 + (-222849557 / 20736000) * t ^ 14 + (-258540589 / 18432000) * t ^ 16 + (13850983 / 2764800) * t ^ 18 + (-350141033 / 165888000) * t ^ 20 + (1532514331 / 552960000) * t ^ 22 + (-852823 / 663552000) * t ^ 24 + (-35265619 / 497664000) * t ^ 26 + (-9025 / 31850496) * t ^ 32) * d_sq
#print axioms v18_00
#print axioms v18_11
#print axioms v18_22
#print axioms v18_33
#print axioms v18_44
end PhotonCertA
