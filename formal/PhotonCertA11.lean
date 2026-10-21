import PhotonCertA10
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
theorem phase11_00 : (phiPlus : ℂ) ^ 0 * star (phiPlus : ℂ) ^ 0 = (1) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase11_01 : (phiPlus : ℂ) ^ 0 * star (phiPlus : ℂ) ^ 1 = ((1 / 24) * d + (1 / 24) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase11_02 : (phiPlus : ℂ) ^ 0 * star (phiPlus : ℂ) ^ 2 = ((95 / 96) + (1 / 288) * alpha * d) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 576)) * alpha_sq + ((1 / 576)) * d_sq
theorem phase11_03 : (phiPlus : ℂ) ^ 0 * star (phiPlus : ℂ) ^ 3 = ((47 / 1152) * d + (143 / 1152) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 4608) * d + (1 / 13824) * alpha) * alpha_sq + ((1 / 13824) * d + (1 / 4608) * alpha) * d_sq
theorem phase11_04 : (phiPlus : ℂ) ^ 0 * star (phiPlus : ℂ) ^ 4 = ((4417 / 4608) + (95 / 13824) * alpha * d) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 110592) + (1 / 55296) * d ^ 2 + (1 / 82944) * alpha * d + (1 / 331776) * alpha ^ 2) * alpha_sq + ((185 / 110592) + (1 / 331776) * d ^ 2 + (1 / 82944) * alpha * d) * d_sq
theorem phase11_10 : (phiPlus : ℂ) ^ 1 * star (phiPlus : ℂ) ^ 0 = ((1 / 24) * d + (-1 / 24) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase11_11 : (phiPlus : ℂ) ^ 1 * star (phiPlus : ℂ) ^ 1 = (1) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 576)) * alpha_sq + ((1 / 576)) * d_sq
theorem phase11_12 : (phiPlus : ℂ) ^ 1 * star (phiPlus : ℂ) ^ 2 = ((1 / 24) * d + (1 / 24) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 13824) * d + (-1 / 13824) * alpha) * alpha_sq + ((1 / 13824) * d + (1 / 13824) * alpha) * d_sq
theorem phase11_13 : (phiPlus : ℂ) ^ 1 * star (phiPlus : ℂ) ^ 3 = ((95 / 96) + (1 / 288) * alpha * d) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 110592) + (-1 / 165888) * alpha * d + (-1 / 331776) * alpha ^ 2) * alpha_sq + ((191 / 110592) + (1 / 331776) * d ^ 2 + (1 / 165888) * alpha * d) * d_sq
theorem phase11_14 : (phiPlus : ℂ) ^ 1 * star (phiPlus : ℂ) ^ 4 = ((47 / 1152) * d + (143 / 1152) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 884736) * d + (1 / 3981312) * d ^ 3 + (1 / 2654208) * alpha + (-1 / 3981312) * alpha * d ^ 2 + (-1 / 2654208) * alpha ^ 2 * d + (-1 / 7962624) * alpha ^ 3) * alpha_sq + ((7 / 98304) * d + (1 / 7962624) * d ^ 3 + (575 / 2654208) * alpha + (1 / 2654208) * alpha * d ^ 2) * d_sq
theorem phase11_20 : (phiPlus : ℂ) ^ 2 * star (phiPlus : ℂ) ^ 0 = ((95 / 96) + (-1 / 288) * alpha * d) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 576)) * alpha_sq + ((1 / 576)) * d_sq
theorem phase11_21 : (phiPlus : ℂ) ^ 2 * star (phiPlus : ℂ) ^ 1 = ((1 / 24) * d + (-1 / 24) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 13824) * d + (1 / 13824) * alpha) * alpha_sq + ((1 / 13824) * d + (-1 / 13824) * alpha) * d_sq
theorem phase11_22 : (phiPlus : ℂ) ^ 2 * star (phiPlus : ℂ) ^ 2 = (1) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 110592) + (-1 / 165888) * d ^ 2 + (1 / 331776) * alpha ^ 2) * alpha_sq + ((193 / 110592) + (1 / 331776) * d ^ 2) * d_sq
theorem phase11_23 : (phiPlus : ℂ) ^ 2 * star (phiPlus : ℂ) ^ 3 = ((1 / 24) * d + (1 / 24) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 2654208) * d + (-1 / 3981312) * d ^ 3 + (-1 / 2654208) * alpha + (-1 / 3981312) * alpha * d ^ 2 + (1 / 7962624) * alpha ^ 2 * d + (1 / 7962624) * alpha ^ 3) * alpha_sq + ((193 / 2654208) * d + (1 / 7962624) * d ^ 3 + (193 / 2654208) * alpha + (1 / 7962624) * alpha * d ^ 2) * d_sq
theorem phase11_24 : (phiPlus : ℂ) ^ 2 * star (phiPlus : ℂ) ^ 4 = ((95 / 96) + (1 / 288) * alpha * d) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 21233664) + (1 / 63700992) * d ^ 2 + (-1 / 191102976) * d ^ 4 + (-1 / 31850496) * alpha * d + (-1 / 47775744) * alpha * d ^ 3 + (-1 / 63700992) * alpha ^ 2 + (-1 / 191102976) * alpha ^ 2 * d ^ 2 + (1 / 95551488) * alpha ^ 3 * d + (1 / 191102976) * alpha ^ 4) * alpha_sq + ((36671 / 21233664) + (1 / 331776) * d ^ 2 + (1 / 191102976) * d ^ 4 + (193 / 31850496) * alpha * d + (1 / 95551488) * alpha * d ^ 3) * d_sq
theorem phase11_30 : (phiPlus : ℂ) ^ 3 * star (phiPlus : ℂ) ^ 0 = ((47 / 1152) * d + (-143 / 1152) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 4608) * d + (-1 / 13824) * alpha) * alpha_sq + ((1 / 13824) * d + (-1 / 4608) * alpha) * d_sq
theorem phase11_31 : (phiPlus : ℂ) ^ 3 * star (phiPlus : ℂ) ^ 1 = ((95 / 96) + (-1 / 288) * alpha * d) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 110592) + (1 / 165888) * alpha * d + (-1 / 331776) * alpha ^ 2) * alpha_sq + ((191 / 110592) + (1 / 331776) * d ^ 2 + (-1 / 165888) * alpha * d) * d_sq
theorem phase11_32 : (phiPlus : ℂ) ^ 3 * star (phiPlus : ℂ) ^ 2 = ((1 / 24) * d + (-1 / 24) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 2654208) * d + (-1 / 3981312) * d ^ 3 + (1 / 2654208) * alpha + (1 / 3981312) * alpha * d ^ 2 + (1 / 7962624) * alpha ^ 2 * d + (-1 / 7962624) * alpha ^ 3) * alpha_sq + ((193 / 2654208) * d + (1 / 7962624) * d ^ 3 + (-193 / 2654208) * alpha + (-1 / 7962624) * alpha * d ^ 2) * d_sq
theorem phase11_33 : (phiPlus : ℂ) ^ 3 * star (phiPlus : ℂ) ^ 3 = (1) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 21233664) + (-1 / 21233664) * d ^ 2 + (-1 / 63700992) * d ^ 4 + (1 / 63700992) * alpha ^ 2 + (1 / 63700992) * alpha ^ 2 * d ^ 2 + (-1 / 191102976) * alpha ^ 4) * alpha_sq + ((37057 / 21233664) + (97 / 31850496) * d ^ 2 + (1 / 191102976) * d ^ 4) * d_sq
theorem phase11_34 : (phiPlus : ℂ) ^ 3 * star (phiPlus : ℂ) ^ 4 = ((1 / 24) * d + (1 / 24) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 509607936) * d + (-1 / 509607936) * d ^ 3 + (-1 / 1528823808) * d ^ 5 + (-1 / 509607936) * alpha + (-1 / 509607936) * alpha * d ^ 2 + (-1 / 1528823808) * alpha * d ^ 4 + (1 / 1528823808) * alpha ^ 2 * d + (1 / 1528823808) * alpha ^ 2 * d ^ 3 + (1 / 1528823808) * alpha ^ 3 + (1 / 1528823808) * alpha ^ 3 * d ^ 2 + (-1 / 4586471424) * alpha ^ 4 * d + (-1 / 4586471424) * alpha ^ 5) * alpha_sq + ((37057 / 509607936) * d + (97 / 764411904) * d ^ 3 + (1 / 4586471424) * d ^ 5 + (37057 / 509607936) * alpha + (97 / 764411904) * alpha * d ^ 2 + (1 / 4586471424) * alpha * d ^ 4) * d_sq
theorem phase11_40 : (phiPlus : ℂ) ^ 4 * star (phiPlus : ℂ) ^ 0 = ((4417 / 4608) + (-95 / 13824) * alpha * d) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 110592) + (1 / 55296) * d ^ 2 + (-1 / 82944) * alpha * d + (1 / 331776) * alpha ^ 2) * alpha_sq + ((185 / 110592) + (1 / 331776) * d ^ 2 + (-1 / 82944) * alpha * d) * d_sq
theorem phase11_41 : (phiPlus : ℂ) ^ 4 * star (phiPlus : ℂ) ^ 1 = ((47 / 1152) * d + (-143 / 1152) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 884736) * d + (1 / 3981312) * d ^ 3 + (-1 / 2654208) * alpha + (1 / 3981312) * alpha * d ^ 2 + (-1 / 2654208) * alpha ^ 2 * d + (1 / 7962624) * alpha ^ 3) * alpha_sq + ((7 / 98304) * d + (1 / 7962624) * d ^ 3 + (-575 / 2654208) * alpha + (-1 / 2654208) * alpha * d ^ 2) * d_sq
theorem phase11_42 : (phiPlus : ℂ) ^ 4 * star (phiPlus : ℂ) ^ 2 = ((95 / 96) + (-1 / 288) * alpha * d) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 21233664) + (1 / 63700992) * d ^ 2 + (-1 / 191102976) * d ^ 4 + (1 / 31850496) * alpha * d + (1 / 47775744) * alpha * d ^ 3 + (-1 / 63700992) * alpha ^ 2 + (-1 / 191102976) * alpha ^ 2 * d ^ 2 + (-1 / 95551488) * alpha ^ 3 * d + (1 / 191102976) * alpha ^ 4) * alpha_sq + ((36671 / 21233664) + (1 / 331776) * d ^ 2 + (1 / 191102976) * d ^ 4 + (-193 / 31850496) * alpha * d + (-1 / 95551488) * alpha * d ^ 3) * d_sq
theorem phase11_43 : (phiPlus : ℂ) ^ 4 * star (phiPlus : ℂ) ^ 3 = ((1 / 24) * d + (-1 / 24) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 509607936) * d + (-1 / 509607936) * d ^ 3 + (-1 / 1528823808) * d ^ 5 + (1 / 509607936) * alpha + (1 / 509607936) * alpha * d ^ 2 + (1 / 1528823808) * alpha * d ^ 4 + (1 / 1528823808) * alpha ^ 2 * d + (1 / 1528823808) * alpha ^ 2 * d ^ 3 + (-1 / 1528823808) * alpha ^ 3 + (-1 / 1528823808) * alpha ^ 3 * d ^ 2 + (-1 / 4586471424) * alpha ^ 4 * d + (1 / 4586471424) * alpha ^ 5) * alpha_sq + ((37057 / 509607936) * d + (97 / 764411904) * d ^ 3 + (1 / 4586471424) * d ^ 5 + (-37057 / 509607936) * alpha + (-97 / 764411904) * alpha * d ^ 2 + (-1 / 4586471424) * alpha * d ^ 4) * d_sq
theorem phase11_44 : (phiPlus : ℂ) ^ 4 * star (phiPlus : ℂ) ^ 4 = (1) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 4076863488) + (-1 / 3057647616) * d ^ 2 + (-1 / 6115295232) * d ^ 4 + (-1 / 27518828544) * d ^ 6 + (1 / 12230590464) * alpha ^ 2 + (1 / 9172942848) * alpha ^ 2 * d ^ 2 + (1 / 18345885696) * alpha ^ 2 * d ^ 4 + (-1 / 36691771392) * alpha ^ 4 + (-1 / 27518828544) * alpha ^ 4 * d ^ 2 + (1 / 110075314176) * alpha ^ 6) * alpha_sq + ((7114945 / 4076863488) + (4139 / 1358954496) * d ^ 2 + (65 / 12230590464) * d ^ 4 + (1 / 110075314176) * d ^ 6) * d_sq
noncomputable def z11 : Fin 11 → ℂ := Fin.snoc z10 phiPlus
theorem v11_00 (t : ℂ) : (momentPoly 11 z11 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00]
  simp only [phase11_00]
  ring
theorem v11_01 (t : ℂ) : (momentPoly 11 z11 0 1).eval t = ((-1) * t + (1 / 24) * d * t + (-7 / 24) * alpha * t) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_01]
  simp only [phase11_00, phase11_01]
  ring
theorem v11_02 (t : ℂ) : (momentPoly 11 z11 0 2).eval t = ((337 / 60) * t ^ 2 + (-1861 / 480) * t ^ 4 + (-1 / 12) * d * t ^ 2 + (109 / 20) * alpha * t ^ 2 + (-73 / 15) * alpha * t ^ 4 + (-1 / 36) * alpha * d * t ^ 2 + (1 / 288) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_01, v10_02]
  simp only [phase11_00, phase11_01, phase11_02]
  linear_combination ((-1 / 36) * t ^ 2) * alpha_sq
theorem v11_03 (t : ℂ) : (momentPoly 11 z11 0 3).eval t = ((-83 / 40) * t ^ 3 + (-183 / 160) * t ^ 5 + (83 / 120) * d * t ^ 3 + (-287 / 480) * d * t ^ 5 + (47 / 1152) * d * t ^ 9 + (-3147 / 200) * alpha * t ^ 3 + (28741 / 2400) * alpha * t ^ 5 + (60151 / 28800) * alpha * t ^ 9 + (83 / 120) * alpha * d * t ^ 3 + (-99 / 160) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_01, v10_02, v10_03]
  simp only [phase11_00, phase11_01, phase11_02, phase11_03]
  linear_combination ((83 / 120) * t ^ 3 + (-73 / 120) * t ^ 5 + (-1 / 288) * d * t ^ 5) * alpha_sq
theorem v11_04 (t : ℂ) : (momentPoly 11 z11 0 4).eval t = ((-49184 / 375) * t ^ 4 + (543911 / 2000) * t ^ 6 + (-945487 / 6000) * t ^ 8 + (909619 / 36000) * t ^ 10 + (-2024771 / 576000) * t ^ 16 + (-83 / 240) * d * t ^ 6 + (73 / 240) * d * t ^ 8 + (-47 / 288) * d * t ^ 10 + (52264 / 375) * alpha * t ^ 4 + (-1278203 / 6000) * alpha * t ^ 6 + (199579 / 2000) * alpha * t ^ 8 + (-314993 / 12000) * alpha * t ^ 10 + (5033 / 1125) * alpha * t ^ 16 + (-616 / 225) * alpha * d * t ^ 4 + (951 / 400) * alpha * d * t ^ 6 + (-73 / 720) * alpha * d * t ^ 8 + (5897 / 21600) * alpha * d * t ^ 10 + (95 / 13824) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_01, v10_02, v10_03, v10_04]
  simp only [phase11_00, phase11_01, phase11_02, phase11_03, phase11_04]
  linear_combination ((-616 / 225) * t ^ 4 + (509 / 225) * t ^ 6 + (3497 / 21600) * t ^ 10 + (83 / 720) * d * t ^ 6 + (-73 / 720) * d * t ^ 8) * alpha_sq
theorem v11_10 (t : ℂ) : (momentPoly 11 z11 1 0).eval t = ((-1) * t + (1 / 24) * d * t + (7 / 24) * alpha * t) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_10]
  simp only [phase11_00, phase11_10]
  ring
theorem v11_11 (t : ℂ) : (momentPoly 11 z11 1 1).eval t = (11 + (-35 / 4) * t ^ 2 + (-1 / 12) * d * t ^ 2) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_01, v10_10, v10_11]
  simp only [phase11_00, phase11_01, phase11_10, phase11_11]
  linear_combination ((1 / 36) * t ^ 2) * alpha_sq
theorem v11_12 (t : ℂ) : (momentPoly 11 z11 1 2).eval t = ((-21) * t + (61 / 8) * t ^ 3 + (877 / 96) * t ^ 5 + (7 / 8) * d * t + (-59 / 120) * d * t ^ 3 + (-33 / 160) * d * t ^ 5 + (-49 / 8) * alpha * t + (163 / 120) * alpha * t ^ 3 + (1973 / 480) * alpha * t ^ 5 + (83 / 360) * alpha * d * t ^ 3 + (-33 / 160) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_01, v10_02, v10_10, v10_11, v10_12]
  simp only [phase11_00, phase11_01, phase11_02, phase11_10, phase11_11, phase11_12]
  linear_combination ((-83 / 360) * t ^ 3 + (73 / 360) * t ^ 5 + (1 / 864) * d * t ^ 5) * alpha_sq
theorem v11_13 (t : ℂ) : (momentPoly 11 z11 1 3).eval t = ((337 / 2) * t ^ 2 + (-574759 / 2400) * t ^ 4 + (30341 / 400) * t ^ 6 + (29027 / 9600) * t ^ 10 + (-5 / 2) * d * t ^ 2 + (13 / 15) * d * t ^ 4 + (161 / 120) * d * t ^ 6 + (-47 / 1152) * d * t ^ 10 + (327 / 2) * alpha * t ^ 2 + (-19978 / 75) * alpha * t ^ 4 + (61541 / 600) * alpha * t ^ 6 + (80009 / 28800) * alpha * t ^ 10 + (-5 / 6) * alpha * d * t ^ 2 + (-691 / 2400) * alpha * d * t ^ 4 + (369 / 400) * alpha * d * t ^ 6 + (2749 / 28800) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_01, v10_02, v10_03, v10_10, v10_11, v10_12, v10_13]
  simp only [phase11_00, phase11_01, phase11_02, phase11_03, phase11_10, phase11_11, phase11_12, phase11_13]
  linear_combination ((-5 / 6) * t ^ 2 + (73 / 75) * t ^ 4 + (-71 / 600) * t ^ 6 + (-3497 / 86400) * t ^ 10) * alpha_sq
theorem v11_14 (t : ℂ) : (momentPoly 11 z11 1 4).eval t = ((-1577 / 20) * t ^ 3 + (61241 / 2000) * t ^ 5 + (-30137 / 750) * t ^ 7 + (478889 / 6000) * t ^ 9 + (-5254 / 1125) * t ^ 11 + (-25557 / 64000) * t ^ 17 + (1577 / 60) * d * t ^ 3 + (-876973 / 18000) * d * t ^ 5 + (6743 / 250) * d * t ^ 7 + (-563437 / 144000) * d * t ^ 9 + (2563 / 18000) * d * t ^ 11 + (-111329 / 576000) * d * t ^ 17 + (-59793 / 100) * alpha * t ^ 3 + (13168147 / 18000) * alpha * t ^ 5 + (3103 / 250) * alpha * t ^ 7 + (-12454637 / 144000) * alpha * t ^ 9 + (-356239 / 6000) * alpha * t ^ 11 + (-1425323 / 192000) * alpha * t ^ 17 + (1577 / 60) * alpha * d * t ^ 3 + (-682667 / 18000) * alpha * d * t ^ 5 + (15233 / 2250) * alpha * d * t ^ 7 + (11171 / 2000) * alpha * d * t ^ 9 + (-221 / 375) * alpha * d * t ^ 11 + (310237 / 1728000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_01, v10_02, v10_03, v10_04, v10_10, v10_11, v10_12, v10_13, v10_14]
  simp only [phase11_00, phase11_01, phase11_02, phase11_03, phase11_04, phase11_10, phase11_11, phase11_12, phase11_13, phase11_14]
  linear_combination ((1577 / 60) * t ^ 3 + (-221087 / 4500) * t ^ 5 + (30506 / 1125) * t ^ 7 + (-48257 / 9000) * t ^ 9 + (5254 / 3375) * t ^ 11 + (-5033 / 27000) * t ^ 17 + (-59 / 432) * d * t ^ 5 + (13 / 270) * d * t ^ 7 + (161 / 2160) * d * t ^ 9 + (95 / 41472) * d * t ^ 17) * alpha_sq
theorem v11_20 (t : ℂ) : (momentPoly 11 z11 2 0).eval t = ((337 / 60) * t ^ 2 + (-1861 / 480) * t ^ 4 + (-1 / 12) * d * t ^ 2 + (-109 / 20) * alpha * t ^ 2 + (73 / 15) * alpha * t ^ 4 + (1 / 36) * alpha * d * t ^ 2 + (-1 / 288) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_10, v10_20]
  simp only [phase11_00, phase11_10, phase11_20]
  linear_combination ((-1 / 36) * t ^ 2) * alpha_sq
theorem v11_21 (t : ℂ) : (momentPoly 11 z11 2 1).eval t = ((-21) * t + (61 / 8) * t ^ 3 + (877 / 96) * t ^ 5 + (7 / 8) * d * t + (-59 / 120) * d * t ^ 3 + (-33 / 160) * d * t ^ 5 + (49 / 8) * alpha * t + (-163 / 120) * alpha * t ^ 3 + (-1973 / 480) * alpha * t ^ 5 + (-83 / 360) * alpha * d * t ^ 3 + (33 / 160) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_01, v10_10, v10_11, v10_20, v10_21]
  simp only [phase11_00, phase11_01, phase11_10, phase11_11, phase11_20, phase11_21]
  linear_combination ((-83 / 360) * t ^ 3 + (73 / 360) * t ^ 5 + (1 / 864) * d * t ^ 5) * alpha_sq
theorem v11_22 (t : ℂ) : (momentPoly 11 z11 2 2).eval t = (231 + (-350) * t ^ 2 + (5524 / 25) * t ^ 4 + (-201629 / 1200) * t ^ 6 + (90127 / 1200) * t ^ 8 + (-10 / 3) * d * t ^ 2 + (52 / 45) * d * t ^ 4 + (457 / 240) * d * t ^ 6 + (-73 / 720) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_01, v10_02, v10_10, v10_11, v10_12, v10_20, v10_21, v10_22]
  simp only [phase11_00, phase11_01, phase11_02, phase11_10, phase11_11, phase11_12, phase11_20, phase11_21, phase11_22]
  linear_combination ((10 / 9) * t ^ 2 + (-52 / 135) * t ^ 4 + (-161 / 270) * t ^ 6 + (-83 / 2160) * d * t ^ 6 + (73 / 2160) * d * t ^ 8) * alpha_sq
theorem v11_23 (t : ℂ) : (momentPoly 11 z11 2 3).eval t = ((-631) * t + (3477 / 8) * t ^ 3 + (4536163 / 12000) * t ^ 5 + (-3769 / 300) * t ^ 7 + (-2058073 / 12000) * t ^ 9 + (2005813 / 144000) * t ^ 11 + (-4247023 / 144000) * t ^ 13 + (631 / 24) * d * t + (-1121 / 40) * d * t ^ 3 + (8077 / 1440) * d * t ^ 5 + (-12833 / 900) * d * t ^ 7 + (26029 / 2400) * d * t ^ 9 + (4489 / 9600) * d * t ^ 11 + (-5129 / 28800) * d * t ^ 13 + (-4417 / 24) * alpha * t + (3097 / 40) * alpha * t ^ 3 + (8486173 / 36000) * alpha * t ^ 5 + (-66269 / 900) * alpha * t ^ 7 + (-652651 / 12000) * alpha * t ^ 9 + (598951 / 144000) * alpha * t ^ 11 + (-1135741 / 144000) * alpha * t ^ 13 + (1577 / 120) * alpha * d * t ^ 3 + (-157439 / 7200) * alpha * d * t ^ 5 + (7657 / 900) * alpha * d * t ^ 7 + (161 / 1440) * alpha * d * t ^ 9 + (1391 / 86400) * alpha * d * t ^ 11 + (3431 / 17280) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_01, v10_02, v10_03, v10_10, v10_11, v10_12, v10_13, v10_20, v10_21, v10_22, v10_23]
  simp only [phase11_00, phase11_01, phase11_02, phase11_03, phase11_10, phase11_11, phase11_12, phase11_13, phase11_20, phase11_21, phase11_22, phase11_23]
  linear_combination ((-1577 / 120) * t ^ 3 + (12997 / 600) * t ^ 5 + (-1898 / 225) * t ^ 7 + (-26747 / 28800) * t ^ 11 + (10439 / 17280) * t ^ 13 + (59 / 864) * d * t ^ 5 + (89 / 2700) * d * t ^ 7 + (-1823 / 21600) * d * t ^ 9 + (-221 / 32400) * d * t ^ 13) * alpha_sq
theorem v11_24 (t : ℂ) : (momentPoly 11 z11 2 4).eval t = ((96382 / 15) * t ^ 2 + (-10658431 / 800) * t ^ 4 + (17182598 / 1875) * t ^ 6 + (-26753201 / 7500) * t ^ 8 + (50373833 / 24000) * t ^ 10 + (-182927687 / 180000) * t ^ 12 + (45422413 / 180000) * t ^ 14 + (135437677 / 2880000) * t ^ 18 + (-137578247 / 2880000) * t ^ 20 + (-286 / 3) * d * t ^ 2 + (312 / 5) * d * t ^ 4 + (29324 / 375) * d * t ^ 6 + (-37307 / 4500) * d * t ^ 8 + (-2853989 / 72000) * d * t ^ 10 + (155849 / 36000) * d * t ^ 12 + (-338053 / 108000) * d * t ^ 14 + (1577 / 13824) * d * t ^ 18 + (-30949 / 576000) * d * t ^ 20 + (31174 / 5) * alpha * t ^ 2 + (-356467 / 25) * alpha * t ^ 4 + (62135684 / 5625) * alpha * t ^ 6 + (-103811513 / 22500) * alpha * t ^ 8 + (190676411 / 72000) * alpha * t ^ 10 + (-673580471 / 540000) * alpha * t ^ 12 + (11529031 / 60000) * alpha * t ^ 14 + (12288443 / 320000) * alpha * t ^ 18 + (-255622891 / 8640000) * alpha * t ^ 20 + (-286 / 9) * alpha * d * t ^ 2 + (-58177 / 2400) * alpha * d * t ^ 4 + (94946 / 1125) * alpha * d * t ^ 6 + (1039 / 900) * alpha * d * t ^ 8 + (-600803 / 24000) * alpha * d * t ^ 10 + (-225283 / 108000) * alpha * d * t ^ 12 + (-238801 / 108000) * alpha * d * t ^ 14 + (-1076137 / 1728000) * alpha * d * t ^ 18 + (-30949 / 1728000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_01, v10_02, v10_03, v10_04, v10_10, v10_11, v10_12, v10_13, v10_14, v10_20, v10_21, v10_22, v10_23, v10_24]
  simp only [phase11_00, phase11_01, phase11_02, phase11_03, phase11_04, phase11_10, phase11_11, phase11_12, phase11_13, phase11_14, phase11_20, phase11_21, phase11_22, phase11_23, phase11_24]
  linear_combination ((-286 / 9) * t ^ 2 + (1752 / 25) * t ^ 4 + (-131644 / 3375) * t ^ 6 + (-8728 / 3375) * t ^ 8 + (2021 / 960) * t ^ 10 + (162469 / 40500) * t ^ 12 + (-1073831 / 324000) * t ^ 14 + (13381 / 20250) * t ^ 18 + (-6533 / 13500) * d * t ^ 8 + (1921 / 2250) * d * t ^ 10 + (-48257 / 108000) * d * t ^ 12 + (7243 / 81000) * d * t ^ 14 + (-1577 / 41472) * d * t ^ 18 + (30949 / 1728000) * d * t ^ 20) * alpha_sq
theorem v11_30 (t : ℂ) : (momentPoly 11 z11 3 0).eval t = ((-83 / 40) * t ^ 3 + (-183 / 160) * t ^ 5 + (83 / 120) * d * t ^ 3 + (-287 / 480) * d * t ^ 5 + (47 / 1152) * d * t ^ 9 + (3147 / 200) * alpha * t ^ 3 + (-28741 / 2400) * alpha * t ^ 5 + (-60151 / 28800) * alpha * t ^ 9 + (-83 / 120) * alpha * d * t ^ 3 + (99 / 160) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_10, v10_20, v10_30]
  simp only [phase11_00, phase11_10, phase11_20, phase11_30]
  linear_combination ((83 / 120) * t ^ 3 + (-73 / 120) * t ^ 5 + (-1 / 288) * d * t ^ 5) * alpha_sq
theorem v11_31 (t : ℂ) : (momentPoly 11 z11 3 1).eval t = ((337 / 2) * t ^ 2 + (-574759 / 2400) * t ^ 4 + (30341 / 400) * t ^ 6 + (29027 / 9600) * t ^ 10 + (-5 / 2) * d * t ^ 2 + (13 / 15) * d * t ^ 4 + (161 / 120) * d * t ^ 6 + (-47 / 1152) * d * t ^ 10 + (-327 / 2) * alpha * t ^ 2 + (19978 / 75) * alpha * t ^ 4 + (-61541 / 600) * alpha * t ^ 6 + (-80009 / 28800) * alpha * t ^ 10 + (5 / 6) * alpha * d * t ^ 2 + (691 / 2400) * alpha * d * t ^ 4 + (-369 / 400) * alpha * d * t ^ 6 + (-2749 / 28800) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_01, v10_10, v10_11, v10_20, v10_21, v10_30, v10_31]
  simp only [phase11_00, phase11_01, phase11_10, phase11_11, phase11_20, phase11_21, phase11_30, phase11_31]
  linear_combination ((-5 / 6) * t ^ 2 + (73 / 75) * t ^ 4 + (-71 / 600) * t ^ 6 + (-3497 / 86400) * t ^ 10) * alpha_sq
theorem v11_32 (t : ℂ) : (momentPoly 11 z11 3 2).eval t = ((-631) * t + (3477 / 8) * t ^ 3 + (4536163 / 12000) * t ^ 5 + (-3769 / 300) * t ^ 7 + (-2058073 / 12000) * t ^ 9 + (2005813 / 144000) * t ^ 11 + (-4247023 / 144000) * t ^ 13 + (631 / 24) * d * t + (-1121 / 40) * d * t ^ 3 + (8077 / 1440) * d * t ^ 5 + (-12833 / 900) * d * t ^ 7 + (26029 / 2400) * d * t ^ 9 + (4489 / 9600) * d * t ^ 11 + (-5129 / 28800) * d * t ^ 13 + (4417 / 24) * alpha * t + (-3097 / 40) * alpha * t ^ 3 + (-8486173 / 36000) * alpha * t ^ 5 + (66269 / 900) * alpha * t ^ 7 + (652651 / 12000) * alpha * t ^ 9 + (-598951 / 144000) * alpha * t ^ 11 + (1135741 / 144000) * alpha * t ^ 13 + (-1577 / 120) * alpha * d * t ^ 3 + (157439 / 7200) * alpha * d * t ^ 5 + (-7657 / 900) * alpha * d * t ^ 7 + (-161 / 1440) * alpha * d * t ^ 9 + (-1391 / 86400) * alpha * d * t ^ 11 + (-3431 / 17280) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_01, v10_02, v10_10, v10_11, v10_12, v10_20, v10_21, v10_22, v10_30, v10_31, v10_32]
  simp only [phase11_00, phase11_01, phase11_02, phase11_10, phase11_11, phase11_12, phase11_20, phase11_21, phase11_22, phase11_30, phase11_31, phase11_32]
  linear_combination ((-1577 / 120) * t ^ 3 + (12997 / 600) * t ^ 5 + (-1898 / 225) * t ^ 7 + (-26747 / 28800) * t ^ 11 + (10439 / 17280) * t ^ 13 + (59 / 864) * d * t ^ 5 + (89 / 2700) * d * t ^ 7 + (-1823 / 21600) * d * t ^ 9 + (-221 / 32400) * d * t ^ 13) * alpha_sq
theorem v11_33 (t : ℂ) : (momentPoly 11 z11 3 3).eval t = (6941 + (-15015) * t ^ 2 + (447444 / 25) * t ^ 4 + (-155932009 / 7500) * t ^ 6 + (432555593 / 30000) * t ^ 8 + (-4349179 / 1250) * t ^ 10 + (7632653 / 22500) * t ^ 12 + (-16561277 / 60000) * t ^ 14 + (547241 / 180000) * t ^ 18 + (-143) * d * t ^ 2 + (468 / 5) * d * t ^ 4 + (190469 / 1500) * d * t ^ 6 + (-12283 / 400) * d * t ^ 8 + (-11129 / 250) * d * t ^ 10 + (3134 / 1125) * d * t ^ 12 + (-40433 / 6000) * d * t ^ 14) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_01, v10_02, v10_03, v10_10, v10_11, v10_12, v10_13, v10_20, v10_21, v10_22, v10_23, v10_30, v10_31, v10_32, v10_33]
  simp only [phase11_00, phase11_01, phase11_02, phase11_03, phase11_10, phase11_11, phase11_12, phase11_13, phase11_20, phase11_21, phase11_22, phase11_23, phase11_30, phase11_31, phase11_32, phase11_33]
  linear_combination ((143 / 3) * t ^ 2 + (-156 / 5) * t ^ 4 + (-14662 / 375) * t ^ 6 + (1096 / 225) * t ^ 8 + (19066 / 1125) * t ^ 10 + (14173 / 4500) * t ^ 12 + (-38269 / 36000) * t ^ 14 + (-31603 / 64800) * t ^ 18 + (-581 / 180) * d * t ^ 6 + (19313 / 3600) * d * t ^ 8 + (-949 / 450) * d * t ^ 10 + (-653 / 10800) * d * t ^ 14) * alpha_sq
theorem v11_34 (t : ℂ) : (momentPoly 11 z11 3 4).eval t = ((-24101) * t + 23607 * t ^ 3 + (55457417 / 4000) * t ^ 5 + (16278553 / 6250) * t ^ 7 + (-2963598967 / 150000) * t ^ 9 + (2698571521 / 1200000) * t ^ 11 + (-600510841 / 720000) * t ^ 13 + (128548543 / 75000) * t ^ 15 + (2079187807 / 3600000) * t ^ 17 + (-334559107 / 1350000) * t ^ 19 + (49164887 / 225000) * t ^ 21 + (313539983 / 10800000) * t ^ 25 + (24101 / 24) * d * t + (-7611 / 5) * d * t ^ 3 + (108443 / 96) * d * t ^ 5 + (-4933189 / 2250) * d * t ^ 7 + (4075421 / 2000) * d * t ^ 9 + (-203435219 / 720000) * d * t ^ 11 + (-73437469 / 432000) * d * t ^ 13 + (2789 / 1000) * d * t ^ 15 + (-839069 / 144000) * d * t ^ 17 + (746461 / 108000) * d * t ^ 19 + (-2305309 / 480000) * d * t ^ 21 + (-40903 / 288000) * d * t ^ 25 + (-168707 / 24) * alpha * t + (21027 / 5) * alpha * t ^ 3 + (155204407 / 12000) * alpha * t ^ 5 + (-158488427 / 18750) * alpha * t ^ 7 + (-116343623 / 50000) * alpha * t ^ 9 + (-1602225599 / 3600000) * alpha * t ^ 11 + (1217588303 / 2160000) * alpha * t ^ 13 + (58914583 / 225000) * alpha * t ^ 15 + (1087515269 / 3600000) * alpha * t ^ 17 + (-209317193 / 2700000) * alpha * t ^ 19 + (330876173 / 7200000) * alpha * t ^ 21 + (168353447 / 21600000) * alpha * t ^ 25 + (3569 / 5) * alpha * d * t ^ 3 + (-4014941 / 2400) * alpha * d * t ^ 5 + (4980227 / 3750) * alpha * d * t ^ 7 + (-52488149 / 90000) * alpha * d * t ^ 9 + (48840631 / 144000) * alpha * d * t ^ 11 + (-93043901 / 720000) * alpha * d * t ^ 13 + (11933 / 15000) * alpha * d * t ^ 15 + (2018951 / 432000) * alpha * d * t ^ 17 + (1595239 / 405000) * alpha * d * t ^ 19 + (-652693 / 135000) * alpha * d * t ^ 21 + (236551 / 1296000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_01, v10_02, v10_03, v10_04, v10_10, v10_11, v10_12, v10_13, v10_14, v10_20, v10_21, v10_22, v10_23, v10_24, v10_30, v10_31, v10_32, v10_33, v10_34]
  simp only [phase11_00, phase11_01, phase11_02, phase11_03, phase11_04, phase11_10, phase11_11, phase11_12, phase11_13, phase11_14, phase11_20, phase11_21, phase11_22, phase11_23, phase11_24, phase11_30, phase11_31, phase11_32, phase11_33, phase11_34]
  linear_combination ((-3569 / 5) * t ^ 3 + (996829 / 600) * t ^ 5 + (-7427278 / 5625) * t ^ 7 + (3334234 / 5625) * t ^ 9 + (-63603241 / 144000) * t ^ 11 + (22596539 / 80000) * t ^ 13 + (-234271 / 5000) * t ^ 15 + (-6900751 / 432000) * t ^ 17 + (-1001011 / 270000) * t ^ 19 + (652693 / 135000) * t ^ 21 + (-719719 / 1296000) * t ^ 25 + (1105 / 288) * d * t ^ 5 + (4717 / 1350) * d * t ^ 7 + (-606061 / 54000) * d * t ^ 9 + (1649 / 3375) * d * t ^ 11 + (437069 / 162000) * d * t ^ 13 + (397 / 810) * d * t ^ 15 + (31141 / 162000) * d * t ^ 17 + (1463 / 12960) * d * t ^ 19 + (-27679 / 2592000) * d * t ^ 21 + (-4199 / 311040) * d * t ^ 25) * alpha_sq
theorem v11_40 (t : ℂ) : (momentPoly 11 z11 4 0).eval t = ((-49184 / 375) * t ^ 4 + (543911 / 2000) * t ^ 6 + (-945487 / 6000) * t ^ 8 + (909619 / 36000) * t ^ 10 + (-2024771 / 576000) * t ^ 16 + (-83 / 240) * d * t ^ 6 + (73 / 240) * d * t ^ 8 + (-47 / 288) * d * t ^ 10 + (-52264 / 375) * alpha * t ^ 4 + (1278203 / 6000) * alpha * t ^ 6 + (-199579 / 2000) * alpha * t ^ 8 + (314993 / 12000) * alpha * t ^ 10 + (-5033 / 1125) * alpha * t ^ 16 + (616 / 225) * alpha * d * t ^ 4 + (-951 / 400) * alpha * d * t ^ 6 + (73 / 720) * alpha * d * t ^ 8 + (-5897 / 21600) * alpha * d * t ^ 10 + (-95 / 13824) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_10, v10_20, v10_30, v10_40]
  simp only [phase11_00, phase11_10, phase11_20, phase11_30, phase11_40]
  linear_combination ((-616 / 225) * t ^ 4 + (509 / 225) * t ^ 6 + (3497 / 21600) * t ^ 10 + (83 / 720) * d * t ^ 6 + (-73 / 720) * d * t ^ 8) * alpha_sq
theorem v11_41 (t : ℂ) : (momentPoly 11 z11 4 1).eval t = ((-1577 / 20) * t ^ 3 + (61241 / 2000) * t ^ 5 + (-30137 / 750) * t ^ 7 + (478889 / 6000) * t ^ 9 + (-5254 / 1125) * t ^ 11 + (-25557 / 64000) * t ^ 17 + (1577 / 60) * d * t ^ 3 + (-876973 / 18000) * d * t ^ 5 + (6743 / 250) * d * t ^ 7 + (-563437 / 144000) * d * t ^ 9 + (2563 / 18000) * d * t ^ 11 + (-111329 / 576000) * d * t ^ 17 + (59793 / 100) * alpha * t ^ 3 + (-13168147 / 18000) * alpha * t ^ 5 + (-3103 / 250) * alpha * t ^ 7 + (12454637 / 144000) * alpha * t ^ 9 + (356239 / 6000) * alpha * t ^ 11 + (1425323 / 192000) * alpha * t ^ 17 + (-1577 / 60) * alpha * d * t ^ 3 + (682667 / 18000) * alpha * d * t ^ 5 + (-15233 / 2250) * alpha * d * t ^ 7 + (-11171 / 2000) * alpha * d * t ^ 9 + (221 / 375) * alpha * d * t ^ 11 + (-310237 / 1728000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_01, v10_10, v10_11, v10_20, v10_21, v10_30, v10_31, v10_40, v10_41]
  simp only [phase11_00, phase11_01, phase11_10, phase11_11, phase11_20, phase11_21, phase11_30, phase11_31, phase11_40, phase11_41]
  linear_combination ((1577 / 60) * t ^ 3 + (-221087 / 4500) * t ^ 5 + (30506 / 1125) * t ^ 7 + (-48257 / 9000) * t ^ 9 + (5254 / 3375) * t ^ 11 + (-5033 / 27000) * t ^ 17 + (-59 / 432) * d * t ^ 5 + (13 / 270) * d * t ^ 7 + (161 / 2160) * d * t ^ 9 + (95 / 41472) * d * t ^ 17) * alpha_sq
theorem v11_42 (t : ℂ) : (momentPoly 11 z11 4 2).eval t = ((96382 / 15) * t ^ 2 + (-10658431 / 800) * t ^ 4 + (17182598 / 1875) * t ^ 6 + (-26753201 / 7500) * t ^ 8 + (50373833 / 24000) * t ^ 10 + (-182927687 / 180000) * t ^ 12 + (45422413 / 180000) * t ^ 14 + (135437677 / 2880000) * t ^ 18 + (-137578247 / 2880000) * t ^ 20 + (-286 / 3) * d * t ^ 2 + (312 / 5) * d * t ^ 4 + (29324 / 375) * d * t ^ 6 + (-37307 / 4500) * d * t ^ 8 + (-2853989 / 72000) * d * t ^ 10 + (155849 / 36000) * d * t ^ 12 + (-338053 / 108000) * d * t ^ 14 + (1577 / 13824) * d * t ^ 18 + (-30949 / 576000) * d * t ^ 20 + (-31174 / 5) * alpha * t ^ 2 + (356467 / 25) * alpha * t ^ 4 + (-62135684 / 5625) * alpha * t ^ 6 + (103811513 / 22500) * alpha * t ^ 8 + (-190676411 / 72000) * alpha * t ^ 10 + (673580471 / 540000) * alpha * t ^ 12 + (-11529031 / 60000) * alpha * t ^ 14 + (-12288443 / 320000) * alpha * t ^ 18 + (255622891 / 8640000) * alpha * t ^ 20 + (286 / 9) * alpha * d * t ^ 2 + (58177 / 2400) * alpha * d * t ^ 4 + (-94946 / 1125) * alpha * d * t ^ 6 + (-1039 / 900) * alpha * d * t ^ 8 + (600803 / 24000) * alpha * d * t ^ 10 + (225283 / 108000) * alpha * d * t ^ 12 + (238801 / 108000) * alpha * d * t ^ 14 + (1076137 / 1728000) * alpha * d * t ^ 18 + (30949 / 1728000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_01, v10_02, v10_10, v10_11, v10_12, v10_20, v10_21, v10_22, v10_30, v10_31, v10_32, v10_40, v10_41, v10_42]
  simp only [phase11_00, phase11_01, phase11_02, phase11_10, phase11_11, phase11_12, phase11_20, phase11_21, phase11_22, phase11_30, phase11_31, phase11_32, phase11_40, phase11_41, phase11_42]
  linear_combination ((-286 / 9) * t ^ 2 + (1752 / 25) * t ^ 4 + (-131644 / 3375) * t ^ 6 + (-8728 / 3375) * t ^ 8 + (2021 / 960) * t ^ 10 + (162469 / 40500) * t ^ 12 + (-1073831 / 324000) * t ^ 14 + (13381 / 20250) * t ^ 18 + (-6533 / 13500) * d * t ^ 8 + (1921 / 2250) * d * t ^ 10 + (-48257 / 108000) * d * t ^ 12 + (7243 / 81000) * d * t ^ 14 + (-1577 / 41472) * d * t ^ 18 + (30949 / 1728000) * d * t ^ 20) * alpha_sq
theorem v11_43 (t : ℂ) : (momentPoly 11 z11 4 3).eval t = ((-24101) * t + 23607 * t ^ 3 + (55457417 / 4000) * t ^ 5 + (16278553 / 6250) * t ^ 7 + (-2963598967 / 150000) * t ^ 9 + (2698571521 / 1200000) * t ^ 11 + (-600510841 / 720000) * t ^ 13 + (128548543 / 75000) * t ^ 15 + (2079187807 / 3600000) * t ^ 17 + (-334559107 / 1350000) * t ^ 19 + (49164887 / 225000) * t ^ 21 + (313539983 / 10800000) * t ^ 25 + (24101 / 24) * d * t + (-7611 / 5) * d * t ^ 3 + (108443 / 96) * d * t ^ 5 + (-4933189 / 2250) * d * t ^ 7 + (4075421 / 2000) * d * t ^ 9 + (-203435219 / 720000) * d * t ^ 11 + (-73437469 / 432000) * d * t ^ 13 + (2789 / 1000) * d * t ^ 15 + (-839069 / 144000) * d * t ^ 17 + (746461 / 108000) * d * t ^ 19 + (-2305309 / 480000) * d * t ^ 21 + (-40903 / 288000) * d * t ^ 25 + (168707 / 24) * alpha * t + (-21027 / 5) * alpha * t ^ 3 + (-155204407 / 12000) * alpha * t ^ 5 + (158488427 / 18750) * alpha * t ^ 7 + (116343623 / 50000) * alpha * t ^ 9 + (1602225599 / 3600000) * alpha * t ^ 11 + (-1217588303 / 2160000) * alpha * t ^ 13 + (-58914583 / 225000) * alpha * t ^ 15 + (-1087515269 / 3600000) * alpha * t ^ 17 + (209317193 / 2700000) * alpha * t ^ 19 + (-330876173 / 7200000) * alpha * t ^ 21 + (-168353447 / 21600000) * alpha * t ^ 25 + (-3569 / 5) * alpha * d * t ^ 3 + (4014941 / 2400) * alpha * d * t ^ 5 + (-4980227 / 3750) * alpha * d * t ^ 7 + (52488149 / 90000) * alpha * d * t ^ 9 + (-48840631 / 144000) * alpha * d * t ^ 11 + (93043901 / 720000) * alpha * d * t ^ 13 + (-11933 / 15000) * alpha * d * t ^ 15 + (-2018951 / 432000) * alpha * d * t ^ 17 + (-1595239 / 405000) * alpha * d * t ^ 19 + (652693 / 135000) * alpha * d * t ^ 21 + (-236551 / 1296000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_01, v10_02, v10_03, v10_10, v10_11, v10_12, v10_13, v10_20, v10_21, v10_22, v10_23, v10_30, v10_31, v10_32, v10_33, v10_40, v10_41, v10_42, v10_43]
  simp only [phase11_00, phase11_01, phase11_02, phase11_03, phase11_10, phase11_11, phase11_12, phase11_13, phase11_20, phase11_21, phase11_22, phase11_23, phase11_30, phase11_31, phase11_32, phase11_33, phase11_40, phase11_41, phase11_42, phase11_43]
  linear_combination ((-3569 / 5) * t ^ 3 + (996829 / 600) * t ^ 5 + (-7427278 / 5625) * t ^ 7 + (3334234 / 5625) * t ^ 9 + (-63603241 / 144000) * t ^ 11 + (22596539 / 80000) * t ^ 13 + (-234271 / 5000) * t ^ 15 + (-6900751 / 432000) * t ^ 17 + (-1001011 / 270000) * t ^ 19 + (652693 / 135000) * t ^ 21 + (-719719 / 1296000) * t ^ 25 + (1105 / 288) * d * t ^ 5 + (4717 / 1350) * d * t ^ 7 + (-606061 / 54000) * d * t ^ 9 + (1649 / 3375) * d * t ^ 11 + (437069 / 162000) * d * t ^ 13 + (397 / 810) * d * t ^ 15 + (31141 / 162000) * d * t ^ 17 + (1463 / 12960) * d * t ^ 19 + (-27679 / 2592000) * d * t ^ 21 + (-4199 / 311040) * d * t ^ 25) * alpha_sq
theorem v11_44 (t : ℂ) : (momentPoly 11 z11 4 4).eval t = (265111 + (-727510) * t ^ 2 + (30691344 / 25) * t ^ 4 + (-27866220829 / 15000) * t ^ 6 + (241808586344 / 140625) * t ^ 8 + (-36434695102 / 46875) * t ^ 10 + (294860477 / 1125) * t ^ 12 + (-201989817113 / 1125000) * t ^ 14 + (3866405329 / 46875) * t ^ 16 + (-9398784241 / 562500) * t ^ 18 + (73212051791 / 13500000) * t ^ 20 + (-4096474033 / 750000) * t ^ 22 + (103781452321 / 36000000) * t ^ 24 + (-7471042513 / 9000000) * t ^ 26 + (6640063337 / 108000000) * t ^ 32 + (-20786 / 3) * d * t ^ 2 + (96304 / 15) * d * t ^ 4 + (21442889 / 3000) * d * t ^ 6 + (-75410248 / 28125) * d * t ^ 8 + (-145971502 / 28125) * d * t ^ 10 + (-5384138 / 28125) * d * t ^ 12 + (18613627 / 22500) * d * t ^ 14 + (27836713 / 84375) * d * t ^ 16 + (21806164 / 84375) * d * t ^ 18 + (-652600919 / 8100000) * d * t ^ 20 + (98544859 / 1350000) * d * t ^ 22 + (226211 / 480000) * d * t ^ 24 + (4835977 / 600000) * d * t ^ 26 + (95627 / 518400) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z11, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v10_00, v10_01, v10_02, v10_03, v10_04, v10_10, v10_11, v10_12, v10_13, v10_14, v10_20, v10_21, v10_22, v10_23, v10_24, v10_30, v10_31, v10_32, v10_33, v10_34, v10_40, v10_41, v10_42, v10_43, v10_44]
  simp only [phase11_00, phase11_01, phase11_02, phase11_03, phase11_04, phase11_10, phase11_11, phase11_12, phase11_13, phase11_14, phase11_20, phase11_21, phase11_22, phase11_23, phase11_24, phase11_30, phase11_31, phase11_32, phase11_33, phase11_34, phase11_40, phase11_41, phase11_42, phase11_43, phase11_44]
  linear_combination ((20786 / 9) * t ^ 2 + (-96304 / 45) * t ^ 4 + (-2422283 / 1125) * t ^ 6 + (29885248 / 84375) * t ^ 8 + (182633392 / 84375) * t ^ 10 + (36886093 / 84375) * t ^ 12 + (-371003527 / 405000) * t ^ 14 + (-40396718 / 253125) * t ^ 16 + (15561133 / 337500) * t ^ 18 + (62932292 / 759375) * t ^ 20 + (-6553544 / 253125) * t ^ 22 + (29365387 / 6075000) * t ^ 26 + (-16517 / 72) * d * t ^ 6 + (4856 / 9) * d * t ^ 8 + (-2444126 / 5625) * d * t ^ 10 + (3334234 / 16875) * d * t ^ 12 + (-4927009 / 40500) * d * t ^ 14 + (2910971 / 50625) * d * t ^ 16 + (-457564 / 50625) * d * t ^ 18 + (-124127 / 64800) * d * t ^ 20 + (1262369 / 810000) * d * t ^ 22 + (-226211 / 1440000) * d * t ^ 24 + (137617 / 388800) * d * t ^ 26 + (-95627 / 1555200) * d * t ^ 32) * alpha_sq
#print axioms v11_00
#print axioms v11_11
#print axioms v11_22
#print axioms v11_33
#print axioms v11_44
end PhotonCertA
