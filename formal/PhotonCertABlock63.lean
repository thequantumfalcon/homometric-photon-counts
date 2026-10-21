import PhotonCertABlock42
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
theorem site43 : ((r ^ 3 * thetaPlus) : ℂ) = ((1 / 10) + (-1 / 30) * c + (-1 / 30) * alpha + (-1 / 30) * alpha * c) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 30) + (1 / 80) * c + (1 / 80) * alpha + (1 / 60) * alpha * c + (1 / 60) * alpha ^ 2 + (1 / 240) * alpha ^ 2 * c + (1 / 240) * alpha ^ 3) * alpha_sq
theorem phase43_00 : ((r ^ 3 * thetaPlus) : ℂ) ^ 0 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 0 = (1) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase43_01 : ((r ^ 3 * thetaPlus) : ℂ) ^ 0 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 1 = ((1 / 10) + (-1 / 30) * c + (1 / 30) * alpha + (1 / 30) * alpha * c) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase43_02 : ((r ^ 3 * thetaPlus) : ℂ) ^ 0 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 2 = ((-73 / 150) + (-1 / 75) * c + (-73 / 150) * alpha + (1 / 225) * alpha * c) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 900) + (1 / 450) * c + (1 / 900) * c ^ 2) * alpha_sq + ((-1 / 450) + (-1 / 450) * alpha) * c_sq
theorem phase43_03 : ((r ^ 3 * thetaPlus) : ℂ) ^ 0 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 3 = ((71 / 1125) * c + (-221 / 1125) * alpha) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 3000) + (1 / 1800) * c + (1 / 9000) * c ^ 2 + (-1 / 9000) * c ^ 3 + (1 / 27000) * alpha + (1 / 9000) * alpha * c + (1 / 9000) * alpha * c ^ 2 + (1 / 27000) * alpha * c ^ 3) * alpha_sq + ((1 / 3375) * c + (-1 / 1125) * alpha) * c_sq
theorem phase43_04 : ((r ^ 3 * thetaPlus) : ℂ) ^ 0 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 4 = ((-5033 / 11250) + (146 / 5625) * c + (5033 / 11250) * alpha + (146 / 16875) * alpha * c) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((17 / 270000) + (1 / 13500) * c + (-1 / 27000) * c ^ 2 + (-1 / 22500) * c ^ 3 + (1 / 270000) * c ^ 4 + (1 / 67500) * alpha + (2 / 50625) * alpha * c + (1 / 33750) * alpha * c ^ 2 + (-1 / 202500) * alpha * c ^ 4 + (1 / 810000) * alpha ^ 2 + (1 / 202500) * alpha ^ 2 * c + (1 / 135000) * alpha ^ 2 * c ^ 2 + (1 / 202500) * alpha ^ 2 * c ^ 3 + (1 / 810000) * alpha ^ 2 * c ^ 4) * alpha_sq + ((-34 / 16875) + (2 / 16875) * c + (-1 / 101250) * c ^ 2 + (34 / 16875) * alpha + (2 / 50625) * alpha * c + (1 / 101250) * alpha * c ^ 2) * c_sq
theorem phase43_10 : ((r ^ 3 * thetaPlus) : ℂ) ^ 1 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 0 = ((1 / 10) + (-1 / 30) * c + (-1 / 30) * alpha + (-1 / 30) * alpha * c) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase43_11 : ((r ^ 3 * thetaPlus) : ℂ) ^ 1 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 1 = (1) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 900) + (-1 / 450) * c + (-1 / 900) * c ^ 2) * alpha_sq + ((1 / 225)) * c_sq
theorem phase43_12 : ((r ^ 3 * thetaPlus) : ℂ) ^ 1 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 2 = ((1 / 10) + (-1 / 30) * c + (1 / 30) * alpha + (1 / 30) * alpha * c) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 9000) + (-1 / 5400) * c + (-1 / 27000) * c ^ 2 + (1 / 27000) * c ^ 3 + (-1 / 27000) * alpha + (-1 / 9000) * alpha * c + (-1 / 9000) * alpha * c ^ 2 + (-1 / 27000) * alpha * c ^ 3) * alpha_sq + ((1 / 2250) + (-1 / 6750) * c + (1 / 6750) * alpha + (1 / 6750) * alpha * c) * c_sq
theorem phase43_13 : ((r ^ 3 * thetaPlus) : ℂ) ^ 1 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 3 = ((-73 / 150) + (-1 / 75) * c + (-73 / 150) * alpha + (1 / 225) * alpha * c) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 270000) + (1 / 67500) * c + (1 / 45000) * c ^ 2 + (1 / 67500) * c ^ 3 + (1 / 270000) * c ^ 4 + (-1 / 135000) * alpha + (-1 / 50625) * alpha * c + (-1 / 67500) * alpha * c ^ 2 + (1 / 405000) * alpha * c ^ 4 + (-1 / 810000) * alpha ^ 2 + (-1 / 202500) * alpha ^ 2 * c + (-1 / 135000) * alpha ^ 2 * c ^ 2 + (-1 / 202500) * alpha ^ 2 * c ^ 3 + (-1 / 810000) * alpha ^ 2 * c ^ 4) * alpha_sq + ((-37 / 16875) + (-1 / 16875) * c + (-1 / 101250) * c ^ 2 + (-37 / 16875) * alpha + (1 / 50625) * alpha * c + (-1 / 101250) * alpha * c ^ 2) * c_sq
theorem phase43_14 : ((r ^ 3 * thetaPlus) : ℂ) ^ 1 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 4 = ((71 / 1125) * c + (-221 / 1125) * alpha) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 300000) + (17 / 2700000) * c + (1 / 270000) * c ^ 2 + (17 / 12150000) * c ^ 3 + (1 / 4860000) * c ^ 4 + (-11 / 24300000) * c ^ 5 + (-1 / 1620000) * alpha + (-1 / 900000) * alpha * c + (1 / 2430000) * alpha * c ^ 2 + (7 / 4050000) * alpha * c ^ 3 + (7 / 8100000) * alpha * c ^ 4 + (1 / 24300000) * alpha * c ^ 5 + (-1 / 2700000) * alpha ^ 2 + (-11 / 8100000) * alpha ^ 2 * c + (-7 / 4050000) * alpha ^ 2 * c ^ 2 + (-1 / 1350000) * alpha ^ 2 * c ^ 3 + (1 / 8100000) * alpha ^ 2 * c ^ 4 + (1 / 8100000) * alpha ^ 2 * c ^ 5 + (-1 / 24300000) * alpha ^ 3 + (-1 / 4860000) * alpha ^ 3 * c + (-1 / 2430000) * alpha ^ 3 * c ^ 2 + (-1 / 2430000) * alpha ^ 3 * c ^ 3 + (-1 / 4860000) * alpha ^ 3 * c ^ 4 + (-1 / 24300000) * alpha ^ 3 * c ^ 5) * alpha_sq + ((8 / 28125) * c + (1 / 759375) * c ^ 3 + (-224 / 253125) * alpha + (-1 / 253125) * alpha * c ^ 2) * c_sq
theorem phase43_20 : ((r ^ 3 * thetaPlus) : ℂ) ^ 2 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 0 = ((-73 / 150) + (-1 / 75) * c + (73 / 150) * alpha + (-1 / 225) * alpha * c) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 900) + (1 / 450) * c + (1 / 900) * c ^ 2) * alpha_sq + ((-1 / 450) + (1 / 450) * alpha) * c_sq
theorem phase43_21 : ((r ^ 3 * thetaPlus) : ℂ) ^ 2 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 1 = ((1 / 10) + (-1 / 30) * c + (-1 / 30) * alpha + (-1 / 30) * alpha * c) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 9000) + (-1 / 5400) * c + (-1 / 27000) * c ^ 2 + (1 / 27000) * c ^ 3 + (1 / 27000) * alpha + (1 / 9000) * alpha * c + (1 / 9000) * alpha * c ^ 2 + (1 / 27000) * alpha * c ^ 3) * alpha_sq + ((1 / 2250) + (-1 / 6750) * c + (-1 / 6750) * alpha + (-1 / 6750) * alpha * c) * c_sq
theorem phase43_22 : ((r ^ 3 * thetaPlus) : ℂ) ^ 2 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 2 = (1) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-7 / 270000) + (-1 / 22500) * c + (-7 / 405000) * c ^ 2 + (-1 / 202500) * c ^ 3 + (-1 / 162000) * c ^ 4 + (1 / 810000) * alpha ^ 2 + (1 / 202500) * alpha ^ 2 * c + (1 / 135000) * alpha ^ 2 * c ^ 2 + (1 / 202500) * alpha ^ 2 * c ^ 3 + (1 / 810000) * alpha ^ 2 * c ^ 4) * alpha_sq + ((76 / 16875) + (1 / 50625) * c ^ 2) * c_sq
theorem phase43_23 : ((r ^ 3 * thetaPlus) : ℂ) ^ 2 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 3 = ((1 / 10) + (-1 / 30) * c + (1 / 30) * alpha + (1 / 30) * alpha * c) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-7 / 2700000) + (-29 / 8100000) * c + (-1 / 4050000) * c ^ 2 + (1 / 12150000) * c ^ 3 + (-11 / 24300000) * c ^ 4 + (1 / 4860000) * c ^ 5 + (-7 / 8100000) * alpha + (-19 / 8100000) * alpha * c + (-1 / 486000) * alpha * c ^ 2 + (-1 / 1350000) * alpha * c ^ 3 + (-1 / 2700000) * alpha * c ^ 4 + (-1 / 4860000) * alpha * c ^ 5 + (1 / 8100000) * alpha ^ 2 + (11 / 24300000) * alpha ^ 2 * c + (7 / 12150000) * alpha ^ 2 * c ^ 2 + (1 / 4050000) * alpha ^ 2 * c ^ 3 + (-1 / 24300000) * alpha ^ 2 * c ^ 4 + (-1 / 24300000) * alpha ^ 2 * c ^ 5 + (1 / 24300000) * alpha ^ 3 + (1 / 4860000) * alpha ^ 3 * c + (1 / 2430000) * alpha ^ 3 * c ^ 2 + (1 / 2430000) * alpha ^ 3 * c ^ 3 + (1 / 4860000) * alpha ^ 3 * c ^ 4 + (1 / 24300000) * alpha ^ 3 * c ^ 5) * alpha_sq + ((38 / 84375) + (-38 / 253125) * c + (1 / 506250) * c ^ 2 + (-1 / 1518750) * c ^ 3 + (38 / 253125) * alpha + (38 / 253125) * alpha * c + (1 / 1518750) * alpha * c ^ 2 + (1 / 1518750) * alpha * c ^ 3) * c_sq
theorem phase43_24 : ((r ^ 3 * thetaPlus) : ℂ) ^ 2 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 4 = ((-73 / 150) + (-1 / 75) * c + (-73 / 150) * alpha + (1 / 225) * alpha * c) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 16200000) + (1 / 8100000) * c + (103 / 243000000) * c ^ 2 + (17 / 60750000) * c ^ 3 + (77 / 729000000) * c ^ 4 + (29 / 364500000) * c ^ 5 + (11 / 729000000) * c ^ 6 + (-7 / 40500000) * alpha + (-1 / 2430000) * alpha * c + (-31 / 121500000) * alpha * c ^ 2 + (-1 / 91125000) * alpha * c ^ 3 + (-1 / 40500000) * alpha * c ^ 4 + (-1 / 60750000) * alpha * c ^ 5 + (1 / 72900000) * alpha * c ^ 6 + (-1 / 60750000) * alpha ^ 2 + (-1 / 15187500) * alpha ^ 2 * c + (-19 / 182250000) * alpha ^ 2 * c ^ 2 + (-1 / 11390625) * alpha ^ 2 * c ^ 3 + (-1 / 20250000) * alpha ^ 2 * c ^ 4 + (-1 / 45562500) * alpha ^ 2 * c ^ 5 + (-1 / 182250000) * alpha ^ 2 * c ^ 6 + (1 / 121500000) * alpha ^ 3 + (7 / 182250000) * alpha ^ 3 * c + (1 / 14580000) * alpha ^ 3 * c ^ 2 + (1 / 18225000) * alpha ^ 3 * c ^ 3 + (1 / 72900000) * alpha ^ 3 * c ^ 4 + (-1 / 182250000) * alpha ^ 3 * c ^ 5 + (-1 / 364500000) * alpha ^ 3 * c ^ 6 + (1 / 729000000) * alpha ^ 4 + (1 / 121500000) * alpha ^ 4 * c + (1 / 48600000) * alpha ^ 4 * c ^ 2 + (1 / 36450000) * alpha ^ 4 * c ^ 3 + (1 / 48600000) * alpha ^ 4 * c ^ 4 + (1 / 121500000) * alpha ^ 4 * c ^ 5 + (1 / 729000000) * alpha ^ 4 * c ^ 6) * alpha_sq + ((-5549 / 2531250) + (-76 / 1265625) * c + (-1 / 101250) * c ^ 2 + (-1 / 3796875) * c ^ 3 + (-1 / 22781250) * c ^ 4 + (-5549 / 2531250) * alpha + (76 / 3796875) * alpha * c + (-1 / 101250) * alpha * c ^ 2 + (1 / 11390625) * alpha * c ^ 3 + (-1 / 22781250) * alpha * c ^ 4) * c_sq
theorem phase43_30 : ((r ^ 3 * thetaPlus) : ℂ) ^ 3 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 0 = ((71 / 1125) * c + (221 / 1125) * alpha) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 3000) + (1 / 1800) * c + (1 / 9000) * c ^ 2 + (-1 / 9000) * c ^ 3 + (-1 / 27000) * alpha + (-1 / 9000) * alpha * c + (-1 / 9000) * alpha * c ^ 2 + (-1 / 27000) * alpha * c ^ 3) * alpha_sq + ((1 / 3375) * c + (1 / 1125) * alpha) * c_sq
theorem phase43_31 : ((r ^ 3 * thetaPlus) : ℂ) ^ 3 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 1 = ((-73 / 150) + (-1 / 75) * c + (73 / 150) * alpha + (-1 / 225) * alpha * c) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 270000) + (1 / 67500) * c + (1 / 45000) * c ^ 2 + (1 / 67500) * c ^ 3 + (1 / 270000) * c ^ 4 + (1 / 135000) * alpha + (1 / 50625) * alpha * c + (1 / 67500) * alpha * c ^ 2 + (-1 / 405000) * alpha * c ^ 4 + (-1 / 810000) * alpha ^ 2 + (-1 / 202500) * alpha ^ 2 * c + (-1 / 135000) * alpha ^ 2 * c ^ 2 + (-1 / 202500) * alpha ^ 2 * c ^ 3 + (-1 / 810000) * alpha ^ 2 * c ^ 4) * alpha_sq + ((-37 / 16875) + (-1 / 16875) * c + (-1 / 101250) * c ^ 2 + (37 / 16875) * alpha + (-1 / 50625) * alpha * c + (1 / 101250) * alpha * c ^ 2) * c_sq
theorem phase43_32 : ((r ^ 3 * thetaPlus) : ℂ) ^ 3 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 2 = ((1 / 10) + (-1 / 30) * c + (-1 / 30) * alpha + (-1 / 30) * alpha * c) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-7 / 2700000) + (-29 / 8100000) * c + (-1 / 4050000) * c ^ 2 + (1 / 12150000) * c ^ 3 + (-11 / 24300000) * c ^ 4 + (1 / 4860000) * c ^ 5 + (7 / 8100000) * alpha + (19 / 8100000) * alpha * c + (1 / 486000) * alpha * c ^ 2 + (1 / 1350000) * alpha * c ^ 3 + (1 / 2700000) * alpha * c ^ 4 + (1 / 4860000) * alpha * c ^ 5 + (1 / 8100000) * alpha ^ 2 + (11 / 24300000) * alpha ^ 2 * c + (7 / 12150000) * alpha ^ 2 * c ^ 2 + (1 / 4050000) * alpha ^ 2 * c ^ 3 + (-1 / 24300000) * alpha ^ 2 * c ^ 4 + (-1 / 24300000) * alpha ^ 2 * c ^ 5 + (-1 / 24300000) * alpha ^ 3 + (-1 / 4860000) * alpha ^ 3 * c + (-1 / 2430000) * alpha ^ 3 * c ^ 2 + (-1 / 2430000) * alpha ^ 3 * c ^ 3 + (-1 / 4860000) * alpha ^ 3 * c ^ 4 + (-1 / 24300000) * alpha ^ 3 * c ^ 5) * alpha_sq + ((38 / 84375) + (-38 / 253125) * c + (1 / 506250) * c ^ 2 + (-1 / 1518750) * c ^ 3 + (-38 / 253125) * alpha + (-38 / 253125) * alpha * c + (-1 / 1518750) * alpha * c ^ 2 + (-1 / 1518750) * alpha * c ^ 3) * c_sq
theorem phase43_33 : ((r ^ 3 * thetaPlus) : ℂ) ^ 3 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 3 = (1) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-37 / 81000000) + (-1 / 1500000) * c + (-19 / 81000000) * c ^ 2 + (-1 / 4050000) * c ^ 3 + (-49 / 243000000) * c ^ 4 + (-1 / 121500000) * c ^ 5 + (-7 / 243000000) * c ^ 6 + (1 / 24300000) * alpha ^ 2 + (1 / 6750000) * alpha ^ 2 * c + (23 / 121500000) * alpha ^ 2 * c ^ 2 + (1 / 10125000) * alpha ^ 2 * c ^ 3 + (1 / 40500000) * alpha ^ 2 * c ^ 4 + (1 / 60750000) * alpha ^ 2 * c ^ 5 + (1 / 121500000) * alpha ^ 2 * c ^ 6 + (-1 / 729000000) * alpha ^ 4 + (-1 / 121500000) * alpha ^ 4 * c + (-1 / 48600000) * alpha ^ 4 * c ^ 2 + (-1 / 36450000) * alpha ^ 4 * c ^ 3 + (-1 / 48600000) * alpha ^ 4 * c ^ 4 + (-1 / 121500000) * alpha ^ 4 * c ^ 5 + (-1 / 729000000) * alpha ^ 4 * c ^ 6) * alpha_sq + ((5701 / 1265625) + (77 / 3796875) * c ^ 2 + (1 / 11390625) * c ^ 4) * c_sq
theorem phase43_34 : ((r ^ 3 * thetaPlus) : ℂ) ^ 3 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 4 = ((1 / 10) + (-1 / 30) * c + (1 / 30) * alpha + (1 / 30) * alpha * c) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-37 / 810000000) + (-1 / 19440000) * c + (-1 / 810000000) * c ^ 2 + (-41 / 2430000000) * c ^ 3 + (-29 / 2430000000) * c ^ 4 + (43 / 7290000000) * c ^ 5 + (-19 / 7290000000) * c ^ 6 + (7 / 7290000000) * c ^ 7 + (-37 / 2430000000) * alpha + (-91 / 2430000000) * alpha * c + (-73 / 2430000000) * alpha * c ^ 2 + (-13 / 810000000) * alpha * c ^ 3 + (-109 / 7290000000) * alpha * c ^ 4 + (-17 / 2430000000) * alpha * c ^ 5 + (-1 / 810000000) * alpha * c ^ 6 + (-7 / 7290000000) * alpha * c ^ 7 + (1 / 243000000) * alpha ^ 2 + (49 / 3645000000) * alpha ^ 2 * c + (17 / 1215000000) * alpha ^ 2 * c ^ 2 + (13 / 3645000000) * alpha ^ 2 * c ^ 3 + (-1 / 1215000000) * alpha ^ 2 * c ^ 4 + (1 / 1215000000) * alpha ^ 2 * c ^ 5 + (1 / 3645000000) * alpha ^ 2 * c ^ 6 + (-1 / 3645000000) * alpha ^ 2 * c ^ 7 + (1 / 729000000) * alpha ^ 3 + (23 / 3645000000) * alpha ^ 3 * c + (41 / 3645000000) * alpha ^ 3 * c ^ 2 + (7 / 729000000) * alpha ^ 3 * c ^ 3 + (1 / 243000000) * alpha ^ 3 * c ^ 4 + (1 / 729000000) * alpha ^ 3 * c ^ 5 + (1 / 1215000000) * alpha ^ 3 * c ^ 6 + (1 / 3645000000) * alpha ^ 3 * c ^ 7 + (-1 / 7290000000) * alpha ^ 4 + (-17 / 21870000000) * alpha ^ 4 * c + (-13 / 7290000000) * alpha ^ 4 * c ^ 2 + (-1 / 486000000) * alpha ^ 4 * c ^ 3 + (-1 / 874800000) * alpha ^ 4 * c ^ 4 + (-1 / 7290000000) * alpha ^ 4 * c ^ 5 + (1 / 7290000000) * alpha ^ 4 * c ^ 6 + (1 / 21870000000) * alpha ^ 4 * c ^ 7 + (-1 / 21870000000) * alpha ^ 5 + (-7 / 21870000000) * alpha ^ 5 * c + (-7 / 7290000000) * alpha ^ 5 * c ^ 2 + (-7 / 4374000000) * alpha ^ 5 * c ^ 3 + (-7 / 4374000000) * alpha ^ 5 * c ^ 4 + (-7 / 7290000000) * alpha ^ 5 * c ^ 5 + (-7 / 21870000000) * alpha ^ 5 * c ^ 6 + (-1 / 21870000000) * alpha ^ 5 * c ^ 7) * alpha_sq + ((5701 / 12656250) + (-5701 / 37968750) * c + (77 / 37968750) * c ^ 2 + (-77 / 113906250) * c ^ 3 + (1 / 113906250) * c ^ 4 + (-1 / 341718750) * c ^ 5 + (5701 / 37968750) * alpha + (5701 / 37968750) * alpha * c + (77 / 113906250) * alpha * c ^ 2 + (77 / 113906250) * alpha * c ^ 3 + (1 / 341718750) * alpha * c ^ 4 + (1 / 341718750) * alpha * c ^ 5) * c_sq
theorem phase43_40 : ((r ^ 3 * thetaPlus) : ℂ) ^ 4 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 0 = ((-5033 / 11250) + (146 / 5625) * c + (-5033 / 11250) * alpha + (-146 / 16875) * alpha * c) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((17 / 270000) + (1 / 13500) * c + (-1 / 27000) * c ^ 2 + (-1 / 22500) * c ^ 3 + (1 / 270000) * c ^ 4 + (-1 / 67500) * alpha + (-2 / 50625) * alpha * c + (-1 / 33750) * alpha * c ^ 2 + (1 / 202500) * alpha * c ^ 4 + (1 / 810000) * alpha ^ 2 + (1 / 202500) * alpha ^ 2 * c + (1 / 135000) * alpha ^ 2 * c ^ 2 + (1 / 202500) * alpha ^ 2 * c ^ 3 + (1 / 810000) * alpha ^ 2 * c ^ 4) * alpha_sq + ((-34 / 16875) + (2 / 16875) * c + (-1 / 101250) * c ^ 2 + (-34 / 16875) * alpha + (-2 / 50625) * alpha * c + (-1 / 101250) * alpha * c ^ 2) * c_sq
theorem phase43_41 : ((r ^ 3 * thetaPlus) : ℂ) ^ 4 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 1 = ((71 / 1125) * c + (221 / 1125) * alpha) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 300000) + (17 / 2700000) * c + (1 / 270000) * c ^ 2 + (17 / 12150000) * c ^ 3 + (1 / 4860000) * c ^ 4 + (-11 / 24300000) * c ^ 5 + (1 / 1620000) * alpha + (1 / 900000) * alpha * c + (-1 / 2430000) * alpha * c ^ 2 + (-7 / 4050000) * alpha * c ^ 3 + (-7 / 8100000) * alpha * c ^ 4 + (-1 / 24300000) * alpha * c ^ 5 + (-1 / 2700000) * alpha ^ 2 + (-11 / 8100000) * alpha ^ 2 * c + (-7 / 4050000) * alpha ^ 2 * c ^ 2 + (-1 / 1350000) * alpha ^ 2 * c ^ 3 + (1 / 8100000) * alpha ^ 2 * c ^ 4 + (1 / 8100000) * alpha ^ 2 * c ^ 5 + (1 / 24300000) * alpha ^ 3 + (1 / 4860000) * alpha ^ 3 * c + (1 / 2430000) * alpha ^ 3 * c ^ 2 + (1 / 2430000) * alpha ^ 3 * c ^ 3 + (1 / 4860000) * alpha ^ 3 * c ^ 4 + (1 / 24300000) * alpha ^ 3 * c ^ 5) * alpha_sq + ((8 / 28125) * c + (1 / 759375) * c ^ 3 + (224 / 253125) * alpha + (1 / 253125) * alpha * c ^ 2) * c_sq
theorem phase43_42 : ((r ^ 3 * thetaPlus) : ℂ) ^ 4 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 2 = ((-73 / 150) + (-1 / 75) * c + (73 / 150) * alpha + (-1 / 225) * alpha * c) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 16200000) + (1 / 8100000) * c + (103 / 243000000) * c ^ 2 + (17 / 60750000) * c ^ 3 + (77 / 729000000) * c ^ 4 + (29 / 364500000) * c ^ 5 + (11 / 729000000) * c ^ 6 + (7 / 40500000) * alpha + (1 / 2430000) * alpha * c + (31 / 121500000) * alpha * c ^ 2 + (1 / 91125000) * alpha * c ^ 3 + (1 / 40500000) * alpha * c ^ 4 + (1 / 60750000) * alpha * c ^ 5 + (-1 / 72900000) * alpha * c ^ 6 + (-1 / 60750000) * alpha ^ 2 + (-1 / 15187500) * alpha ^ 2 * c + (-19 / 182250000) * alpha ^ 2 * c ^ 2 + (-1 / 11390625) * alpha ^ 2 * c ^ 3 + (-1 / 20250000) * alpha ^ 2 * c ^ 4 + (-1 / 45562500) * alpha ^ 2 * c ^ 5 + (-1 / 182250000) * alpha ^ 2 * c ^ 6 + (-1 / 121500000) * alpha ^ 3 + (-7 / 182250000) * alpha ^ 3 * c + (-1 / 14580000) * alpha ^ 3 * c ^ 2 + (-1 / 18225000) * alpha ^ 3 * c ^ 3 + (-1 / 72900000) * alpha ^ 3 * c ^ 4 + (1 / 182250000) * alpha ^ 3 * c ^ 5 + (1 / 364500000) * alpha ^ 3 * c ^ 6 + (1 / 729000000) * alpha ^ 4 + (1 / 121500000) * alpha ^ 4 * c + (1 / 48600000) * alpha ^ 4 * c ^ 2 + (1 / 36450000) * alpha ^ 4 * c ^ 3 + (1 / 48600000) * alpha ^ 4 * c ^ 4 + (1 / 121500000) * alpha ^ 4 * c ^ 5 + (1 / 729000000) * alpha ^ 4 * c ^ 6) * alpha_sq + ((-5549 / 2531250) + (-76 / 1265625) * c + (-1 / 101250) * c ^ 2 + (-1 / 3796875) * c ^ 3 + (-1 / 22781250) * c ^ 4 + (5549 / 2531250) * alpha + (-76 / 3796875) * alpha * c + (1 / 101250) * alpha * c ^ 2 + (-1 / 11390625) * alpha * c ^ 3 + (1 / 22781250) * alpha * c ^ 4) * c_sq
theorem phase43_43 : ((r ^ 3 * thetaPlus) : ℂ) ^ 4 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 3 = ((1 / 10) + (-1 / 30) * c + (-1 / 30) * alpha + (-1 / 30) * alpha * c) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-37 / 810000000) + (-1 / 19440000) * c + (-1 / 810000000) * c ^ 2 + (-41 / 2430000000) * c ^ 3 + (-29 / 2430000000) * c ^ 4 + (43 / 7290000000) * c ^ 5 + (-19 / 7290000000) * c ^ 6 + (7 / 7290000000) * c ^ 7 + (37 / 2430000000) * alpha + (91 / 2430000000) * alpha * c + (73 / 2430000000) * alpha * c ^ 2 + (13 / 810000000) * alpha * c ^ 3 + (109 / 7290000000) * alpha * c ^ 4 + (17 / 2430000000) * alpha * c ^ 5 + (1 / 810000000) * alpha * c ^ 6 + (7 / 7290000000) * alpha * c ^ 7 + (1 / 243000000) * alpha ^ 2 + (49 / 3645000000) * alpha ^ 2 * c + (17 / 1215000000) * alpha ^ 2 * c ^ 2 + (13 / 3645000000) * alpha ^ 2 * c ^ 3 + (-1 / 1215000000) * alpha ^ 2 * c ^ 4 + (1 / 1215000000) * alpha ^ 2 * c ^ 5 + (1 / 3645000000) * alpha ^ 2 * c ^ 6 + (-1 / 3645000000) * alpha ^ 2 * c ^ 7 + (-1 / 729000000) * alpha ^ 3 + (-23 / 3645000000) * alpha ^ 3 * c + (-41 / 3645000000) * alpha ^ 3 * c ^ 2 + (-7 / 729000000) * alpha ^ 3 * c ^ 3 + (-1 / 243000000) * alpha ^ 3 * c ^ 4 + (-1 / 729000000) * alpha ^ 3 * c ^ 5 + (-1 / 1215000000) * alpha ^ 3 * c ^ 6 + (-1 / 3645000000) * alpha ^ 3 * c ^ 7 + (-1 / 7290000000) * alpha ^ 4 + (-17 / 21870000000) * alpha ^ 4 * c + (-13 / 7290000000) * alpha ^ 4 * c ^ 2 + (-1 / 486000000) * alpha ^ 4 * c ^ 3 + (-1 / 874800000) * alpha ^ 4 * c ^ 4 + (-1 / 7290000000) * alpha ^ 4 * c ^ 5 + (1 / 7290000000) * alpha ^ 4 * c ^ 6 + (1 / 21870000000) * alpha ^ 4 * c ^ 7 + (1 / 21870000000) * alpha ^ 5 + (7 / 21870000000) * alpha ^ 5 * c + (7 / 7290000000) * alpha ^ 5 * c ^ 2 + (7 / 4374000000) * alpha ^ 5 * c ^ 3 + (7 / 4374000000) * alpha ^ 5 * c ^ 4 + (7 / 7290000000) * alpha ^ 5 * c ^ 5 + (7 / 21870000000) * alpha ^ 5 * c ^ 6 + (1 / 21870000000) * alpha ^ 5 * c ^ 7) * alpha_sq + ((5701 / 12656250) + (-5701 / 37968750) * c + (77 / 37968750) * c ^ 2 + (-77 / 113906250) * c ^ 3 + (1 / 113906250) * c ^ 4 + (-1 / 341718750) * c ^ 5 + (-5701 / 37968750) * alpha + (-5701 / 37968750) * alpha * c + (-77 / 113906250) * alpha * c ^ 2 + (-77 / 113906250) * alpha * c ^ 3 + (-1 / 341718750) * alpha * c ^ 4 + (-1 / 341718750) * alpha * c ^ 5) * c_sq
theorem phase43_44 : ((r ^ 3 * thetaPlus) : ℂ) ^ 4 * star ((r ^ 3 * thetaPlus) : ℂ) ^ 4 = (1) := by
  rw [site43]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-7 / 972000000) + (-1 / 112500000) * c + (-67 / 18225000000) * c ^ 2 + (-7 / 1012500000) * c ^ 3 + (-151 / 36450000000) * c ^ 4 + (-7 / 9112500000) * c ^ 5 + (-47 / 32805000000) * c ^ 6 + (-1 / 82012500000) * c ^ 7 + (-17 / 131220000000) * c ^ 8 + (67 / 72900000000) * alpha ^ 2 + (1 / 337500000) * alpha ^ 2 * c + (7 / 2187000000) * alpha ^ 2 * c ^ 2 + (13 / 9112500000) * alpha ^ 2 * c ^ 3 + (91 / 109350000000) * alpha ^ 2 * c ^ 4 + (23 / 27337500000) * alpha ^ 2 * c ^ 5 + (1 / 3645000000) * alpha ^ 2 * c ^ 6 + (1 / 27337500000) * alpha ^ 2 * c ^ 7 + (1 / 24300000000) * alpha ^ 2 * c ^ 8 + (-13 / 218700000000) * alpha ^ 4 + (-1 / 3037500000) * alpha ^ 4 * c + (-121 / 164025000000) * alpha ^ 4 * c ^ 2 + (-23 / 27337500000) * alpha ^ 4 * c ^ 3 + (-11 / 21870000000) * alpha ^ 4 * c ^ 4 + (-13 / 82012500000) * alpha ^ 4 * c ^ 5 + (-1 / 18225000000) * alpha ^ 4 * c ^ 6 + (-1 / 27337500000) * alpha ^ 4 * c ^ 7 + (-7 / 656100000000) * alpha ^ 4 * c ^ 8 + (1 / 656100000000) * alpha ^ 6 + (1 / 82012500000) * alpha ^ 6 * c + (7 / 164025000000) * alpha ^ 6 * c ^ 2 + (7 / 82012500000) * alpha ^ 6 * c ^ 3 + (7 / 65610000000) * alpha ^ 6 * c ^ 4 + (7 / 82012500000) * alpha ^ 6 * c ^ 5 + (7 / 164025000000) * alpha ^ 6 * c ^ 6 + (1 / 82012500000) * alpha ^ 6 * c ^ 7 + (1 / 656100000000) * alpha ^ 6 * c ^ 8) * alpha_sq + ((427576 / 94921875) + (214 / 10546875) * c ^ 2 + (26 / 284765625) * c ^ 4 + (1 / 2562890625) * c ^ 6) * c_sq
noncomputable def z43 : Fin 43 → ℂ := Fin.snoc z42 (r ^ 3 * thetaPlus)
theorem v43_00 (t : ℂ) : (momentPoly 43 z43 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00]
  try simp only [phase43_00]
  try simp only [star_one, star_neg]
  ring
theorem v43_01 (t : ℂ) : (momentPoly 43 z43 0 1).eval t = ((1 / 10) * t + (-1 / 30) * c * t + (1 / 30) * alpha * t + (1 / 30) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01]
  try simp only [phase43_00, phase43_01]
  try simp only [star_one, star_neg]
  ring
theorem v43_02 (t : ℂ) : (momentPoly 43 z43 0 2).eval t = ((171 / 40) * t ^ 2 + (-2857 / 600) * t ^ 4 + (-1 / 75) * c * t ^ 4 + (131 / 24) * alpha * t ^ 2 + (-1189 / 200) * alpha * t ^ 4 + (1 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02]
  try simp only [phase43_00, phase43_01, phase43_02]
  try simp only [star_one, star_neg]
  ring
theorem v43_03 (t : ℂ) : (momentPoly 43 z43 0 3).eval t = ((-71 / 200) * t ^ 3 + (71 / 200) * t ^ 5 + (-413 / 200) * c * t ^ 3 + (413 / 200) * c * t ^ 5 + (71 / 1125) * c * t ^ 9 + (413 / 200) * alpha * t ^ 3 + (-413 / 200) * alpha * t ^ 5 + (-221 / 1125) * alpha * t ^ 9 + (-71 / 600) * alpha * c * t ^ 3 + (71 / 600) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_03]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03]
  try simp only [star_one, star_neg]
  linear_combination ((131 / 240) * t ^ 3 + (-131 / 240) * t ^ 5 + (131 / 240) * c * t ^ 3 + (-131 / 240) * c * t ^ 5) * alpha_sq
theorem v43_04 (t : ℂ) : (momentPoly 43 z43 0 4).eval t = ((-1533069 / 8000) * t ^ 4 + (1674397 / 4000) * t ^ 6 + (-3804891 / 16000) * t ^ 8 + (173441 / 12000) * t ^ 10 + (-2923727 / 720000) * t ^ 16 + (-292 / 375) * c * t ^ 6 + (292 / 375) * c * t ^ 8 + (146 / 5625) * c * t ^ 16 + (103681 / 960) * alpha * t ^ 4 + (-2933081 / 12000) * alpha * t ^ 6 + (7316399 / 48000) * alpha * t ^ 8 + (-6145 / 288) * alpha * t ^ 10 + (1387579 / 240000) * alpha * t ^ 16 + (-121 / 375) * alpha * c * t ^ 6 + (121 / 375) * alpha * c * t ^ 8 + (146 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_03, v42_04]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04]
  try simp only [star_one, star_neg]
  linear_combination ((-9563 / 600) * t ^ 6 + (9563 / 600) * t ^ 8 + (131 / 900) * c * t ^ 6 + (-131 / 900) * c * t ^ 8) * alpha_sq
theorem v43_10 (t : ℂ) : (momentPoly 43 z43 1 0).eval t = ((1 / 10) * t + (-1 / 30) * c * t + (-1 / 30) * alpha * t + (-1 / 30) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_10]
  try simp only [phase43_00, phase43_10]
  try simp only [star_one, star_neg]
  ring
theorem v43_11 (t : ℂ) : (momentPoly 43 z43 1 1).eval t = (43 + (-42) * t ^ 2) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_10, v42_11]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11]
  try simp only [star_one, star_neg]
  ring
theorem v43_12 (t : ℂ) : (momentPoly 43 z43 1 2).eval t = ((17 / 2) * t + (-557 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-17 / 6) * c * t + (961 / 300) * c * t ^ 3 + (-121 / 300) * c * t ^ 5 + (17 / 6) * alpha * t + (-719 / 300) * alpha * t ^ 3 + (-121 / 300) * alpha * t ^ 5 + (17 / 6) * alpha * c * t + (-703 / 225) * alpha * c * t ^ 3 + (73 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_10, v42_11, v42_12]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12]
  try simp only [star_one, star_neg]
  linear_combination ((-131 / 720) * t ^ 3 + (131 / 720) * t ^ 5 + (-131 / 720) * c * t ^ 3 + (131 / 720) * c * t ^ 5) * alpha_sq
theorem v43_13 (t : ℂ) : (momentPoly 43 z43 1 3).eval t = ((10773 / 20) * t ^ 2 + (-670639 / 600) * t ^ 4 + (14358 / 25) * t ^ 6 + (171 / 40) * t ^ 10 + (-127 / 75) * c * t ^ 4 + (42 / 25) * c * t ^ 6 + (2751 / 4) * alpha * t ^ 2 + (-282003 / 200) * alpha * t ^ 4 + (17908 / 25) * alpha * t ^ 6 + (131 / 24) * alpha * t ^ 10 + (127 / 225) * alpha * c * t ^ 4 + (-14 / 25) * alpha * c * t ^ 6) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_03, v42_10, v42_11, v42_12, v42_13]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13]
  try simp only [star_one, star_neg]
  ring
theorem v43_14 (t : ℂ) : (momentPoly 43 z43 1 4).eval t = ((-5893 / 100) * t ^ 3 + (4313603 / 40000) * t ^ 5 + (-2404409 / 60000) * t ^ 7 + (-1883281 / 240000) * t ^ 9 + (-209101 / 180000) * t ^ 11 + (123901 / 720000) * t ^ 17 + (-34279 / 100) * c * t ^ 3 + (27725249 / 40000) * c * t ^ 5 + (-21886547 / 60000) * c * t ^ 7 + (21466991 / 720000) * c * t ^ 9 + (-2874863 / 180000) * c * t ^ 11 + (470783 / 720000) * c * t ^ 17 + (34279 / 100) * alpha * t ^ 3 + (-79050653 / 120000) * alpha * t ^ 5 + (17761453 / 60000) * alpha * t ^ 7 + (-10115729 / 720000) * alpha * t ^ 9 + (5965297 / 180000) * alpha * t ^ 11 + (470783 / 720000) * alpha * t ^ 17 + (-5893 / 300) * alpha * c * t ^ 3 + (14947991 / 360000) * alpha * c * t ^ 5 + (-4411591 / 180000) * alpha * c * t ^ 7 + (1883281 / 720000) * alpha * c * t ^ 9 + (38701 / 540000) * alpha * c * t ^ 11 + (-123901 / 2160000) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_03, v42_04, v42_10, v42_11, v42_12, v42_13, v42_14]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14]
  try simp only [star_one, star_neg]
  linear_combination ((10873 / 120) * t ^ 3 + (-1749787 / 9600) * t ^ 5 + (1361281 / 14400) * t ^ 7 + (-238087 / 57600) * t ^ 9 + (12433 / 8640) * t ^ 11 + (-1229 / 6912) * t ^ 17 + (10873 / 120) * c * t ^ 3 + (-1749787 / 9600) * c * t ^ 5 + (1361281 / 14400) * c * t ^ 7 + (-238087 / 57600) * c * t ^ 9 + (12433 / 8640) * c * t ^ 11 + (-1229 / 6912) * c * t ^ 17) * alpha_sq
theorem v43_20 (t : ℂ) : (momentPoly 43 z43 2 0).eval t = ((171 / 40) * t ^ 2 + (-2857 / 600) * t ^ 4 + (-1 / 75) * c * t ^ 4 + (-131 / 24) * alpha * t ^ 2 + (1189 / 200) * alpha * t ^ 4 + (-1 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_10, v42_20]
  try simp only [phase43_00, phase43_10, phase43_20]
  try simp only [star_one, star_neg]
  ring
theorem v43_21 (t : ℂ) : (momentPoly 43 z43 2 1).eval t = ((17 / 2) * t + (-557 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-17 / 6) * c * t + (961 / 300) * c * t ^ 3 + (-121 / 300) * c * t ^ 5 + (-17 / 6) * alpha * t + (719 / 300) * alpha * t ^ 3 + (121 / 300) * alpha * t ^ 5 + (-17 / 6) * alpha * c * t + (703 / 225) * alpha * c * t ^ 3 + (-73 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_10, v42_11, v42_20, v42_21]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21]
  try simp only [star_one, star_neg]
  linear_combination ((-131 / 720) * t ^ 3 + (131 / 720) * t ^ 5 + (-131 / 720) * c * t ^ 3 + (131 / 720) * c * t ^ 5) * alpha_sq
theorem v43_22 (t : ℂ) : (momentPoly 43 z43 2 2).eval t = (3655 + (-7056) * t ^ 2 + (4060387 / 1200) * t ^ 4 + (-67411 / 1000) * t ^ 6 + (514531 / 6000) * t ^ 8 + (71 / 2250) * c * t ^ 6 + (-71 / 2250) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_10, v42_11, v42_12, v42_20, v42_21, v42_22]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22]
  try simp only [star_one, star_neg]
  linear_combination ((9563 / 1800) * t ^ 6 + (-9563 / 1800) * t ^ 8 + (-131 / 2700) * c * t ^ 6 + (131 / 2700) * c * t ^ 8) * alpha_sq
theorem v43_23 (t : ℂ) : (momentPoly 43 z43 2 3).eval t = ((10711 / 10) * t + (-46231 / 25) * t ^ 3 + (6446281 / 12000) * t ^ 5 + (438813 / 2000) * t ^ 7 + (78787 / 4000) * t ^ 9 + (-11431 / 9000) * t ^ 11 + (28951 / 9000) * t ^ 13 + (-10711 / 30) * c * t + (79763 / 100) * c * t ^ 3 + (-2145609 / 4000) * c * t ^ 5 + (609187 / 6000) * c * t ^ 7 + (-78787 / 12000) * c * t ^ 9 + (16147 / 15000) * c * t ^ 11 + (-1349 / 5000) * c * t ^ 13 + (10711 / 30) * alpha * t + (-59677 / 100) * alpha * t ^ 3 + (1683947 / 12000) * alpha * t ^ 5 + (552413 / 6000) * alpha * t ^ 7 + (78787 / 12000) * alpha * t ^ 9 + (-497 / 15000) * alpha * t ^ 11 + (4199 / 5000) * alpha * t ^ 13 + (10711 / 30) * alpha * c * t + (-58349 / 75) * alpha * c * t ^ 3 + (17916041 / 36000) * alpha * c * t ^ 5 + (-495587 / 6000) * alpha * c * t ^ 7 + (78787 / 12000) * alpha * c * t ^ 9 + (-26821 / 27000) * alpha * c * t ^ 11 + (9301 / 27000) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_03, v42_10, v42_11, v42_12, v42_13, v42_20, v42_21, v42_22, v42_23]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23]
  try simp only [star_one, star_neg]
  linear_combination ((-10873 / 240) * t ^ 3 + (64321 / 720) * t ^ 5 + (-131 / 3) * t ^ 7 + (9563 / 13500) * t ^ 11 + (-28951 / 27000) * t ^ 13 + (-10873 / 240) * c * t ^ 3 + (64321 / 720) * c * t ^ 5 + (-131 / 3) * c * t ^ 7 + (-131 / 360) * c * t ^ 11) * alpha_sq
theorem v43_24 (t : ℂ) : (momentPoly 43 z43 2 4).eval t = (89433 * t ^ 2 + (-161678221 / 600) * t ^ 4 + (128055246389 / 480000) * t ^ 6 + (-203070107491 / 2400000) * t ^ 8 + (-635614367 / 1600000) * t ^ 10 + (-28929019433 / 14400000) * t ^ 12 + (999070469 / 3600000) * t ^ 14 + (330065903 / 4800000) * t ^ 18 + (-379527191 / 4800000) * t ^ 20 + (-21253 / 75) * c * t ^ 4 + (13888 / 25) * c * t ^ 6 + (-60006901 / 225000) * c * t ^ 8 + (-473099 / 112500) * c * t ^ 10 + (-202373 / 225000) * c * t ^ 12 + (-40264 / 84375) * c * t ^ 14 + (21316 / 84375) * c * t ^ 18 + (-2 / 15) * c * t ^ 20 + (342565 / 3) * alpha * t ^ 2 + (-68237817 / 200) * alpha * t ^ 4 + (32189841727 / 96000) * alpha * t ^ 6 + (-764994320687 / 7200000) * alpha * t ^ 8 + (4619830823 / 14400000) * alpha * t ^ 10 + (-36233878207 / 14400000) * alpha * t ^ 12 + (1553662633 / 10800000) * alpha * t ^ 14 + (1553662633 / 43200000) * alpha * t ^ 18 + (-1977576041 / 43200000) * alpha * t ^ 20 + (21253 / 225) * alpha * c * t ^ 4 + (-13888 / 75) * alpha * c * t ^ 6 + (13446377 / 150000) * alpha * c * t ^ 8 + (-6377 / 75000) * alpha * c * t ^ 10 + (299197 / 300000) * alpha * c * t ^ 12 + (16519 / 75000) * alpha * c * t ^ 14 + (-8833 / 84375) * alpha * c * t ^ 18 + (26797 / 540000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_03, v42_04, v42_10, v42_11, v42_12, v42_13, v42_14, v42_20, v42_21, v42_22, v42_23, v42_24]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24]
  try simp only [star_one, star_neg]
  linear_combination ((7568713 / 144000) * t ^ 8 + (-7568713 / 72000) * t ^ 10 + (17380351 / 288000) * t ^ 12 + (-89717 / 8640) * t ^ 14 + (-659323 / 270000) * t ^ 18 + (21763793 / 4320000) * t ^ 20 + (-103681 / 216000) * c * t ^ 8 + (103681 / 108000) * c * t ^ 10 + (-238087 / 432000) * c * t ^ 12 + (1229 / 12960) * c * t ^ 14 + (-9563 / 202500) * c * t ^ 18 + (50797 / 2160000) * c * t ^ 20) * alpha_sq
theorem v43_30 (t : ℂ) : (momentPoly 43 z43 3 0).eval t = ((-71 / 200) * t ^ 3 + (71 / 200) * t ^ 5 + (-413 / 200) * c * t ^ 3 + (413 / 200) * c * t ^ 5 + (71 / 1125) * c * t ^ 9 + (-413 / 200) * alpha * t ^ 3 + (413 / 200) * alpha * t ^ 5 + (221 / 1125) * alpha * t ^ 9 + (71 / 600) * alpha * c * t ^ 3 + (-71 / 600) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_10, v42_20, v42_30]
  try simp only [phase43_00, phase43_10, phase43_20, phase43_30]
  try simp only [star_one, star_neg]
  linear_combination ((131 / 240) * t ^ 3 + (-131 / 240) * t ^ 5 + (131 / 240) * c * t ^ 3 + (-131 / 240) * c * t ^ 5) * alpha_sq
theorem v43_31 (t : ℂ) : (momentPoly 43 z43 3 1).eval t = ((10773 / 20) * t ^ 2 + (-670639 / 600) * t ^ 4 + (14358 / 25) * t ^ 6 + (171 / 40) * t ^ 10 + (-127 / 75) * c * t ^ 4 + (42 / 25) * c * t ^ 6 + (-2751 / 4) * alpha * t ^ 2 + (282003 / 200) * alpha * t ^ 4 + (-17908 / 25) * alpha * t ^ 6 + (-131 / 24) * alpha * t ^ 10 + (-127 / 225) * alpha * c * t ^ 4 + (14 / 25) * alpha * c * t ^ 6) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_10, v42_11, v42_20, v42_21, v42_30, v42_31]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21, phase43_30, phase43_31]
  try simp only [star_one, star_neg]
  ring
theorem v43_32 (t : ℂ) : (momentPoly 43 z43 3 2).eval t = ((10711 / 10) * t + (-46231 / 25) * t ^ 3 + (6446281 / 12000) * t ^ 5 + (438813 / 2000) * t ^ 7 + (78787 / 4000) * t ^ 9 + (-11431 / 9000) * t ^ 11 + (28951 / 9000) * t ^ 13 + (-10711 / 30) * c * t + (79763 / 100) * c * t ^ 3 + (-2145609 / 4000) * c * t ^ 5 + (609187 / 6000) * c * t ^ 7 + (-78787 / 12000) * c * t ^ 9 + (16147 / 15000) * c * t ^ 11 + (-1349 / 5000) * c * t ^ 13 + (-10711 / 30) * alpha * t + (59677 / 100) * alpha * t ^ 3 + (-1683947 / 12000) * alpha * t ^ 5 + (-552413 / 6000) * alpha * t ^ 7 + (-78787 / 12000) * alpha * t ^ 9 + (497 / 15000) * alpha * t ^ 11 + (-4199 / 5000) * alpha * t ^ 13 + (-10711 / 30) * alpha * c * t + (58349 / 75) * alpha * c * t ^ 3 + (-17916041 / 36000) * alpha * c * t ^ 5 + (495587 / 6000) * alpha * c * t ^ 7 + (-78787 / 12000) * alpha * c * t ^ 9 + (26821 / 27000) * alpha * c * t ^ 11 + (-9301 / 27000) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_10, v42_11, v42_12, v42_20, v42_21, v42_22, v42_30, v42_31, v42_32]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22, phase43_30, phase43_31, phase43_32]
  try simp only [star_one, star_neg]
  linear_combination ((-10873 / 240) * t ^ 3 + (64321 / 720) * t ^ 5 + (-131 / 3) * t ^ 7 + (9563 / 13500) * t ^ 11 + (-28951 / 27000) * t ^ 13 + (-10873 / 240) * c * t ^ 3 + (64321 / 720) * c * t ^ 5 + (-131 / 3) * c * t ^ 7 + (-131 / 360) * c * t ^ 11) * alpha_sq
theorem v43_33 (t : ℂ) : (momentPoly 43 z43 3 3).eval t = (460573 + (-1317960) * t ^ 2 + (499427601 / 400) * t ^ 4 + (-416207187 / 1000) * t ^ 6 + (4445963 / 80) * t ^ 8 + (-6089211 / 200) * t ^ 10 + (28387 / 200) * t ^ 12 + (-202233 / 1000) * t ^ 14 + (-42) * t ^ 18 + (4402 / 375) * c * t ^ 6 + (-3479 / 150) * c * t ^ 8 + (284 / 25) * c * t ^ 10 + (71 / 750) * c * t ^ 14) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_03, v42_10, v42_11, v42_12, v42_13, v42_20, v42_21, v42_22, v42_23, v42_30, v42_31, v42_32, v42_33]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23, phase43_30, phase43_31, phase43_32, phase43_33]
  try simp only [star_one, star_neg]
  linear_combination ((296453 / 150) * t ^ 6 + (-468587 / 120) * t ^ 8 + (9563 / 5) * t ^ 10 + (9563 / 600) * t ^ 14 + (-4061 / 225) * c * t ^ 6 + (6419 / 180) * c * t ^ 8 + (-262 / 15) * c * t ^ 10 + (-131 / 900) * c * t ^ 14) * alpha_sq
theorem v43_34 (t : ℂ) : (momentPoly 43 z43 3 4).eval t = ((1778533 / 10) * t + (-11376168 / 25) * t ^ 3 + (638417321 / 2000) * t ^ 5 + (365336339 / 100000) * t ^ 7 + (-3506485867 / 100000) * t ^ 9 + (-444802779 / 40000) * t ^ 11 + (1775013851 / 900000) * t ^ 13 + (-1223619869 / 900000) * t ^ 15 + (-52617227 / 720000) * t ^ 17 + (61535689 / 5400000) * t ^ 19 + (-18844871 / 600000) * t ^ 21 + (-271609 / 86400) * t ^ 25 + (-1778533 / 30) * c * t + (4906866 / 25) * c * t ^ 3 + (-473203207 / 2000) * c * t ^ 5 + (49499184293 / 400000) * c * t ^ 7 + (-32161151237 / 1200000) * c * t ^ 9 + (1563432001 / 480000) * c * t ^ 11 + (-27769380751 / 36000000) * c * t ^ 13 + (1666879453 / 9000000) * c * t ^ 15 + (-230010109 / 18000000) * c * t ^ 17 + (1159845053 / 108000000) * c * t ^ 19 + (-31377131 / 7200000) * c * t ^ 21 + (-12314311 / 54000000) * c * t ^ 25 + (1778533 / 30) * alpha * t + (-3671214 / 25) * alpha * t ^ 3 + (184579487 / 2000) * alpha * t ^ 5 + (17772006479 / 1200000) * alpha * t ^ 7 + (-19199206837 / 1200000) * alpha * t ^ 9 + (-1671126719 / 480000) * alpha * t ^ 11 + (11780096249 / 36000000) * alpha * t ^ 13 + (-3007315847 / 9000000) * alpha * t ^ 15 + (-715946959 / 18000000) * alpha * t ^ 17 + (-320972947 / 108000000) * alpha * t ^ 19 + (-31377131 / 7200000) * alpha * t ^ 21 + (-38330461 / 54000000) * alpha * t ^ 25 + (1778533 / 30) * alpha * c * t + (-4786024 / 25) * alpha * c * t ^ 3 + (1334930761 / 6000) * alpha * c * t ^ 5 + (-11015574313 / 100000) * alpha * c * t ^ 7 + (6746971967 / 300000) * alpha * c * t ^ 9 + (-382081061 / 120000) * alpha * c * t ^ 11 + (338861629 / 450000) * alpha * c * t ^ 13 + (-636908581 / 2700000) * alpha * c * t ^ 15 + (16904177 / 2160000) * alpha * c * t ^ 17 + (-288692989 / 16200000) * alpha * c * t ^ 19 + (18844871 / 1800000) * alpha * c * t ^ 21 + (87259 / 259200) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_03, v42_04, v42_10, v42_11, v42_12, v42_13, v42_14, v42_20, v42_21, v42_22, v42_23, v42_24, v42_30, v42_31, v42_32, v42_33, v42_34]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24, phase43_30, phase43_31, phase43_32, phase43_33, phase43_34]
  try simp only [star_one, star_neg]
  linear_combination ((-111481 / 10) * t ^ 3 + (7811923 / 240) * t ^ 5 + (-29991779647 / 960000) * t ^ 7 + (3079139647 / 320000) * t ^ 9 + (208837999 / 384000) * t ^ 11 + (-2806139023 / 3456000) * t ^ 13 + (1985506823 / 4320000) * t ^ 15 + (52617227 / 2160000) * t ^ 17 + (-158809427 / 51840000) * t ^ 19 + (21351323 / 5760000) * t ^ 21 + (271609 / 259200) * t ^ 25 + (-111481 / 10) * c * t ^ 3 + (7811923 / 240) * c * t ^ 5 + (-29991779647 / 960000) * c * t ^ 7 + (3079139647 / 320000) * c * t ^ 9 + (5022959 / 384000) * c * t ^ 11 + (1247409143 / 5760000) * c * t ^ 13 + (-18207323 / 1440000) * c * t ^ 15 + (-18207323 / 5760000) * c * t ^ 19 + (21351323 / 5760000) * c * t ^ 21) * alpha_sq
theorem v43_40 (t : ℂ) : (momentPoly 43 z43 4 0).eval t = ((-1533069 / 8000) * t ^ 4 + (1674397 / 4000) * t ^ 6 + (-3804891 / 16000) * t ^ 8 + (173441 / 12000) * t ^ 10 + (-2923727 / 720000) * t ^ 16 + (-292 / 375) * c * t ^ 6 + (292 / 375) * c * t ^ 8 + (146 / 5625) * c * t ^ 16 + (-103681 / 960) * alpha * t ^ 4 + (2933081 / 12000) * alpha * t ^ 6 + (-7316399 / 48000) * alpha * t ^ 8 + (6145 / 288) * alpha * t ^ 10 + (-1387579 / 240000) * alpha * t ^ 16 + (121 / 375) * alpha * c * t ^ 6 + (-121 / 375) * alpha * c * t ^ 8 + (-146 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_10, v42_20, v42_30, v42_40]
  try simp only [phase43_00, phase43_10, phase43_20, phase43_30, phase43_40]
  try simp only [star_one, star_neg]
  linear_combination ((-9563 / 600) * t ^ 6 + (9563 / 600) * t ^ 8 + (131 / 900) * c * t ^ 6 + (-131 / 900) * c * t ^ 8) * alpha_sq
theorem v43_41 (t : ℂ) : (momentPoly 43 z43 4 1).eval t = ((-5893 / 100) * t ^ 3 + (4313603 / 40000) * t ^ 5 + (-2404409 / 60000) * t ^ 7 + (-1883281 / 240000) * t ^ 9 + (-209101 / 180000) * t ^ 11 + (123901 / 720000) * t ^ 17 + (-34279 / 100) * c * t ^ 3 + (27725249 / 40000) * c * t ^ 5 + (-21886547 / 60000) * c * t ^ 7 + (21466991 / 720000) * c * t ^ 9 + (-2874863 / 180000) * c * t ^ 11 + (470783 / 720000) * c * t ^ 17 + (-34279 / 100) * alpha * t ^ 3 + (79050653 / 120000) * alpha * t ^ 5 + (-17761453 / 60000) * alpha * t ^ 7 + (10115729 / 720000) * alpha * t ^ 9 + (-5965297 / 180000) * alpha * t ^ 11 + (-470783 / 720000) * alpha * t ^ 17 + (5893 / 300) * alpha * c * t ^ 3 + (-14947991 / 360000) * alpha * c * t ^ 5 + (4411591 / 180000) * alpha * c * t ^ 7 + (-1883281 / 720000) * alpha * c * t ^ 9 + (-38701 / 540000) * alpha * c * t ^ 11 + (123901 / 2160000) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_10, v42_11, v42_20, v42_21, v42_30, v42_31, v42_40, v42_41]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21, phase43_30, phase43_31, phase43_40, phase43_41]
  try simp only [star_one, star_neg]
  linear_combination ((10873 / 120) * t ^ 3 + (-1749787 / 9600) * t ^ 5 + (1361281 / 14400) * t ^ 7 + (-238087 / 57600) * t ^ 9 + (12433 / 8640) * t ^ 11 + (-1229 / 6912) * t ^ 17 + (10873 / 120) * c * t ^ 3 + (-1749787 / 9600) * c * t ^ 5 + (1361281 / 14400) * c * t ^ 7 + (-238087 / 57600) * c * t ^ 9 + (12433 / 8640) * c * t ^ 11 + (-1229 / 6912) * c * t ^ 17) * alpha_sq
theorem v43_42 (t : ℂ) : (momentPoly 43 z43 4 2).eval t = (89433 * t ^ 2 + (-161678221 / 600) * t ^ 4 + (128055246389 / 480000) * t ^ 6 + (-203070107491 / 2400000) * t ^ 8 + (-635614367 / 1600000) * t ^ 10 + (-28929019433 / 14400000) * t ^ 12 + (999070469 / 3600000) * t ^ 14 + (330065903 / 4800000) * t ^ 18 + (-379527191 / 4800000) * t ^ 20 + (-21253 / 75) * c * t ^ 4 + (13888 / 25) * c * t ^ 6 + (-60006901 / 225000) * c * t ^ 8 + (-473099 / 112500) * c * t ^ 10 + (-202373 / 225000) * c * t ^ 12 + (-40264 / 84375) * c * t ^ 14 + (21316 / 84375) * c * t ^ 18 + (-2 / 15) * c * t ^ 20 + (-342565 / 3) * alpha * t ^ 2 + (68237817 / 200) * alpha * t ^ 4 + (-32189841727 / 96000) * alpha * t ^ 6 + (764994320687 / 7200000) * alpha * t ^ 8 + (-4619830823 / 14400000) * alpha * t ^ 10 + (36233878207 / 14400000) * alpha * t ^ 12 + (-1553662633 / 10800000) * alpha * t ^ 14 + (-1553662633 / 43200000) * alpha * t ^ 18 + (1977576041 / 43200000) * alpha * t ^ 20 + (-21253 / 225) * alpha * c * t ^ 4 + (13888 / 75) * alpha * c * t ^ 6 + (-13446377 / 150000) * alpha * c * t ^ 8 + (6377 / 75000) * alpha * c * t ^ 10 + (-299197 / 300000) * alpha * c * t ^ 12 + (-16519 / 75000) * alpha * c * t ^ 14 + (8833 / 84375) * alpha * c * t ^ 18 + (-26797 / 540000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_10, v42_11, v42_12, v42_20, v42_21, v42_22, v42_30, v42_31, v42_32, v42_40, v42_41, v42_42]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22, phase43_30, phase43_31, phase43_32, phase43_40, phase43_41, phase43_42]
  try simp only [star_one, star_neg]
  linear_combination ((7568713 / 144000) * t ^ 8 + (-7568713 / 72000) * t ^ 10 + (17380351 / 288000) * t ^ 12 + (-89717 / 8640) * t ^ 14 + (-659323 / 270000) * t ^ 18 + (21763793 / 4320000) * t ^ 20 + (-103681 / 216000) * c * t ^ 8 + (103681 / 108000) * c * t ^ 10 + (-238087 / 432000) * c * t ^ 12 + (1229 / 12960) * c * t ^ 14 + (-9563 / 202500) * c * t ^ 18 + (50797 / 2160000) * c * t ^ 20) * alpha_sq
theorem v43_43 (t : ℂ) : (momentPoly 43 z43 4 3).eval t = ((1778533 / 10) * t + (-11376168 / 25) * t ^ 3 + (638417321 / 2000) * t ^ 5 + (365336339 / 100000) * t ^ 7 + (-3506485867 / 100000) * t ^ 9 + (-444802779 / 40000) * t ^ 11 + (1775013851 / 900000) * t ^ 13 + (-1223619869 / 900000) * t ^ 15 + (-52617227 / 720000) * t ^ 17 + (61535689 / 5400000) * t ^ 19 + (-18844871 / 600000) * t ^ 21 + (-271609 / 86400) * t ^ 25 + (-1778533 / 30) * c * t + (4906866 / 25) * c * t ^ 3 + (-473203207 / 2000) * c * t ^ 5 + (49499184293 / 400000) * c * t ^ 7 + (-32161151237 / 1200000) * c * t ^ 9 + (1563432001 / 480000) * c * t ^ 11 + (-27769380751 / 36000000) * c * t ^ 13 + (1666879453 / 9000000) * c * t ^ 15 + (-230010109 / 18000000) * c * t ^ 17 + (1159845053 / 108000000) * c * t ^ 19 + (-31377131 / 7200000) * c * t ^ 21 + (-12314311 / 54000000) * c * t ^ 25 + (-1778533 / 30) * alpha * t + (3671214 / 25) * alpha * t ^ 3 + (-184579487 / 2000) * alpha * t ^ 5 + (-17772006479 / 1200000) * alpha * t ^ 7 + (19199206837 / 1200000) * alpha * t ^ 9 + (1671126719 / 480000) * alpha * t ^ 11 + (-11780096249 / 36000000) * alpha * t ^ 13 + (3007315847 / 9000000) * alpha * t ^ 15 + (715946959 / 18000000) * alpha * t ^ 17 + (320972947 / 108000000) * alpha * t ^ 19 + (31377131 / 7200000) * alpha * t ^ 21 + (38330461 / 54000000) * alpha * t ^ 25 + (-1778533 / 30) * alpha * c * t + (4786024 / 25) * alpha * c * t ^ 3 + (-1334930761 / 6000) * alpha * c * t ^ 5 + (11015574313 / 100000) * alpha * c * t ^ 7 + (-6746971967 / 300000) * alpha * c * t ^ 9 + (382081061 / 120000) * alpha * c * t ^ 11 + (-338861629 / 450000) * alpha * c * t ^ 13 + (636908581 / 2700000) * alpha * c * t ^ 15 + (-16904177 / 2160000) * alpha * c * t ^ 17 + (288692989 / 16200000) * alpha * c * t ^ 19 + (-18844871 / 1800000) * alpha * c * t ^ 21 + (-87259 / 259200) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_03, v42_10, v42_11, v42_12, v42_13, v42_20, v42_21, v42_22, v42_23, v42_30, v42_31, v42_32, v42_33, v42_40, v42_41, v42_42, v42_43]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23, phase43_30, phase43_31, phase43_32, phase43_33, phase43_40, phase43_41, phase43_42, phase43_43]
  try simp only [star_one, star_neg]
  linear_combination ((-111481 / 10) * t ^ 3 + (7811923 / 240) * t ^ 5 + (-29991779647 / 960000) * t ^ 7 + (3079139647 / 320000) * t ^ 9 + (208837999 / 384000) * t ^ 11 + (-2806139023 / 3456000) * t ^ 13 + (1985506823 / 4320000) * t ^ 15 + (52617227 / 2160000) * t ^ 17 + (-158809427 / 51840000) * t ^ 19 + (21351323 / 5760000) * t ^ 21 + (271609 / 259200) * t ^ 25 + (-111481 / 10) * c * t ^ 3 + (7811923 / 240) * c * t ^ 5 + (-29991779647 / 960000) * c * t ^ 7 + (3079139647 / 320000) * c * t ^ 9 + (5022959 / 384000) * c * t ^ 11 + (1247409143 / 5760000) * c * t ^ 13 + (-18207323 / 1440000) * c * t ^ 15 + (-18207323 / 5760000) * c * t ^ 19 + (21351323 / 5760000) * c * t ^ 21) * alpha_sq
theorem v43_44 (t : ℂ) : (momentPoly 43 z43 4 4).eval t = (76476919 + (-288334032) * t ^ 2 + (40469877229 / 100) * t ^ 4 + (-129258732747 / 500) * t ^ 6 + (1329242049726409 / 16000000) * t ^ 8 + (-314257462140551 / 12000000) * t ^ 10 + (408110435337353 / 48000000) * t ^ 12 + (12617405491583 / 72000000) * t ^ 14 + (2998544608073 / 23040000) * t ^ 16 + (-3529731904417 / 72000000) * t ^ 18 + (69604439185781 / 2160000000) * t ^ 20 + (-3844026991327 / 360000000) * t ^ 22 + (8931604128197 / 1440000000) * t ^ 24 + (-200389123183 / 1080000000) * t ^ 26 + (213030516677 / 2880000000) * t ^ 32 + (479463 / 125) * c * t ^ 6 + (-2526464 / 225) * c * t ^ 8 + (16265221123 / 1500000) * c * t ^ 10 + (-1724421123 / 500000) * c * t ^ 12 + (158101831 / 1800000) * c * t ^ 14 + (-206834089 / 3000000) * c * t ^ 16 + (-15235451 / 750000) * c * t ^ 18 + (-73262143 / 16875000) * c * t ^ 20 + (486598993 / 135000000) * c * t ^ 22 + (110117243 / 135000000) * c * t ^ 24 + (-9044773 / 25312500) * c * t ^ 26 + (9044773 / 101250000) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_03, v42_04, v42_10, v42_11, v42_12, v42_13, v42_14, v42_20, v42_21, v42_22, v42_23, v42_24, v42_30, v42_31, v42_32, v42_33, v42_34, v42_40, v42_41, v42_42, v42_43, v42_44]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24, phase43_30, phase43_31, phase43_32, phase43_33, phase43_34, phase43_40, phase43_41, phase43_42, phase43_43, phase43_44]
  try simp only [star_one, star_neg]
  linear_combination ((64578939 / 100) * t ^ 6 + (-85072448 / 45) * t ^ 8 + (2183279594231 / 1200000) * t ^ 10 + (-224777194231 / 400000) * t ^ 12 + (-1161231221 / 1440000) * t ^ 14 + (-91060867439 / 7200000) * t ^ 16 + (1329134579 / 1800000) * t ^ 18 + (-521826473 / 5400000) * t ^ 20 + (8162015521 / 21600000) * t ^ 22 + (-7072523479 / 21600000) * t ^ 24 + (6185557 / 324000) * t ^ 26 + (-6185557 / 1296000) * t ^ 32 + (-294881 / 50) * c * t ^ 6 + (2330752 / 135) * c * t ^ 8 + (-29907939647 / 1800000) * c * t ^ 10 + (3079139647 / 600000) * c * t ^ 12 + (15907277 / 2160000) * c * t ^ 14 + (1247409143 / 10800000) * c * t ^ 16 + (-18207323 / 2700000) * c * t ^ 18 + (-7568713 / 4050000) * c * t ^ 20 + (66477439 / 32400000) * c * t ^ 22 + (-1093487 / 6480000) * c * t ^ 24 + (89717 / 243000) * c * t ^ 26 + (-89717 / 972000) * c * t ^ 32) * alpha_sq
#print axioms v43_00
#print axioms v43_11
#print axioms v43_22
#print axioms v43_33
#print axioms v43_44
end PhotonCertA
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z44 : Fin 44 → ℂ := Fin.snoc z43 (r ^ 3 * thetaPlus)
theorem v44_00 (t : ℂ) : (momentPoly 44 z44 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00]
  try simp only [phase43_00]
  try simp only [star_one, star_neg]
  ring
theorem v44_01 (t : ℂ) : (momentPoly 44 z44 0 1).eval t = ((1 / 5) * t + (-1 / 15) * c * t + (1 / 15) * alpha * t + (1 / 15) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01]
  try simp only [phase43_00, phase43_01]
  try simp only [star_one, star_neg]
  ring
theorem v44_02 (t : ℂ) : (momentPoly 44 z44 0 2).eval t = ((1981 / 600) * t ^ 2 + (-3149 / 600) * t ^ 4 + (-2 / 75) * c * t ^ 2 + (-2 / 75) * c * t ^ 4 + (897 / 200) * alpha * t ^ 2 + (-3859 / 600) * alpha * t ^ 4 + (2 / 225) * alpha * c * t ^ 2 + (2 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02]
  try simp only [phase43_00, phase43_01, phase43_02]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 450) * t ^ 2 + (1 / 225) * c * t ^ 2 + (1 / 450) * c ^ 2 * t ^ 2) * alpha_sq + ((-1 / 225) * t ^ 2 + (-1 / 225) * alpha * t ^ 2) * c_sq
theorem v44_03 (t : ℂ) : (momentPoly 44 z44 0 3).eval t = ((-71 / 100) * t ^ 3 + (71 / 100) * t ^ 5 + (-413 / 100) * c * t ^ 3 + (6763 / 1500) * c * t ^ 5 + (142 / 1125) * c * t ^ 9 + (413 / 100) * alpha * t ^ 3 + (-7963 / 1500) * alpha * t ^ 5 + (-442 / 1125) * alpha * t ^ 9 + (-71 / 300) * alpha * c * t ^ 3 + (71 / 300) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_03]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03]
  try simp only [star_one, star_neg]
  linear_combination ((131 / 240) * t ^ 3 + (-3859 / 6000) * t ^ 5 + (131 / 240) * c * t ^ 3 + (-11561 / 18000) * c * t ^ 5 + (1 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-4 / 1125) * alpha * t ^ 5) * c_sq
theorem v44_04 (t : ℂ) : (momentPoly 44 z44 0 4).eval t = ((-967757 / 8000) * t ^ 4 + (1533069 / 4000) * t ^ 6 + (-66197269 / 240000) * t ^ 8 + (1957391 / 180000) * t ^ 10 + (-3245839 / 720000) * t ^ 16 + (-584 / 375) * c * t ^ 4 + (3212 / 1875) * c * t ^ 8 + (1168 / 5625) * c * t ^ 10 + (292 / 5625) * c * t ^ 16 + (409267 / 8000) * alpha * t ^ 4 + (-103681 / 480) * alpha * t ^ 6 + (44047339 / 240000) * alpha * t ^ 8 + (-1065467 / 60000) * alpha * t ^ 10 + (4484849 / 720000) * alpha * t ^ 16 + (-242 / 375) * alpha * c * t ^ 4 + (3922 / 5625) * alpha * c * t ^ 8 + (1168 / 16875) * alpha * c * t ^ 10 + (292 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_03, v43_04]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04]
  try simp only [star_one, star_neg]
  linear_combination ((413 / 1500) * t ^ 4 + (-48641 / 3000) * t ^ 6 + (86797 / 5000) * t ^ 8 + (-884 / 16875) * t ^ 10 + (292 / 1125) * c * t ^ 4 + (-57 / 500) * c * t ^ 6 + (-3859 / 22500) * c * t ^ 8 + (-884 / 16875) * c * t ^ 10 + (-71 / 4500) * c ^ 2 * t ^ 4 + (71 / 4500) * c ^ 2 * t ^ 6 + (2 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((121 / 375) * t ^ 4 + (-121 / 375) * t ^ 6 + (4 / 5625) * t ^ 8 + (-284 / 16875) * t ^ 10 + (-292 / 1125) * alpha * t ^ 4 + (292 / 1125) * alpha * t ^ 6 + (-4 / 5625) * alpha * t ^ 8 + (284 / 16875) * alpha * t ^ 10) * c_sq
theorem v44_10 (t : ℂ) : (momentPoly 44 z44 1 0).eval t = ((1 / 5) * t + (-1 / 15) * c * t + (-1 / 15) * alpha * t + (-1 / 15) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_10]
  try simp only [phase43_00, phase43_10]
  try simp only [star_one, star_neg]
  ring
theorem v44_11 (t : ℂ) : (momentPoly 44 z44 1 1).eval t = (44 + (-40) * t ^ 2) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_10, v43_11]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 450) * t ^ 2 + (-1 / 225) * c * t ^ 2 + (-1 / 450) * c ^ 2 * t ^ 2) * alpha_sq + ((2 / 225) * t ^ 2) * c_sq
theorem v44_12 (t : ℂ) : (momentPoly 44 z44 1 2).eval t = ((87 / 5) * t + (-1114 / 75) * t ^ 3 + (-131 / 75) * t ^ 5 + (-29 / 5) * c * t + (961 / 150) * c * t ^ 3 + (-131 / 150) * c * t ^ 5 + (29 / 5) * alpha * t + (-719 / 150) * alpha * t ^ 3 + (-37 / 50) * alpha * t ^ 5 + (29 / 5) * alpha * c * t + (-1406 / 225) * alpha * c * t ^ 3 + (161 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_10, v43_11, v43_12]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12]
  try simp only [star_one, star_neg]
  linear_combination ((-131 / 720) * t ^ 3 + (3859 / 18000) * t ^ 5 + (-131 / 720) * c * t ^ 3 + (11561 / 54000) * c * t ^ 5 + (-1 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((2 / 1125) * t ^ 5 + (2 / 3375) * alpha * t ^ 5) * c_sq
theorem v44_13 (t : ℂ) : (momentPoly 44 z44 1 3).eval t = ((85183 / 200) * t ^ 2 + (-157049 / 150) * t ^ 4 + (60999 / 100) * t ^ 6 + (1981 / 600) * t ^ 10 + (-86 / 25) * c * t ^ 2 + (-8 / 75) * c * t ^ 4 + (84 / 25) * c * t ^ 6 + (-2 / 75) * c * t ^ 10 + (115713 / 200) * alpha * t ^ 2 + (-200359 / 150) * alpha * t ^ 4 + (74489 / 100) * alpha * t ^ 6 + (897 / 200) * alpha * t ^ 10 + (86 / 75) * alpha * c * t ^ 2 + (8 / 225) * alpha * c * t ^ 4 + (-28 / 25) * alpha * c * t ^ 6 + (2 / 225) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_03, v43_10, v43_11, v43_12, v43_13]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13]
  try simp only [star_one, star_neg]
  linear_combination ((43 / 150) * t ^ 2 + (-617 / 2000) * t ^ 4 + (57 / 2000) * t ^ 6 + (221 / 16875) * t ^ 10 + (43 / 75) * c * t ^ 2 + (-617 / 1000) * c * t ^ 4 + (57 / 1000) * c * t ^ 6 + (221 / 16875) * c * t ^ 10 + (43 / 150) * c ^ 2 * t ^ 2 + (-617 / 2000) * c ^ 2 * t ^ 4 + (57 / 2000) * c ^ 2 * t ^ 6) * alpha_sq + ((-43 / 75) * t ^ 2 + (337 / 500) * t ^ 4 + (-57 / 500) * t ^ 6 + (-71 / 16875) * t ^ 10 + (-43 / 75) * alpha * t ^ 2 + (127 / 180) * alpha * t ^ 4 + (-131 / 900) * alpha * t ^ 6 + (-71 / 16875) * alpha * t ^ 10) * c_sq
theorem v44_14 (t : ℂ) : (momentPoly 44 z44 1 4).eval t = ((-1207 / 10) * t ^ 3 + (4370403 / 20000) * t ^ 5 + (-2447009 / 30000) * t ^ 7 + (-1712881 / 120000) * t ^ 9 + (-209101 / 90000) * t ^ 11 + (123901 / 360000) * t ^ 17 + (-7021 / 10) * c * t ^ 3 + (264178921 / 180000) * c * t ^ 5 + (-24042827 / 30000) * c * t ^ 7 + (24622351 / 360000) * c * t ^ 9 + (-2874863 / 90000) * c * t ^ 11 + (516223 / 360000) * c * t ^ 17 + (7021 / 10) * alpha * t ^ 3 + (-276475639 / 180000) * alpha * t ^ 5 + (23949733 / 30000) * alpha * t ^ 7 + (-13655089 / 360000) * alpha * t ^ 9 + (5965297 / 90000) * alpha * t ^ 11 + (109781 / 120000) * alpha * t ^ 17 + (-1207 / 30) * alpha * c * t ^ 3 + (15118391 / 180000) * alpha * c * t ^ 5 + (-4454191 / 90000) * alpha * c * t ^ 7 + (2053681 / 360000) * alpha * c * t ^ 9 + (38701 / 270000) * alpha * c * t ^ 11 + (-123901 / 1080000) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_03, v43_04, v43_10, v43_11, v43_12, v43_13, v43_14]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14]
  try simp only [star_one, star_neg]
  linear_combination ((2227 / 24) * t ^ 3 + (-28962613 / 144000) * t ^ 5 + (39835817 / 360000) * t ^ 7 + (-5620463 / 1440000) * t ^ 9 + (12433 / 8640) * t ^ 11 + (-4484849 / 21600000) * t ^ 17 + (2227 / 24) * c * t ^ 3 + (-86822047 / 432000) * c * t ^ 5 + (40554841 / 360000) * c * t ^ 7 + (-8711599 / 1440000) * c * t ^ 9 + (12433 / 8640) * c * t ^ 11 + (-13491923 / 64800000) * c * t ^ 17 + (514 / 3375) * c ^ 2 * t ^ 5 + (-4969 / 33750) * c ^ 2 * t ^ 7 + (-71 / 33750) * c ^ 2 * t ^ 9 + (-146 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((-71 / 5625) * t ^ 7 + (71 / 5625) * t ^ 9 + (-2056 / 3375) * alpha * t ^ 5 + (3773 / 5625) * alpha * t ^ 7 + (-413 / 5625) * alpha * t ^ 9 + (-584 / 253125) * alpha * t ^ 17) * c_sq
theorem v44_20 (t : ℂ) : (momentPoly 44 z44 2 0).eval t = ((1981 / 600) * t ^ 2 + (-3149 / 600) * t ^ 4 + (-2 / 75) * c * t ^ 2 + (-2 / 75) * c * t ^ 4 + (-897 / 200) * alpha * t ^ 2 + (3859 / 600) * alpha * t ^ 4 + (-2 / 225) * alpha * c * t ^ 2 + (-2 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_10, v43_20]
  try simp only [phase43_00, phase43_10, phase43_20]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 450) * t ^ 2 + (1 / 225) * c * t ^ 2 + (1 / 450) * c ^ 2 * t ^ 2) * alpha_sq + ((-1 / 225) * t ^ 2 + (1 / 225) * alpha * t ^ 2) * c_sq
theorem v44_21 (t : ℂ) : (momentPoly 44 z44 2 1).eval t = ((87 / 5) * t + (-1114 / 75) * t ^ 3 + (-131 / 75) * t ^ 5 + (-29 / 5) * c * t + (961 / 150) * c * t ^ 3 + (-131 / 150) * c * t ^ 5 + (-29 / 5) * alpha * t + (719 / 150) * alpha * t ^ 3 + (37 / 50) * alpha * t ^ 5 + (-29 / 5) * alpha * c * t + (1406 / 225) * alpha * c * t ^ 3 + (-161 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_10, v43_11, v43_20, v43_21]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21]
  try simp only [star_one, star_neg]
  linear_combination ((-131 / 720) * t ^ 3 + (3859 / 18000) * t ^ 5 + (-131 / 720) * c * t ^ 3 + (11561 / 54000) * c * t ^ 5 + (-1 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((2 / 1125) * t ^ 5 + (-2 / 3375) * alpha * t ^ 5) * c_sq
theorem v44_22 (t : ℂ) : (momentPoly 44 z44 2 2).eval t = (3828 + (-6880) * t ^ 2 + (18044743 / 6000) * t ^ 4 + (-28387 / 600) * t ^ 6 + (215709 / 2000) * t ^ 8 + (71 / 1125) * c * t ^ 4 + (-71 / 1125) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_10, v43_11, v43_12, v43_20, v43_21, v43_22]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22]
  try simp only [star_one, star_neg]
  linear_combination ((-86 / 225) * t ^ 2 + (719 / 2250) * t ^ 4 + (48299 / 9000) * t ^ 6 + (-86797 / 15000) * t ^ 8 + (-172 / 225) * c * t ^ 2 + (4969 / 6750) * c * t ^ 4 + (-19 / 500) * c * t ^ 6 + (3859 / 67500) * c * t ^ 8 + (-86 / 225) * c ^ 2 * t ^ 2 + (1406 / 3375) * c ^ 2 * t ^ 4 + (-146 / 3375) * c ^ 2 * t ^ 6 + (-2 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((344 / 225) * t ^ 2 + (-3773 / 2250) * t ^ 4 + (413 / 2250) * t ^ 6 + (8 / 16875) * t ^ 8) * c_sq
theorem v44_23 (t : ℂ) : (momentPoly 44 z44 2 3).eval t = ((11224 / 5) * t + (-18938 / 5) * t ^ 3 + (6684601 / 6000) * t ^ 5 + (1124857 / 3000) * t ^ 7 + (2537 / 48) * t ^ 9 + (-11431 / 4500) * t ^ 11 + (29851 / 4500) * t ^ 13 + (-11224 / 15) * c * t + (16337 / 10) * c * t ^ 3 + (-6568667 / 6000) * c * t ^ 5 + (3358517 / 15000) * c * t ^ 7 + (-515099 / 30000) * c * t ^ 9 + (16147 / 7500) * c * t ^ 11 + (-4547 / 7500) * c * t ^ 13 + (11224 / 15) * alpha * t + (-12223 / 10) * alpha * t ^ 3 + (1757707 / 6000) * alpha * t ^ 5 + (2470783 / 15000) * alpha * t ^ 7 + (472499 / 30000) * alpha * t ^ 9 + (-497 / 7500) * alpha * t ^ 11 + (13097 / 7500) * alpha * t ^ 13 + (11224 / 15) * alpha * c * t + (-23902 / 15) * alpha * c * t ^ 3 + (18294521 / 18000) * alpha * c * t ^ 5 + (-1674083 / 9000) * alpha * c * t ^ 7 + (61721 / 3600) * alpha * c * t ^ 9 + (-26821 / 13500) * alpha * c * t ^ 11 + (10201 / 13500) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_03, v43_10, v43_11, v43_12, v43_13, v43_20, v43_21, v43_22, v43_23]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23]
  try simp only [star_one, star_neg]
  linear_combination ((-2227 / 48) * t ^ 3 + (1777763 / 18000) * t ^ 5 + (-301493 / 6000) * t ^ 7 + (-9563 / 6000) * t ^ 9 + (9563 / 13500) * t ^ 11 + (-852839 / 675000) * t ^ 13 + (-2227 / 48) * c * t ^ 3 + (5329177 / 54000) * c * t ^ 5 + (-313883 / 6000) * c * t ^ 7 + (131 / 240) * c * t ^ 9 + (-131 / 360) * c * t ^ 11 + (442 / 253125) * c * t ^ 13 + (-257 / 3375) * c ^ 2 * t ^ 5 + (2147 / 27000) * c ^ 2 * t ^ 7 + (-131 / 27000) * c ^ 2 * t ^ 9) * alpha_sq + ((514 / 1125) * t ^ 5 + (-5111 / 11250) * t ^ 7 + (71 / 11250) * t ^ 9 + (-142 / 84375) * t ^ 13 + (514 / 3375) * alpha * t ^ 5 + (-1609 / 11250) * alpha * t ^ 7 + (-71 / 11250) * alpha * t ^ 9 + (-142 / 253125) * alpha * t ^ 13) * c_sq
theorem v44_24 (t : ℂ) : (momentPoly 44 z44 2 4).eval t = ((21725627 / 300) * t ^ 2 + (-47889837 / 200) * t ^ 4 + (612862016633 / 2400000) * t ^ 6 + (-205956624523 / 2400000) * t ^ 8 + (-4289356621 / 4800000) * t ^ 10 + (-9023907947 / 4800000) * t ^ 12 + (2479979 / 9600) * t ^ 14 + (178900217 / 2880000) * t ^ 18 + (-1317372541 / 14400000) * t ^ 20 + (-43868 / 75) * c * t ^ 2 + (13374 / 25) * c * t ^ 4 + (68009099 / 112500) * c * t ^ 6 + (-60953099 / 112500) * c * t ^ 8 + (-2004043 / 112500) * c * t ^ 10 + (755099 / 112500) * c * t ^ 12 + (-251056 / 84375) * c * t ^ 14 + (62764 / 84375) * c * t ^ 18 + (-22 / 75) * c * t ^ 20 + (9837399 / 100) * alpha * t ^ 2 + (-62226867 / 200) * alpha * t ^ 4 + (2305331449301 / 7200000) * alpha * t ^ 6 + (-755537180351 / 7200000) * alpha * t ^ 8 + (-2133673177 / 14400000) * alpha * t ^ 10 + (-106895121437 / 43200000) * alpha * t ^ 12 + (18207323 / 144000) * alpha * t ^ 14 + (18207323 / 576000) * alpha * t ^ 18 + (-2395850857 / 43200000) * alpha * t ^ 20 + (43868 / 225) * alpha * c * t ^ 2 + (-4458 / 25) * alpha * c * t ^ 4 + (-5000541 / 25000) * alpha * c * t ^ 6 + (13433623 / 75000) * alpha * c * t ^ 8 + (1906411 / 450000) * alpha * c * t ^ 10 + (-1027199 / 1350000) * alpha * c * t ^ 12 + (431327 / 337500) * alpha * c * t ^ 14 + (-431327 / 1350000) * alpha * c * t ^ 18 + (29197 / 270000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_03, v43_04, v43_10, v43_11, v43_12, v43_13, v43_14, v43_20, v43_21, v43_22, v43_23, v43_24]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24]
  try simp only [star_one, star_neg]
  linear_combination ((10967 / 225) * t ^ 2 + (-12957 / 125) * t ^ 4 + (37644931 / 600000) * t ^ 6 + (162365053 / 3600000) * t ^ 8 + (-45950007 / 400000) * t ^ 10 + (168199493 / 2400000) * t ^ 12 + (-57179893 / 5400000) * t ^ 14 + (-8947901 / 3600000) * t ^ 18 + (21893451 / 4000000) * t ^ 20 + (21934 / 225) * c * t ^ 2 + (-25914 / 125) * c * t ^ 4 + (85349101 / 675000) * c * t ^ 6 + (-93518441 / 5400000) * c * t ^ 8 + (15411709 / 2700000) * c * t ^ 10 + (-57526703 / 10800000) * c * t ^ 12 + (4112173 / 8100000) * c * t ^ 14 + (-88079 / 1012500) * c * t ^ 18 + (60397 / 2160000) * c * t ^ 20 + (10967 / 225) * c ^ 2 * t ^ 2 + (-12957 / 125) * c ^ 2 * t ^ 4 + (343988429 / 5400000) * c ^ 2 * t ^ 6 + (-25323629 / 2700000) * c ^ 2 * t ^ 8 + (7586647 / 10800000) * c ^ 2 * t ^ 10 + (-1123157 / 8100000) * c ^ 2 * t ^ 12 + (9301 / 202500) * c ^ 2 * t ^ 14 + (123901 / 32400000) * c ^ 2 * t ^ 18 + (-292 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-21934 / 225) * t ^ 2 + (28308 / 125) * t ^ 4 + (-74658209 / 450000) * t ^ 6 + (8756609 / 225000) * t ^ 8 + (-3545729 / 900000) * t ^ 10 + (1443167 / 675000) * t ^ 12 + (-17182 / 84375) * t ^ 14 + (-16519 / 300000) * t ^ 18 + (-584 / 1265625) * t ^ 20 + (-21934 / 225) * alpha * t ^ 2 + (3556 / 15) * alpha * t ^ 4 + (-42172903 / 225000) * alpha * t ^ 6 + (17044709 / 337500) * alpha * t ^ 8 + (-3126709 / 675000) * alpha * t ^ 10 + (107128 / 50625) * alpha * t ^ 12 + (-41464 / 253125) * alpha * t ^ 14 + (-10066 / 253125) * alpha * t ^ 18 + (-584 / 1265625) * alpha * t ^ 20) * c_sq
theorem v44_30 (t : ℂ) : (momentPoly 44 z44 3 0).eval t = ((-71 / 100) * t ^ 3 + (71 / 100) * t ^ 5 + (-413 / 100) * c * t ^ 3 + (6763 / 1500) * c * t ^ 5 + (142 / 1125) * c * t ^ 9 + (-413 / 100) * alpha * t ^ 3 + (7963 / 1500) * alpha * t ^ 5 + (442 / 1125) * alpha * t ^ 9 + (71 / 300) * alpha * c * t ^ 3 + (-71 / 300) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_10, v43_20, v43_30]
  try simp only [phase43_00, phase43_10, phase43_20, phase43_30]
  try simp only [star_one, star_neg]
  linear_combination ((131 / 240) * t ^ 3 + (-3859 / 6000) * t ^ 5 + (131 / 240) * c * t ^ 3 + (-11561 / 18000) * c * t ^ 5 + (1 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((4 / 1125) * alpha * t ^ 5) * c_sq
theorem v44_31 (t : ℂ) : (momentPoly 44 z44 3 1).eval t = ((85183 / 200) * t ^ 2 + (-157049 / 150) * t ^ 4 + (60999 / 100) * t ^ 6 + (1981 / 600) * t ^ 10 + (-86 / 25) * c * t ^ 2 + (-8 / 75) * c * t ^ 4 + (84 / 25) * c * t ^ 6 + (-2 / 75) * c * t ^ 10 + (-115713 / 200) * alpha * t ^ 2 + (200359 / 150) * alpha * t ^ 4 + (-74489 / 100) * alpha * t ^ 6 + (-897 / 200) * alpha * t ^ 10 + (-86 / 75) * alpha * c * t ^ 2 + (-8 / 225) * alpha * c * t ^ 4 + (28 / 25) * alpha * c * t ^ 6 + (-2 / 225) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_10, v43_11, v43_20, v43_21, v43_30, v43_31]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21, phase43_30, phase43_31]
  try simp only [star_one, star_neg]
  linear_combination ((43 / 150) * t ^ 2 + (-617 / 2000) * t ^ 4 + (57 / 2000) * t ^ 6 + (221 / 16875) * t ^ 10 + (43 / 75) * c * t ^ 2 + (-617 / 1000) * c * t ^ 4 + (57 / 1000) * c * t ^ 6 + (221 / 16875) * c * t ^ 10 + (43 / 150) * c ^ 2 * t ^ 2 + (-617 / 2000) * c ^ 2 * t ^ 4 + (57 / 2000) * c ^ 2 * t ^ 6) * alpha_sq + ((-43 / 75) * t ^ 2 + (337 / 500) * t ^ 4 + (-57 / 500) * t ^ 6 + (-71 / 16875) * t ^ 10 + (43 / 75) * alpha * t ^ 2 + (-127 / 180) * alpha * t ^ 4 + (131 / 900) * alpha * t ^ 6 + (71 / 16875) * alpha * t ^ 10) * c_sq
theorem v44_32 (t : ℂ) : (momentPoly 44 z44 3 2).eval t = ((11224 / 5) * t + (-18938 / 5) * t ^ 3 + (6684601 / 6000) * t ^ 5 + (1124857 / 3000) * t ^ 7 + (2537 / 48) * t ^ 9 + (-11431 / 4500) * t ^ 11 + (29851 / 4500) * t ^ 13 + (-11224 / 15) * c * t + (16337 / 10) * c * t ^ 3 + (-6568667 / 6000) * c * t ^ 5 + (3358517 / 15000) * c * t ^ 7 + (-515099 / 30000) * c * t ^ 9 + (16147 / 7500) * c * t ^ 11 + (-4547 / 7500) * c * t ^ 13 + (-11224 / 15) * alpha * t + (12223 / 10) * alpha * t ^ 3 + (-1757707 / 6000) * alpha * t ^ 5 + (-2470783 / 15000) * alpha * t ^ 7 + (-472499 / 30000) * alpha * t ^ 9 + (497 / 7500) * alpha * t ^ 11 + (-13097 / 7500) * alpha * t ^ 13 + (-11224 / 15) * alpha * c * t + (23902 / 15) * alpha * c * t ^ 3 + (-18294521 / 18000) * alpha * c * t ^ 5 + (1674083 / 9000) * alpha * c * t ^ 7 + (-61721 / 3600) * alpha * c * t ^ 9 + (26821 / 13500) * alpha * c * t ^ 11 + (-10201 / 13500) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_10, v43_11, v43_12, v43_20, v43_21, v43_22, v43_30, v43_31, v43_32]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22, phase43_30, phase43_31, phase43_32]
  try simp only [star_one, star_neg]
  linear_combination ((-2227 / 48) * t ^ 3 + (1777763 / 18000) * t ^ 5 + (-301493 / 6000) * t ^ 7 + (-9563 / 6000) * t ^ 9 + (9563 / 13500) * t ^ 11 + (-852839 / 675000) * t ^ 13 + (-2227 / 48) * c * t ^ 3 + (5329177 / 54000) * c * t ^ 5 + (-313883 / 6000) * c * t ^ 7 + (131 / 240) * c * t ^ 9 + (-131 / 360) * c * t ^ 11 + (442 / 253125) * c * t ^ 13 + (-257 / 3375) * c ^ 2 * t ^ 5 + (2147 / 27000) * c ^ 2 * t ^ 7 + (-131 / 27000) * c ^ 2 * t ^ 9) * alpha_sq + ((514 / 1125) * t ^ 5 + (-5111 / 11250) * t ^ 7 + (71 / 11250) * t ^ 9 + (-142 / 84375) * t ^ 13 + (-514 / 3375) * alpha * t ^ 5 + (1609 / 11250) * alpha * t ^ 7 + (71 / 11250) * alpha * t ^ 9 + (142 / 253125) * alpha * t ^ 13) * c_sq
theorem v44_33 (t : ℂ) : (momentPoly 44 z44 3 3).eval t = (493856 + (-1316040) * t ^ 2 + (1136818809 / 1000) * t ^ 4 + (-66755743 / 200) * t ^ 6 + (14186277 / 250) * t ^ 8 + (-3725601 / 100) * t ^ 10 + (-99257 / 1000) * t ^ 12 + (-28387 / 200) * t ^ 14 + (-40) * t ^ 18 + (2982 / 125) * c * t ^ 4 + (-568 / 25) * c * t ^ 6 + (-9088 / 375) * c * t ^ 8 + (568 / 25) * c * t ^ 10 + (142 / 375) * c * t ^ 12) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_03, v43_10, v43_11, v43_12, v43_13, v43_20, v43_21, v43_22, v43_23, v43_30, v43_31, v43_32, v43_33]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23, phase43_30, phase43_31, phase43_32, phase43_33]
  try simp only [star_one, star_neg]
  linear_combination ((-10967 / 150) * t ^ 2 + (15099 / 125) * t ^ 4 + (39926891 / 20000) * t ^ 6 + (-124590509 / 30000) * t ^ 8 + (125420477 / 60000) * t ^ 10 + (184037 / 225000) * t ^ 12 + (841447 / 56250) * t ^ 14 + (-97682 / 1265625) * t ^ 18 + (-10967 / 75) * c * t ^ 2 + (34783 / 125) * c * t ^ 4 + (-4381127 / 30000) * c * t ^ 6 + (337733 / 9000) * c * t ^ 8 + (-233633 / 10000) * c * t ^ 10 + (8933 / 56250) * c * t ^ 12 + (-4199 / 12500) * c * t ^ 14 + (-10967 / 150) * c ^ 2 * t ^ 2 + (19684 / 125) * c ^ 2 * t ^ 4 + (-17951081 / 180000) * c ^ 2 * t ^ 6 + (4456187 / 270000) * c ^ 2 * t ^ 8 + (-77891 / 60000) * c ^ 2 * t ^ 10 + (26821 / 135000) * c ^ 2 * t ^ 12 + (-9301 / 135000) * c ^ 2 * t ^ 14) * alpha_sq + ((21934 / 75) * t ^ 2 + (-79233 / 125) * t ^ 4 + (6100607 / 15000) * t ^ 6 + (-313573 / 4500) * t ^ 8 + (76099 / 15000) * t ^ 10 + (-30149 / 28125) * t ^ 12 + (29323 / 56250) * t ^ 14 + (10082 / 1265625) * t ^ 18) * c_sq
theorem v44_34 (t : ℂ) : (momentPoly 44 z44 3 4).eval t = ((1908599 / 5) * t + (-23868564 / 25) * t ^ 3 + (664332643 / 1000) * t ^ 5 + (-2922835783 / 150000) * t ^ 7 + (-4458550869 / 100000) * t ^ 9 + (-112553121 / 4000) * t ^ 11 + (7059171599 / 1800000) * t ^ 13 + (-52250081 / 18750) * t ^ 15 + (-56822027 / 360000) * t ^ 17 + (9423889 / 2700000) * t ^ 19 + (-112279151 / 1800000) * t ^ 21 + (-262969 / 43200) * t ^ 25 + (-1908599 / 15) * c * t + (10295193 / 25) * c * t ^ 3 + (-490443981 / 1000) * c * t ^ 5 + (52078749413 / 200000) * c * t ^ 7 + (-185624105383 / 3000000) * c * t ^ 9 + (52083982417 / 6000000) * c * t ^ 11 + (-6259472201 / 3600000) * c * t ^ 13 + (25829153 / 60000) * c * t ^ 15 + (-273570109 / 9000000) * c * t ^ 17 + (1247260253 / 54000000) * c * t ^ 19 + (-23405853 / 2000000) * c * t ^ 21 + (-14114311 / 27000000) * c * t ^ 25 + (1908599 / 15) * alpha * t + (-7702647 / 25) * alpha * t ^ 3 + (192285461 / 1000) * alpha * t ^ 5 + (13248855119 / 600000) * alpha * t ^ 7 + (-76273357283 / 3000000) * alpha * t ^ 9 + (-46955261183 / 6000000) * alpha * t ^ 11 + (1975714819 / 3600000) * alpha * t ^ 13 + (-13809837 / 20000) * alpha * t ^ 15 + (-759506959 / 9000000) * alpha * t ^ 17 + (-593068147 / 54000000) * alpha * t ^ 19 + (-47616059 / 6000000) * alpha * t ^ 21 + (-36530461 / 27000000) * alpha * t ^ 25 + (1908599 / 15) * alpha * c * t + (-10041652 / 25) * alpha * c * t ^ 3 + (1383855683 / 3000) * alpha * c * t ^ 5 + (-104734007617 / 450000) * alpha * c * t ^ 7 + (47876432657 / 900000) * alpha * c * t ^ 9 + (-304449553 / 36000) * alpha * c * t ^ 11 + (3013432117 / 1800000) * alpha * c * t ^ 13 + (-20002921 / 37500) * alpha * c * t ^ 15 + (21108977 / 1080000) * alpha * c * t ^ 17 + (-305434789 / 8100000) * alpha * c * t ^ 19 + (135137801 / 5400000) * alpha * c * t ^ 21 + (95899 / 129600) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_03, v43_04, v43_10, v43_11, v43_12, v43_13, v43_14, v43_20, v43_21, v43_22, v43_23, v43_24, v43_30, v43_31, v43_32, v43_33, v43_34]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24, phase43_30, phase43_31, phase43_32, phase43_33, phase43_34]
  try simp only [star_one, star_neg]
  linear_combination ((-467801 / 40) * t ^ 3 + (214459417 / 6000) * t ^ 5 + (-33666897407 / 960000) * t ^ 7 + (724789676099 / 72000000) * t ^ 9 + (174298507529 / 144000000) * t ^ 11 + (-40336561927 / 48000000) * t ^ 13 + (19755193961 / 36000000) * t ^ 15 + (1749343843 / 54000000) * t ^ 17 + (-5731866203 / 1296000000) * t ^ 19 + (2789078717 / 432000000) * t ^ 21 + (991151629 / 810000000) * t ^ 25 + (-467801 / 40) * c * t ^ 3 + (643030043 / 18000) * c * t ^ 5 + (-34662062207 / 960000) * c * t ^ 7 + (873863561107 / 72000000) * c * t ^ 9 + (-45738392503 / 144000000) * c * t ^ 11 + (356369785283 / 1296000000) * c * t ^ 13 + (-392001289 / 21600000) * c * t ^ 15 + (392579 / 375000) * c * t ^ 17 + (-511329443 / 144000000) * c * t ^ 19 + (1920335117 / 432000000) * c * t ^ 21 + (64532 / 18984375) * c * t ^ 25 + (-21763 / 1125) * c ^ 2 * t ^ 5 + (538897 / 13500) * c ^ 2 * t ^ 7 + (-615827597 / 27000000) * c ^ 2 * t ^ 9 + (34261597 / 13500000) * c ^ 2 * t ^ 11 + (-16723267 / 54000000) * c ^ 2 * t ^ 13 + (47371 / 13500000) * c ^ 2 * t ^ 15 + (-9301 / 1012500) * c ^ 2 * t ^ 17 + (58181 / 5062500) * c ^ 2 * t ^ 19 + (-18797 / 3600000) * c ^ 2 * t ^ 21) * alpha_sq + ((43526 / 375) * t ^ 5 + (-1282861 / 5625) * t ^ 7 + (51006479 / 450000) * t ^ 9 + (-503839 / 225000) * t ^ 11 + (-353 / 4320) * t ^ 13 + (1071311 / 1125000) * t ^ 15 + (41464 / 421875) * t ^ 17 + (-9563 / 84375) * t ^ 19 + (50797 / 900000) * t ^ 21 + (20732 / 6328125) * t ^ 25 + (43526 / 1125) * alpha * t ^ 5 + (-403859 / 5625) * alpha * t ^ 7 + (21891157 / 750000) * alpha * t ^ 9 + (4373329 / 1125000) * alpha * t ^ 11 + (-12402811 / 40500000) * alpha * t ^ 13 + (14339 / 45000) * alpha * t ^ 15 + (17182 / 421875) * alpha * t ^ 17 + (-1387 / 46875) * alpha * t ^ 19 + (45203 / 2700000) * alpha * t ^ 21 + (20732 / 18984375) * alpha * t ^ 25) * c_sq
theorem v44_40 (t : ℂ) : (momentPoly 44 z44 4 0).eval t = ((-967757 / 8000) * t ^ 4 + (1533069 / 4000) * t ^ 6 + (-66197269 / 240000) * t ^ 8 + (1957391 / 180000) * t ^ 10 + (-3245839 / 720000) * t ^ 16 + (-584 / 375) * c * t ^ 4 + (3212 / 1875) * c * t ^ 8 + (1168 / 5625) * c * t ^ 10 + (292 / 5625) * c * t ^ 16 + (-409267 / 8000) * alpha * t ^ 4 + (103681 / 480) * alpha * t ^ 6 + (-44047339 / 240000) * alpha * t ^ 8 + (1065467 / 60000) * alpha * t ^ 10 + (-4484849 / 720000) * alpha * t ^ 16 + (242 / 375) * alpha * c * t ^ 4 + (-3922 / 5625) * alpha * c * t ^ 8 + (-1168 / 16875) * alpha * c * t ^ 10 + (-292 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_10, v43_20, v43_30, v43_40]
  try simp only [phase43_00, phase43_10, phase43_20, phase43_30, phase43_40]
  try simp only [star_one, star_neg]
  linear_combination ((413 / 1500) * t ^ 4 + (-48641 / 3000) * t ^ 6 + (86797 / 5000) * t ^ 8 + (-884 / 16875) * t ^ 10 + (292 / 1125) * c * t ^ 4 + (-57 / 500) * c * t ^ 6 + (-3859 / 22500) * c * t ^ 8 + (-884 / 16875) * c * t ^ 10 + (-71 / 4500) * c ^ 2 * t ^ 4 + (71 / 4500) * c ^ 2 * t ^ 6 + (2 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((121 / 375) * t ^ 4 + (-121 / 375) * t ^ 6 + (4 / 5625) * t ^ 8 + (-284 / 16875) * t ^ 10 + (292 / 1125) * alpha * t ^ 4 + (-292 / 1125) * alpha * t ^ 6 + (4 / 5625) * alpha * t ^ 8 + (-284 / 16875) * alpha * t ^ 10) * c_sq
theorem v44_41 (t : ℂ) : (momentPoly 44 z44 4 1).eval t = ((-1207 / 10) * t ^ 3 + (4370403 / 20000) * t ^ 5 + (-2447009 / 30000) * t ^ 7 + (-1712881 / 120000) * t ^ 9 + (-209101 / 90000) * t ^ 11 + (123901 / 360000) * t ^ 17 + (-7021 / 10) * c * t ^ 3 + (264178921 / 180000) * c * t ^ 5 + (-24042827 / 30000) * c * t ^ 7 + (24622351 / 360000) * c * t ^ 9 + (-2874863 / 90000) * c * t ^ 11 + (516223 / 360000) * c * t ^ 17 + (-7021 / 10) * alpha * t ^ 3 + (276475639 / 180000) * alpha * t ^ 5 + (-23949733 / 30000) * alpha * t ^ 7 + (13655089 / 360000) * alpha * t ^ 9 + (-5965297 / 90000) * alpha * t ^ 11 + (-109781 / 120000) * alpha * t ^ 17 + (1207 / 30) * alpha * c * t ^ 3 + (-15118391 / 180000) * alpha * c * t ^ 5 + (4454191 / 90000) * alpha * c * t ^ 7 + (-2053681 / 360000) * alpha * c * t ^ 9 + (-38701 / 270000) * alpha * c * t ^ 11 + (123901 / 1080000) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_10, v43_11, v43_20, v43_21, v43_30, v43_31, v43_40, v43_41]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21, phase43_30, phase43_31, phase43_40, phase43_41]
  try simp only [star_one, star_neg]
  linear_combination ((2227 / 24) * t ^ 3 + (-28962613 / 144000) * t ^ 5 + (39835817 / 360000) * t ^ 7 + (-5620463 / 1440000) * t ^ 9 + (12433 / 8640) * t ^ 11 + (-4484849 / 21600000) * t ^ 17 + (2227 / 24) * c * t ^ 3 + (-86822047 / 432000) * c * t ^ 5 + (40554841 / 360000) * c * t ^ 7 + (-8711599 / 1440000) * c * t ^ 9 + (12433 / 8640) * c * t ^ 11 + (-13491923 / 64800000) * c * t ^ 17 + (514 / 3375) * c ^ 2 * t ^ 5 + (-4969 / 33750) * c ^ 2 * t ^ 7 + (-71 / 33750) * c ^ 2 * t ^ 9 + (-146 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((-71 / 5625) * t ^ 7 + (71 / 5625) * t ^ 9 + (2056 / 3375) * alpha * t ^ 5 + (-3773 / 5625) * alpha * t ^ 7 + (413 / 5625) * alpha * t ^ 9 + (584 / 253125) * alpha * t ^ 17) * c_sq
theorem v44_42 (t : ℂ) : (momentPoly 44 z44 4 2).eval t = ((21725627 / 300) * t ^ 2 + (-47889837 / 200) * t ^ 4 + (612862016633 / 2400000) * t ^ 6 + (-205956624523 / 2400000) * t ^ 8 + (-4289356621 / 4800000) * t ^ 10 + (-9023907947 / 4800000) * t ^ 12 + (2479979 / 9600) * t ^ 14 + (178900217 / 2880000) * t ^ 18 + (-1317372541 / 14400000) * t ^ 20 + (-43868 / 75) * c * t ^ 2 + (13374 / 25) * c * t ^ 4 + (68009099 / 112500) * c * t ^ 6 + (-60953099 / 112500) * c * t ^ 8 + (-2004043 / 112500) * c * t ^ 10 + (755099 / 112500) * c * t ^ 12 + (-251056 / 84375) * c * t ^ 14 + (62764 / 84375) * c * t ^ 18 + (-22 / 75) * c * t ^ 20 + (-9837399 / 100) * alpha * t ^ 2 + (62226867 / 200) * alpha * t ^ 4 + (-2305331449301 / 7200000) * alpha * t ^ 6 + (755537180351 / 7200000) * alpha * t ^ 8 + (2133673177 / 14400000) * alpha * t ^ 10 + (106895121437 / 43200000) * alpha * t ^ 12 + (-18207323 / 144000) * alpha * t ^ 14 + (-18207323 / 576000) * alpha * t ^ 18 + (2395850857 / 43200000) * alpha * t ^ 20 + (-43868 / 225) * alpha * c * t ^ 2 + (4458 / 25) * alpha * c * t ^ 4 + (5000541 / 25000) * alpha * c * t ^ 6 + (-13433623 / 75000) * alpha * c * t ^ 8 + (-1906411 / 450000) * alpha * c * t ^ 10 + (1027199 / 1350000) * alpha * c * t ^ 12 + (-431327 / 337500) * alpha * c * t ^ 14 + (431327 / 1350000) * alpha * c * t ^ 18 + (-29197 / 270000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_10, v43_11, v43_12, v43_20, v43_21, v43_22, v43_30, v43_31, v43_32, v43_40, v43_41, v43_42]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22, phase43_30, phase43_31, phase43_32, phase43_40, phase43_41, phase43_42]
  try simp only [star_one, star_neg]
  linear_combination ((10967 / 225) * t ^ 2 + (-12957 / 125) * t ^ 4 + (37644931 / 600000) * t ^ 6 + (162365053 / 3600000) * t ^ 8 + (-45950007 / 400000) * t ^ 10 + (168199493 / 2400000) * t ^ 12 + (-57179893 / 5400000) * t ^ 14 + (-8947901 / 3600000) * t ^ 18 + (21893451 / 4000000) * t ^ 20 + (21934 / 225) * c * t ^ 2 + (-25914 / 125) * c * t ^ 4 + (85349101 / 675000) * c * t ^ 6 + (-93518441 / 5400000) * c * t ^ 8 + (15411709 / 2700000) * c * t ^ 10 + (-57526703 / 10800000) * c * t ^ 12 + (4112173 / 8100000) * c * t ^ 14 + (-88079 / 1012500) * c * t ^ 18 + (60397 / 2160000) * c * t ^ 20 + (10967 / 225) * c ^ 2 * t ^ 2 + (-12957 / 125) * c ^ 2 * t ^ 4 + (343988429 / 5400000) * c ^ 2 * t ^ 6 + (-25323629 / 2700000) * c ^ 2 * t ^ 8 + (7586647 / 10800000) * c ^ 2 * t ^ 10 + (-1123157 / 8100000) * c ^ 2 * t ^ 12 + (9301 / 202500) * c ^ 2 * t ^ 14 + (123901 / 32400000) * c ^ 2 * t ^ 18 + (-292 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-21934 / 225) * t ^ 2 + (28308 / 125) * t ^ 4 + (-74658209 / 450000) * t ^ 6 + (8756609 / 225000) * t ^ 8 + (-3545729 / 900000) * t ^ 10 + (1443167 / 675000) * t ^ 12 + (-17182 / 84375) * t ^ 14 + (-16519 / 300000) * t ^ 18 + (-584 / 1265625) * t ^ 20 + (21934 / 225) * alpha * t ^ 2 + (-3556 / 15) * alpha * t ^ 4 + (42172903 / 225000) * alpha * t ^ 6 + (-17044709 / 337500) * alpha * t ^ 8 + (3126709 / 675000) * alpha * t ^ 10 + (-107128 / 50625) * alpha * t ^ 12 + (41464 / 253125) * alpha * t ^ 14 + (10066 / 253125) * alpha * t ^ 18 + (584 / 1265625) * alpha * t ^ 20) * c_sq
theorem v44_43 (t : ℂ) : (momentPoly 44 z44 4 3).eval t = ((1908599 / 5) * t + (-23868564 / 25) * t ^ 3 + (664332643 / 1000) * t ^ 5 + (-2922835783 / 150000) * t ^ 7 + (-4458550869 / 100000) * t ^ 9 + (-112553121 / 4000) * t ^ 11 + (7059171599 / 1800000) * t ^ 13 + (-52250081 / 18750) * t ^ 15 + (-56822027 / 360000) * t ^ 17 + (9423889 / 2700000) * t ^ 19 + (-112279151 / 1800000) * t ^ 21 + (-262969 / 43200) * t ^ 25 + (-1908599 / 15) * c * t + (10295193 / 25) * c * t ^ 3 + (-490443981 / 1000) * c * t ^ 5 + (52078749413 / 200000) * c * t ^ 7 + (-185624105383 / 3000000) * c * t ^ 9 + (52083982417 / 6000000) * c * t ^ 11 + (-6259472201 / 3600000) * c * t ^ 13 + (25829153 / 60000) * c * t ^ 15 + (-273570109 / 9000000) * c * t ^ 17 + (1247260253 / 54000000) * c * t ^ 19 + (-23405853 / 2000000) * c * t ^ 21 + (-14114311 / 27000000) * c * t ^ 25 + (-1908599 / 15) * alpha * t + (7702647 / 25) * alpha * t ^ 3 + (-192285461 / 1000) * alpha * t ^ 5 + (-13248855119 / 600000) * alpha * t ^ 7 + (76273357283 / 3000000) * alpha * t ^ 9 + (46955261183 / 6000000) * alpha * t ^ 11 + (-1975714819 / 3600000) * alpha * t ^ 13 + (13809837 / 20000) * alpha * t ^ 15 + (759506959 / 9000000) * alpha * t ^ 17 + (593068147 / 54000000) * alpha * t ^ 19 + (47616059 / 6000000) * alpha * t ^ 21 + (36530461 / 27000000) * alpha * t ^ 25 + (-1908599 / 15) * alpha * c * t + (10041652 / 25) * alpha * c * t ^ 3 + (-1383855683 / 3000) * alpha * c * t ^ 5 + (104734007617 / 450000) * alpha * c * t ^ 7 + (-47876432657 / 900000) * alpha * c * t ^ 9 + (304449553 / 36000) * alpha * c * t ^ 11 + (-3013432117 / 1800000) * alpha * c * t ^ 13 + (20002921 / 37500) * alpha * c * t ^ 15 + (-21108977 / 1080000) * alpha * c * t ^ 17 + (305434789 / 8100000) * alpha * c * t ^ 19 + (-135137801 / 5400000) * alpha * c * t ^ 21 + (-95899 / 129600) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_03, v43_10, v43_11, v43_12, v43_13, v43_20, v43_21, v43_22, v43_23, v43_30, v43_31, v43_32, v43_33, v43_40, v43_41, v43_42, v43_43]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23, phase43_30, phase43_31, phase43_32, phase43_33, phase43_40, phase43_41, phase43_42, phase43_43]
  try simp only [star_one, star_neg]
  linear_combination ((-467801 / 40) * t ^ 3 + (214459417 / 6000) * t ^ 5 + (-33666897407 / 960000) * t ^ 7 + (724789676099 / 72000000) * t ^ 9 + (174298507529 / 144000000) * t ^ 11 + (-40336561927 / 48000000) * t ^ 13 + (19755193961 / 36000000) * t ^ 15 + (1749343843 / 54000000) * t ^ 17 + (-5731866203 / 1296000000) * t ^ 19 + (2789078717 / 432000000) * t ^ 21 + (991151629 / 810000000) * t ^ 25 + (-467801 / 40) * c * t ^ 3 + (643030043 / 18000) * c * t ^ 5 + (-34662062207 / 960000) * c * t ^ 7 + (873863561107 / 72000000) * c * t ^ 9 + (-45738392503 / 144000000) * c * t ^ 11 + (356369785283 / 1296000000) * c * t ^ 13 + (-392001289 / 21600000) * c * t ^ 15 + (392579 / 375000) * c * t ^ 17 + (-511329443 / 144000000) * c * t ^ 19 + (1920335117 / 432000000) * c * t ^ 21 + (64532 / 18984375) * c * t ^ 25 + (-21763 / 1125) * c ^ 2 * t ^ 5 + (538897 / 13500) * c ^ 2 * t ^ 7 + (-615827597 / 27000000) * c ^ 2 * t ^ 9 + (34261597 / 13500000) * c ^ 2 * t ^ 11 + (-16723267 / 54000000) * c ^ 2 * t ^ 13 + (47371 / 13500000) * c ^ 2 * t ^ 15 + (-9301 / 1012500) * c ^ 2 * t ^ 17 + (58181 / 5062500) * c ^ 2 * t ^ 19 + (-18797 / 3600000) * c ^ 2 * t ^ 21) * alpha_sq + ((43526 / 375) * t ^ 5 + (-1282861 / 5625) * t ^ 7 + (51006479 / 450000) * t ^ 9 + (-503839 / 225000) * t ^ 11 + (-353 / 4320) * t ^ 13 + (1071311 / 1125000) * t ^ 15 + (41464 / 421875) * t ^ 17 + (-9563 / 84375) * t ^ 19 + (50797 / 900000) * t ^ 21 + (20732 / 6328125) * t ^ 25 + (-43526 / 1125) * alpha * t ^ 5 + (403859 / 5625) * alpha * t ^ 7 + (-21891157 / 750000) * alpha * t ^ 9 + (-4373329 / 1125000) * alpha * t ^ 11 + (12402811 / 40500000) * alpha * t ^ 13 + (-14339 / 45000) * alpha * t ^ 15 + (-17182 / 421875) * alpha * t ^ 17 + (1387 / 46875) * alpha * t ^ 19 + (-45203 / 2700000) * alpha * t ^ 21 + (-20732 / 18984375) * alpha * t ^ 25) * c_sq
theorem v44_44 (t : ℂ) : (momentPoly 44 z44 4 4).eval t = (83978356 + (-294929600) * t ^ 2 + (94392050633 / 250) * t ^ 4 + (-21316817291 / 100) * t ^ 6 + (620360686108927 / 9600000) * t ^ 8 + (-114509660817977 / 4000000) * t ^ 10 + (2414673983141869 / 240000000) * t ^ 12 + (155264894301911 / 360000000) * t ^ 14 + (85952612111447 / 960000000) * t ^ 16 + (-17402470008277 / 360000000) * t ^ 18 + (19400597616983 / 720000000) * t ^ 20 + (-3843654369779 / 360000000) * t ^ 22 + (466986001309 / 57600000) * t ^ 24 + (-24913339267 / 216000000) * t ^ 26 + (808016403727 / 8640000000) * t ^ 32 + (2971208 / 375) * c * t ^ 4 + (-372608 / 25) * c * t ^ 6 + (-2863368631 / 2250000) * c * t ^ 8 + (5682298877 / 375000) * c * t ^ 10 + (-148940332439 / 22500000) * c * t ^ 12 + (-1607202799 / 8437500) * c * t ^ 14 + (-831692189 / 67500000) * c * t ^ 16 + (-1271692439 / 16875000) * c * t ^ 18 + (-4189462789 / 202500000) * c * t ^ 20 + (73262143 / 4218750) * c * t ^ 22 + (8049089 / 4500000) * c * t ^ 24 + (9044773 / 50625000) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_03, v43_04, v43_10, v43_11, v43_12, v43_13, v43_14, v43_20, v43_21, v43_22, v43_23, v43_24, v43_30, v43_31, v43_32, v43_33, v43_34, v43_40, v43_41, v43_42, v43_43, v43_44]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24, phase43_30, phase43_31, phase43_32, phase43_33, phase43_34, phase43_40, phase43_41, phase43_42, phase43_43, phase43_44]
  try simp only [star_one, star_neg]
  linear_combination ((-737324 / 45) * t ^ 2 + (15044356 / 375) * t ^ 4 + (4895758681 / 7500) * t ^ 6 + (-9083854141679 / 4500000) * t ^ 8 + (35525283252013 / 18000000) * t ^ 10 + (-6190249779089 / 10000000) * t ^ 12 + (17960028737 / 21600000) * t ^ 14 + (-7635884282549 / 540000000) * t ^ 16 + (67096092197 / 81000000) * t ^ 18 + (-184611691 / 4218750) * t ^ 20 + (232142488213 / 540000000) * t ^ 22 + (-218009923327 / 540000000) * t ^ 24 + (514048709 / 25312500) * t ^ 26 + (-6983685107 / 1350000000) * t ^ 32 + (-1474648 / 45) * c * t ^ 2 + (103971356 / 1125) * c * t ^ 4 + (-341811269 / 3750) * c * t ^ 6 + (598973803031 / 13500000) * c * t ^ 8 + (-20827083233 / 1000000) * c * t ^ 10 + (133957048753 / 16875000) * c * t ^ 12 + (-196752761051 / 810000000) * c * t ^ 14 + (205348868173 / 810000000) * c * t ^ 16 + (1264455613 / 202500000) * c * t ^ 18 + (4603011457 / 1215000000) * c * t ^ 20 + (58149077 / 162000000) * c * t ^ 22 + (-52641353 / 270000000) * c * t ^ 24 + (38330461 / 101250000) * c * t ^ 26 + (-327393977 / 3037500000) * c * t ^ 32 + (-737324 / 45) * c ^ 2 * t ^ 2 + (58838288 / 1125) * c ^ 2 * t ^ 4 + (-676429241 / 11250) * c ^ 2 * t ^ 6 + (298706768951 / 10125000) * c ^ 2 * t ^ 8 + (-6747590017 / 1125000) * c ^ 2 * t ^ 10 + (28548365051 / 33750000) * c ^ 2 * t ^ 12 + (-1698920383 / 8437500) * c ^ 2 * t ^ 14 + (795462533 / 12656250) * c ^ 2 * t ^ 16 + (-424983161 / 202500000) * c ^ 2 * t ^ 18 + (288692989 / 60750000) * c ^ 2 * t ^ 20 + (-281542441 / 101250000) * c ^ 2 * t ^ 22 + (-416641 / 50625000) * c ^ 2 * t ^ 24 + (-87259 / 972000) * c ^ 2 * t ^ 26 + (-42632 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((2949296 / 45) * t ^ 2 + (-78946252 / 375) * t ^ 4 + (152708613 / 625) * t ^ 6 + (-1641890938841 / 13500000) * t ^ 8 + (112776303641 / 4500000) * t ^ 10 + (-53090550199 / 15000000) * t ^ 12 + (156851245639 / 135000000) * t ^ 14 + (-4747167371 / 11250000) * t ^ 16 + (1258801597 / 50625000) * t ^ 18 + (-10199549201 / 405000000) * t ^ 20 + (424047209 / 45000000) * t ^ 22 + (486251 / 5625000) * t ^ 24 + (33425593 / 50625000) * t ^ 26 + (170528 / 94921875) * t ^ 32) * c_sq
#print axioms v44_00
#print axioms v44_11
#print axioms v44_22
#print axioms v44_33
#print axioms v44_44
end PhotonCertA
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z45 : Fin 45 → ℂ := Fin.snoc z44 (r ^ 3 * thetaPlus)
theorem v45_00 (t : ℂ) : (momentPoly 45 z45 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00]
  try simp only [phase43_00]
  try simp only [star_one, star_neg]
  ring
theorem v45_01 (t : ℂ) : (momentPoly 45 z45 0 1).eval t = ((3 / 10) * t + (-1 / 10) * c * t + (1 / 10) * alpha * t + (1 / 10) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01]
  try simp only [phase43_00, phase43_01]
  try simp only [star_one, star_neg]
  ring
theorem v45_02 (t : ℂ) : (momentPoly 45 z45 0 2).eval t = ((271 / 200) * t ^ 2 + (-1147 / 200) * t ^ 4 + (-2 / 25) * c * t ^ 2 + (-1 / 25) * c * t ^ 4 + (1523 / 600) * alpha * t ^ 2 + (-4151 / 600) * alpha * t ^ 4 + (2 / 75) * alpha * c * t ^ 2 + (1 / 75) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02]
  try simp only [phase43_00, phase43_01, phase43_02]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 225) * t ^ 2 + (2 / 225) * c * t ^ 2 + (1 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((-2 / 225) * t ^ 2 + (-2 / 225) * alpha * t ^ 2) * c_sq
theorem v45_03 (t : ℂ) : (momentPoly 45 z45 0 3).eval t = ((-213 / 200) * t ^ 3 + (213 / 200) * t ^ 5 + (-17449 / 3000) * c * t ^ 3 + (7331 / 1000) * c * t ^ 5 + (71 / 375) * c * t ^ 9 + (15049 / 3000) * alpha * t ^ 3 + (-9731 / 1000) * alpha * t ^ 5 + (-221 / 375) * alpha * t ^ 9 + (-71 / 200) * alpha * c * t ^ 3 + (71 / 200) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_03]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03]
  try simp only [star_one, star_neg]
  linear_combination ((897 / 2000) * t ^ 3 + (-1481 / 2000) * t ^ 5 + (8089 / 18000) * c * t ^ 3 + (-13297 / 18000) * c * t ^ 5 + (1 / 1125) * c ^ 2 * t ^ 3 + (2 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-4 / 1125) * alpha * t ^ 3 + (-8 / 1125) * alpha * t ^ 5) * c_sq
theorem v45_04 (t : ℂ) : (momentPoly 45 z45 0 4).eval t = ((162867 / 8000) * t ^ 4 + (5223313 / 20000) * t ^ 6 + (-25321799 / 80000) * t ^ 8 + (74327 / 20000) * t ^ 10 + (-396439 / 80000) * t ^ 16 + (-584 / 125) * c * t ^ 4 + (2044 / 625) * c * t ^ 6 + (1752 / 625) * c * t ^ 8 + (1168 / 1875) * c * t ^ 10 + (146 / 1875) * c * t ^ 16 + (-1500647 / 24000) * alpha * t ^ 4 + (-6877949 / 60000) * alpha * t ^ 6 + (52156907 / 240000) * alpha * t ^ 8 + (-1907953 / 180000) * alpha * t ^ 10 + (4806961 / 720000) * alpha * t ^ 16 + (-242 / 125) * alpha * c * t ^ 4 + (2399 / 1875) * alpha * c * t ^ 6 + (2107 / 1875) * alpha * c * t ^ 8 + (1168 / 5625) * alpha * c * t ^ 10 + (146 / 5625) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_03, v44_04]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04]
  try simp only [star_one, star_neg]
  linear_combination ((413 / 750) * t ^ 4 + (-621181 / 45000) * t ^ 6 + (281707 / 15000) * t ^ 8 + (-1768 / 16875) * t ^ 10 + (584 / 1125) * c * t ^ 4 + (-13109 / 22500) * c * t ^ 6 + (-1481 / 7500) * c * t ^ 8 + (-1768 / 16875) * c * t ^ 10 + (-71 / 2250) * c ^ 2 * t ^ 4 + (1073 / 33750) * c ^ 2 * t ^ 6 + (4 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((242 / 375) * t ^ 4 + (-434 / 625) * t ^ 6 + (8 / 5625) * t ^ 8 + (-568 / 16875) * t ^ 10 + (-584 / 1125) * alpha * t ^ 4 + (3196 / 5625) * alpha * t ^ 6 + (-8 / 5625) * alpha * t ^ 8 + (568 / 16875) * alpha * t ^ 10) * c_sq
theorem v45_10 (t : ℂ) : (momentPoly 45 z45 1 0).eval t = ((3 / 10) * t + (-1 / 10) * c * t + (-1 / 10) * alpha * t + (-1 / 10) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_10]
  try simp only [phase43_00, phase43_10]
  try simp only [star_one, star_neg]
  ring
theorem v45_11 (t : ℂ) : (momentPoly 45 z45 1 1).eval t = (45 + (-36) * t ^ 2) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_10, v44_11]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 225) * t ^ 2 + (-2 / 225) * c * t ^ 2 + (-1 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((4 / 225) * t ^ 2) * c_sq
theorem v45_12 (t : ℂ) : (momentPoly 45 z45 1 2).eval t = ((267 / 10) * t + (-542 / 25) * t ^ 3 + (-58 / 25) * t ^ 5 + (-89 / 10) * c * t + (941 / 100) * c * t ^ 3 + (-141 / 100) * c * t ^ 5 + (89 / 10) * alpha * t + (-699 / 100) * alpha * t ^ 3 + (-101 / 100) * alpha * t ^ 5 + (89 / 10) * alpha * c * t + (-688 / 75) * alpha * c * t ^ 3 + (88 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_10, v44_11, v44_12]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12]
  try simp only [star_one, star_neg]
  linear_combination ((-299 / 2000) * t ^ 3 + (1481 / 6000) * t ^ 5 + (-8089 / 54000) * c * t ^ 3 + (13297 / 54000) * c * t ^ 5 + (-1 / 3375) * c ^ 2 * t ^ 3 + (-2 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((2 / 1125) * t ^ 3 + (4 / 1125) * t ^ 5 + (2 / 3375) * alpha * t ^ 3 + (4 / 3375) * alpha * t ^ 5) * c_sq
theorem v45_13 (t : ℂ) : (momentPoly 45 z45 1 3).eval t = ((8943 / 50) * t ^ 2 + (-166177 / 200) * t ^ 4 + (2445 / 4) * t ^ 6 + (271 / 200) * t ^ 10 + (-264 / 25) * c * t ^ 2 + (119 / 25) * c * t ^ 4 + (24 / 5) * c * t ^ 6 + (-2 / 25) * c * t ^ 10 + (16753 / 50) * alpha * t ^ 2 + (-665381 / 600) * alpha * t ^ 4 + (14639 / 20) * alpha * t ^ 6 + (1523 / 600) * alpha * t ^ 10 + (88 / 25) * alpha * c * t ^ 2 + (-119 / 75) * alpha * c * t ^ 4 + (-8 / 5) * alpha * c * t ^ 6 + (2 / 75) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_03, v44_10, v44_11, v44_12, v44_13]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13]
  try simp only [star_one, star_neg]
  linear_combination ((44 / 75) * t ^ 2 + (-617 / 1000) * t ^ 4 + (4633 / 45000) * t ^ 6 + (442 / 16875) * t ^ 10 + (88 / 75) * c * t ^ 2 + (-617 / 500) * c * t ^ 4 + (3749 / 22500) * c * t ^ 6 + (442 / 16875) * c * t ^ 10 + (44 / 75) * c ^ 2 * t ^ 2 + (-617 / 1000) * c ^ 2 * t ^ 4 + (191 / 3000) * c ^ 2 * t ^ 6) * alpha_sq + ((-88 / 75) * t ^ 2 + (337 / 250) * t ^ 4 + (-2857 / 11250) * t ^ 6 + (-142 / 16875) * t ^ 10 + (-88 / 75) * alpha * t ^ 2 + (127 / 90) * alpha * t ^ 4 + (-1189 / 3750) * alpha * t ^ 6 + (-142 / 16875) * alpha * t ^ 10) * c_sq
theorem v45_14 (t : ℂ) : (momentPoly 45 z45 1 4).eval t = ((-18531 / 100) * t ^ 3 + (13111209 / 40000) * t ^ 5 + (-2404409 / 20000) * t ^ 7 + (-1542481 / 80000) * t ^ 9 + (-209101 / 60000) * t ^ 11 + (123901 / 240000) * t ^ 17 + (-506021 / 500) * c * t ^ 3 + (268768361 / 120000) * c * t ^ 5 + (-25703507 / 20000) * c * t ^ 7 + (9350117 / 80000) * c * t ^ 9 + (-2783983 / 60000) * c * t ^ 11 + (187221 / 80000) * c * t ^ 17 + (436421 / 500) * alpha * t ^ 3 + (-290761079 / 120000) * alpha * t ^ 5 + (29642413 / 20000) * alpha * t ^ 7 + (-6014363 / 80000) * alpha * t ^ 9 + (1894139 / 20000) * alpha * t ^ 11 + (187903 / 240000) * alpha * t ^ 17 + (-6177 / 100) * alpha * c * t ^ 3 + (15118391 / 120000) * alpha * c * t ^ 5 + (-4411591 / 60000) * alpha * c * t ^ 7 + (2224081 / 240000) * alpha * c * t ^ 9 + (38701 / 180000) * alpha * c * t ^ 11 + (-123901 / 720000) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_03, v44_04, v44_10, v44_11, v44_12, v44_13, v44_14]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14]
  try simp only [star_one, star_neg]
  linear_combination ((78039 / 1000) * t ^ 3 + (-47557027 / 240000) * t ^ 5 + (43385497 / 360000) * t ^ 7 + (-28489579 / 7200000) * t ^ 9 + (2141867 / 1800000) * t ^ 11 + (-569897 / 2400000) * t ^ 17 + (234581 / 3000) * c * t ^ 3 + (-427616059 / 2160000) * c * t ^ 5 + (44815801 / 360000) * c * t ^ 7 + (-178201793 / 21600000) * c * t ^ 9 + (19258627 / 16200000) * c * t ^ 11 + (-15461971 / 64800000) * c * t ^ 17 + (58 / 375) * c ^ 2 * t ^ 3 + (3103 / 16875) * c ^ 2 * t ^ 5 + (-5332 / 16875) * c ^ 2 * t ^ 7 + (-13 / 3125) * c ^ 2 * t ^ 9 + (-284 / 253125) * c ^ 2 * t ^ 11 + (-292 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((-71 / 5625) * t ^ 5 + (-71 / 5625) * t ^ 7 + (142 / 5625) * t ^ 9 + (-232 / 375) * alpha * t ^ 3 + (-9721 / 16875) * alpha * t ^ 5 + (7133 / 5625) * alpha * t ^ 7 + (-13574 / 84375) * alpha * t ^ 9 + (-3536 / 253125) * alpha * t ^ 11 + (-1168 / 253125) * alpha * t ^ 17) * c_sq
theorem v45_20 (t : ℂ) : (momentPoly 45 z45 2 0).eval t = ((271 / 200) * t ^ 2 + (-1147 / 200) * t ^ 4 + (-2 / 25) * c * t ^ 2 + (-1 / 25) * c * t ^ 4 + (-1523 / 600) * alpha * t ^ 2 + (4151 / 600) * alpha * t ^ 4 + (-2 / 75) * alpha * c * t ^ 2 + (-1 / 75) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_10, v44_20]
  try simp only [phase43_00, phase43_10, phase43_20]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 225) * t ^ 2 + (2 / 225) * c * t ^ 2 + (1 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((-2 / 225) * t ^ 2 + (2 / 225) * alpha * t ^ 2) * c_sq
theorem v45_21 (t : ℂ) : (momentPoly 45 z45 2 1).eval t = ((267 / 10) * t + (-542 / 25) * t ^ 3 + (-58 / 25) * t ^ 5 + (-89 / 10) * c * t + (941 / 100) * c * t ^ 3 + (-141 / 100) * c * t ^ 5 + (-89 / 10) * alpha * t + (699 / 100) * alpha * t ^ 3 + (101 / 100) * alpha * t ^ 5 + (-89 / 10) * alpha * c * t + (688 / 75) * alpha * c * t ^ 3 + (-88 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_10, v44_11, v44_20, v44_21]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21]
  try simp only [star_one, star_neg]
  linear_combination ((-299 / 2000) * t ^ 3 + (1481 / 6000) * t ^ 5 + (-8089 / 54000) * c * t ^ 3 + (13297 / 54000) * c * t ^ 5 + (-1 / 3375) * c ^ 2 * t ^ 3 + (-2 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((2 / 1125) * t ^ 3 + (4 / 1125) * t ^ 5 + (-2 / 3375) * alpha * t ^ 3 + (-4 / 3375) * alpha * t ^ 5) * c_sq
theorem v45_22 (t : ℂ) : (momentPoly 45 z45 2 2).eval t = (4005 + (-6336) * t ^ 2 + (13530359 / 6000) * t ^ 4 + (74959 / 3000) * t ^ 6 + (791723 / 6000) * t ^ 8 + (71 / 375) * c * t ^ 4 + (-71 / 750) * c * t ^ 6 + (-71 / 750) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_10, v44_11, v44_12, v44_20, v44_21, v44_22]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22]
  try simp only [star_one, star_neg]
  linear_combination ((-176 / 225) * t ^ 2 + (719 / 1125) * t ^ 4 + (66961 / 15000) * t ^ 6 + (-281707 / 45000) * t ^ 8 + (-352 / 225) * c * t ^ 2 + (4969 / 3375) * c * t ^ 4 + (-629 / 22500) * c * t ^ 6 + (1481 / 22500) * c * t ^ 8 + (-176 / 225) * c ^ 2 * t ^ 2 + (2812 / 3375) * c ^ 2 * t ^ 4 + (-4834 / 50625) * c ^ 2 * t ^ 6 + (-4 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((704 / 225) * t ^ 2 + (-3773 / 1125) * t ^ 4 + (6811 / 16875) * t ^ 6 + (16 / 16875) * t ^ 8) * c_sq
theorem v45_23 (t : ℂ) : (momentPoly 45 z45 2 3).eval t = ((35247 / 10) * t + (-141462 / 25) * t ^ 3 + (3795239 / 2400) * t ^ 5 + (2810509 / 6000) * t ^ 7 + (405089 / 4000) * t ^ 9 + (-9631 / 3000) * t ^ 11 + (30751 / 3000) * t ^ 13 + (-11749 / 10) * c * t + (245601 / 100) * c * t ^ 3 + (-32340959 / 20000) * c * t ^ 5 + (3582311 / 10000) * c * t ^ 7 + (-648263 / 20000) * c * t ^ 9 + (15147 / 5000) * c * t ^ 11 + (-5047 / 5000) * c * t ^ 13 + (11749 / 10) * alpha * t + (-182439 / 100) * alpha * t ^ 3 + (8217759 / 20000) * alpha * t ^ 5 + (2157289 / 10000) * alpha * t ^ 7 + (563063 / 20000) * alpha * t ^ 9 + (503 / 5000) * alpha * t ^ 11 + (13597 / 5000) * alpha * t ^ 13 + (11749 / 10) * alpha * c * t + (-59856 / 25) * alpha * c * t ^ 3 + (10792631 / 7200) * alpha * c * t ^ 5 + (-5441891 / 18000) * alpha * c * t ^ 7 + (388049 / 12000) * alpha * c * t ^ 9 + (-25021 / 9000) * alpha * c * t ^ 11 + (11101 / 9000) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_03, v44_10, v44_11, v44_12, v44_13, v44_20, v44_21, v44_22, v44_23]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23]
  try simp only [star_one, star_neg]
  linear_combination ((-78039 / 2000) * t ^ 3 + (196449 / 2000) * t ^ 5 + (-163943 / 3000) * t ^ 7 + (-824389 / 225000) * t ^ 9 + (21827 / 37500) * t ^ 11 + (-327301 / 225000) * t ^ 13 + (-234581 / 6000) * c * t ^ 3 + (5299739 / 54000) * c * t ^ 5 + (-176333 / 3000) * c * t ^ 7 + (805511 / 675000) * c * t ^ 9 + (-603139 / 2025000) * c * t ^ 11 + (884 / 253125) * c * t ^ 13 + (-29 / 375) * c ^ 2 * t ^ 3 + (-274 / 3375) * c ^ 2 * t ^ 5 + (2147 / 13500) * c ^ 2 * t ^ 7 + (-143 / 13500) * c ^ 2 * t ^ 9 + (-2 / 3375) * c ^ 2 * t ^ 11) * alpha_sq + ((58 / 125) * t ^ 3 + (601 / 1250) * t ^ 5 + (-10151 / 11250) * t ^ 7 + (121 / 9375) * t ^ 9 + (158 / 84375) * t ^ 11 + (-284 / 84375) * t ^ 13 + (58 / 375) * alpha * t ^ 3 + (5693 / 33750) * alpha * t ^ 5 + (-3289 / 11250) * alpha * t ^ 7 + (-1057 / 84375) * alpha * t ^ 9 + (158 / 253125) * alpha * t ^ 11 + (-284 / 253125) * alpha * t ^ 13) * c_sq
theorem v45_24 (t : ℂ) : (momentPoly 45 z45 2 4).eval t = ((1556353 / 50) * t ^ 2 + (-31436531 / 200) * t ^ 4 + (490754674009 / 2400000) * t ^ 6 + (-59863966769 / 800000) * t ^ 8 + (-13025075533 / 4800000) * t ^ 10 + (-19534463129 / 14400000) * t ^ 12 + (662963573 / 3600000) * t ^ 14 + (583108733 / 14400000) * t ^ 18 + (-1510179509 / 14400000) * t ^ 20 + (-45944 / 25) * c * t ^ 2 + (63367 / 25) * c * t ^ 4 + (2393099 / 37500) * c * t ^ 6 + (-11033837 / 15000) * c * t ^ 8 + (-1264 / 25) * c * t ^ 10 + (564857 / 25000) * c * t ^ 12 + (-73264 / 9375) * c * t ^ 14 + (13066 / 9375) * c * t ^ 18 + (-12 / 25) * c * t ^ 20 + (8746589 / 150) * alpha * t ^ 2 + (-135779983 / 600) * alpha * t ^ 4 + (208475030317 / 800000) * alpha * t ^ 6 + (-213094842373 / 2400000) * alpha * t ^ 8 + (-3412385169 / 1600000) * alpha * t ^ 10 + (-29504859391 / 14400000) * alpha * t ^ 12 + (225021667 / 3600000) * alpha * t ^ 14 + (225021667 / 14400000) * alpha * t ^ 18 + (-952057891 / 14400000) * alpha * t ^ 20 + (45944 / 75) * alpha * c * t ^ 2 + (-63367 / 75) * alpha * c * t ^ 4 + (-1260869 / 75000) * alpha * c * t ^ 6 + (7133059 / 30000) * alpha * c * t ^ 8 + (508397 / 30000) * alpha * c * t ^ 10 + (-4675171 / 900000) * alpha * c * t ^ 12 + (737983 / 225000) * alpha * c * t ^ 14 + (-277999 / 450000) * alpha * c * t ^ 18 + (31597 / 180000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_03, v44_04, v44_10, v44_11, v44_12, v44_13, v44_14, v44_20, v44_21, v44_22, v44_23, v44_24]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24]
  try simp only [star_one, star_neg]
  linear_combination ((22972 / 225) * t ^ 2 + (-26531 / 125) * t ^ 4 + (383049979 / 2700000) * t ^ 6 + (-508963 / 80000) * t ^ 8 + (-51762353 / 540000) * t ^ 10 + (2920469267 / 36000000) * t ^ 12 + (-80916851 / 9000000) * t ^ 14 + (-18607309 / 9000000) * t ^ 18 + (638151529 / 108000000) * t ^ 20 + (45944 / 225) * c * t ^ 2 + (-53062 / 125) * c * t ^ 4 + (30604567 / 112500) * c * t ^ 6 + (-426419 / 8000) * c * t ^ 8 + (10917419 / 900000) * c * t ^ 10 + (-4035453 / 400000) * c * t ^ 12 + (2722847 / 2700000) * c * t ^ 14 + (-32441 / 337500) * c * t ^ 18 + (69997 / 2160000) * c * t ^ 20 + (22972 / 225) * c ^ 2 * t ^ 2 + (-26531 / 125) * c ^ 2 * t ^ 4 + (351459629 / 2700000) * c ^ 2 * t ^ 6 + (-29023597 / 1350000) * c ^ 2 * t ^ 8 + (1143391 / 600000) * c ^ 2 * t ^ 10 + (-5620457 / 20250000) * c ^ 2 * t ^ 12 + (762739 / 7593750) * c ^ 2 * t ^ 14 + (1839827 / 243000000) * c ^ 2 * t ^ 18 + (-584 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-45944 / 225) * t ^ 2 + (57964 / 125) * t ^ 4 + (-231279427 / 675000) * t ^ 6 + (9909857 / 112500) * t ^ 8 + (-12793603 / 1350000) * t ^ 10 + (7213499 / 1687500) * t ^ 12 + (-561596 / 1265625) * t ^ 14 + (-2409809 / 20250000) * t ^ 18 + (-1168 / 1265625) * t ^ 20 + (-45944 / 225) * alpha * t ^ 2 + (21844 / 45) * alpha * t ^ 4 + (-130341509 / 337500) * alpha * t ^ 6 + (18798721 / 168750) * alpha * t ^ 8 + (-137559 / 12500) * alpha * t ^ 10 + (5354648 / 1265625) * alpha * t ^ 12 + (-153592 / 421875) * alpha * t ^ 14 + (-37298 / 421875) * alpha * t ^ 18 + (-1168 / 1265625) * alpha * t ^ 20) * c_sq
theorem v45_30 (t : ℂ) : (momentPoly 45 z45 3 0).eval t = ((-213 / 200) * t ^ 3 + (213 / 200) * t ^ 5 + (-17449 / 3000) * c * t ^ 3 + (7331 / 1000) * c * t ^ 5 + (71 / 375) * c * t ^ 9 + (-15049 / 3000) * alpha * t ^ 3 + (9731 / 1000) * alpha * t ^ 5 + (221 / 375) * alpha * t ^ 9 + (71 / 200) * alpha * c * t ^ 3 + (-71 / 200) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_10, v44_20, v44_30]
  try simp only [phase43_00, phase43_10, phase43_20, phase43_30]
  try simp only [star_one, star_neg]
  linear_combination ((897 / 2000) * t ^ 3 + (-1481 / 2000) * t ^ 5 + (8089 / 18000) * c * t ^ 3 + (-13297 / 18000) * c * t ^ 5 + (1 / 1125) * c ^ 2 * t ^ 3 + (2 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((4 / 1125) * alpha * t ^ 3 + (8 / 1125) * alpha * t ^ 5) * c_sq
theorem v45_31 (t : ℂ) : (momentPoly 45 z45 3 1).eval t = ((8943 / 50) * t ^ 2 + (-166177 / 200) * t ^ 4 + (2445 / 4) * t ^ 6 + (271 / 200) * t ^ 10 + (-264 / 25) * c * t ^ 2 + (119 / 25) * c * t ^ 4 + (24 / 5) * c * t ^ 6 + (-2 / 25) * c * t ^ 10 + (-16753 / 50) * alpha * t ^ 2 + (665381 / 600) * alpha * t ^ 4 + (-14639 / 20) * alpha * t ^ 6 + (-1523 / 600) * alpha * t ^ 10 + (-88 / 25) * alpha * c * t ^ 2 + (119 / 75) * alpha * c * t ^ 4 + (8 / 5) * alpha * c * t ^ 6 + (-2 / 75) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_10, v44_11, v44_20, v44_21, v44_30, v44_31]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21, phase43_30, phase43_31]
  try simp only [star_one, star_neg]
  linear_combination ((44 / 75) * t ^ 2 + (-617 / 1000) * t ^ 4 + (4633 / 45000) * t ^ 6 + (442 / 16875) * t ^ 10 + (88 / 75) * c * t ^ 2 + (-617 / 500) * c * t ^ 4 + (3749 / 22500) * c * t ^ 6 + (442 / 16875) * c * t ^ 10 + (44 / 75) * c ^ 2 * t ^ 2 + (-617 / 1000) * c ^ 2 * t ^ 4 + (191 / 3000) * c ^ 2 * t ^ 6) * alpha_sq + ((-88 / 75) * t ^ 2 + (337 / 250) * t ^ 4 + (-2857 / 11250) * t ^ 6 + (-142 / 16875) * t ^ 10 + (88 / 75) * alpha * t ^ 2 + (-127 / 90) * alpha * t ^ 4 + (1189 / 3750) * alpha * t ^ 6 + (142 / 16875) * alpha * t ^ 10) * c_sq
theorem v45_32 (t : ℂ) : (momentPoly 45 z45 3 2).eval t = ((35247 / 10) * t + (-141462 / 25) * t ^ 3 + (3795239 / 2400) * t ^ 5 + (2810509 / 6000) * t ^ 7 + (405089 / 4000) * t ^ 9 + (-9631 / 3000) * t ^ 11 + (30751 / 3000) * t ^ 13 + (-11749 / 10) * c * t + (245601 / 100) * c * t ^ 3 + (-32340959 / 20000) * c * t ^ 5 + (3582311 / 10000) * c * t ^ 7 + (-648263 / 20000) * c * t ^ 9 + (15147 / 5000) * c * t ^ 11 + (-5047 / 5000) * c * t ^ 13 + (-11749 / 10) * alpha * t + (182439 / 100) * alpha * t ^ 3 + (-8217759 / 20000) * alpha * t ^ 5 + (-2157289 / 10000) * alpha * t ^ 7 + (-563063 / 20000) * alpha * t ^ 9 + (-503 / 5000) * alpha * t ^ 11 + (-13597 / 5000) * alpha * t ^ 13 + (-11749 / 10) * alpha * c * t + (59856 / 25) * alpha * c * t ^ 3 + (-10792631 / 7200) * alpha * c * t ^ 5 + (5441891 / 18000) * alpha * c * t ^ 7 + (-388049 / 12000) * alpha * c * t ^ 9 + (25021 / 9000) * alpha * c * t ^ 11 + (-11101 / 9000) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_10, v44_11, v44_12, v44_20, v44_21, v44_22, v44_30, v44_31, v44_32]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22, phase43_30, phase43_31, phase43_32]
  try simp only [star_one, star_neg]
  linear_combination ((-78039 / 2000) * t ^ 3 + (196449 / 2000) * t ^ 5 + (-163943 / 3000) * t ^ 7 + (-824389 / 225000) * t ^ 9 + (21827 / 37500) * t ^ 11 + (-327301 / 225000) * t ^ 13 + (-234581 / 6000) * c * t ^ 3 + (5299739 / 54000) * c * t ^ 5 + (-176333 / 3000) * c * t ^ 7 + (805511 / 675000) * c * t ^ 9 + (-603139 / 2025000) * c * t ^ 11 + (884 / 253125) * c * t ^ 13 + (-29 / 375) * c ^ 2 * t ^ 3 + (-274 / 3375) * c ^ 2 * t ^ 5 + (2147 / 13500) * c ^ 2 * t ^ 7 + (-143 / 13500) * c ^ 2 * t ^ 9 + (-2 / 3375) * c ^ 2 * t ^ 11) * alpha_sq + ((58 / 125) * t ^ 3 + (601 / 1250) * t ^ 5 + (-10151 / 11250) * t ^ 7 + (121 / 9375) * t ^ 9 + (158 / 84375) * t ^ 11 + (-284 / 84375) * t ^ 13 + (-58 / 375) * alpha * t ^ 3 + (-5693 / 33750) * alpha * t ^ 5 + (3289 / 11250) * alpha * t ^ 7 + (1057 / 84375) * alpha * t ^ 9 + (-158 / 253125) * alpha * t ^ 11 + (284 / 253125) * alpha * t ^ 13) * c_sq
theorem v45_33 (t : ℂ) : (momentPoly 45 z45 3 3).eval t = (528705 + (-1240488) * t ^ 2 + (1745416311 / 2000) * t ^ 4 + (-3105073 / 20) * t ^ 6 + (15261989 / 400) * t ^ 8 + (-10638699 / 250) * t ^ 10 + (-581641 / 1000) * t ^ 12 + (74959 / 1000) * t ^ 14 + (-36) * t ^ 18 + (9159 / 125) * c * t ^ 4 + (-2627 / 25) * c * t ^ 6 + (-71 / 50) * c * t ^ 8 + (4047 / 125) * c * t ^ 10 + (142 / 125) * c * t ^ 12 + (-71 / 250) * c * t ^ 14) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_03, v44_10, v44_11, v44_12, v44_13, v44_20, v44_21, v44_22, v44_23, v44_30, v44_31, v44_32, v44_33]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23, phase43_30, phase43_31, phase43_32, phase43_33]
  try simp only [star_one, star_neg]
  linear_combination ((-11486 / 75) * t ^ 2 + (30917 / 125) * t ^ 4 + (49330793 / 30000) * t ^ 6 + (-148201729 / 37500) * t ^ 8 + (325789321 / 150000) * t ^ 10 + (184037 / 112500) * t ^ 12 + (35981653 / 3375000) * t ^ 14 + (-195364 / 1265625) * t ^ 18 + (-22972 / 75) * c * t ^ 2 + (213667 / 375) * c * t ^ 4 + (-1370109 / 5000) * c * t ^ 6 + (1130027 / 28125) * c * t ^ 8 + (-6685441 / 225000) * c * t ^ 10 + (8933 / 28125) * c * t ^ 12 + (-6263 / 12500) * c * t ^ 14 + (-11486 / 75) * c ^ 2 * t ^ 2 + (120916 / 375) * c ^ 2 * t ^ 4 + (-55007803 / 270000) * c ^ 2 * t ^ 6 + (5022089 / 135000) * c ^ 2 * t ^ 8 + (-305917 / 90000) * c ^ 2 * t ^ 10 + (26821 / 67500) * c ^ 2 * t ^ 12 + (-10217 / 67500) * c ^ 2 * t ^ 14) * alpha_sq + ((45944 / 75) * t ^ 2 + (-162239 / 125) * t ^ 4 + (18696481 / 22500) * t ^ 6 + (-8795899 / 56250) * t ^ 8 + (501091 / 37500) * t ^ 10 + (-60298 / 28125) * t ^ 12 + (483709 / 421875) * t ^ 14 + (20164 / 1265625) * t ^ 18) * c_sq
theorem v45_34 (t : ℂ) : (momentPoly 45 z45 3 4).eval t = ((6134571 / 10) * t + (-36506952 / 25) * t ^ 3 + (383601107 / 400) * t ^ 5 + (-5067632377 / 150000) * t ^ 7 + (-260126894 / 9375) * t ^ 9 + (-3086904733 / 60000) * t ^ 11 + (9888687791 / 1800000) * t ^ 13 + (-1225413619 / 300000) * t ^ 15 + (-60594827 / 240000) * t ^ 17 + (-18079759 / 450000) * t ^ 19 + (-27332269 / 300000) * t ^ 21 + (-254329 / 28800) * t ^ 25 + (-2044857 / 10) * c * t + (15845499 / 25) * c * t ^ 3 + (-1464004929 / 2000) * c * t ^ 5 + (779216604663 / 2000000) * c * t ^ 7 + (-202200295117 / 2000000) * c * t ^ 9 + (194570872391 / 12000000) * c * t ^ 11 + (-100328657201 / 36000000) * c * t ^ 13 + (2105656697 / 3000000) * c * t ^ 15 + (-320730109 / 6000000) * c * t ^ 17 + (1256618209 / 36000000) * c * t ^ 19 + (-271619699 / 12000000) * c * t ^ 21 + (-15914311 / 18000000) * c * t ^ 25 + (2044857 / 10) * alpha * t + (-11770461 / 25) * alpha * t ^ 3 + (551898489 / 2000) * alpha * t ^ 5 + (61725197263 / 2000000) * alpha * t ^ 7 + (-53045330117 / 2000000) * alpha * t ^ 9 + (-158829189409 / 12000000) * alpha * t ^ 11 + (19732265599 / 36000000) * alpha * t ^ 13 + (-3069274003 / 3000000) * alpha * t ^ 15 + (-799466959 / 6000000) * alpha * t ^ 17 + (-989685191 / 36000000) * alpha * t ^ 19 + (-121610699 / 12000000) * alpha * t ^ 21 + (-34730461 / 18000000) * alpha * t ^ 25 + (2044857 / 10) * alpha * c * t + (-15446976 / 25) * alpha * c * t ^ 3 + (824813123 / 1200) * alpha * c * t ^ 5 + (-26132045333 / 75000) * alpha * c * t ^ 7 + (39836815079 / 450000) * alpha * c * t ^ 9 + (-710446253 / 45000) * alpha * c * t ^ 11 + (14268752509 / 5400000) * alpha * c * t ^ 13 + (-770467331 / 900000) * alpha * c * t ^ 15 + (25745777 / 720000) * alpha * c * t ^ 17 + (-153474607 / 2700000) * alpha * c * t ^ 19 + (19920797 / 450000) * alpha * c * t ^ 21 + (104539 / 86400) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_03, v44_04, v44_10, v44_11, v44_12, v44_13, v44_14, v44_20, v44_21, v44_22, v44_23, v44_24, v44_30, v44_31, v44_32, v44_33, v44_34]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24, phase43_30, phase43_31, phase43_32, phase43_33, phase43_34]
  try simp only [star_one, star_neg]
  linear_combination ((-5034861 / 500) * t ^ 3 + (67735837 / 2000) * t ^ 5 + (-2511392521301 / 72000000) * t ^ 7 + (130922048507 / 14400000) * t ^ 9 + (304822457017 / 144000000) * t ^ 11 + (-348207738283 / 432000000) * t ^ 13 + (67696398023 / 108000000) * t ^ 15 + (11111218559 / 270000000) * t ^ 17 + (-10741395629 / 2160000000) * t ^ 19 + (740527951 / 80000000) * t ^ 21 + (125947237 / 90000000) * t ^ 25 + (-15134519 / 1500) * c * t ^ 3 + (67730941 / 2000) * c * t ^ 5 + (-2665526413493 / 72000000) * c * t ^ 7 + (586807472017 / 43200000) * c * t ^ 9 + (-266517387893 / 432000000) * c * t ^ 11 + (396458116591 / 1296000000) * c * t ^ 13 + (-2173590449 / 108000000) * c * t ^ 15 + (58138793 / 25312500) * c * t ^ 17 + (-59064836053 / 19440000000) * c * t ^ 19 + (34314801503 / 6480000000) * c * t ^ 21 + (129064 / 18984375) * c * t ^ 25 + (-7484 / 375) * c ^ 2 * t ^ 3 + (-306 / 125) * c ^ 2 * t ^ 5 + (430761607 / 6750000) * c ^ 2 * t ^ 7 + (-24935441 / 540000) * c ^ 2 * t ^ 9 + (70104469 / 13500000) * c ^ 2 * t ^ 11 + (-12343483 / 27000000) * c ^ 2 * t ^ 13 + (-19183 / 250000) * c ^ 2 * t ^ 15 + (-10201 / 506250) * c ^ 2 * t ^ 17 + (1376909 / 40500000) * c ^ 2 * t ^ 19 + (-6799 / 600000) * c ^ 2 * t ^ 21) * alpha_sq + ((14968 / 125) * t ^ 3 + (4301 / 375) * t ^ 5 + (-159135121 / 450000) * t ^ 7 + (2107078 / 9375) * t ^ 9 + (-15950303 / 4500000) * t ^ 11 + (-5733467 / 6750000) * t ^ 13 + (4187429 / 1687500) * t ^ 15 + (152624 / 703125) * t ^ 17 + (-56133779 / 202500000) * t ^ 19 + (4151087 / 33750000) * t ^ 21 + (41464 / 6328125) * t ^ 25 + (14968 / 375) * alpha * t ^ 3 + (3043 / 375) * alpha * t ^ 5 + (-29472281 / 250000) * alpha * t ^ 7 + (5244874 / 84375) * alpha * t ^ 9 + (106087279 / 13500000) * alpha * t ^ 11 + (-16699477 / 20250000) * alpha * t ^ 13 + (1301281 / 1687500) * alpha * t ^ 15 + (558692 / 6328125) * alpha * t ^ 17 + (-42465389 / 607500000) * alpha * t ^ 19 + (3731537 / 101250000) * alpha * t ^ 21 + (41464 / 18984375) * alpha * t ^ 25) * c_sq
theorem v45_40 (t : ℂ) : (momentPoly 45 z45 4 0).eval t = ((162867 / 8000) * t ^ 4 + (5223313 / 20000) * t ^ 6 + (-25321799 / 80000) * t ^ 8 + (74327 / 20000) * t ^ 10 + (-396439 / 80000) * t ^ 16 + (-584 / 125) * c * t ^ 4 + (2044 / 625) * c * t ^ 6 + (1752 / 625) * c * t ^ 8 + (1168 / 1875) * c * t ^ 10 + (146 / 1875) * c * t ^ 16 + (1500647 / 24000) * alpha * t ^ 4 + (6877949 / 60000) * alpha * t ^ 6 + (-52156907 / 240000) * alpha * t ^ 8 + (1907953 / 180000) * alpha * t ^ 10 + (-4806961 / 720000) * alpha * t ^ 16 + (242 / 125) * alpha * c * t ^ 4 + (-2399 / 1875) * alpha * c * t ^ 6 + (-2107 / 1875) * alpha * c * t ^ 8 + (-1168 / 5625) * alpha * c * t ^ 10 + (-146 / 5625) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_10, v44_20, v44_30, v44_40]
  try simp only [phase43_00, phase43_10, phase43_20, phase43_30, phase43_40]
  try simp only [star_one, star_neg]
  linear_combination ((413 / 750) * t ^ 4 + (-621181 / 45000) * t ^ 6 + (281707 / 15000) * t ^ 8 + (-1768 / 16875) * t ^ 10 + (584 / 1125) * c * t ^ 4 + (-13109 / 22500) * c * t ^ 6 + (-1481 / 7500) * c * t ^ 8 + (-1768 / 16875) * c * t ^ 10 + (-71 / 2250) * c ^ 2 * t ^ 4 + (1073 / 33750) * c ^ 2 * t ^ 6 + (4 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((242 / 375) * t ^ 4 + (-434 / 625) * t ^ 6 + (8 / 5625) * t ^ 8 + (-568 / 16875) * t ^ 10 + (584 / 1125) * alpha * t ^ 4 + (-3196 / 5625) * alpha * t ^ 6 + (8 / 5625) * alpha * t ^ 8 + (-568 / 16875) * alpha * t ^ 10) * c_sq
theorem v45_41 (t : ℂ) : (momentPoly 45 z45 4 1).eval t = ((-18531 / 100) * t ^ 3 + (13111209 / 40000) * t ^ 5 + (-2404409 / 20000) * t ^ 7 + (-1542481 / 80000) * t ^ 9 + (-209101 / 60000) * t ^ 11 + (123901 / 240000) * t ^ 17 + (-506021 / 500) * c * t ^ 3 + (268768361 / 120000) * c * t ^ 5 + (-25703507 / 20000) * c * t ^ 7 + (9350117 / 80000) * c * t ^ 9 + (-2783983 / 60000) * c * t ^ 11 + (187221 / 80000) * c * t ^ 17 + (-436421 / 500) * alpha * t ^ 3 + (290761079 / 120000) * alpha * t ^ 5 + (-29642413 / 20000) * alpha * t ^ 7 + (6014363 / 80000) * alpha * t ^ 9 + (-1894139 / 20000) * alpha * t ^ 11 + (-187903 / 240000) * alpha * t ^ 17 + (6177 / 100) * alpha * c * t ^ 3 + (-15118391 / 120000) * alpha * c * t ^ 5 + (4411591 / 60000) * alpha * c * t ^ 7 + (-2224081 / 240000) * alpha * c * t ^ 9 + (-38701 / 180000) * alpha * c * t ^ 11 + (123901 / 720000) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_10, v44_11, v44_20, v44_21, v44_30, v44_31, v44_40, v44_41]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21, phase43_30, phase43_31, phase43_40, phase43_41]
  try simp only [star_one, star_neg]
  linear_combination ((78039 / 1000) * t ^ 3 + (-47557027 / 240000) * t ^ 5 + (43385497 / 360000) * t ^ 7 + (-28489579 / 7200000) * t ^ 9 + (2141867 / 1800000) * t ^ 11 + (-569897 / 2400000) * t ^ 17 + (234581 / 3000) * c * t ^ 3 + (-427616059 / 2160000) * c * t ^ 5 + (44815801 / 360000) * c * t ^ 7 + (-178201793 / 21600000) * c * t ^ 9 + (19258627 / 16200000) * c * t ^ 11 + (-15461971 / 64800000) * c * t ^ 17 + (58 / 375) * c ^ 2 * t ^ 3 + (3103 / 16875) * c ^ 2 * t ^ 5 + (-5332 / 16875) * c ^ 2 * t ^ 7 + (-13 / 3125) * c ^ 2 * t ^ 9 + (-284 / 253125) * c ^ 2 * t ^ 11 + (-292 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((-71 / 5625) * t ^ 5 + (-71 / 5625) * t ^ 7 + (142 / 5625) * t ^ 9 + (232 / 375) * alpha * t ^ 3 + (9721 / 16875) * alpha * t ^ 5 + (-7133 / 5625) * alpha * t ^ 7 + (13574 / 84375) * alpha * t ^ 9 + (3536 / 253125) * alpha * t ^ 11 + (1168 / 253125) * alpha * t ^ 17) * c_sq
theorem v45_42 (t : ℂ) : (momentPoly 45 z45 4 2).eval t = ((1556353 / 50) * t ^ 2 + (-31436531 / 200) * t ^ 4 + (490754674009 / 2400000) * t ^ 6 + (-59863966769 / 800000) * t ^ 8 + (-13025075533 / 4800000) * t ^ 10 + (-19534463129 / 14400000) * t ^ 12 + (662963573 / 3600000) * t ^ 14 + (583108733 / 14400000) * t ^ 18 + (-1510179509 / 14400000) * t ^ 20 + (-45944 / 25) * c * t ^ 2 + (63367 / 25) * c * t ^ 4 + (2393099 / 37500) * c * t ^ 6 + (-11033837 / 15000) * c * t ^ 8 + (-1264 / 25) * c * t ^ 10 + (564857 / 25000) * c * t ^ 12 + (-73264 / 9375) * c * t ^ 14 + (13066 / 9375) * c * t ^ 18 + (-12 / 25) * c * t ^ 20 + (-8746589 / 150) * alpha * t ^ 2 + (135779983 / 600) * alpha * t ^ 4 + (-208475030317 / 800000) * alpha * t ^ 6 + (213094842373 / 2400000) * alpha * t ^ 8 + (3412385169 / 1600000) * alpha * t ^ 10 + (29504859391 / 14400000) * alpha * t ^ 12 + (-225021667 / 3600000) * alpha * t ^ 14 + (-225021667 / 14400000) * alpha * t ^ 18 + (952057891 / 14400000) * alpha * t ^ 20 + (-45944 / 75) * alpha * c * t ^ 2 + (63367 / 75) * alpha * c * t ^ 4 + (1260869 / 75000) * alpha * c * t ^ 6 + (-7133059 / 30000) * alpha * c * t ^ 8 + (-508397 / 30000) * alpha * c * t ^ 10 + (4675171 / 900000) * alpha * c * t ^ 12 + (-737983 / 225000) * alpha * c * t ^ 14 + (277999 / 450000) * alpha * c * t ^ 18 + (-31597 / 180000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_10, v44_11, v44_12, v44_20, v44_21, v44_22, v44_30, v44_31, v44_32, v44_40, v44_41, v44_42]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22, phase43_30, phase43_31, phase43_32, phase43_40, phase43_41, phase43_42]
  try simp only [star_one, star_neg]
  linear_combination ((22972 / 225) * t ^ 2 + (-26531 / 125) * t ^ 4 + (383049979 / 2700000) * t ^ 6 + (-508963 / 80000) * t ^ 8 + (-51762353 / 540000) * t ^ 10 + (2920469267 / 36000000) * t ^ 12 + (-80916851 / 9000000) * t ^ 14 + (-18607309 / 9000000) * t ^ 18 + (638151529 / 108000000) * t ^ 20 + (45944 / 225) * c * t ^ 2 + (-53062 / 125) * c * t ^ 4 + (30604567 / 112500) * c * t ^ 6 + (-426419 / 8000) * c * t ^ 8 + (10917419 / 900000) * c * t ^ 10 + (-4035453 / 400000) * c * t ^ 12 + (2722847 / 2700000) * c * t ^ 14 + (-32441 / 337500) * c * t ^ 18 + (69997 / 2160000) * c * t ^ 20 + (22972 / 225) * c ^ 2 * t ^ 2 + (-26531 / 125) * c ^ 2 * t ^ 4 + (351459629 / 2700000) * c ^ 2 * t ^ 6 + (-29023597 / 1350000) * c ^ 2 * t ^ 8 + (1143391 / 600000) * c ^ 2 * t ^ 10 + (-5620457 / 20250000) * c ^ 2 * t ^ 12 + (762739 / 7593750) * c ^ 2 * t ^ 14 + (1839827 / 243000000) * c ^ 2 * t ^ 18 + (-584 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-45944 / 225) * t ^ 2 + (57964 / 125) * t ^ 4 + (-231279427 / 675000) * t ^ 6 + (9909857 / 112500) * t ^ 8 + (-12793603 / 1350000) * t ^ 10 + (7213499 / 1687500) * t ^ 12 + (-561596 / 1265625) * t ^ 14 + (-2409809 / 20250000) * t ^ 18 + (-1168 / 1265625) * t ^ 20 + (45944 / 225) * alpha * t ^ 2 + (-21844 / 45) * alpha * t ^ 4 + (130341509 / 337500) * alpha * t ^ 6 + (-18798721 / 168750) * alpha * t ^ 8 + (137559 / 12500) * alpha * t ^ 10 + (-5354648 / 1265625) * alpha * t ^ 12 + (153592 / 421875) * alpha * t ^ 14 + (37298 / 421875) * alpha * t ^ 18 + (1168 / 1265625) * alpha * t ^ 20) * c_sq
theorem v45_43 (t : ℂ) : (momentPoly 45 z45 4 3).eval t = ((6134571 / 10) * t + (-36506952 / 25) * t ^ 3 + (383601107 / 400) * t ^ 5 + (-5067632377 / 150000) * t ^ 7 + (-260126894 / 9375) * t ^ 9 + (-3086904733 / 60000) * t ^ 11 + (9888687791 / 1800000) * t ^ 13 + (-1225413619 / 300000) * t ^ 15 + (-60594827 / 240000) * t ^ 17 + (-18079759 / 450000) * t ^ 19 + (-27332269 / 300000) * t ^ 21 + (-254329 / 28800) * t ^ 25 + (-2044857 / 10) * c * t + (15845499 / 25) * c * t ^ 3 + (-1464004929 / 2000) * c * t ^ 5 + (779216604663 / 2000000) * c * t ^ 7 + (-202200295117 / 2000000) * c * t ^ 9 + (194570872391 / 12000000) * c * t ^ 11 + (-100328657201 / 36000000) * c * t ^ 13 + (2105656697 / 3000000) * c * t ^ 15 + (-320730109 / 6000000) * c * t ^ 17 + (1256618209 / 36000000) * c * t ^ 19 + (-271619699 / 12000000) * c * t ^ 21 + (-15914311 / 18000000) * c * t ^ 25 + (-2044857 / 10) * alpha * t + (11770461 / 25) * alpha * t ^ 3 + (-551898489 / 2000) * alpha * t ^ 5 + (-61725197263 / 2000000) * alpha * t ^ 7 + (53045330117 / 2000000) * alpha * t ^ 9 + (158829189409 / 12000000) * alpha * t ^ 11 + (-19732265599 / 36000000) * alpha * t ^ 13 + (3069274003 / 3000000) * alpha * t ^ 15 + (799466959 / 6000000) * alpha * t ^ 17 + (989685191 / 36000000) * alpha * t ^ 19 + (121610699 / 12000000) * alpha * t ^ 21 + (34730461 / 18000000) * alpha * t ^ 25 + (-2044857 / 10) * alpha * c * t + (15446976 / 25) * alpha * c * t ^ 3 + (-824813123 / 1200) * alpha * c * t ^ 5 + (26132045333 / 75000) * alpha * c * t ^ 7 + (-39836815079 / 450000) * alpha * c * t ^ 9 + (710446253 / 45000) * alpha * c * t ^ 11 + (-14268752509 / 5400000) * alpha * c * t ^ 13 + (770467331 / 900000) * alpha * c * t ^ 15 + (-25745777 / 720000) * alpha * c * t ^ 17 + (153474607 / 2700000) * alpha * c * t ^ 19 + (-19920797 / 450000) * alpha * c * t ^ 21 + (-104539 / 86400) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_03, v44_10, v44_11, v44_12, v44_13, v44_20, v44_21, v44_22, v44_23, v44_30, v44_31, v44_32, v44_33, v44_40, v44_41, v44_42, v44_43]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23, phase43_30, phase43_31, phase43_32, phase43_33, phase43_40, phase43_41, phase43_42, phase43_43]
  try simp only [star_one, star_neg]
  linear_combination ((-5034861 / 500) * t ^ 3 + (67735837 / 2000) * t ^ 5 + (-2511392521301 / 72000000) * t ^ 7 + (130922048507 / 14400000) * t ^ 9 + (304822457017 / 144000000) * t ^ 11 + (-348207738283 / 432000000) * t ^ 13 + (67696398023 / 108000000) * t ^ 15 + (11111218559 / 270000000) * t ^ 17 + (-10741395629 / 2160000000) * t ^ 19 + (740527951 / 80000000) * t ^ 21 + (125947237 / 90000000) * t ^ 25 + (-15134519 / 1500) * c * t ^ 3 + (67730941 / 2000) * c * t ^ 5 + (-2665526413493 / 72000000) * c * t ^ 7 + (586807472017 / 43200000) * c * t ^ 9 + (-266517387893 / 432000000) * c * t ^ 11 + (396458116591 / 1296000000) * c * t ^ 13 + (-2173590449 / 108000000) * c * t ^ 15 + (58138793 / 25312500) * c * t ^ 17 + (-59064836053 / 19440000000) * c * t ^ 19 + (34314801503 / 6480000000) * c * t ^ 21 + (129064 / 18984375) * c * t ^ 25 + (-7484 / 375) * c ^ 2 * t ^ 3 + (-306 / 125) * c ^ 2 * t ^ 5 + (430761607 / 6750000) * c ^ 2 * t ^ 7 + (-24935441 / 540000) * c ^ 2 * t ^ 9 + (70104469 / 13500000) * c ^ 2 * t ^ 11 + (-12343483 / 27000000) * c ^ 2 * t ^ 13 + (-19183 / 250000) * c ^ 2 * t ^ 15 + (-10201 / 506250) * c ^ 2 * t ^ 17 + (1376909 / 40500000) * c ^ 2 * t ^ 19 + (-6799 / 600000) * c ^ 2 * t ^ 21) * alpha_sq + ((14968 / 125) * t ^ 3 + (4301 / 375) * t ^ 5 + (-159135121 / 450000) * t ^ 7 + (2107078 / 9375) * t ^ 9 + (-15950303 / 4500000) * t ^ 11 + (-5733467 / 6750000) * t ^ 13 + (4187429 / 1687500) * t ^ 15 + (152624 / 703125) * t ^ 17 + (-56133779 / 202500000) * t ^ 19 + (4151087 / 33750000) * t ^ 21 + (41464 / 6328125) * t ^ 25 + (-14968 / 375) * alpha * t ^ 3 + (-3043 / 375) * alpha * t ^ 5 + (29472281 / 250000) * alpha * t ^ 7 + (-5244874 / 84375) * alpha * t ^ 9 + (-106087279 / 13500000) * alpha * t ^ 11 + (16699477 / 20250000) * alpha * t ^ 13 + (-1301281 / 1687500) * alpha * t ^ 15 + (-558692 / 6328125) * alpha * t ^ 17 + (42465389 / 607500000) * alpha * t ^ 19 + (-3731537 / 101250000) * alpha * t ^ 21 + (-41464 / 18984375) * alpha * t ^ 25) * c_sq
theorem v45_44 (t : ℂ) : (momentPoly 45 z45 4 4).eval t = (92018565 + (-284611104) * t ^ 2 + (148414507871 / 500) * t ^ 4 + (-53769423959 / 500) * t ^ 6 + (739790076763451 / 48000000) * t ^ 8 + (-1399107814847939 / 60000000) * t ^ 10 + (2470750988061469 / 240000000) * t ^ 12 + (365231533097611 / 360000000) * t ^ 14 + (-8408782693459 / 115200000) * t ^ 16 + (-14261428775941 / 360000000) * t ^ 18 + (32837019312389 / 2160000000) * t ^ 20 + (-2690210725327 / 360000000) * t ^ 22 + (14968497270949 / 1440000000) * t ^ 24 + (154740584209 / 1080000000) * t ^ 26 + (994221257423 / 8640000000) * t ^ 32 + (3115196 / 125) * c * t ^ 4 + (-7307249 / 125) * c * t ^ 6 + (24074599369 / 750000) * c * t ^ 8 + (78883741487 / 7500000) * c * t ^ 10 + (-1264197361 / 156250) * c * t ^ 12 + (-44427498733 / 45000000) * c * t ^ 14 + (1505072831 / 9000000) * c * t ^ 16 + (-1908909583 / 11250000) * c * t ^ 18 + (-3233637073 / 67500000) * c * t ^ 20 + (1951385951 / 45000000) * c * t ^ 22 + (131355427 / 45000000) * c * t ^ 24 + (9044773 / 8437500) * c * t ^ 26 + (9044773 / 33750000) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_03, v44_04, v44_10, v44_11, v44_12, v44_13, v44_14, v44_20, v44_21, v44_22, v44_23, v44_24, v44_30, v44_31, v44_32, v44_33, v44_34, v44_40, v44_41, v44_42, v44_43, v44_44]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24, phase43_30, phase43_31, phase43_32, phase43_33, phase43_34, phase43_40, phase43_41, phase43_42, phase43_43, phase43_44]
  try simp only [star_one, star_neg]
  linear_combination ((-2635288 / 75) * t ^ 2 + (31546844 / 375) * t ^ 4 + (1329492047 / 2500) * t ^ 6 + (-4149035379439 / 2250000) * t ^ 8 + (56647050828679 / 30000000) * t ^ 10 + (-18288831469097 / 30000000) * t ^ 12 + (-218170843577 / 64800000) * t ^ 14 + (-7026422991397 / 540000000) * t ^ 16 + (94592366837 / 135000000) * t ^ 18 + (2759349931 / 45000000) * t ^ 20 + (205193173441 / 540000000) * t ^ 22 + (-146429564131 / 300000000) * t ^ 24 + (17908486903 / 1012500000) * t ^ 26 + (-22572245017 / 4050000000) * t ^ 32 + (-5270576 / 75) * c * t ^ 2 + (218019844 / 1125) * c * t ^ 4 + (-677073707 / 3750) * c * t ^ 6 + (485687088151 / 6750000) * c * t ^ 8 + (-3486567357961 / 135000000) * c * t ^ 10 + (58991595193 / 5400000) * c * t ^ 12 + (-70028400893 / 162000000) * c * t ^ 14 + (33850978133 / 90000000) * c * t ^ 16 + (5462867491 / 202500000) * c * t ^ 18 + (7837750087 / 607500000) * c * t ^ 20 + (-3540767749 / 810000000) * c * t ^ 22 + (-94617559 / 450000000) * c * t ^ 24 + (28922431 / 126562500) * c * t ^ 26 + (-41602481 / 337500000) * c * t ^ 32 + (-2635288 / 75) * c ^ 2 * t ^ 2 + (123379312 / 1125) * c ^ 2 * t ^ 4 + (-2103422858 / 16875) * c ^ 2 * t ^ 6 + (315756815951 / 5062500) * c ^ 2 * t ^ 8 + (-239662363309 / 16875000) * c ^ 2 * t ^ 10 + (37948632649 / 16875000) * c ^ 2 * t ^ 12 + (-45346898687 / 101250000) * c ^ 2 * t ^ 14 + (3601552979 / 25312500) * c ^ 2 * t ^ 16 + (-534625657 / 101250000) * c ^ 2 * t ^ 18 + (1528869881 / 151875000) * c ^ 2 * t ^ 20 + (-673963697 / 101250000) * c ^ 2 * t ^ 22 + (-6770671 / 379687500) * c ^ 2 * t ^ 24 + (-904510021 / 4556250000) * c ^ 2 * t ^ 26 + (-85264 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((10541152 / 75) * t ^ 2 + (-165544148 / 375) * t ^ 4 + (2849484386 / 5625) * t ^ 6 + (-1734731561561 / 6750000) * t ^ 8 + (664153617817 / 11250000) * t ^ 10 + (-42005658449 / 4500000) * t ^ 12 + (517263967129 / 202500000) * t ^ 14 + (-15986577677 / 16875000) * t ^ 16 + (497968031 / 8437500) * t ^ 18 + (-10644954833 / 202500000) * t ^ 20 + (1550546279 / 67500000) * t ^ 22 + (23965519 / 126562500) * t ^ 24 + (558037591 / 379687500) * t ^ 26 + (341056 / 94921875) * t ^ 32) * c_sq
#print axioms v45_00
#print axioms v45_11
#print axioms v45_22
#print axioms v45_33
#print axioms v45_44
end PhotonCertA
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z46 : Fin 46 → ℂ := Fin.snoc z45 (r ^ 3 * thetaPlus)
theorem v46_00 (t : ℂ) : (momentPoly 46 z46 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00]
  try simp only [phase43_00]
  try simp only [star_one, star_neg]
  ring
theorem v46_01 (t : ℂ) : (momentPoly 46 z46 0 1).eval t = ((2 / 5) * t + (-2 / 15) * c * t + (2 / 15) * alpha * t + (2 / 15) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01]
  try simp only [phase43_00, phase43_01]
  try simp only [star_one, star_neg]
  ring
theorem v46_02 (t : ℂ) : (momentPoly 46 z46 0 2).eval t = ((-313 / 200) * t ^ 2 + (-3733 / 600) * t ^ 4 + (-4 / 25) * c * t ^ 2 + (-4 / 75) * c * t ^ 4 + (-229 / 600) * alpha * t ^ 2 + (-1481 / 200) * alpha * t ^ 4 + (4 / 75) * alpha * c * t ^ 2 + (4 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02]
  try simp only [phase43_00, phase43_01, phase43_02]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 150) * t ^ 2 + (1 / 75) * c * t ^ 2 + (1 / 150) * c ^ 2 * t ^ 2) * alpha_sq + ((-1 / 75) * t ^ 2 + (-1 / 75) * alpha * t ^ 2) * c_sq
theorem v46_03 (t : ℂ) : (momentPoly 46 z46 0 3).eval t = ((-71 / 50) * t ^ 3 + (71 / 50) * t ^ 5 + (-5059 / 750) * c * t ^ 3 + (2633 / 250) * c * t ^ 5 + (284 / 1125) * c * t ^ 9 + (2659 / 750) * alpha * t ^ 3 + (-3833 / 250) * alpha * t ^ 5 + (-884 / 1125) * alpha * t ^ 9 + (-71 / 150) * alpha * c * t ^ 3 + (71 / 150) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_03]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03]
  try simp only [star_one, star_neg]
  linear_combination ((1523 / 6000) * t ^ 3 + (-5027 / 6000) * t ^ 5 + (513 / 2000) * c * t ^ 3 + (-5011 / 6000) * c * t ^ 5 + (1 / 375) * c ^ 2 * t ^ 3 + (1 / 375) * c ^ 2 * t ^ 5) * alpha_sq + ((-4 / 375) * alpha * t ^ 3 + (-4 / 375) * alpha * t ^ 5) * c_sq
theorem v46_04 (t : ℂ) : (momentPoly 46 z46 0 4).eval t = ((26593597 / 120000) * t ^ 4 + (723777 / 20000) * t ^ 6 + (-28792583 / 80000) * t ^ 8 + (-421243 / 60000) * t ^ 10 + (-3890063 / 720000) * t ^ 16 + (-16352 / 1875) * c * t ^ 4 + (18688 / 1875) * c * t ^ 6 + (7592 / 1875) * c * t ^ 8 + (2336 / 1875) * c * t ^ 10 + (584 / 5625) * c * t ^ 16 + (-26678147 / 120000) * alpha * t ^ 4 + (4547459 / 60000) * alpha * t ^ 6 + (60910699 / 240000) * alpha * t ^ 8 + (24719 / 180000) * alpha * t ^ 10 + (569897 / 80000) * alpha * t ^ 16 + (-20612 / 5625) * alpha * c * t ^ 4 + (2392 / 625) * alpha * c * t ^ 6 + (3004 / 1875) * alpha * c * t ^ 8 + (2336 / 5625) * alpha * c * t ^ 10 + (584 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_03, v45_04]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04]
  try simp only [star_one, star_neg]
  linear_combination ((15049 / 22500) * t ^ 4 + (-43547 / 5000) * t ^ 6 + (303023 / 15000) * t ^ 8 + (-884 / 5625) * t ^ 10 + (3496 / 5625) * c * t ^ 4 + (-28357 / 22500) * c * t ^ 6 + (-5027 / 22500) * c * t ^ 8 + (-884 / 5625) * c * t ^ 10 + (-71 / 1500) * c ^ 2 * t ^ 4 + (1081 / 22500) * c ^ 2 * t ^ 6 + (2 / 5625) * c ^ 2 * t ^ 8) * alpha_sq + ((5161 / 5625) * t ^ 4 + (-697 / 625) * t ^ 6 + (4 / 1875) * t ^ 8 + (-284 / 5625) * t ^ 10 + (-4096 / 5625) * alpha * t ^ 4 + (1736 / 1875) * alpha * t ^ 6 + (-4 / 1875) * alpha * t ^ 8 + (284 / 5625) * alpha * t ^ 10) * c_sq
theorem v46_10 (t : ℂ) : (momentPoly 46 z46 1 0).eval t = ((2 / 5) * t + (-2 / 15) * c * t + (-2 / 15) * alpha * t + (-2 / 15) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_10]
  try simp only [phase43_00, phase43_10]
  try simp only [star_one, star_neg]
  ring
theorem v46_11 (t : ℂ) : (momentPoly 46 z46 1 1).eval t = (46 + (-30) * t ^ 2) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_10, v45_11]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 150) * t ^ 2 + (-1 / 75) * c * t ^ 2 + (-1 / 150) * c ^ 2 * t ^ 2) * alpha_sq + ((2 / 75) * t ^ 2) * c_sq
theorem v46_12 (t : ℂ) : (momentPoly 46 z46 1 2).eval t = ((182 / 5) * t + (-2048 / 75) * t ^ 3 + (-202 / 75) * t ^ 5 + (-182 / 15) * c * t + (901 / 75) * c * t ^ 3 + (-151 / 75) * c * t ^ 5 + (182 / 15) * alpha * t + (-659 / 75) * alpha * t ^ 3 + (-91 / 75) * alpha * t ^ 5 + (182 / 15) * alpha * c * t + (-2632 / 225) * alpha * c * t ^ 3 + (382 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_10, v45_11, v45_12]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12]
  try simp only [star_one, star_neg]
  linear_combination ((-1523 / 18000) * t ^ 3 + (5027 / 18000) * t ^ 5 + (-171 / 2000) * c * t ^ 3 + (5011 / 18000) * c * t ^ 5 + (-1 / 1125) * c ^ 2 * t ^ 3 + (-1 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((2 / 375) * t ^ 3 + (2 / 375) * t ^ 5 + (2 / 1125) * alpha * t ^ 3 + (2 / 1125) * alpha * t ^ 5) * c_sq
theorem v46_13 (t : ℂ) : (momentPoly 46 z46 1 3).eval t = ((-8451 / 40) * t ^ 2 + (-72163 / 150) * t ^ 4 + (28467 / 50) * t ^ 6 + (-313 / 200) * t ^ 10 + (-108 / 5) * c * t ^ 2 + (944 / 75) * c * t ^ 4 + (144 / 25) * c * t ^ 6 + (-4 / 25) * c * t ^ 10 + (-2061 / 40) * alpha * t ^ 2 + (-37071 / 50) * alpha * t ^ 4 + (33437 / 50) * alpha * t ^ 6 + (-229 / 600) * alpha * t ^ 10 + (36 / 5) * alpha * c * t ^ 2 + (-944 / 225) * alpha * c * t ^ 4 + (-48 / 25) * alpha * c * t ^ 6 + (4 / 75) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_03, v45_10, v45_11, v45_12, v45_13]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13]
  try simp only [star_one, star_neg]
  linear_combination ((9 / 10) * t ^ 2 + (-77959 / 90000) * t ^ 4 + (6701 / 30000) * t ^ 6 + (221 / 5625) * t ^ 10 + (9 / 5) * c * t ^ 2 + (-79727 / 45000) * c * t ^ 4 + (4933 / 15000) * c * t ^ 6 + (221 / 5625) * c * t ^ 10 + (9 / 10) * c ^ 2 * t ^ 2 + (-1811 / 2000) * c ^ 2 * t ^ 4 + (211 / 2000) * c ^ 2 * t ^ 6) * alpha_sq + ((-9 / 5) * t ^ 2 + (44311 / 22500) * t ^ 4 + (-3149 / 7500) * t ^ 6 + (-71 / 5625) * t ^ 10 + (-9 / 5) * alpha * t ^ 2 + (46441 / 22500) * alpha * t ^ 4 + (-3859 / 7500) * alpha * t ^ 6 + (-71 / 5625) * alpha * t ^ 10) * c_sq
theorem v46_14 (t : ℂ) : (momentPoly 46 z46 1 4).eval t = ((-6319 / 25) * t ^ 3 + (4313603 / 10000) * t ^ 5 + (-2276609 / 15000) * t ^ 7 + (-1372081 / 60000) * t ^ 9 + (-209101 / 45000) * t ^ 11 + (123901 / 180000) * t ^ 17 + (-450251 / 375) * c * t ^ 3 + (87765187 / 30000) * c * t ^ 5 + (-26732267 / 15000) * c * t ^ 7 + (31750991 / 180000) * c * t ^ 9 + (-2602223 / 45000) * c * t ^ 11 + (607103 / 180000) * c * t ^ 17 + (236651 / 375) * alpha * t ^ 3 + (-31112031 / 10000) * alpha * t ^ 5 + (34415173 / 15000) * alpha * t ^ 7 + (-23279729 / 180000) * alpha * t ^ 9 + (5116657 / 45000) * alpha * t ^ 11 + (46463 / 180000) * alpha * t ^ 17 + (-6319 / 75) * alpha * c * t ^ 3 + (14947991 / 90000) * alpha * c * t ^ 5 + (-4283791 / 45000) * alpha * c * t ^ 7 + (2394481 / 180000) * alpha * c * t ^ 9 + (38701 / 135000) * alpha * c * t ^ 11 + (-123901 / 540000) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_03, v45_04, v45_10, v45_11, v45_12, v45_13, v45_14]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14]
  try simp only [star_one, star_neg]
  linear_combination ((135547 / 3000) * t ^ 3 + (-41602691 / 240000) * t ^ 5 + (219285389 / 1800000) * t ^ 7 + (-30922667 / 7200000) * t ^ 9 + (3735553 / 5400000) * t ^ 11 + (-5773297 / 21600000) * t ^ 17 + (45657 / 1000) * c * t ^ 3 + (-124739849 / 720000) * c * t ^ 5 + (229964701 / 1800000) * c * t ^ 7 + (-77288683 / 7200000) * c * t ^ 9 + (3717377 / 5400000) * c * t ^ 11 + (-1936891 / 7200000) * c * t ^ 17 + (178 / 375) * c ^ 2 * t ^ 3 + (533 / 5625) * c ^ 2 * t ^ 5 + (-28159 / 56250) * c ^ 2 * t ^ 7 + (-347 / 56250) * c ^ 2 * t ^ 9 + (-284 / 84375) * c ^ 2 * t ^ 11 + (-146 / 84375) * c ^ 2 * t ^ 17) * alpha_sq + ((-71 / 1875) * t ^ 5 + (71 / 1875) * t ^ 9 + (-712 / 375) * alpha * t ^ 3 + (559 / 5625) * alpha * t ^ 5 + (47432 / 28125) * alpha * t ^ 7 + (-7379 / 28125) * alpha * t ^ 9 + (-3536 / 84375) * alpha * t ^ 11 + (-584 / 84375) * alpha * t ^ 17) * c_sq
theorem v46_20 (t : ℂ) : (momentPoly 46 z46 2 0).eval t = ((-313 / 200) * t ^ 2 + (-3733 / 600) * t ^ 4 + (-4 / 25) * c * t ^ 2 + (-4 / 75) * c * t ^ 4 + (229 / 600) * alpha * t ^ 2 + (1481 / 200) * alpha * t ^ 4 + (-4 / 75) * alpha * c * t ^ 2 + (-4 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_10, v45_20]
  try simp only [phase43_00, phase43_10, phase43_20]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 150) * t ^ 2 + (1 / 75) * c * t ^ 2 + (1 / 150) * c ^ 2 * t ^ 2) * alpha_sq + ((-1 / 75) * t ^ 2 + (1 / 75) * alpha * t ^ 2) * c_sq
theorem v46_21 (t : ℂ) : (momentPoly 46 z46 2 1).eval t = ((182 / 5) * t + (-2048 / 75) * t ^ 3 + (-202 / 75) * t ^ 5 + (-182 / 15) * c * t + (901 / 75) * c * t ^ 3 + (-151 / 75) * c * t ^ 5 + (-182 / 15) * alpha * t + (659 / 75) * alpha * t ^ 3 + (91 / 75) * alpha * t ^ 5 + (-182 / 15) * alpha * c * t + (2632 / 225) * alpha * c * t ^ 3 + (-382 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_10, v45_11, v45_20, v45_21]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21]
  try simp only [star_one, star_neg]
  linear_combination ((-1523 / 18000) * t ^ 3 + (5027 / 18000) * t ^ 5 + (-171 / 2000) * c * t ^ 3 + (5011 / 18000) * c * t ^ 5 + (-1 / 1125) * c ^ 2 * t ^ 3 + (-1 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((2 / 375) * t ^ 3 + (2 / 375) * t ^ 5 + (-2 / 1125) * alpha * t ^ 3 + (-2 / 1125) * alpha * t ^ 5) * c_sq
theorem v46_22 (t : ℂ) : (momentPoly 46 z46 2 2).eval t = (4186 + (-5400) * t ^ 2 + (6902783 / 6000) * t ^ 4 + (161483 / 1000) * t ^ 6 + (948319 / 6000) * t ^ 8 + (142 / 375) * c * t ^ 4 + (-284 / 1125) * c * t ^ 6 + (-142 / 1125) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_10, v45_11, v45_12, v45_20, v45_21, v45_22]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22]
  try simp only [star_one, star_neg]
  linear_combination ((-6 / 5) * t ^ 2 + (233 / 250) * t ^ 4 + (117239 / 45000) * t ^ 6 + (-303023 / 45000) * t ^ 8 + (-12 / 5) * c * t ^ 2 + (4849 / 2250) * c * t ^ 4 + (-1241 / 67500) * c * t ^ 6 + (5027 / 67500) * c * t ^ 8 + (-6 / 5) * c ^ 2 * t ^ 2 + (1376 / 1125) * c ^ 2 * t ^ 4 + (-2644 / 16875) * c ^ 2 * t ^ 6 + (-2 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((24 / 5) * t ^ 2 + (-1231 / 250) * t ^ 4 + (7427 / 11250) * t ^ 6 + (8 / 5625) * t ^ 8) * c_sq
theorem v46_23 (t : ℂ) : (momentPoly 46 z46 2 3).eval t = ((24572 / 5) * t + (-182272 / 25) * t ^ 3 + (5368673 / 3000) * t ^ 5 + (766777 / 1500) * t ^ 7 + (166751 / 1000) * t ^ 9 + (-6031 / 2250) * t ^ 11 + (31651 / 2250) * t ^ 13 + (-24572 / 15) * c * t + (80189 / 25) * c * t ^ 3 + (-10225669 / 5000) * c * t ^ 5 + (3693317 / 7500) * c * t ^ 7 + (-793427 / 15000) * c * t ^ 9 + (13147 / 3750) * c * t ^ 11 + (-1849 / 1250) * c * t ^ 13 + (24572 / 15) * alpha * t + (-58651 / 25) * alpha * t ^ 3 + (6707407 / 15000) * alpha * t ^ 5 + (1845583 / 7500) * alpha * t ^ 7 + (665627 / 15000) * alpha * t ^ 9 + (2503 / 3750) * alpha * t ^ 11 + (4699 / 1250) * alpha * t ^ 13 + (24572 / 15) * alpha * c * t + (-234248 / 75) * alpha * c * t ^ 3 + (5665211 / 3000) * alpha * c * t ^ 5 + (-1892003 / 4500) * alpha * c * t ^ 7 + (158231 / 3000) * alpha * c * t ^ 9 + (-21421 / 6750) * alpha * c * t ^ 11 + (12001 / 6750) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_03, v45_10, v45_11, v45_12, v45_13, v45_20, v45_21, v45_22, v45_23]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23]
  try simp only [star_one, star_neg]
  linear_combination ((-135547 / 6000) * t ^ 3 + (1578859 / 18000) * t ^ 5 + (-25452353 / 450000) * t ^ 7 + (-931553 / 150000) * t ^ 9 + (111179 / 337500) * t ^ 11 + (-1110967 / 675000) * t ^ 13 + (-45657 / 2000) * c * t ^ 3 + (1578587 / 18000) * c * t ^ 5 + (-83949653 / 1350000) * c * t ^ 7 + (874147 / 450000) * c * t ^ 9 + (-111889 / 675000) * c * t ^ 11 + (442 / 84375) * c * t ^ 13 + (-89 / 375) * c ^ 2 * t ^ 3 + (-17 / 1125) * c ^ 2 * t ^ 5 + (83 / 360) * c ^ 2 * t ^ 7 + (-31 / 1800) * c ^ 2 * t ^ 9 + (-2 / 1125) * c ^ 2 * t ^ 11) * alpha_sq + ((178 / 125) * t ^ 3 + (269 / 3750) * t ^ 5 + (-36592 / 28125) * t ^ 7 + (371 / 18750) * t ^ 9 + (158 / 28125) * t ^ 11 + (-142 / 28125) * t ^ 13 + (178 / 375) * alpha * t ^ 3 + (553 / 11250) * alpha * t ^ 5 + (-36592 / 84375) * alpha * t ^ 7 + (-1049 / 56250) * alpha * t ^ 9 + (158 / 84375) * alpha * t ^ 11 + (-142 / 84375) * alpha * t ^ 13) * c_sq
theorem v46_24 (t : ℂ) : (momentPoly 46 z46 2 4).eval t = ((-3761321 / 100) * t ^ 2 + (-13950931 / 600) * t ^ 4 + (275723672489 / 2400000) * t ^ 6 + (-23498937727 / 480000) * t ^ 8 + (-2076237139 / 320000) * t ^ 10 + (-7116149297 / 14400000) * t ^ 12 + (155936813 / 3600000) * t ^ 14 + (1552517 / 1600000) * t ^ 18 + (-190778053 / 1600000) * t ^ 20 + (-96136 / 25) * c * t ^ 2 + (426212 / 75) * c * t ^ 4 + (-58719647 / 56250) * c * t ^ 6 + (-8599243 / 11250) * c * t ^ 8 + (-6472069 / 56250) * c * t ^ 10 + (2544043 / 56250) * c * t ^ 12 + (-1292224 / 84375) * c * t ^ 14 + (179056 / 84375) * c * t ^ 18 + (-52 / 75) * c * t ^ 20 + (-2751893 / 300) * alpha * t ^ 2 + (-17420607 / 200) * alpha * t ^ 4 + (1132195045813 / 7200000) * alpha * t ^ 6 + (-1766655743 / 32000) * alpha * t ^ 8 + (-18176044421 / 2880000) * alpha * t ^ 10 + (-18652246943 / 14400000) * alpha * t ^ 12 + (-643934039 / 10800000) * alpha * t ^ 14 + (-643934039 / 43200000) * alpha * t ^ 18 + (-3358544489 / 43200000) * alpha * t ^ 20 + (96136 / 75) * alpha * c * t ^ 2 + (-426212 / 225) * alpha * c * t ^ 4 + (40094737 / 112500) * alpha * c * t ^ 6 + (5343013 / 22500) * alpha * c * t ^ 8 + (3224051 / 75000) * alpha * c * t ^ 10 + (-2654381 / 225000) * alpha * c * t ^ 12 + (356213 / 56250) * alpha * c * t ^ 14 + (-656669 / 675000) * alpha * c * t ^ 18 + (33997 / 135000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_03, v45_04, v45_10, v45_11, v45_12, v45_13, v45_14, v45_20, v45_21, v45_22, v45_23, v45_24]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24]
  try simp only [star_one, star_neg]
  linear_combination ((12017 / 75) * t ^ 2 + (-1715098 / 5625) * t ^ 4 + (390982427 / 1800000) * t ^ 6 + (-72341263 / 720000) * t ^ 8 + (-239464783 / 6000000) * t ^ 10 + (3382907291 / 36000000) * t ^ 12 + (-150918889 / 27000000) * t ^ 14 + (-64140617 / 54000000) * t ^ 18 + (685179881 / 108000000) * t ^ 20 + (24034 / 75) * c * t ^ 2 + (-3507988 / 5625) * c * t ^ 4 + (276141751 / 675000) * c * t ^ 6 + (-21223403 / 200000) * c * t ^ 8 + (55898149 / 2700000) * c * t ^ 10 + (-154575919 / 10800000) * c * t ^ 12 + (12937229 / 8100000) * c * t ^ 14 + (-75547 / 1012500) * c * t ^ 18 + (79597 / 2160000) * c * t ^ 20 + (12017 / 75) * c ^ 2 * t ^ 2 + (-39842 / 125) * c ^ 2 * t ^ 4 + (1036186727 / 5400000) * c ^ 2 * t ^ 6 + (-19115963 / 540000) * c ^ 2 * t ^ 8 + (199161113 / 54000000) * c ^ 2 * t ^ 10 + (-1755043 / 4500000) * c ^ 2 * t ^ 12 + (827903 / 5062500) * c ^ 2 * t ^ 14 + (1821139 / 162000000) * c ^ 2 * t ^ 18 + (-292 / 1265625) * c ^ 2 * t ^ 20) * alpha_sq + ((-24034 / 75) * t ^ 2 + (3899368 / 5625) * t ^ 4 + (-45880391 / 90000) * t ^ 6 + (32436259 / 225000) * t ^ 8 + (-25282757 / 1500000) * t ^ 10 + (2326921 / 375000) * t ^ 12 + (-303866 / 421875) * t ^ 14 + (-2589553 / 13500000) * t ^ 18 + (-584 / 421875) * t ^ 20 + (-24034 / 75) * alpha * t ^ 2 + (4086808 / 5625) * alpha * t ^ 4 + (-15531559 / 27000) * alpha * t ^ 6 + (60313343 / 337500) * alpha * t ^ 8 + (-7260643 / 375000) * alpha * t ^ 10 + (2590048 / 421875) * alpha * t ^ 12 + (-253456 / 421875) * alpha * t ^ 14 + (-61564 / 421875) * alpha * t ^ 18 + (-584 / 421875) * alpha * t ^ 20) * c_sq
theorem v46_30 (t : ℂ) : (momentPoly 46 z46 3 0).eval t = ((-71 / 50) * t ^ 3 + (71 / 50) * t ^ 5 + (-5059 / 750) * c * t ^ 3 + (2633 / 250) * c * t ^ 5 + (284 / 1125) * c * t ^ 9 + (-2659 / 750) * alpha * t ^ 3 + (3833 / 250) * alpha * t ^ 5 + (884 / 1125) * alpha * t ^ 9 + (71 / 150) * alpha * c * t ^ 3 + (-71 / 150) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_10, v45_20, v45_30]
  try simp only [phase43_00, phase43_10, phase43_20, phase43_30]
  try simp only [star_one, star_neg]
  linear_combination ((1523 / 6000) * t ^ 3 + (-5027 / 6000) * t ^ 5 + (513 / 2000) * c * t ^ 3 + (-5011 / 6000) * c * t ^ 5 + (1 / 375) * c ^ 2 * t ^ 3 + (1 / 375) * c ^ 2 * t ^ 5) * alpha_sq + ((4 / 375) * alpha * t ^ 3 + (4 / 375) * alpha * t ^ 5) * c_sq
theorem v46_31 (t : ℂ) : (momentPoly 46 z46 3 1).eval t = ((-8451 / 40) * t ^ 2 + (-72163 / 150) * t ^ 4 + (28467 / 50) * t ^ 6 + (-313 / 200) * t ^ 10 + (-108 / 5) * c * t ^ 2 + (944 / 75) * c * t ^ 4 + (144 / 25) * c * t ^ 6 + (-4 / 25) * c * t ^ 10 + (2061 / 40) * alpha * t ^ 2 + (37071 / 50) * alpha * t ^ 4 + (-33437 / 50) * alpha * t ^ 6 + (229 / 600) * alpha * t ^ 10 + (-36 / 5) * alpha * c * t ^ 2 + (944 / 225) * alpha * c * t ^ 4 + (48 / 25) * alpha * c * t ^ 6 + (-4 / 75) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_10, v45_11, v45_20, v45_21, v45_30, v45_31]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21, phase43_30, phase43_31]
  try simp only [star_one, star_neg]
  linear_combination ((9 / 10) * t ^ 2 + (-77959 / 90000) * t ^ 4 + (6701 / 30000) * t ^ 6 + (221 / 5625) * t ^ 10 + (9 / 5) * c * t ^ 2 + (-79727 / 45000) * c * t ^ 4 + (4933 / 15000) * c * t ^ 6 + (221 / 5625) * c * t ^ 10 + (9 / 10) * c ^ 2 * t ^ 2 + (-1811 / 2000) * c ^ 2 * t ^ 4 + (211 / 2000) * c ^ 2 * t ^ 6) * alpha_sq + ((-9 / 5) * t ^ 2 + (44311 / 22500) * t ^ 4 + (-3149 / 7500) * t ^ 6 + (-71 / 5625) * t ^ 10 + (9 / 5) * alpha * t ^ 2 + (-46441 / 22500) * alpha * t ^ 4 + (3859 / 7500) * alpha * t ^ 6 + (71 / 5625) * alpha * t ^ 10) * c_sq
theorem v46_32 (t : ℂ) : (momentPoly 46 z46 3 2).eval t = ((24572 / 5) * t + (-182272 / 25) * t ^ 3 + (5368673 / 3000) * t ^ 5 + (766777 / 1500) * t ^ 7 + (166751 / 1000) * t ^ 9 + (-6031 / 2250) * t ^ 11 + (31651 / 2250) * t ^ 13 + (-24572 / 15) * c * t + (80189 / 25) * c * t ^ 3 + (-10225669 / 5000) * c * t ^ 5 + (3693317 / 7500) * c * t ^ 7 + (-793427 / 15000) * c * t ^ 9 + (13147 / 3750) * c * t ^ 11 + (-1849 / 1250) * c * t ^ 13 + (-24572 / 15) * alpha * t + (58651 / 25) * alpha * t ^ 3 + (-6707407 / 15000) * alpha * t ^ 5 + (-1845583 / 7500) * alpha * t ^ 7 + (-665627 / 15000) * alpha * t ^ 9 + (-2503 / 3750) * alpha * t ^ 11 + (-4699 / 1250) * alpha * t ^ 13 + (-24572 / 15) * alpha * c * t + (234248 / 75) * alpha * c * t ^ 3 + (-5665211 / 3000) * alpha * c * t ^ 5 + (1892003 / 4500) * alpha * c * t ^ 7 + (-158231 / 3000) * alpha * c * t ^ 9 + (21421 / 6750) * alpha * c * t ^ 11 + (-12001 / 6750) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_10, v45_11, v45_12, v45_20, v45_21, v45_22, v45_30, v45_31, v45_32]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22, phase43_30, phase43_31, phase43_32]
  try simp only [star_one, star_neg]
  linear_combination ((-135547 / 6000) * t ^ 3 + (1578859 / 18000) * t ^ 5 + (-25452353 / 450000) * t ^ 7 + (-931553 / 150000) * t ^ 9 + (111179 / 337500) * t ^ 11 + (-1110967 / 675000) * t ^ 13 + (-45657 / 2000) * c * t ^ 3 + (1578587 / 18000) * c * t ^ 5 + (-83949653 / 1350000) * c * t ^ 7 + (874147 / 450000) * c * t ^ 9 + (-111889 / 675000) * c * t ^ 11 + (442 / 84375) * c * t ^ 13 + (-89 / 375) * c ^ 2 * t ^ 3 + (-17 / 1125) * c ^ 2 * t ^ 5 + (83 / 360) * c ^ 2 * t ^ 7 + (-31 / 1800) * c ^ 2 * t ^ 9 + (-2 / 1125) * c ^ 2 * t ^ 11) * alpha_sq + ((178 / 125) * t ^ 3 + (269 / 3750) * t ^ 5 + (-36592 / 28125) * t ^ 7 + (371 / 18750) * t ^ 9 + (158 / 28125) * t ^ 11 + (-142 / 28125) * t ^ 13 + (-178 / 375) * alpha * t ^ 3 + (-553 / 11250) * alpha * t ^ 5 + (36592 / 84375) * alpha * t ^ 7 + (1049 / 56250) * alpha * t ^ 9 + (-158 / 84375) * alpha * t ^ 11 + (142 / 84375) * alpha * t ^ 13) * c_sq
theorem v46_33 (t : ℂ) : (momentPoly 46 z46 3 3).eval t = (565156 + (-1081530) * t ^ 2 + (227791839 / 500) * t ^ 4 + (5752311 / 50) * t ^ 6 + (-4316081 / 1000) * t ^ 8 + (-45041049 / 1000) * t ^ 10 + (-1257217 / 1000) * t ^ 12 + (484449 / 1000) * t ^ 14 + (-30) * t ^ 18 + (18744 / 125) * c * t ^ 4 + (-17608 / 75) * c * t ^ 6 + (16756 / 375) * c * t ^ 8 + (4828 / 125) * c * t ^ 10 + (284 / 125) * c * t ^ 12 + (-284 / 375) * c * t ^ 14) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_03, v45_10, v45_11, v45_12, v45_13, v45_20, v45_21, v45_22, v45_23, v45_30, v45_31, v45_32, v45_33]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23, phase43_30, phase43_31, phase43_32, phase43_33]
  try simp only [star_one, star_neg]
  linear_combination ((-12017 / 50) * t ^ 2 + (46134 / 125) * t ^ 4 + (271264663 / 300000) * t ^ 6 + (-495230227 / 150000) * t ^ 8 + (213166337 / 100000) * t ^ 10 + (6583753 / 3375000) * t ^ 12 + (1712729 / 562500) * t ^ 14 + (-97682 / 421875) * t ^ 18 + (-12017 / 25) * c * t ^ 2 + (106678 / 125) * c * t ^ 4 + (-171322763 / 450000) * c * t ^ 6 + (1062063 / 25000) * c * t ^ 8 + (-1814439 / 50000) * c * t ^ 10 + (7433 / 18750) * c * t ^ 12 + (-72103 / 112500) * c * t ^ 14 + (-12017 / 50) * c ^ 2 * t ^ 2 + (60544 / 125) * c ^ 2 * t ^ 4 + (-18035633 / 60000) * c ^ 2 * t ^ 6 + (5445667 / 90000) * c ^ 2 * t ^ 8 + (-385489 / 60000) * c ^ 2 * t ^ 10 + (25021 / 45000) * c ^ 2 * t ^ 12 + (-1237 / 5000) * c ^ 2 * t ^ 14) * alpha_sq + ((24034 / 25) * t ^ 2 + (-243738 / 125) * t ^ 4 + (30672211 / 25000) * t ^ 6 + (-9507977 / 37500) * t ^ 8 + (634327 / 25000) * t ^ 10 + (-1269041 / 421875) * t ^ 12 + (527573 / 281250) * t ^ 14 + (10082 / 421875) * t ^ 18) * c_sq
theorem v46_34 (t : ℂ) : (momentPoly 46 z46 3 4).eval t = ((4374902 / 5) * t + (-48132096 / 25) * t ^ 3 + (559796591 / 500) * t ^ 5 + (28595503 / 18750) * t ^ 7 + (1602770203 / 150000) * t ^ 9 + (-1208796559 / 15000) * t ^ 11 + (635484021 / 100000) * t ^ 13 + (-564067447 / 112500) * t ^ 15 + (-63935627 / 180000) * t ^ 17 + (-90226543 / 675000) * t ^ 19 + (-11579889 / 100000) * t ^ 21 + (-245689 / 21600) * t ^ 25 + (-4374902 / 15) * c * t + (21175302 / 25) * c * t ^ 3 + (-2322339509 / 2500) * c * t ^ 5 + (244476593733 / 500000) * c * t ^ 7 + (-207635014987 / 1500000) * c * t ^ 9 + (5088620291 / 200000) * c * t ^ 11 + (-11423584979 / 3000000) * c * t ^ 13 + (2139890119 / 2250000) * c * t ^ 15 + (-371490109 / 4500000) * c * t ^ 17 + (1166318921 / 27000000) * c * t ^ 19 + (-339786721 / 9000000) * c * t ^ 21 + (-17714311 / 13500000) * c * t ^ 25 + (4374902 / 15) * alpha * t + (-15487818 / 25) * alpha * t ^ 3 + (792398509 / 2500) * alpha * t ^ 5 + (77667670999 / 1500000) * alpha * t ^ 7 + (-28883663087 / 1500000) * alpha * t ^ 9 + (-3954756869 / 200000) * alpha * t ^ 11 + (215715507 / 1000000) * alpha * t ^ 13 + (-2861097881 / 2250000) * alpha * t ^ 15 + (-835826959 / 4500000) * alpha * t ^ 17 + (-1489224079 / 27000000) * alpha * t ^ 19 + (-93173221 / 9000000) * alpha * t ^ 21 + (-32930461 / 13500000) * alpha * t ^ 25 + (4374902 / 15) * alpha * c * t + (-20619088 / 25) * alpha * c * t ^ 3 + (1303274431 / 1500) * alpha * c * t ^ 5 + (-16343095927 / 37500) * alpha * c * t ^ 7 + (55335930947 / 450000) * alpha * c * t ^ 9 + (-278999159 / 11250) * alpha * c * t ^ 11 + (9568735061 / 2700000) * alpha * c * t ^ 13 + (-389137553 / 337500) * alpha * c * t ^ 15 + (30814577 / 540000) * alpha * c * t ^ 17 + (-36249533 / 506250) * alpha * c * t ^ 19 + (6879813 / 100000) * alpha * c * t ^ 21 + (113179 / 64800) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_03, v45_04, v45_10, v45_11, v45_12, v45_13, v45_14, v45_20, v45_21, v45_22, v45_23, v45_24, v45_30, v45_31, v45_32, v45_33, v45_34]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24, phase43_30, phase43_31, phase43_32, phase43_33, phase43_34]
  try simp only [star_one, star_neg]
  linear_combination ((-5965591 / 1000) * t ^ 3 + (159346789 / 6000) * t ^ 5 + (-2191398101333 / 72000000) * t ^ 7 + (52130480307 / 8000000) * t ^ 9 + (157001371363 / 48000000) * t ^ 11 + (-61479670123 / 86400000) * t ^ 13 + (369871070623 / 540000000) * t ^ 15 + (13670651407 / 270000000) * t ^ 17 + (-5047324379 / 1296000000) * t ^ 19 + (2905925489 / 240000000) * t ^ 21 + (1275898637 / 810000000) * t ^ 25 + (-6028263 / 1000) * c * t ^ 3 + (159666677 / 6000) * c * t ^ 5 + (-7224804684767 / 216000000) * c * t ^ 7 + (968057766523 / 72000000) * c * t ^ 9 + (-115534609207 / 144000000) * c * t ^ 11 + (134789312393 / 432000000) * c * t ^ 13 + (-8993134601 / 540000000) * c * t ^ 15 + (63279421 / 16875000) * c * t ^ 17 + (-1715527771 / 1296000000) * c * t ^ 19 + (13516520873 / 2160000000) * c * t ^ 21 + (64532 / 6328125) * c * t ^ 25 + (-7834 / 125) * c ^ 2 * t ^ 3 + (19993 / 375) * c ^ 2 * t ^ 5 + (151845107 / 2250000) * c ^ 2 * t ^ 7 + (-1768453583 / 27000000) * c ^ 2 * t ^ 9 + (12381341 / 1687500) * c ^ 2 * t ^ 11 + (-8395699 / 18000000) * c ^ 2 * t ^ 13 + (-1155253 / 4500000) * c ^ 2 * t ^ 15 + (-11101 / 337500) * c ^ 2 * t ^ 17 + (875461 / 13500000) * c ^ 2 * t ^ 19 + (-21997 / 1200000) * c ^ 2 * t ^ 21) * alpha_sq + ((47004 / 125) * t ^ 3 + (-206107 / 625) * t ^ 5 + (-31849991 / 90000) * t ^ 7 + (697294991 / 2250000) * t ^ 9 + (-5276281 / 4500000) * t ^ 11 + (-3306763 / 1500000) * t ^ 13 + (25994737 / 5625000) * t ^ 15 + (250552 / 703125) * t ^ 17 + (-6287831 / 13500000) * t ^ 19 + (4492399 / 22500000) * t ^ 21 + (20732 / 2109375) * t ^ 25 + (15668 / 125) * alpha * t ^ 3 + (-181399 / 1875) * alpha * t ^ 5 + (-884063321 / 6750000) * alpha * t ^ 7 + (205635187 / 2250000) * alpha * t ^ 9 + (55121411 / 4500000) * alpha * t ^ 11 + (-20552623 / 13500000) * alpha * t ^ 13 + (23097167 / 16875000) * alpha * t ^ 15 + (300962 / 2109375) * alpha * t ^ 17 + (-4549289 / 40500000) * alpha * t ^ 19 + (4072849 / 67500000) * alpha * t ^ 21 + (20732 / 6328125) * alpha * t ^ 25) * c_sq
theorem v46_40 (t : ℂ) : (momentPoly 46 z46 4 0).eval t = ((26593597 / 120000) * t ^ 4 + (723777 / 20000) * t ^ 6 + (-28792583 / 80000) * t ^ 8 + (-421243 / 60000) * t ^ 10 + (-3890063 / 720000) * t ^ 16 + (-16352 / 1875) * c * t ^ 4 + (18688 / 1875) * c * t ^ 6 + (7592 / 1875) * c * t ^ 8 + (2336 / 1875) * c * t ^ 10 + (584 / 5625) * c * t ^ 16 + (26678147 / 120000) * alpha * t ^ 4 + (-4547459 / 60000) * alpha * t ^ 6 + (-60910699 / 240000) * alpha * t ^ 8 + (-24719 / 180000) * alpha * t ^ 10 + (-569897 / 80000) * alpha * t ^ 16 + (20612 / 5625) * alpha * c * t ^ 4 + (-2392 / 625) * alpha * c * t ^ 6 + (-3004 / 1875) * alpha * c * t ^ 8 + (-2336 / 5625) * alpha * c * t ^ 10 + (-584 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_10, v45_20, v45_30, v45_40]
  try simp only [phase43_00, phase43_10, phase43_20, phase43_30, phase43_40]
  try simp only [star_one, star_neg]
  linear_combination ((15049 / 22500) * t ^ 4 + (-43547 / 5000) * t ^ 6 + (303023 / 15000) * t ^ 8 + (-884 / 5625) * t ^ 10 + (3496 / 5625) * c * t ^ 4 + (-28357 / 22500) * c * t ^ 6 + (-5027 / 22500) * c * t ^ 8 + (-884 / 5625) * c * t ^ 10 + (-71 / 1500) * c ^ 2 * t ^ 4 + (1081 / 22500) * c ^ 2 * t ^ 6 + (2 / 5625) * c ^ 2 * t ^ 8) * alpha_sq + ((5161 / 5625) * t ^ 4 + (-697 / 625) * t ^ 6 + (4 / 1875) * t ^ 8 + (-284 / 5625) * t ^ 10 + (4096 / 5625) * alpha * t ^ 4 + (-1736 / 1875) * alpha * t ^ 6 + (4 / 1875) * alpha * t ^ 8 + (-284 / 5625) * alpha * t ^ 10) * c_sq
theorem v46_41 (t : ℂ) : (momentPoly 46 z46 4 1).eval t = ((-6319 / 25) * t ^ 3 + (4313603 / 10000) * t ^ 5 + (-2276609 / 15000) * t ^ 7 + (-1372081 / 60000) * t ^ 9 + (-209101 / 45000) * t ^ 11 + (123901 / 180000) * t ^ 17 + (-450251 / 375) * c * t ^ 3 + (87765187 / 30000) * c * t ^ 5 + (-26732267 / 15000) * c * t ^ 7 + (31750991 / 180000) * c * t ^ 9 + (-2602223 / 45000) * c * t ^ 11 + (607103 / 180000) * c * t ^ 17 + (-236651 / 375) * alpha * t ^ 3 + (31112031 / 10000) * alpha * t ^ 5 + (-34415173 / 15000) * alpha * t ^ 7 + (23279729 / 180000) * alpha * t ^ 9 + (-5116657 / 45000) * alpha * t ^ 11 + (-46463 / 180000) * alpha * t ^ 17 + (6319 / 75) * alpha * c * t ^ 3 + (-14947991 / 90000) * alpha * c * t ^ 5 + (4283791 / 45000) * alpha * c * t ^ 7 + (-2394481 / 180000) * alpha * c * t ^ 9 + (-38701 / 135000) * alpha * c * t ^ 11 + (123901 / 540000) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_10, v45_11, v45_20, v45_21, v45_30, v45_31, v45_40, v45_41]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21, phase43_30, phase43_31, phase43_40, phase43_41]
  try simp only [star_one, star_neg]
  linear_combination ((135547 / 3000) * t ^ 3 + (-41602691 / 240000) * t ^ 5 + (219285389 / 1800000) * t ^ 7 + (-30922667 / 7200000) * t ^ 9 + (3735553 / 5400000) * t ^ 11 + (-5773297 / 21600000) * t ^ 17 + (45657 / 1000) * c * t ^ 3 + (-124739849 / 720000) * c * t ^ 5 + (229964701 / 1800000) * c * t ^ 7 + (-77288683 / 7200000) * c * t ^ 9 + (3717377 / 5400000) * c * t ^ 11 + (-1936891 / 7200000) * c * t ^ 17 + (178 / 375) * c ^ 2 * t ^ 3 + (533 / 5625) * c ^ 2 * t ^ 5 + (-28159 / 56250) * c ^ 2 * t ^ 7 + (-347 / 56250) * c ^ 2 * t ^ 9 + (-284 / 84375) * c ^ 2 * t ^ 11 + (-146 / 84375) * c ^ 2 * t ^ 17) * alpha_sq + ((-71 / 1875) * t ^ 5 + (71 / 1875) * t ^ 9 + (712 / 375) * alpha * t ^ 3 + (-559 / 5625) * alpha * t ^ 5 + (-47432 / 28125) * alpha * t ^ 7 + (7379 / 28125) * alpha * t ^ 9 + (3536 / 84375) * alpha * t ^ 11 + (584 / 84375) * alpha * t ^ 17) * c_sq
theorem v46_42 (t : ℂ) : (momentPoly 46 z46 4 2).eval t = ((-3761321 / 100) * t ^ 2 + (-13950931 / 600) * t ^ 4 + (275723672489 / 2400000) * t ^ 6 + (-23498937727 / 480000) * t ^ 8 + (-2076237139 / 320000) * t ^ 10 + (-7116149297 / 14400000) * t ^ 12 + (155936813 / 3600000) * t ^ 14 + (1552517 / 1600000) * t ^ 18 + (-190778053 / 1600000) * t ^ 20 + (-96136 / 25) * c * t ^ 2 + (426212 / 75) * c * t ^ 4 + (-58719647 / 56250) * c * t ^ 6 + (-8599243 / 11250) * c * t ^ 8 + (-6472069 / 56250) * c * t ^ 10 + (2544043 / 56250) * c * t ^ 12 + (-1292224 / 84375) * c * t ^ 14 + (179056 / 84375) * c * t ^ 18 + (-52 / 75) * c * t ^ 20 + (2751893 / 300) * alpha * t ^ 2 + (17420607 / 200) * alpha * t ^ 4 + (-1132195045813 / 7200000) * alpha * t ^ 6 + (1766655743 / 32000) * alpha * t ^ 8 + (18176044421 / 2880000) * alpha * t ^ 10 + (18652246943 / 14400000) * alpha * t ^ 12 + (643934039 / 10800000) * alpha * t ^ 14 + (643934039 / 43200000) * alpha * t ^ 18 + (3358544489 / 43200000) * alpha * t ^ 20 + (-96136 / 75) * alpha * c * t ^ 2 + (426212 / 225) * alpha * c * t ^ 4 + (-40094737 / 112500) * alpha * c * t ^ 6 + (-5343013 / 22500) * alpha * c * t ^ 8 + (-3224051 / 75000) * alpha * c * t ^ 10 + (2654381 / 225000) * alpha * c * t ^ 12 + (-356213 / 56250) * alpha * c * t ^ 14 + (656669 / 675000) * alpha * c * t ^ 18 + (-33997 / 135000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_10, v45_11, v45_12, v45_20, v45_21, v45_22, v45_30, v45_31, v45_32, v45_40, v45_41, v45_42]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22, phase43_30, phase43_31, phase43_32, phase43_40, phase43_41, phase43_42]
  try simp only [star_one, star_neg]
  linear_combination ((12017 / 75) * t ^ 2 + (-1715098 / 5625) * t ^ 4 + (390982427 / 1800000) * t ^ 6 + (-72341263 / 720000) * t ^ 8 + (-239464783 / 6000000) * t ^ 10 + (3382907291 / 36000000) * t ^ 12 + (-150918889 / 27000000) * t ^ 14 + (-64140617 / 54000000) * t ^ 18 + (685179881 / 108000000) * t ^ 20 + (24034 / 75) * c * t ^ 2 + (-3507988 / 5625) * c * t ^ 4 + (276141751 / 675000) * c * t ^ 6 + (-21223403 / 200000) * c * t ^ 8 + (55898149 / 2700000) * c * t ^ 10 + (-154575919 / 10800000) * c * t ^ 12 + (12937229 / 8100000) * c * t ^ 14 + (-75547 / 1012500) * c * t ^ 18 + (79597 / 2160000) * c * t ^ 20 + (12017 / 75) * c ^ 2 * t ^ 2 + (-39842 / 125) * c ^ 2 * t ^ 4 + (1036186727 / 5400000) * c ^ 2 * t ^ 6 + (-19115963 / 540000) * c ^ 2 * t ^ 8 + (199161113 / 54000000) * c ^ 2 * t ^ 10 + (-1755043 / 4500000) * c ^ 2 * t ^ 12 + (827903 / 5062500) * c ^ 2 * t ^ 14 + (1821139 / 162000000) * c ^ 2 * t ^ 18 + (-292 / 1265625) * c ^ 2 * t ^ 20) * alpha_sq + ((-24034 / 75) * t ^ 2 + (3899368 / 5625) * t ^ 4 + (-45880391 / 90000) * t ^ 6 + (32436259 / 225000) * t ^ 8 + (-25282757 / 1500000) * t ^ 10 + (2326921 / 375000) * t ^ 12 + (-303866 / 421875) * t ^ 14 + (-2589553 / 13500000) * t ^ 18 + (-584 / 421875) * t ^ 20 + (24034 / 75) * alpha * t ^ 2 + (-4086808 / 5625) * alpha * t ^ 4 + (15531559 / 27000) * alpha * t ^ 6 + (-60313343 / 337500) * alpha * t ^ 8 + (7260643 / 375000) * alpha * t ^ 10 + (-2590048 / 421875) * alpha * t ^ 12 + (253456 / 421875) * alpha * t ^ 14 + (61564 / 421875) * alpha * t ^ 18 + (584 / 421875) * alpha * t ^ 20) * c_sq
theorem v46_43 (t : ℂ) : (momentPoly 46 z46 4 3).eval t = ((4374902 / 5) * t + (-48132096 / 25) * t ^ 3 + (559796591 / 500) * t ^ 5 + (28595503 / 18750) * t ^ 7 + (1602770203 / 150000) * t ^ 9 + (-1208796559 / 15000) * t ^ 11 + (635484021 / 100000) * t ^ 13 + (-564067447 / 112500) * t ^ 15 + (-63935627 / 180000) * t ^ 17 + (-90226543 / 675000) * t ^ 19 + (-11579889 / 100000) * t ^ 21 + (-245689 / 21600) * t ^ 25 + (-4374902 / 15) * c * t + (21175302 / 25) * c * t ^ 3 + (-2322339509 / 2500) * c * t ^ 5 + (244476593733 / 500000) * c * t ^ 7 + (-207635014987 / 1500000) * c * t ^ 9 + (5088620291 / 200000) * c * t ^ 11 + (-11423584979 / 3000000) * c * t ^ 13 + (2139890119 / 2250000) * c * t ^ 15 + (-371490109 / 4500000) * c * t ^ 17 + (1166318921 / 27000000) * c * t ^ 19 + (-339786721 / 9000000) * c * t ^ 21 + (-17714311 / 13500000) * c * t ^ 25 + (-4374902 / 15) * alpha * t + (15487818 / 25) * alpha * t ^ 3 + (-792398509 / 2500) * alpha * t ^ 5 + (-77667670999 / 1500000) * alpha * t ^ 7 + (28883663087 / 1500000) * alpha * t ^ 9 + (3954756869 / 200000) * alpha * t ^ 11 + (-215715507 / 1000000) * alpha * t ^ 13 + (2861097881 / 2250000) * alpha * t ^ 15 + (835826959 / 4500000) * alpha * t ^ 17 + (1489224079 / 27000000) * alpha * t ^ 19 + (93173221 / 9000000) * alpha * t ^ 21 + (32930461 / 13500000) * alpha * t ^ 25 + (-4374902 / 15) * alpha * c * t + (20619088 / 25) * alpha * c * t ^ 3 + (-1303274431 / 1500) * alpha * c * t ^ 5 + (16343095927 / 37500) * alpha * c * t ^ 7 + (-55335930947 / 450000) * alpha * c * t ^ 9 + (278999159 / 11250) * alpha * c * t ^ 11 + (-9568735061 / 2700000) * alpha * c * t ^ 13 + (389137553 / 337500) * alpha * c * t ^ 15 + (-30814577 / 540000) * alpha * c * t ^ 17 + (36249533 / 506250) * alpha * c * t ^ 19 + (-6879813 / 100000) * alpha * c * t ^ 21 + (-113179 / 64800) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_03, v45_10, v45_11, v45_12, v45_13, v45_20, v45_21, v45_22, v45_23, v45_30, v45_31, v45_32, v45_33, v45_40, v45_41, v45_42, v45_43]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23, phase43_30, phase43_31, phase43_32, phase43_33, phase43_40, phase43_41, phase43_42, phase43_43]
  try simp only [star_one, star_neg]
  linear_combination ((-5965591 / 1000) * t ^ 3 + (159346789 / 6000) * t ^ 5 + (-2191398101333 / 72000000) * t ^ 7 + (52130480307 / 8000000) * t ^ 9 + (157001371363 / 48000000) * t ^ 11 + (-61479670123 / 86400000) * t ^ 13 + (369871070623 / 540000000) * t ^ 15 + (13670651407 / 270000000) * t ^ 17 + (-5047324379 / 1296000000) * t ^ 19 + (2905925489 / 240000000) * t ^ 21 + (1275898637 / 810000000) * t ^ 25 + (-6028263 / 1000) * c * t ^ 3 + (159666677 / 6000) * c * t ^ 5 + (-7224804684767 / 216000000) * c * t ^ 7 + (968057766523 / 72000000) * c * t ^ 9 + (-115534609207 / 144000000) * c * t ^ 11 + (134789312393 / 432000000) * c * t ^ 13 + (-8993134601 / 540000000) * c * t ^ 15 + (63279421 / 16875000) * c * t ^ 17 + (-1715527771 / 1296000000) * c * t ^ 19 + (13516520873 / 2160000000) * c * t ^ 21 + (64532 / 6328125) * c * t ^ 25 + (-7834 / 125) * c ^ 2 * t ^ 3 + (19993 / 375) * c ^ 2 * t ^ 5 + (151845107 / 2250000) * c ^ 2 * t ^ 7 + (-1768453583 / 27000000) * c ^ 2 * t ^ 9 + (12381341 / 1687500) * c ^ 2 * t ^ 11 + (-8395699 / 18000000) * c ^ 2 * t ^ 13 + (-1155253 / 4500000) * c ^ 2 * t ^ 15 + (-11101 / 337500) * c ^ 2 * t ^ 17 + (875461 / 13500000) * c ^ 2 * t ^ 19 + (-21997 / 1200000) * c ^ 2 * t ^ 21) * alpha_sq + ((47004 / 125) * t ^ 3 + (-206107 / 625) * t ^ 5 + (-31849991 / 90000) * t ^ 7 + (697294991 / 2250000) * t ^ 9 + (-5276281 / 4500000) * t ^ 11 + (-3306763 / 1500000) * t ^ 13 + (25994737 / 5625000) * t ^ 15 + (250552 / 703125) * t ^ 17 + (-6287831 / 13500000) * t ^ 19 + (4492399 / 22500000) * t ^ 21 + (20732 / 2109375) * t ^ 25 + (-15668 / 125) * alpha * t ^ 3 + (181399 / 1875) * alpha * t ^ 5 + (884063321 / 6750000) * alpha * t ^ 7 + (-205635187 / 2250000) * alpha * t ^ 9 + (-55121411 / 4500000) * alpha * t ^ 11 + (20552623 / 13500000) * alpha * t ^ 13 + (-23097167 / 16875000) * alpha * t ^ 15 + (-300962 / 2109375) * alpha * t ^ 17 + (4549289 / 40500000) * alpha * t ^ 19 + (-4072849 / 67500000) * alpha * t ^ 21 + (-20732 / 6328125) * alpha * t ^ 25) * c_sq
theorem v46_44 (t : ℂ) : (momentPoly 46 z46 4 4).eval t = (100622746 + (-253906320) * t ^ 2 + (19824792776 / 125) * t ^ 4 + (28711161957 / 500) * t ^ 6 + (-15489466284264569 / 240000000) * t ^ 8 + (-161914598402413 / 20000000) * t ^ 10 + (401993202631769 / 48000000) * t ^ 12 + (79015288209471 / 40000000) * t ^ 14 + (-1091156675820731 / 2880000000) * t ^ 16 + (-6941666385077 / 360000000) * t ^ 18 + (-6313496467723 / 2160000000) * t ^ 20 + (207938582573 / 360000000) * t ^ 22 + (18864985842869 / 1440000000) * t ^ 24 + (689372718449 / 1080000000) * t ^ 26 + (44359485597 / 320000000) * t ^ 32 + (6525184 / 125) * c * t ^ 4 + (-15944328 / 125) * c * t ^ 6 + (495529453391 / 5625000) * c * t ^ 8 + (-2754925417 / 703125) * c * t ^ 10 + (-2924219993 / 450000) * c * t ^ 12 + (-41749632217 / 16875000) * c * t ^ 14 + (1683355003 / 3750000) * c * t ^ 16 + (-865748909 / 2812500) * c * t ^ 18 + (-2791550317 / 33750000) * c * t ^ 20 + (1412086991 / 16875000) * c * t ^ 22 + (141974519 / 33750000) * c * t ^ 24 + (18089546 / 6328125) * c * t ^ 26 + (9044773 / 25312500) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_03, v45_04, v45_10, v45_11, v45_12, v45_13, v45_14, v45_20, v45_21, v45_22, v45_23, v45_24, v45_30, v45_31, v45_32, v45_33, v45_34, v45_40, v45_41, v45_42, v45_43, v45_44]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24, phase43_30, phase43_31, phase43_32, phase43_33, phase43_34, phase43_40, phase43_41, phase43_42, phase43_43, phase43_44]
  try simp only [star_one, star_neg]
  linear_combination ((-4231772 / 75) * t ^ 2 + (16060224 / 125) * t ^ 4 + (3394055251 / 12500) * t ^ 6 + (-30318249682189 / 22500000) * t ^ 8 + (15402942882897 / 10000000) * t ^ 10 + (-138677886913807 / 270000000) * t ^ 12 + (-2950087963541 / 180000000) * t ^ 14 + (-1685484062023 / 180000000) * t ^ 16 + (38001423191 / 135000000) * t ^ 18 + (4772578009 / 22500000) * t ^ 20 + (530629105841 / 2700000000) * t ^ 22 + (-1567514816507 / 2700000000) * t ^ 24 + (5684740627 / 506250000) * t ^ 26 + (-24193434713 / 4050000000) * t ^ 32 + (-8463544 / 75) * c * t ^ 2 + (111410624 / 375) * c * t ^ 4 + (-14594598083 / 56250) * c * t ^ 6 + (6216148029353 / 67500000) * c * t ^ 8 + (-830428406879 / 27000000) * c * t ^ 10 + (929492111333 / 67500000) * c * t ^ 12 + (-361096381303 / 810000000) * c * t ^ 14 + (125415150799 / 270000000) * c * t ^ 16 + (3805724803 / 67500000) * c * t ^ 18 + (10384635449 / 405000000) * c * t ^ 20 + (-51454938031 / 4050000000) * c * t ^ 22 + (-869242583 / 4050000000) * c * t ^ 24 + (-122931979 / 1518750000) * c * t ^ 26 + (-421450681 / 3037500000) * c * t ^ 32 + (-4231772 / 75) * c ^ 2 * t ^ 2 + (63229952 / 375) * c ^ 2 * t ^ 4 + (-417881741 / 2250) * c ^ 2 * t ^ 6 + (39421243912 / 421875) * c ^ 2 * t ^ 8 + (-99805572653 / 4218750) * c ^ 2 * t ^ 10 + (7090569653 / 1687500) * c ^ 2 * t ^ 12 + (-14327095201 / 20250000) * c ^ 2 * t ^ 14 + (1928505913 / 8437500) * c ^ 2 * t ^ 16 + (-72828017 / 7500000) * c ^ 2 * t ^ 18 + (769068971 / 50625000) * c ^ 2 * t ^ 20 + (-746345911 / 63281250) * c ^ 2 * t ^ 22 + (-7291727 / 253125000) * c ^ 2 * t ^ 24 + (-990966917 / 3037500000) * c ^ 2 * t ^ 26 + (-42632 / 94921875) * c ^ 2 * t ^ 32) * alpha_sq + ((16927088 / 75) * t ^ 2 + (-84850368 / 125) * t ^ 4 + (7080603793 / 9375) * t ^ 6 + (-8667115559509 / 22500000) * t ^ 8 + (440876220739 / 4500000) * t ^ 10 + (-2339592183013 / 135000000) * t ^ 12 + (180448468543 / 45000000) * t ^ 14 + (-17160146041 / 11250000) * t ^ 16 + (1750637309 / 16875000) * t ^ 18 + (-10604516041 / 135000000) * t ^ 20 + (27921439133 / 675000000) * t ^ 22 + (26049743 / 84375000) * t ^ 24 + (614691287 / 253125000) * t ^ 26 + (170528 / 31640625) * t ^ 32) * c_sq
#print axioms v46_00
#print axioms v46_11
#print axioms v46_22
#print axioms v46_33
#print axioms v46_44
end PhotonCertA
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z47 : Fin 47 → ℂ := Fin.snoc z46 (r ^ 3 * thetaPlus)
theorem v47_00 (t : ℂ) : (momentPoly 47 z47 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00]
  try simp only [phase43_00]
  try simp only [star_one, star_neg]
  ring
theorem v47_01 (t : ℂ) : (momentPoly 47 z47 0 1).eval t = ((1 / 2) * t + (-1 / 6) * c * t + (1 / 6) * alpha * t + (1 / 6) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01]
  try simp only [phase43_00, phase43_01]
  try simp only [star_one, star_neg]
  ring
theorem v47_02 (t : ℂ) : (momentPoly 47 z47 0 2).eval t = ((-131 / 24) * t ^ 2 + (-161 / 24) * t ^ 4 + (-4 / 15) * c * t ^ 2 + (-1 / 15) * c * t ^ 4 + (-171 / 40) * alpha * t ^ 2 + (-947 / 120) * alpha * t ^ 4 + (4 / 45) * alpha * c * t ^ 2 + (1 / 45) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02]
  try simp only [phase43_00, phase43_01, phase43_02]
  try simp only [star_one, star_neg]
  linear_combination ((2 / 225) * t ^ 2 + (4 / 225) * c * t ^ 2 + (2 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((-4 / 225) * t ^ 2 + (-4 / 225) * alpha * t ^ 2) * c_sq
theorem v47_03 (t : ℂ) : (momentPoly 47 z47 0 3).eval t = ((-71 / 40) * t ^ 3 + (71 / 40) * t ^ 5 + (-3923 / 600) * c * t ^ 3 + (8467 / 600) * c * t ^ 5 + (71 / 225) * c * t ^ 9 + (-877 / 600) * alpha * t ^ 3 + (-13267 / 600) * alpha * t ^ 5 + (-221 / 225) * alpha * t ^ 9 + (-71 / 120) * alpha * c * t ^ 3 + (71 / 120) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_03]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03]
  try simp only [star_one, star_neg]
  linear_combination ((-229 / 6000) * t ^ 3 + (-5611 / 6000) * t ^ 5 + (-197 / 6000) * c * t ^ 3 + (-16769 / 18000) * c * t ^ 5 + (2 / 375) * c ^ 2 * t ^ 3 + (4 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-8 / 375) * alpha * t ^ 3 + (-16 / 1125) * alpha * t ^ 5) * c_sq
theorem v47_04 (t : ℂ) : (momentPoly 47 z47 0 4).eval t = ((2214341 / 4800) * t ^ 4 + (-49243 / 160) * t ^ 6 + (-3897373 / 9600) * t ^ 8 + (-6145 / 288) * t ^ 10 + (-168487 / 28800) * t ^ 16 + (-4672 / 375) * c * t ^ 4 + (2628 / 125) * c * t ^ 6 + (2044 / 375) * c * t ^ 8 + (2336 / 1125) * c * t ^ 10 + (146 / 1125) * c * t ^ 16 + (-9761767 / 24000) * alpha * t ^ 4 + (4456487 / 12000) * alpha * t ^ 6 + (14061743 / 48000) * alpha * t ^ 8 + (173441 / 12000) * alpha * t ^ 10 + (1090237 / 144000) * alpha * t ^ 16 + (-6092 / 1125) * alpha * c * t ^ 4 + (2983 / 375) * alpha * c * t ^ 6 + (2399 / 1125) * alpha * c * t ^ 8 + (2336 / 3375) * alpha * c * t ^ 10 + (146 / 3375) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_03, v46_04]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04]
  try simp only [star_one, star_neg]
  linear_combination ((2659 / 5625) * t ^ 4 + (-4649 / 5000) * t ^ 6 + (108113 / 5000) * t ^ 8 + (-3536 / 16875) * t ^ 10 + (256 / 625) * c * t ^ 4 + (-16103 / 7500) * c * t ^ 6 + (-5611 / 22500) * c * t ^ 8 + (-3536 / 16875) * c * t ^ 10 + (-71 / 1125) * c ^ 2 * t ^ 4 + (121 / 1875) * c ^ 2 * t ^ 6 + (8 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((6124 / 5625) * t ^ 4 + (-2972 / 1875) * t ^ 6 + (16 / 5625) * t ^ 8 + (-1136 / 16875) * t ^ 10 + (-1568 / 1875) * alpha * t ^ 4 + (7496 / 5625) * alpha * t ^ 6 + (-16 / 5625) * alpha * t ^ 8 + (1136 / 16875) * alpha * t ^ 10) * c_sq
theorem v47_10 (t : ℂ) : (momentPoly 47 z47 1 0).eval t = ((1 / 2) * t + (-1 / 6) * c * t + (-1 / 6) * alpha * t + (-1 / 6) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_10]
  try simp only [phase43_00, phase43_10]
  try simp only [star_one, star_neg]
  ring
theorem v47_11 (t : ℂ) : (momentPoly 47 z47 1 1).eval t = (47 + (-22) * t ^ 2) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_10, v46_11]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11]
  try simp only [star_one, star_neg]
  linear_combination ((-2 / 225) * t ^ 2 + (-4 / 225) * c * t ^ 2 + (-2 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((8 / 225) * t ^ 2) * c_sq
theorem v47_12 (t : ℂ) : (momentPoly 47 z47 1 2).eval t = ((93 / 2) * t + (-467 / 15) * t ^ 3 + (-43 / 15) * t ^ 5 + (-31 / 2) * c * t + (841 / 60) * c * t ^ 3 + (-161 / 60) * c * t ^ 5 + (31 / 2) * alpha * t + (-599 / 60) * alpha * t ^ 3 + (-27 / 20) * alpha * t ^ 5 + (31 / 2) * alpha * c * t + (-613 / 45) * alpha * c * t ^ 3 + (103 / 45) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_10, v46_11, v46_12]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12]
  try simp only [star_one, star_neg]
  linear_combination ((229 / 18000) * t ^ 3 + (5611 / 18000) * t ^ 5 + (197 / 18000) * c * t ^ 3 + (16769 / 54000) * c * t ^ 5 + (-2 / 1125) * c ^ 2 * t ^ 3 + (-4 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((4 / 375) * t ^ 3 + (8 / 1125) * t ^ 5 + (4 / 1125) * alpha * t ^ 3 + (8 / 3375) * alpha * t ^ 5) * c_sq
theorem v47_13 (t : ℂ) : (momentPoly 47 z47 1 3).eval t = ((-3013 / 4) * t ^ 2 + (-503 / 24) * t ^ 4 + (951 / 2) * t ^ 6 + (-131 / 24) * t ^ 10 + (-184 / 5) * c * t ^ 2 + (341 / 15) * c * t ^ 4 + 6 * c * t ^ 6 + (-4 / 15) * c * t ^ 10 + (-11799 / 20) * alpha * t ^ 2 + (-30773 / 120) * alpha * t ^ 4 + (1093 / 2) * alpha * t ^ 6 + (-171 / 40) * alpha * t ^ 10 + (184 / 15) * alpha * c * t ^ 2 + (-341 / 45) * alpha * c * t ^ 4 + (-2) * alpha * c * t ^ 6 + (4 / 45) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_03, v46_10, v46_11, v46_12, v46_13]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13]
  try simp only [star_one, star_neg]
  linear_combination ((92 / 75) * t ^ 2 + (-22429 / 22500) * t ^ 4 + (2923 / 7500) * t ^ 6 + (884 / 16875) * t ^ 10 + (184 / 75) * c * t ^ 2 + (-24197 / 11250) * c * t ^ 4 + (2039 / 3750) * c * t ^ 6 + (884 / 16875) * c * t ^ 10 + (92 / 75) * c ^ 2 * t ^ 2 + (-577 / 500) * c ^ 2 * t ^ 4 + (77 / 500) * c ^ 2 * t ^ 6) * alpha_sq + ((-184 / 75) * t ^ 2 + (13981 / 5625) * t ^ 4 + (-1147 / 1875) * t ^ 6 + (-284 / 16875) * t ^ 10 + (-184 / 75) * alpha * t ^ 2 + (4897 / 1875) * alpha * t ^ 4 + (-4151 / 5625) * alpha * t ^ 6 + (-284 / 16875) * alpha * t ^ 10) * c_sq
theorem v47_14 (t : ℂ) : (momentPoly 47 z47 1 4).eval t = ((-6461 / 20) * t ^ 3 + (4200003 / 8000) * t ^ 5 + (-2063609 / 12000) * t ^ 7 + (-1201681 / 48000) * t ^ 9 + (-209101 / 36000) * t ^ 11 + (123901 / 144000) * t ^ 17 + (-356993 / 300) * c * t ^ 3 + (248305801 / 72000) * c * t ^ 5 + (-26992787 / 12000) * c * t ^ 7 + (35724271 / 144000) * c * t ^ 9 + (-2329583 / 36000) * c * t ^ 11 + (652543 / 144000) * c * t ^ 17 + (-79807 / 300) * alpha * t ^ 3 + (-245914519 / 72000) * alpha * t ^ 5 + (37843693 / 12000) * alpha * t ^ 7 + (-29365009 / 144000) * alpha * t ^ 9 + (4268017 / 36000) * alpha * t ^ 11 + (-10553 / 16000) * alpha * t ^ 17 + (-6461 / 60) * alpha * c * t ^ 3 + (14607191 / 72000) * alpha * c * t ^ 5 + (-4070791 / 36000) * alpha * c * t ^ 7 + (2564881 / 144000) * alpha * c * t ^ 9 + (38701 / 108000) * alpha * c * t ^ 11 + (-123901 / 432000) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_03, v46_04, v46_10, v46_11, v46_12, v46_13, v46_14]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14]
  try simp only [star_one, star_neg]
  linear_combination ((-20839 / 3000) * t ^ 3 + (-51446117 / 400000) * t ^ 5 + (202132861 / 1800000) * t ^ 7 + (-35401579 / 7200000) * t ^ 9 + (-299519 / 5400000) * t ^ 11 + (-6417521 / 21600000) * t ^ 17 + (-17927 / 3000) * c * t ^ 3 + (-1390209191 / 10800000) * c * t ^ 5 + (216321469 / 1800000) * c * t ^ 7 + (-32407417 / 2400000) * c * t ^ 9 + (-37319 / 600000) * c * t ^ 11 + (-19402067 / 64800000) * c * t ^ 17 + (364 / 375) * c ^ 2 * t ^ 3 + (-9094 / 84375) * c ^ 2 * t ^ 5 + (-58684 / 84375) * c ^ 2 * t ^ 7 + (-686 / 84375) * c ^ 2 * t ^ 9 + (-568 / 84375) * c ^ 2 * t ^ 11 + (-584 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((-142 / 1875) * t ^ 5 + (142 / 5625) * t ^ 7 + (284 / 5625) * t ^ 9 + (-1456 / 375) * alpha * t ^ 3 + (37478 / 28125) * alpha * t ^ 5 + (17066 / 9375) * alpha * t ^ 7 + (-10628 / 28125) * alpha * t ^ 9 + (-7072 / 84375) * alpha * t ^ 11 + (-2336 / 253125) * alpha * t ^ 17) * c_sq
theorem v47_20 (t : ℂ) : (momentPoly 47 z47 2 0).eval t = ((-131 / 24) * t ^ 2 + (-161 / 24) * t ^ 4 + (-4 / 15) * c * t ^ 2 + (-1 / 15) * c * t ^ 4 + (171 / 40) * alpha * t ^ 2 + (947 / 120) * alpha * t ^ 4 + (-4 / 45) * alpha * c * t ^ 2 + (-1 / 45) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_10, v46_20]
  try simp only [phase43_00, phase43_10, phase43_20]
  try simp only [star_one, star_neg]
  linear_combination ((2 / 225) * t ^ 2 + (4 / 225) * c * t ^ 2 + (2 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((-4 / 225) * t ^ 2 + (4 / 225) * alpha * t ^ 2) * c_sq
theorem v47_21 (t : ℂ) : (momentPoly 47 z47 2 1).eval t = ((93 / 2) * t + (-467 / 15) * t ^ 3 + (-43 / 15) * t ^ 5 + (-31 / 2) * c * t + (841 / 60) * c * t ^ 3 + (-161 / 60) * c * t ^ 5 + (-31 / 2) * alpha * t + (599 / 60) * alpha * t ^ 3 + (27 / 20) * alpha * t ^ 5 + (-31 / 2) * alpha * c * t + (613 / 45) * alpha * c * t ^ 3 + (-103 / 45) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_10, v46_11, v46_20, v46_21]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21]
  try simp only [star_one, star_neg]
  linear_combination ((229 / 18000) * t ^ 3 + (5611 / 18000) * t ^ 5 + (197 / 18000) * c * t ^ 3 + (16769 / 54000) * c * t ^ 5 + (-2 / 1125) * c ^ 2 * t ^ 3 + (-4 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((4 / 375) * t ^ 3 + (8 / 1125) * t ^ 5 + (-4 / 1125) * alpha * t ^ 3 + (-8 / 3375) * alpha * t ^ 5) * c_sq
theorem v47_22 (t : ℂ) : (momentPoly 47 z47 2 2).eval t = (4371 + (-4048) * t ^ 2 + (-309997 / 1200) * t ^ 4 + (224507 / 600) * t ^ 6 + (74461 / 400) * t ^ 8 + (142 / 225) * c * t ^ 4 + (-71 / 150) * c * t ^ 6 + (-71 / 450) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_10, v46_11, v46_12, v46_20, v46_21, v46_22]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22]
  try simp only [star_one, star_neg]
  linear_combination ((-368 / 225) * t ^ 2 + (1318 / 1125) * t ^ 4 + (-9437 / 45000) * t ^ 6 + (-108113 / 15000) * t ^ 8 + (-736 / 225) * c * t ^ 2 + (9218 / 3375) * c * t ^ 4 + (-209 / 22500) * c * t ^ 6 + (5611 / 67500) * c * t ^ 8 + (-368 / 225) * c ^ 2 * t ^ 2 + (5264 / 3375) * c ^ 2 * t ^ 4 + (-1276 / 5625) * c ^ 2 * t ^ 6 + (-8 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((1472 / 225) * t ^ 2 + (-7066 / 1125) * t ^ 4 + (5362 / 5625) * t ^ 6 + (32 / 16875) * t ^ 8) * c_sq
theorem v47_23 (t : ℂ) : (momentPoly 47 z47 2 3).eval t = ((12835 / 2) * t + (-42497 / 5) * t ^ 3 + (51243 / 32) * t ^ 5 + (209693 / 400) * t ^ 7 + (602617 / 2400) * t ^ 9 + (-631 / 1800) * t ^ 11 + (32551 / 1800) * t ^ 13 + (-12835 / 6) * c * t + (76531 / 20) * c * t ^ 3 + (-27899479 / 12000) * c * t ^ 5 + (733507 / 1200) * c * t ^ 7 + (-950591 / 12000) * c * t ^ 9 + (10147 / 3000) * c * t ^ 11 + (-6047 / 3000) * c * t ^ 13 + (12835 / 6) * alpha * t + (-54509 / 20) * alpha * t ^ 3 + (4305479 / 12000) * alpha * t ^ 5 + (311933 / 1200) * alpha * t ^ 7 + (780191 / 12000) * alpha * t ^ 9 + (5503 / 3000) * alpha * t ^ 11 + (14597 / 3000) * alpha * t ^ 13 + (12835 / 6) * alpha * c * t + (-55783 / 15) * alpha * c * t ^ 3 + (3069413 / 1440) * alpha * c * t ^ 5 + (-631267 / 1200) * alpha * c * t ^ 7 + (568537 / 7200) * alpha * c * t ^ 9 + (-16021 / 5400) * alpha * c * t ^ 11 + (12901 / 5400) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_03, v46_10, v46_11, v46_12, v46_13, v46_20, v46_21, v46_22, v46_23]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23]
  try simp only [star_one, star_neg]
  linear_combination ((20839 / 6000) * t ^ 3 + (1224233 / 18000) * t ^ 5 + (-6264653 / 112500) * t ^ 7 + (-115413 / 12500) * t ^ 9 + (-16717 / 337500) * t ^ 11 + (-1240031 / 675000) * t ^ 13 + (17927 / 6000) * c * t ^ 3 + (3678907 / 54000) * c * t ^ 5 + (-20811053 / 337500) * c * t ^ 7 + (314261 / 112500) * c * t ^ 9 + (21847 / 675000) * c * t ^ 11 + (1768 / 253125) * c * t ^ 13 + (-182 / 375) * c ^ 2 * t ^ 3 + (388 / 3375) * c ^ 2 * t ^ 5 + (1931 / 6750) * c ^ 2 * t ^ 7 + (-167 / 6750) * c ^ 2 * t ^ 9 + (-4 / 1125) * c ^ 2 * t ^ 11) * alpha_sq + ((364 / 125) * t ^ 3 + (-4093 / 5625) * t ^ 5 + (-15071 / 9375) * t ^ 7 + (758 / 28125) * t ^ 9 + (316 / 28125) * t ^ 11 + (-568 / 84375) * t ^ 13 + (364 / 375) * alpha * t ^ 3 + (-3241 / 16875) * alpha * t ^ 5 + (-46633 / 84375) * alpha * t ^ 7 + (-694 / 28125) * alpha * t ^ 9 + (316 / 84375) * alpha * t ^ 11 + (-568 / 253125) * alpha * t ^ 13) * c_sq
theorem v47_24 (t : ℂ) : (momentPoly 47 z47 2 4).eval t = ((-411340 / 3) * t ^ 2 + (1257425 / 8) * t ^ 4 + (-3985258219 / 480000) * t ^ 6 + (-1063607181 / 160000) * t ^ 8 + (-2487157381 / 192000) * t ^ 10 + (580769177 / 960000) * t ^ 12 + (-42209077 / 240000) * t ^ 14 + (-170991031 / 2880000) * t ^ 18 + (-387568289 / 2880000) * t ^ 20 + (-20096 / 3) * c * t ^ 2 + 9821 * c * t ^ 4 + (-1942523 / 750) * c * t ^ 6 + (-561761 / 1000) * c * t ^ 8 + (-8165 / 36) * c * t ^ 10 + (646303 / 9000) * c * t ^ 12 + (-87064 / 3375) * c * t ^ 14 + (9616 / 3375) * c * t ^ 18 + (-14 / 15) * c * t ^ 20 + (-107388) * alpha * t ^ 2 + (811687 / 8) * alpha * t ^ 4 + (22173163889 / 1440000) * alpha * t ^ 6 + (-4158484067 / 1440000) * alpha * t ^ 8 + (-7756813633 / 576000) * alpha * t ^ 10 + (-2727329881 / 8640000) * alpha * t ^ 12 + (-60390931 / 240000) * alpha * t ^ 14 + (-60390931 / 960000) * alpha * t ^ 18 + (-780592661 / 8640000) * alpha * t ^ 20 + (20096 / 9) * alpha * c * t ^ 2 + (-9821 / 3) * alpha * c * t ^ 4 + (788179 / 900) * alpha * c * t ^ 6 + (2813767 / 18000) * alpha * c * t ^ 8 + (198587 / 2250) * alpha * c * t ^ 10 + (-2120623 / 108000) * alpha * c * t ^ 12 + (284659 / 27000) * alpha * c * t ^ 14 + (-36667 / 27000) * alpha * c * t ^ 18 + (36397 / 108000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_03, v46_04, v46_10, v46_11, v46_12, v46_13, v46_14, v46_20, v46_21, v46_22, v46_23, v46_24]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24]
  try simp only [star_one, star_neg]
  linear_combination ((10048 / 45) * t ^ 2 + (-44858 / 125) * t ^ 4 + (120867241 / 450000) * t ^ 6 + (-4110132011 / 18000000) * t ^ 8 + (550035097 / 9000000) * t ^ 10 + (1309413089 / 12000000) * t ^ 12 + (-10404473 / 27000000) * t ^ 14 + (230311 / 1500000) * t ^ 18 + (244069411 / 36000000) * t ^ 20 + (20096 / 45) * c * t ^ 2 + (-96788 / 125) * c * t ^ 4 + (86049749 / 168750) * c * t ^ 6 + (-921532633 / 5400000) * c * t ^ 8 + (17226773 / 540000) * c * t ^ 10 + (-188714927 / 10800000) * c * t ^ 12 + (18418237 / 8100000) * c * t ^ 14 + (-22751 / 1012500) * c * t ^ 18 + (89197 / 2160000) * c * t ^ 20 + (10048 / 45) * c ^ 2 * t ^ 2 + (-10386 / 25) * c ^ 2 * t ^ 4 + (325796269 / 1350000) * c ^ 2 * t ^ 6 + (-503179139 / 10125000) * c ^ 2 * t ^ 8 + (82736563 / 13500000) * c ^ 2 * t ^ 10 + (-4549801 / 10125000) * c ^ 2 * t ^ 12 + (297689 / 1265625) * c ^ 2 * t ^ 14 + (600817 / 40500000) * c ^ 2 * t ^ 18 + (-1168 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-20096 / 45) * t ^ 2 + (111848 / 125) * t ^ 4 + (-72780737 / 112500) * t ^ 6 + (170713583 / 843750) * t ^ 8 + (-29608901 / 1125000) * t ^ 10 + (6517627 / 843750) * t ^ 12 + (-145304 / 140625) * t ^ 14 + (-923099 / 3375000) * t ^ 18 + (-2336 / 1265625) * t ^ 20 + (-20096 / 45) * alpha * t ^ 2 + (117528 / 125) * alpha * t ^ 4 + (-123783157 / 168750) * alpha * t ^ 6 + (34730503 / 140625) * alpha * t ^ 8 + (-25267937 / 843750) * alpha * t ^ 10 + (9665488 / 1265625) * alpha * t ^ 12 + (-1106096 / 1265625) * alpha * t ^ 14 + (-268724 / 1265625) * alpha * t ^ 18 + (-2336 / 1265625) * alpha * t ^ 20) * c_sq
theorem v47_30 (t : ℂ) : (momentPoly 47 z47 3 0).eval t = ((-71 / 40) * t ^ 3 + (71 / 40) * t ^ 5 + (-3923 / 600) * c * t ^ 3 + (8467 / 600) * c * t ^ 5 + (71 / 225) * c * t ^ 9 + (877 / 600) * alpha * t ^ 3 + (13267 / 600) * alpha * t ^ 5 + (221 / 225) * alpha * t ^ 9 + (71 / 120) * alpha * c * t ^ 3 + (-71 / 120) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_10, v46_20, v46_30]
  try simp only [phase43_00, phase43_10, phase43_20, phase43_30]
  try simp only [star_one, star_neg]
  linear_combination ((-229 / 6000) * t ^ 3 + (-5611 / 6000) * t ^ 5 + (-197 / 6000) * c * t ^ 3 + (-16769 / 18000) * c * t ^ 5 + (2 / 375) * c ^ 2 * t ^ 3 + (4 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((8 / 375) * alpha * t ^ 3 + (16 / 1125) * alpha * t ^ 5) * c_sq
theorem v47_31 (t : ℂ) : (momentPoly 47 z47 3 1).eval t = ((-3013 / 4) * t ^ 2 + (-503 / 24) * t ^ 4 + (951 / 2) * t ^ 6 + (-131 / 24) * t ^ 10 + (-184 / 5) * c * t ^ 2 + (341 / 15) * c * t ^ 4 + 6 * c * t ^ 6 + (-4 / 15) * c * t ^ 10 + (11799 / 20) * alpha * t ^ 2 + (30773 / 120) * alpha * t ^ 4 + (-1093 / 2) * alpha * t ^ 6 + (171 / 40) * alpha * t ^ 10 + (-184 / 15) * alpha * c * t ^ 2 + (341 / 45) * alpha * c * t ^ 4 + 2 * alpha * c * t ^ 6 + (-4 / 45) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_10, v46_11, v46_20, v46_21, v46_30, v46_31]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21, phase43_30, phase43_31]
  try simp only [star_one, star_neg]
  linear_combination ((92 / 75) * t ^ 2 + (-22429 / 22500) * t ^ 4 + (2923 / 7500) * t ^ 6 + (884 / 16875) * t ^ 10 + (184 / 75) * c * t ^ 2 + (-24197 / 11250) * c * t ^ 4 + (2039 / 3750) * c * t ^ 6 + (884 / 16875) * c * t ^ 10 + (92 / 75) * c ^ 2 * t ^ 2 + (-577 / 500) * c ^ 2 * t ^ 4 + (77 / 500) * c ^ 2 * t ^ 6) * alpha_sq + ((-184 / 75) * t ^ 2 + (13981 / 5625) * t ^ 4 + (-1147 / 1875) * t ^ 6 + (-284 / 16875) * t ^ 10 + (184 / 75) * alpha * t ^ 2 + (-4897 / 1875) * alpha * t ^ 4 + (4151 / 5625) * alpha * t ^ 6 + (284 / 16875) * alpha * t ^ 10) * c_sq
theorem v47_32 (t : ℂ) : (momentPoly 47 z47 3 2).eval t = ((12835 / 2) * t + (-42497 / 5) * t ^ 3 + (51243 / 32) * t ^ 5 + (209693 / 400) * t ^ 7 + (602617 / 2400) * t ^ 9 + (-631 / 1800) * t ^ 11 + (32551 / 1800) * t ^ 13 + (-12835 / 6) * c * t + (76531 / 20) * c * t ^ 3 + (-27899479 / 12000) * c * t ^ 5 + (733507 / 1200) * c * t ^ 7 + (-950591 / 12000) * c * t ^ 9 + (10147 / 3000) * c * t ^ 11 + (-6047 / 3000) * c * t ^ 13 + (-12835 / 6) * alpha * t + (54509 / 20) * alpha * t ^ 3 + (-4305479 / 12000) * alpha * t ^ 5 + (-311933 / 1200) * alpha * t ^ 7 + (-780191 / 12000) * alpha * t ^ 9 + (-5503 / 3000) * alpha * t ^ 11 + (-14597 / 3000) * alpha * t ^ 13 + (-12835 / 6) * alpha * c * t + (55783 / 15) * alpha * c * t ^ 3 + (-3069413 / 1440) * alpha * c * t ^ 5 + (631267 / 1200) * alpha * c * t ^ 7 + (-568537 / 7200) * alpha * c * t ^ 9 + (16021 / 5400) * alpha * c * t ^ 11 + (-12901 / 5400) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_10, v46_11, v46_12, v46_20, v46_21, v46_22, v46_30, v46_31, v46_32]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22, phase43_30, phase43_31, phase43_32]
  try simp only [star_one, star_neg]
  linear_combination ((20839 / 6000) * t ^ 3 + (1224233 / 18000) * t ^ 5 + (-6264653 / 112500) * t ^ 7 + (-115413 / 12500) * t ^ 9 + (-16717 / 337500) * t ^ 11 + (-1240031 / 675000) * t ^ 13 + (17927 / 6000) * c * t ^ 3 + (3678907 / 54000) * c * t ^ 5 + (-20811053 / 337500) * c * t ^ 7 + (314261 / 112500) * c * t ^ 9 + (21847 / 675000) * c * t ^ 11 + (1768 / 253125) * c * t ^ 13 + (-182 / 375) * c ^ 2 * t ^ 3 + (388 / 3375) * c ^ 2 * t ^ 5 + (1931 / 6750) * c ^ 2 * t ^ 7 + (-167 / 6750) * c ^ 2 * t ^ 9 + (-4 / 1125) * c ^ 2 * t ^ 11) * alpha_sq + ((364 / 125) * t ^ 3 + (-4093 / 5625) * t ^ 5 + (-15071 / 9375) * t ^ 7 + (758 / 28125) * t ^ 9 + (316 / 28125) * t ^ 11 + (-568 / 84375) * t ^ 13 + (-364 / 375) * alpha * t ^ 3 + (3241 / 16875) * alpha * t ^ 5 + (46633 / 84375) * alpha * t ^ 7 + (694 / 28125) * alpha * t ^ 9 + (-316 / 84375) * alpha * t ^ 11 + (568 / 253125) * alpha * t ^ 13) * c_sq
theorem v47_33 (t : ℂ) : (momentPoly 47 z47 3 3).eval t = (603245 + (-828960) * t ^ 2 + (-8369919 / 80) * t ^ 4 + (92542391 / 200) * t ^ 6 + (-5809689 / 80) * t ^ 8 + (-8639481 / 200) * t ^ 10 + (-405997 / 200) * t ^ 12 + (224507 / 200) * t ^ 14 + (-22) * t ^ 18 + (1278 / 5) * c * t ^ 4 + (-10224 / 25) * c * t ^ 6 + (3337 / 30) * c * t ^ 8 + (994 / 25) * c * t ^ 10 + (284 / 75) * c * t ^ 12 + (-71 / 50) * c * t ^ 14) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_03, v46_10, v46_11, v46_12, v46_13, v46_20, v46_21, v46_22, v46_23, v46_30, v46_31, v46_32, v46_33]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23, phase43_30, phase43_31, phase43_32, phase43_33]
  try simp only [star_one, star_neg]
  linear_combination ((-5024 / 15) * t ^ 2 + (11862 / 25) * t ^ 4 + (-6006789 / 25000) * t ^ 6 + (-167683841 / 75000) * t ^ 8 + (145788433 / 75000) * t ^ 10 + (1062643 / 843750) * t ^ 12 + (-8876339 / 1125000) * t ^ 14 + (-390728 / 1265625) * t ^ 18 + (-10048 / 15) * c * t ^ 2 + (27654 / 25) * c * t ^ 4 + (-50044453 / 112500) * c * t ^ 6 + (4797341 / 112500) * c * t ^ 8 + (-1607371 / 37500) * c * t ^ 10 + (8866 / 28125) * c * t ^ 12 + (-28333 / 37500) * c * t ^ 14 + (-5024 / 15) * c ^ 2 * t ^ 2 + (15792 / 25) * c ^ 2 * t ^ 4 + (-17050177 / 45000) * c ^ 2 * t ^ 6 + (5683529 / 67500) * c ^ 2 * t ^ 8 + (-157463 / 15000) * c ^ 2 * t ^ 10 + (21421 / 33750) * c ^ 2 * t ^ 12 + (-12049 / 33750) * c ^ 2 * t ^ 14) * alpha_sq + ((20096 / 15) * t ^ 2 + (-63594 / 25) * t ^ 4 + (29037263 / 18750) * t ^ 6 + (-9902599 / 28125) * t ^ 8 + (780203 / 18750) * t ^ 10 + (-1458284 / 421875) * t ^ 12 + (126986 / 46875) * t ^ 14 + (40328 / 1265625) * t ^ 18) * c_sq
theorem v47_34 (t : ℂ) : (momentPoly 47 z47 3 4).eval t = ((2336525 / 2) * t + (-11476992 / 5) * t ^ 3 + (84930349 / 80) * t ^ 5 + (7584951007 / 60000) * t ^ 7 + (3649248409 / 60000) * t ^ 9 + (-2735484463 / 24000) * t ^ 11 + (562813073 / 90000) * t ^ 13 + (-317481923 / 60000) * t ^ 15 + (-66844427 / 144000) * t ^ 17 + (-311738261 / 1080000) * t ^ 19 + (-48474463 / 360000) * t ^ 21 + (-237049 / 17280) * t ^ 25 + (-2336525 / 6) * c * t + (5167104 / 5) * c * t ^ 3 + (-2096444331 / 2000) * c * t ^ 5 + (214436843601 / 400000) * c * t ^ 7 + (-199493988193 / 1200000) * c * t ^ 9 + (85224002321 / 2400000) * c * t ^ 11 + (-6797953723 / 1440000) * c * t ^ 13 + (669162247 / 600000) * c * t ^ 15 + (-425850109 / 3600000) * c * t ^ 17 + (954762389 / 21600000) * c * t ^ 19 + (-138384581 / 2400000) * c * t ^ 21 + (-19514311 / 10800000) * c * t ^ 25 + (2336525 / 6) * alpha * t + (-3680256 / 5) * alpha * t ^ 3 + (577692931 / 2000) * alpha * t ^ 5 + (114233456803 / 1200000) * alpha * t ^ 7 + (-6345752993 / 1200000) * alpha * t ^ 9 + (-65468310079 / 2400000) * alpha * t ^ 11 + (-764114563 / 1440000) * alpha * t ^ 13 + (-816761653 / 600000) * alpha * t ^ 15 + (-868586959 / 3600000) * alpha * t ^ 17 + (-2070084811 / 21600000) * alpha * t ^ 19 + (-19178581 / 2400000) * alpha * t ^ 21 + (-31130461 / 10800000) * alpha * t ^ 25 + (2336525 / 6) * alpha * c * t + (-5021696 / 5) * alpha * c * t ^ 3 + (77868111 / 80) * alpha * c * t ^ 5 + (-85253766307 / 180000) * alpha * c * t ^ 7 + (8966973797 / 60000) * alpha * c * t ^ 9 + (-2497532917 / 72000) * alpha * c * t ^ 11 + (2317909129 / 540000) * alpha * c * t ^ 13 + (-244602827 / 180000) * alpha * c * t ^ 15 + (36315377 / 432000) * alpha * c * t ^ 17 + (-251335939 / 3240000) * alpha * c * t ^ 19 + (107151763 / 1080000) * alpha * c * t ^ 21 + (121819 / 51840) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_03, v46_04, v46_10, v46_11, v46_12, v46_13, v46_14, v46_20, v46_21, v46_22, v46_23, v46_24, v46_30, v46_31, v46_32, v46_33, v46_34]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24, phase43_30, phase43_31, phase43_32, phase43_33, phase43_34]
  try simp only [star_one, star_neg]
  linear_combination ((117248 / 125) * t ^ 3 + (83176531 / 6000) * t ^ 5 + (-527181967591 / 24000000) * t ^ 7 + (10786651553 / 4800000) * t ^ 9 + (5366987917 / 1152000) * t ^ 11 + (-1213655879567 / 2160000000) * t ^ 13 + (42857291843 / 60000000) * t ^ 15 + (16425017759 / 270000000) * t ^ 17 + (-2387511943 / 6480000000) * t ^ 19 + (32422617757 / 2160000000) * t ^ 21 + (1418272141 / 810000000) * t ^ 25 + (100864 / 125) * c * t ^ 3 + (252171449 / 18000) * c * t ^ 5 + (-5461570439903 / 216000000) * c * t ^ 7 + (271065911141 / 24000000) * c * t ^ 9 + (-111053375719 / 144000000) * c * t ^ 11 + (216497910923 / 720000000) * c * t ^ 13 + (-1045735903 / 180000000) * c * t ^ 15 + (22806683 / 4218750) * c * t ^ 17 + (4087685107 / 2160000000) * c * t ^ 19 + (15836436701 / 2160000000) * c * t ^ 21 + (258128 / 18984375) * c * t ^ 25 + (-16384 / 125) * c ^ 2 * t ^ 3 + (165116 / 1125) * c ^ 2 * t ^ 5 + (169330789 / 3375000) * c ^ 2 * t ^ 7 + (-515819041 / 6750000) * c ^ 2 * t ^ 9 + (55087243 / 6750000) * c ^ 2 * t ^ 11 + (-1091183 / 2700000) * c ^ 2 * t ^ 13 + (-372913 / 675000) * c ^ 2 * t ^ 15 + (-12001 / 253125) * c ^ 2 * t ^ 17 + (410587 / 4050000) * c ^ 2 * t ^ 19 + (-23597 / 900000) * c ^ 2 * t ^ 21) * alpha_sq + ((98304 / 125) * t ^ 3 + (-1689074 / 1875) * t ^ 5 + (-51101011 / 225000) * t ^ 7 + (97357373 / 281250) * t ^ 9 + (6258289 / 750000) * t ^ 11 + (-64697731 / 16875000) * t ^ 13 + (10414147 / 1406250) * t ^ 15 + (1088672 / 2109375) * t ^ 17 + (-22045331 / 33750000) * t ^ 19 + (537079 / 1875000) * t ^ 21 + (82928 / 6328125) * t ^ 25 + (32768 / 125) * alpha * t ^ 3 + (-1537418 / 5625) * alpha * t ^ 5 + (-372182089 / 3375000) * alpha * t ^ 7 + (3419057 / 31250) * alpha * t ^ 9 + (7937107 / 450000) * alpha * t ^ 11 + (-116191021 / 50625000) * alpha * t ^ 13 + (8955077 / 4218750) * alpha * t ^ 15 + (143368 / 703125) * alpha * t ^ 17 + (-1667909 / 11250000) * alpha * t ^ 19 + (1471387 / 16875000) * alpha * t ^ 21 + (82928 / 18984375) * alpha * t ^ 25) * c_sq
theorem v47_40 (t : ℂ) : (momentPoly 47 z47 4 0).eval t = ((2214341 / 4800) * t ^ 4 + (-49243 / 160) * t ^ 6 + (-3897373 / 9600) * t ^ 8 + (-6145 / 288) * t ^ 10 + (-168487 / 28800) * t ^ 16 + (-4672 / 375) * c * t ^ 4 + (2628 / 125) * c * t ^ 6 + (2044 / 375) * c * t ^ 8 + (2336 / 1125) * c * t ^ 10 + (146 / 1125) * c * t ^ 16 + (9761767 / 24000) * alpha * t ^ 4 + (-4456487 / 12000) * alpha * t ^ 6 + (-14061743 / 48000) * alpha * t ^ 8 + (-173441 / 12000) * alpha * t ^ 10 + (-1090237 / 144000) * alpha * t ^ 16 + (6092 / 1125) * alpha * c * t ^ 4 + (-2983 / 375) * alpha * c * t ^ 6 + (-2399 / 1125) * alpha * c * t ^ 8 + (-2336 / 3375) * alpha * c * t ^ 10 + (-146 / 3375) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_10, v46_20, v46_30, v46_40]
  try simp only [phase43_00, phase43_10, phase43_20, phase43_30, phase43_40]
  try simp only [star_one, star_neg]
  linear_combination ((2659 / 5625) * t ^ 4 + (-4649 / 5000) * t ^ 6 + (108113 / 5000) * t ^ 8 + (-3536 / 16875) * t ^ 10 + (256 / 625) * c * t ^ 4 + (-16103 / 7500) * c * t ^ 6 + (-5611 / 22500) * c * t ^ 8 + (-3536 / 16875) * c * t ^ 10 + (-71 / 1125) * c ^ 2 * t ^ 4 + (121 / 1875) * c ^ 2 * t ^ 6 + (8 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((6124 / 5625) * t ^ 4 + (-2972 / 1875) * t ^ 6 + (16 / 5625) * t ^ 8 + (-1136 / 16875) * t ^ 10 + (1568 / 1875) * alpha * t ^ 4 + (-7496 / 5625) * alpha * t ^ 6 + (16 / 5625) * alpha * t ^ 8 + (-1136 / 16875) * alpha * t ^ 10) * c_sq
theorem v47_41 (t : ℂ) : (momentPoly 47 z47 4 1).eval t = ((-6461 / 20) * t ^ 3 + (4200003 / 8000) * t ^ 5 + (-2063609 / 12000) * t ^ 7 + (-1201681 / 48000) * t ^ 9 + (-209101 / 36000) * t ^ 11 + (123901 / 144000) * t ^ 17 + (-356993 / 300) * c * t ^ 3 + (248305801 / 72000) * c * t ^ 5 + (-26992787 / 12000) * c * t ^ 7 + (35724271 / 144000) * c * t ^ 9 + (-2329583 / 36000) * c * t ^ 11 + (652543 / 144000) * c * t ^ 17 + (79807 / 300) * alpha * t ^ 3 + (245914519 / 72000) * alpha * t ^ 5 + (-37843693 / 12000) * alpha * t ^ 7 + (29365009 / 144000) * alpha * t ^ 9 + (-4268017 / 36000) * alpha * t ^ 11 + (10553 / 16000) * alpha * t ^ 17 + (6461 / 60) * alpha * c * t ^ 3 + (-14607191 / 72000) * alpha * c * t ^ 5 + (4070791 / 36000) * alpha * c * t ^ 7 + (-2564881 / 144000) * alpha * c * t ^ 9 + (-38701 / 108000) * alpha * c * t ^ 11 + (123901 / 432000) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_10, v46_11, v46_20, v46_21, v46_30, v46_31, v46_40, v46_41]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21, phase43_30, phase43_31, phase43_40, phase43_41]
  try simp only [star_one, star_neg]
  linear_combination ((-20839 / 3000) * t ^ 3 + (-51446117 / 400000) * t ^ 5 + (202132861 / 1800000) * t ^ 7 + (-35401579 / 7200000) * t ^ 9 + (-299519 / 5400000) * t ^ 11 + (-6417521 / 21600000) * t ^ 17 + (-17927 / 3000) * c * t ^ 3 + (-1390209191 / 10800000) * c * t ^ 5 + (216321469 / 1800000) * c * t ^ 7 + (-32407417 / 2400000) * c * t ^ 9 + (-37319 / 600000) * c * t ^ 11 + (-19402067 / 64800000) * c * t ^ 17 + (364 / 375) * c ^ 2 * t ^ 3 + (-9094 / 84375) * c ^ 2 * t ^ 5 + (-58684 / 84375) * c ^ 2 * t ^ 7 + (-686 / 84375) * c ^ 2 * t ^ 9 + (-568 / 84375) * c ^ 2 * t ^ 11 + (-584 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((-142 / 1875) * t ^ 5 + (142 / 5625) * t ^ 7 + (284 / 5625) * t ^ 9 + (1456 / 375) * alpha * t ^ 3 + (-37478 / 28125) * alpha * t ^ 5 + (-17066 / 9375) * alpha * t ^ 7 + (10628 / 28125) * alpha * t ^ 9 + (7072 / 84375) * alpha * t ^ 11 + (2336 / 253125) * alpha * t ^ 17) * c_sq
theorem v47_42 (t : ℂ) : (momentPoly 47 z47 4 2).eval t = ((-411340 / 3) * t ^ 2 + (1257425 / 8) * t ^ 4 + (-3985258219 / 480000) * t ^ 6 + (-1063607181 / 160000) * t ^ 8 + (-2487157381 / 192000) * t ^ 10 + (580769177 / 960000) * t ^ 12 + (-42209077 / 240000) * t ^ 14 + (-170991031 / 2880000) * t ^ 18 + (-387568289 / 2880000) * t ^ 20 + (-20096 / 3) * c * t ^ 2 + 9821 * c * t ^ 4 + (-1942523 / 750) * c * t ^ 6 + (-561761 / 1000) * c * t ^ 8 + (-8165 / 36) * c * t ^ 10 + (646303 / 9000) * c * t ^ 12 + (-87064 / 3375) * c * t ^ 14 + (9616 / 3375) * c * t ^ 18 + (-14 / 15) * c * t ^ 20 + 107388 * alpha * t ^ 2 + (-811687 / 8) * alpha * t ^ 4 + (-22173163889 / 1440000) * alpha * t ^ 6 + (4158484067 / 1440000) * alpha * t ^ 8 + (7756813633 / 576000) * alpha * t ^ 10 + (2727329881 / 8640000) * alpha * t ^ 12 + (60390931 / 240000) * alpha * t ^ 14 + (60390931 / 960000) * alpha * t ^ 18 + (780592661 / 8640000) * alpha * t ^ 20 + (-20096 / 9) * alpha * c * t ^ 2 + (9821 / 3) * alpha * c * t ^ 4 + (-788179 / 900) * alpha * c * t ^ 6 + (-2813767 / 18000) * alpha * c * t ^ 8 + (-198587 / 2250) * alpha * c * t ^ 10 + (2120623 / 108000) * alpha * c * t ^ 12 + (-284659 / 27000) * alpha * c * t ^ 14 + (36667 / 27000) * alpha * c * t ^ 18 + (-36397 / 108000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_10, v46_11, v46_12, v46_20, v46_21, v46_22, v46_30, v46_31, v46_32, v46_40, v46_41, v46_42]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22, phase43_30, phase43_31, phase43_32, phase43_40, phase43_41, phase43_42]
  try simp only [star_one, star_neg]
  linear_combination ((10048 / 45) * t ^ 2 + (-44858 / 125) * t ^ 4 + (120867241 / 450000) * t ^ 6 + (-4110132011 / 18000000) * t ^ 8 + (550035097 / 9000000) * t ^ 10 + (1309413089 / 12000000) * t ^ 12 + (-10404473 / 27000000) * t ^ 14 + (230311 / 1500000) * t ^ 18 + (244069411 / 36000000) * t ^ 20 + (20096 / 45) * c * t ^ 2 + (-96788 / 125) * c * t ^ 4 + (86049749 / 168750) * c * t ^ 6 + (-921532633 / 5400000) * c * t ^ 8 + (17226773 / 540000) * c * t ^ 10 + (-188714927 / 10800000) * c * t ^ 12 + (18418237 / 8100000) * c * t ^ 14 + (-22751 / 1012500) * c * t ^ 18 + (89197 / 2160000) * c * t ^ 20 + (10048 / 45) * c ^ 2 * t ^ 2 + (-10386 / 25) * c ^ 2 * t ^ 4 + (325796269 / 1350000) * c ^ 2 * t ^ 6 + (-503179139 / 10125000) * c ^ 2 * t ^ 8 + (82736563 / 13500000) * c ^ 2 * t ^ 10 + (-4549801 / 10125000) * c ^ 2 * t ^ 12 + (297689 / 1265625) * c ^ 2 * t ^ 14 + (600817 / 40500000) * c ^ 2 * t ^ 18 + (-1168 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-20096 / 45) * t ^ 2 + (111848 / 125) * t ^ 4 + (-72780737 / 112500) * t ^ 6 + (170713583 / 843750) * t ^ 8 + (-29608901 / 1125000) * t ^ 10 + (6517627 / 843750) * t ^ 12 + (-145304 / 140625) * t ^ 14 + (-923099 / 3375000) * t ^ 18 + (-2336 / 1265625) * t ^ 20 + (20096 / 45) * alpha * t ^ 2 + (-117528 / 125) * alpha * t ^ 4 + (123783157 / 168750) * alpha * t ^ 6 + (-34730503 / 140625) * alpha * t ^ 8 + (25267937 / 843750) * alpha * t ^ 10 + (-9665488 / 1265625) * alpha * t ^ 12 + (1106096 / 1265625) * alpha * t ^ 14 + (268724 / 1265625) * alpha * t ^ 18 + (2336 / 1265625) * alpha * t ^ 20) * c_sq
theorem v47_43 (t : ℂ) : (momentPoly 47 z47 4 3).eval t = ((2336525 / 2) * t + (-11476992 / 5) * t ^ 3 + (84930349 / 80) * t ^ 5 + (7584951007 / 60000) * t ^ 7 + (3649248409 / 60000) * t ^ 9 + (-2735484463 / 24000) * t ^ 11 + (562813073 / 90000) * t ^ 13 + (-317481923 / 60000) * t ^ 15 + (-66844427 / 144000) * t ^ 17 + (-311738261 / 1080000) * t ^ 19 + (-48474463 / 360000) * t ^ 21 + (-237049 / 17280) * t ^ 25 + (-2336525 / 6) * c * t + (5167104 / 5) * c * t ^ 3 + (-2096444331 / 2000) * c * t ^ 5 + (214436843601 / 400000) * c * t ^ 7 + (-199493988193 / 1200000) * c * t ^ 9 + (85224002321 / 2400000) * c * t ^ 11 + (-6797953723 / 1440000) * c * t ^ 13 + (669162247 / 600000) * c * t ^ 15 + (-425850109 / 3600000) * c * t ^ 17 + (954762389 / 21600000) * c * t ^ 19 + (-138384581 / 2400000) * c * t ^ 21 + (-19514311 / 10800000) * c * t ^ 25 + (-2336525 / 6) * alpha * t + (3680256 / 5) * alpha * t ^ 3 + (-577692931 / 2000) * alpha * t ^ 5 + (-114233456803 / 1200000) * alpha * t ^ 7 + (6345752993 / 1200000) * alpha * t ^ 9 + (65468310079 / 2400000) * alpha * t ^ 11 + (764114563 / 1440000) * alpha * t ^ 13 + (816761653 / 600000) * alpha * t ^ 15 + (868586959 / 3600000) * alpha * t ^ 17 + (2070084811 / 21600000) * alpha * t ^ 19 + (19178581 / 2400000) * alpha * t ^ 21 + (31130461 / 10800000) * alpha * t ^ 25 + (-2336525 / 6) * alpha * c * t + (5021696 / 5) * alpha * c * t ^ 3 + (-77868111 / 80) * alpha * c * t ^ 5 + (85253766307 / 180000) * alpha * c * t ^ 7 + (-8966973797 / 60000) * alpha * c * t ^ 9 + (2497532917 / 72000) * alpha * c * t ^ 11 + (-2317909129 / 540000) * alpha * c * t ^ 13 + (244602827 / 180000) * alpha * c * t ^ 15 + (-36315377 / 432000) * alpha * c * t ^ 17 + (251335939 / 3240000) * alpha * c * t ^ 19 + (-107151763 / 1080000) * alpha * c * t ^ 21 + (-121819 / 51840) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_03, v46_10, v46_11, v46_12, v46_13, v46_20, v46_21, v46_22, v46_23, v46_30, v46_31, v46_32, v46_33, v46_40, v46_41, v46_42, v46_43]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23, phase43_30, phase43_31, phase43_32, phase43_33, phase43_40, phase43_41, phase43_42, phase43_43]
  try simp only [star_one, star_neg]
  linear_combination ((117248 / 125) * t ^ 3 + (83176531 / 6000) * t ^ 5 + (-527181967591 / 24000000) * t ^ 7 + (10786651553 / 4800000) * t ^ 9 + (5366987917 / 1152000) * t ^ 11 + (-1213655879567 / 2160000000) * t ^ 13 + (42857291843 / 60000000) * t ^ 15 + (16425017759 / 270000000) * t ^ 17 + (-2387511943 / 6480000000) * t ^ 19 + (32422617757 / 2160000000) * t ^ 21 + (1418272141 / 810000000) * t ^ 25 + (100864 / 125) * c * t ^ 3 + (252171449 / 18000) * c * t ^ 5 + (-5461570439903 / 216000000) * c * t ^ 7 + (271065911141 / 24000000) * c * t ^ 9 + (-111053375719 / 144000000) * c * t ^ 11 + (216497910923 / 720000000) * c * t ^ 13 + (-1045735903 / 180000000) * c * t ^ 15 + (22806683 / 4218750) * c * t ^ 17 + (4087685107 / 2160000000) * c * t ^ 19 + (15836436701 / 2160000000) * c * t ^ 21 + (258128 / 18984375) * c * t ^ 25 + (-16384 / 125) * c ^ 2 * t ^ 3 + (165116 / 1125) * c ^ 2 * t ^ 5 + (169330789 / 3375000) * c ^ 2 * t ^ 7 + (-515819041 / 6750000) * c ^ 2 * t ^ 9 + (55087243 / 6750000) * c ^ 2 * t ^ 11 + (-1091183 / 2700000) * c ^ 2 * t ^ 13 + (-372913 / 675000) * c ^ 2 * t ^ 15 + (-12001 / 253125) * c ^ 2 * t ^ 17 + (410587 / 4050000) * c ^ 2 * t ^ 19 + (-23597 / 900000) * c ^ 2 * t ^ 21) * alpha_sq + ((98304 / 125) * t ^ 3 + (-1689074 / 1875) * t ^ 5 + (-51101011 / 225000) * t ^ 7 + (97357373 / 281250) * t ^ 9 + (6258289 / 750000) * t ^ 11 + (-64697731 / 16875000) * t ^ 13 + (10414147 / 1406250) * t ^ 15 + (1088672 / 2109375) * t ^ 17 + (-22045331 / 33750000) * t ^ 19 + (537079 / 1875000) * t ^ 21 + (82928 / 6328125) * t ^ 25 + (-32768 / 125) * alpha * t ^ 3 + (1537418 / 5625) * alpha * t ^ 5 + (372182089 / 3375000) * alpha * t ^ 7 + (-3419057 / 31250) * alpha * t ^ 9 + (-7937107 / 450000) * alpha * t ^ 11 + (116191021 / 50625000) * alpha * t ^ 13 + (-8955077 / 4218750) * alpha * t ^ 15 + (-143368 / 703125) * alpha * t ^ 17 + (1667909 / 11250000) * alpha * t ^ 19 + (-1471387 / 16875000) * alpha * t ^ 21 + (-82928 / 18984375) * alpha * t ^ 25) * c_sq
theorem v47_44 (t : ℂ) : (momentPoly 47 z47 4 4).eval t = (109816675 + (-199030832) * t ^ 2 + (-3725853943 / 100) * t ^ 4 + (27304170793 / 100) * t ^ 6 + (-2721487992629879 / 16000000) * t ^ 8 + (214435646672857 / 12000000) * t ^ 10 + (33691464998869 / 9600000) * t ^ 12 + (80248722843349 / 24000000) * t ^ 14 + (-53247617063463 / 64000000) * t ^ 16 + (1209609320863 / 72000000) * t ^ 18 + (-420856743741 / 16000000) * t ^ 20 + (1109221638893 / 72000000) * t ^ 22 + (4683191149697 / 288000000) * t ^ 24 + (306233941277 / 216000000) * t ^ 26 + (283694192963 / 1728000000) * t ^ 32 + (6826792 / 75) * c * t ^ 4 + (-5530829 / 25) * c * t ^ 6 + (183050739701 / 1125000) * c * t ^ 8 + (-122846833871 / 4500000) * c * t ^ 10 + (-124782161 / 180000) * c * t ^ 12 + (-130720192231 / 27000000) * c * t ^ 14 + (21429360427 / 27000000) * c * t ^ 16 + (-3336703871 / 6750000) * c * t ^ 18 + (-2423629663 / 20250000) * c * t ^ 20 + (3790558381 / 27000000) * c * t ^ 22 + (50864537 / 9000000) * c * t ^ 24 + (9044773 / 1687500) * c * t ^ 26 + (9044773 / 20250000) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_03, v46_04, v46_10, v46_11, v46_12, v46_13, v46_14, v46_20, v46_21, v46_22, v46_23, v46_24, v46_30, v46_31, v46_32, v46_33, v46_34, v46_40, v46_41, v46_42, v46_43, v46_44]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24, phase43_30, phase43_31, phase43_32, phase43_33, phase43_34, phase43_40, phase43_41, phase43_42, phase43_43, phase43_44]
  try simp only [star_one, star_neg]
  linear_combination ((-18093712 / 225) * t ^ 2 + (63364168 / 375) * t ^ 4 + (-5235406939 / 37500) * t ^ 6 + (-3006408716599 / 5625000) * t ^ 8 + (28014430972847 / 30000000) * t ^ 10 + (-3414370316549 / 10800000) * t ^ 12 + (-7531197344689 / 180000000) * t ^ 14 + (-390931797697 / 108000000) * t ^ 16 + (-203778961109 / 405000000) * t ^ 18 + (264815935391 / 675000000) * t ^ 20 + (-410680955731 / 2700000000) * t ^ 22 + (-1838995834619 / 2700000000) * t ^ 24 + (944931413 / 1012500000) * t ^ 26 + (-2868291601 / 450000000) * t ^ 32 + (-36187424 / 225) * c * t ^ 2 + (443164568 / 1125) * c * t ^ 4 + (-17542047061 / 56250) * c * t ^ 6 + (1625273525443 / 16875000) * c * t ^ 8 + (-4622731767389 / 135000000) * c * t ^ 10 + (434387190503 / 27000000) * c * t ^ 12 + (-1611577821 / 10000000) * c * t ^ 14 + (402684585373 / 810000000) * c * t ^ 16 + (19314864367 / 202500000) * c * t ^ 18 + (31422132433 / 759375000) * c * t ^ 20 + (-102091491829 / 4050000000) * c * t ^ 22 + (-93630439 / 450000000) * c * t ^ 24 + (-139174423 / 253125000) * c * t ^ 26 + (-468479033 / 3037500000) * c * t ^ 32 + (-18093712 / 225) * c ^ 2 * t ^ 2 + (253072064 / 1125) * c ^ 2 * t ^ 4 + (-1320675664 / 5625) * c ^ 2 * t ^ 6 + (148067882293 / 1265625) * c ^ 2 * t ^ 8 + (-277549769183 / 8437500) * c ^ 2 * t ^ 10 + (2786790677 / 421875) * c ^ 2 * t ^ 12 + (-48104137141 / 50625000) * c ^ 2 * t ^ 14 + (3899338673 / 12656250) * c ^ 2 * t ^ 16 + (-787462649 / 50625000) * c ^ 2 * t ^ 18 + (606165118 / 31640625) * c ^ 2 * t ^ 20 + (-4647503531 / 253125000) * c ^ 2 * t ^ 22 + (-868087 / 21093750) * c ^ 2 * t ^ 24 + (-119713757 / 253125000) * c ^ 2 * t ^ 26 + (-170528 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((72374848 / 225) * t ^ 2 + (-339705016 / 375) * t ^ 4 + (2987426612 / 3125) * t ^ 6 + (-8151734688517 / 16875000) * t ^ 8 + (152827259981 / 1125000) * t ^ 10 + (-182890740331 / 6750000) * t ^ 12 + (20134735571 / 3750000) * t ^ 14 + (-78184837 / 37500) * t ^ 16 + (405800249 / 2531250) * t ^ 18 + (-1849530983 / 18750000) * t ^ 20 + (11023953083 / 168750000) * t ^ 22 + (9377989 / 21093750) * t ^ 24 + (24864629 / 7031250) * t ^ 26 + (682112 / 94921875) * t ^ 32) * c_sq
#print axioms v47_00
#print axioms v47_11
#print axioms v47_22
#print axioms v47_33
#print axioms v47_44
end PhotonCertA
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
theorem site48 : ((r ^ 3 * thetaMinus) : ℂ) = ((1 / 10) + (1 / 30) * c + (-1 / 30) * alpha + (1 / 30) * alpha * c) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 30) + (-1 / 80) * c + (1 / 80) * alpha + (-1 / 60) * alpha * c + (1 / 60) * alpha ^ 2 + (-1 / 240) * alpha ^ 2 * c + (1 / 240) * alpha ^ 3) * alpha_sq
theorem phase48_00 : ((r ^ 3 * thetaMinus) : ℂ) ^ 0 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 0 = (1) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase48_01 : ((r ^ 3 * thetaMinus) : ℂ) ^ 0 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 1 = ((1 / 10) + (1 / 30) * c + (1 / 30) * alpha + (-1 / 30) * alpha * c) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase48_02 : ((r ^ 3 * thetaMinus) : ℂ) ^ 0 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 2 = ((-73 / 150) + (1 / 75) * c + (-73 / 150) * alpha + (-1 / 225) * alpha * c) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 900) + (-1 / 450) * c + (1 / 900) * c ^ 2) * alpha_sq + ((-1 / 450) + (-1 / 450) * alpha) * c_sq
theorem phase48_03 : ((r ^ 3 * thetaMinus) : ℂ) ^ 0 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 3 = ((-71 / 1125) * c + (-221 / 1125) * alpha) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 3000) + (-1 / 1800) * c + (1 / 9000) * c ^ 2 + (1 / 9000) * c ^ 3 + (1 / 27000) * alpha + (-1 / 9000) * alpha * c + (1 / 9000) * alpha * c ^ 2 + (-1 / 27000) * alpha * c ^ 3) * alpha_sq + ((-1 / 3375) * c + (-1 / 1125) * alpha) * c_sq
theorem phase48_04 : ((r ^ 3 * thetaMinus) : ℂ) ^ 0 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 4 = ((-5033 / 11250) + (-146 / 5625) * c + (5033 / 11250) * alpha + (-146 / 16875) * alpha * c) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((17 / 270000) + (-1 / 13500) * c + (-1 / 27000) * c ^ 2 + (1 / 22500) * c ^ 3 + (1 / 270000) * c ^ 4 + (1 / 67500) * alpha + (-2 / 50625) * alpha * c + (1 / 33750) * alpha * c ^ 2 + (-1 / 202500) * alpha * c ^ 4 + (1 / 810000) * alpha ^ 2 + (-1 / 202500) * alpha ^ 2 * c + (1 / 135000) * alpha ^ 2 * c ^ 2 + (-1 / 202500) * alpha ^ 2 * c ^ 3 + (1 / 810000) * alpha ^ 2 * c ^ 4) * alpha_sq + ((-34 / 16875) + (-2 / 16875) * c + (-1 / 101250) * c ^ 2 + (34 / 16875) * alpha + (-2 / 50625) * alpha * c + (1 / 101250) * alpha * c ^ 2) * c_sq
theorem phase48_10 : ((r ^ 3 * thetaMinus) : ℂ) ^ 1 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 0 = ((1 / 10) + (1 / 30) * c + (-1 / 30) * alpha + (1 / 30) * alpha * c) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase48_11 : ((r ^ 3 * thetaMinus) : ℂ) ^ 1 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 1 = (1) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 900) + (1 / 450) * c + (-1 / 900) * c ^ 2) * alpha_sq + ((1 / 225)) * c_sq
theorem phase48_12 : ((r ^ 3 * thetaMinus) : ℂ) ^ 1 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 2 = ((1 / 10) + (1 / 30) * c + (1 / 30) * alpha + (-1 / 30) * alpha * c) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 9000) + (1 / 5400) * c + (-1 / 27000) * c ^ 2 + (-1 / 27000) * c ^ 3 + (-1 / 27000) * alpha + (1 / 9000) * alpha * c + (-1 / 9000) * alpha * c ^ 2 + (1 / 27000) * alpha * c ^ 3) * alpha_sq + ((1 / 2250) + (1 / 6750) * c + (1 / 6750) * alpha + (-1 / 6750) * alpha * c) * c_sq
theorem phase48_13 : ((r ^ 3 * thetaMinus) : ℂ) ^ 1 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 3 = ((-73 / 150) + (1 / 75) * c + (-73 / 150) * alpha + (-1 / 225) * alpha * c) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 270000) + (-1 / 67500) * c + (1 / 45000) * c ^ 2 + (-1 / 67500) * c ^ 3 + (1 / 270000) * c ^ 4 + (-1 / 135000) * alpha + (1 / 50625) * alpha * c + (-1 / 67500) * alpha * c ^ 2 + (1 / 405000) * alpha * c ^ 4 + (-1 / 810000) * alpha ^ 2 + (1 / 202500) * alpha ^ 2 * c + (-1 / 135000) * alpha ^ 2 * c ^ 2 + (1 / 202500) * alpha ^ 2 * c ^ 3 + (-1 / 810000) * alpha ^ 2 * c ^ 4) * alpha_sq + ((-37 / 16875) + (1 / 16875) * c + (-1 / 101250) * c ^ 2 + (-37 / 16875) * alpha + (-1 / 50625) * alpha * c + (-1 / 101250) * alpha * c ^ 2) * c_sq
theorem phase48_14 : ((r ^ 3 * thetaMinus) : ℂ) ^ 1 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 4 = ((-71 / 1125) * c + (-221 / 1125) * alpha) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 300000) + (-17 / 2700000) * c + (1 / 270000) * c ^ 2 + (-17 / 12150000) * c ^ 3 + (1 / 4860000) * c ^ 4 + (11 / 24300000) * c ^ 5 + (-1 / 1620000) * alpha + (1 / 900000) * alpha * c + (1 / 2430000) * alpha * c ^ 2 + (-7 / 4050000) * alpha * c ^ 3 + (7 / 8100000) * alpha * c ^ 4 + (-1 / 24300000) * alpha * c ^ 5 + (-1 / 2700000) * alpha ^ 2 + (11 / 8100000) * alpha ^ 2 * c + (-7 / 4050000) * alpha ^ 2 * c ^ 2 + (1 / 1350000) * alpha ^ 2 * c ^ 3 + (1 / 8100000) * alpha ^ 2 * c ^ 4 + (-1 / 8100000) * alpha ^ 2 * c ^ 5 + (-1 / 24300000) * alpha ^ 3 + (1 / 4860000) * alpha ^ 3 * c + (-1 / 2430000) * alpha ^ 3 * c ^ 2 + (1 / 2430000) * alpha ^ 3 * c ^ 3 + (-1 / 4860000) * alpha ^ 3 * c ^ 4 + (1 / 24300000) * alpha ^ 3 * c ^ 5) * alpha_sq + ((-8 / 28125) * c + (-1 / 759375) * c ^ 3 + (-224 / 253125) * alpha + (-1 / 253125) * alpha * c ^ 2) * c_sq
theorem phase48_20 : ((r ^ 3 * thetaMinus) : ℂ) ^ 2 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 0 = ((-73 / 150) + (1 / 75) * c + (73 / 150) * alpha + (1 / 225) * alpha * c) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 900) + (-1 / 450) * c + (1 / 900) * c ^ 2) * alpha_sq + ((-1 / 450) + (1 / 450) * alpha) * c_sq
theorem phase48_21 : ((r ^ 3 * thetaMinus) : ℂ) ^ 2 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 1 = ((1 / 10) + (1 / 30) * c + (-1 / 30) * alpha + (1 / 30) * alpha * c) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 9000) + (1 / 5400) * c + (-1 / 27000) * c ^ 2 + (-1 / 27000) * c ^ 3 + (1 / 27000) * alpha + (-1 / 9000) * alpha * c + (1 / 9000) * alpha * c ^ 2 + (-1 / 27000) * alpha * c ^ 3) * alpha_sq + ((1 / 2250) + (1 / 6750) * c + (-1 / 6750) * alpha + (1 / 6750) * alpha * c) * c_sq
theorem phase48_22 : ((r ^ 3 * thetaMinus) : ℂ) ^ 2 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 2 = (1) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-7 / 270000) + (1 / 22500) * c + (-7 / 405000) * c ^ 2 + (1 / 202500) * c ^ 3 + (-1 / 162000) * c ^ 4 + (1 / 810000) * alpha ^ 2 + (-1 / 202500) * alpha ^ 2 * c + (1 / 135000) * alpha ^ 2 * c ^ 2 + (-1 / 202500) * alpha ^ 2 * c ^ 3 + (1 / 810000) * alpha ^ 2 * c ^ 4) * alpha_sq + ((76 / 16875) + (1 / 50625) * c ^ 2) * c_sq
theorem phase48_23 : ((r ^ 3 * thetaMinus) : ℂ) ^ 2 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 3 = ((1 / 10) + (1 / 30) * c + (1 / 30) * alpha + (-1 / 30) * alpha * c) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-7 / 2700000) + (29 / 8100000) * c + (-1 / 4050000) * c ^ 2 + (-1 / 12150000) * c ^ 3 + (-11 / 24300000) * c ^ 4 + (-1 / 4860000) * c ^ 5 + (-7 / 8100000) * alpha + (19 / 8100000) * alpha * c + (-1 / 486000) * alpha * c ^ 2 + (1 / 1350000) * alpha * c ^ 3 + (-1 / 2700000) * alpha * c ^ 4 + (1 / 4860000) * alpha * c ^ 5 + (1 / 8100000) * alpha ^ 2 + (-11 / 24300000) * alpha ^ 2 * c + (7 / 12150000) * alpha ^ 2 * c ^ 2 + (-1 / 4050000) * alpha ^ 2 * c ^ 3 + (-1 / 24300000) * alpha ^ 2 * c ^ 4 + (1 / 24300000) * alpha ^ 2 * c ^ 5 + (1 / 24300000) * alpha ^ 3 + (-1 / 4860000) * alpha ^ 3 * c + (1 / 2430000) * alpha ^ 3 * c ^ 2 + (-1 / 2430000) * alpha ^ 3 * c ^ 3 + (1 / 4860000) * alpha ^ 3 * c ^ 4 + (-1 / 24300000) * alpha ^ 3 * c ^ 5) * alpha_sq + ((38 / 84375) + (38 / 253125) * c + (1 / 506250) * c ^ 2 + (1 / 1518750) * c ^ 3 + (38 / 253125) * alpha + (-38 / 253125) * alpha * c + (1 / 1518750) * alpha * c ^ 2 + (-1 / 1518750) * alpha * c ^ 3) * c_sq
theorem phase48_24 : ((r ^ 3 * thetaMinus) : ℂ) ^ 2 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 4 = ((-73 / 150) + (1 / 75) * c + (-73 / 150) * alpha + (-1 / 225) * alpha * c) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 16200000) + (-1 / 8100000) * c + (103 / 243000000) * c ^ 2 + (-17 / 60750000) * c ^ 3 + (77 / 729000000) * c ^ 4 + (-29 / 364500000) * c ^ 5 + (11 / 729000000) * c ^ 6 + (-7 / 40500000) * alpha + (1 / 2430000) * alpha * c + (-31 / 121500000) * alpha * c ^ 2 + (1 / 91125000) * alpha * c ^ 3 + (-1 / 40500000) * alpha * c ^ 4 + (1 / 60750000) * alpha * c ^ 5 + (1 / 72900000) * alpha * c ^ 6 + (-1 / 60750000) * alpha ^ 2 + (1 / 15187500) * alpha ^ 2 * c + (-19 / 182250000) * alpha ^ 2 * c ^ 2 + (1 / 11390625) * alpha ^ 2 * c ^ 3 + (-1 / 20250000) * alpha ^ 2 * c ^ 4 + (1 / 45562500) * alpha ^ 2 * c ^ 5 + (-1 / 182250000) * alpha ^ 2 * c ^ 6 + (1 / 121500000) * alpha ^ 3 + (-7 / 182250000) * alpha ^ 3 * c + (1 / 14580000) * alpha ^ 3 * c ^ 2 + (-1 / 18225000) * alpha ^ 3 * c ^ 3 + (1 / 72900000) * alpha ^ 3 * c ^ 4 + (1 / 182250000) * alpha ^ 3 * c ^ 5 + (-1 / 364500000) * alpha ^ 3 * c ^ 6 + (1 / 729000000) * alpha ^ 4 + (-1 / 121500000) * alpha ^ 4 * c + (1 / 48600000) * alpha ^ 4 * c ^ 2 + (-1 / 36450000) * alpha ^ 4 * c ^ 3 + (1 / 48600000) * alpha ^ 4 * c ^ 4 + (-1 / 121500000) * alpha ^ 4 * c ^ 5 + (1 / 729000000) * alpha ^ 4 * c ^ 6) * alpha_sq + ((-5549 / 2531250) + (76 / 1265625) * c + (-1 / 101250) * c ^ 2 + (1 / 3796875) * c ^ 3 + (-1 / 22781250) * c ^ 4 + (-5549 / 2531250) * alpha + (-76 / 3796875) * alpha * c + (-1 / 101250) * alpha * c ^ 2 + (-1 / 11390625) * alpha * c ^ 3 + (-1 / 22781250) * alpha * c ^ 4) * c_sq
theorem phase48_30 : ((r ^ 3 * thetaMinus) : ℂ) ^ 3 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 0 = ((-71 / 1125) * c + (221 / 1125) * alpha) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 3000) + (-1 / 1800) * c + (1 / 9000) * c ^ 2 + (1 / 9000) * c ^ 3 + (-1 / 27000) * alpha + (1 / 9000) * alpha * c + (-1 / 9000) * alpha * c ^ 2 + (1 / 27000) * alpha * c ^ 3) * alpha_sq + ((-1 / 3375) * c + (1 / 1125) * alpha) * c_sq
theorem phase48_31 : ((r ^ 3 * thetaMinus) : ℂ) ^ 3 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 1 = ((-73 / 150) + (1 / 75) * c + (73 / 150) * alpha + (1 / 225) * alpha * c) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 270000) + (-1 / 67500) * c + (1 / 45000) * c ^ 2 + (-1 / 67500) * c ^ 3 + (1 / 270000) * c ^ 4 + (1 / 135000) * alpha + (-1 / 50625) * alpha * c + (1 / 67500) * alpha * c ^ 2 + (-1 / 405000) * alpha * c ^ 4 + (-1 / 810000) * alpha ^ 2 + (1 / 202500) * alpha ^ 2 * c + (-1 / 135000) * alpha ^ 2 * c ^ 2 + (1 / 202500) * alpha ^ 2 * c ^ 3 + (-1 / 810000) * alpha ^ 2 * c ^ 4) * alpha_sq + ((-37 / 16875) + (1 / 16875) * c + (-1 / 101250) * c ^ 2 + (37 / 16875) * alpha + (1 / 50625) * alpha * c + (1 / 101250) * alpha * c ^ 2) * c_sq
theorem phase48_32 : ((r ^ 3 * thetaMinus) : ℂ) ^ 3 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 2 = ((1 / 10) + (1 / 30) * c + (-1 / 30) * alpha + (1 / 30) * alpha * c) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-7 / 2700000) + (29 / 8100000) * c + (-1 / 4050000) * c ^ 2 + (-1 / 12150000) * c ^ 3 + (-11 / 24300000) * c ^ 4 + (-1 / 4860000) * c ^ 5 + (7 / 8100000) * alpha + (-19 / 8100000) * alpha * c + (1 / 486000) * alpha * c ^ 2 + (-1 / 1350000) * alpha * c ^ 3 + (1 / 2700000) * alpha * c ^ 4 + (-1 / 4860000) * alpha * c ^ 5 + (1 / 8100000) * alpha ^ 2 + (-11 / 24300000) * alpha ^ 2 * c + (7 / 12150000) * alpha ^ 2 * c ^ 2 + (-1 / 4050000) * alpha ^ 2 * c ^ 3 + (-1 / 24300000) * alpha ^ 2 * c ^ 4 + (1 / 24300000) * alpha ^ 2 * c ^ 5 + (-1 / 24300000) * alpha ^ 3 + (1 / 4860000) * alpha ^ 3 * c + (-1 / 2430000) * alpha ^ 3 * c ^ 2 + (1 / 2430000) * alpha ^ 3 * c ^ 3 + (-1 / 4860000) * alpha ^ 3 * c ^ 4 + (1 / 24300000) * alpha ^ 3 * c ^ 5) * alpha_sq + ((38 / 84375) + (38 / 253125) * c + (1 / 506250) * c ^ 2 + (1 / 1518750) * c ^ 3 + (-38 / 253125) * alpha + (38 / 253125) * alpha * c + (-1 / 1518750) * alpha * c ^ 2 + (1 / 1518750) * alpha * c ^ 3) * c_sq
theorem phase48_33 : ((r ^ 3 * thetaMinus) : ℂ) ^ 3 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 3 = (1) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-37 / 81000000) + (1 / 1500000) * c + (-19 / 81000000) * c ^ 2 + (1 / 4050000) * c ^ 3 + (-49 / 243000000) * c ^ 4 + (1 / 121500000) * c ^ 5 + (-7 / 243000000) * c ^ 6 + (1 / 24300000) * alpha ^ 2 + (-1 / 6750000) * alpha ^ 2 * c + (23 / 121500000) * alpha ^ 2 * c ^ 2 + (-1 / 10125000) * alpha ^ 2 * c ^ 3 + (1 / 40500000) * alpha ^ 2 * c ^ 4 + (-1 / 60750000) * alpha ^ 2 * c ^ 5 + (1 / 121500000) * alpha ^ 2 * c ^ 6 + (-1 / 729000000) * alpha ^ 4 + (1 / 121500000) * alpha ^ 4 * c + (-1 / 48600000) * alpha ^ 4 * c ^ 2 + (1 / 36450000) * alpha ^ 4 * c ^ 3 + (-1 / 48600000) * alpha ^ 4 * c ^ 4 + (1 / 121500000) * alpha ^ 4 * c ^ 5 + (-1 / 729000000) * alpha ^ 4 * c ^ 6) * alpha_sq + ((5701 / 1265625) + (77 / 3796875) * c ^ 2 + (1 / 11390625) * c ^ 4) * c_sq
theorem phase48_34 : ((r ^ 3 * thetaMinus) : ℂ) ^ 3 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 4 = ((1 / 10) + (1 / 30) * c + (1 / 30) * alpha + (-1 / 30) * alpha * c) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-37 / 810000000) + (1 / 19440000) * c + (-1 / 810000000) * c ^ 2 + (41 / 2430000000) * c ^ 3 + (-29 / 2430000000) * c ^ 4 + (-43 / 7290000000) * c ^ 5 + (-19 / 7290000000) * c ^ 6 + (-7 / 7290000000) * c ^ 7 + (-37 / 2430000000) * alpha + (91 / 2430000000) * alpha * c + (-73 / 2430000000) * alpha * c ^ 2 + (13 / 810000000) * alpha * c ^ 3 + (-109 / 7290000000) * alpha * c ^ 4 + (17 / 2430000000) * alpha * c ^ 5 + (-1 / 810000000) * alpha * c ^ 6 + (7 / 7290000000) * alpha * c ^ 7 + (1 / 243000000) * alpha ^ 2 + (-49 / 3645000000) * alpha ^ 2 * c + (17 / 1215000000) * alpha ^ 2 * c ^ 2 + (-13 / 3645000000) * alpha ^ 2 * c ^ 3 + (-1 / 1215000000) * alpha ^ 2 * c ^ 4 + (-1 / 1215000000) * alpha ^ 2 * c ^ 5 + (1 / 3645000000) * alpha ^ 2 * c ^ 6 + (1 / 3645000000) * alpha ^ 2 * c ^ 7 + (1 / 729000000) * alpha ^ 3 + (-23 / 3645000000) * alpha ^ 3 * c + (41 / 3645000000) * alpha ^ 3 * c ^ 2 + (-7 / 729000000) * alpha ^ 3 * c ^ 3 + (1 / 243000000) * alpha ^ 3 * c ^ 4 + (-1 / 729000000) * alpha ^ 3 * c ^ 5 + (1 / 1215000000) * alpha ^ 3 * c ^ 6 + (-1 / 3645000000) * alpha ^ 3 * c ^ 7 + (-1 / 7290000000) * alpha ^ 4 + (17 / 21870000000) * alpha ^ 4 * c + (-13 / 7290000000) * alpha ^ 4 * c ^ 2 + (1 / 486000000) * alpha ^ 4 * c ^ 3 + (-1 / 874800000) * alpha ^ 4 * c ^ 4 + (1 / 7290000000) * alpha ^ 4 * c ^ 5 + (1 / 7290000000) * alpha ^ 4 * c ^ 6 + (-1 / 21870000000) * alpha ^ 4 * c ^ 7 + (-1 / 21870000000) * alpha ^ 5 + (7 / 21870000000) * alpha ^ 5 * c + (-7 / 7290000000) * alpha ^ 5 * c ^ 2 + (7 / 4374000000) * alpha ^ 5 * c ^ 3 + (-7 / 4374000000) * alpha ^ 5 * c ^ 4 + (7 / 7290000000) * alpha ^ 5 * c ^ 5 + (-7 / 21870000000) * alpha ^ 5 * c ^ 6 + (1 / 21870000000) * alpha ^ 5 * c ^ 7) * alpha_sq + ((5701 / 12656250) + (5701 / 37968750) * c + (77 / 37968750) * c ^ 2 + (77 / 113906250) * c ^ 3 + (1 / 113906250) * c ^ 4 + (1 / 341718750) * c ^ 5 + (5701 / 37968750) * alpha + (-5701 / 37968750) * alpha * c + (77 / 113906250) * alpha * c ^ 2 + (-77 / 113906250) * alpha * c ^ 3 + (1 / 341718750) * alpha * c ^ 4 + (-1 / 341718750) * alpha * c ^ 5) * c_sq
theorem phase48_40 : ((r ^ 3 * thetaMinus) : ℂ) ^ 4 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 0 = ((-5033 / 11250) + (-146 / 5625) * c + (-5033 / 11250) * alpha + (146 / 16875) * alpha * c) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((17 / 270000) + (-1 / 13500) * c + (-1 / 27000) * c ^ 2 + (1 / 22500) * c ^ 3 + (1 / 270000) * c ^ 4 + (-1 / 67500) * alpha + (2 / 50625) * alpha * c + (-1 / 33750) * alpha * c ^ 2 + (1 / 202500) * alpha * c ^ 4 + (1 / 810000) * alpha ^ 2 + (-1 / 202500) * alpha ^ 2 * c + (1 / 135000) * alpha ^ 2 * c ^ 2 + (-1 / 202500) * alpha ^ 2 * c ^ 3 + (1 / 810000) * alpha ^ 2 * c ^ 4) * alpha_sq + ((-34 / 16875) + (-2 / 16875) * c + (-1 / 101250) * c ^ 2 + (-34 / 16875) * alpha + (2 / 50625) * alpha * c + (-1 / 101250) * alpha * c ^ 2) * c_sq
theorem phase48_41 : ((r ^ 3 * thetaMinus) : ℂ) ^ 4 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 1 = ((-71 / 1125) * c + (221 / 1125) * alpha) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 300000) + (-17 / 2700000) * c + (1 / 270000) * c ^ 2 + (-17 / 12150000) * c ^ 3 + (1 / 4860000) * c ^ 4 + (11 / 24300000) * c ^ 5 + (1 / 1620000) * alpha + (-1 / 900000) * alpha * c + (-1 / 2430000) * alpha * c ^ 2 + (7 / 4050000) * alpha * c ^ 3 + (-7 / 8100000) * alpha * c ^ 4 + (1 / 24300000) * alpha * c ^ 5 + (-1 / 2700000) * alpha ^ 2 + (11 / 8100000) * alpha ^ 2 * c + (-7 / 4050000) * alpha ^ 2 * c ^ 2 + (1 / 1350000) * alpha ^ 2 * c ^ 3 + (1 / 8100000) * alpha ^ 2 * c ^ 4 + (-1 / 8100000) * alpha ^ 2 * c ^ 5 + (1 / 24300000) * alpha ^ 3 + (-1 / 4860000) * alpha ^ 3 * c + (1 / 2430000) * alpha ^ 3 * c ^ 2 + (-1 / 2430000) * alpha ^ 3 * c ^ 3 + (1 / 4860000) * alpha ^ 3 * c ^ 4 + (-1 / 24300000) * alpha ^ 3 * c ^ 5) * alpha_sq + ((-8 / 28125) * c + (-1 / 759375) * c ^ 3 + (224 / 253125) * alpha + (1 / 253125) * alpha * c ^ 2) * c_sq
theorem phase48_42 : ((r ^ 3 * thetaMinus) : ℂ) ^ 4 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 2 = ((-73 / 150) + (1 / 75) * c + (73 / 150) * alpha + (1 / 225) * alpha * c) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 16200000) + (-1 / 8100000) * c + (103 / 243000000) * c ^ 2 + (-17 / 60750000) * c ^ 3 + (77 / 729000000) * c ^ 4 + (-29 / 364500000) * c ^ 5 + (11 / 729000000) * c ^ 6 + (7 / 40500000) * alpha + (-1 / 2430000) * alpha * c + (31 / 121500000) * alpha * c ^ 2 + (-1 / 91125000) * alpha * c ^ 3 + (1 / 40500000) * alpha * c ^ 4 + (-1 / 60750000) * alpha * c ^ 5 + (-1 / 72900000) * alpha * c ^ 6 + (-1 / 60750000) * alpha ^ 2 + (1 / 15187500) * alpha ^ 2 * c + (-19 / 182250000) * alpha ^ 2 * c ^ 2 + (1 / 11390625) * alpha ^ 2 * c ^ 3 + (-1 / 20250000) * alpha ^ 2 * c ^ 4 + (1 / 45562500) * alpha ^ 2 * c ^ 5 + (-1 / 182250000) * alpha ^ 2 * c ^ 6 + (-1 / 121500000) * alpha ^ 3 + (7 / 182250000) * alpha ^ 3 * c + (-1 / 14580000) * alpha ^ 3 * c ^ 2 + (1 / 18225000) * alpha ^ 3 * c ^ 3 + (-1 / 72900000) * alpha ^ 3 * c ^ 4 + (-1 / 182250000) * alpha ^ 3 * c ^ 5 + (1 / 364500000) * alpha ^ 3 * c ^ 6 + (1 / 729000000) * alpha ^ 4 + (-1 / 121500000) * alpha ^ 4 * c + (1 / 48600000) * alpha ^ 4 * c ^ 2 + (-1 / 36450000) * alpha ^ 4 * c ^ 3 + (1 / 48600000) * alpha ^ 4 * c ^ 4 + (-1 / 121500000) * alpha ^ 4 * c ^ 5 + (1 / 729000000) * alpha ^ 4 * c ^ 6) * alpha_sq + ((-5549 / 2531250) + (76 / 1265625) * c + (-1 / 101250) * c ^ 2 + (1 / 3796875) * c ^ 3 + (-1 / 22781250) * c ^ 4 + (5549 / 2531250) * alpha + (76 / 3796875) * alpha * c + (1 / 101250) * alpha * c ^ 2 + (1 / 11390625) * alpha * c ^ 3 + (1 / 22781250) * alpha * c ^ 4) * c_sq
theorem phase48_43 : ((r ^ 3 * thetaMinus) : ℂ) ^ 4 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 3 = ((1 / 10) + (1 / 30) * c + (-1 / 30) * alpha + (1 / 30) * alpha * c) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-37 / 810000000) + (1 / 19440000) * c + (-1 / 810000000) * c ^ 2 + (41 / 2430000000) * c ^ 3 + (-29 / 2430000000) * c ^ 4 + (-43 / 7290000000) * c ^ 5 + (-19 / 7290000000) * c ^ 6 + (-7 / 7290000000) * c ^ 7 + (37 / 2430000000) * alpha + (-91 / 2430000000) * alpha * c + (73 / 2430000000) * alpha * c ^ 2 + (-13 / 810000000) * alpha * c ^ 3 + (109 / 7290000000) * alpha * c ^ 4 + (-17 / 2430000000) * alpha * c ^ 5 + (1 / 810000000) * alpha * c ^ 6 + (-7 / 7290000000) * alpha * c ^ 7 + (1 / 243000000) * alpha ^ 2 + (-49 / 3645000000) * alpha ^ 2 * c + (17 / 1215000000) * alpha ^ 2 * c ^ 2 + (-13 / 3645000000) * alpha ^ 2 * c ^ 3 + (-1 / 1215000000) * alpha ^ 2 * c ^ 4 + (-1 / 1215000000) * alpha ^ 2 * c ^ 5 + (1 / 3645000000) * alpha ^ 2 * c ^ 6 + (1 / 3645000000) * alpha ^ 2 * c ^ 7 + (-1 / 729000000) * alpha ^ 3 + (23 / 3645000000) * alpha ^ 3 * c + (-41 / 3645000000) * alpha ^ 3 * c ^ 2 + (7 / 729000000) * alpha ^ 3 * c ^ 3 + (-1 / 243000000) * alpha ^ 3 * c ^ 4 + (1 / 729000000) * alpha ^ 3 * c ^ 5 + (-1 / 1215000000) * alpha ^ 3 * c ^ 6 + (1 / 3645000000) * alpha ^ 3 * c ^ 7 + (-1 / 7290000000) * alpha ^ 4 + (17 / 21870000000) * alpha ^ 4 * c + (-13 / 7290000000) * alpha ^ 4 * c ^ 2 + (1 / 486000000) * alpha ^ 4 * c ^ 3 + (-1 / 874800000) * alpha ^ 4 * c ^ 4 + (1 / 7290000000) * alpha ^ 4 * c ^ 5 + (1 / 7290000000) * alpha ^ 4 * c ^ 6 + (-1 / 21870000000) * alpha ^ 4 * c ^ 7 + (1 / 21870000000) * alpha ^ 5 + (-7 / 21870000000) * alpha ^ 5 * c + (7 / 7290000000) * alpha ^ 5 * c ^ 2 + (-7 / 4374000000) * alpha ^ 5 * c ^ 3 + (7 / 4374000000) * alpha ^ 5 * c ^ 4 + (-7 / 7290000000) * alpha ^ 5 * c ^ 5 + (7 / 21870000000) * alpha ^ 5 * c ^ 6 + (-1 / 21870000000) * alpha ^ 5 * c ^ 7) * alpha_sq + ((5701 / 12656250) + (5701 / 37968750) * c + (77 / 37968750) * c ^ 2 + (77 / 113906250) * c ^ 3 + (1 / 113906250) * c ^ 4 + (1 / 341718750) * c ^ 5 + (-5701 / 37968750) * alpha + (5701 / 37968750) * alpha * c + (-77 / 113906250) * alpha * c ^ 2 + (77 / 113906250) * alpha * c ^ 3 + (-1 / 341718750) * alpha * c ^ 4 + (1 / 341718750) * alpha * c ^ 5) * c_sq
theorem phase48_44 : ((r ^ 3 * thetaMinus) : ℂ) ^ 4 * star ((r ^ 3 * thetaMinus) : ℂ) ^ 4 = (1) := by
  rw [site48]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-7 / 972000000) + (1 / 112500000) * c + (-67 / 18225000000) * c ^ 2 + (7 / 1012500000) * c ^ 3 + (-151 / 36450000000) * c ^ 4 + (7 / 9112500000) * c ^ 5 + (-47 / 32805000000) * c ^ 6 + (1 / 82012500000) * c ^ 7 + (-17 / 131220000000) * c ^ 8 + (67 / 72900000000) * alpha ^ 2 + (-1 / 337500000) * alpha ^ 2 * c + (7 / 2187000000) * alpha ^ 2 * c ^ 2 + (-13 / 9112500000) * alpha ^ 2 * c ^ 3 + (91 / 109350000000) * alpha ^ 2 * c ^ 4 + (-23 / 27337500000) * alpha ^ 2 * c ^ 5 + (1 / 3645000000) * alpha ^ 2 * c ^ 6 + (-1 / 27337500000) * alpha ^ 2 * c ^ 7 + (1 / 24300000000) * alpha ^ 2 * c ^ 8 + (-13 / 218700000000) * alpha ^ 4 + (1 / 3037500000) * alpha ^ 4 * c + (-121 / 164025000000) * alpha ^ 4 * c ^ 2 + (23 / 27337500000) * alpha ^ 4 * c ^ 3 + (-11 / 21870000000) * alpha ^ 4 * c ^ 4 + (13 / 82012500000) * alpha ^ 4 * c ^ 5 + (-1 / 18225000000) * alpha ^ 4 * c ^ 6 + (1 / 27337500000) * alpha ^ 4 * c ^ 7 + (-7 / 656100000000) * alpha ^ 4 * c ^ 8 + (1 / 656100000000) * alpha ^ 6 + (-1 / 82012500000) * alpha ^ 6 * c + (7 / 164025000000) * alpha ^ 6 * c ^ 2 + (-7 / 82012500000) * alpha ^ 6 * c ^ 3 + (7 / 65610000000) * alpha ^ 6 * c ^ 4 + (-7 / 82012500000) * alpha ^ 6 * c ^ 5 + (7 / 164025000000) * alpha ^ 6 * c ^ 6 + (-1 / 82012500000) * alpha ^ 6 * c ^ 7 + (1 / 656100000000) * alpha ^ 6 * c ^ 8) * alpha_sq + ((427576 / 94921875) + (214 / 10546875) * c ^ 2 + (26 / 284765625) * c ^ 4 + (1 / 2562890625) * c ^ 6) * c_sq
noncomputable def z48 : Fin 48 → ℂ := Fin.snoc z47 (r ^ 3 * thetaMinus)
theorem v48_00 (t : ℂ) : (momentPoly 48 z48 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00]
  try simp only [phase48_00]
  try simp only [star_one, star_neg]
  ring
theorem v48_01 (t : ℂ) : (momentPoly 48 z48 0 1).eval t = ((3 / 5) * t + (-2 / 15) * c * t + (1 / 5) * alpha * t + (2 / 15) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01]
  try simp only [phase48_00, phase48_01]
  try simp only [star_one, star_neg]
  ring
theorem v48_02 (t : ℂ) : (momentPoly 48 z48 0 2).eval t = ((-11 / 24) * t ^ 2 + (-1439 / 200) * t ^ 4 + (-4 / 15) * c * t ^ 2 + (-4 / 75) * c * t ^ 4 + (29 / 40) * alpha * t ^ 2 + (-5027 / 600) * alpha * t ^ 4 + (4 / 45) * alpha * c * t ^ 2 + (4 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02]
  try simp only [phase48_00, phase48_01, phase48_02]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 90) * t ^ 2 + (-1 / 90) * c ^ 2 * t ^ 2) * alpha_sq + ((1 / 45) * t ^ 2 + (1 / 45) * alpha * t ^ 2) * c_sq
theorem v48_03 (t : ℂ) : (momentPoly 48 z48 0 3).eval t = ((-213 / 100) * t ^ 3 + (213 / 100) * t ^ 5 + (-1271 / 150) * c * t ^ 3 + (1807 / 150) * c * t ^ 5 + (284 / 1125) * c * t ^ 9 + (1381 / 300) * alpha * t ^ 3 + (-6653 / 300) * alpha * t ^ 5 + (-442 / 375) * alpha * t ^ 9 + (-71 / 150) * alpha * c * t ^ 3 + (71 / 150) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_03]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03]
  try simp only [star_one, star_neg]
  linear_combination ((-171 / 400) * t ^ 3 + (-413 / 400) * t ^ 5 + (1571 / 3600) * c * t ^ 3 + (131 / 240) * c * t ^ 5 + (-2 / 225) * c ^ 2 * t ^ 3 + (-1 / 225) * c ^ 2 * t ^ 5) * alpha_sq + ((8 / 225) * alpha * t ^ 3 + (4 / 225) * alpha * t ^ 5) * c_sq
theorem v48_04 (t : ℂ) : (momentPoly 48 z48 0 4).eval t = ((1032581 / 4800) * t ^ 4 + (589453 / 4000) * t ^ 6 + (-21902801 / 48000) * t ^ 8 + (-2693 / 1440) * t ^ 10 + (-1511429 / 240000) * t ^ 16 + (-5872 / 375) * c * t ^ 4 + (6976 / 375) * c * t ^ 6 + (584 / 125) * c * t ^ 8 + (2336 / 1125) * c * t ^ 10 + (584 / 5625) * c * t ^ 16 + (-5556967 / 24000) * alpha * t ^ 4 + (-70169 / 12000) * alpha * t ^ 6 + (5381989 / 16000) * alpha * t ^ 8 + (-20053 / 4000) * alpha * t ^ 10 + (5773297 / 720000) * alpha * t ^ 16 + (-7292 / 1125) * alpha * c * t ^ 4 + (2704 / 375) * alpha * c * t ^ 6 + (2036 / 1125) * alpha * c * t ^ 8 + (2336 / 3375) * alpha * c * t ^ 10 + (584 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_03, v47_04]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04]
  try simp only [star_one, star_neg]
  linear_combination ((-877 / 4500) * t ^ 4 + (85813 / 9000) * t ^ 6 + (69131 / 3000) * t ^ 8 + (-884 / 3375) * t ^ 10 + (29 / 250) * c * t ^ 4 + (12967 / 4500) * c * t ^ 6 + (131 / 900) * c * t ^ 8 + (71 / 900) * c ^ 2 * t ^ 4 + (-1097 / 13500) * c ^ 2 * t ^ 6 + (-2 / 3375) * c ^ 2 * t ^ 8) * alpha_sq + ((-1247 / 1125) * t ^ 4 + (263 / 125) * t ^ 6 + (-4 / 1125) * t ^ 8 + (284 / 3375) * t ^ 10 + (892 / 1125) * alpha * t ^ 4 + (-2012 / 1125) * alpha * t ^ 6 + (4 / 1125) * alpha * t ^ 8 + (-284 / 3375) * alpha * t ^ 10) * c_sq
theorem v48_10 (t : ℂ) : (momentPoly 48 z48 1 0).eval t = ((3 / 5) * t + (-2 / 15) * c * t + (-1 / 5) * alpha * t + (-2 / 15) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_10]
  try simp only [phase48_00, phase48_10]
  try simp only [star_one, star_neg]
  ring
theorem v48_11 (t : ℂ) : (momentPoly 48 z48 1 1).eval t = (48 + (-476 / 15) * t ^ 2) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_10, v47_11]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 90) * t ^ 2 + (1 / 90) * c ^ 2 * t ^ 2) * alpha_sq + ((-2 / 45) * t ^ 2) * c_sq
theorem v48_12 (t : ℂ) : (momentPoly 48 z48 1 2).eval t = (57 * t + (-3034 / 75) * t ^ 3 + (-509 / 75) * t ^ 5 + (-38 / 3) * c * t + (115 / 9) * c * t ^ 3 + (-57 / 25) * c * t ^ 5 + 19 * alpha * t + (-1171 / 90) * alpha * t ^ 3 + (-1231 / 450) * alpha * t ^ 5 + (38 / 3) * alpha * c * t + (-2804 / 225) * alpha * c * t ^ 3 + (442 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_10, v47_11, v47_12]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12]
  try simp only [star_one, star_neg]
  linear_combination ((57 / 400) * t ^ 3 + (413 / 1200) * t ^ 5 + (-1571 / 10800) * c * t ^ 3 + (-131 / 720) * c * t ^ 5 + (2 / 675) * c ^ 2 * t ^ 3 + (1 / 675) * c ^ 2 * t ^ 5) * alpha_sq + ((-4 / 225) * t ^ 3 + (-2 / 225) * t ^ 5 + (-4 / 675) * alpha * t ^ 3 + (-2 / 675) * alpha * t ^ 5) * c_sq
theorem v48_13 (t : ℂ) : (momentPoly 48 z48 1 3).eval t = ((-517 / 8) * t ^ 2 + (-561133 / 750) * t ^ 4 + (1033939 / 1500) * t ^ 6 + (-8861 / 9000) * t ^ 10 + (-188 / 5) * c * t ^ 2 + (3248 / 125) * c * t ^ 4 + (2504 / 375) * c * t ^ 6 + (-4 / 15) * c * t ^ 10 + (4089 / 40) * alpha * t ^ 2 + (-255441 / 250) * alpha * t ^ 4 + (397423 / 500) * alpha * t ^ 6 + (1789 / 9000) * alpha * t ^ 10 + (188 / 15) * alpha * c * t ^ 2 + (-3248 / 375) * alpha * c * t ^ 4 + (-2504 / 1125) * alpha * c * t ^ 6 + (4 / 45) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_03, v47_10, v47_11, v47_12, v47_13]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13]
  try simp only [star_one, star_neg]
  linear_combination ((47 / 30) * t ^ 2 + (-17093 / 18000) * t ^ 4 + (10837 / 18000) * t ^ 6 + (221 / 3375) * t ^ 10 + (-442 / 1125) * c * t ^ 4 + (-442 / 1125) * c * t ^ 6 + (-47 / 30) * c ^ 2 * t ^ 2 + (537 / 400) * c ^ 2 * t ^ 4 + (-251 / 1200) * c ^ 2 * t ^ 6) * alpha_sq + ((47 / 15) * t ^ 2 + (-12797 / 4500) * t ^ 4 + (3733 / 4500) * t ^ 6 + (71 / 3375) * t ^ 10 + (47 / 15) * alpha * t ^ 2 + (-13507 / 4500) * alpha * t ^ 4 + (1481 / 1500) * alpha * t ^ 6 + (71 / 3375) * alpha * t ^ 10) * c_sq
theorem v48_14 (t : ℂ) : (momentPoly 48 z48 1 4).eval t = ((-19809 / 50) * t ^ 3 + (39628987 / 60000) * t ^ 5 + (-6136867 / 30000) * t ^ 7 + (-6456403 / 120000) * t ^ 9 + (-209101 / 30000) * t ^ 11 + (123901 / 120000) * t ^ 17 + (-39401 / 25) * c * t ^ 3 + (109420771 / 30000) * c * t ^ 5 + (-32583691 / 15000) * c * t ^ 7 + (40121743 / 180000) * c * t ^ 9 + (-8588237 / 135000) * c * t ^ 11 + (232661 / 60000) * c * t ^ 17 + (42811 / 50) * alpha * t ^ 3 + (-270577207 / 60000) * alpha * t ^ 5 + (32558309 / 10000) * alpha * t ^ 7 + (-27788051 / 360000) * alpha * t ^ 9 + (44974969 / 270000) * alpha * t ^ 11 + (680779 / 216000) * alpha * t ^ 17 + (-2201 / 25) * alpha * c * t ^ 3 + (15777271 / 90000) * alpha * c * t ^ 5 + (-4613231 / 45000) * alpha * c * t ^ 7 + (2735281 / 180000) * alpha * c * t ^ 9 + (38701 / 135000) * alpha * c * t ^ 11 + (-123901 / 540000) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_03, v47_04, v47_10, v47_11, v47_12, v47_13, v47_14]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14]
  try simp only [star_one, star_neg]
  linear_combination ((-15903 / 200) * t ^ 3 + (-48813833 / 720000) * t ^ 5 + (32269993 / 360000) * t ^ 7 + (-8385263 / 1440000) * t ^ 9 + (-378641 / 360000) * t ^ 11 + (-470783 / 1440000) * t ^ 17 + (48701 / 600) * c * t ^ 3 + (-53165413 / 2160000) * c * t ^ 5 + (-7551449 / 360000) * c * t ^ 7 + (13160717 / 4320000) * c * t ^ 9 + (3371417 / 3240000) * c * t ^ 11 + (1229 / 6912) * c * t ^ 17 + (-124 / 75) * c ^ 2 * t ^ 3 + (6904 / 16875) * c ^ 2 * t ^ 5 + (30209 / 33750) * c ^ 2 * t ^ 7 + (113 / 11250) * c ^ 2 * t ^ 9 + (568 / 50625) * c ^ 2 * t ^ 11 + (146 / 50625) * c ^ 2 * t ^ 17) * alpha_sq + ((142 / 1125) * t ^ 5 + (-71 / 1125) * t ^ 7 + (-71 / 1125) * t ^ 9 + (496 / 75) * alpha * t ^ 3 + (-16618 / 5625) * alpha * t ^ 5 + (-2933 / 1875) * alpha * t ^ 7 + (8563 / 16875) * alpha * t ^ 9 + (7072 / 50625) * alpha * t ^ 11 + (584 / 50625) * alpha * t ^ 17) * c_sq
theorem v48_20 (t : ℂ) : (momentPoly 48 z48 2 0).eval t = ((-11 / 24) * t ^ 2 + (-1439 / 200) * t ^ 4 + (-4 / 15) * c * t ^ 2 + (-4 / 75) * c * t ^ 4 + (-29 / 40) * alpha * t ^ 2 + (5027 / 600) * alpha * t ^ 4 + (-4 / 45) * alpha * c * t ^ 2 + (-4 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_10, v47_20]
  try simp only [phase48_00, phase48_10, phase48_20]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 90) * t ^ 2 + (-1 / 90) * c ^ 2 * t ^ 2) * alpha_sq + ((1 / 45) * t ^ 2 + (-1 / 45) * alpha * t ^ 2) * c_sq
theorem v48_21 (t : ℂ) : (momentPoly 48 z48 2 1).eval t = (57 * t + (-3034 / 75) * t ^ 3 + (-509 / 75) * t ^ 5 + (-38 / 3) * c * t + (115 / 9) * c * t ^ 3 + (-57 / 25) * c * t ^ 5 + (-19) * alpha * t + (1171 / 90) * alpha * t ^ 3 + (1231 / 450) * alpha * t ^ 5 + (-38 / 3) * alpha * c * t + (2804 / 225) * alpha * c * t ^ 3 + (-442 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_10, v47_11, v47_20, v47_21]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21]
  try simp only [star_one, star_neg]
  linear_combination ((57 / 400) * t ^ 3 + (413 / 1200) * t ^ 5 + (-1571 / 10800) * c * t ^ 3 + (-131 / 720) * c * t ^ 5 + (2 / 675) * c ^ 2 * t ^ 3 + (1 / 675) * c ^ 2 * t ^ 5) * alpha_sq + ((-4 / 225) * t ^ 3 + (-2 / 225) * t ^ 5 + (4 / 675) * alpha * t ^ 3 + (2 / 675) * alpha * t ^ 5) * c_sq
theorem v48_22 (t : ℂ) : (momentPoly 48 z48 2 2).eval t = (4560 + (-89488 / 15) * t ^ 2 + (1619723 / 1200) * t ^ 4 + (949523 / 9000) * t ^ 6 + (3873589 / 18000) * t ^ 8 + (142 / 225) * c * t ^ 4 + (-568 / 1125) * c * t ^ 6 + (-142 / 1125) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_10, v47_11, v47_12, v47_20, v47_21, v47_22]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22]
  try simp only [star_one, star_neg]
  linear_combination ((-94 / 45) * t ^ 2 + (599 / 450) * t ^ 4 + (-3981 / 1000) * t ^ 6 + (-69131 / 9000) * t ^ 8 + (131 / 270) * c * t ^ 4 + (-131 / 300) * c * t ^ 6 + (-131 / 2700) * c * t ^ 8 + (94 / 45) * c ^ 2 * t ^ 2 + (-1226 / 675) * c ^ 2 * t ^ 4 + (3098 / 10125) * c ^ 2 * t ^ 6 + (2 / 10125) * c ^ 2 * t ^ 8) * alpha_sq + ((-376 / 45) * t ^ 2 + (3293 / 450) * t ^ 4 + (-8659 / 6750) * t ^ 6 + (-8 / 3375) * t ^ 8) * c_sq
theorem v48_23 (t : ℂ) : (momentPoly 48 z48 2 3).eval t = ((40188 / 5) * t + (-282162 / 25) * t ^ 3 + (10300411 / 6000) * t ^ 5 + (19919831 / 15000) * t ^ 7 + (3408169 / 10000) * t ^ 9 + (-88537 / 22500) * t ^ 11 + (585829 / 22500) * t ^ 13 + (-26792 / 15) * c * t + 3565 * c * t ^ 3 + (-7069291 / 3000) * c * t ^ 5 + (13817887 / 22500) * c * t ^ 7 + (-3340321 / 45000) * c * t ^ 9 + (139387 / 33750) * c * t ^ 11 + (-6547 / 3750) * c * t ^ 13 + (13396 / 5) * alpha * t + (-36301 / 10) * alpha * t ^ 3 + (6202291 / 18000) * alpha * t ^ 5 + (24600151 / 45000) * alpha * t ^ 7 + (9383867 / 90000) * alpha * t ^ 9 + (69509 / 67500) * alpha * t ^ 11 + (491683 / 67500) * alpha * t ^ 13 + (26792 / 15) * alpha * c * t + (-86924 / 25) * alpha * c * t ^ 3 + (19732777 / 9000) * alpha * c * t ^ 5 + (-12119567 / 22500) * alpha * c * t ^ 7 + (3328961 / 45000) * alpha * c * t ^ 9 + (-4747 / 1250) * alpha * c * t ^ 11 + (13801 / 6750) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_03, v47_10, v47_11, v47_12, v47_13, v47_20, v47_21, v47_22, v47_23]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23]
  try simp only [star_one, star_neg]
  linear_combination ((15903 / 400) * t ^ 3 + (16271 / 400) * t ^ 5 + (-4654831 / 90000) * t ^ 7 + (-1145881 / 90000) * t ^ 9 + (-1387 / 2500) * t ^ 11 + (-91273 / 45000) * t ^ 13 + (-48701 / 1200) * c * t ^ 3 + (809 / 144) * c * t ^ 5 + (4387681 / 270000) * c * t ^ 7 + (948631 / 270000) * c * t ^ 9 + (-110753 / 405000) * c * t ^ 11 + (62 / 75) * c ^ 2 * t ^ 3 + (-199 / 675) * c ^ 2 * t ^ 5 + (-343 / 1080) * c ^ 2 * t ^ 7 + (179 / 5400) * c ^ 2 * t ^ 9 + (4 / 675) * c ^ 2 * t ^ 11) * alpha_sq + ((-124 / 25) * t ^ 3 + (229 / 125) * t ^ 5 + (6671 / 3750) * t ^ 7 + (-43 / 1250) * t ^ 9 + (-316 / 16875) * t ^ 11 + (142 / 16875) * t ^ 13 + (-124 / 75) * alpha * t ^ 3 + (1777 / 3375) * alpha * t ^ 5 + (21433 / 33750) * alpha * t ^ 7 + (1033 / 33750) * alpha * t ^ 9 + (-316 / 50625) * alpha * t ^ 11 + (142 / 50625) * alpha * t ^ 13) * c_sq
theorem v48_24 (t : ℂ) : (momentPoly 48 z48 2 4).eval t = ((-144265 / 12) * t ^ 2 + (-272267771 / 3000) * t ^ 4 + (245588300623 / 1440000) * t ^ 6 + (-88880435981 / 1440000) * t ^ 8 + (-17366942171 / 2880000) * t ^ 10 + (-1174465609 / 576000) * t ^ 12 + (278305579 / 2160000) * t ^ 14 + (157232203 / 8640000) * t ^ 18 + (-1294767211 / 8640000) * t ^ 20 + (-20984 / 3) * c * t ^ 2 + (1366284 / 125) * c * t ^ 4 + (-6388081 / 2250) * c * t ^ 6 + (-6528843 / 6250) * c * t ^ 8 + (-10576831 / 56250) * c * t ^ 10 + (4404859 / 56250) * c * t ^ 12 + (-2562592 / 84375) * c * t ^ 14 + (369448 / 84375) * c * t ^ 18 + (-4 / 5) * c * t ^ 20 + (76067 / 4) * alpha * t ^ 2 + (-161079767 / 1000) * alpha * t ^ 4 + (314114559569 / 1440000) * alpha * t ^ 6 + (-500804062079 / 7200000) * alpha * t ^ 8 + (-25889367923 / 4800000) * alpha * t ^ 10 + (-131383133597 / 43200000) * alpha * t ^ 12 + (126603 / 400000) * alpha * t ^ 14 + (-51903773 / 14400000) * alpha * t ^ 18 + (-4445176937 / 43200000) * alpha * t ^ 20 + (20984 / 9) * alpha * c * t ^ 2 + (-455428 / 125) * alpha * c * t ^ 4 + (12977789 / 13500) * alpha * c * t ^ 6 + (21365659 / 67500) * alpha * c * t ^ 8 + (3343451 / 45000) * alpha * c * t ^ 10 + (-607463 / 27000) * alpha * c * t ^ 12 + (1215673 / 101250) * alpha * c * t ^ 14 + (-748189 / 405000) * alpha * c * t ^ 18 + (38797 / 135000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_03, v47_04, v47_10, v47_11, v47_12, v47_13, v47_14, v47_20, v47_21, v47_22, v47_23, v47_24]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24]
  try simp only [star_one, star_neg]
  linear_combination ((2623 / 9) * t ^ 2 + (-393139 / 1125) * t ^ 4 + (300181147 / 1080000) * t ^ 6 + (-1344709651 / 3600000) * t ^ 8 + (2326050071 / 10800000) * t ^ 10 + (914879599 / 7200000) * t ^ 12 + (3973171 / 600000) * t ^ 14 + (2347813 / 1200000) * t ^ 18 + (155847317 / 21600000) * t ^ 20 + (-162656 / 1125) * c * t ^ 4 + (-3471719 / 540000) * c * t ^ 6 + (586106021 / 5400000) * c * t ^ 8 + (25451353 / 5400000) * c * t ^ 10 + (-12145129 / 10800000) * c * t ^ 12 + (5047457 / 2700000) * c * t ^ 14 + (-182887 / 1800000) * c * t ^ 18 + (-50797 / 2160000) * c * t ^ 20 + (-2623 / 9) * c ^ 2 * t ^ 2 + (12351 / 25) * c ^ 2 * t ^ 4 + (-97745903 / 360000) * c ^ 2 * t ^ 6 + (506883491 / 8100000) * c ^ 2 * t ^ 8 + (-100501171 / 10800000) * c ^ 2 * t ^ 10 + (3474473 / 8100000) * c ^ 2 * t ^ 12 + (-958231 / 3037500) * c ^ 2 * t ^ 14 + (-1783763 / 97200000) * c ^ 2 * t ^ 18 + (292 / 759375) * c ^ 2 * t ^ 20) * alpha_sq + ((5246 / 9) * t ^ 2 + (-1177324 / 1125) * t ^ 4 + (39704903 / 54000) * t ^ 6 + (-173008847 / 675000) * t ^ 8 + (102903311 / 2700000) * t ^ 10 + (-5824091 / 675000) * t ^ 12 + (350002 / 253125) * t ^ 14 + (2949041 / 8100000) * t ^ 18 + (584 / 253125) * t ^ 20 + (5246 / 9) * alpha * t ^ 2 + (-1242644 / 1125) * alpha * t ^ 4 + (22722833 / 27000) * alpha * t ^ 6 + (-104383481 / 337500) * alpha * t ^ 8 + (9676163 / 225000) * alpha * t ^ 10 + (-2156296 / 253125) * alpha * t ^ 12 + (11096 / 9375) * alpha * t ^ 14 + (24266 / 84375) * alpha * t ^ 18 + (584 / 253125) * alpha * t ^ 20) * c_sq
theorem v48_30 (t : ℂ) : (momentPoly 48 z48 3 0).eval t = ((-213 / 100) * t ^ 3 + (213 / 100) * t ^ 5 + (-1271 / 150) * c * t ^ 3 + (1807 / 150) * c * t ^ 5 + (284 / 1125) * c * t ^ 9 + (-1381 / 300) * alpha * t ^ 3 + (6653 / 300) * alpha * t ^ 5 + (442 / 375) * alpha * t ^ 9 + (71 / 150) * alpha * c * t ^ 3 + (-71 / 150) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_10, v47_20, v47_30]
  try simp only [phase48_00, phase48_10, phase48_20, phase48_30]
  try simp only [star_one, star_neg]
  linear_combination ((-171 / 400) * t ^ 3 + (-413 / 400) * t ^ 5 + (1571 / 3600) * c * t ^ 3 + (131 / 240) * c * t ^ 5 + (-2 / 225) * c ^ 2 * t ^ 3 + (-1 / 225) * c ^ 2 * t ^ 5) * alpha_sq + ((-8 / 225) * alpha * t ^ 3 + (-4 / 225) * alpha * t ^ 5) * c_sq
theorem v48_31 (t : ℂ) : (momentPoly 48 z48 3 1).eval t = ((-517 / 8) * t ^ 2 + (-561133 / 750) * t ^ 4 + (1033939 / 1500) * t ^ 6 + (-8861 / 9000) * t ^ 10 + (-188 / 5) * c * t ^ 2 + (3248 / 125) * c * t ^ 4 + (2504 / 375) * c * t ^ 6 + (-4 / 15) * c * t ^ 10 + (-4089 / 40) * alpha * t ^ 2 + (255441 / 250) * alpha * t ^ 4 + (-397423 / 500) * alpha * t ^ 6 + (-1789 / 9000) * alpha * t ^ 10 + (-188 / 15) * alpha * c * t ^ 2 + (3248 / 375) * alpha * c * t ^ 4 + (2504 / 1125) * alpha * c * t ^ 6 + (-4 / 45) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_10, v47_11, v47_20, v47_21, v47_30, v47_31]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21, phase48_30, phase48_31]
  try simp only [star_one, star_neg]
  linear_combination ((47 / 30) * t ^ 2 + (-17093 / 18000) * t ^ 4 + (10837 / 18000) * t ^ 6 + (221 / 3375) * t ^ 10 + (-442 / 1125) * c * t ^ 4 + (-442 / 1125) * c * t ^ 6 + (-47 / 30) * c ^ 2 * t ^ 2 + (537 / 400) * c ^ 2 * t ^ 4 + (-251 / 1200) * c ^ 2 * t ^ 6) * alpha_sq + ((47 / 15) * t ^ 2 + (-12797 / 4500) * t ^ 4 + (3733 / 4500) * t ^ 6 + (71 / 3375) * t ^ 10 + (-47 / 15) * alpha * t ^ 2 + (13507 / 4500) * alpha * t ^ 4 + (-1481 / 1500) * alpha * t ^ 6 + (-71 / 3375) * alpha * t ^ 10) * c_sq
theorem v48_32 (t : ℂ) : (momentPoly 48 z48 3 2).eval t = ((40188 / 5) * t + (-282162 / 25) * t ^ 3 + (10300411 / 6000) * t ^ 5 + (19919831 / 15000) * t ^ 7 + (3408169 / 10000) * t ^ 9 + (-88537 / 22500) * t ^ 11 + (585829 / 22500) * t ^ 13 + (-26792 / 15) * c * t + 3565 * c * t ^ 3 + (-7069291 / 3000) * c * t ^ 5 + (13817887 / 22500) * c * t ^ 7 + (-3340321 / 45000) * c * t ^ 9 + (139387 / 33750) * c * t ^ 11 + (-6547 / 3750) * c * t ^ 13 + (-13396 / 5) * alpha * t + (36301 / 10) * alpha * t ^ 3 + (-6202291 / 18000) * alpha * t ^ 5 + (-24600151 / 45000) * alpha * t ^ 7 + (-9383867 / 90000) * alpha * t ^ 9 + (-69509 / 67500) * alpha * t ^ 11 + (-491683 / 67500) * alpha * t ^ 13 + (-26792 / 15) * alpha * c * t + (86924 / 25) * alpha * c * t ^ 3 + (-19732777 / 9000) * alpha * c * t ^ 5 + (12119567 / 22500) * alpha * c * t ^ 7 + (-3328961 / 45000) * alpha * c * t ^ 9 + (4747 / 1250) * alpha * c * t ^ 11 + (-13801 / 6750) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_10, v47_11, v47_12, v47_20, v47_21, v47_22, v47_30, v47_31, v47_32]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22, phase48_30, phase48_31, phase48_32]
  try simp only [star_one, star_neg]
  linear_combination ((15903 / 400) * t ^ 3 + (16271 / 400) * t ^ 5 + (-4654831 / 90000) * t ^ 7 + (-1145881 / 90000) * t ^ 9 + (-1387 / 2500) * t ^ 11 + (-91273 / 45000) * t ^ 13 + (-48701 / 1200) * c * t ^ 3 + (809 / 144) * c * t ^ 5 + (4387681 / 270000) * c * t ^ 7 + (948631 / 270000) * c * t ^ 9 + (-110753 / 405000) * c * t ^ 11 + (62 / 75) * c ^ 2 * t ^ 3 + (-199 / 675) * c ^ 2 * t ^ 5 + (-343 / 1080) * c ^ 2 * t ^ 7 + (179 / 5400) * c ^ 2 * t ^ 9 + (4 / 675) * c ^ 2 * t ^ 11) * alpha_sq + ((-124 / 25) * t ^ 3 + (229 / 125) * t ^ 5 + (6671 / 3750) * t ^ 7 + (-43 / 1250) * t ^ 9 + (-316 / 16875) * t ^ 11 + (142 / 16875) * t ^ 13 + (124 / 75) * alpha * t ^ 3 + (-1777 / 3375) * alpha * t ^ 5 + (-21433 / 33750) * alpha * t ^ 7 + (-1033 / 33750) * alpha * t ^ 9 + (316 / 50625) * alpha * t ^ 11 + (-142 / 50625) * alpha * t ^ 13) * c_sq
theorem v48_33 (t : ℂ) : (momentPoly 48 z48 3 3).eval t = (643008 + (-1248548) * t ^ 2 + (111760887 / 200) * t ^ 4 + (1280554741 / 15000) * t ^ 6 + (44502383 / 1500) * t ^ 8 + (-39422864 / 625) * t ^ 10 + (-292229737 / 225000) * t ^ 12 + (91415633 / 225000) * t ^ 14 + (-2504636 / 84375) * t ^ 18 + (6532 / 25) * c * t ^ 4 + (-820192 / 1875) * c * t ^ 6 + (9656 / 75) * c * t ^ 8 + (84632 / 1875) * c * t ^ 10 + (284 / 75) * c * t ^ 12 + (-568 / 375) * c * t ^ 14) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_03, v47_10, v47_11, v47_12, v47_13, v47_20, v47_21, v47_22, v47_23, v47_30, v47_31, v47_32, v47_33]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23, phase48_30, phase48_31, phase48_32, phase48_33]
  try simp only [star_one, star_neg]
  linear_combination ((-2623 / 6) * t ^ 2 + (13777 / 25) * t ^ 4 + (-108365099 / 60000) * t ^ 6 + (-4943053 / 6000) * t ^ 8 + (94966609 / 60000) * t ^ 10 + (-635269 / 675000) * t ^ 12 + (-1868363 / 84375) * t ^ 14 + (-97682 / 253125) * t ^ 18 + (3013 / 15) * c * t ^ 4 + (-7571261 / 22500) * c * t ^ 6 + (5764 / 45) * c * t ^ 8 + (33434 / 5625) * c * t ^ 10 + (131 / 180) * c * t ^ 12 + (131 / 150) * c * t ^ 14 + (2623 / 6) * c ^ 2 * t ^ 2 + (-56396 / 75) * c ^ 2 * t ^ 4 + (46225099 / 108000) * c ^ 2 * t ^ 6 + (-5692283 / 54000) * c ^ 2 * t ^ 8 + (566617 / 36000) * c ^ 2 * t ^ 10 + (-16021 / 27000) * c ^ 2 * t ^ 12 + (2593 / 5400) * c ^ 2 * t ^ 14) * alpha_sq + ((-5246 / 3) * t ^ 2 + (75739 / 25) * t ^ 4 + (-78911873 / 45000) * t ^ 6 + (1981361 / 4500) * t ^ 8 + (-938719 / 15000) * t ^ 10 + (276907 / 84375) * t ^ 12 + (-615301 / 168750) * t ^ 14 + (-10082 / 253125) * t ^ 18) * c_sq
theorem v48_34 (t : ℂ) : (momentPoly 48 z48 3 4).eval t = ((7476669 / 5) * t + (-77894916 / 25) * t ^ 3 + (1448353041 / 1000) * t ^ 5 + (55634891761 / 150000) * t ^ 7 + (-3115121891 / 100000) * t ^ 9 + (-9699183563 / 60000) * t ^ 11 + (66535602509 / 9000000) * t ^ 13 + (-5296687433 / 562500) * t ^ 15 + (-2660604691 / 3000000) * t ^ 17 + (-2066913143 / 13500000) * t ^ 19 + (-2844589573 / 9000000) * t ^ 21 + (-624640379 / 27000000) * t ^ 25 + (-1661482 / 5) * c * t + 984170 * c * t ^ 3 + (-557466901 / 500) * c * t ^ 5 + (559868019877 / 900000) * c * t ^ 7 + (-174822224617 / 900000) * c * t ^ 9 + (70498147967 / 1800000) * c * t ^ 11 + (-154547414287 / 27000000) * c * t ^ 13 + (2972213987 / 2250000) * c * t ^ 15 + (-1456810423 / 13500000) * c * t ^ 17 + (4776816127 / 81000000) * c * t ^ 19 + (-1471035703 / 27000000) * c * t ^ 21 + (-21314311 / 13500000) * c * t ^ 25 + (2492223 / 5) * alpha * t + (-5010709 / 5) * alpha * t ^ 3 + (394115287 / 1000) * alpha * t ^ 5 + (70817445731 / 360000) * alpha * t ^ 7 + (-65596013287 / 1800000) * alpha * t ^ 9 + (-166719901811 / 3600000) * alpha * t ^ 11 + (-22067097041 / 54000000) * alpha * t ^ 13 + (-1277310151 / 500000) * alpha * t ^ 15 + (-11339928199 / 27000000) * alpha * t ^ 17 + (-489366059 / 6480000) * alpha * t ^ 19 + (-2947524401 / 54000000) * alpha * t ^ 21 + (-460347653 / 81000000) * alpha * t ^ 25 + (1661482 / 5) * alpha * c * t + (-23996632 / 25) * alpha * c * t ^ 3 + (1573807547 / 1500) * alpha * c * t ^ 5 + (-126818222987 / 225000) * alpha * c * t ^ 7 + (79532064533 / 450000) * alpha * c * t ^ 9 + (-3422408003 / 90000) * alpha * c * t ^ 11 + (71894866807 / 13500000) * alpha * c * t ^ 13 + (-650044912 / 421875) * alpha * c * t ^ 15 + (353861507 / 4500000) * alpha * c * t ^ 17 + (-207328583 / 2250000) * alpha * c * t ^ 19 + (1213997209 / 13500000) * alpha * c * t ^ 21 + (130459 / 64800) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_03, v47_04, v47_10, v47_11, v47_12, v47_13, v47_14, v47_20, v47_21, v47_22, v47_23, v47_24, v47_30, v47_31, v47_32, v47_33, v47_34]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24, phase48_30, phase48_31, phase48_32, phase48_33, phase48_34]
  try simp only [star_one, star_neg]
  linear_combination ((2195127 / 200) * t ^ 3 + (-1481921 / 400) * t ^ 5 + (-48798043963 / 4800000) * t ^ 7 + (-1184344909 / 320000) * t ^ 9 + (179874517877 / 28800000) * t ^ 11 + (-5828586941 / 16000000) * t ^ 13 + (76247226731 / 108000000) * t ^ 15 + (3874863523 / 54000000) * t ^ 17 + (2775484471 / 432000000) * t ^ 19 + (2586807983 / 144000000) * t ^ 21 + (104043043 / 54000000) * t ^ 25 + (-6722309 / 600) * c * t ^ 3 + (4024159 / 240) * c * t ^ 5 + (-410493759533 / 43200000) * c * t ^ 7 + (267578855507 / 43200000) * c * t ^ 9 + (-259177989631 / 86400000) * c * t ^ 11 + (283782263957 / 1296000000) * c * t ^ 13 + (-3535536667 / 108000000) * c * t ^ 15 + (76188137 / 10125000) * c * t ^ 17 + (-22150131599 / 3888000000) * c * t ^ 19 + (-12897632911 / 1296000000) * c * t ^ 21 + (17116 / 75) * c ^ 2 * t ^ 3 + (-6813 / 25) * c ^ 2 * t ^ 5 + (-393313 / 27000) * c ^ 2 * t ^ 7 + (45186389 / 600000) * c ^ 2 * t ^ 9 + (-18020371 / 2700000) * c ^ 2 * t ^ 11 + (4100131 / 10800000) * c ^ 2 * t ^ 13 + (881959 / 900000) * c ^ 2 * t ^ 15 + (12901 / 202500) * c ^ 2 * t ^ 17 + (-570737 / 4050000) * c ^ 2 * t ^ 19 + (8399 / 240000) * c ^ 2 * t ^ 21) * alpha_sq + ((-34232 / 25) * t ^ 3 + (626092 / 375) * t ^ 5 + (-109421 / 15000) * t ^ 7 + (-141793727 / 450000) * t ^ 9 + (-291983 / 10000) * t ^ 11 + (23445323 / 4500000) * t ^ 13 + (-36680257 / 3375000) * t ^ 15 + (-97928 / 140625) * t ^ 17 + (16476707 / 20250000) * t ^ 19 + (-5175023 / 13500000) * t ^ 21 + (-20732 / 1265625) * t ^ 25 + (-34232 / 75) * alpha * t ^ 3 + (191468 / 375) * alpha * t ^ 5 + (8310991 / 135000) * alpha * t ^ 7 + (-148024297 / 1350000) * alpha * t ^ 9 + (-33539677 / 1350000) * alpha * t ^ 11 + (120160879 / 40500000) * alpha * t ^ 13 + (-3424823 / 1125000) * alpha * t ^ 15 + (-344194 / 1265625) * alpha * t ^ 17 + (10271837 / 60750000) * alpha * t ^ 19 + (-4755473 / 40500000) * alpha * t ^ 21 + (-20732 / 3796875) * alpha * t ^ 25) * c_sq
theorem v48_40 (t : ℂ) : (momentPoly 48 z48 4 0).eval t = ((1032581 / 4800) * t ^ 4 + (589453 / 4000) * t ^ 6 + (-21902801 / 48000) * t ^ 8 + (-2693 / 1440) * t ^ 10 + (-1511429 / 240000) * t ^ 16 + (-5872 / 375) * c * t ^ 4 + (6976 / 375) * c * t ^ 6 + (584 / 125) * c * t ^ 8 + (2336 / 1125) * c * t ^ 10 + (584 / 5625) * c * t ^ 16 + (5556967 / 24000) * alpha * t ^ 4 + (70169 / 12000) * alpha * t ^ 6 + (-5381989 / 16000) * alpha * t ^ 8 + (20053 / 4000) * alpha * t ^ 10 + (-5773297 / 720000) * alpha * t ^ 16 + (7292 / 1125) * alpha * c * t ^ 4 + (-2704 / 375) * alpha * c * t ^ 6 + (-2036 / 1125) * alpha * c * t ^ 8 + (-2336 / 3375) * alpha * c * t ^ 10 + (-584 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_10, v47_20, v47_30, v47_40]
  try simp only [phase48_00, phase48_10, phase48_20, phase48_30, phase48_40]
  try simp only [star_one, star_neg]
  linear_combination ((-877 / 4500) * t ^ 4 + (85813 / 9000) * t ^ 6 + (69131 / 3000) * t ^ 8 + (-884 / 3375) * t ^ 10 + (29 / 250) * c * t ^ 4 + (12967 / 4500) * c * t ^ 6 + (131 / 900) * c * t ^ 8 + (71 / 900) * c ^ 2 * t ^ 4 + (-1097 / 13500) * c ^ 2 * t ^ 6 + (-2 / 3375) * c ^ 2 * t ^ 8) * alpha_sq + ((-1247 / 1125) * t ^ 4 + (263 / 125) * t ^ 6 + (-4 / 1125) * t ^ 8 + (284 / 3375) * t ^ 10 + (-892 / 1125) * alpha * t ^ 4 + (2012 / 1125) * alpha * t ^ 6 + (-4 / 1125) * alpha * t ^ 8 + (284 / 3375) * alpha * t ^ 10) * c_sq
theorem v48_41 (t : ℂ) : (momentPoly 48 z48 4 1).eval t = ((-19809 / 50) * t ^ 3 + (39628987 / 60000) * t ^ 5 + (-6136867 / 30000) * t ^ 7 + (-6456403 / 120000) * t ^ 9 + (-209101 / 30000) * t ^ 11 + (123901 / 120000) * t ^ 17 + (-39401 / 25) * c * t ^ 3 + (109420771 / 30000) * c * t ^ 5 + (-32583691 / 15000) * c * t ^ 7 + (40121743 / 180000) * c * t ^ 9 + (-8588237 / 135000) * c * t ^ 11 + (232661 / 60000) * c * t ^ 17 + (-42811 / 50) * alpha * t ^ 3 + (270577207 / 60000) * alpha * t ^ 5 + (-32558309 / 10000) * alpha * t ^ 7 + (27788051 / 360000) * alpha * t ^ 9 + (-44974969 / 270000) * alpha * t ^ 11 + (-680779 / 216000) * alpha * t ^ 17 + (2201 / 25) * alpha * c * t ^ 3 + (-15777271 / 90000) * alpha * c * t ^ 5 + (4613231 / 45000) * alpha * c * t ^ 7 + (-2735281 / 180000) * alpha * c * t ^ 9 + (-38701 / 135000) * alpha * c * t ^ 11 + (123901 / 540000) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_10, v47_11, v47_20, v47_21, v47_30, v47_31, v47_40, v47_41]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21, phase48_30, phase48_31, phase48_40, phase48_41]
  try simp only [star_one, star_neg]
  linear_combination ((-15903 / 200) * t ^ 3 + (-48813833 / 720000) * t ^ 5 + (32269993 / 360000) * t ^ 7 + (-8385263 / 1440000) * t ^ 9 + (-378641 / 360000) * t ^ 11 + (-470783 / 1440000) * t ^ 17 + (48701 / 600) * c * t ^ 3 + (-53165413 / 2160000) * c * t ^ 5 + (-7551449 / 360000) * c * t ^ 7 + (13160717 / 4320000) * c * t ^ 9 + (3371417 / 3240000) * c * t ^ 11 + (1229 / 6912) * c * t ^ 17 + (-124 / 75) * c ^ 2 * t ^ 3 + (6904 / 16875) * c ^ 2 * t ^ 5 + (30209 / 33750) * c ^ 2 * t ^ 7 + (113 / 11250) * c ^ 2 * t ^ 9 + (568 / 50625) * c ^ 2 * t ^ 11 + (146 / 50625) * c ^ 2 * t ^ 17) * alpha_sq + ((142 / 1125) * t ^ 5 + (-71 / 1125) * t ^ 7 + (-71 / 1125) * t ^ 9 + (-496 / 75) * alpha * t ^ 3 + (16618 / 5625) * alpha * t ^ 5 + (2933 / 1875) * alpha * t ^ 7 + (-8563 / 16875) * alpha * t ^ 9 + (-7072 / 50625) * alpha * t ^ 11 + (-584 / 50625) * alpha * t ^ 17) * c_sq
theorem v48_42 (t : ℂ) : (momentPoly 48 z48 4 2).eval t = ((-144265 / 12) * t ^ 2 + (-272267771 / 3000) * t ^ 4 + (245588300623 / 1440000) * t ^ 6 + (-88880435981 / 1440000) * t ^ 8 + (-17366942171 / 2880000) * t ^ 10 + (-1174465609 / 576000) * t ^ 12 + (278305579 / 2160000) * t ^ 14 + (157232203 / 8640000) * t ^ 18 + (-1294767211 / 8640000) * t ^ 20 + (-20984 / 3) * c * t ^ 2 + (1366284 / 125) * c * t ^ 4 + (-6388081 / 2250) * c * t ^ 6 + (-6528843 / 6250) * c * t ^ 8 + (-10576831 / 56250) * c * t ^ 10 + (4404859 / 56250) * c * t ^ 12 + (-2562592 / 84375) * c * t ^ 14 + (369448 / 84375) * c * t ^ 18 + (-4 / 5) * c * t ^ 20 + (-76067 / 4) * alpha * t ^ 2 + (161079767 / 1000) * alpha * t ^ 4 + (-314114559569 / 1440000) * alpha * t ^ 6 + (500804062079 / 7200000) * alpha * t ^ 8 + (25889367923 / 4800000) * alpha * t ^ 10 + (131383133597 / 43200000) * alpha * t ^ 12 + (-126603 / 400000) * alpha * t ^ 14 + (51903773 / 14400000) * alpha * t ^ 18 + (4445176937 / 43200000) * alpha * t ^ 20 + (-20984 / 9) * alpha * c * t ^ 2 + (455428 / 125) * alpha * c * t ^ 4 + (-12977789 / 13500) * alpha * c * t ^ 6 + (-21365659 / 67500) * alpha * c * t ^ 8 + (-3343451 / 45000) * alpha * c * t ^ 10 + (607463 / 27000) * alpha * c * t ^ 12 + (-1215673 / 101250) * alpha * c * t ^ 14 + (748189 / 405000) * alpha * c * t ^ 18 + (-38797 / 135000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_10, v47_11, v47_12, v47_20, v47_21, v47_22, v47_30, v47_31, v47_32, v47_40, v47_41, v47_42]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22, phase48_30, phase48_31, phase48_32, phase48_40, phase48_41, phase48_42]
  try simp only [star_one, star_neg]
  linear_combination ((2623 / 9) * t ^ 2 + (-393139 / 1125) * t ^ 4 + (300181147 / 1080000) * t ^ 6 + (-1344709651 / 3600000) * t ^ 8 + (2326050071 / 10800000) * t ^ 10 + (914879599 / 7200000) * t ^ 12 + (3973171 / 600000) * t ^ 14 + (2347813 / 1200000) * t ^ 18 + (155847317 / 21600000) * t ^ 20 + (-162656 / 1125) * c * t ^ 4 + (-3471719 / 540000) * c * t ^ 6 + (586106021 / 5400000) * c * t ^ 8 + (25451353 / 5400000) * c * t ^ 10 + (-12145129 / 10800000) * c * t ^ 12 + (5047457 / 2700000) * c * t ^ 14 + (-182887 / 1800000) * c * t ^ 18 + (-50797 / 2160000) * c * t ^ 20 + (-2623 / 9) * c ^ 2 * t ^ 2 + (12351 / 25) * c ^ 2 * t ^ 4 + (-97745903 / 360000) * c ^ 2 * t ^ 6 + (506883491 / 8100000) * c ^ 2 * t ^ 8 + (-100501171 / 10800000) * c ^ 2 * t ^ 10 + (3474473 / 8100000) * c ^ 2 * t ^ 12 + (-958231 / 3037500) * c ^ 2 * t ^ 14 + (-1783763 / 97200000) * c ^ 2 * t ^ 18 + (292 / 759375) * c ^ 2 * t ^ 20) * alpha_sq + ((5246 / 9) * t ^ 2 + (-1177324 / 1125) * t ^ 4 + (39704903 / 54000) * t ^ 6 + (-173008847 / 675000) * t ^ 8 + (102903311 / 2700000) * t ^ 10 + (-5824091 / 675000) * t ^ 12 + (350002 / 253125) * t ^ 14 + (2949041 / 8100000) * t ^ 18 + (584 / 253125) * t ^ 20 + (-5246 / 9) * alpha * t ^ 2 + (1242644 / 1125) * alpha * t ^ 4 + (-22722833 / 27000) * alpha * t ^ 6 + (104383481 / 337500) * alpha * t ^ 8 + (-9676163 / 225000) * alpha * t ^ 10 + (2156296 / 253125) * alpha * t ^ 12 + (-11096 / 9375) * alpha * t ^ 14 + (-24266 / 84375) * alpha * t ^ 18 + (-584 / 253125) * alpha * t ^ 20) * c_sq
theorem v48_43 (t : ℂ) : (momentPoly 48 z48 4 3).eval t = ((7476669 / 5) * t + (-77894916 / 25) * t ^ 3 + (1448353041 / 1000) * t ^ 5 + (55634891761 / 150000) * t ^ 7 + (-3115121891 / 100000) * t ^ 9 + (-9699183563 / 60000) * t ^ 11 + (66535602509 / 9000000) * t ^ 13 + (-5296687433 / 562500) * t ^ 15 + (-2660604691 / 3000000) * t ^ 17 + (-2066913143 / 13500000) * t ^ 19 + (-2844589573 / 9000000) * t ^ 21 + (-624640379 / 27000000) * t ^ 25 + (-1661482 / 5) * c * t + 984170 * c * t ^ 3 + (-557466901 / 500) * c * t ^ 5 + (559868019877 / 900000) * c * t ^ 7 + (-174822224617 / 900000) * c * t ^ 9 + (70498147967 / 1800000) * c * t ^ 11 + (-154547414287 / 27000000) * c * t ^ 13 + (2972213987 / 2250000) * c * t ^ 15 + (-1456810423 / 13500000) * c * t ^ 17 + (4776816127 / 81000000) * c * t ^ 19 + (-1471035703 / 27000000) * c * t ^ 21 + (-21314311 / 13500000) * c * t ^ 25 + (-2492223 / 5) * alpha * t + (5010709 / 5) * alpha * t ^ 3 + (-394115287 / 1000) * alpha * t ^ 5 + (-70817445731 / 360000) * alpha * t ^ 7 + (65596013287 / 1800000) * alpha * t ^ 9 + (166719901811 / 3600000) * alpha * t ^ 11 + (22067097041 / 54000000) * alpha * t ^ 13 + (1277310151 / 500000) * alpha * t ^ 15 + (11339928199 / 27000000) * alpha * t ^ 17 + (489366059 / 6480000) * alpha * t ^ 19 + (2947524401 / 54000000) * alpha * t ^ 21 + (460347653 / 81000000) * alpha * t ^ 25 + (-1661482 / 5) * alpha * c * t + (23996632 / 25) * alpha * c * t ^ 3 + (-1573807547 / 1500) * alpha * c * t ^ 5 + (126818222987 / 225000) * alpha * c * t ^ 7 + (-79532064533 / 450000) * alpha * c * t ^ 9 + (3422408003 / 90000) * alpha * c * t ^ 11 + (-71894866807 / 13500000) * alpha * c * t ^ 13 + (650044912 / 421875) * alpha * c * t ^ 15 + (-353861507 / 4500000) * alpha * c * t ^ 17 + (207328583 / 2250000) * alpha * c * t ^ 19 + (-1213997209 / 13500000) * alpha * c * t ^ 21 + (-130459 / 64800) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_03, v47_10, v47_11, v47_12, v47_13, v47_20, v47_21, v47_22, v47_23, v47_30, v47_31, v47_32, v47_33, v47_40, v47_41, v47_42, v47_43]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23, phase48_30, phase48_31, phase48_32, phase48_33, phase48_40, phase48_41, phase48_42, phase48_43]
  try simp only [star_one, star_neg]
  linear_combination ((2195127 / 200) * t ^ 3 + (-1481921 / 400) * t ^ 5 + (-48798043963 / 4800000) * t ^ 7 + (-1184344909 / 320000) * t ^ 9 + (179874517877 / 28800000) * t ^ 11 + (-5828586941 / 16000000) * t ^ 13 + (76247226731 / 108000000) * t ^ 15 + (3874863523 / 54000000) * t ^ 17 + (2775484471 / 432000000) * t ^ 19 + (2586807983 / 144000000) * t ^ 21 + (104043043 / 54000000) * t ^ 25 + (-6722309 / 600) * c * t ^ 3 + (4024159 / 240) * c * t ^ 5 + (-410493759533 / 43200000) * c * t ^ 7 + (267578855507 / 43200000) * c * t ^ 9 + (-259177989631 / 86400000) * c * t ^ 11 + (283782263957 / 1296000000) * c * t ^ 13 + (-3535536667 / 108000000) * c * t ^ 15 + (76188137 / 10125000) * c * t ^ 17 + (-22150131599 / 3888000000) * c * t ^ 19 + (-12897632911 / 1296000000) * c * t ^ 21 + (17116 / 75) * c ^ 2 * t ^ 3 + (-6813 / 25) * c ^ 2 * t ^ 5 + (-393313 / 27000) * c ^ 2 * t ^ 7 + (45186389 / 600000) * c ^ 2 * t ^ 9 + (-18020371 / 2700000) * c ^ 2 * t ^ 11 + (4100131 / 10800000) * c ^ 2 * t ^ 13 + (881959 / 900000) * c ^ 2 * t ^ 15 + (12901 / 202500) * c ^ 2 * t ^ 17 + (-570737 / 4050000) * c ^ 2 * t ^ 19 + (8399 / 240000) * c ^ 2 * t ^ 21) * alpha_sq + ((-34232 / 25) * t ^ 3 + (626092 / 375) * t ^ 5 + (-109421 / 15000) * t ^ 7 + (-141793727 / 450000) * t ^ 9 + (-291983 / 10000) * t ^ 11 + (23445323 / 4500000) * t ^ 13 + (-36680257 / 3375000) * t ^ 15 + (-97928 / 140625) * t ^ 17 + (16476707 / 20250000) * t ^ 19 + (-5175023 / 13500000) * t ^ 21 + (-20732 / 1265625) * t ^ 25 + (34232 / 75) * alpha * t ^ 3 + (-191468 / 375) * alpha * t ^ 5 + (-8310991 / 135000) * alpha * t ^ 7 + (148024297 / 1350000) * alpha * t ^ 9 + (33539677 / 1350000) * alpha * t ^ 11 + (-120160879 / 40500000) * alpha * t ^ 13 + (3424823 / 1125000) * alpha * t ^ 15 + (344194 / 1265625) * alpha * t ^ 17 + (-10271837 / 60750000) * alpha * t ^ 19 + (4755473 / 40500000) * alpha * t ^ 21 + (20732 / 3796875) * alpha * t ^ 25) * c_sq
theorem v48_44 (t : ℂ) : (momentPoly 48 z48 4 4).eval t = (119626704 + (-1532144992 / 5) * t ^ 2 + (10173480163 / 50) * t ^ 4 + (68888202179 / 1500) * t ^ 6 + (-8157720609215311 / 144000000) * t ^ 8 + (-235780504109323 / 12000000) * t ^ 10 + (113572499532053 / 9600000) * t ^ 12 + (486000648290881 / 216000000) * t ^ 14 + (-55190169783509 / 192000000) * t ^ 16 + (-690718821659 / 24000000) * t ^ 18 + (-10415238778267 / 2160000000) * t ^ 20 + (-1154038638131 / 360000000) * t ^ 22 + (84874834142783 / 4320000000) * t ^ 24 + (1300311156563 / 3240000000) * t ^ 26 + (4866172017709 / 25920000000) * t ^ 32 + (7135216 / 75) * c * t ^ 4 + (-90217712 / 375) * c * t ^ 6 + (67884209567 / 375000) * c * t ^ 8 + (-13275829103 / 562500) * c * t ^ 10 + (-17862765743 / 2250000) * c * t ^ 12 + (-7548088471 / 1687500) * c * t ^ 14 + (726479279 / 750000) * c * t ^ 16 + (-920952907 / 1687500) * c * t ^ 18 + (-15355887017 / 101250000) * c * t ^ 20 + (1274728187 / 8437500) * c * t ^ 22 + (163212703 / 33750000) * c * t ^ 24 + (36179092 / 6328125) * c * t ^ 26 + (9044773 / 25312500) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_03, v47_04, v47_10, v47_11, v47_12, v47_13, v47_14, v47_20, v47_21, v47_22, v47_23, v47_24, v47_30, v47_31, v47_32, v47_33, v47_34, v47_40, v47_41, v47_42, v47_43, v47_44]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24, phase48_30, phase48_31, phase48_32, phase48_33, phase48_34, phase48_40, phase48_41, phase48_42, phase48_43, phase48_44]
  try simp only [star_one, star_neg]
  linear_combination ((-1609396 / 15) * t ^ 2 + (15049276 / 75) * t ^ 4 + (-356978001 / 500) * t ^ 6 + (2532107915197 / 4500000) * t ^ 8 + (1795346397469 / 18000000) * t ^ 10 + (-180252161213 / 18000000) * t ^ 12 + (-27209745281473 / 324000000) * t ^ 14 + (375370671823 / 108000000) * t ^ 16 + (-15544744907 / 9000000) * t ^ 18 + (19433490379 / 33750000) * t ^ 20 + (-376669486043 / 540000000) * t ^ 22 + (-47384647367 / 60000000) * t ^ 24 + (-668258131 / 50625000) * t ^ 26 + (-5487162821 / 810000000) * t ^ 32 + (3291244 / 45) * c * t ^ 4 + (-44489183 / 250) * c * t ^ 6 + (1877619796549 / 13500000) * c * t ^ 8 + (-953194183309 / 27000000) * c * t ^ 10 + (17362890679 / 6750000) * c * t ^ 12 + (-188637156169 / 162000000) * c * t ^ 14 + (-50194781849 / 162000000) * c * t ^ 16 + (-429873439 / 40500000) * c * t ^ 18 + (-1579566713 / 243000000) * c * t ^ 20 + (-2190537263 / 54000000) * c * t ^ 22 + (2014087 / 6480000) * c * t ^ 24 + (-89717 / 40500) * c * t ^ 26 + (89717 / 972000) * c * t ^ 32 + (1609396 / 15) * c ^ 2 * t ^ 2 + (-61604048 / 225) * c ^ 2 * t ^ 4 + (1775893463 / 6750) * c ^ 2 * t ^ 6 + (-257821455821 / 2025000) * c ^ 2 * t ^ 8 + (27017537101 / 675000) * c ^ 2 * t ^ 10 + (-12482817917 / 1350000) * c ^ 2 * t ^ 12 + (467041501 / 405000) * c ^ 2 * t ^ 14 + (-91991138 / 253125) * c ^ 2 * t ^ 16 + (186131429 / 8100000) * c ^ 2 * t ^ 18 + (-701317811 / 33750000) * c ^ 2 * t ^ 20 + (895132417 / 33750000) * c ^ 2 * t ^ 22 + (8333839 / 151875000) * c ^ 2 * t ^ 24 + (1163880709 / 1822500000) * c ^ 2 * t ^ 26 + (42632 / 56953125) * c ^ 2 * t ^ 32) * alpha_sq + ((-6437584 / 15) * t ^ 2 + (82733332 / 75) * t ^ 4 + (-241565321 / 225) * t ^ 6 + (7120907994829 / 13500000) * t ^ 8 + (-247422795631 / 1500000) * t ^ 10 + (339557094581 / 9000000) * t ^ 12 + (-527018858533 / 81000000) * t ^ 14 + (17110285649 / 6750000) * t ^ 16 + (-776331967 / 3375000) * t ^ 18 + (14505071863 / 135000000) * t ^ 20 + (-12903151511 / 135000000) * t ^ 22 + (-30218191 / 50625000) * t ^ 24 + (-727998679 / 151875000) * t ^ 26 + (-170528 / 18984375) * t ^ 32) * c_sq
#print axioms v48_00
#print axioms v48_11
#print axioms v48_22
#print axioms v48_33
#print axioms v48_44
end PhotonCertA
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z49 : Fin 49 → ℂ := Fin.snoc z48 (r ^ 3 * thetaMinus)
theorem v49_00 (t : ℂ) : (momentPoly 49 z49 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00]
  try simp only [phase48_00]
  try simp only [star_one, star_neg]
  ring
theorem v49_01 (t : ℂ) : (momentPoly 49 z49 0 1).eval t = ((7 / 10) * t + (-1 / 10) * c * t + (7 / 30) * alpha * t + (1 / 10) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01]
  try simp only [phase48_00, phase48_01]
  try simp only [star_one, star_neg]
  ring
theorem v49_02 (t : ℂ) : (momentPoly 49 z49 0 2).eval t = ((2141 / 600) * t ^ 2 + (-4609 / 600) * t ^ 4 + (-6 / 25) * c * t ^ 2 + (-1 / 25) * c * t ^ 4 + (2851 / 600) * alpha * t ^ 2 + (-1773 / 200) * alpha * t ^ 4 + (2 / 25) * alpha * c * t ^ 2 + (1 / 75) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02]
  try simp only [phase48_00, phase48_01, phase48_02]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 75) * t ^ 2 + (-1 / 225) * c * t ^ 2 + (-2 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((4 / 225) * t ^ 2 + (4 / 225) * alpha * t ^ 2) * c_sq
theorem v49_03 (t : ℂ) : (momentPoly 49 z49 0 3).eval t = ((-497 / 200) * t ^ 3 + (497 / 200) * t ^ 5 + (-1009 / 120) * c * t ^ 3 + (9603 / 1000) * c * t ^ 5 + (71 / 375) * c * t ^ 9 + (7601 / 600) * alpha * t ^ 3 + (-70261 / 3000) * alpha * t ^ 5 + (-1547 / 1125) * alpha * t ^ 9 + (-71 / 200) * alpha * c * t ^ 3 + (71 / 200) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_03]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03]
  try simp only [star_one, star_neg]
  linear_combination ((29 / 400) * t ^ 3 + (-6779 / 6000) * t ^ 5 + (-229 / 3600) * c * t ^ 3 + (11561 / 18000) * c * t ^ 5 + (-2 / 225) * c ^ 2 * t ^ 3 + (-4 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((8 / 225) * alpha * t ^ 3 + (16 / 1125) * alpha * t ^ 5) * c_sq
theorem v49_04 (t : ℂ) : (momentPoly 49 z49 0 4).eval t = ((-1929959 / 24000) * t ^ 4 + (89637 / 160) * t ^ 6 + (-122237909 / 240000) * t ^ 8 + (2523151 / 180000) * t ^ 10 + (-4856399 / 720000) * t ^ 16 + (-6488 / 375) * c * t ^ 4 + (2028 / 125) * c * t ^ 6 + (2336 / 625) * c * t ^ 8 + (1168 / 625) * c * t ^ 10 + (146 / 1875) * c * t ^ 16 + (163609 / 24000) * alpha * t ^ 4 + (-4255513 / 12000) * alpha * t ^ 6 + (30598393 / 80000) * alpha * t ^ 8 + (-3762161 / 180000) * alpha * t ^ 10 + (2031803 / 240000) * alpha * t ^ 16 + (-7766 / 1125) * alpha * c * t ^ 4 + (2383 / 375) * alpha * c * t ^ 6 + (897 / 625) * alpha * c * t ^ 8 + (1168 / 1875) * alpha * c * t ^ 10 + (146 / 5625) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_03, v48_04]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04]
  try simp only [star_one, star_neg]
  linear_combination ((1381 / 2250) * t ^ 4 + (-9133 / 1800) * t ^ 6 + (366971 / 15000) * t ^ 8 + (-1768 / 5625) * t ^ 10 + (-1523 / 2250) * c * t ^ 4 + (2467 / 900) * c * t ^ 6 + (3859 / 22500) * c * t ^ 8 + (884 / 16875) * c * t ^ 10 + (71 / 1125) * c ^ 2 * t ^ 4 + (-221 / 3375) * c ^ 2 * t ^ 6 + (-8 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-1484 / 1125) * t ^ 4 + (668 / 375) * t ^ 6 + (-16 / 5625) * t ^ 8 + (1136 / 16875) * t ^ 10 + (16 / 15) * alpha * t ^ 4 + (-344 / 225) * alpha * t ^ 6 + (16 / 5625) * alpha * t ^ 8 + (-1136 / 16875) * alpha * t ^ 10) * c_sq
theorem v49_10 (t : ℂ) : (momentPoly 49 z49 1 0).eval t = ((7 / 10) * t + (-1 / 10) * c * t + (-7 / 30) * alpha * t + (-1 / 10) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_10]
  try simp only [phase48_00, phase48_10]
  try simp only [star_one, star_neg]
  ring
theorem v49_11 (t : ℂ) : (momentPoly 49 z49 1 1).eval t = (49 + (-592 / 15) * t ^ 2) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_10, v48_11]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 75) * t ^ 2 + (1 / 225) * c * t ^ 2 + (2 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((-8 / 225) * t ^ 2) * c_sq
theorem v49_12 (t : ℂ) : (momentPoly 49 z49 1 2).eval t = ((679 / 10) * t + (-1268 / 25) * t ^ 3 + (-788 / 75) * t ^ 5 + (-97 / 10) * c * t + (3167 / 300) * c * t ^ 3 + (-181 / 100) * c * t ^ 5 + (679 / 30) * alpha * t + (-14719 / 900) * alpha * t ^ 3 + (-3649 / 900) * alpha * t ^ 5 + (97 / 10) * alpha * c * t + (-258 / 25) * alpha * c * t ^ 3 + (118 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_10, v48_11, v48_12]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12]
  try simp only [star_one, star_neg]
  linear_combination ((-29 / 1200) * t ^ 3 + (6779 / 18000) * t ^ 5 + (229 / 10800) * c * t ^ 3 + (-11561 / 54000) * c * t ^ 5 + (2 / 675) * c ^ 2 * t ^ 3 + (4 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((-4 / 225) * t ^ 3 + (-8 / 1125) * t ^ 5 + (-4 / 675) * alpha * t ^ 3 + (-8 / 3375) * alpha * t ^ 5) * c_sq
theorem v49_13 (t : ℂ) : (momentPoly 49 z49 1 3).eval t = ((12846 / 25) * t ^ 2 + (-4340479 / 3000) * t ^ 4 + (267377 / 300) * t ^ 6 + (22643 / 9000) * t ^ 10 + (-864 / 25) * c * t ^ 2 + (9733 / 375) * c * t ^ 4 + (772 / 125) * c * t ^ 6 + (-6 / 25) * c * t ^ 10 + (17106 / 25) * alpha * t ^ 2 + (-5254249 / 3000) * alpha * t ^ 4 + (307279 / 300) * alpha * t ^ 6 + (33293 / 9000) * alpha * t ^ 10 + (288 / 25) * alpha * c * t ^ 2 + (-9733 / 1125) * alpha * c * t ^ 4 + (-772 / 375) * alpha * c * t ^ 6 + (2 / 25) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_03, v48_10, v48_11, v48_12, v48_13]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13]
  try simp only [star_one, star_neg]
  linear_combination ((48 / 25) * t ^ 2 + (-13091 / 9000) * t ^ 4 + (1397 / 3000) * t ^ 6 + (442 / 5625) * t ^ 10 + (-16 / 25) * c * t ^ 2 + (2017 / 9000) * c * t ^ 4 + (-57 / 200) * c * t ^ 6 + (-221 / 16875) * c * t ^ 10 + (-32 / 25) * c ^ 2 * t ^ 2 + (5537 / 4500) * c ^ 2 * t ^ 4 + (-271 / 1500) * c ^ 2 * t ^ 6) * alpha_sq + ((64 / 25) * t ^ 2 + (-337 / 125) * t ^ 4 + (161 / 225) * t ^ 6 + (284 / 16875) * t ^ 10 + (64 / 25) * alpha * t ^ 2 + (-127 / 45) * alpha * t ^ 4 + (947 / 1125) * alpha * t ^ 6 + (284 / 16875) * alpha * t ^ 10) * c_sq
theorem v49_14 (t : ℂ) : (momentPoly 49 z49 1 4).eval t = ((-9443 / 20) * t ^ 3 + (96663263 / 120000) * t ^ 5 + (-14717903 / 60000) * t ^ 7 + (-19476407 / 240000) * t ^ 9 + (-1463707 / 180000) * t ^ 11 + (867307 / 720000) * t ^ 17 + (-19171 / 12) * c * t ^ 3 + (1215954299 / 360000) * c * t ^ 5 + (-114091193 / 60000) * c * t ^ 7 + (8958371 / 48000) * c * t ^ 9 + (-1983017 / 36000) * c * t ^ 11 + (743423 / 240000) * c * t ^ 17 + (144419 / 60) * alpha * t ^ 3 + (-750142763 / 120000) * alpha * t ^ 5 + (206808443 / 60000) * alpha * t ^ 7 + (4254913 / 80000) * alpha * t ^ 9 + (119896517 / 540000) * alpha * t ^ 11 + (2838319 / 432000) * alpha * t ^ 17 + (-1349 / 20) * alpha * c * t ^ 3 + (5592317 / 40000) * alpha * c * t ^ 5 + (-1690157 / 20000) * alpha * c * t ^ 7 + (2905681 / 240000) * alpha * c * t ^ 9 + (38701 / 180000) * alpha * c * t ^ 11 + (-123901 / 720000) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_03, v48_04, v48_10, v48_11, v48_12, v48_13, v48_14]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14]
  try simp only [star_one, star_neg]
  linear_combination ((551 / 40) * t ^ 3 + (-133964777 / 720000) * t ^ 5 + (5766673 / 40000) * t ^ 7 + (-4643503 / 1440000) * t ^ 9 + (209101 / 1080000) * t ^ 11 + (-7705969 / 21600000) * t ^ 17 + (-4351 / 360) * c * t ^ 3 + (39528511 / 432000) * c * t ^ 5 + (-75572843 / 1080000) * c * t ^ 7 + (7904047 / 1440000) * c * t ^ 9 + (-132731 / 648000) * c * t ^ 11 + (13491923 / 64800000) * c * t ^ 17 + (-76 / 45) * c ^ 2 * t ^ 3 + (10042 / 16875) * c ^ 2 * t ^ 5 + (14672 / 16875) * c ^ 2 * t ^ 7 + (134 / 16875) * c ^ 2 * t ^ 9 + (568 / 50625) * c ^ 2 * t ^ 11 + (584 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((142 / 1125) * t ^ 5 + (-142 / 1875) * t ^ 7 + (-284 / 5625) * t ^ 9 + (304 / 45) * alpha * t ^ 3 + (-22402 / 5625) * alpha * t ^ 5 + (-9362 / 5625) * alpha * t ^ 7 + (7324 / 16875) * alpha * t ^ 9 + (7072 / 50625) * alpha * t ^ 11 + (2336 / 253125) * alpha * t ^ 17) * c_sq
theorem v49_20 (t : ℂ) : (momentPoly 49 z49 2 0).eval t = ((2141 / 600) * t ^ 2 + (-4609 / 600) * t ^ 4 + (-6 / 25) * c * t ^ 2 + (-1 / 25) * c * t ^ 4 + (-2851 / 600) * alpha * t ^ 2 + (1773 / 200) * alpha * t ^ 4 + (-2 / 25) * alpha * c * t ^ 2 + (-1 / 75) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_10, v48_20]
  try simp only [phase48_00, phase48_10, phase48_20]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 75) * t ^ 2 + (-1 / 225) * c * t ^ 2 + (-2 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((4 / 225) * t ^ 2 + (-4 / 225) * alpha * t ^ 2) * c_sq
theorem v49_21 (t : ℂ) : (momentPoly 49 z49 2 1).eval t = ((679 / 10) * t + (-1268 / 25) * t ^ 3 + (-788 / 75) * t ^ 5 + (-97 / 10) * c * t + (3167 / 300) * c * t ^ 3 + (-181 / 100) * c * t ^ 5 + (-679 / 30) * alpha * t + (14719 / 900) * alpha * t ^ 3 + (3649 / 900) * alpha * t ^ 5 + (-97 / 10) * alpha * c * t + (258 / 25) * alpha * c * t ^ 3 + (-118 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_10, v48_11, v48_20, v48_21]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21]
  try simp only [star_one, star_neg]
  linear_combination ((-29 / 1200) * t ^ 3 + (6779 / 18000) * t ^ 5 + (229 / 10800) * c * t ^ 3 + (-11561 / 54000) * c * t ^ 5 + (2 / 675) * c ^ 2 * t ^ 3 + (4 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((-4 / 225) * t ^ 3 + (-8 / 1125) * t ^ 5 + (4 / 675) * alpha * t ^ 3 + (8 / 3375) * alpha * t ^ 5) * c_sq
theorem v49_22 (t : ℂ) : (momentPoly 49 z49 2 2).eval t = (4753 + (-37888 / 5) * t ^ 2 + (50638517 / 18000) * t ^ 4 + (-259223 / 1800) * t ^ 6 + (4432433 / 18000) * t ^ 8 + (71 / 125) * c * t ^ 4 + (-71 / 150) * c * t ^ 6 + (-71 / 750) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_10, v48_11, v48_12, v48_20, v48_21, v48_22]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22]
  try simp only [star_one, star_neg]
  linear_combination ((-64 / 25) * t ^ 2 + (1171 / 675) * t ^ 4 + (28901 / 27000) * t ^ 6 + (-366971 / 45000) * t ^ 8 + (64 / 75) * c * t ^ 2 + (-247 / 3375) * c * t ^ 4 + (-1441 / 2700) * c * t ^ 6 + (-3859 / 67500) * c * t ^ 8 + (128 / 75) * c ^ 2 * t ^ 2 + (-5608 / 3375) * c ^ 2 * t ^ 4 + (532 / 2025) * c ^ 2 * t ^ 6 + (8 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((-512 / 75) * t ^ 2 + (22574 / 3375) * t ^ 4 + (-742 / 675) * t ^ 6 + (-32 / 16875) * t ^ 8) * c_sq
theorem v49_23 (t : ℂ) : (momentPoly 49 z49 2 3).eval t = ((97783 / 10) * t + (-72276 / 5) * t ^ 3 + (42178161 / 20000) * t ^ 5 + (64611757 / 30000) * t ^ 7 + (5428471 / 12000) * t ^ 9 + (-78089 / 9000) * t ^ 11 + (170949 / 5000) * t ^ 13 + (-13969 / 10) * c * t + (60173 / 20) * c * t ^ 3 + (-379968743 / 180000) * c * t ^ 5 + (49676159 / 90000) * c * t ^ 7 + (-3864869 / 60000) * c * t ^ 9 + (178451 / 45000) * c * t ^ 11 + (-7047 / 5000) * c * t ^ 13 + (97783 / 30) * alpha * t + (-279661 / 60) * alpha * t ^ 3 + (75070843 / 180000) * alpha * t ^ 5 + (5083187 / 6000) * alpha * t ^ 7 + (26806099 / 180000) * alpha * t ^ 9 + (-21671 / 135000) * alpha * t ^ 11 + (1318867 / 135000) * alpha * t ^ 13 + (13969 / 10) * alpha * c * t + (-14706 / 5) * alpha * c * t ^ 3 + (356780143 / 180000) * alpha * c * t ^ 5 + (-4908279 / 10000) * alpha * c * t ^ 7 + (3851237 / 60000) * alpha * c * t ^ 9 + (-167233 / 45000) * alpha * c * t ^ 11 + (14701 / 9000) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_03, v48_10, v48_11, v48_12, v48_13, v48_20, v48_21, v48_22, v48_23]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23]
  try simp only [star_one, star_neg]
  linear_combination ((-551 / 80) * t ^ 3 + (968901 / 10000) * t ^ 5 + (-209237 / 3000) * t ^ 7 + (-133079 / 9000) * t ^ 9 + (8719 / 67500) * t ^ 11 + (-1498159 / 675000) * t ^ 13 + (4351 / 720) * c * t ^ 3 + (-1485047 / 30000) * c * t ^ 5 + (2332793 / 67500) * c * t ^ 7 + (20003 / 6750) * c * t ^ 9 + (10039 / 405000) * c * t ^ 11 + (-442 / 253125) * c * t ^ 13 + (38 / 45) * c ^ 2 * t ^ 3 + (-6844 / 16875) * c ^ 2 * t ^ 5 + (-10687 / 33750) * c ^ 2 * t ^ 7 + (191 / 6750) * c ^ 2 * t ^ 9 + (4 / 675) * c ^ 2 * t ^ 11) * alpha_sq + ((-76 / 15) * t ^ 3 + (4681 / 1875) * t ^ 5 + (9803 / 5625) * t ^ 7 + (-158 / 5625) * t ^ 9 + (-316 / 16875) * t ^ 11 + (568 / 84375) * t ^ 13 + (-76 / 45) * alpha * t ^ 3 + (12623 / 16875) * alpha * t ^ 5 + (2131 / 3375) * alpha * t ^ 7 + (82 / 3375) * alpha * t ^ 9 + (-316 / 50625) * alpha * t ^ 11 + (568 / 253125) * alpha * t ^ 13) * c_sq
theorem v49_24 (t : ℂ) : (momentPoly 49 z49 2 4).eval t = ((14646581 / 150) * t ^ 2 + (-1014990229 / 3000) * t ^ 4 + (58424172471 / 160000) * t ^ 6 + (-175355829829 / 1440000) * t ^ 8 + (3904147493 / 2880000) * t ^ 10 + (-41082493103 / 8640000) * t ^ 12 + (891607603 / 2160000) * t ^ 14 + (767358379 / 8640000) * t ^ 18 + (-287047831 / 1728000) * t ^ 20 + (-164184 / 25) * c * t ^ 2 + (4061233 / 375) * c * t ^ 4 + (-37570997 / 12500) * c * t ^ 6 + (-265128619 / 225000) * c * t ^ 8 + (-2894309 / 18750) * c * t ^ 10 + (5745803 / 75000) * c * t ^ 12 + (-284992 / 9375) * c * t ^ 14 + (44798 / 9375) * c * t ^ 18 + (-16 / 25) * c * t ^ 20 + (19503691 / 150) * alpha * t ^ 2 + (-1263516499 / 3000) * alpha * t ^ 4 + (346732417773 / 800000) * alpha * t ^ 6 + (-1008335157967 / 7200000) * alpha * t ^ 8 + (4925988079 / 1600000) * alpha * t ^ 10 + (-252703494269 / 43200000) * alpha * t ^ 12 + (103659281 / 432000) * alpha * t ^ 14 + (90019601 / 1728000) * alpha * t ^ 18 + (-1676479523 / 14400000) * alpha * t ^ 20 + (54728 / 25) * alpha * c * t ^ 2 + (-4061233 / 1125) * alpha * c * t ^ 4 + (137411941 / 135000) * alpha * c * t ^ 6 + (97760099 / 270000) * alpha * c * t ^ 8 + (5582537 / 90000) * alpha * c * t ^ 10 + (-4088087 / 180000) * alpha * c * t ^ 12 + (1591769 / 135000) * alpha * c * t ^ 14 + (-520987 / 270000) * alpha * c * t ^ 18 + (41197 / 180000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_03, v48_04, v48_10, v48_11, v48_12, v48_13, v48_14, v48_20, v48_21, v48_22, v48_23, v48_24]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24]
  try simp only [star_one, star_neg]
  linear_combination ((27364 / 75) * t ^ 2 + (-615277 / 1125) * t ^ 4 + (940806641 / 2700000) * t ^ 6 + (-2773969189 / 10800000) * t ^ 8 + (7057739 / 225000) * t ^ 10 + (9234693007 / 64800000) * t ^ 12 + (-11722627 / 3240000) * t ^ 14 + (-8658347 / 16200000) * t ^ 18 + (826264937 / 108000000) * t ^ 20 + (-27364 / 225) * c * t ^ 2 + (94799 / 1125) * c * t ^ 4 + (-60366301 / 900000) * c * t ^ 6 + (134995111 / 1800000) * c * t ^ 8 + (16924561 / 5400000) * c * t ^ 10 + (32674199 / 10800000) * c * t ^ 12 + (1043611 / 900000) * c * t ^ 14 + (1036363 / 5400000) * c * t ^ 18 + (-60397 / 2160000) * c * t ^ 20 + (-54728 / 225) * c ^ 2 * t ^ 2 + (520478 / 1125) * c ^ 2 * t ^ 4 + (-379853869 / 1350000) * c ^ 2 * t ^ 6 + (5261471 / 81000) * c ^ 2 * t ^ 8 + (-23809879 / 2700000) * c ^ 2 * t ^ 10 + (1080341 / 2025000) * c ^ 2 * t ^ 12 + (-204679 / 759375) * c ^ 2 * t ^ 14 + (-70603 / 4860000) * c ^ 2 * t ^ 18 + (1168 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((109456 / 225) * t ^ 2 + (-126712 / 125) * t ^ 4 + (17410061 / 22500) * t ^ 6 + (-43530787 / 168750) * t ^ 8 + (23539843 / 675000) * t ^ 10 + (-4285117 / 506250) * t ^ 12 + (298456 / 253125) * t ^ 14 + (625757 / 2025000) * t ^ 18 + (2336 / 1265625) * t ^ 20 + (109456 / 225) * alpha * t ^ 2 + (-47752 / 45) * alpha * t ^ 4 + (48641591 / 56250) * alpha * t ^ 6 + (-25778849 / 84375) * alpha * t ^ 8 + (6593773 / 168750) * alpha * t ^ 10 + (-2120368 / 253125) * alpha * t ^ 12 + (258128 / 253125) * alpha * t ^ 14 + (62732 / 253125) * alpha * t ^ 18 + (2336 / 1265625) * alpha * t ^ 20) * c_sq
theorem v49_30 (t : ℂ) : (momentPoly 49 z49 3 0).eval t = ((-497 / 200) * t ^ 3 + (497 / 200) * t ^ 5 + (-1009 / 120) * c * t ^ 3 + (9603 / 1000) * c * t ^ 5 + (71 / 375) * c * t ^ 9 + (-7601 / 600) * alpha * t ^ 3 + (70261 / 3000) * alpha * t ^ 5 + (1547 / 1125) * alpha * t ^ 9 + (71 / 200) * alpha * c * t ^ 3 + (-71 / 200) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_10, v48_20, v48_30]
  try simp only [phase48_00, phase48_10, phase48_20, phase48_30]
  try simp only [star_one, star_neg]
  linear_combination ((29 / 400) * t ^ 3 + (-6779 / 6000) * t ^ 5 + (-229 / 3600) * c * t ^ 3 + (11561 / 18000) * c * t ^ 5 + (-2 / 225) * c ^ 2 * t ^ 3 + (-4 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-8 / 225) * alpha * t ^ 3 + (-16 / 1125) * alpha * t ^ 5) * c_sq
theorem v49_31 (t : ℂ) : (momentPoly 49 z49 3 1).eval t = ((12846 / 25) * t ^ 2 + (-4340479 / 3000) * t ^ 4 + (267377 / 300) * t ^ 6 + (22643 / 9000) * t ^ 10 + (-864 / 25) * c * t ^ 2 + (9733 / 375) * c * t ^ 4 + (772 / 125) * c * t ^ 6 + (-6 / 25) * c * t ^ 10 + (-17106 / 25) * alpha * t ^ 2 + (5254249 / 3000) * alpha * t ^ 4 + (-307279 / 300) * alpha * t ^ 6 + (-33293 / 9000) * alpha * t ^ 10 + (-288 / 25) * alpha * c * t ^ 2 + (9733 / 1125) * alpha * c * t ^ 4 + (772 / 375) * alpha * c * t ^ 6 + (-2 / 25) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_10, v48_11, v48_20, v48_21, v48_30, v48_31]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21, phase48_30, phase48_31]
  try simp only [star_one, star_neg]
  linear_combination ((48 / 25) * t ^ 2 + (-13091 / 9000) * t ^ 4 + (1397 / 3000) * t ^ 6 + (442 / 5625) * t ^ 10 + (-16 / 25) * c * t ^ 2 + (2017 / 9000) * c * t ^ 4 + (-57 / 200) * c * t ^ 6 + (-221 / 16875) * c * t ^ 10 + (-32 / 25) * c ^ 2 * t ^ 2 + (5537 / 4500) * c ^ 2 * t ^ 4 + (-271 / 1500) * c ^ 2 * t ^ 6) * alpha_sq + ((64 / 25) * t ^ 2 + (-337 / 125) * t ^ 4 + (161 / 225) * t ^ 6 + (284 / 16875) * t ^ 10 + (-64 / 25) * alpha * t ^ 2 + (127 / 45) * alpha * t ^ 4 + (-947 / 1125) * alpha * t ^ 6 + (-284 / 16875) * alpha * t ^ 10) * c_sq
theorem v49_32 (t : ℂ) : (momentPoly 49 z49 3 2).eval t = ((97783 / 10) * t + (-72276 / 5) * t ^ 3 + (42178161 / 20000) * t ^ 5 + (64611757 / 30000) * t ^ 7 + (5428471 / 12000) * t ^ 9 + (-78089 / 9000) * t ^ 11 + (170949 / 5000) * t ^ 13 + (-13969 / 10) * c * t + (60173 / 20) * c * t ^ 3 + (-379968743 / 180000) * c * t ^ 5 + (49676159 / 90000) * c * t ^ 7 + (-3864869 / 60000) * c * t ^ 9 + (178451 / 45000) * c * t ^ 11 + (-7047 / 5000) * c * t ^ 13 + (-97783 / 30) * alpha * t + (279661 / 60) * alpha * t ^ 3 + (-75070843 / 180000) * alpha * t ^ 5 + (-5083187 / 6000) * alpha * t ^ 7 + (-26806099 / 180000) * alpha * t ^ 9 + (21671 / 135000) * alpha * t ^ 11 + (-1318867 / 135000) * alpha * t ^ 13 + (-13969 / 10) * alpha * c * t + (14706 / 5) * alpha * c * t ^ 3 + (-356780143 / 180000) * alpha * c * t ^ 5 + (4908279 / 10000) * alpha * c * t ^ 7 + (-3851237 / 60000) * alpha * c * t ^ 9 + (167233 / 45000) * alpha * c * t ^ 11 + (-14701 / 9000) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_10, v48_11, v48_12, v48_20, v48_21, v48_22, v48_30, v48_31, v48_32]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22, phase48_30, phase48_31, phase48_32]
  try simp only [star_one, star_neg]
  linear_combination ((-551 / 80) * t ^ 3 + (968901 / 10000) * t ^ 5 + (-209237 / 3000) * t ^ 7 + (-133079 / 9000) * t ^ 9 + (8719 / 67500) * t ^ 11 + (-1498159 / 675000) * t ^ 13 + (4351 / 720) * c * t ^ 3 + (-1485047 / 30000) * c * t ^ 5 + (2332793 / 67500) * c * t ^ 7 + (20003 / 6750) * c * t ^ 9 + (10039 / 405000) * c * t ^ 11 + (-442 / 253125) * c * t ^ 13 + (38 / 45) * c ^ 2 * t ^ 3 + (-6844 / 16875) * c ^ 2 * t ^ 5 + (-10687 / 33750) * c ^ 2 * t ^ 7 + (191 / 6750) * c ^ 2 * t ^ 9 + (4 / 675) * c ^ 2 * t ^ 11) * alpha_sq + ((-76 / 15) * t ^ 3 + (4681 / 1875) * t ^ 5 + (9803 / 5625) * t ^ 7 + (-158 / 5625) * t ^ 9 + (-316 / 16875) * t ^ 11 + (568 / 84375) * t ^ 13 + (76 / 45) * alpha * t ^ 3 + (-12623 / 16875) * alpha * t ^ 5 + (-2131 / 3375) * alpha * t ^ 7 + (-82 / 3375) * alpha * t ^ 9 + (316 / 50625) * alpha * t ^ 11 + (-568 / 253125) * alpha * t ^ 13) * c_sq
theorem v49_33 (t : ℂ) : (momentPoly 49 z49 3 3).eval t = (684481 + (-8099744 / 5) * t ^ 2 + (2380010299 / 2000) * t ^ 4 + (-1169356097 / 3750) * t ^ 6 + (7179437549 / 50000) * t ^ 8 + (-3179119027 / 37500) * t ^ 10 + (-85347449 / 225000) * t ^ 12 + (-10807997 / 45000) * t ^ 14 + (-2984272 / 84375) * t ^ 18 + (30033 / 125) * c * t ^ 4 + (-781639 / 1875) * c * t ^ 6 + (496787 / 3750) * c * t ^ 8 + (26341 / 625) * c * t ^ 10 + (426 / 125) * c * t ^ 12 + (-71 / 50) * c * t ^ 14) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_03, v48_10, v48_11, v48_12, v48_13, v48_20, v48_21, v48_22, v48_23, v48_30, v48_31, v48_32, v48_33]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23, phase48_30, phase48_31, phase48_32, phase48_33]
  try simp only [star_one, star_neg]
  linear_combination ((-13682 / 25) * t ^ 2 + (55037 / 75) * t ^ 4 + (21000689 / 90000) * t ^ 6 + (-87675458 / 28125) * t ^ 8 + (1035043777 / 450000) * t ^ 10 + (540893 / 337500) * t ^ 12 + (-719203 / 75000) * t ^ 14 + (-195364 / 421875) * t ^ 18 + (13682 / 75) * c * t ^ 2 + (-11609 / 375) * c * t ^ 4 + (-29952863 / 90000) * c * t ^ 6 + (7395923 / 45000) * c * t ^ 8 + (373577 / 18000) * c * t ^ 10 + (263083 / 337500) * c * t ^ 12 + (252913 / 168750) * c * t ^ 14 + (27364 / 75) * c ^ 2 * t ^ 2 + (-263576 / 375) * c ^ 2 * t ^ 4 + (59402891 / 135000) * c ^ 2 * t ^ 6 + (-36436493 / 337500) * c ^ 2 * t ^ 8 + (9946819 / 675000) * c ^ 2 * t ^ 10 + (-4747 / 6250) * c ^ 2 * t ^ 12 + (4627 / 11250) * c ^ 2 * t ^ 14) * alpha_sq + ((-109456 / 75) * t ^ 2 + (1060978 / 375) * t ^ 4 + (-20202161 / 11250) * t ^ 6 + (4207313 / 9375) * t ^ 8 + (-3291737 / 56250) * t ^ 10 + (13044 / 3125) * t ^ 12 + (-263666 / 84375) * t ^ 14 + (-40328 / 1265625) * t ^ 18) * c_sq
theorem v49_34 (t : ℂ) : (momentPoly 49 z49 3 4).eval t = ((18582823 / 10) * t + (-101931984 / 25) * t ^ 3 + (20028783719 / 10000) * t ^ 5 + (14383901 / 25) * t ^ 7 + (-100252108433 / 750000) * t ^ 9 + (-162638337073 / 750000) * t ^ 11 + (72595548553 / 9000000) * t ^ 13 + (-64721379037 / 4500000) * t ^ 15 + (-325852399 / 240000) * t ^ 17 + (1439941481 / 13500000) * t ^ 19 + (-45944239 / 90000) * t ^ 21 + (-582327797 / 18000000) * t ^ 25 + (-2654689 / 10) * c * t + (21215733 / 25) * c * t ^ 3 + (-10355882333 / 10000) * c * t ^ 5 + (2207966296523 / 3600000) * c * t ^ 7 + (-3504135754813 / 18000000) * c * t ^ 9 + (1377350202253 / 36000000) * c * t ^ 11 + (-625789151083 / 108000000) * c * t ^ 13 + (11745113107 / 9000000) * c * t ^ 15 + (-1646870519 / 18000000) * c * t ^ 17 + (2214577913 / 36000000) * c * t ^ 19 + (-1718210177 / 36000000) * c * t ^ 21 + (-23114311 / 18000000) * c * t ^ 25 + (18582823 / 30) * alpha * t + (-32867527 / 25) * alpha * t ^ 3 + (16545252499 / 30000) * alpha * t ^ 5 + (349961568349 / 1200000) * alpha * t ^ 7 + (-448630708939 / 6000000) * alpha * t ^ 9 + (-2433095734751 / 36000000) * alpha * t ^ 11 + (-61388336623 / 108000000) * alpha * t ^ 13 + (-107897130439 / 27000000) * alpha * t ^ 15 + (-33249255419 / 54000000) * alpha * t ^ 17 + (-5132225899 / 324000000) * alpha * t ^ 19 + (-11327063407 / 108000000) * alpha * t ^ 21 + (-1363633697 / 162000000) * alpha * t ^ 25 + (2654689 / 10) * alpha * c * t + (-20740104 / 25) * alpha * c * t ^ 3 + (9823119633 / 10000) * alpha * c * t ^ 5 + (-84577388987 / 150000) * alpha * c * t ^ 7 + (201131571781 / 1125000) * alpha * c * t ^ 9 + (-3704139201 / 100000) * alpha * c * t ^ 11 + (49031802569 / 9000000) * alpha * c * t ^ 13 + (-743044899 / 500000) * alpha * c * t ^ 15 + (1226084617 / 18000000) * alpha * c * t ^ 17 + (-122311901 / 1350000) * alpha * c * t ^ 19 + (341819197 / 4500000) * alpha * c * t ^ 21 + (139099 / 86400) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_03, v48_04, v48_10, v48_11, v48_12, v48_13, v48_14, v48_20, v48_21, v48_22, v48_23, v48_24, v48_30, v48_31, v48_32, v48_33, v48_34]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24, phase48_30, phase48_31, phase48_32, phase48_33, phase48_34]
  try simp only [star_one, star_neg]
  linear_combination ((-194271 / 100) * t ^ 3 + (733586219 / 30000) * t ^ 5 + (-454295289809 / 14400000) * t ^ 7 + (18987405259 / 14400000) * t ^ 9 + (1003654843129 / 144000000) * t ^ 11 + (-51798291913 / 144000000) * t ^ 13 + (18783292363 / 21600000) * t ^ 15 + (943366039 / 10800000) * t ^ 17 + (-3275790491 / 1296000000) * t ^ 19 + (10719073889 / 432000000) * t ^ 21 + (1703019149 / 810000000) * t ^ 25 + (511357 / 300) * c * t ^ 3 + (-970957433 / 90000) * c * t ^ 5 + (500914676147 / 43200000) * c * t ^ 7 + (-79535216189 / 216000000) * c * t ^ 9 + (-950997115211 / 432000000) * c * t ^ 11 + (-18148526699 / 259200000) * c * t ^ 13 + (-3215209669 / 324000000) * c * t ^ 15 + (550123 / 84375) * c * t ^ 17 + (1095237553 / 3888000000) * c * t ^ 19 + (-14275564667 / 1296000000) * c * t ^ 21 + (-64532 / 18984375) * c * t ^ 25 + (17864 / 75) * c ^ 2 * t ^ 3 + (-1797164 / 5625) * c ^ 2 * t ^ 5 + (18241 / 27000) * c ^ 2 * t ^ 7 + (208284467 / 2250000) * c ^ 2 * t ^ 9 + (-55791233 / 6750000) * c ^ 2 * t ^ 11 + (-1006181 / 13500000) * c ^ 2 * t ^ 13 + (11170079 / 10125000) * c ^ 2 * t ^ 15 + (13801 / 253125) * c ^ 2 * t ^ 17 + (-3823873 / 20250000) * c ^ 2 * t ^ 19 + (26797 / 900000) * c ^ 2 * t ^ 21) * alpha_sq + ((-35728 / 25) * t ^ 3 + (3660358 / 1875) * t ^ 5 + (-2953683 / 25000) * t ^ 7 + (-57294281 / 140625) * t ^ 9 + (-36703621 / 2250000) * t ^ 11 + (6737873 / 1125000) * t ^ 13 + (-1089629 / 93750) * t ^ 15 + (-50464 / 84375) * t ^ 17 + (23501459 / 20250000) * t ^ 19 + (-1103267 / 3375000) * t ^ 21 + (-82928 / 6328125) * t ^ 25 + (-35728 / 75) * alpha * t ^ 3 + (3396238 / 5625) * alpha * t ^ 5 + (21813731 / 675000) * alpha * t ^ 7 + (-20639981 / 140625) * alpha * t ^ 9 + (-139258187 / 6750000) * alpha * t ^ 11 + (1193797 / 405000) * alpha * t ^ 13 + (-8339363 / 2531250) * alpha * t ^ 15 + (-292648 / 1265625) * alpha * t ^ 17 + (17794157 / 60750000) * alpha * t ^ 19 + (-1019357 / 10125000) * alpha * t ^ 21 + (-82928 / 18984375) * alpha * t ^ 25) * c_sq
theorem v49_40 (t : ℂ) : (momentPoly 49 z49 4 0).eval t = ((-1929959 / 24000) * t ^ 4 + (89637 / 160) * t ^ 6 + (-122237909 / 240000) * t ^ 8 + (2523151 / 180000) * t ^ 10 + (-4856399 / 720000) * t ^ 16 + (-6488 / 375) * c * t ^ 4 + (2028 / 125) * c * t ^ 6 + (2336 / 625) * c * t ^ 8 + (1168 / 625) * c * t ^ 10 + (146 / 1875) * c * t ^ 16 + (-163609 / 24000) * alpha * t ^ 4 + (4255513 / 12000) * alpha * t ^ 6 + (-30598393 / 80000) * alpha * t ^ 8 + (3762161 / 180000) * alpha * t ^ 10 + (-2031803 / 240000) * alpha * t ^ 16 + (7766 / 1125) * alpha * c * t ^ 4 + (-2383 / 375) * alpha * c * t ^ 6 + (-897 / 625) * alpha * c * t ^ 8 + (-1168 / 1875) * alpha * c * t ^ 10 + (-146 / 5625) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_10, v48_20, v48_30, v48_40]
  try simp only [phase48_00, phase48_10, phase48_20, phase48_30, phase48_40]
  try simp only [star_one, star_neg]
  linear_combination ((1381 / 2250) * t ^ 4 + (-9133 / 1800) * t ^ 6 + (366971 / 15000) * t ^ 8 + (-1768 / 5625) * t ^ 10 + (-1523 / 2250) * c * t ^ 4 + (2467 / 900) * c * t ^ 6 + (3859 / 22500) * c * t ^ 8 + (884 / 16875) * c * t ^ 10 + (71 / 1125) * c ^ 2 * t ^ 4 + (-221 / 3375) * c ^ 2 * t ^ 6 + (-8 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-1484 / 1125) * t ^ 4 + (668 / 375) * t ^ 6 + (-16 / 5625) * t ^ 8 + (1136 / 16875) * t ^ 10 + (-16 / 15) * alpha * t ^ 4 + (344 / 225) * alpha * t ^ 6 + (-16 / 5625) * alpha * t ^ 8 + (1136 / 16875) * alpha * t ^ 10) * c_sq
theorem v49_41 (t : ℂ) : (momentPoly 49 z49 4 1).eval t = ((-9443 / 20) * t ^ 3 + (96663263 / 120000) * t ^ 5 + (-14717903 / 60000) * t ^ 7 + (-19476407 / 240000) * t ^ 9 + (-1463707 / 180000) * t ^ 11 + (867307 / 720000) * t ^ 17 + (-19171 / 12) * c * t ^ 3 + (1215954299 / 360000) * c * t ^ 5 + (-114091193 / 60000) * c * t ^ 7 + (8958371 / 48000) * c * t ^ 9 + (-1983017 / 36000) * c * t ^ 11 + (743423 / 240000) * c * t ^ 17 + (-144419 / 60) * alpha * t ^ 3 + (750142763 / 120000) * alpha * t ^ 5 + (-206808443 / 60000) * alpha * t ^ 7 + (-4254913 / 80000) * alpha * t ^ 9 + (-119896517 / 540000) * alpha * t ^ 11 + (-2838319 / 432000) * alpha * t ^ 17 + (1349 / 20) * alpha * c * t ^ 3 + (-5592317 / 40000) * alpha * c * t ^ 5 + (1690157 / 20000) * alpha * c * t ^ 7 + (-2905681 / 240000) * alpha * c * t ^ 9 + (-38701 / 180000) * alpha * c * t ^ 11 + (123901 / 720000) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_10, v48_11, v48_20, v48_21, v48_30, v48_31, v48_40, v48_41]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21, phase48_30, phase48_31, phase48_40, phase48_41]
  try simp only [star_one, star_neg]
  linear_combination ((551 / 40) * t ^ 3 + (-133964777 / 720000) * t ^ 5 + (5766673 / 40000) * t ^ 7 + (-4643503 / 1440000) * t ^ 9 + (209101 / 1080000) * t ^ 11 + (-7705969 / 21600000) * t ^ 17 + (-4351 / 360) * c * t ^ 3 + (39528511 / 432000) * c * t ^ 5 + (-75572843 / 1080000) * c * t ^ 7 + (7904047 / 1440000) * c * t ^ 9 + (-132731 / 648000) * c * t ^ 11 + (13491923 / 64800000) * c * t ^ 17 + (-76 / 45) * c ^ 2 * t ^ 3 + (10042 / 16875) * c ^ 2 * t ^ 5 + (14672 / 16875) * c ^ 2 * t ^ 7 + (134 / 16875) * c ^ 2 * t ^ 9 + (568 / 50625) * c ^ 2 * t ^ 11 + (584 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((142 / 1125) * t ^ 5 + (-142 / 1875) * t ^ 7 + (-284 / 5625) * t ^ 9 + (-304 / 45) * alpha * t ^ 3 + (22402 / 5625) * alpha * t ^ 5 + (9362 / 5625) * alpha * t ^ 7 + (-7324 / 16875) * alpha * t ^ 9 + (-7072 / 50625) * alpha * t ^ 11 + (-2336 / 253125) * alpha * t ^ 17) * c_sq
theorem v49_42 (t : ℂ) : (momentPoly 49 z49 4 2).eval t = ((14646581 / 150) * t ^ 2 + (-1014990229 / 3000) * t ^ 4 + (58424172471 / 160000) * t ^ 6 + (-175355829829 / 1440000) * t ^ 8 + (3904147493 / 2880000) * t ^ 10 + (-41082493103 / 8640000) * t ^ 12 + (891607603 / 2160000) * t ^ 14 + (767358379 / 8640000) * t ^ 18 + (-287047831 / 1728000) * t ^ 20 + (-164184 / 25) * c * t ^ 2 + (4061233 / 375) * c * t ^ 4 + (-37570997 / 12500) * c * t ^ 6 + (-265128619 / 225000) * c * t ^ 8 + (-2894309 / 18750) * c * t ^ 10 + (5745803 / 75000) * c * t ^ 12 + (-284992 / 9375) * c * t ^ 14 + (44798 / 9375) * c * t ^ 18 + (-16 / 25) * c * t ^ 20 + (-19503691 / 150) * alpha * t ^ 2 + (1263516499 / 3000) * alpha * t ^ 4 + (-346732417773 / 800000) * alpha * t ^ 6 + (1008335157967 / 7200000) * alpha * t ^ 8 + (-4925988079 / 1600000) * alpha * t ^ 10 + (252703494269 / 43200000) * alpha * t ^ 12 + (-103659281 / 432000) * alpha * t ^ 14 + (-90019601 / 1728000) * alpha * t ^ 18 + (1676479523 / 14400000) * alpha * t ^ 20 + (-54728 / 25) * alpha * c * t ^ 2 + (4061233 / 1125) * alpha * c * t ^ 4 + (-137411941 / 135000) * alpha * c * t ^ 6 + (-97760099 / 270000) * alpha * c * t ^ 8 + (-5582537 / 90000) * alpha * c * t ^ 10 + (4088087 / 180000) * alpha * c * t ^ 12 + (-1591769 / 135000) * alpha * c * t ^ 14 + (520987 / 270000) * alpha * c * t ^ 18 + (-41197 / 180000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_10, v48_11, v48_12, v48_20, v48_21, v48_22, v48_30, v48_31, v48_32, v48_40, v48_41, v48_42]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22, phase48_30, phase48_31, phase48_32, phase48_40, phase48_41, phase48_42]
  try simp only [star_one, star_neg]
  linear_combination ((27364 / 75) * t ^ 2 + (-615277 / 1125) * t ^ 4 + (940806641 / 2700000) * t ^ 6 + (-2773969189 / 10800000) * t ^ 8 + (7057739 / 225000) * t ^ 10 + (9234693007 / 64800000) * t ^ 12 + (-11722627 / 3240000) * t ^ 14 + (-8658347 / 16200000) * t ^ 18 + (826264937 / 108000000) * t ^ 20 + (-27364 / 225) * c * t ^ 2 + (94799 / 1125) * c * t ^ 4 + (-60366301 / 900000) * c * t ^ 6 + (134995111 / 1800000) * c * t ^ 8 + (16924561 / 5400000) * c * t ^ 10 + (32674199 / 10800000) * c * t ^ 12 + (1043611 / 900000) * c * t ^ 14 + (1036363 / 5400000) * c * t ^ 18 + (-60397 / 2160000) * c * t ^ 20 + (-54728 / 225) * c ^ 2 * t ^ 2 + (520478 / 1125) * c ^ 2 * t ^ 4 + (-379853869 / 1350000) * c ^ 2 * t ^ 6 + (5261471 / 81000) * c ^ 2 * t ^ 8 + (-23809879 / 2700000) * c ^ 2 * t ^ 10 + (1080341 / 2025000) * c ^ 2 * t ^ 12 + (-204679 / 759375) * c ^ 2 * t ^ 14 + (-70603 / 4860000) * c ^ 2 * t ^ 18 + (1168 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((109456 / 225) * t ^ 2 + (-126712 / 125) * t ^ 4 + (17410061 / 22500) * t ^ 6 + (-43530787 / 168750) * t ^ 8 + (23539843 / 675000) * t ^ 10 + (-4285117 / 506250) * t ^ 12 + (298456 / 253125) * t ^ 14 + (625757 / 2025000) * t ^ 18 + (2336 / 1265625) * t ^ 20 + (-109456 / 225) * alpha * t ^ 2 + (47752 / 45) * alpha * t ^ 4 + (-48641591 / 56250) * alpha * t ^ 6 + (25778849 / 84375) * alpha * t ^ 8 + (-6593773 / 168750) * alpha * t ^ 10 + (2120368 / 253125) * alpha * t ^ 12 + (-258128 / 253125) * alpha * t ^ 14 + (-62732 / 253125) * alpha * t ^ 18 + (-2336 / 1265625) * alpha * t ^ 20) * c_sq
theorem v49_43 (t : ℂ) : (momentPoly 49 z49 4 3).eval t = ((18582823 / 10) * t + (-101931984 / 25) * t ^ 3 + (20028783719 / 10000) * t ^ 5 + (14383901 / 25) * t ^ 7 + (-100252108433 / 750000) * t ^ 9 + (-162638337073 / 750000) * t ^ 11 + (72595548553 / 9000000) * t ^ 13 + (-64721379037 / 4500000) * t ^ 15 + (-325852399 / 240000) * t ^ 17 + (1439941481 / 13500000) * t ^ 19 + (-45944239 / 90000) * t ^ 21 + (-582327797 / 18000000) * t ^ 25 + (-2654689 / 10) * c * t + (21215733 / 25) * c * t ^ 3 + (-10355882333 / 10000) * c * t ^ 5 + (2207966296523 / 3600000) * c * t ^ 7 + (-3504135754813 / 18000000) * c * t ^ 9 + (1377350202253 / 36000000) * c * t ^ 11 + (-625789151083 / 108000000) * c * t ^ 13 + (11745113107 / 9000000) * c * t ^ 15 + (-1646870519 / 18000000) * c * t ^ 17 + (2214577913 / 36000000) * c * t ^ 19 + (-1718210177 / 36000000) * c * t ^ 21 + (-23114311 / 18000000) * c * t ^ 25 + (-18582823 / 30) * alpha * t + (32867527 / 25) * alpha * t ^ 3 + (-16545252499 / 30000) * alpha * t ^ 5 + (-349961568349 / 1200000) * alpha * t ^ 7 + (448630708939 / 6000000) * alpha * t ^ 9 + (2433095734751 / 36000000) * alpha * t ^ 11 + (61388336623 / 108000000) * alpha * t ^ 13 + (107897130439 / 27000000) * alpha * t ^ 15 + (33249255419 / 54000000) * alpha * t ^ 17 + (5132225899 / 324000000) * alpha * t ^ 19 + (11327063407 / 108000000) * alpha * t ^ 21 + (1363633697 / 162000000) * alpha * t ^ 25 + (-2654689 / 10) * alpha * c * t + (20740104 / 25) * alpha * c * t ^ 3 + (-9823119633 / 10000) * alpha * c * t ^ 5 + (84577388987 / 150000) * alpha * c * t ^ 7 + (-201131571781 / 1125000) * alpha * c * t ^ 9 + (3704139201 / 100000) * alpha * c * t ^ 11 + (-49031802569 / 9000000) * alpha * c * t ^ 13 + (743044899 / 500000) * alpha * c * t ^ 15 + (-1226084617 / 18000000) * alpha * c * t ^ 17 + (122311901 / 1350000) * alpha * c * t ^ 19 + (-341819197 / 4500000) * alpha * c * t ^ 21 + (-139099 / 86400) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_03, v48_10, v48_11, v48_12, v48_13, v48_20, v48_21, v48_22, v48_23, v48_30, v48_31, v48_32, v48_33, v48_40, v48_41, v48_42, v48_43]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23, phase48_30, phase48_31, phase48_32, phase48_33, phase48_40, phase48_41, phase48_42, phase48_43]
  try simp only [star_one, star_neg]
  linear_combination ((-194271 / 100) * t ^ 3 + (733586219 / 30000) * t ^ 5 + (-454295289809 / 14400000) * t ^ 7 + (18987405259 / 14400000) * t ^ 9 + (1003654843129 / 144000000) * t ^ 11 + (-51798291913 / 144000000) * t ^ 13 + (18783292363 / 21600000) * t ^ 15 + (943366039 / 10800000) * t ^ 17 + (-3275790491 / 1296000000) * t ^ 19 + (10719073889 / 432000000) * t ^ 21 + (1703019149 / 810000000) * t ^ 25 + (511357 / 300) * c * t ^ 3 + (-970957433 / 90000) * c * t ^ 5 + (500914676147 / 43200000) * c * t ^ 7 + (-79535216189 / 216000000) * c * t ^ 9 + (-950997115211 / 432000000) * c * t ^ 11 + (-18148526699 / 259200000) * c * t ^ 13 + (-3215209669 / 324000000) * c * t ^ 15 + (550123 / 84375) * c * t ^ 17 + (1095237553 / 3888000000) * c * t ^ 19 + (-14275564667 / 1296000000) * c * t ^ 21 + (-64532 / 18984375) * c * t ^ 25 + (17864 / 75) * c ^ 2 * t ^ 3 + (-1797164 / 5625) * c ^ 2 * t ^ 5 + (18241 / 27000) * c ^ 2 * t ^ 7 + (208284467 / 2250000) * c ^ 2 * t ^ 9 + (-55791233 / 6750000) * c ^ 2 * t ^ 11 + (-1006181 / 13500000) * c ^ 2 * t ^ 13 + (11170079 / 10125000) * c ^ 2 * t ^ 15 + (13801 / 253125) * c ^ 2 * t ^ 17 + (-3823873 / 20250000) * c ^ 2 * t ^ 19 + (26797 / 900000) * c ^ 2 * t ^ 21) * alpha_sq + ((-35728 / 25) * t ^ 3 + (3660358 / 1875) * t ^ 5 + (-2953683 / 25000) * t ^ 7 + (-57294281 / 140625) * t ^ 9 + (-36703621 / 2250000) * t ^ 11 + (6737873 / 1125000) * t ^ 13 + (-1089629 / 93750) * t ^ 15 + (-50464 / 84375) * t ^ 17 + (23501459 / 20250000) * t ^ 19 + (-1103267 / 3375000) * t ^ 21 + (-82928 / 6328125) * t ^ 25 + (35728 / 75) * alpha * t ^ 3 + (-3396238 / 5625) * alpha * t ^ 5 + (-21813731 / 675000) * alpha * t ^ 7 + (20639981 / 140625) * alpha * t ^ 9 + (139258187 / 6750000) * alpha * t ^ 11 + (-1193797 / 405000) * alpha * t ^ 13 + (8339363 / 2531250) * alpha * t ^ 15 + (292648 / 1265625) * alpha * t ^ 17 + (-17794157 / 60750000) * alpha * t ^ 19 + (1019357 / 10125000) * alpha * t ^ 21 + (82928 / 18984375) * alpha * t ^ 25) * c_sq
theorem v49_44 (t : ℂ) : (momentPoly 49 z49 4 4).eval t = (130079761 + (-1218653312 / 3) * t ^ 2 + (664225427489 / 1500) * t ^ 4 + (-518357302203 / 2500) * t ^ 6 + (12376538444073329 / 144000000) * t ^ 8 + (-2473291816867669 / 36000000) * t ^ 10 + (5382060256850237 / 240000000) * t ^ 12 + (762850154329249 / 1080000000) * t ^ 14 + (1012981038482533 / 2880000000) * t ^ 16 + (-3102410564829 / 40000000) * t ^ 18 + (133733400720431 / 6480000000) * t ^ 20 + (-8267537256527 / 360000000) * t ^ 22 + (812946807067 / 34560000) * t ^ 24 + (-366719972393 / 648000000) * t ^ 26 + (5528771140973 / 25920000000) * t ^ 32 + (11175684 / 125) * c * t ^ 4 + (-438705379 / 1875) * c * t ^ 6 + (410844077249 / 2250000) * c * t ^ 8 + (-107625575099 / 4500000) * c * t ^ 10 + (-119349108923 / 11250000) * c * t ^ 12 + (-537122329891 / 135000000) * c * t ^ 14 + (45416301211 / 45000000) * c * t ^ 16 + (-5923945199 / 11250000) * c * t ^ 18 + (-10731292507 / 67500000) * c * t ^ 20 + (6500863483 / 45000000) * c * t ^ 22 + (34766359 / 9000000) * c * t ^ 24 + (9044773 / 1687500) * c * t ^ 26 + (9044773 / 33750000) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_03, v48_04, v48_10, v48_11, v48_12, v48_13, v48_14, v48_20, v48_21, v48_22, v48_23, v48_24, v48_30, v48_31, v48_32, v48_33, v48_34, v48_40, v48_41, v48_42, v48_43, v48_44]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24, phase48_30, phase48_31, phase48_32, phase48_33, phase48_34, phase48_40, phase48_41, phase48_42, phase48_43, phase48_44]
  try simp only [star_one, star_neg]
  linear_combination ((-2058536 / 15) * t ^ 2 + (61440028 / 225) * t ^ 4 + (52572677 / 7500) * t ^ 6 + (-1363498757123 / 1350000) * t ^ 8 + (69975281831747 / 54000000) * t ^ 10 + (-105976871859881 / 270000000) * t ^ 12 + (-62402865168929 / 1620000000) * t ^ 14 + (-6460075094117 / 540000000) * t ^ 16 + (-3771155593 / 405000000) * t ^ 18 + (594245217917 / 1215000000) * t ^ 20 + (-408945961 / 324000000) * t ^ 22 + (-487023220223 / 540000000) * t ^ 24 + (6654760709 / 607500000) * t ^ 26 + (-29057003801 / 4050000000) * t ^ 32 + (2058536 / 45) * c * t ^ 2 + (-12959596 / 1125) * c * t ^ 4 + (-1831658171 / 11250) * c * t ^ 6 + (1176848262551 / 6750000) * c * t ^ 8 + (-118419687043 / 3000000) * c * t ^ 10 + (-567225260269 / 135000000) * c * t ^ 12 + (-888436043039 / 810000000) * c * t ^ 14 + (-587284720013 / 810000000) * c * t ^ 16 + (-876415417 / 22500000) * c * t ^ 18 + (4056509483 / 607500000) * c * t ^ 20 + (-560697707 / 10000000) * c * t ^ 22 + (317252243 / 810000000) * c * t ^ 24 + (-947412937 / 303750000) * c * t ^ 26 + (327393977 / 3037500000) * c * t ^ 32 + (4117072 / 45) * c ^ 2 * t ^ 2 + (-294240544 / 1125) * c ^ 2 * t ^ 4 + (177140836 / 625) * c ^ 2 * t ^ 6 + (-127710389647 / 843750) * c ^ 2 * t ^ 8 + (239453359799 / 5062500) * c ^ 2 * t ^ 10 + (-51281417969 / 5062500) * c ^ 2 * t ^ 12 + (72261725867 / 50625000) * c ^ 2 * t ^ 14 + (-5215545871 / 12656250) * c ^ 2 * t ^ 16 + (3282007403 / 151875000) * c ^ 2 * t ^ 18 + (-1874474303 / 75937500) * c ^ 2 * t ^ 20 + (3645977479 / 151875000) * c ^ 2 * t ^ 22 + (1770979 / 37968750) * c ^ 2 * t ^ 24 + (250067521 / 455625000) * c ^ 2 * t ^ 26 + (170528 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((-16468288 / 45) * t ^ 2 + (1184412632 / 1125) * t ^ 4 + (-2160939116 / 1875) * t ^ 6 + (2101648723561 / 3375000) * t ^ 8 + (-131130661363 / 675000) * t ^ 10 + (1399701305263 / 33750000) * t ^ 12 + (-778527066601 / 101250000) * t ^ 14 + (7587596863 / 2812500) * t ^ 16 + (-296904629 / 1406250) * t ^ 18 + (37273650851 / 303750000) * t ^ 20 + (-325549343 / 3750000) * t ^ 22 + (-6460483 / 12656250) * t ^ 24 + (-6277219 / 1518750) * t ^ 26 + (-682112 / 94921875) * t ^ 32) * c_sq
#print axioms v49_00
#print axioms v49_11
#print axioms v49_22
#print axioms v49_33
#print axioms v49_44
end PhotonCertA
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z50 : Fin 50 → ℂ := Fin.snoc z49 (r ^ 3 * thetaMinus)
theorem v50_00 (t : ℂ) : (momentPoly 50 z50 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00]
  try simp only [phase48_00]
  try simp only [star_one, star_neg]
  ring
theorem v50_01 (t : ℂ) : (momentPoly 50 z50 0 1).eval t = ((4 / 5) * t + (-1 / 15) * c * t + (4 / 15) * alpha * t + (1 / 15) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01]
  try simp only [phase48_00, phase48_01]
  try simp only [star_one, star_neg]
  ring
theorem v50_02 (t : ℂ) : (momentPoly 50 z50 0 2).eval t = ((3973 / 600) * t ^ 2 + (-4901 / 600) * t ^ 4 + (-14 / 75) * c * t ^ 2 + (-2 / 75) * c * t ^ 4 + (1561 / 200) * alpha * t ^ 2 + (-5611 / 600) * alpha * t ^ 4 + (14 / 225) * alpha * c * t ^ 2 + (2 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02]
  try simp only [phase48_00, phase48_01, phase48_02]
  try simp only [star_one, star_neg]
  linear_combination ((7 / 450) * t ^ 2 + (-2 / 225) * c * t ^ 2 + (-1 / 150) * c ^ 2 * t ^ 2) * alpha_sq + ((1 / 75) * t ^ 2 + (1 / 75) * alpha * t ^ 2) * c_sq
theorem v50_03 (t : ℂ) : (momentPoly 50 z50 0 3).eval t = ((-71 / 25) * t ^ 3 + (71 / 25) * t ^ 5 + (-3361 / 500) * c * t ^ 3 + (10171 / 1500) * c * t ^ 5 + (142 / 1125) * c * t ^ 9 + (8083 / 375) * alpha * t ^ 3 + (-9691 / 375) * alpha * t ^ 5 + (-1768 / 1125) * alpha * t ^ 9 + (-71 / 300) * alpha * c * t ^ 3 + (71 / 300) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_03]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03]
  try simp only [star_one, star_neg]
  linear_combination ((2851 / 6000) * t ^ 3 + (-7363 / 6000) * t ^ 5 + (-2803 / 6000) * c * t ^ 3 + (13297 / 18000) * c * t ^ 5 + (-1 / 125) * c ^ 2 * t ^ 3 + (-1 / 375) * c ^ 2 * t ^ 5) * alpha_sq + ((4 / 125) * alpha * t ^ 3 + (4 / 375) * alpha * t ^ 5) * c_sq
theorem v50_04 (t : ℂ) : (momentPoly 50 z50 0 4).eval t = ((-8805287 / 24000) * t ^ 4 + (18294593 / 20000) * t ^ 6 + (-135606037 / 240000) * t ^ 8 + (4738703 / 180000) * t ^ 10 + (-5178511 / 720000) * t ^ 16 + (-1184 / 75) * c * t ^ 4 + (8096 / 625) * c * t ^ 6 + (4964 / 1875) * c * t ^ 8 + (8176 / 5625) * c * t ^ 10 + (292 / 5625) * c * t ^ 16 + (5998361 / 24000) * alpha * t ^ 4 + (-39531389 / 60000) * alpha * t ^ 6 + (103504747 / 240000) * alpha * t ^ 8 + (-1992571 / 60000) * alpha * t ^ 10 + (6417521 / 720000) * alpha * t ^ 16 + (-6914 / 1125) * alpha * c * t ^ 4 + (3172 / 625) * alpha * c * t ^ 6 + (5674 / 5625) * alpha * c * t ^ 8 + (8176 / 16875) * alpha * c * t ^ 10 + (292 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_03, v49_04]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04]
  try simp only [star_one, star_neg]
  linear_combination ((7601 / 4500) * t ^ 4 + (-764891 / 45000) * t ^ 6 + (129429 / 5000) * t ^ 8 + (-6188 / 16875) * t ^ 10 + (-3907 / 2250) * c * t ^ 4 + (21073 / 7500) * c * t ^ 6 + (1481 / 7500) * c * t ^ 8 + (1768 / 16875) * c * t ^ 10 + (71 / 1500) * c ^ 2 * t ^ 4 + (-371 / 7500) * c ^ 2 * t ^ 6 + (-2 / 5625) * c ^ 2 * t ^ 8) * alpha_sq + ((-1421 / 1125) * t ^ 4 + (881 / 625) * t ^ 6 + (-4 / 1875) * t ^ 8 + (284 / 5625) * t ^ 10 + (1208 / 1125) * alpha * t ^ 4 + (-2288 / 1875) * alpha * t ^ 6 + (4 / 1875) * alpha * t ^ 8 + (-284 / 5625) * alpha * t ^ 10) * c_sq
theorem v50_10 (t : ℂ) : (momentPoly 50 z50 1 0).eval t = ((4 / 5) * t + (-1 / 15) * c * t + (-4 / 15) * alpha * t + (-1 / 15) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_10]
  try simp only [phase48_00, phase48_10]
  try simp only [star_one, star_neg]
  ring
theorem v50_11 (t : ℂ) : (momentPoly 50 z50 1 1).eval t = (50 + (-226 / 5) * t ^ 2) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_10, v49_11]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11]
  try simp only [star_one, star_neg]
  linear_combination ((-7 / 450) * t ^ 2 + (2 / 225) * c * t ^ 2 + (1 / 150) * c ^ 2 * t ^ 2) * alpha_sq + ((-2 / 75) * t ^ 2) * c_sq
theorem v50_12 (t : ℂ) : (momentPoly 50 z50 1 2).eval t = ((396 / 5) * t + (-184 / 3) * t ^ 3 + (-1052 / 75) * t ^ 5 + (-33 / 5) * c * t + (1133 / 150) * c * t ^ 3 + (-191 / 150) * c * t ^ 5 + (132 / 5) * alpha * t + (-1486 / 75) * alpha * t ^ 3 + (-398 / 75) * alpha * t ^ 5 + (33 / 5) * alpha * c * t + (-1664 / 225) * alpha * c * t ^ 3 + (251 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_10, v49_11, v49_12]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12]
  try simp only [star_one, star_neg]
  linear_combination ((-2851 / 18000) * t ^ 3 + (7363 / 18000) * t ^ 5 + (2803 / 18000) * c * t ^ 3 + (-13297 / 54000) * c * t ^ 5 + (1 / 375) * c ^ 2 * t ^ 3 + (1 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-2 / 125) * t ^ 3 + (-2 / 375) * t ^ 5 + (-2 / 375) * alpha * t ^ 3 + (-2 / 1125) * alpha * t ^ 5) * c_sq
theorem v50_13 (t : ℂ) : (momentPoly 50 z50 1 3).eval t = ((194677 / 200) * t ^ 2 + (-514621 / 250) * t ^ 4 + (134079 / 125) * t ^ 6 + (5043 / 1000) * t ^ 10 + (-686 / 25) * c * t ^ 2 + (328 / 15) * c * t ^ 4 + (592 / 125) * c * t ^ 6 + (-14 / 75) * c * t ^ 10 + (229467 / 200) * alpha * t ^ 2 + (-1790233 / 750) * alpha * t ^ 4 + (153249 / 125) * alpha * t ^ 6 + (18679 / 3000) * alpha * t ^ 10 + (686 / 75) * alpha * c * t ^ 2 + (-328 / 45) * alpha * c * t ^ 4 + (-592 / 375) * alpha * c * t ^ 6 + (14 / 225) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_03, v49_10, v49_11, v49_12, v49_13]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13]
  try simp only [star_one, star_neg]
  linear_combination ((343 / 150) * t ^ 2 + (-37039 / 18000) * t ^ 4 + (11257 / 30000) * t ^ 6 + (1547 / 16875) * t ^ 10 + (-98 / 75) * c * t ^ 2 + (4669 / 4500) * c * t ^ 4 + (-1723 / 7500) * c * t ^ 6 + (-442 / 16875) * c * t ^ 10 + (-49 / 50) * c ^ 2 * t ^ 2 + (6121 / 6000) * c ^ 2 * t ^ 4 + (-291 / 2000) * c ^ 2 * t ^ 6) * alpha_sq + ((49 / 25) * t ^ 2 + (-10283 / 4500) * t ^ 4 + (1439 / 2500) * t ^ 6 + (71 / 5625) * t ^ 10 + (49 / 25) * alpha * t ^ 2 + (-10709 / 4500) * alpha * t ^ 4 + (5027 / 7500) * alpha * t ^ 6 + (71 / 5625) * alpha * t ^ 10) * c_sq
theorem v50_14 (t : ℂ) : (momentPoly 50 z50 1 4).eval t = ((-13774 / 25) * t ^ 3 + (4779363 / 5000) * t ^ 5 + (-2174369 / 7500) * t ^ 7 + (-3212401 / 30000) * t ^ 9 + (-209101 / 22500) * t ^ 11 + (123901 / 90000) * t ^ 17 + (-326017 / 250) * c * t ^ 3 + (476122633 / 180000) * c * t ^ 5 + (-43196587 / 30000) * c * t ^ 7 + (49734607 / 360000) * c * t ^ 9 + (-3656431 / 90000) * c * t ^ 11 + (788863 / 360000) * c * t ^ 17 + (1568102 / 375) * alpha * t ^ 3 + (-381502327 / 45000) * alpha * t ^ 5 + (5691937 / 1500) * alpha * t ^ 7 + (16529999 / 90000) * alpha * t ^ 9 + (6304753 / 22500) * alpha * t ^ 11 + (172723 / 18000) * alpha * t ^ 17 + (-6887 / 150) * alpha * c * t ^ 3 + (17606231 / 180000) * alpha * c * t ^ 5 + (-5442511 / 90000) * alpha * c * t ^ 7 + (3076081 / 360000) * alpha * c * t ^ 9 + (38701 / 270000) * alpha * c * t ^ 11 + (-123901 / 1080000) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_03, v49_04, v49_10, v49_11, v49_12, v49_13, v49_14]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14]
  try simp only [star_one, star_neg]
  linear_combination ((276547 / 3000) * t ^ 3 + (-217487497 / 720000) * t ^ 5 + (4707463 / 24000) * t ^ 7 + (-6554539 / 7200000) * t ^ 9 + (2141867 / 1800000) * t ^ 11 + (-8350193 / 21600000) * t ^ 17 + (-271891 / 3000) * c * t ^ 3 + (443826587 / 2160000) * c * t ^ 5 + (-25553903 / 216000) * c * t ^ 7 + (177454273 / 21600000) * c * t ^ 9 + (-2160043 / 1800000) * c * t ^ 11 + (15461971 / 64800000) * c * t ^ 17 + (-194 / 125) * c ^ 2 * t ^ 3 + (11143 / 16875) * c ^ 2 * t ^ 5 + (8567 / 11250) * c ^ 2 * t ^ 7 + (331 / 56250) * c ^ 2 * t ^ 9 + (284 / 28125) * c ^ 2 * t ^ 11 + (146 / 84375) * c ^ 2 * t ^ 17) * alpha_sq + ((71 / 625) * t ^ 5 + (-142 / 1875) * t ^ 7 + (-71 / 1875) * t ^ 9 + (776 / 125) * alpha * t ^ 3 + (-8191 / 1875) * alpha * t ^ 5 + (-1634 / 1125) * alpha * t ^ 7 + (1083 / 3125) * alpha * t ^ 9 + (3536 / 28125) * alpha * t ^ 11 + (584 / 84375) * alpha * t ^ 17) * c_sq
theorem v50_20 (t : ℂ) : (momentPoly 50 z50 2 0).eval t = ((3973 / 600) * t ^ 2 + (-4901 / 600) * t ^ 4 + (-14 / 75) * c * t ^ 2 + (-2 / 75) * c * t ^ 4 + (-1561 / 200) * alpha * t ^ 2 + (5611 / 600) * alpha * t ^ 4 + (-14 / 225) * alpha * c * t ^ 2 + (-2 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_10, v49_20]
  try simp only [phase48_00, phase48_10, phase48_20]
  try simp only [star_one, star_neg]
  linear_combination ((7 / 450) * t ^ 2 + (-2 / 225) * c * t ^ 2 + (-1 / 150) * c ^ 2 * t ^ 2) * alpha_sq + ((1 / 75) * t ^ 2 + (-1 / 75) * alpha * t ^ 2) * c_sq
theorem v50_21 (t : ℂ) : (momentPoly 50 z50 2 1).eval t = ((396 / 5) * t + (-184 / 3) * t ^ 3 + (-1052 / 75) * t ^ 5 + (-33 / 5) * c * t + (1133 / 150) * c * t ^ 3 + (-191 / 150) * c * t ^ 5 + (-132 / 5) * alpha * t + (1486 / 75) * alpha * t ^ 3 + (398 / 75) * alpha * t ^ 5 + (-33 / 5) * alpha * c * t + (1664 / 225) * alpha * c * t ^ 3 + (-251 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_10, v49_11, v49_20, v49_21]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21]
  try simp only [star_one, star_neg]
  linear_combination ((-2851 / 18000) * t ^ 3 + (7363 / 18000) * t ^ 5 + (2803 / 18000) * c * t ^ 3 + (-13297 / 54000) * c * t ^ 5 + (1 / 375) * c ^ 2 * t ^ 3 + (1 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-2 / 125) * t ^ 3 + (-2 / 375) * t ^ 5 + (2 / 375) * alpha * t ^ 3 + (2 / 1125) * alpha * t ^ 5) * c_sq
theorem v50_22 (t : ℂ) : (momentPoly 50 z50 2 2).eval t = (4950 + (-44296 / 5) * t ^ 2 + (8030629 / 2000) * t ^ 4 + (-1087103 / 3000) * t ^ 6 + (1675759 / 6000) * t ^ 8 + (497 / 1125) * c * t ^ 4 + (-142 / 375) * c * t ^ 6 + (-71 / 1125) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_10, v49_11, v49_12, v49_20, v49_21, v49_22]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22]
  try simp only [star_one, star_neg]
  linear_combination ((-686 / 225) * t ^ 2 + (14719 / 6750) * t ^ 4 + (697349 / 135000) * t ^ 6 + (-43143 / 5000) * t ^ 8 + (392 / 225) * c * t ^ 2 + (-5431 / 6750) * c * t ^ 4 + (-4727 / 7500) * c * t ^ 6 + (-1481 / 22500) * c * t ^ 8 + (98 / 75) * c ^ 2 * t ^ 2 + (-172 / 125) * c ^ 2 * t ^ 4 + (1184 / 5625) * c ^ 2 * t ^ 6 + (2 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-392 / 75) * t ^ 2 + (2491 / 450) * t ^ 4 + (-1099 / 1250) * t ^ 6 + (-8 / 5625) * t ^ 8) * c_sq
theorem v50_23 (t : ℂ) : (momentPoly 50 z50 2 3).eval t = ((58216 / 5) * t + (-17848) * t ^ 3 + (19884269 / 7500) * t ^ 5 + (3694839 / 1250) * t ^ 7 + (4406681 / 7500) * t ^ 9 + (-78611 / 5625) * t ^ 11 + (239303 / 5625) * t ^ 13 + (-14554 / 15) * c * t + (109901 / 50) * c * t ^ 3 + (-28940857 / 18000) * c * t ^ 5 + (19153103 / 45000) * c * t ^ 7 + (-491713 / 10000) * c * t ^ 9 + (13901 / 4500) * c * t ^ 11 + (-7547 / 7500) * c * t ^ 13 + (58216 / 15) * alpha * t + (-144142 / 25) * alpha * t ^ 3 + (12079381 / 22500) * alpha * t ^ 5 + (12864629 / 11250) * alpha * t ^ 7 + (299383 / 1500) * alpha * t ^ 9 + (-2881 / 1875) * alpha * t ^ 11 + (69307 / 5625) * alpha * t ^ 13 + (14554 / 15) * alpha * c * t + (-161408 / 75) * alpha * c * t ^ 3 + (15186557 / 10000) * alpha * c * t ^ 5 + (-382507 / 1000) * alpha * c * t ^ 7 + (4409513 / 90000) * alpha * c * t ^ 9 + (-197297 / 67500) * alpha * c * t ^ 11 + (15601 / 13500) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_03, v49_10, v49_11, v49_12, v49_13, v49_20, v49_21, v49_22, v49_23]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23]
  try simp only [star_one, star_neg]
  linear_combination ((-276547 / 6000) * t ^ 3 + (4527581 / 30000) * t ^ 5 + (-7739681 / 90000) * t ^ 7 + (-7792823 / 450000) * t ^ 9 + (231803 / 337500) * t ^ 11 + (-1627223 / 675000) * t ^ 13 + (271891 / 6000) * c * t ^ 3 + (-3075269 / 30000) * c * t ^ 5 + (4771777 / 90000) * c * t ^ 7 + (3120773 / 1350000) * c * t ^ 9 + (173473 / 675000) * c * t ^ 11 + (-884 / 253125) * c * t ^ 13 + (97 / 125) * c ^ 2 * t ^ 3 + (-7513 / 16875) * c ^ 2 * t ^ 5 + (-12439 / 45000) * c ^ 2 * t ^ 7 + (203 / 9000) * c ^ 2 * t ^ 9 + (2 / 375) * c ^ 2 * t ^ 11) * alpha_sq + ((-582 / 125) * t ^ 3 + (30691 / 11250) * t ^ 5 + (8459 / 5625) * t ^ 7 + (-403 / 18750) * t ^ 9 + (-158 / 9375) * t ^ 11 + (142 / 28125) * t ^ 13 + (-194 / 125) * alpha * t ^ 3 + (5627 / 6750) * alpha * t ^ 5 + (9311 / 16875) * alpha * t ^ 7 + (113 / 6250) * alpha * t ^ 9 + (-158 / 28125) * alpha * t ^ 11 + (142 / 84375) * alpha * t ^ 13) * c_sq
theorem v50_24 (t : ℂ) : (momentPoly 50 z50 2 4).eval t = ((56658953 / 300) * t ^ 2 + (-562389821 / 1000) * t ^ 4 + (264937704757 / 480000) * t ^ 6 + (-86618926559 / 480000) * t ^ 8 + (2781942221 / 320000) * t ^ 10 + (-21111788957 / 2880000) * t ^ 12 + (53140577 / 80000) * t ^ 14 + (86145109 / 576000) * t ^ 18 + (-58671137 / 320000) * t ^ 20 + (-399308 / 75) * c * t ^ 2 + (228534 / 25) * c * t ^ 4 + (-34348891 / 12500) * c * t ^ 6 + (-7480321 / 7500) * c * t ^ 8 + (-2673893 / 22500) * c * t ^ 10 + (7182347 / 112500) * c * t ^ 12 + (-2156608 / 84375) * c * t ^ 14 + (348352 / 84375) * c * t ^ 18 + (-34 / 75) * c * t ^ 20 + (22261421 / 100) * alpha * t ^ 2 + (-655491411 / 1000) * alpha * t ^ 4 + (4585125816181 / 7200000) * alpha * t ^ 6 + (-1492361694943 / 7200000) * alpha * t ^ 8 + (164065506023 / 14400000) * alpha * t ^ 10 + (-368426544221 / 43200000) * alpha * t ^ 12 + (1640151779 / 3600000) * alpha * t ^ 14 + (1458289379 / 14400000) * alpha * t ^ 18 + (-5655748201 / 43200000) * alpha * t ^ 20 + (399308 / 225) * alpha * c * t ^ 2 + (-76178 / 25) * alpha * c * t ^ 4 + (41860441 / 45000) * alpha * c * t ^ 6 + (4596431 / 15000) * alpha * c * t ^ 8 + (1451771 / 30000) * alpha * c * t ^ 10 + (-5215339 / 270000) * alpha * c * t ^ 12 + (132151 / 13500) * alpha * c * t ^ 14 + (-440453 / 270000) * alpha * c * t ^ 18 + (43597 / 270000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_03, v49_04, v49_10, v49_11, v49_12, v49_13, v49_14, v49_20, v49_21, v49_22, v49_23, v49_24]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24]
  try simp only [star_one, star_neg]
  linear_combination ((99827 / 225) * t ^ 2 + (-296312 / 375) * t ^ 4 + (2558816701 / 5400000) * t ^ 6 + (-27242357 / 240000) * t ^ 8 + (-55285717 / 400000) * t ^ 10 + (51342926483 / 324000000) * t ^ 12 + (-976461179 / 81000000) * t ^ 14 + (-415335967 / 162000000) * t ^ 18 + (291097763 / 36000000) * t ^ 20 + (-57044 / 225) * c * t ^ 2 + (149408 / 375) * c * t ^ 4 + (-196480697 / 900000) * c * t ^ 6 + (32213021 / 600000) * c * t ^ 8 + (2349193 / 5400000) * c * t ^ 10 + (92909719 / 10800000) * c * t ^ 12 + (976769 / 2700000) * c * t ^ 14 + (90961 / 200000) * c * t ^ 18 + (-69997 / 2160000) * c * t ^ 20 + (-14261 / 75) * c ^ 2 * t ^ 2 + (48968 / 125) * c ^ 2 * t ^ 4 + (-1379932519 / 5400000) * c ^ 2 * t ^ 6 + (484211381 / 8100000) * c ^ 2 * t ^ 8 + (-83407621 / 10800000) * c ^ 2 * t ^ 10 + (2322979 / 4500000) * c ^ 2 * t ^ 12 + (-13439 / 62500) * c ^ 2 * t ^ 14 + (-64681 / 6000000) * c ^ 2 * t ^ 18 + (292 / 1265625) * c ^ 2 * t ^ 20) * alpha_sq + ((28522 / 75) * t ^ 2 + (-329056 / 375) * t ^ 4 + (319906787 / 450000) * t ^ 6 + (-52356707 / 225000) * t ^ 8 + (26718659 / 900000) * t ^ 10 + (-24687697 / 3375000) * t ^ 12 + (132046 / 140625) * t ^ 14 + (1102843 / 4500000) * t ^ 18 + (584 / 421875) * t ^ 20 + (28522 / 75) * alpha * t ^ 2 + (-342688 / 375) * alpha * t ^ 4 + (528469807 / 675000) * alpha * t ^ 6 + (-91673087 / 337500) * alpha * t ^ 8 + (2478919 / 75000) * alpha * t ^ 10 + (-1019408 / 140625) * alpha * t ^ 12 + (345728 / 421875) * alpha * t ^ 14 + (84032 / 421875) * alpha * t ^ 18 + (584 / 421875) * alpha * t ^ 20) * c_sq
theorem v50_30 (t : ℂ) : (momentPoly 50 z50 3 0).eval t = ((-71 / 25) * t ^ 3 + (71 / 25) * t ^ 5 + (-3361 / 500) * c * t ^ 3 + (10171 / 1500) * c * t ^ 5 + (142 / 1125) * c * t ^ 9 + (-8083 / 375) * alpha * t ^ 3 + (9691 / 375) * alpha * t ^ 5 + (1768 / 1125) * alpha * t ^ 9 + (71 / 300) * alpha * c * t ^ 3 + (-71 / 300) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_10, v49_20, v49_30]
  try simp only [phase48_00, phase48_10, phase48_20, phase48_30]
  try simp only [star_one, star_neg]
  linear_combination ((2851 / 6000) * t ^ 3 + (-7363 / 6000) * t ^ 5 + (-2803 / 6000) * c * t ^ 3 + (13297 / 18000) * c * t ^ 5 + (-1 / 125) * c ^ 2 * t ^ 3 + (-1 / 375) * c ^ 2 * t ^ 5) * alpha_sq + ((-4 / 125) * alpha * t ^ 3 + (-4 / 375) * alpha * t ^ 5) * c_sq
theorem v50_31 (t : ℂ) : (momentPoly 50 z50 3 1).eval t = ((194677 / 200) * t ^ 2 + (-514621 / 250) * t ^ 4 + (134079 / 125) * t ^ 6 + (5043 / 1000) * t ^ 10 + (-686 / 25) * c * t ^ 2 + (328 / 15) * c * t ^ 4 + (592 / 125) * c * t ^ 6 + (-14 / 75) * c * t ^ 10 + (-229467 / 200) * alpha * t ^ 2 + (1790233 / 750) * alpha * t ^ 4 + (-153249 / 125) * alpha * t ^ 6 + (-18679 / 3000) * alpha * t ^ 10 + (-686 / 75) * alpha * c * t ^ 2 + (328 / 45) * alpha * c * t ^ 4 + (592 / 375) * alpha * c * t ^ 6 + (-14 / 225) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_10, v49_11, v49_20, v49_21, v49_30, v49_31]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21, phase48_30, phase48_31]
  try simp only [star_one, star_neg]
  linear_combination ((343 / 150) * t ^ 2 + (-37039 / 18000) * t ^ 4 + (11257 / 30000) * t ^ 6 + (1547 / 16875) * t ^ 10 + (-98 / 75) * c * t ^ 2 + (4669 / 4500) * c * t ^ 4 + (-1723 / 7500) * c * t ^ 6 + (-442 / 16875) * c * t ^ 10 + (-49 / 50) * c ^ 2 * t ^ 2 + (6121 / 6000) * c ^ 2 * t ^ 4 + (-291 / 2000) * c ^ 2 * t ^ 6) * alpha_sq + ((49 / 25) * t ^ 2 + (-10283 / 4500) * t ^ 4 + (1439 / 2500) * t ^ 6 + (71 / 5625) * t ^ 10 + (-49 / 25) * alpha * t ^ 2 + (10709 / 4500) * alpha * t ^ 4 + (-5027 / 7500) * alpha * t ^ 6 + (-71 / 5625) * alpha * t ^ 10) * c_sq
theorem v50_32 (t : ℂ) : (momentPoly 50 z50 3 2).eval t = ((58216 / 5) * t + (-17848) * t ^ 3 + (19884269 / 7500) * t ^ 5 + (3694839 / 1250) * t ^ 7 + (4406681 / 7500) * t ^ 9 + (-78611 / 5625) * t ^ 11 + (239303 / 5625) * t ^ 13 + (-14554 / 15) * c * t + (109901 / 50) * c * t ^ 3 + (-28940857 / 18000) * c * t ^ 5 + (19153103 / 45000) * c * t ^ 7 + (-491713 / 10000) * c * t ^ 9 + (13901 / 4500) * c * t ^ 11 + (-7547 / 7500) * c * t ^ 13 + (-58216 / 15) * alpha * t + (144142 / 25) * alpha * t ^ 3 + (-12079381 / 22500) * alpha * t ^ 5 + (-12864629 / 11250) * alpha * t ^ 7 + (-299383 / 1500) * alpha * t ^ 9 + (2881 / 1875) * alpha * t ^ 11 + (-69307 / 5625) * alpha * t ^ 13 + (-14554 / 15) * alpha * c * t + (161408 / 75) * alpha * c * t ^ 3 + (-15186557 / 10000) * alpha * c * t ^ 5 + (382507 / 1000) * alpha * c * t ^ 7 + (-4409513 / 90000) * alpha * c * t ^ 9 + (197297 / 67500) * alpha * c * t ^ 11 + (-15601 / 13500) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_10, v49_11, v49_12, v49_20, v49_21, v49_22, v49_30, v49_31, v49_32]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22, phase48_30, phase48_31, phase48_32]
  try simp only [star_one, star_neg]
  linear_combination ((-276547 / 6000) * t ^ 3 + (4527581 / 30000) * t ^ 5 + (-7739681 / 90000) * t ^ 7 + (-7792823 / 450000) * t ^ 9 + (231803 / 337500) * t ^ 11 + (-1627223 / 675000) * t ^ 13 + (271891 / 6000) * c * t ^ 3 + (-3075269 / 30000) * c * t ^ 5 + (4771777 / 90000) * c * t ^ 7 + (3120773 / 1350000) * c * t ^ 9 + (173473 / 675000) * c * t ^ 11 + (-884 / 253125) * c * t ^ 13 + (97 / 125) * c ^ 2 * t ^ 3 + (-7513 / 16875) * c ^ 2 * t ^ 5 + (-12439 / 45000) * c ^ 2 * t ^ 7 + (203 / 9000) * c ^ 2 * t ^ 9 + (2 / 375) * c ^ 2 * t ^ 11) * alpha_sq + ((-582 / 125) * t ^ 3 + (30691 / 11250) * t ^ 5 + (8459 / 5625) * t ^ 7 + (-403 / 18750) * t ^ 9 + (-158 / 9375) * t ^ 11 + (142 / 28125) * t ^ 13 + (194 / 125) * alpha * t ^ 3 + (-5627 / 6750) * alpha * t ^ 5 + (-9311 / 16875) * alpha * t ^ 7 + (-113 / 6250) * alpha * t ^ 9 + (158 / 28125) * alpha * t ^ 11 + (-142 / 84375) * alpha * t ^ 13) * c_sq
theorem v50_33 (t : ℂ) : (momentPoly 50 z50 3 3).eval t = (727700 + (-9668958 / 5) * t ^ 2 + (216826983 / 125) * t ^ 4 + (-25448183437 / 37500) * t ^ 6 + (19332869239 / 75000) * t ^ 8 + (-2681356199 / 25000) * t ^ 10 + (114106063 / 225000) * t ^ 12 + (-19521831 / 25000) * t ^ 14 + (-1098386 / 28125) * t ^ 18 + (23856 / 125) * c * t ^ 4 + (-127516 / 375) * c * t ^ 6 + (71994 / 625) * c * t ^ 8 + (20306 / 625) * c * t ^ 10 + (994 / 375) * c * t ^ 12 + (-142 / 125) * c * t ^ 14) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_03, v49_10, v49_11, v49_12, v49_13, v49_20, v49_21, v49_22, v49_23, v49_30, v49_31, v49_32, v49_33]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23, phase48_30, phase48_31, phase48_32, phase48_33]
  try simp only [star_one, star_neg]
  linear_combination ((-99827 / 150) * t ^ 2 + (117752 / 125) * t ^ 4 + (1737788657 / 900000) * t ^ 6 + (-265473053 / 50000) * t ^ 8 + (2664957941 / 900000) * t ^ 10 + (3381313 / 675000) * t ^ 12 + (-198977 / 562500) * t ^ 14 + (-683774 / 1265625) * t ^ 18 + (28522 / 75) * c * t ^ 2 + (-43448 / 125) * c * t ^ 4 + (-2377277 / 9000) * c * t ^ 6 + (21987079 / 112500) * c * t ^ 8 + (956237 / 25000) * c * t ^ 10 + (192941 / 337500) * c * t ^ 12 + (354191 / 168750) * c * t ^ 14 + (14261 / 50) * c ^ 2 * t ^ 2 + (-74304 / 125) * c ^ 2 * t ^ 4 + (357908143 / 900000) * c ^ 2 * t ^ 6 + (-132834509 / 1350000) * c ^ 2 * t ^ 8 + (11504303 / 900000) * c ^ 2 * t ^ 10 + (-167233 / 225000) * c ^ 2 * t ^ 12 + (14797 / 45000) * c ^ 2 * t ^ 14) * alpha_sq + ((-28522 / 25) * t ^ 2 + (59784 / 25) * t ^ 4 + (-364294043 / 225000) * t ^ 6 + (45860899 / 112500) * t ^ 8 + (-3805237 / 75000) * t ^ 10 + (68921 / 16875) * t ^ 12 + (-234343 / 93750) * t ^ 14 + (-10082 / 421875) * t ^ 18) * c_sq
theorem v50_34 (t : ℂ) : (momentPoly 50 z50 3 4).eval t = ((11296268 / 5) * t + (-5141328) * t ^ 3 + (665449471 / 250) * t ^ 5 + (138503462123 / 187500) * t ^ 7 + (-83462884171 / 375000) * t ^ 9 + (-105607500541 / 375000) * t ^ 11 + (17828004067 / 2250000) * t ^ 13 + (-930581936 / 46875) * t ^ 15 + (-4218632339 / 2250000) * t ^ 17 + (1447380479 / 3375000) * t ^ 19 + (-1611291139 / 2250000) * t ^ 21 + (-279235753 / 6750000) * t ^ 25 + (-2824067 / 15) * c * t + (15829143 / 25) * c * t ^ 3 + (-487206127 / 600) * c * t ^ 5 + (4517846330021 / 9000000) * c * t ^ 7 + (-19544728907 / 120000) * c * t ^ 9 + (573024604111 / 18000000) * c * t ^ 11 + (-261888665651 / 54000000) * c * t ^ 13 + (4803557887 / 4500000) * c * t ^ 15 + (-123182041 / 1800000) * c * t ^ 17 + (2800080001 / 54000000) * c * t ^ 19 + (-662328217 / 18000000) * c * t ^ 21 + (-24914311 / 27000000) * c * t ^ 25 + (11296268 / 15) * alpha * t + (-41521812 / 25) * alpha * t ^ 3 + (555983659 / 750) * alpha * t ^ 5 + (282769432547 / 750000) * alpha * t ^ 7 + (-83674590851 / 750000) * alpha * t ^ 9 + (-410865084133 / 4500000) * alpha * t ^ 11 + (-15186166147 / 13500000) * alpha * t ^ 13 + (-6292173661 / 1125000) * alpha * t ^ 15 + (-1862691727 / 2250000) * alpha * t ^ 17 + (872484181 / 13500000) * alpha * t ^ 19 + (-15828037 / 100000) * alpha * t ^ 21 + (-24941279 / 2250000) * alpha * t ^ 25 + (2824067 / 15) * alpha * c * t + (-15498496 / 25) * alpha * c * t ^ 3 + (2322377527 / 3000) * alpha * c * t ^ 5 + (-262011688037 / 562500) * alpha * c * t ^ 7 + (678198077347 / 4500000) * alpha * c * t ^ 9 + (-13852855399 / 450000) * alpha * c * t ^ 11 + (24750124673 / 5400000) * alpha * c * t ^ 13 + (-269385893 / 225000) * alpha * c * t ^ 15 + (1401384713 / 27000000) * alpha * c * t ^ 17 + (-1490661007 / 20250000) * alpha * c * t ^ 19 + (1531356367 / 27000000) * alpha * c * t ^ 21 + (147739 / 129600) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_03, v49_04, v49_10, v49_11, v49_12, v49_13, v49_14, v49_20, v49_21, v49_22, v49_23, v49_24, v49_30, v49_31, v49_32, v49_33, v49_34]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24, phase48_30, phase48_31, phase48_32, phase48_33, phase48_34]
  try simp only [star_one, star_neg]
  linear_combination ((-13277107 / 1000) * t ^ 3 + (12592709 / 240) * t ^ 5 + (-1294033907719 / 24000000) * t ^ 7 + (144635145161 / 24000000) * t ^ 9 + (371388643747 / 48000000) * t ^ 11 + (-123257262791 / 432000000) * t ^ 13 + (111767014019 / 108000000) * t ^ 15 + (27988917839 / 270000000) * t ^ 17 + (-78253104967 / 6480000000) * t ^ 19 + (22832944259 / 720000000) * t ^ 21 + (1845392653 / 810000000) * t ^ 25 + (13053571 / 1000) * c * t ^ 3 + (-688162127 / 18000) * c * t ^ 5 + (7518896462111 / 216000000) * c * t ^ 7 + (-584060899379 / 72000000) * c * t ^ 9 + (-56439893923 / 48000000) * c * t ^ 11 + (-98775412391 / 259200000) * c * t ^ 13 + (4816348103 / 324000000) * c * t ^ 15 + (268925659 / 50625000) * c * t ^ 17 + (37947420871 / 6480000000) * c * t ^ 19 + (-78992468483 / 6480000000) * c * t ^ 21 + (-129064 / 18984375) * c * t ^ 25 + (27942 / 125) * c ^ 2 * t ^ 3 + (-367523 / 1125) * c ^ 2 * t ^ 5 + (28451401 / 1350000) * c ^ 2 * t ^ 7 + (163832561 / 1800000) * c ^ 2 * t ^ 9 + (-17956567 / 2250000) * c ^ 2 * t ^ 11 + (-2388431 / 6000000) * c ^ 2 * t ^ 13 + (14618527 / 13500000) * c ^ 2 * t ^ 15 + (14701 / 337500) * c ^ 2 * t ^ 17 + (-882133 / 4500000) * c ^ 2 * t ^ 19 + (28397 / 1200000) * c ^ 2 * t ^ 21) * alpha_sq + ((-167652 / 125) * t ^ 3 + (747187 / 375) * t ^ 5 + (-538111891 / 2250000) * t ^ 7 + (-101707219 / 250000) * t ^ 9 + (-40972957 / 4500000) * t ^ 11 + (83420587 / 13500000) * t ^ 13 + (-12315293 / 1125000) * t ^ 15 + (-337016 / 703125) * t ^ 17 + (82810457 / 67500000) * t ^ 19 + (-1952549 / 7500000) * t ^ 21 + (-20732 / 2109375) * t ^ 25 + (-55884 / 125) * alpha * t ^ 3 + (698623 / 1125) * alpha * t ^ 5 + (-62648213 / 6750000) * alpha * t ^ 7 + (-339411167 / 2250000) * alpha * t ^ 9 + (-43686391 / 2700000) * alpha * t ^ 11 + (111313477 / 40500000) * alpha * t ^ 13 + (-10552067 / 3375000) * alpha * t ^ 15 + (-129142 / 703125) * alpha * t ^ 17 + (66683687 / 202500000) * alpha * t ^ 19 + (-201411 / 2500000) * alpha * t ^ 21 + (-20732 / 6328125) * alpha * t ^ 25) * c_sq
theorem v50_40 (t : ℂ) : (momentPoly 50 z50 4 0).eval t = ((-8805287 / 24000) * t ^ 4 + (18294593 / 20000) * t ^ 6 + (-135606037 / 240000) * t ^ 8 + (4738703 / 180000) * t ^ 10 + (-5178511 / 720000) * t ^ 16 + (-1184 / 75) * c * t ^ 4 + (8096 / 625) * c * t ^ 6 + (4964 / 1875) * c * t ^ 8 + (8176 / 5625) * c * t ^ 10 + (292 / 5625) * c * t ^ 16 + (-5998361 / 24000) * alpha * t ^ 4 + (39531389 / 60000) * alpha * t ^ 6 + (-103504747 / 240000) * alpha * t ^ 8 + (1992571 / 60000) * alpha * t ^ 10 + (-6417521 / 720000) * alpha * t ^ 16 + (6914 / 1125) * alpha * c * t ^ 4 + (-3172 / 625) * alpha * c * t ^ 6 + (-5674 / 5625) * alpha * c * t ^ 8 + (-8176 / 16875) * alpha * c * t ^ 10 + (-292 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_10, v49_20, v49_30, v49_40]
  try simp only [phase48_00, phase48_10, phase48_20, phase48_30, phase48_40]
  try simp only [star_one, star_neg]
  linear_combination ((7601 / 4500) * t ^ 4 + (-764891 / 45000) * t ^ 6 + (129429 / 5000) * t ^ 8 + (-6188 / 16875) * t ^ 10 + (-3907 / 2250) * c * t ^ 4 + (21073 / 7500) * c * t ^ 6 + (1481 / 7500) * c * t ^ 8 + (1768 / 16875) * c * t ^ 10 + (71 / 1500) * c ^ 2 * t ^ 4 + (-371 / 7500) * c ^ 2 * t ^ 6 + (-2 / 5625) * c ^ 2 * t ^ 8) * alpha_sq + ((-1421 / 1125) * t ^ 4 + (881 / 625) * t ^ 6 + (-4 / 1875) * t ^ 8 + (284 / 5625) * t ^ 10 + (-1208 / 1125) * alpha * t ^ 4 + (2288 / 1875) * alpha * t ^ 6 + (-4 / 1875) * alpha * t ^ 8 + (284 / 5625) * alpha * t ^ 10) * c_sq
theorem v50_41 (t : ℂ) : (momentPoly 50 z50 4 1).eval t = ((-13774 / 25) * t ^ 3 + (4779363 / 5000) * t ^ 5 + (-2174369 / 7500) * t ^ 7 + (-3212401 / 30000) * t ^ 9 + (-209101 / 22500) * t ^ 11 + (123901 / 90000) * t ^ 17 + (-326017 / 250) * c * t ^ 3 + (476122633 / 180000) * c * t ^ 5 + (-43196587 / 30000) * c * t ^ 7 + (49734607 / 360000) * c * t ^ 9 + (-3656431 / 90000) * c * t ^ 11 + (788863 / 360000) * c * t ^ 17 + (-1568102 / 375) * alpha * t ^ 3 + (381502327 / 45000) * alpha * t ^ 5 + (-5691937 / 1500) * alpha * t ^ 7 + (-16529999 / 90000) * alpha * t ^ 9 + (-6304753 / 22500) * alpha * t ^ 11 + (-172723 / 18000) * alpha * t ^ 17 + (6887 / 150) * alpha * c * t ^ 3 + (-17606231 / 180000) * alpha * c * t ^ 5 + (5442511 / 90000) * alpha * c * t ^ 7 + (-3076081 / 360000) * alpha * c * t ^ 9 + (-38701 / 270000) * alpha * c * t ^ 11 + (123901 / 1080000) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_10, v49_11, v49_20, v49_21, v49_30, v49_31, v49_40, v49_41]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21, phase48_30, phase48_31, phase48_40, phase48_41]
  try simp only [star_one, star_neg]
  linear_combination ((276547 / 3000) * t ^ 3 + (-217487497 / 720000) * t ^ 5 + (4707463 / 24000) * t ^ 7 + (-6554539 / 7200000) * t ^ 9 + (2141867 / 1800000) * t ^ 11 + (-8350193 / 21600000) * t ^ 17 + (-271891 / 3000) * c * t ^ 3 + (443826587 / 2160000) * c * t ^ 5 + (-25553903 / 216000) * c * t ^ 7 + (177454273 / 21600000) * c * t ^ 9 + (-2160043 / 1800000) * c * t ^ 11 + (15461971 / 64800000) * c * t ^ 17 + (-194 / 125) * c ^ 2 * t ^ 3 + (11143 / 16875) * c ^ 2 * t ^ 5 + (8567 / 11250) * c ^ 2 * t ^ 7 + (331 / 56250) * c ^ 2 * t ^ 9 + (284 / 28125) * c ^ 2 * t ^ 11 + (146 / 84375) * c ^ 2 * t ^ 17) * alpha_sq + ((71 / 625) * t ^ 5 + (-142 / 1875) * t ^ 7 + (-71 / 1875) * t ^ 9 + (-776 / 125) * alpha * t ^ 3 + (8191 / 1875) * alpha * t ^ 5 + (1634 / 1125) * alpha * t ^ 7 + (-1083 / 3125) * alpha * t ^ 9 + (-3536 / 28125) * alpha * t ^ 11 + (-584 / 84375) * alpha * t ^ 17) * c_sq
theorem v50_42 (t : ℂ) : (momentPoly 50 z50 4 2).eval t = ((56658953 / 300) * t ^ 2 + (-562389821 / 1000) * t ^ 4 + (264937704757 / 480000) * t ^ 6 + (-86618926559 / 480000) * t ^ 8 + (2781942221 / 320000) * t ^ 10 + (-21111788957 / 2880000) * t ^ 12 + (53140577 / 80000) * t ^ 14 + (86145109 / 576000) * t ^ 18 + (-58671137 / 320000) * t ^ 20 + (-399308 / 75) * c * t ^ 2 + (228534 / 25) * c * t ^ 4 + (-34348891 / 12500) * c * t ^ 6 + (-7480321 / 7500) * c * t ^ 8 + (-2673893 / 22500) * c * t ^ 10 + (7182347 / 112500) * c * t ^ 12 + (-2156608 / 84375) * c * t ^ 14 + (348352 / 84375) * c * t ^ 18 + (-34 / 75) * c * t ^ 20 + (-22261421 / 100) * alpha * t ^ 2 + (655491411 / 1000) * alpha * t ^ 4 + (-4585125816181 / 7200000) * alpha * t ^ 6 + (1492361694943 / 7200000) * alpha * t ^ 8 + (-164065506023 / 14400000) * alpha * t ^ 10 + (368426544221 / 43200000) * alpha * t ^ 12 + (-1640151779 / 3600000) * alpha * t ^ 14 + (-1458289379 / 14400000) * alpha * t ^ 18 + (5655748201 / 43200000) * alpha * t ^ 20 + (-399308 / 225) * alpha * c * t ^ 2 + (76178 / 25) * alpha * c * t ^ 4 + (-41860441 / 45000) * alpha * c * t ^ 6 + (-4596431 / 15000) * alpha * c * t ^ 8 + (-1451771 / 30000) * alpha * c * t ^ 10 + (5215339 / 270000) * alpha * c * t ^ 12 + (-132151 / 13500) * alpha * c * t ^ 14 + (440453 / 270000) * alpha * c * t ^ 18 + (-43597 / 270000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_10, v49_11, v49_12, v49_20, v49_21, v49_22, v49_30, v49_31, v49_32, v49_40, v49_41, v49_42]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22, phase48_30, phase48_31, phase48_32, phase48_40, phase48_41, phase48_42]
  try simp only [star_one, star_neg]
  linear_combination ((99827 / 225) * t ^ 2 + (-296312 / 375) * t ^ 4 + (2558816701 / 5400000) * t ^ 6 + (-27242357 / 240000) * t ^ 8 + (-55285717 / 400000) * t ^ 10 + (51342926483 / 324000000) * t ^ 12 + (-976461179 / 81000000) * t ^ 14 + (-415335967 / 162000000) * t ^ 18 + (291097763 / 36000000) * t ^ 20 + (-57044 / 225) * c * t ^ 2 + (149408 / 375) * c * t ^ 4 + (-196480697 / 900000) * c * t ^ 6 + (32213021 / 600000) * c * t ^ 8 + (2349193 / 5400000) * c * t ^ 10 + (92909719 / 10800000) * c * t ^ 12 + (976769 / 2700000) * c * t ^ 14 + (90961 / 200000) * c * t ^ 18 + (-69997 / 2160000) * c * t ^ 20 + (-14261 / 75) * c ^ 2 * t ^ 2 + (48968 / 125) * c ^ 2 * t ^ 4 + (-1379932519 / 5400000) * c ^ 2 * t ^ 6 + (484211381 / 8100000) * c ^ 2 * t ^ 8 + (-83407621 / 10800000) * c ^ 2 * t ^ 10 + (2322979 / 4500000) * c ^ 2 * t ^ 12 + (-13439 / 62500) * c ^ 2 * t ^ 14 + (-64681 / 6000000) * c ^ 2 * t ^ 18 + (292 / 1265625) * c ^ 2 * t ^ 20) * alpha_sq + ((28522 / 75) * t ^ 2 + (-329056 / 375) * t ^ 4 + (319906787 / 450000) * t ^ 6 + (-52356707 / 225000) * t ^ 8 + (26718659 / 900000) * t ^ 10 + (-24687697 / 3375000) * t ^ 12 + (132046 / 140625) * t ^ 14 + (1102843 / 4500000) * t ^ 18 + (584 / 421875) * t ^ 20 + (-28522 / 75) * alpha * t ^ 2 + (342688 / 375) * alpha * t ^ 4 + (-528469807 / 675000) * alpha * t ^ 6 + (91673087 / 337500) * alpha * t ^ 8 + (-2478919 / 75000) * alpha * t ^ 10 + (1019408 / 140625) * alpha * t ^ 12 + (-345728 / 421875) * alpha * t ^ 14 + (-84032 / 421875) * alpha * t ^ 18 + (-584 / 421875) * alpha * t ^ 20) * c_sq
theorem v50_43 (t : ℂ) : (momentPoly 50 z50 4 3).eval t = ((11296268 / 5) * t + (-5141328) * t ^ 3 + (665449471 / 250) * t ^ 5 + (138503462123 / 187500) * t ^ 7 + (-83462884171 / 375000) * t ^ 9 + (-105607500541 / 375000) * t ^ 11 + (17828004067 / 2250000) * t ^ 13 + (-930581936 / 46875) * t ^ 15 + (-4218632339 / 2250000) * t ^ 17 + (1447380479 / 3375000) * t ^ 19 + (-1611291139 / 2250000) * t ^ 21 + (-279235753 / 6750000) * t ^ 25 + (-2824067 / 15) * c * t + (15829143 / 25) * c * t ^ 3 + (-487206127 / 600) * c * t ^ 5 + (4517846330021 / 9000000) * c * t ^ 7 + (-19544728907 / 120000) * c * t ^ 9 + (573024604111 / 18000000) * c * t ^ 11 + (-261888665651 / 54000000) * c * t ^ 13 + (4803557887 / 4500000) * c * t ^ 15 + (-123182041 / 1800000) * c * t ^ 17 + (2800080001 / 54000000) * c * t ^ 19 + (-662328217 / 18000000) * c * t ^ 21 + (-24914311 / 27000000) * c * t ^ 25 + (-11296268 / 15) * alpha * t + (41521812 / 25) * alpha * t ^ 3 + (-555983659 / 750) * alpha * t ^ 5 + (-282769432547 / 750000) * alpha * t ^ 7 + (83674590851 / 750000) * alpha * t ^ 9 + (410865084133 / 4500000) * alpha * t ^ 11 + (15186166147 / 13500000) * alpha * t ^ 13 + (6292173661 / 1125000) * alpha * t ^ 15 + (1862691727 / 2250000) * alpha * t ^ 17 + (-872484181 / 13500000) * alpha * t ^ 19 + (15828037 / 100000) * alpha * t ^ 21 + (24941279 / 2250000) * alpha * t ^ 25 + (-2824067 / 15) * alpha * c * t + (15498496 / 25) * alpha * c * t ^ 3 + (-2322377527 / 3000) * alpha * c * t ^ 5 + (262011688037 / 562500) * alpha * c * t ^ 7 + (-678198077347 / 4500000) * alpha * c * t ^ 9 + (13852855399 / 450000) * alpha * c * t ^ 11 + (-24750124673 / 5400000) * alpha * c * t ^ 13 + (269385893 / 225000) * alpha * c * t ^ 15 + (-1401384713 / 27000000) * alpha * c * t ^ 17 + (1490661007 / 20250000) * alpha * c * t ^ 19 + (-1531356367 / 27000000) * alpha * c * t ^ 21 + (-147739 / 129600) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_03, v49_10, v49_11, v49_12, v49_13, v49_20, v49_21, v49_22, v49_23, v49_30, v49_31, v49_32, v49_33, v49_40, v49_41, v49_42, v49_43]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23, phase48_30, phase48_31, phase48_32, phase48_33, phase48_40, phase48_41, phase48_42, phase48_43]
  try simp only [star_one, star_neg]
  linear_combination ((-13277107 / 1000) * t ^ 3 + (12592709 / 240) * t ^ 5 + (-1294033907719 / 24000000) * t ^ 7 + (144635145161 / 24000000) * t ^ 9 + (371388643747 / 48000000) * t ^ 11 + (-123257262791 / 432000000) * t ^ 13 + (111767014019 / 108000000) * t ^ 15 + (27988917839 / 270000000) * t ^ 17 + (-78253104967 / 6480000000) * t ^ 19 + (22832944259 / 720000000) * t ^ 21 + (1845392653 / 810000000) * t ^ 25 + (13053571 / 1000) * c * t ^ 3 + (-688162127 / 18000) * c * t ^ 5 + (7518896462111 / 216000000) * c * t ^ 7 + (-584060899379 / 72000000) * c * t ^ 9 + (-56439893923 / 48000000) * c * t ^ 11 + (-98775412391 / 259200000) * c * t ^ 13 + (4816348103 / 324000000) * c * t ^ 15 + (268925659 / 50625000) * c * t ^ 17 + (37947420871 / 6480000000) * c * t ^ 19 + (-78992468483 / 6480000000) * c * t ^ 21 + (-129064 / 18984375) * c * t ^ 25 + (27942 / 125) * c ^ 2 * t ^ 3 + (-367523 / 1125) * c ^ 2 * t ^ 5 + (28451401 / 1350000) * c ^ 2 * t ^ 7 + (163832561 / 1800000) * c ^ 2 * t ^ 9 + (-17956567 / 2250000) * c ^ 2 * t ^ 11 + (-2388431 / 6000000) * c ^ 2 * t ^ 13 + (14618527 / 13500000) * c ^ 2 * t ^ 15 + (14701 / 337500) * c ^ 2 * t ^ 17 + (-882133 / 4500000) * c ^ 2 * t ^ 19 + (28397 / 1200000) * c ^ 2 * t ^ 21) * alpha_sq + ((-167652 / 125) * t ^ 3 + (747187 / 375) * t ^ 5 + (-538111891 / 2250000) * t ^ 7 + (-101707219 / 250000) * t ^ 9 + (-40972957 / 4500000) * t ^ 11 + (83420587 / 13500000) * t ^ 13 + (-12315293 / 1125000) * t ^ 15 + (-337016 / 703125) * t ^ 17 + (82810457 / 67500000) * t ^ 19 + (-1952549 / 7500000) * t ^ 21 + (-20732 / 2109375) * t ^ 25 + (55884 / 125) * alpha * t ^ 3 + (-698623 / 1125) * alpha * t ^ 5 + (62648213 / 6750000) * alpha * t ^ 7 + (339411167 / 2250000) * alpha * t ^ 9 + (43686391 / 2700000) * alpha * t ^ 11 + (-111313477 / 40500000) * alpha * t ^ 13 + (10552067 / 3375000) * alpha * t ^ 15 + (129142 / 703125) * alpha * t ^ 17 + (-66683687 / 202500000) * alpha * t ^ 19 + (201411 / 2500000) * alpha * t ^ 21 + (20732 / 6328125) * alpha * t ^ 25) * c_sq
theorem v50_44 (t : ℂ) : (momentPoly 50 z50 4 4).eval t = (141203350 + (-2476133744 / 5) * t ^ 2 + (82418345427 / 125) * t ^ 4 + (-16954321363649 / 37500) * t ^ 6 + (33999189051114769 / 144000000) * t ^ 8 + (-7411235721054247 / 60000000) * t ^ 10 + (24709788603928471 / 720000000) * t ^ 12 + (-368633452390537 / 360000000) * t ^ 14 + (116222600774797 / 115200000) * t ^ 16 + (-45545813130613 / 360000000) * t ^ 18 + (99229458406997 / 2160000000) * t ^ 20 + (-1707205379899 / 40000000) * t ^ 22 + (40211312489077 / 1440000000) * t ^ 24 + (-1550901312143 / 1080000000) * t ^ 26 + (2081070088079 / 8640000000) * t ^ 32 + (27203792 / 375) * c * t ^ 4 + (-14616628 / 75) * c * t ^ 6 + (39367908127 / 250000) * c * t ^ 8 + (-64782375137 / 2812500) * c * t ^ 10 + (-209900236741 / 22500000) * c * t ^ 12 + (-107802243299 / 33750000) * c * t ^ 14 + (11798024279 / 13500000) * c * t ^ 16 + (-7294245863 / 16875000) * c * t ^ 18 + (-27797538091 / 202500000) * c * t ^ 20 + (3998205293 / 33750000) * c * t ^ 22 + (20494543 / 7500000) * c * t ^ 24 + (9044773 / 2109375) * c * t ^ 26 + (9044773 / 50625000) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_03, v49_04, v49_10, v49_11, v49_12, v49_13, v49_14, v49_20, v49_21, v49_22, v49_23, v49_24, v49_30, v49_31, v49_32, v49_33, v49_34, v49_40, v49_41, v49_42, v49_43, v49_44]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24, phase48_30, phase48_31, phase48_32, phase48_33, phase48_34, phase48_40, phase48_41, phase48_42, phase48_43, phase48_44]
  try simp only [star_one, star_neg]
  linear_combination ((-38347204 / 225) * t ^ 2 + (402829592 / 1125) * t ^ 4 + (23336161121 / 37500) * t ^ 6 + (-3849146050943 / 1500000) * t ^ 8 + (77003961307139 / 30000000) * t ^ 10 + (-71644144060957 / 90000000) * t ^ 12 + (13466270393971 / 1620000000) * t ^ 14 + (-44840415304511 / 1620000000) * t ^ 16 + (222336643807 / 135000000) * t ^ 18 + (210837656569 / 607500000) * t ^ 20 + (1052197495399 / 1620000000) * t ^ 22 + (-919918449833 / 900000000) * t ^ 24 + (47493231187 / 1518750000) * t ^ 26 + (-10226064499 / 1350000000) * t ^ 32 + (21912688 / 225) * c * t ^ 2 + (-148635608 / 1125) * c * t ^ 4 + (-1095721727 / 11250) * c * t ^ 6 + (100624050967 / 540000) * c * t ^ 8 + (-5171276474429 / 135000000) * c * t ^ 10 + (-306016459213 / 22500000) * c * t ^ 12 + (-682718833441 / 810000000) * c * t ^ 14 + (-1009895180509 / 810000000) * c * t ^ 16 + (-5513065933 / 67500000) * c * t ^ 18 + (32281057409 / 1215000000) * c * t ^ 20 + (-11102929409 / 162000000) * c * t ^ 22 + (207718319 / 450000000) * c * t ^ 24 + (-325979359 / 84375000) * c * t ^ 26 + (41602481 / 337500000) * c * t ^ 32 + (5478172 / 75) * c ^ 2 * t ^ 2 + (-28243776 / 125) * c ^ 2 * t ^ 4 + (14919870881 / 56250) * c ^ 2 * t ^ 6 + (-766153128313 / 5062500) * c ^ 2 * t ^ 8 + (1210755723871 / 25312500) * c ^ 2 * t ^ 10 + (-99876442109 / 10125000) * c ^ 2 * t ^ 12 + (16410681103 / 11250000) * c ^ 2 * t ^ 14 + (-3353922263 / 8437500) * c ^ 2 * t ^ 16 + (3805595371 / 202500000) * c ^ 2 * t ^ 18 + (-1843749203 / 75937500) * c ^ 2 * t ^ 20 + (1025814409 / 50625000) * c ^ 2 * t ^ 22 + (3125317 / 84375000) * c ^ 2 * t ^ 24 + (445598167 / 1012500000) * c ^ 2 * t ^ 26 + (42632 / 94921875) * c ^ 2 * t ^ 32) * alpha_sq + ((-21912688 / 75) * t ^ 2 + (68173688 / 75) * t ^ 4 + (-30271760627 / 28125) * t ^ 6 + (8372655715747 / 13500000) * t ^ 8 + (-1469935753621 / 7500000) * t ^ 10 + (5457276495989 / 135000000) * t ^ 12 + (-1033908622861 / 135000000) * t ^ 14 + (84807776891 / 33750000) * t ^ 16 + (-337435349 / 1875000) * t ^ 18 + (47771000779 / 405000000) * t ^ 20 + (-9935208649 / 135000000) * t ^ 22 + (-11462213 / 28125000) * t ^ 24 + (-280435357 / 84375000) * t ^ 26 + (-170528 / 31640625) * t ^ 32) * c_sq
#print axioms v50_00
#print axioms v50_11
#print axioms v50_22
#print axioms v50_33
#print axioms v50_44
end PhotonCertA
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z51 : Fin 51 → ℂ := Fin.snoc z50 (r ^ 3 * thetaMinus)
theorem v51_00 (t : ℂ) : (momentPoly 51 z51 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00]
  try simp only [phase48_00]
  try simp only [star_one, star_neg]
  ring
theorem v51_01 (t : ℂ) : (momentPoly 51 z51 0 1).eval t = ((9 / 10) * t + (-1 / 30) * c * t + (3 / 10) * alpha * t + (1 / 30) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01]
  try simp only [phase48_00, phase48_01]
  try simp only [star_one, star_neg]
  ring
theorem v51_02 (t : ℂ) : (momentPoly 51 z51 0 2).eval t = ((5221 / 600) * t ^ 2 + (-1731 / 200) * t ^ 4 + (-8 / 75) * c * t ^ 2 + (-1 / 75) * c * t ^ 4 + (1977 / 200) * alpha * t ^ 2 + (-5903 / 600) * alpha * t ^ 4 + (8 / 225) * alpha * c * t ^ 2 + (1 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02]
  try simp only [phase48_00, phase48_01, phase48_02]
  try simp only [star_one, star_neg]
  linear_combination ((4 / 225) * t ^ 2 + (-1 / 75) * c * t ^ 2 + (-1 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((2 / 225) * t ^ 2 + (2 / 225) * alpha * t ^ 2) * c_sq
theorem v51_03 (t : ℂ) : (momentPoly 51 z51 0 3).eval t = ((-639 / 200) * t ^ 3 + (639 / 200) * t ^ 5 + (-3793 / 1000) * c * t ^ 3 + (10739 / 3000) * c * t ^ 5 + (71 / 1125) * c * t ^ 9 + (90251 / 3000) * alpha * t ^ 3 + (-88331 / 3000) * alpha * t ^ 5 + (-221 / 125) * alpha * t ^ 9 + (-71 / 600) * alpha * c * t ^ 3 + (71 / 600) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_03]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03]
  try simp only [star_one, star_neg]
  linear_combination ((1561 / 2000) * t ^ 3 + (-2649 / 2000) * t ^ 5 + (-13937 / 18000) * c * t ^ 3 + (5011 / 6000) * c * t ^ 5 + (-7 / 1125) * c ^ 2 * t ^ 3 + (-2 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((28 / 1125) * alpha * t ^ 3 + (8 / 1125) * alpha * t ^ 5) * c_sq
theorem v51_04 (t : ℂ) : (momentPoly 51 z51 0 4).eval t = ((-23865281 / 40000) * t ^ 4 + (23895057 / 20000) * t ^ 6 + (-149618389 / 240000) * t ^ 8 + (6310031 / 180000) * t ^ 10 + (-1833541 / 240000) * t ^ 16 + (-6336 / 625) * c * t ^ 4 + (14732 / 1875) * c * t ^ 6 + (876 / 625) * c * t ^ 8 + (4672 / 5625) * c * t ^ 10 + (146 / 5625) * c * t ^ 16 + (18005631 / 40000) * alpha * t ^ 4 + (-54145981 / 60000) * alpha * t ^ 6 + (38619513 / 80000) * alpha * t ^ 8 + (-2516347 / 60000) * alpha * t ^ 10 + (6739633 / 720000) * alpha * t ^ 16 + (-21848 / 5625) * alpha * c * t ^ 4 + (1913 / 625) * alpha * c * t ^ 6 + (2983 / 5625) * alpha * c * t ^ 8 + (4672 / 16875) * alpha * c * t ^ 10 + (146 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_03, v50_04]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04]
  try simp only [star_one, star_neg]
  linear_combination ((16166 / 5625) * t ^ 4 + (-1180633 / 45000) * t ^ 6 + (409603 / 15000) * t ^ 8 + (-7072 / 16875) * t ^ 10 + (-32687 / 11250) * c * t ^ 4 + (69467 / 22500) * c * t ^ 6 + (5027 / 22500) * c * t ^ 8 + (884 / 5625) * c * t ^ 10 + (71 / 2250) * c ^ 2 * t ^ 4 + (-1121 / 33750) * c ^ 2 * t ^ 6 + (-4 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-1858 / 1875) * t ^ 4 + (618 / 625) * t ^ 6 + (-8 / 5625) * t ^ 8 + (568 / 16875) * t ^ 10 + (4864 / 5625) * alpha * t ^ 4 + (-4852 / 5625) * alpha * t ^ 6 + (8 / 5625) * alpha * t ^ 8 + (-568 / 16875) * alpha * t ^ 10) * c_sq
theorem v51_10 (t : ℂ) : (momentPoly 51 z51 1 0).eval t = ((9 / 10) * t + (-1 / 30) * c * t + (-3 / 10) * alpha * t + (-1 / 30) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_10]
  try simp only [phase48_00, phase48_10]
  try simp only [star_one, star_neg]
  ring
theorem v51_11 (t : ℂ) : (momentPoly 51 z51 1 1).eval t = (51 + (-734 / 15) * t ^ 2) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_10, v50_11]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11]
  try simp only [star_one, star_neg]
  linear_combination ((-4 / 225) * t ^ 2 + (1 / 75) * c * t ^ 2 + (1 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((-4 / 225) * t ^ 2) * c_sq
theorem v51_12 (t : ℂ) : (momentPoly 51 z51 1 2).eval t = ((909 / 10) * t + (-5377 / 75) * t ^ 3 + (-1301 / 75) * t ^ 5 + (-101 / 30) * c * t + (3571 / 900) * c * t ^ 3 + (-67 / 100) * c * t ^ 5 + (303 / 10) * alpha * t + (-20869 / 900) * alpha * t ^ 3 + (-5843 / 900) * alpha * t ^ 5 + (101 / 30) * alpha * c * t + (-35 / 9) * alpha * c * t ^ 3 + (133 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_10, v50_11, v50_12]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12]
  try simp only [star_one, star_neg]
  linear_combination ((-1561 / 6000) * t ^ 3 + (883 / 2000) * t ^ 5 + (13937 / 54000) * c * t ^ 3 + (-5011 / 18000) * c * t ^ 5 + (7 / 3375) * c ^ 2 * t ^ 3 + (2 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((-14 / 1125) * t ^ 3 + (-4 / 1125) * t ^ 5 + (-14 / 3375) * alpha * t ^ 3 + (-4 / 3375) * alpha * t ^ 5) * c_sq
theorem v51_13 (t : ℂ) : (momentPoly 51 z51 1 3).eval t = ((5221 / 4) * t ^ 2 + (-2536409 / 1000) * t ^ 4 + (459247 / 375) * t ^ 6 + (59371 / 9000) * t ^ 10 + (-16) * c * t ^ 2 + (4973 / 375) * c * t ^ 4 + (974 / 375) * c * t ^ 6 + (-8 / 75) * c * t ^ 10 + (5931 / 4) * alpha * t ^ 2 + (-8645117 / 3000) * alpha * t ^ 4 + (173909 / 125) * alpha * t ^ 6 + (70021 / 9000) * alpha * t ^ 10 + (16 / 3) * alpha * c * t ^ 2 + (-4973 / 1125) * alpha * c * t ^ 4 + (-974 / 1125) * alpha * c * t ^ 6 + (8 / 225) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_03, v50_10, v50_11, v50_12, v50_13]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13]
  try simp only [star_one, star_neg]
  linear_combination ((8 / 3) * t ^ 2 + (-30373 / 11250) * t ^ 4 + (3721 / 11250) * t ^ 6 + (1768 / 16875) * t ^ 10 + (-2) * c * t ^ 2 + (88567 / 45000) * c * t ^ 4 + (-10219 / 45000) * c * t ^ 6 + (-221 / 5625) * c * t ^ 10 + (-2 / 3) * c ^ 2 * t ^ 2 + (439 / 600) * c ^ 2 * t ^ 4 + (-311 / 3000) * c ^ 2 * t ^ 6) * alpha_sq + ((4 / 3) * t ^ 2 + (-6239 / 3750) * t ^ 4 + (4609 / 11250) * t ^ 6 + (142 / 16875) * t ^ 10 + (4 / 3) * alpha * t ^ 2 + (-19427 / 11250) * alpha * t ^ 4 + (591 / 1250) * alpha * t ^ 6 + (142 / 16875) * alpha * t ^ 10) * c_sq
theorem v51_14 (t : ℂ) : (momentPoly 51 z51 1 4).eval t = ((-63261 / 100) * t ^ 3 + (132871121 / 120000) * t ^ 5 + (-20049281 / 60000) * t ^ 7 + (-31581209 / 240000) * t ^ 9 + (-209101 / 20000) * t ^ 11 + (123901 / 80000) * t ^ 17 + (-375507 / 500) * c * t ^ 3 + (107574133 / 72000) * c * t ^ 5 + (-47945939 / 60000) * c * t ^ 7 + (54949999 / 720000) * c * t ^ 9 + (-11750861 / 540000) * c * t ^ 11 + (278101 / 240000) * c * t ^ 17 + (2978283 / 500) * alpha * t ^ 3 + (-3944624911 / 360000) * alpha * t ^ 5 + (260342933 / 60000) * alpha * t ^ 7 + (223715303 / 720000) * alpha * t ^ 9 + (181656683 / 540000) * alpha * t ^ 11 + (5282657 / 432000) * alpha * t ^ 17 + (-2343 / 100) * alpha * c * t ^ 3 + (18265111 / 360000) * alpha * c * t ^ 5 + (-5729351 / 180000) * alpha * c * t ^ 7 + (3246481 / 720000) * alpha * c * t ^ 9 + (38701 / 540000) * alpha * c * t ^ 11 + (-123901 / 2160000) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_03, v50_04, v50_10, v50_11, v50_12, v50_13, v50_14]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14]
  try simp only [star_one, star_neg]
  linear_combination ((154539 / 1000) * t ^ 3 + (-19491463 / 48000) * t ^ 5 + (437908349 / 1800000) * t ^ 7 + (8062613 / 7200000) * t ^ 9 + (1162297 / 600000) * t ^ 11 + (-2998139 / 7200000) * t ^ 17 + (-153307 / 1000) * c * t ^ 3 + (221464297 / 720000) * c * t ^ 5 + (-294630781 / 1800000) * c * t ^ 7 + (242484289 / 21600000) * c * t ^ 9 + (-31509251 / 16200000) * c * t ^ 11 + (1936891 / 7200000) * c * t ^ 17 + (-154 / 125) * c ^ 2 * t ^ 3 + (9923 / 16875) * c ^ 2 * t ^ 5 + (48674 / 84375) * c ^ 2 * t ^ 7 + (109 / 28125) * c ^ 2 * t ^ 9 + (1988 / 253125) * c ^ 2 * t ^ 11 + (292 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((497 / 5625) * t ^ 5 + (-71 / 1125) * t ^ 7 + (-142 / 5625) * t ^ 9 + (616 / 125) * alpha * t ^ 3 + (-65857 / 16875) * alpha * t ^ 5 + (-29083 / 28125) * alpha * t ^ 7 + (20678 / 84375) * alpha * t ^ 9 + (24752 / 253125) * alpha * t ^ 11 + (1168 / 253125) * alpha * t ^ 17) * c_sq
theorem v51_20 (t : ℂ) : (momentPoly 51 z51 2 0).eval t = ((5221 / 600) * t ^ 2 + (-1731 / 200) * t ^ 4 + (-8 / 75) * c * t ^ 2 + (-1 / 75) * c * t ^ 4 + (-1977 / 200) * alpha * t ^ 2 + (5903 / 600) * alpha * t ^ 4 + (-8 / 225) * alpha * c * t ^ 2 + (-1 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_10, v50_20]
  try simp only [phase48_00, phase48_10, phase48_20]
  try simp only [star_one, star_neg]
  linear_combination ((4 / 225) * t ^ 2 + (-1 / 75) * c * t ^ 2 + (-1 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((2 / 225) * t ^ 2 + (-2 / 225) * alpha * t ^ 2) * c_sq
theorem v51_21 (t : ℂ) : (momentPoly 51 z51 2 1).eval t = ((909 / 10) * t + (-5377 / 75) * t ^ 3 + (-1301 / 75) * t ^ 5 + (-101 / 30) * c * t + (3571 / 900) * c * t ^ 3 + (-67 / 100) * c * t ^ 5 + (-303 / 10) * alpha * t + (20869 / 900) * alpha * t ^ 3 + (5843 / 900) * alpha * t ^ 5 + (-101 / 30) * alpha * c * t + (35 / 9) * alpha * c * t ^ 3 + (-133 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_10, v50_11, v50_20, v50_21]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21]
  try simp only [star_one, star_neg]
  linear_combination ((-1561 / 6000) * t ^ 3 + (883 / 2000) * t ^ 5 + (13937 / 54000) * c * t ^ 3 + (-5011 / 18000) * c * t ^ 5 + (7 / 3375) * c ^ 2 * t ^ 3 + (2 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((-14 / 1125) * t ^ 3 + (-4 / 1125) * t ^ 5 + (14 / 3375) * alpha * t ^ 3 + (4 / 3375) * alpha * t ^ 5) * c_sq
theorem v51_22 (t : ℂ) : (momentPoly 51 z51 2 2).eval t = (5151 + (-29360 / 3) * t ^ 2 + (29178959 / 6000) * t ^ 4 + (-4838059 / 9000) * t ^ 6 + (5658121 / 18000) * t ^ 8 + (284 / 1125) * c * t ^ 4 + (-497 / 2250) * c * t ^ 6 + (-71 / 2250) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_10, v50_11, v50_12, v50_20, v50_21, v50_22]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22]
  try simp only [star_one, star_neg]
  linear_combination ((-32 / 9) * t ^ 2 + (2972 / 1125) * t ^ 4 + (373699 / 45000) * t ^ 6 + (-409603 / 45000) * t ^ 8 + (8 / 3) * c * t ^ 2 + (-5588 / 3375) * c * t ^ 4 + (-16343 / 22500) * c * t ^ 6 + (-5027 / 67500) * c * t ^ 8 + (8 / 9) * c ^ 2 * t ^ 2 + (-3328 / 3375) * c ^ 2 * t ^ 4 + (7558 / 50625) * c ^ 2 * t ^ 6 + (4 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((-32 / 9) * t ^ 2 + (1487 / 375) * t ^ 4 + (-10507 / 16875) * t ^ 6 + (-16 / 16875) * t ^ 8) * c_sq
theorem v51_23 (t : ℂ) : (momentPoly 51 z51 2 3).eval t = ((136359 / 10) * t + (-532323 / 25) * t ^ 3 + (7637693 / 2400) * t ^ 5 + (4438147 / 1200) * t ^ 7 + (14963431 / 20000) * t ^ 9 + (-865403 / 45000) * t ^ 11 + (2299307 / 45000) * t ^ 13 + (-15151 / 30) * c * t + (117843 / 100) * c * t ^ 3 + (-159482677 / 180000) * c * t ^ 5 + (21529037 / 90000) * c * t ^ 7 + (-1004393 / 36000) * c * t ^ 9 + (229579 / 135000) * c * t ^ 11 + (-8047 / 15000) * c * t ^ 13 + (45453 / 10) * alpha * t + (-688677 / 100) * alpha * t ^ 3 + (39180463 / 60000) * alpha * t ^ 5 + (42625177 / 30000) * alpha * t ^ 7 + (46235317 / 180000) * alpha * t ^ 9 + (-78253 / 27000) * alpha * t ^ 11 + (2016869 / 135000) * alpha * t ^ 13 + (15151 / 30) * alpha * c * t + (-1155) * alpha * c * t ^ 3 + (151219981 / 180000) * alpha * c * t ^ 5 + (-19511501 / 90000) * alpha * c * t ^ 7 + (5003789 / 180000) * alpha * c * t ^ 9 + (-72787 / 45000) * alpha * c * t ^ 11 + (16501 / 27000) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_03, v50_10, v50_11, v50_12, v50_13, v50_20, v50_21, v50_22, v50_23]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23]
  try simp only [star_one, star_neg]
  linear_combination ((-154539 / 2000) * t ^ 3 + (17898349 / 90000) * t ^ 5 + (-5634581 / 56250) * t ^ 7 + (-1143253 / 56250) * t ^ 9 + (13977 / 12500) * t ^ 11 + (-195143 / 75000) * t ^ 13 + (153307 / 2000) * c * t ^ 3 + (-40372207 / 270000) * c * t ^ 5 + (47760959 / 675000) * c * t ^ 7 + (1051837 / 675000) * c * t ^ 9 + (856907 / 2025000) * c * t ^ 11 + (-442 / 84375) * c * t ^ 13 + (77 / 125) * c ^ 2 * t ^ 3 + (-446 / 1125) * c ^ 2 * t ^ 5 + (-13831 / 67500) * c ^ 2 * t ^ 7 + (43 / 2700) * c ^ 2 * t ^ 9 + (14 / 3375) * c ^ 2 * t ^ 11) * alpha_sq + ((-462 / 125) * t ^ 3 + (27257 / 11250) * t ^ 5 + (62161 / 56250) * t ^ 7 + (-137 / 9375) * t ^ 9 + (-1106 / 84375) * t ^ 11 + (284 / 84375) * t ^ 13 + (-154 / 125) * alpha * t ^ 3 + (8423 / 11250) * alpha * t ^ 5 + (23087 / 56250) * alpha * t ^ 7 + (1009 / 84375) * alpha * t ^ 9 + (-1106 / 253125) * alpha * t ^ 11 + (284 / 253125) * alpha * t ^ 13) * c_sq
theorem v51_24 (t : ℂ) : (momentPoly 51 z51 2 4).eval t = ((19385573 / 75) * t ^ 2 + (-742489723 / 1000) * t ^ 4 + (1020002302943 / 1440000) * t ^ 6 + (-66515170769 / 288000) * t ^ 8 + (44261881429 / 2880000) * t ^ 10 + (-9216114311 / 960000) * t ^ 12 + (1882640707 / 2160000) * t ^ 14 + (1706458171 / 8640000) * t ^ 18 + (-1741411843 / 8640000) * t ^ 20 + (-237632 / 75) * c * t ^ 2 + (2094871 / 375) * c * t ^ 4 + (-50607413 / 28125) * c * t ^ 6 + (-1030601 / 1800) * c * t ^ 8 + (-8057759 / 112500) * c * t ^ 10 + (8642491 / 225000) * c * t ^ 12 + (-1310632 / 84375) * c * t ^ 14 + (211708 / 84375) * c * t ^ 18 + (-6 / 25) * c * t ^ 20 + (7340601 / 25) * alpha * t ^ 2 + (-2530264999 / 3000) * alpha * t ^ 4 + (5796152908021 / 7200000) * alpha * t ^ 6 + (-379915150883 / 1440000) * alpha * t ^ 8 + (3626571541 / 192000) * alpha * t ^ 10 + (-471399400253 / 43200000) * alpha * t ^ 12 + (2288064739 / 3600000) * alpha * t ^ 14 + (2030426339 / 14400000) * alpha * t ^ 18 + (-6324105833 / 43200000) * alpha * t ^ 20 + (237632 / 225) * alpha * c * t ^ 2 + (-2094871 / 1125) * alpha * c * t ^ 4 + (6849247 / 11250) * alpha * c * t ^ 6 + (15724751 / 90000) * alpha * c * t ^ 8 + (1321879 / 45000) * alpha * c * t ^ 10 + (-6361471 / 540000) * alpha * c * t ^ 12 + (2387161 / 405000) * alpha * c * t ^ 14 + (-198293 / 202500) * alpha * c * t ^ 18 + (45997 / 540000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_03, v50_04, v50_10, v50_11, v50_12, v50_13, v50_14, v50_20, v50_21, v50_22, v50_23, v50_24]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24]
  try simp only [star_one, star_neg]
  linear_combination ((118816 / 225) * t ^ 2 + (-5953108 / 5625) * t ^ 4 + (430712891 / 675000) * t ^ 6 + (228183811 / 10800000) * t ^ 8 + (-7700866171 / 27000000) * t ^ 10 + (2105161537 / 12000000) * t ^ 12 + (-504602809 / 27000000) * t ^ 14 + (-13943807 / 3375000) * t ^ 18 + (920321641 / 108000000) * t ^ 20 + (-29704 / 75) * c * t ^ 2 + (4339783 / 5625) * c * t ^ 4 + (-1192622143 / 2700000) * c * t ^ 6 + (18596059 / 360000) * c * t ^ 8 + (-20843711 / 5400000) * c * t ^ 10 + (162893591 / 10800000) * c * t ^ 12 + (-282947 / 540000) * c * t ^ 14 + (1236697 / 1800000) * c * t ^ 18 + (-79597 / 2160000) * c * t ^ 20 + (-29704 / 225) * c ^ 2 * t ^ 2 + (21511 / 75) * c ^ 2 * t ^ 4 + (-530229421 / 2700000) * c ^ 2 * t ^ 6 + (190115623 / 4050000) * c ^ 2 * t ^ 8 + (-53463697 / 9000000) * c ^ 2 * t ^ 10 + (8176169 / 20250000) * c ^ 2 * t ^ 12 + (-1153723 / 7593750) * c ^ 2 * t ^ 14 + (-1727699 / 243000000) * c ^ 2 * t ^ 18 + (584 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((59408 / 225) * t ^ 2 + (-1222844 / 1875) * t ^ 4 + (372264899 / 675000) * t ^ 6 + (-12166471 / 67500) * t ^ 8 + (150585551 / 6750000) * t ^ 10 + (-9086203 / 1687500) * t ^ 12 + (838412 / 1265625) * t ^ 14 + (3488273 / 20250000) * t ^ 18 + (1168 / 1265625) * t ^ 20 + (59408 / 225) * alpha * t ^ 2 + (-3807692 / 5625) * alpha * t ^ 4 + (203046037 / 337500) * alpha * t ^ 6 + (-35089649 / 168750) * alpha * t ^ 8 + (4630361 / 187500) * alpha * t ^ 10 + (-6759176 / 1265625) * alpha * t ^ 12 + (245864 / 421875) * alpha * t ^ 14 + (19922 / 140625) * alpha * t ^ 18 + (1168 / 1265625) * alpha * t ^ 20) * c_sq
theorem v51_30 (t : ℂ) : (momentPoly 51 z51 3 0).eval t = ((-639 / 200) * t ^ 3 + (639 / 200) * t ^ 5 + (-3793 / 1000) * c * t ^ 3 + (10739 / 3000) * c * t ^ 5 + (71 / 1125) * c * t ^ 9 + (-90251 / 3000) * alpha * t ^ 3 + (88331 / 3000) * alpha * t ^ 5 + (221 / 125) * alpha * t ^ 9 + (71 / 600) * alpha * c * t ^ 3 + (-71 / 600) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_10, v50_20, v50_30]
  try simp only [phase48_00, phase48_10, phase48_20, phase48_30]
  try simp only [star_one, star_neg]
  linear_combination ((1561 / 2000) * t ^ 3 + (-2649 / 2000) * t ^ 5 + (-13937 / 18000) * c * t ^ 3 + (5011 / 6000) * c * t ^ 5 + (-7 / 1125) * c ^ 2 * t ^ 3 + (-2 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-28 / 1125) * alpha * t ^ 3 + (-8 / 1125) * alpha * t ^ 5) * c_sq
theorem v51_31 (t : ℂ) : (momentPoly 51 z51 3 1).eval t = ((5221 / 4) * t ^ 2 + (-2536409 / 1000) * t ^ 4 + (459247 / 375) * t ^ 6 + (59371 / 9000) * t ^ 10 + (-16) * c * t ^ 2 + (4973 / 375) * c * t ^ 4 + (974 / 375) * c * t ^ 6 + (-8 / 75) * c * t ^ 10 + (-5931 / 4) * alpha * t ^ 2 + (8645117 / 3000) * alpha * t ^ 4 + (-173909 / 125) * alpha * t ^ 6 + (-70021 / 9000) * alpha * t ^ 10 + (-16 / 3) * alpha * c * t ^ 2 + (4973 / 1125) * alpha * c * t ^ 4 + (974 / 1125) * alpha * c * t ^ 6 + (-8 / 225) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_10, v50_11, v50_20, v50_21, v50_30, v50_31]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21, phase48_30, phase48_31]
  try simp only [star_one, star_neg]
  linear_combination ((8 / 3) * t ^ 2 + (-30373 / 11250) * t ^ 4 + (3721 / 11250) * t ^ 6 + (1768 / 16875) * t ^ 10 + (-2) * c * t ^ 2 + (88567 / 45000) * c * t ^ 4 + (-10219 / 45000) * c * t ^ 6 + (-221 / 5625) * c * t ^ 10 + (-2 / 3) * c ^ 2 * t ^ 2 + (439 / 600) * c ^ 2 * t ^ 4 + (-311 / 3000) * c ^ 2 * t ^ 6) * alpha_sq + ((4 / 3) * t ^ 2 + (-6239 / 3750) * t ^ 4 + (4609 / 11250) * t ^ 6 + (142 / 16875) * t ^ 10 + (-4 / 3) * alpha * t ^ 2 + (19427 / 11250) * alpha * t ^ 4 + (-591 / 1250) * alpha * t ^ 6 + (-142 / 16875) * alpha * t ^ 10) * c_sq
theorem v51_32 (t : ℂ) : (momentPoly 51 z51 3 2).eval t = ((136359 / 10) * t + (-532323 / 25) * t ^ 3 + (7637693 / 2400) * t ^ 5 + (4438147 / 1200) * t ^ 7 + (14963431 / 20000) * t ^ 9 + (-865403 / 45000) * t ^ 11 + (2299307 / 45000) * t ^ 13 + (-15151 / 30) * c * t + (117843 / 100) * c * t ^ 3 + (-159482677 / 180000) * c * t ^ 5 + (21529037 / 90000) * c * t ^ 7 + (-1004393 / 36000) * c * t ^ 9 + (229579 / 135000) * c * t ^ 11 + (-8047 / 15000) * c * t ^ 13 + (-45453 / 10) * alpha * t + (688677 / 100) * alpha * t ^ 3 + (-39180463 / 60000) * alpha * t ^ 5 + (-42625177 / 30000) * alpha * t ^ 7 + (-46235317 / 180000) * alpha * t ^ 9 + (78253 / 27000) * alpha * t ^ 11 + (-2016869 / 135000) * alpha * t ^ 13 + (-15151 / 30) * alpha * c * t + 1155 * alpha * c * t ^ 3 + (-151219981 / 180000) * alpha * c * t ^ 5 + (19511501 / 90000) * alpha * c * t ^ 7 + (-5003789 / 180000) * alpha * c * t ^ 9 + (72787 / 45000) * alpha * c * t ^ 11 + (-16501 / 27000) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_10, v50_11, v50_12, v50_20, v50_21, v50_22, v50_30, v50_31, v50_32]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22, phase48_30, phase48_31, phase48_32]
  try simp only [star_one, star_neg]
  linear_combination ((-154539 / 2000) * t ^ 3 + (17898349 / 90000) * t ^ 5 + (-5634581 / 56250) * t ^ 7 + (-1143253 / 56250) * t ^ 9 + (13977 / 12500) * t ^ 11 + (-195143 / 75000) * t ^ 13 + (153307 / 2000) * c * t ^ 3 + (-40372207 / 270000) * c * t ^ 5 + (47760959 / 675000) * c * t ^ 7 + (1051837 / 675000) * c * t ^ 9 + (856907 / 2025000) * c * t ^ 11 + (-442 / 84375) * c * t ^ 13 + (77 / 125) * c ^ 2 * t ^ 3 + (-446 / 1125) * c ^ 2 * t ^ 5 + (-13831 / 67500) * c ^ 2 * t ^ 7 + (43 / 2700) * c ^ 2 * t ^ 9 + (14 / 3375) * c ^ 2 * t ^ 11) * alpha_sq + ((-462 / 125) * t ^ 3 + (27257 / 11250) * t ^ 5 + (62161 / 56250) * t ^ 7 + (-137 / 9375) * t ^ 9 + (-1106 / 84375) * t ^ 11 + (284 / 84375) * t ^ 13 + (154 / 125) * alpha * t ^ 3 + (-8423 / 11250) * alpha * t ^ 5 + (-23087 / 56250) * alpha * t ^ 7 + (-1009 / 84375) * alpha * t ^ 9 + (1106 / 253125) * alpha * t ^ 11 + (-284 / 253125) * alpha * t ^ 13) * c_sq
theorem v51_33 (t : ℂ) : (momentPoly 51 z51 3 3).eval t = (772701 + (-10901368 / 5) * t ^ 2 + (4289306973 / 2000) * t ^ 4 + (-24198102287 / 25000) * t ^ 6 + (10804084901 / 30000) * t ^ 8 + (-3231271803 / 25000) * t ^ 10 + (29681847 / 25000) * t ^ 12 + (-265453849 / 225000) * t ^ 14 + (-3437294 / 84375) * t ^ 18 + (13916 / 125) * c * t ^ 4 + (-126238 / 625) * c * t ^ 6 + (269729 / 3750) * c * t ^ 8 + (33512 / 1875) * c * t ^ 10 + (568 / 375) * c * t ^ 12 + (-497 / 750) * c * t ^ 14) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_03, v50_10, v50_11, v50_12, v50_13, v50_20, v50_21, v50_22, v50_23, v50_30, v50_31, v50_32, v50_33]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23, phase48_30, phase48_31, phase48_32, phase48_33]
  try simp only [star_one, star_neg]
  linear_combination ((-59408 / 75) * t ^ 2 + (145628 / 125) * t ^ 4 + (367742309 / 112500) * t ^ 6 + (-1625846669 / 225000) * t ^ 8 + (132749209 / 37500) * t ^ 10 + (3702331 / 421875) * t ^ 12 + (18776299 / 3375000) * t ^ 14 + (-781456 / 1265625) * t ^ 18 + (14852 / 25) * c * t ^ 2 + (-273812 / 375) * c * t ^ 4 + (-64133329 / 450000) * c * t ^ 6 + (49510397 / 225000) * c * t ^ 8 + (26191003 / 450000) * c * t ^ 10 + (6911 / 37500) * c * t ^ 12 + (150403 / 56250) * c * t ^ 14 + (14852 / 75) * c ^ 2 * t ^ 2 + (-163072 / 375) * c ^ 2 * t ^ 4 + (411272159 / 1350000) * c ^ 2 * t ^ 6 + (-1150433 / 15000) * c ^ 2 * t ^ 8 + (487841 / 50000) * c ^ 2 * t ^ 10 + (-197297 / 337500) * c ^ 2 * t ^ 12 + (15713 / 67500) * c ^ 2 * t ^ 14) * alpha_sq + ((-59408 / 75) * t ^ 2 + (218589 / 125) * t ^ 4 + (-139328701 / 112500) * t ^ 6 + (17828927 / 56250) * t ^ 8 + (-484073 / 12500) * t ^ 10 + (452818 / 140625) * t ^ 12 + (-746893 / 421875) * t ^ 14 + (-20164 / 1265625) * t ^ 18) * c_sq
theorem v51_34 (t : ℂ) : (momentPoly 51 z51 3 4).eval t = ((27004509 / 10) * t + (-156535224 / 25) * t ^ 3 + (1334133037 / 400) * t ^ 5 + (1322179759969 / 1500000) * t ^ 7 + (-415009990057 / 1500000) * t ^ 9 + (-214498539017 / 600000) * t ^ 11 + (29071965637 / 4500000) * t ^ 13 + (-114503642833 / 4500000) * t ^ 15 + (-4873512723 / 2000000) * t ^ 17 + (20359828937 / 27000000) * t ^ 19 + (-8380611541 / 9000000) * t ^ 21 + (-2709988657 / 54000000) * t ^ 25 + (-1000167 / 10) * c * t + (8663246 / 25) * c * t ^ 3 + (-13751209369 / 30000) * c * t ^ 5 + (1052258520637 / 3600000) * c * t ^ 7 + (-116795763029 / 1200000) * c * t ^ 9 + (46072277621 / 2400000) * c * t ^ 11 + (-312628711741 / 108000000) * c * t ^ 13 + (5605374541 / 9000000) * c * t ^ 15 + (-2059390711 / 54000000) * c * t ^ 17 + (9981534919 / 324000000) * c * t ^ 19 + (-18218873 / 864000) * c * t ^ 21 + (-26714311 / 54000000) * c * t ^ 25 + (9001503 / 10) * alpha * t + (-50628194 / 25) * alpha * t ^ 3 + (28054649033 / 30000) * alpha * t ^ 5 + (2739820462483 / 6000000) * alpha * t ^ 7 + (-2493975079427 / 18000000) * alpha * t ^ 9 + (-847003440521 / 7200000) * alpha * t ^ 11 + (-242423261933 / 108000000) * alpha * t ^ 13 + (-21713534117 / 3000000) * alpha * t ^ 15 + (-11402698897 / 10800000) * alpha * t ^ 17 + (9597819427 / 64800000) * alpha * t ^ 19 + (-23131898461 / 108000000) * alpha * t ^ 21 + (-2217110479 / 162000000) * alpha * t ^ 25 + (1000167 / 10) * alpha * c * t + (-339640) * alpha * c * t ^ 3 + (4384028319 / 10000) * alpha * c * t ^ 5 + (-1228147735177 / 4500000) * alpha * c * t ^ 7 + (407839384421 / 4500000) * alpha * c * t ^ 9 + (-33404087431 / 1800000) * alpha * c * t ^ 11 + (616908947 / 225000) * alpha * c * t ^ 13 + (-9334277393 / 13500000) * alpha * c * t ^ 15 + (176387201 / 6000000) * alpha * c * t ^ 17 + (-1151669743 / 27000000) * alpha * c * t ^ 19 + (853117973 / 27000000) * alpha * c * t ^ 21 + (156379 / 259200) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_03, v50_04, v50_10, v50_11, v50_12, v50_13, v50_14, v50_20, v50_21, v50_22, v50_23, v50_24, v50_30, v50_31, v50_32, v50_33, v50_34]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24, phase48_30, phase48_31, phase48_32, phase48_33, phase48_34]
  try simp only [star_one, star_neg]
  linear_combination ((-5680479 / 250) * t ^ 3 + (2339792471 / 30000) * t ^ 5 + (-5398350604661 / 72000000) * t ^ 7 + (28327541591 / 2880000) * t ^ 9 + (1244671734041 / 144000000) * t ^ 11 + (-11345628631 / 86400000) * t ^ 13 + (644214892363 / 540000000) * t ^ 15 + (32588618207 / 270000000) * t ^ 17 + (-123272059 / 5760000) * t ^ 19 + (9279167749 / 240000000) * t ^ 21 + (662588719 / 270000000) * t ^ 25 + (16905581 / 750) * c * t ^ 3 + (-5689930493 / 90000) * c * t ^ 5 + (12438749260543 / 216000000) * c * t ^ 7 + (-702997756337 / 43200000) * c * t ^ 9 + (2890509799 / 144000000) * c * t ^ 11 + (-900142498031 / 1296000000) * c * t ^ 13 + (7147244647 / 180000000) * c * t ^ 15 + (98748131 / 25312500) * c * t ^ 17 + (41704936849 / 3888000000) * c * t ^ 19 + (-87332099999 / 6480000000) * c * t ^ 21 + (-64532 / 6328125) * c * t ^ 25 + (67928 / 375) * c ^ 2 * t ^ 3 + (-316574 / 1125) * c ^ 2 * t ^ 5 + (45888403 / 1350000) * c ^ 2 * t ^ 7 + (978861073 / 13500000) * c ^ 2 * t ^ 9 + (-82921847 / 13500000) * c ^ 2 * t ^ 11 + (-2760241 / 5400000) * c ^ 2 * t ^ 13 + (243773 / 270000) * c ^ 2 * t ^ 15 + (15601 / 506250) * c ^ 2 * t ^ 17 + (-6689723 / 40500000) * c ^ 2 * t ^ 19 + (3333 / 200000) * c ^ 2 * t ^ 21) * alpha_sq + ((-135856 / 125) * t ^ 3 + (3213949 / 1875) * t ^ 5 + (-665793613 / 2250000) * t ^ 7 + (-36518011 / 112500) * t ^ 9 + (-26022071 / 4500000) * t ^ 11 + (36122879 / 6750000) * t ^ 13 + (-74309737 / 8437500) * t ^ 15 + (-79696 / 234375) * t ^ 17 + (42049537 / 40500000) * t ^ 19 + (-6198959 / 33750000) * t ^ 21 + (-41464 / 6328125) * t ^ 25 + (-135856 / 375) * alpha * t ^ 3 + (3021113 / 5625) * alpha * t ^ 5 + (-89909753 / 2250000) * alpha * t ^ 7 + (-41792381 / 337500) * alpha * t ^ 9 + (-154878137 / 13500000) * alpha * t ^ 11 + (45086833 / 20250000) * alpha * t ^ 13 + (-7112663 / 2812500) * alpha * t ^ 15 + (-818084 / 6328125) * alpha * t ^ 17 + (34855423 / 121500000) * alpha * t ^ 19 + (-5779409 / 101250000) * alpha * t ^ 21 + (-41464 / 18984375) * alpha * t ^ 25) * c_sq
theorem v51_40 (t : ℂ) : (momentPoly 51 z51 4 0).eval t = ((-23865281 / 40000) * t ^ 4 + (23895057 / 20000) * t ^ 6 + (-149618389 / 240000) * t ^ 8 + (6310031 / 180000) * t ^ 10 + (-1833541 / 240000) * t ^ 16 + (-6336 / 625) * c * t ^ 4 + (14732 / 1875) * c * t ^ 6 + (876 / 625) * c * t ^ 8 + (4672 / 5625) * c * t ^ 10 + (146 / 5625) * c * t ^ 16 + (-18005631 / 40000) * alpha * t ^ 4 + (54145981 / 60000) * alpha * t ^ 6 + (-38619513 / 80000) * alpha * t ^ 8 + (2516347 / 60000) * alpha * t ^ 10 + (-6739633 / 720000) * alpha * t ^ 16 + (21848 / 5625) * alpha * c * t ^ 4 + (-1913 / 625) * alpha * c * t ^ 6 + (-2983 / 5625) * alpha * c * t ^ 8 + (-4672 / 16875) * alpha * c * t ^ 10 + (-146 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_10, v50_20, v50_30, v50_40]
  try simp only [phase48_00, phase48_10, phase48_20, phase48_30, phase48_40]
  try simp only [star_one, star_neg]
  linear_combination ((16166 / 5625) * t ^ 4 + (-1180633 / 45000) * t ^ 6 + (409603 / 15000) * t ^ 8 + (-7072 / 16875) * t ^ 10 + (-32687 / 11250) * c * t ^ 4 + (69467 / 22500) * c * t ^ 6 + (5027 / 22500) * c * t ^ 8 + (884 / 5625) * c * t ^ 10 + (71 / 2250) * c ^ 2 * t ^ 4 + (-1121 / 33750) * c ^ 2 * t ^ 6 + (-4 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-1858 / 1875) * t ^ 4 + (618 / 625) * t ^ 6 + (-8 / 5625) * t ^ 8 + (568 / 16875) * t ^ 10 + (-4864 / 5625) * alpha * t ^ 4 + (4852 / 5625) * alpha * t ^ 6 + (-8 / 5625) * alpha * t ^ 8 + (568 / 16875) * alpha * t ^ 10) * c_sq
theorem v51_41 (t : ℂ) : (momentPoly 51 z51 4 1).eval t = ((-63261 / 100) * t ^ 3 + (132871121 / 120000) * t ^ 5 + (-20049281 / 60000) * t ^ 7 + (-31581209 / 240000) * t ^ 9 + (-209101 / 20000) * t ^ 11 + (123901 / 80000) * t ^ 17 + (-375507 / 500) * c * t ^ 3 + (107574133 / 72000) * c * t ^ 5 + (-47945939 / 60000) * c * t ^ 7 + (54949999 / 720000) * c * t ^ 9 + (-11750861 / 540000) * c * t ^ 11 + (278101 / 240000) * c * t ^ 17 + (-2978283 / 500) * alpha * t ^ 3 + (3944624911 / 360000) * alpha * t ^ 5 + (-260342933 / 60000) * alpha * t ^ 7 + (-223715303 / 720000) * alpha * t ^ 9 + (-181656683 / 540000) * alpha * t ^ 11 + (-5282657 / 432000) * alpha * t ^ 17 + (2343 / 100) * alpha * c * t ^ 3 + (-18265111 / 360000) * alpha * c * t ^ 5 + (5729351 / 180000) * alpha * c * t ^ 7 + (-3246481 / 720000) * alpha * c * t ^ 9 + (-38701 / 540000) * alpha * c * t ^ 11 + (123901 / 2160000) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_10, v50_11, v50_20, v50_21, v50_30, v50_31, v50_40, v50_41]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21, phase48_30, phase48_31, phase48_40, phase48_41]
  try simp only [star_one, star_neg]
  linear_combination ((154539 / 1000) * t ^ 3 + (-19491463 / 48000) * t ^ 5 + (437908349 / 1800000) * t ^ 7 + (8062613 / 7200000) * t ^ 9 + (1162297 / 600000) * t ^ 11 + (-2998139 / 7200000) * t ^ 17 + (-153307 / 1000) * c * t ^ 3 + (221464297 / 720000) * c * t ^ 5 + (-294630781 / 1800000) * c * t ^ 7 + (242484289 / 21600000) * c * t ^ 9 + (-31509251 / 16200000) * c * t ^ 11 + (1936891 / 7200000) * c * t ^ 17 + (-154 / 125) * c ^ 2 * t ^ 3 + (9923 / 16875) * c ^ 2 * t ^ 5 + (48674 / 84375) * c ^ 2 * t ^ 7 + (109 / 28125) * c ^ 2 * t ^ 9 + (1988 / 253125) * c ^ 2 * t ^ 11 + (292 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((497 / 5625) * t ^ 5 + (-71 / 1125) * t ^ 7 + (-142 / 5625) * t ^ 9 + (-616 / 125) * alpha * t ^ 3 + (65857 / 16875) * alpha * t ^ 5 + (29083 / 28125) * alpha * t ^ 7 + (-20678 / 84375) * alpha * t ^ 9 + (-24752 / 253125) * alpha * t ^ 11 + (-1168 / 253125) * alpha * t ^ 17) * c_sq
theorem v51_42 (t : ℂ) : (momentPoly 51 z51 4 2).eval t = ((19385573 / 75) * t ^ 2 + (-742489723 / 1000) * t ^ 4 + (1020002302943 / 1440000) * t ^ 6 + (-66515170769 / 288000) * t ^ 8 + (44261881429 / 2880000) * t ^ 10 + (-9216114311 / 960000) * t ^ 12 + (1882640707 / 2160000) * t ^ 14 + (1706458171 / 8640000) * t ^ 18 + (-1741411843 / 8640000) * t ^ 20 + (-237632 / 75) * c * t ^ 2 + (2094871 / 375) * c * t ^ 4 + (-50607413 / 28125) * c * t ^ 6 + (-1030601 / 1800) * c * t ^ 8 + (-8057759 / 112500) * c * t ^ 10 + (8642491 / 225000) * c * t ^ 12 + (-1310632 / 84375) * c * t ^ 14 + (211708 / 84375) * c * t ^ 18 + (-6 / 25) * c * t ^ 20 + (-7340601 / 25) * alpha * t ^ 2 + (2530264999 / 3000) * alpha * t ^ 4 + (-5796152908021 / 7200000) * alpha * t ^ 6 + (379915150883 / 1440000) * alpha * t ^ 8 + (-3626571541 / 192000) * alpha * t ^ 10 + (471399400253 / 43200000) * alpha * t ^ 12 + (-2288064739 / 3600000) * alpha * t ^ 14 + (-2030426339 / 14400000) * alpha * t ^ 18 + (6324105833 / 43200000) * alpha * t ^ 20 + (-237632 / 225) * alpha * c * t ^ 2 + (2094871 / 1125) * alpha * c * t ^ 4 + (-6849247 / 11250) * alpha * c * t ^ 6 + (-15724751 / 90000) * alpha * c * t ^ 8 + (-1321879 / 45000) * alpha * c * t ^ 10 + (6361471 / 540000) * alpha * c * t ^ 12 + (-2387161 / 405000) * alpha * c * t ^ 14 + (198293 / 202500) * alpha * c * t ^ 18 + (-45997 / 540000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_10, v50_11, v50_12, v50_20, v50_21, v50_22, v50_30, v50_31, v50_32, v50_40, v50_41, v50_42]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22, phase48_30, phase48_31, phase48_32, phase48_40, phase48_41, phase48_42]
  try simp only [star_one, star_neg]
  linear_combination ((118816 / 225) * t ^ 2 + (-5953108 / 5625) * t ^ 4 + (430712891 / 675000) * t ^ 6 + (228183811 / 10800000) * t ^ 8 + (-7700866171 / 27000000) * t ^ 10 + (2105161537 / 12000000) * t ^ 12 + (-504602809 / 27000000) * t ^ 14 + (-13943807 / 3375000) * t ^ 18 + (920321641 / 108000000) * t ^ 20 + (-29704 / 75) * c * t ^ 2 + (4339783 / 5625) * c * t ^ 4 + (-1192622143 / 2700000) * c * t ^ 6 + (18596059 / 360000) * c * t ^ 8 + (-20843711 / 5400000) * c * t ^ 10 + (162893591 / 10800000) * c * t ^ 12 + (-282947 / 540000) * c * t ^ 14 + (1236697 / 1800000) * c * t ^ 18 + (-79597 / 2160000) * c * t ^ 20 + (-29704 / 225) * c ^ 2 * t ^ 2 + (21511 / 75) * c ^ 2 * t ^ 4 + (-530229421 / 2700000) * c ^ 2 * t ^ 6 + (190115623 / 4050000) * c ^ 2 * t ^ 8 + (-53463697 / 9000000) * c ^ 2 * t ^ 10 + (8176169 / 20250000) * c ^ 2 * t ^ 12 + (-1153723 / 7593750) * c ^ 2 * t ^ 14 + (-1727699 / 243000000) * c ^ 2 * t ^ 18 + (584 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((59408 / 225) * t ^ 2 + (-1222844 / 1875) * t ^ 4 + (372264899 / 675000) * t ^ 6 + (-12166471 / 67500) * t ^ 8 + (150585551 / 6750000) * t ^ 10 + (-9086203 / 1687500) * t ^ 12 + (838412 / 1265625) * t ^ 14 + (3488273 / 20250000) * t ^ 18 + (1168 / 1265625) * t ^ 20 + (-59408 / 225) * alpha * t ^ 2 + (3807692 / 5625) * alpha * t ^ 4 + (-203046037 / 337500) * alpha * t ^ 6 + (35089649 / 168750) * alpha * t ^ 8 + (-4630361 / 187500) * alpha * t ^ 10 + (6759176 / 1265625) * alpha * t ^ 12 + (-245864 / 421875) * alpha * t ^ 14 + (-19922 / 140625) * alpha * t ^ 18 + (-1168 / 1265625) * alpha * t ^ 20) * c_sq
theorem v51_43 (t : ℂ) : (momentPoly 51 z51 4 3).eval t = ((27004509 / 10) * t + (-156535224 / 25) * t ^ 3 + (1334133037 / 400) * t ^ 5 + (1322179759969 / 1500000) * t ^ 7 + (-415009990057 / 1500000) * t ^ 9 + (-214498539017 / 600000) * t ^ 11 + (29071965637 / 4500000) * t ^ 13 + (-114503642833 / 4500000) * t ^ 15 + (-4873512723 / 2000000) * t ^ 17 + (20359828937 / 27000000) * t ^ 19 + (-8380611541 / 9000000) * t ^ 21 + (-2709988657 / 54000000) * t ^ 25 + (-1000167 / 10) * c * t + (8663246 / 25) * c * t ^ 3 + (-13751209369 / 30000) * c * t ^ 5 + (1052258520637 / 3600000) * c * t ^ 7 + (-116795763029 / 1200000) * c * t ^ 9 + (46072277621 / 2400000) * c * t ^ 11 + (-312628711741 / 108000000) * c * t ^ 13 + (5605374541 / 9000000) * c * t ^ 15 + (-2059390711 / 54000000) * c * t ^ 17 + (9981534919 / 324000000) * c * t ^ 19 + (-18218873 / 864000) * c * t ^ 21 + (-26714311 / 54000000) * c * t ^ 25 + (-9001503 / 10) * alpha * t + (50628194 / 25) * alpha * t ^ 3 + (-28054649033 / 30000) * alpha * t ^ 5 + (-2739820462483 / 6000000) * alpha * t ^ 7 + (2493975079427 / 18000000) * alpha * t ^ 9 + (847003440521 / 7200000) * alpha * t ^ 11 + (242423261933 / 108000000) * alpha * t ^ 13 + (21713534117 / 3000000) * alpha * t ^ 15 + (11402698897 / 10800000) * alpha * t ^ 17 + (-9597819427 / 64800000) * alpha * t ^ 19 + (23131898461 / 108000000) * alpha * t ^ 21 + (2217110479 / 162000000) * alpha * t ^ 25 + (-1000167 / 10) * alpha * c * t + 339640 * alpha * c * t ^ 3 + (-4384028319 / 10000) * alpha * c * t ^ 5 + (1228147735177 / 4500000) * alpha * c * t ^ 7 + (-407839384421 / 4500000) * alpha * c * t ^ 9 + (33404087431 / 1800000) * alpha * c * t ^ 11 + (-616908947 / 225000) * alpha * c * t ^ 13 + (9334277393 / 13500000) * alpha * c * t ^ 15 + (-176387201 / 6000000) * alpha * c * t ^ 17 + (1151669743 / 27000000) * alpha * c * t ^ 19 + (-853117973 / 27000000) * alpha * c * t ^ 21 + (-156379 / 259200) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_03, v50_10, v50_11, v50_12, v50_13, v50_20, v50_21, v50_22, v50_23, v50_30, v50_31, v50_32, v50_33, v50_40, v50_41, v50_42, v50_43]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23, phase48_30, phase48_31, phase48_32, phase48_33, phase48_40, phase48_41, phase48_42, phase48_43]
  try simp only [star_one, star_neg]
  linear_combination ((-5680479 / 250) * t ^ 3 + (2339792471 / 30000) * t ^ 5 + (-5398350604661 / 72000000) * t ^ 7 + (28327541591 / 2880000) * t ^ 9 + (1244671734041 / 144000000) * t ^ 11 + (-11345628631 / 86400000) * t ^ 13 + (644214892363 / 540000000) * t ^ 15 + (32588618207 / 270000000) * t ^ 17 + (-123272059 / 5760000) * t ^ 19 + (9279167749 / 240000000) * t ^ 21 + (662588719 / 270000000) * t ^ 25 + (16905581 / 750) * c * t ^ 3 + (-5689930493 / 90000) * c * t ^ 5 + (12438749260543 / 216000000) * c * t ^ 7 + (-702997756337 / 43200000) * c * t ^ 9 + (2890509799 / 144000000) * c * t ^ 11 + (-900142498031 / 1296000000) * c * t ^ 13 + (7147244647 / 180000000) * c * t ^ 15 + (98748131 / 25312500) * c * t ^ 17 + (41704936849 / 3888000000) * c * t ^ 19 + (-87332099999 / 6480000000) * c * t ^ 21 + (-64532 / 6328125) * c * t ^ 25 + (67928 / 375) * c ^ 2 * t ^ 3 + (-316574 / 1125) * c ^ 2 * t ^ 5 + (45888403 / 1350000) * c ^ 2 * t ^ 7 + (978861073 / 13500000) * c ^ 2 * t ^ 9 + (-82921847 / 13500000) * c ^ 2 * t ^ 11 + (-2760241 / 5400000) * c ^ 2 * t ^ 13 + (243773 / 270000) * c ^ 2 * t ^ 15 + (15601 / 506250) * c ^ 2 * t ^ 17 + (-6689723 / 40500000) * c ^ 2 * t ^ 19 + (3333 / 200000) * c ^ 2 * t ^ 21) * alpha_sq + ((-135856 / 125) * t ^ 3 + (3213949 / 1875) * t ^ 5 + (-665793613 / 2250000) * t ^ 7 + (-36518011 / 112500) * t ^ 9 + (-26022071 / 4500000) * t ^ 11 + (36122879 / 6750000) * t ^ 13 + (-74309737 / 8437500) * t ^ 15 + (-79696 / 234375) * t ^ 17 + (42049537 / 40500000) * t ^ 19 + (-6198959 / 33750000) * t ^ 21 + (-41464 / 6328125) * t ^ 25 + (135856 / 375) * alpha * t ^ 3 + (-3021113 / 5625) * alpha * t ^ 5 + (89909753 / 2250000) * alpha * t ^ 7 + (41792381 / 337500) * alpha * t ^ 9 + (154878137 / 13500000) * alpha * t ^ 11 + (-45086833 / 20250000) * alpha * t ^ 13 + (7112663 / 2812500) * alpha * t ^ 15 + (818084 / 6328125) * alpha * t ^ 17 + (-34855423 / 121500000) * alpha * t ^ 19 + (5779409 / 101250000) * alpha * t ^ 21 + (41464 / 18984375) * alpha * t ^ 25) * c_sq
theorem v51_44 (t : ℂ) : (momentPoly 51 z51 4 4).eval t = (153025551 + (-2849863632 / 5) * t ^ 2 + (416179492217 / 500) * t ^ 4 + (-24499611507049 / 37500) * t ^ 6 + (266041561946642389 / 720000000) * t ^ 8 + (-10593763836825827 / 60000000) * t ^ 10 + (6645745165121371 / 144000000) * t ^ 12 + (-953041842334853 / 360000000) * t ^ 14 + (4616726727000997 / 2880000000) * t ^ 16 + (-20645632641847 / 120000000) * t ^ 18 + (144638391725621 / 2160000000) * t ^ 20 + (-7304250961397 / 120000000) * t ^ 22 + (142077113894351 / 4320000000) * t ^ 24 + (-7001481066829 / 3240000000) * t ^ 26 + (7009489387501 / 25920000000) * t ^ 32 + (16202768 / 375) * c * t ^ 4 + (-221478607 / 1875) * c * t ^ 6 + (91974305879 / 937500) * c * t ^ 8 + (-40638069939 / 2500000) * c * t ^ 10 + (-7908521413 / 1500000) * c * t ^ 12 + (-29033352451 / 15000000) * c * t ^ 14 + (2696281041 / 5000000) * c * t ^ 16 + (-8715666527 / 33750000) * c * t ^ 18 + (-2133979481 / 25312500) * c * t ^ 20 + (9585554057 / 135000000) * c * t ^ 22 + (195069979 / 135000000) * c * t ^ 24 + (63313411 / 25312500) * c * t ^ 26 + (9044773 / 101250000) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_03, v50_04, v50_10, v50_11, v50_12, v50_13, v50_14, v50_20, v50_21, v50_22, v50_23, v50_24, v50_30, v50_31, v50_32, v50_33, v50_34, v50_40, v50_41, v50_42, v50_43, v50_44]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24, phase48_30, phase48_31, phase48_32, phase48_33, phase48_34, phase48_40, phase48_41, phase48_42, phase48_43, phase48_44]
  try simp only [star_one, star_neg]
  linear_combination ((-5176864 / 25) * t ^ 2 + (169558544 / 375) * t ^ 4 + (41979256189 / 37500) * t ^ 6 + (-3719688306049 / 937500) * t ^ 8 + (67816276221529 / 18000000) * t ^ 10 + (-318469221212789 / 270000000) * t ^ 12 + (9639163556927 / 180000000) * t ^ 14 + (-4573893844481 / 108000000) * t ^ 16 + (427629603649 / 135000000) * t ^ 18 + (80799726677 / 405000000) * t ^ 20 + (3302480583101 / 2700000000) * t ^ 22 + (-1035408958889 / 900000000) * t ^ 24 + (48347496209 / 1012500000) * t ^ 26 + (-32299383193 / 4050000000) * t ^ 32 + (3882648 / 25) * c * t ^ 2 + (-318806576 / 1125) * c * t ^ 4 + (76323709 / 6250) * c * t ^ 6 + (163112508121 / 937500) * c * t ^ 8 + (-4070695858723 / 135000000) * c * t ^ 10 + (-1146319082509 / 45000000) * c * t ^ 12 + (-371086536691 / 810000000) * c * t ^ 14 + (-1486265044717 / 810000000) * c * t ^ 16 + (-28291232333 / 202500000) * c * t ^ 18 + (14249925317 / 303750000) * c * t ^ 20 + (-11610013537 / 150000000) * c * t ^ 22 + (2108415343 / 4050000000) * c * t ^ 24 + (-2252026277 / 506250000) * c * t ^ 26 + (421450681 / 3037500000) * c * t ^ 32 + (1294216 / 25) * c ^ 2 * t ^ 2 + (-189869056 / 1125) * c ^ 2 * t ^ 4 + (17631096772 / 84375) * c ^ 2 * t ^ 6 + (-790942907486 / 6328125) * c ^ 2 * t ^ 8 + (680354351267 / 16875000) * c ^ 2 * t ^ 10 + (-4611056231 / 562500) * c ^ 2 * t ^ 12 + (8280003343 / 6750000) * c ^ 2 * t ^ 14 + (-1621530697 / 5062500) * c ^ 2 * t ^ 16 + (484748371 / 33750000) * c ^ 2 * t ^ 18 + (-499578853 / 25312500) * c ^ 2 * t ^ 20 + (2552398429 / 168750000) * c ^ 2 * t ^ 22 + (9897007 / 379687500) * c ^ 2 * t ^ 24 + (1423251397 / 4556250000) * c ^ 2 * t ^ 26 + (85264 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((-5176864 / 25) * t ^ 2 + (84836324 / 125) * t ^ 4 + (-23817871402 / 28125) * t ^ 6 + (17245594653397 / 33750000) * t ^ 8 + (-206126168457 / 1250000) * t ^ 10 + (2267238532231 / 67500000) * t ^ 12 + (-28498054261 / 4500000) * t ^ 14 + (33459071893 / 16875000) * t ^ 16 + (-1141108447 / 8437500) * t ^ 18 + (6369875843 / 67500000) * t ^ 20 + (-18630033451 / 337500000) * t ^ 22 + (-36470863 / 126562500) * t ^ 24 + (-897959767 / 379687500) * t ^ 26 + (-341056 / 94921875) * t ^ 32) * c_sq
#print axioms v51_00
#print axioms v51_11
#print axioms v51_22
#print axioms v51_33
#print axioms v51_44
end PhotonCertA
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z52 : Fin 52 → ℂ := Fin.snoc z51 (r ^ 3 * thetaMinus)
theorem v52_00 (t : ℂ) : (momentPoly 52 z52 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00]
  try simp only [phase48_00]
  try simp only [star_one, star_neg]
  ring
theorem v52_01 (t : ℂ) : (momentPoly 52 z52 0 1).eval t = (1 * t + (1 / 3) * alpha * t) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01]
  try simp only [phase48_00, phase48_01]
  try simp only [star_one, star_neg]
  ring
theorem v52_02 (t : ℂ) : (momentPoly 52 z52 0 2).eval t = ((1177 / 120) * t ^ 2 + (-1097 / 120) * t ^ 4 + (1319 / 120) * alpha * t ^ 2 + (-413 / 40) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02]
  try simp only [phase48_00, phase48_01, phase48_02]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 50) * t ^ 2 + (-4 / 225) * c * t ^ 2 + (-1 / 450) * c ^ 2 * t ^ 2) * alpha_sq + ((1 / 225) * t ^ 2 + (1 / 225) * alpha * t ^ 2) * c_sq
theorem v52_03 (t : ℂ) : (momentPoly 52 z52 0 3).eval t = ((-71 / 20) * t ^ 3 + (71 / 20) * t ^ 5 + (11123 / 300) * alpha * t ^ 3 + (-10267 / 300) * alpha * t ^ 5 + (-442 / 225) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_03]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03]
  try simp only [star_one, star_neg]
  linear_combination ((1977 / 2000) * t ^ 3 + (-8531 / 6000) * t ^ 5 + (-17729 / 18000) * c * t ^ 3 + (16769 / 18000) * c * t ^ 5 + (-4 / 1125) * c ^ 2 * t ^ 3 + (-1 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((16 / 1125) * alpha * t ^ 3 + (4 / 1125) * alpha * t ^ 5) * c_sq
theorem v52_04 (t : ℂ) : (momentPoly 52 z52 0 4).eval t = ((-17585383 / 24000) * t ^ 4 + (5536781 / 4000) * t ^ 6 + (-32854993 / 48000) * t ^ 8 + (1447427 / 36000) * t ^ 10 + (-1164547 / 144000) * t ^ 16 + (4564147 / 8000) * alpha * t ^ 4 + (-12831001 / 12000) * alpha * t ^ 6 + (8590437 / 16000) * alpha * t ^ 8 + (-1695229 / 36000) * alpha * t ^ 10 + (470783 / 48000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_03, v51_04]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04]
  try simp only [star_one, star_neg]
  linear_combination ((90251 / 22500) * t ^ 4 + (-1475551 / 45000) * t ^ 6 + (430919 / 15000) * t ^ 8 + (-884 / 1875) * t ^ 10 + (-15101 / 3750) * c * t ^ 4 + (80419 / 22500) * c * t ^ 6 + (5611 / 22500) * c * t ^ 8 + (3536 / 16875) * c * t ^ 10 + (71 / 4500) * c ^ 2 * t ^ 4 + (-1129 / 67500) * c ^ 2 * t ^ 6 + (-2 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-1037 / 1875) * t ^ 4 + (973 / 1875) * t ^ 6 + (-4 / 5625) * t ^ 8 + (284 / 16875) * t ^ 10 + (2756 / 5625) * alpha * t ^ 4 + (-2564 / 5625) * alpha * t ^ 6 + (4 / 5625) * alpha * t ^ 8 + (-284 / 16875) * alpha * t ^ 10) * c_sq
theorem v52_10 (t : ℂ) : (momentPoly 52 z52 1 0).eval t = (1 * t + (-1 / 3) * alpha * t) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_10]
  try simp only [phase48_00, phase48_10]
  try simp only [star_one, star_neg]
  ring
theorem v52_11 (t : ℂ) : (momentPoly 52 z52 1 1).eval t = (52 + (-152 / 3) * t ^ 2) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_10, v51_11]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 50) * t ^ 2 + (4 / 225) * c * t ^ 2 + (1 / 450) * c ^ 2 * t ^ 2) * alpha_sq + ((-2 / 225) * t ^ 2) * c_sq
theorem v52_12 (t : ℂ) : (momentPoly 52 z52 1 2).eval t = (103 * t + (-406 / 5) * t ^ 3 + (-307 / 15) * t ^ 5 + (103 / 3) * alpha * t + (-473 / 18) * alpha * t ^ 3 + (-137 / 18) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_10, v51_11, v51_12]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12]
  try simp only [star_one, star_neg]
  linear_combination ((-659 / 2000) * t ^ 3 + (8531 / 18000) * t ^ 5 + (17729 / 54000) * c * t ^ 3 + (-16769 / 54000) * c * t ^ 5 + (4 / 3375) * c ^ 2 * t ^ 3 + (1 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((-8 / 1125) * t ^ 3 + (-2 / 1125) * t ^ 5 + (-8 / 3375) * alpha * t ^ 3 + (-2 / 3375) * alpha * t ^ 5) * c_sq
theorem v52_13 (t : ℂ) : (momentPoly 52 z52 1 3).eval t = ((60027 / 40) * t ^ 2 + (-142277 / 50) * t ^ 4 + (401573 / 300) * t ^ 6 + (12919 / 1800) * t ^ 10 + (67269 / 40) * alpha * t ^ 2 + (-160027 / 50) * alpha * t ^ 4 + (453403 / 300) * alpha * t ^ 6 + (15049 / 1800) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_03, v51_10, v51_11, v51_12, v51_13]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13]
  try simp only [star_one, star_neg]
  linear_combination ((153 / 50) * t ^ 2 + (-99647 / 30000) * t ^ 4 + (9967 / 30000) * t ^ 6 + (221 / 1875) * t ^ 10 + (-68 / 25) * c * t ^ 2 + (33037 / 11250) * c * t ^ 4 + (-1039 / 3750) * c * t ^ 6 + (-884 / 16875) * c * t ^ 10 + (-17 / 50) * c ^ 2 * t ^ 2 + (6929 / 18000) * c ^ 2 * t ^ 4 + (-331 / 6000) * c ^ 2 * t ^ 6) * alpha_sq + ((17 / 25) * t ^ 2 + (-19901 / 22500) * t ^ 4 + (4901 / 22500) * t ^ 6 + (71 / 16875) * t ^ 10 + (17 / 25) * alpha * t ^ 2 + (-20611 / 22500) * alpha * t ^ 4 + (5611 / 22500) * alpha * t ^ 6 + (71 / 16875) * alpha * t ^ 10) * c_sq
theorem v52_14 (t : ℂ) : (momentPoly 52 z52 1 4).eval t = ((-7171 / 10) * t ^ 3 + (15065129 / 12000) * t ^ 5 + (-2242529 / 6000) * t ^ 7 + (-3712241 / 24000) * t ^ 9 + (-209101 / 18000) * t ^ 11 + (123901 / 72000) * t ^ 17 + (1123423 / 150) * alpha * t ^ 3 + (-482796407 / 36000) * alpha * t ^ 5 + (30549349 / 6000) * alpha * t ^ 7 + (10339141 / 24000) * alpha * t ^ 9 + (20837843 / 54000) * alpha * t ^ 11 + (3125117 / 216000) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_03, v51_04, v51_10, v51_11, v51_12, v51_13, v51_14]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14]
  try simp only [star_one, star_neg]
  linear_combination ((199677 / 1000) * t ^ 3 + (-1764935213 / 3600000) * t ^ 5 + (56658469 / 200000) * t ^ 7 + (20633941 / 7200000) * t ^ 9 + (13150721 / 5400000) * t ^ 11 + (-9638641 / 21600000) * t ^ 17 + (-1790629 / 9000) * c * t ^ 3 + (4212344071 / 10800000) * c * t ^ 5 + (-1100669047 / 5400000) * c * t ^ 7 + (104550251 / 7200000) * c * t ^ 9 + (-39524867 / 16200000) * c * t ^ 11 + (19402067 / 64800000) * c * t ^ 17 + (-808 / 1125) * c ^ 2 * t ^ 3 + (31106 / 84375) * c ^ 2 * t ^ 5 + (54197 / 168750) * c ^ 2 * t ^ 7 + (323 / 168750) * c ^ 2 * t ^ 9 + (1136 / 253125) * c ^ 2 * t ^ 11 + (146 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((284 / 5625) * t ^ 5 + (-71 / 1875) * t ^ 7 + (-71 / 5625) * t ^ 9 + (3232 / 1125) * alpha * t ^ 3 + (-207556 / 84375) * alpha * t ^ 5 + (-14477 / 28125) * alpha * t ^ 7 + (10931 / 84375) * alpha * t ^ 9 + (14144 / 253125) * alpha * t ^ 11 + (584 / 253125) * alpha * t ^ 17) * c_sq
theorem v52_20 (t : ℂ) : (momentPoly 52 z52 2 0).eval t = ((1177 / 120) * t ^ 2 + (-1097 / 120) * t ^ 4 + (-1319 / 120) * alpha * t ^ 2 + (413 / 40) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_10, v51_20]
  try simp only [phase48_00, phase48_10, phase48_20]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 50) * t ^ 2 + (-4 / 225) * c * t ^ 2 + (-1 / 450) * c ^ 2 * t ^ 2) * alpha_sq + ((1 / 225) * t ^ 2 + (-1 / 225) * alpha * t ^ 2) * c_sq
theorem v52_21 (t : ℂ) : (momentPoly 52 z52 2 1).eval t = (103 * t + (-406 / 5) * t ^ 3 + (-307 / 15) * t ^ 5 + (-103 / 3) * alpha * t + (473 / 18) * alpha * t ^ 3 + (137 / 18) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_10, v51_11, v51_20, v51_21]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21]
  try simp only [star_one, star_neg]
  linear_combination ((-659 / 2000) * t ^ 3 + (8531 / 18000) * t ^ 5 + (17729 / 54000) * c * t ^ 3 + (-16769 / 54000) * c * t ^ 5 + (4 / 3375) * c ^ 2 * t ^ 3 + (1 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((-8 / 1125) * t ^ 3 + (-2 / 1125) * t ^ 5 + (8 / 3375) * alpha * t ^ 3 + (2 / 3375) * alpha * t ^ 5) * c_sq
theorem v52_22 (t : ℂ) : (momentPoly 52 z52 2 2).eval t = (5356 + (-10336) * t ^ 2 + (19036753 / 3600) * t ^ 4 + (-1183673 / 1800) * t ^ 6 + (1264993 / 3600) * t ^ 8) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_10, v51_11, v51_12, v51_20, v51_21, v51_22]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22]
  try simp only [star_one, star_neg]
  linear_combination ((-102 / 25) * t ^ 2 + (20869 / 6750) * t ^ 4 + (1415749 / 135000) * t ^ 6 + (-430919 / 45000) * t ^ 8 + (272 / 75) * c * t ^ 2 + (-17369 / 6750) * c * t ^ 4 + (-55483 / 67500) * c * t ^ 6 + (-5611 / 67500) * c * t ^ 8 + (34 / 75) * c ^ 2 * t ^ 2 + (-14 / 27) * c ^ 2 * t ^ 4 + (4006 / 50625) * c ^ 2 * t ^ 6 + (2 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((-136 / 75) * t ^ 2 + (14071 / 6750) * t ^ 4 + (-11123 / 33750) * t ^ 6 + (-8 / 16875) * t ^ 8) * c_sq
theorem v52_23 (t : ℂ) : (momentPoly 52 z52 2 3).eval t = (15760 * t + (-123018 / 5) * t ^ 3 + (21109501 / 6000) * t ^ 5 + (522613 / 120) * t ^ 7 + (5616089 / 6000) * t ^ 9 + (-107299 / 4500) * t ^ 11 + (89773 / 1500) * t ^ 13 + (15760 / 3) * alpha * t + (-47773 / 6) * alpha * t ^ 3 + (1413917 / 2000) * alpha * t ^ 5 + (3001577 / 1800) * alpha * t ^ 7 + (5784217 / 18000) * alpha * t ^ 9 + (-54617 / 13500) * alpha * t ^ 11 + (237937 / 13500) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_03, v51_10, v51_11, v51_12, v51_13, v51_20, v51_21, v51_22, v51_23]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23]
  try simp only [star_one, star_neg]
  linear_combination ((-199677 / 2000) * t ^ 3 + (21386479 / 90000) * t ^ 5 + (-50384207 / 450000) * t ^ 7 + (-10713553 / 450000) * t ^ 9 + (480323 / 337500) * t ^ 11 + (-1885351 / 675000) * t ^ 13 + (1790629 / 18000) * c * t ^ 3 + (-50611189 / 270000) * c * t ^ 5 + (13034753 / 150000) * c * t ^ 7 + (949303 / 1350000) * c * t ^ 9 + (1059659 / 2025000) * c * t ^ 11 + (-1768 / 253125) * c * t ^ 13 + (404 / 1125) * c ^ 2 * t ^ 3 + (-467 / 1875) * c ^ 2 * t ^ 5 + (-14863 / 135000) * c ^ 2 * t ^ 7 + (227 / 27000) * c ^ 2 * t ^ 9 + (8 / 3375) * c ^ 2 * t ^ 11) * alpha_sq + ((-808 / 375) * t ^ 3 + (8548 / 5625) * t ^ 5 + (11053 / 18750) * t ^ 7 + (-419 / 56250) * t ^ 9 + (-632 / 84375) * t ^ 11 + (142 / 84375) * t ^ 13 + (-808 / 1125) * alpha * t ^ 3 + (532 / 1125) * alpha * t ^ 5 + (12473 / 56250) * alpha * t ^ 7 + (1001 / 168750) * alpha * t ^ 9 + (-632 / 253125) * alpha * t ^ 11 + (142 / 253125) * alpha * t ^ 13) * c_sq
theorem v52_24 (t : ℂ) : (momentPoly 52 z52 2 4).eval t = ((3638107 / 12) * t ^ 2 + (-6890885 / 8) * t ^ 4 + (1172659685423 / 1440000) * t ^ 6 + (-383628727469 / 1440000) * t ^ 8 + (2380137293 / 115200) * t ^ 10 + (-98884563047 / 8640000) * t ^ 12 + (2209914187 / 2160000) * t ^ 14 + (1984974187 / 8640000) * t ^ 18 + (-1907112587 / 8640000) * t ^ 20 + (4077029 / 12) * alpha * t ^ 2 + (-7740187 / 8) * alpha * t ^ 4 + (440395410139 / 480000) * alpha * t ^ 6 + (-435465774451 / 1440000) * alpha * t ^ 8 + (4760911637 / 192000) * alpha * t ^ 10 + (-111297496633 / 8640000) * alpha * t ^ 12 + (1659310933 / 2160000) * alpha * t ^ 14 + (1454715733 / 8640000) * alpha * t ^ 18 + (-156322477 / 960000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_03, v51_04, v51_10, v51_11, v51_12, v51_13, v51_14, v51_20, v51_21, v51_22, v51_23, v51_24]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24]
  try simp only [star_one, star_neg]
  linear_combination ((3091 / 5) * t ^ 2 + (-99647 / 75) * t ^ 4 + (4421966707 / 5400000) * t ^ 6 + (2146388689 / 18000000) * t ^ 8 + (-7226773171 / 18000000) * t ^ 10 + (62824165283 / 324000000) * t ^ 12 + (-1905107419 / 81000000) * t ^ 14 + (-848483777 / 162000000) * t ^ 18 + (967349993 / 108000000) * t ^ 20 + (-24728 / 45) * c * t ^ 2 + (264296 / 225) * c * t ^ 4 + (-1917080147 / 2700000) * c * t ^ 6 + (395016037 / 5400000) * c * t ^ 8 + (-55223111 / 5400000) * c * t ^ 10 + (9478319 / 432000) * c * t ^ 12 + (-1347893 / 900000) * c * t ^ 14 + (959759 / 1080000) * c * t ^ 18 + (-89197 / 2160000) * c * t ^ 20 + (-3091 / 45) * c ^ 2 * t ^ 2 + (6929 / 45) * c ^ 2 * t ^ 4 + (-195935471 / 1800000) * c ^ 2 * t ^ 6 + (1084050659 / 40500000) * c ^ 2 * t ^ 8 + (-61061521 / 18000000) * c ^ 2 * t ^ 10 + (9023401 / 40500000) * c ^ 2 * t ^ 12 + (-1218887 / 15187500) * c ^ 2 * t ^ 14 + (-1709011 / 486000000) * c ^ 2 * t ^ 18 + (292 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((6182 / 45) * t ^ 2 + (-79604 / 225) * t ^ 4 + (416122339 / 1350000) * t ^ 6 + (-343552783 / 3375000) * t ^ 8 + (168675983 / 13500000) * t ^ 10 + (-29138321 / 10125000) * t ^ 12 + (442274 / 1265625) * t ^ 14 + (3668017 / 40500000) * t ^ 18 + (584 / 1265625) * t ^ 20 + (6182 / 45) * alpha * t ^ 2 + (-82444 / 225) * alpha * t ^ 4 + (225541621 / 675000) * alpha * t ^ 6 + (-196255609 / 1687500) * alpha * t ^ 8 + (46437257 / 3375000) * alpha * t ^ 10 + (-3614552 / 1265625) * alpha * t ^ 12 + (391864 / 1265625) * alpha * t ^ 14 + (95266 / 1265625) * alpha * t ^ 18 + (584 / 1265625) * alpha * t ^ 20) * c_sq
theorem v52_30 (t : ℂ) : (momentPoly 52 z52 3 0).eval t = ((-71 / 20) * t ^ 3 + (71 / 20) * t ^ 5 + (-11123 / 300) * alpha * t ^ 3 + (10267 / 300) * alpha * t ^ 5 + (442 / 225) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_10, v51_20, v51_30]
  try simp only [phase48_00, phase48_10, phase48_20, phase48_30]
  try simp only [star_one, star_neg]
  linear_combination ((1977 / 2000) * t ^ 3 + (-8531 / 6000) * t ^ 5 + (-17729 / 18000) * c * t ^ 3 + (16769 / 18000) * c * t ^ 5 + (-4 / 1125) * c ^ 2 * t ^ 3 + (-1 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-16 / 1125) * alpha * t ^ 3 + (-4 / 1125) * alpha * t ^ 5) * c_sq
theorem v52_31 (t : ℂ) : (momentPoly 52 z52 3 1).eval t = ((60027 / 40) * t ^ 2 + (-142277 / 50) * t ^ 4 + (401573 / 300) * t ^ 6 + (12919 / 1800) * t ^ 10 + (-67269 / 40) * alpha * t ^ 2 + (160027 / 50) * alpha * t ^ 4 + (-453403 / 300) * alpha * t ^ 6 + (-15049 / 1800) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_10, v51_11, v51_20, v51_21, v51_30, v51_31]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21, phase48_30, phase48_31]
  try simp only [star_one, star_neg]
  linear_combination ((153 / 50) * t ^ 2 + (-99647 / 30000) * t ^ 4 + (9967 / 30000) * t ^ 6 + (221 / 1875) * t ^ 10 + (-68 / 25) * c * t ^ 2 + (33037 / 11250) * c * t ^ 4 + (-1039 / 3750) * c * t ^ 6 + (-884 / 16875) * c * t ^ 10 + (-17 / 50) * c ^ 2 * t ^ 2 + (6929 / 18000) * c ^ 2 * t ^ 4 + (-331 / 6000) * c ^ 2 * t ^ 6) * alpha_sq + ((17 / 25) * t ^ 2 + (-19901 / 22500) * t ^ 4 + (4901 / 22500) * t ^ 6 + (71 / 16875) * t ^ 10 + (-17 / 25) * alpha * t ^ 2 + (20611 / 22500) * alpha * t ^ 4 + (-5611 / 22500) * alpha * t ^ 6 + (-71 / 16875) * alpha * t ^ 10) * c_sq
theorem v52_32 (t : ℂ) : (momentPoly 52 z52 3 2).eval t = (15760 * t + (-123018 / 5) * t ^ 3 + (21109501 / 6000) * t ^ 5 + (522613 / 120) * t ^ 7 + (5616089 / 6000) * t ^ 9 + (-107299 / 4500) * t ^ 11 + (89773 / 1500) * t ^ 13 + (-15760 / 3) * alpha * t + (47773 / 6) * alpha * t ^ 3 + (-1413917 / 2000) * alpha * t ^ 5 + (-3001577 / 1800) * alpha * t ^ 7 + (-5784217 / 18000) * alpha * t ^ 9 + (54617 / 13500) * alpha * t ^ 11 + (-237937 / 13500) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_10, v51_11, v51_12, v51_20, v51_21, v51_22, v51_30, v51_31, v51_32]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22, phase48_30, phase48_31, phase48_32]
  try simp only [star_one, star_neg]
  linear_combination ((-199677 / 2000) * t ^ 3 + (21386479 / 90000) * t ^ 5 + (-50384207 / 450000) * t ^ 7 + (-10713553 / 450000) * t ^ 9 + (480323 / 337500) * t ^ 11 + (-1885351 / 675000) * t ^ 13 + (1790629 / 18000) * c * t ^ 3 + (-50611189 / 270000) * c * t ^ 5 + (13034753 / 150000) * c * t ^ 7 + (949303 / 1350000) * c * t ^ 9 + (1059659 / 2025000) * c * t ^ 11 + (-1768 / 253125) * c * t ^ 13 + (404 / 1125) * c ^ 2 * t ^ 3 + (-467 / 1875) * c ^ 2 * t ^ 5 + (-14863 / 135000) * c ^ 2 * t ^ 7 + (227 / 27000) * c ^ 2 * t ^ 9 + (8 / 3375) * c ^ 2 * t ^ 11) * alpha_sq + ((-808 / 375) * t ^ 3 + (8548 / 5625) * t ^ 5 + (11053 / 18750) * t ^ 7 + (-419 / 56250) * t ^ 9 + (-632 / 84375) * t ^ 11 + (142 / 84375) * t ^ 13 + (808 / 1125) * alpha * t ^ 3 + (-532 / 1125) * alpha * t ^ 5 + (-12473 / 56250) * alpha * t ^ 7 + (-1001 / 168750) * alpha * t ^ 9 + (632 / 253125) * alpha * t ^ 11 + (-142 / 253125) * alpha * t ^ 13) * c_sq
theorem v52_33 (t : ℂ) : (momentPoly 52 z52 3 3).eval t = (819520 + (-2349160) * t ^ 2 + (19036753 / 8) * t ^ 4 + (-5696823791 / 5000) * t ^ 6 + (822393823 / 1875) * t ^ 8 + (-1119685859 / 7500) * t ^ 10 + (69110011 / 45000) * t ^ 12 + (-63042419 / 45000) * t ^ 14 + (-682136 / 16875) * t ^ 18) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_03, v51_10, v51_11, v51_12, v51_13, v51_20, v51_21, v51_22, v51_23, v51_30, v51_31, v51_32, v51_33]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23, phase48_30, phase48_31, phase48_32, phase48_33]
  try simp only [star_one, star_neg]
  linear_combination ((-9273 / 10) * t ^ 2 + (20869 / 15) * t ^ 4 + (423178799 / 100000) * t ^ 6 + (-1309121449 / 150000) * t ^ 8 + (3610027499 / 900000) * t ^ 10 + (13949089 / 1125000) * t ^ 12 + (2295529 / 281250) * t ^ 14 + (-97682 / 140625) * t ^ 18 + (12364 / 15) * c * t ^ 2 + (-17369 / 15) * c * t ^ 4 + (388409 / 28125) * c * t ^ 6 + (2672147 / 11250) * c * t ^ 8 + (9043349 / 112500) * c * t ^ 10 + (-102143 / 337500) * c * t ^ 12 + (543967 / 168750) * c * t ^ 14 + (3091 / 30) * c ^ 2 * t ^ 2 + (-700 / 3) * c ^ 2 * t ^ 4 + (455004103 / 2700000) * c ^ 2 * t ^ 6 + (-19564493 / 450000) * c ^ 2 * t ^ 8 + (14949031 / 2700000) * c ^ 2 * t ^ 10 + (-72787 / 225000) * c ^ 2 * t ^ 12 + (5543 / 45000) * c ^ 2 * t ^ 14) * alpha_sq + ((-6182 / 15) * t ^ 2 + (14071 / 15) * t ^ 4 + (-30800413 / 45000) * t ^ 6 + (20174861 / 112500) * t ^ 8 + (-4945997 / 225000) * t ^ 10 + (754891 / 421875) * t ^ 12 + (-790757 / 843750) * t ^ 14 + (-10082 / 1265625) * t ^ 18) * c_sq
theorem v52_34 (t : ℂ) : (momentPoly 52 z52 3 4).eval t = (3184135 * t + (-36912708 / 5) * t ^ 3 + (3912376799 / 1000) * t ^ 5 + (52100600971 / 50000) * t ^ 7 + (-83949434411 / 300000) * t ^ 9 + (-133578058219 / 300000) * t ^ 11 + (1107930959 / 360000) * t ^ 13 + (-1728962411 / 56250) * t ^ 15 + (-608268859 / 200000) * t ^ 17 + (2768321089 / 2700000) * t ^ 19 + (-2076912971 / 1800000) * t ^ 21 + (-105843043 / 1800000) * t ^ 25 + (3184135 / 3) * alpha * t + (-2389123) * alpha * t ^ 3 + (3293085547 / 3000) * alpha * t ^ 5 + (971525318161 / 1800000) * alpha * t ^ 7 + (-267695231561 / 1800000) * alpha * t ^ 9 + (-527984219053 / 3600000) * alpha * t ^ 11 + (-8911680119 / 2160000) * alpha * t ^ 13 + (-23783919463 / 2700000) * alpha * t ^ 15 + (-7014353453 / 5400000) * alpha * t ^ 17 + (7051726583 / 32400000) * alpha * t ^ 19 + (-2937511891 / 10800000) * alpha * t ^ 21 + (-262764887 / 16200000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_03, v51_04, v51_10, v51_11, v51_12, v51_13, v51_14, v51_20, v51_21, v51_22, v51_23, v51_24, v51_30, v51_31, v51_32, v51_33, v51_34]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24, phase48_30, phase48_31, phase48_32, phase48_33, phase48_34]
  try simp only [star_one, star_neg]
  linear_combination ((-29957481 / 1000) * t ^ 3 + (2968394477 / 30000) * t ^ 5 + (-740386146509 / 8000000) * t ^ 7 + (175635389767 / 14400000) * t ^ 9 + (1405850126729 / 144000000) * t ^ 11 + (26326664957 / 240000000) * t ^ 13 + (720942251527 / 540000000) * t ^ 15 + (37383252079 / 270000000) * t ^ 17 + (-192353712583 / 6480000000) * t ^ 19 + (98636400337 / 2160000000) * t ^ 21 + (2130139661 / 810000000) * t ^ 25 + (89549179 / 3000) * c * t ^ 3 + (-7532244287 / 90000) * c * t ^ 5 + (16732098545183 / 216000000) * c * t ^ 7 + (-1036762854749 / 43200000) * c * t ^ 9 + (188559827287 / 144000000) * c * t ^ 11 + (-2150369208109 / 2160000000) * c * t ^ 13 + (101539220827 / 1620000000) * c * t ^ 15 + (38595203 / 16875000) * c * t ^ 17 + (283700570357 / 19440000000) * c * t ^ 19 + (-96396717883 / 6480000000) * c * t ^ 21 + (-258128 / 18984375) * c * t ^ 25 + (40408 / 375) * c ^ 2 * t ^ 3 + (-980609 / 5625) * c ^ 2 * t ^ 5 + (273881 / 9375) * c ^ 2 * t ^ 7 + (219159113 / 5400000) * c ^ 2 * t ^ 9 + (-8785397 / 2700000) * c ^ 2 * t ^ 11 + (-20337917 / 54000000) * c ^ 2 * t ^ 13 + (22163423 / 40500000) * c ^ 2 * t ^ 15 + (16501 / 1012500) * c ^ 2 * t ^ 17 + (-1001831 / 10125000) * c ^ 2 * t ^ 19 + (31597 / 3600000) * c ^ 2 * t ^ 21) * alpha_sq + ((-80816 / 125) * t ^ 3 + (1989334 / 1875) * t ^ 5 + (-42925757 / 187500) * t ^ 7 + (-406064947 / 2250000) * t ^ 9 + (-17227 / 4500) * t ^ 11 + (24687569 / 7500000) * t ^ 13 + (-9692569 / 1875000) * t ^ 15 + (-380248 / 2109375) * t ^ 17 + (31423451 / 50625000) * t ^ 19 + (-6540271 / 67500000) * t ^ 21 + (-20732 / 6328125) * t ^ 25 + (-80816 / 375) * alpha * t ^ 3 + (375374 / 1125) * alpha * t ^ 5 + (-69082873 / 1687500) * alpha * t ^ 7 + (-479082709 / 6750000) * alpha * t ^ 9 + (-10541173 / 1687500) * alpha * t ^ 11 + (265339511 / 202500000) * alpha * t ^ 13 + (-75457711 / 50625000) * alpha * t ^ 15 + (-430658 / 6328125) * alpha * t ^ 17 + (26462501 / 151875000) * alpha * t ^ 19 + (-6120721 / 202500000) * alpha * t ^ 21 + (-20732 / 18984375) * alpha * t ^ 25) * c_sq
theorem v52_40 (t : ℂ) : (momentPoly 52 z52 4 0).eval t = ((-17585383 / 24000) * t ^ 4 + (5536781 / 4000) * t ^ 6 + (-32854993 / 48000) * t ^ 8 + (1447427 / 36000) * t ^ 10 + (-1164547 / 144000) * t ^ 16 + (-4564147 / 8000) * alpha * t ^ 4 + (12831001 / 12000) * alpha * t ^ 6 + (-8590437 / 16000) * alpha * t ^ 8 + (1695229 / 36000) * alpha * t ^ 10 + (-470783 / 48000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_10, v51_20, v51_30, v51_40]
  try simp only [phase48_00, phase48_10, phase48_20, phase48_30, phase48_40]
  try simp only [star_one, star_neg]
  linear_combination ((90251 / 22500) * t ^ 4 + (-1475551 / 45000) * t ^ 6 + (430919 / 15000) * t ^ 8 + (-884 / 1875) * t ^ 10 + (-15101 / 3750) * c * t ^ 4 + (80419 / 22500) * c * t ^ 6 + (5611 / 22500) * c * t ^ 8 + (3536 / 16875) * c * t ^ 10 + (71 / 4500) * c ^ 2 * t ^ 4 + (-1129 / 67500) * c ^ 2 * t ^ 6 + (-2 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-1037 / 1875) * t ^ 4 + (973 / 1875) * t ^ 6 + (-4 / 5625) * t ^ 8 + (284 / 16875) * t ^ 10 + (-2756 / 5625) * alpha * t ^ 4 + (2564 / 5625) * alpha * t ^ 6 + (-4 / 5625) * alpha * t ^ 8 + (284 / 16875) * alpha * t ^ 10) * c_sq
theorem v52_41 (t : ℂ) : (momentPoly 52 z52 4 1).eval t = ((-7171 / 10) * t ^ 3 + (15065129 / 12000) * t ^ 5 + (-2242529 / 6000) * t ^ 7 + (-3712241 / 24000) * t ^ 9 + (-209101 / 18000) * t ^ 11 + (123901 / 72000) * t ^ 17 + (-1123423 / 150) * alpha * t ^ 3 + (482796407 / 36000) * alpha * t ^ 5 + (-30549349 / 6000) * alpha * t ^ 7 + (-10339141 / 24000) * alpha * t ^ 9 + (-20837843 / 54000) * alpha * t ^ 11 + (-3125117 / 216000) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_10, v51_11, v51_20, v51_21, v51_30, v51_31, v51_40, v51_41]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21, phase48_30, phase48_31, phase48_40, phase48_41]
  try simp only [star_one, star_neg]
  linear_combination ((199677 / 1000) * t ^ 3 + (-1764935213 / 3600000) * t ^ 5 + (56658469 / 200000) * t ^ 7 + (20633941 / 7200000) * t ^ 9 + (13150721 / 5400000) * t ^ 11 + (-9638641 / 21600000) * t ^ 17 + (-1790629 / 9000) * c * t ^ 3 + (4212344071 / 10800000) * c * t ^ 5 + (-1100669047 / 5400000) * c * t ^ 7 + (104550251 / 7200000) * c * t ^ 9 + (-39524867 / 16200000) * c * t ^ 11 + (19402067 / 64800000) * c * t ^ 17 + (-808 / 1125) * c ^ 2 * t ^ 3 + (31106 / 84375) * c ^ 2 * t ^ 5 + (54197 / 168750) * c ^ 2 * t ^ 7 + (323 / 168750) * c ^ 2 * t ^ 9 + (1136 / 253125) * c ^ 2 * t ^ 11 + (146 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((284 / 5625) * t ^ 5 + (-71 / 1875) * t ^ 7 + (-71 / 5625) * t ^ 9 + (-3232 / 1125) * alpha * t ^ 3 + (207556 / 84375) * alpha * t ^ 5 + (14477 / 28125) * alpha * t ^ 7 + (-10931 / 84375) * alpha * t ^ 9 + (-14144 / 253125) * alpha * t ^ 11 + (-584 / 253125) * alpha * t ^ 17) * c_sq
theorem v52_42 (t : ℂ) : (momentPoly 52 z52 4 2).eval t = ((3638107 / 12) * t ^ 2 + (-6890885 / 8) * t ^ 4 + (1172659685423 / 1440000) * t ^ 6 + (-383628727469 / 1440000) * t ^ 8 + (2380137293 / 115200) * t ^ 10 + (-98884563047 / 8640000) * t ^ 12 + (2209914187 / 2160000) * t ^ 14 + (1984974187 / 8640000) * t ^ 18 + (-1907112587 / 8640000) * t ^ 20 + (-4077029 / 12) * alpha * t ^ 2 + (7740187 / 8) * alpha * t ^ 4 + (-440395410139 / 480000) * alpha * t ^ 6 + (435465774451 / 1440000) * alpha * t ^ 8 + (-4760911637 / 192000) * alpha * t ^ 10 + (111297496633 / 8640000) * alpha * t ^ 12 + (-1659310933 / 2160000) * alpha * t ^ 14 + (-1454715733 / 8640000) * alpha * t ^ 18 + (156322477 / 960000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_10, v51_11, v51_12, v51_20, v51_21, v51_22, v51_30, v51_31, v51_32, v51_40, v51_41, v51_42]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22, phase48_30, phase48_31, phase48_32, phase48_40, phase48_41, phase48_42]
  try simp only [star_one, star_neg]
  linear_combination ((3091 / 5) * t ^ 2 + (-99647 / 75) * t ^ 4 + (4421966707 / 5400000) * t ^ 6 + (2146388689 / 18000000) * t ^ 8 + (-7226773171 / 18000000) * t ^ 10 + (62824165283 / 324000000) * t ^ 12 + (-1905107419 / 81000000) * t ^ 14 + (-848483777 / 162000000) * t ^ 18 + (967349993 / 108000000) * t ^ 20 + (-24728 / 45) * c * t ^ 2 + (264296 / 225) * c * t ^ 4 + (-1917080147 / 2700000) * c * t ^ 6 + (395016037 / 5400000) * c * t ^ 8 + (-55223111 / 5400000) * c * t ^ 10 + (9478319 / 432000) * c * t ^ 12 + (-1347893 / 900000) * c * t ^ 14 + (959759 / 1080000) * c * t ^ 18 + (-89197 / 2160000) * c * t ^ 20 + (-3091 / 45) * c ^ 2 * t ^ 2 + (6929 / 45) * c ^ 2 * t ^ 4 + (-195935471 / 1800000) * c ^ 2 * t ^ 6 + (1084050659 / 40500000) * c ^ 2 * t ^ 8 + (-61061521 / 18000000) * c ^ 2 * t ^ 10 + (9023401 / 40500000) * c ^ 2 * t ^ 12 + (-1218887 / 15187500) * c ^ 2 * t ^ 14 + (-1709011 / 486000000) * c ^ 2 * t ^ 18 + (292 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((6182 / 45) * t ^ 2 + (-79604 / 225) * t ^ 4 + (416122339 / 1350000) * t ^ 6 + (-343552783 / 3375000) * t ^ 8 + (168675983 / 13500000) * t ^ 10 + (-29138321 / 10125000) * t ^ 12 + (442274 / 1265625) * t ^ 14 + (3668017 / 40500000) * t ^ 18 + (584 / 1265625) * t ^ 20 + (-6182 / 45) * alpha * t ^ 2 + (82444 / 225) * alpha * t ^ 4 + (-225541621 / 675000) * alpha * t ^ 6 + (196255609 / 1687500) * alpha * t ^ 8 + (-46437257 / 3375000) * alpha * t ^ 10 + (3614552 / 1265625) * alpha * t ^ 12 + (-391864 / 1265625) * alpha * t ^ 14 + (-95266 / 1265625) * alpha * t ^ 18 + (-584 / 1265625) * alpha * t ^ 20) * c_sq
theorem v52_43 (t : ℂ) : (momentPoly 52 z52 4 3).eval t = (3184135 * t + (-36912708 / 5) * t ^ 3 + (3912376799 / 1000) * t ^ 5 + (52100600971 / 50000) * t ^ 7 + (-83949434411 / 300000) * t ^ 9 + (-133578058219 / 300000) * t ^ 11 + (1107930959 / 360000) * t ^ 13 + (-1728962411 / 56250) * t ^ 15 + (-608268859 / 200000) * t ^ 17 + (2768321089 / 2700000) * t ^ 19 + (-2076912971 / 1800000) * t ^ 21 + (-105843043 / 1800000) * t ^ 25 + (-3184135 / 3) * alpha * t + 2389123 * alpha * t ^ 3 + (-3293085547 / 3000) * alpha * t ^ 5 + (-971525318161 / 1800000) * alpha * t ^ 7 + (267695231561 / 1800000) * alpha * t ^ 9 + (527984219053 / 3600000) * alpha * t ^ 11 + (8911680119 / 2160000) * alpha * t ^ 13 + (23783919463 / 2700000) * alpha * t ^ 15 + (7014353453 / 5400000) * alpha * t ^ 17 + (-7051726583 / 32400000) * alpha * t ^ 19 + (2937511891 / 10800000) * alpha * t ^ 21 + (262764887 / 16200000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_03, v51_10, v51_11, v51_12, v51_13, v51_20, v51_21, v51_22, v51_23, v51_30, v51_31, v51_32, v51_33, v51_40, v51_41, v51_42, v51_43]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23, phase48_30, phase48_31, phase48_32, phase48_33, phase48_40, phase48_41, phase48_42, phase48_43]
  try simp only [star_one, star_neg]
  linear_combination ((-29957481 / 1000) * t ^ 3 + (2968394477 / 30000) * t ^ 5 + (-740386146509 / 8000000) * t ^ 7 + (175635389767 / 14400000) * t ^ 9 + (1405850126729 / 144000000) * t ^ 11 + (26326664957 / 240000000) * t ^ 13 + (720942251527 / 540000000) * t ^ 15 + (37383252079 / 270000000) * t ^ 17 + (-192353712583 / 6480000000) * t ^ 19 + (98636400337 / 2160000000) * t ^ 21 + (2130139661 / 810000000) * t ^ 25 + (89549179 / 3000) * c * t ^ 3 + (-7532244287 / 90000) * c * t ^ 5 + (16732098545183 / 216000000) * c * t ^ 7 + (-1036762854749 / 43200000) * c * t ^ 9 + (188559827287 / 144000000) * c * t ^ 11 + (-2150369208109 / 2160000000) * c * t ^ 13 + (101539220827 / 1620000000) * c * t ^ 15 + (38595203 / 16875000) * c * t ^ 17 + (283700570357 / 19440000000) * c * t ^ 19 + (-96396717883 / 6480000000) * c * t ^ 21 + (-258128 / 18984375) * c * t ^ 25 + (40408 / 375) * c ^ 2 * t ^ 3 + (-980609 / 5625) * c ^ 2 * t ^ 5 + (273881 / 9375) * c ^ 2 * t ^ 7 + (219159113 / 5400000) * c ^ 2 * t ^ 9 + (-8785397 / 2700000) * c ^ 2 * t ^ 11 + (-20337917 / 54000000) * c ^ 2 * t ^ 13 + (22163423 / 40500000) * c ^ 2 * t ^ 15 + (16501 / 1012500) * c ^ 2 * t ^ 17 + (-1001831 / 10125000) * c ^ 2 * t ^ 19 + (31597 / 3600000) * c ^ 2 * t ^ 21) * alpha_sq + ((-80816 / 125) * t ^ 3 + (1989334 / 1875) * t ^ 5 + (-42925757 / 187500) * t ^ 7 + (-406064947 / 2250000) * t ^ 9 + (-17227 / 4500) * t ^ 11 + (24687569 / 7500000) * t ^ 13 + (-9692569 / 1875000) * t ^ 15 + (-380248 / 2109375) * t ^ 17 + (31423451 / 50625000) * t ^ 19 + (-6540271 / 67500000) * t ^ 21 + (-20732 / 6328125) * t ^ 25 + (80816 / 375) * alpha * t ^ 3 + (-375374 / 1125) * alpha * t ^ 5 + (69082873 / 1687500) * alpha * t ^ 7 + (479082709 / 6750000) * alpha * t ^ 9 + (10541173 / 1687500) * alpha * t ^ 11 + (-265339511 / 202500000) * alpha * t ^ 13 + (75457711 / 50625000) * alpha * t ^ 15 + (430658 / 6328125) * alpha * t ^ 17 + (-26462501 / 151875000) * alpha * t ^ 19 + (6120721 / 202500000) * alpha * t ^ 21 + (20732 / 18984375) * alpha * t ^ 25) * c_sq
theorem v52_44 (t : ℂ) : (momentPoly 52 z52 4 4).eval t = (165575020 + (-1879944512 / 3) * t ^ 2 + (141385964531 / 150) * t ^ 4 + (-5838727364441 / 7500) * t ^ 6 + (66530143223285233 / 144000000) * t ^ 8 + (-7893559858939873 / 36000000) * t ^ 10 + (179921123800231 / 3200000) * t ^ 12 + (-278099538861301 / 72000000) * t ^ 14 + (1183500518407681 / 576000000) * t ^ 16 + (-5039423395163 / 24000000) * t ^ 18 + (103472586267523 / 1296000000) * t ^ 20 + (-1818290094013 / 24000000) * t ^ 22 + (33220680032947 / 864000000) * t ^ 24 + (-1744882250633 / 648000000) * t ^ 26 + (1565521702153 / 5184000000) * t ^ 32) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_03, v51_04, v51_10, v51_11, v51_12, v51_13, v51_14, v51_20, v51_21, v51_22, v51_23, v51_24, v51_30, v51_31, v51_32, v51_33, v51_34, v51_40, v51_41, v51_42, v51_43, v51_44]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24, phase48_30, phase48_31, phase48_32, phase48_33, phase48_34, phase48_40, phase48_41, phase48_42, phase48_43, phase48_44]
  try simp only [star_one, star_neg]
  linear_combination ((-6184028 / 25) * t ^ 2 + (619976252 / 1125) * t ^ 4 + (167344244903 / 112500) * t ^ 6 + (-12736402228187 / 2500000) * t ^ 8 + (1285072442919107 / 270000000) * t ^ 10 + (-80999109715423 / 54000000) * t ^ 12 + (6074208644899 / 64800000) * t ^ 14 + (-29687616136501 / 540000000) * t ^ 16 + (362784910741 / 81000000) * t ^ 18 + (65617683443 / 759375000) * t ^ 20 + (13672989829787 / 8100000000) * t ^ 22 + (-3474530682619 / 2700000000) * t ^ 24 + (5732558822 / 94921875) * t ^ 26 + (-33920572889 / 4050000000) * t ^ 32 + (49472224 / 225) * c * t ^ 2 + (-515998252 / 1125) * c * t ^ 4 + (8678195417 / 56250) * c * t ^ 6 + (9506211157757 / 67500000) * c * t ^ 8 + (-633382350547 / 45000000) * c * t ^ 10 + (-4938921343 / 125000) * c * t ^ 12 + (-2499590299 / 54000000) * c * t ^ 14 + (-1981669874621 / 810000000) * c * t ^ 16 + (-2888755357 / 13500000) * c * t ^ 18 + (378161211131 / 6075000000) * c * t ^ 20 + (-36942449029 / 450000000) * c * t ^ 22 + (2303112631 / 4050000000) * c * t ^ 24 + (-462650987 / 94921875) * c * t ^ 26 + (468479033 / 3037500000) * c * t ^ 32 + (6184028 / 225) * c ^ 2 * t ^ 2 + (-831824 / 9) * c ^ 2 * t ^ 4 + (2218305623 / 18750) * c ^ 2 * t ^ 6 + (-3707063062031 / 50625000) * c ^ 2 * t ^ 8 + (1227407443993 / 50625000) * c ^ 2 * t ^ 10 + (-33358657307 / 6750000) * c ^ 2 * t ^ 12 + (928590214 / 1265625) * c ^ 2 * t ^ 14 + (-2341521187 / 12656250) * c ^ 2 * t ^ 16 + (4953427307 / 607500000) * c ^ 2 * t ^ 18 + (-17377120001 / 1518750000) * c ^ 2 * t ^ 20 + (12797890219 / 1518750000) * c ^ 2 * t ^ 22 + (10418063 / 759375000) * c ^ 2 * t ^ 24 + (1509708293 / 9112500000) * c ^ 2 * t ^ 26 + (42632 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((-24736112 / 225) * t ^ 2 + (418021268 / 1125) * t ^ 4 + (-2694905773 / 5625) * t ^ 6 + (20176093762909 / 67500000) * t ^ 8 + (-6683937843799 / 67500000) * t ^ 10 + (546410272451 / 27000000) * t ^ 12 + (-20204335423 / 5400000) * t ^ 14 + (38161610497 / 33750000) * t ^ 16 + (-47300781 / 625000) * t ^ 18 + (328374998623 / 6075000000) * t ^ 20 + (-20863777543 / 675000000) * t ^ 22 + (-38555087 / 253125000) * t ^ 24 + (-954613463 / 759375000) * t ^ 26 + (-170528 / 94921875) * t ^ 32) * c_sq
#print axioms v52_00
#print axioms v52_11
#print axioms v52_22
#print axioms v52_33
#print axioms v52_44
end PhotonCertA
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
theorem site53 : ((r ^ 3 * phiPlus) : ℂ) = ((-1 / 24) * d + (1 / 24) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 64) * d + (-1 / 64) * alpha + (1 / 192) * alpha * d + (-1 / 192) * alpha ^ 2) * alpha_sq
theorem phase53_00 : ((r ^ 3 * phiPlus) : ℂ) ^ 0 * star ((r ^ 3 * phiPlus) : ℂ) ^ 0 = (1) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase53_01 : ((r ^ 3 * phiPlus) : ℂ) ^ 0 * star ((r ^ 3 * phiPlus) : ℂ) ^ 1 = ((-1 / 24) * d + (-1 / 24) * alpha) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase53_02 : ((r ^ 3 * phiPlus) : ℂ) ^ 0 * star ((r ^ 3 * phiPlus) : ℂ) ^ 2 = ((95 / 96) + (1 / 288) * alpha * d) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 576)) * alpha_sq + ((1 / 576)) * d_sq
theorem phase53_03 : ((r ^ 3 * phiPlus) : ℂ) ^ 0 * star ((r ^ 3 * phiPlus) : ℂ) ^ 3 = ((-47 / 1152) * d + (-143 / 1152) * alpha) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 4608) * d + (-1 / 13824) * alpha) * alpha_sq + ((-1 / 13824) * d + (-1 / 4608) * alpha) * d_sq
theorem phase53_04 : ((r ^ 3 * phiPlus) : ℂ) ^ 0 * star ((r ^ 3 * phiPlus) : ℂ) ^ 4 = ((4417 / 4608) + (95 / 13824) * alpha * d) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 110592) + (1 / 55296) * d ^ 2 + (1 / 82944) * alpha * d + (1 / 331776) * alpha ^ 2) * alpha_sq + ((185 / 110592) + (1 / 331776) * d ^ 2 + (1 / 82944) * alpha * d) * d_sq
theorem phase53_10 : ((r ^ 3 * phiPlus) : ℂ) ^ 1 * star ((r ^ 3 * phiPlus) : ℂ) ^ 0 = ((-1 / 24) * d + (1 / 24) * alpha) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase53_11 : ((r ^ 3 * phiPlus) : ℂ) ^ 1 * star ((r ^ 3 * phiPlus) : ℂ) ^ 1 = (1) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 576)) * alpha_sq + ((1 / 576)) * d_sq
theorem phase53_12 : ((r ^ 3 * phiPlus) : ℂ) ^ 1 * star ((r ^ 3 * phiPlus) : ℂ) ^ 2 = ((-1 / 24) * d + (-1 / 24) * alpha) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 13824) * d + (1 / 13824) * alpha) * alpha_sq + ((-1 / 13824) * d + (-1 / 13824) * alpha) * d_sq
theorem phase53_13 : ((r ^ 3 * phiPlus) : ℂ) ^ 1 * star ((r ^ 3 * phiPlus) : ℂ) ^ 3 = ((95 / 96) + (1 / 288) * alpha * d) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 110592) + (-1 / 165888) * alpha * d + (-1 / 331776) * alpha ^ 2) * alpha_sq + ((191 / 110592) + (1 / 331776) * d ^ 2 + (1 / 165888) * alpha * d) * d_sq
theorem phase53_14 : ((r ^ 3 * phiPlus) : ℂ) ^ 1 * star ((r ^ 3 * phiPlus) : ℂ) ^ 4 = ((-47 / 1152) * d + (-143 / 1152) * alpha) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 884736) * d + (-1 / 3981312) * d ^ 3 + (-1 / 2654208) * alpha + (1 / 3981312) * alpha * d ^ 2 + (1 / 2654208) * alpha ^ 2 * d + (1 / 7962624) * alpha ^ 3) * alpha_sq + ((-7 / 98304) * d + (-1 / 7962624) * d ^ 3 + (-575 / 2654208) * alpha + (-1 / 2654208) * alpha * d ^ 2) * d_sq
theorem phase53_20 : ((r ^ 3 * phiPlus) : ℂ) ^ 2 * star ((r ^ 3 * phiPlus) : ℂ) ^ 0 = ((95 / 96) + (-1 / 288) * alpha * d) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 576)) * alpha_sq + ((1 / 576)) * d_sq
theorem phase53_21 : ((r ^ 3 * phiPlus) : ℂ) ^ 2 * star ((r ^ 3 * phiPlus) : ℂ) ^ 1 = ((-1 / 24) * d + (1 / 24) * alpha) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 13824) * d + (-1 / 13824) * alpha) * alpha_sq + ((-1 / 13824) * d + (1 / 13824) * alpha) * d_sq
theorem phase53_22 : ((r ^ 3 * phiPlus) : ℂ) ^ 2 * star ((r ^ 3 * phiPlus) : ℂ) ^ 2 = (1) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 110592) + (-1 / 165888) * d ^ 2 + (1 / 331776) * alpha ^ 2) * alpha_sq + ((193 / 110592) + (1 / 331776) * d ^ 2) * d_sq
theorem phase53_23 : ((r ^ 3 * phiPlus) : ℂ) ^ 2 * star ((r ^ 3 * phiPlus) : ℂ) ^ 3 = ((-1 / 24) * d + (-1 / 24) * alpha) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 2654208) * d + (1 / 3981312) * d ^ 3 + (1 / 2654208) * alpha + (1 / 3981312) * alpha * d ^ 2 + (-1 / 7962624) * alpha ^ 2 * d + (-1 / 7962624) * alpha ^ 3) * alpha_sq + ((-193 / 2654208) * d + (-1 / 7962624) * d ^ 3 + (-193 / 2654208) * alpha + (-1 / 7962624) * alpha * d ^ 2) * d_sq
theorem phase53_24 : ((r ^ 3 * phiPlus) : ℂ) ^ 2 * star ((r ^ 3 * phiPlus) : ℂ) ^ 4 = ((95 / 96) + (1 / 288) * alpha * d) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 21233664) + (1 / 63700992) * d ^ 2 + (-1 / 191102976) * d ^ 4 + (-1 / 31850496) * alpha * d + (-1 / 47775744) * alpha * d ^ 3 + (-1 / 63700992) * alpha ^ 2 + (-1 / 191102976) * alpha ^ 2 * d ^ 2 + (1 / 95551488) * alpha ^ 3 * d + (1 / 191102976) * alpha ^ 4) * alpha_sq + ((36671 / 21233664) + (1 / 331776) * d ^ 2 + (1 / 191102976) * d ^ 4 + (193 / 31850496) * alpha * d + (1 / 95551488) * alpha * d ^ 3) * d_sq
theorem phase53_30 : ((r ^ 3 * phiPlus) : ℂ) ^ 3 * star ((r ^ 3 * phiPlus) : ℂ) ^ 0 = ((-47 / 1152) * d + (143 / 1152) * alpha) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 4608) * d + (1 / 13824) * alpha) * alpha_sq + ((-1 / 13824) * d + (1 / 4608) * alpha) * d_sq
theorem phase53_31 : ((r ^ 3 * phiPlus) : ℂ) ^ 3 * star ((r ^ 3 * phiPlus) : ℂ) ^ 1 = ((95 / 96) + (-1 / 288) * alpha * d) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 110592) + (1 / 165888) * alpha * d + (-1 / 331776) * alpha ^ 2) * alpha_sq + ((191 / 110592) + (1 / 331776) * d ^ 2 + (-1 / 165888) * alpha * d) * d_sq
theorem phase53_32 : ((r ^ 3 * phiPlus) : ℂ) ^ 3 * star ((r ^ 3 * phiPlus) : ℂ) ^ 2 = ((-1 / 24) * d + (1 / 24) * alpha) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 2654208) * d + (1 / 3981312) * d ^ 3 + (-1 / 2654208) * alpha + (-1 / 3981312) * alpha * d ^ 2 + (-1 / 7962624) * alpha ^ 2 * d + (1 / 7962624) * alpha ^ 3) * alpha_sq + ((-193 / 2654208) * d + (-1 / 7962624) * d ^ 3 + (193 / 2654208) * alpha + (1 / 7962624) * alpha * d ^ 2) * d_sq
theorem phase53_33 : ((r ^ 3 * phiPlus) : ℂ) ^ 3 * star ((r ^ 3 * phiPlus) : ℂ) ^ 3 = (1) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 21233664) + (-1 / 21233664) * d ^ 2 + (-1 / 63700992) * d ^ 4 + (1 / 63700992) * alpha ^ 2 + (1 / 63700992) * alpha ^ 2 * d ^ 2 + (-1 / 191102976) * alpha ^ 4) * alpha_sq + ((37057 / 21233664) + (97 / 31850496) * d ^ 2 + (1 / 191102976) * d ^ 4) * d_sq
theorem phase53_34 : ((r ^ 3 * phiPlus) : ℂ) ^ 3 * star ((r ^ 3 * phiPlus) : ℂ) ^ 4 = ((-1 / 24) * d + (-1 / 24) * alpha) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 509607936) * d + (1 / 509607936) * d ^ 3 + (1 / 1528823808) * d ^ 5 + (1 / 509607936) * alpha + (1 / 509607936) * alpha * d ^ 2 + (1 / 1528823808) * alpha * d ^ 4 + (-1 / 1528823808) * alpha ^ 2 * d + (-1 / 1528823808) * alpha ^ 2 * d ^ 3 + (-1 / 1528823808) * alpha ^ 3 + (-1 / 1528823808) * alpha ^ 3 * d ^ 2 + (1 / 4586471424) * alpha ^ 4 * d + (1 / 4586471424) * alpha ^ 5) * alpha_sq + ((-37057 / 509607936) * d + (-97 / 764411904) * d ^ 3 + (-1 / 4586471424) * d ^ 5 + (-37057 / 509607936) * alpha + (-97 / 764411904) * alpha * d ^ 2 + (-1 / 4586471424) * alpha * d ^ 4) * d_sq
theorem phase53_40 : ((r ^ 3 * phiPlus) : ℂ) ^ 4 * star ((r ^ 3 * phiPlus) : ℂ) ^ 0 = ((4417 / 4608) + (-95 / 13824) * alpha * d) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 110592) + (1 / 55296) * d ^ 2 + (-1 / 82944) * alpha * d + (1 / 331776) * alpha ^ 2) * alpha_sq + ((185 / 110592) + (1 / 331776) * d ^ 2 + (-1 / 82944) * alpha * d) * d_sq
theorem phase53_41 : ((r ^ 3 * phiPlus) : ℂ) ^ 4 * star ((r ^ 3 * phiPlus) : ℂ) ^ 1 = ((-47 / 1152) * d + (143 / 1152) * alpha) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 884736) * d + (-1 / 3981312) * d ^ 3 + (1 / 2654208) * alpha + (-1 / 3981312) * alpha * d ^ 2 + (1 / 2654208) * alpha ^ 2 * d + (-1 / 7962624) * alpha ^ 3) * alpha_sq + ((-7 / 98304) * d + (-1 / 7962624) * d ^ 3 + (575 / 2654208) * alpha + (1 / 2654208) * alpha * d ^ 2) * d_sq
theorem phase53_42 : ((r ^ 3 * phiPlus) : ℂ) ^ 4 * star ((r ^ 3 * phiPlus) : ℂ) ^ 2 = ((95 / 96) + (-1 / 288) * alpha * d) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 21233664) + (1 / 63700992) * d ^ 2 + (-1 / 191102976) * d ^ 4 + (1 / 31850496) * alpha * d + (1 / 47775744) * alpha * d ^ 3 + (-1 / 63700992) * alpha ^ 2 + (-1 / 191102976) * alpha ^ 2 * d ^ 2 + (-1 / 95551488) * alpha ^ 3 * d + (1 / 191102976) * alpha ^ 4) * alpha_sq + ((36671 / 21233664) + (1 / 331776) * d ^ 2 + (1 / 191102976) * d ^ 4 + (-193 / 31850496) * alpha * d + (-1 / 95551488) * alpha * d ^ 3) * d_sq
theorem phase53_43 : ((r ^ 3 * phiPlus) : ℂ) ^ 4 * star ((r ^ 3 * phiPlus) : ℂ) ^ 3 = ((-1 / 24) * d + (1 / 24) * alpha) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 509607936) * d + (1 / 509607936) * d ^ 3 + (1 / 1528823808) * d ^ 5 + (-1 / 509607936) * alpha + (-1 / 509607936) * alpha * d ^ 2 + (-1 / 1528823808) * alpha * d ^ 4 + (-1 / 1528823808) * alpha ^ 2 * d + (-1 / 1528823808) * alpha ^ 2 * d ^ 3 + (1 / 1528823808) * alpha ^ 3 + (1 / 1528823808) * alpha ^ 3 * d ^ 2 + (1 / 4586471424) * alpha ^ 4 * d + (-1 / 4586471424) * alpha ^ 5) * alpha_sq + ((-37057 / 509607936) * d + (-97 / 764411904) * d ^ 3 + (-1 / 4586471424) * d ^ 5 + (37057 / 509607936) * alpha + (97 / 764411904) * alpha * d ^ 2 + (1 / 4586471424) * alpha * d ^ 4) * d_sq
theorem phase53_44 : ((r ^ 3 * phiPlus) : ℂ) ^ 4 * star ((r ^ 3 * phiPlus) : ℂ) ^ 4 = (1) := by
  rw [site53]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 4076863488) + (-1 / 3057647616) * d ^ 2 + (-1 / 6115295232) * d ^ 4 + (-1 / 27518828544) * d ^ 6 + (1 / 12230590464) * alpha ^ 2 + (1 / 9172942848) * alpha ^ 2 * d ^ 2 + (1 / 18345885696) * alpha ^ 2 * d ^ 4 + (-1 / 36691771392) * alpha ^ 4 + (-1 / 27518828544) * alpha ^ 4 * d ^ 2 + (1 / 110075314176) * alpha ^ 6) * alpha_sq + ((7114945 / 4076863488) + (4139 / 1358954496) * d ^ 2 + (65 / 12230590464) * d ^ 4 + (1 / 110075314176) * d ^ 6) * d_sq
noncomputable def z53 : Fin 53 → ℂ := Fin.snoc z52 (r ^ 3 * phiPlus)
theorem v53_00 (t : ℂ) : (momentPoly 53 z53 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00]
  try simp only [phase53_00]
  try simp only [star_one, star_neg]
  ring
theorem v53_01 (t : ℂ) : (momentPoly 53 z53 0 1).eval t = (1 * t + (-1 / 24) * d * t + (7 / 24) * alpha * t) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01]
  try simp only [phase53_00, phase53_01]
  try simp only [star_one, star_neg]
  ring
theorem v53_02 (t : ℂ) : (momentPoly 53 z53 0 2).eval t = ((1187 / 120) * t ^ 2 + (-3913 / 480) * t ^ 4 + (-1 / 12) * d * t ^ 2 + (1309 / 120) * alpha * t ^ 2 + (-413 / 40) * alpha * t ^ 4 + (-1 / 36) * alpha * d * t ^ 2 + (1 / 288) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02]
  try simp only [phase53_00, phase53_01, phase53_02]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 36) * t ^ 2) * alpha_sq
theorem v53_03 (t : ℂ) : (momentPoly 53 z53 0 3).eval t = ((183 / 320) * t ^ 3 + (847 / 320) * t ^ 5 + (-1177 / 960) * d * t ^ 3 + (1087 / 960) * d * t ^ 5 + (-47 / 1152) * d * t ^ 9 + (57361 / 1600) * alpha * t ^ 3 + (-154037 / 4800) * alpha * t ^ 5 + (-60151 / 28800) * alpha * t ^ 9 + (-1319 / 960) * alpha * d * t ^ 3 + (1249 / 960) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_03]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03]
  try simp only [star_one, star_neg]
  linear_combination ((-1319 / 960) * t ^ 3 + (413 / 320) * t ^ 5 + (1 / 288) * d * t ^ 5) * alpha_sq
theorem v53_04 (t : ℂ) : (momentPoly 53 z53 0 4).eval t = ((-17140463 / 24000) * t ^ 4 + (22805129 / 16000) * t ^ 6 + (-2216273 / 3000) * t ^ 8 + (714971 / 18000) * t ^ 10 + (-4106063 / 576000) * t ^ 16 + (71 / 120) * d * t ^ 4 + (-491 / 384) * d * t ^ 6 + (413 / 640) * d * t ^ 8 + (-47 / 288) * d * t ^ 10 + (13706641 / 24000) * alpha * t ^ 4 + (-48219779 / 48000) * alpha * t ^ 6 + (3804781 / 8000) * alpha * t ^ 8 + (-107069 / 2250) * alpha * t ^ 10 + (470783 / 48000) * alpha * t ^ 16 + (-11123 / 1800) * alpha * d * t ^ 4 + (56719 / 9600) * alpha * d * t ^ 6 + (-1097 / 5760) * alpha * d * t ^ 8 + (5897 / 21600) * alpha * d * t ^ 10 + (95 / 13824) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_03, v52_04]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04]
  try simp only [star_one, star_neg]
  linear_combination ((-11123 / 1800) * t ^ 4 + (10267 / 1800) * t ^ 6 + (3497 / 21600) * t ^ 10 + (1319 / 5760) * d * t ^ 6 + (-413 / 1920) * d * t ^ 8) * alpha_sq
theorem v53_10 (t : ℂ) : (momentPoly 53 z53 1 0).eval t = (1 * t + (-1 / 24) * d * t + (-7 / 24) * alpha * t) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_10]
  try simp only [phase53_00, phase53_10]
  try simp only [star_one, star_neg]
  ring
theorem v53_11 (t : ℂ) : (momentPoly 53 z53 1 1).eval t = (53 + (-203 / 4) * t ^ 2 + (-1 / 12) * d * t ^ 2) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_10, v52_11]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 36) * t ^ 2) * alpha_sq
theorem v53_12 (t : ℂ) : (momentPoly 53 z53 1 2).eval t = (105 * t + (-79271 / 960) * t ^ 3 + (-17459 / 960) * t ^ 5 + (-35 / 8) * d * t + (3661 / 960) * d * t ^ 3 + (123 / 320) * d * t ^ 5 + (245 / 8) * alpha * t + (-6927 / 320) * alpha * t ^ 3 + (-2663 / 320) * alpha * t ^ 5 + (-1319 / 2880) * alpha * d * t ^ 3 + (1249 / 2880) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_10, v52_11, v52_12]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12]
  try simp only [star_one, star_neg]
  linear_combination ((1319 / 2880) * t ^ 3 + (-413 / 960) * t ^ 5 + (-1 / 864) * d * t ^ 5) * alpha_sq
theorem v53_13 (t : ℂ) : (momentPoly 53 z53 1 3).eval t = ((15431 / 10) * t ^ 2 + (-3278507 / 1200) * t ^ 4 + (951667 / 800) * t ^ 6 + (70067 / 9600) * t ^ 10 + (-13) * d * t ^ 2 + (4943 / 480) * d * t ^ 4 + (1157 / 480) * d * t ^ 6 + (-47 / 1152) * d * t ^ 10 + (17017 / 10) * alpha * t ^ 2 + (-7731631 / 2400) * alpha * t ^ 4 + (3633719 / 2400) * alpha * t ^ 6 + (237209 / 28800) * alpha * t ^ 10 + (-13 / 3) * alpha * d * t ^ 2 + (457 / 200) * alpha * d * t ^ 4 + (4439 / 2400) * alpha * d * t ^ 6 + (2749 / 28800) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_03, v52_10, v52_11, v52_12, v52_13]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13]
  try simp only [star_one, star_neg]
  linear_combination ((-13 / 3) * t ^ 2 + (11591 / 2400) * t ^ 4 + (-1139 / 2400) * t ^ 6 + (-3497 / 86400) * t ^ 10) * alpha_sq
theorem v53_14 (t : ℂ) : (momentPoly 53 z53 1 4).eval t = ((18849 / 160) * t ^ 3 + (13172461 / 64000) * t ^ 5 + (1070339 / 32000) * t ^ 7 + (-131831167 / 384000) * t ^ 9 + (-446467 / 288000) * t ^ 11 + (1674317 / 1152000) * t ^ 17 + (-121231 / 480) * d * t ^ 3 + (290829623 / 576000) * d * t ^ 5 + (-26796341 / 96000) * d * t ^ 7 + (23579993 / 1152000) * d * t ^ 9 + (518117 / 96000) * d * t ^ 11 + (44011 / 128000) * d * t ^ 17 + (5908183 / 800) * alpha * t ^ 3 + (-1485702043 / 115200) * alpha * t ^ 5 + (91586161 / 19200) * alpha * t ^ 7 + (74484923 / 230400) * alpha * t ^ 9 + (7901231 / 19200) * alpha * t ^ 11 + (212147 / 15360) * alpha * t ^ 17 + (-135857 / 480) * alpha * d * t ^ 3 + (296290199 / 576000) * alpha * d * t ^ 5 + (-20066893 / 96000) * alpha * d * t ^ 7 + (-26262511 / 1152000) * alpha * d * t ^ 9 + (491309 / 864000) * alpha * d * t ^ 11 + (-1388599 / 3456000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_03, v52_04, v52_10, v52_11, v52_12, v52_13, v52_14]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14]
  try simp only [star_one, star_neg]
  linear_combination ((-135857 / 480) * t ^ 3 + (107477027 / 192000) * t ^ 5 + (-85375481 / 288000) * t ^ 7 + (2863479 / 128000) * t ^ 9 + (-966383 / 288000) * t ^ 11 + (470783 / 1152000) * t ^ 17 + (311 / 432) * d * t ^ 5 + (-473 / 864) * d * t ^ 7 + (-137 / 864) * d * t ^ 9 + (-95 / 41472) * d * t ^ 17) * alpha_sq
theorem v53_20 (t : ℂ) : (momentPoly 53 z53 2 0).eval t = ((1187 / 120) * t ^ 2 + (-3913 / 480) * t ^ 4 + (-1 / 12) * d * t ^ 2 + (-1309 / 120) * alpha * t ^ 2 + (413 / 40) * alpha * t ^ 4 + (1 / 36) * alpha * d * t ^ 2 + (-1 / 288) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_10, v52_20]
  try simp only [phase53_00, phase53_10, phase53_20]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 36) * t ^ 2) * alpha_sq
theorem v53_21 (t : ℂ) : (momentPoly 53 z53 2 1).eval t = (105 * t + (-79271 / 960) * t ^ 3 + (-17459 / 960) * t ^ 5 + (-35 / 8) * d * t + (3661 / 960) * d * t ^ 3 + (123 / 320) * d * t ^ 5 + (-245 / 8) * alpha * t + (6927 / 320) * alpha * t ^ 3 + (2663 / 320) * alpha * t ^ 5 + (1319 / 2880) * alpha * d * t ^ 3 + (-1249 / 2880) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_10, v52_11, v52_20, v52_21]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21]
  try simp only [star_one, star_neg]
  linear_combination ((1319 / 2880) * t ^ 3 + (-413 / 960) * t ^ 5 + (-1 / 864) * d * t ^ 5) * alpha_sq
theorem v53_22 (t : ℂ) : (momentPoly 53 z53 2 2).eval t = (5565 + (-10556) * t ^ 2 + (6361351 / 1200) * t ^ 4 + (-6090031 / 9600) * t ^ 6 + (1066541 / 3200) * t ^ 8 + (-52 / 3) * d * t ^ 2 + (203 / 15) * d * t ^ 4 + (6989 / 1920) * d * t ^ 6 + (-413 / 1920) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_10, v52_11, v52_12, v52_20, v52_21, v52_22]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22]
  try simp only [star_one, star_neg]
  linear_combination ((52 / 9) * t ^ 2 + (-473 / 108) * t ^ 4 + (-137 / 108) * t ^ 6 + (-1319 / 17280) * d * t ^ 6 + (413 / 5760) * d * t ^ 8) * alpha_sq
theorem v53_23 (t : ℂ) : (momentPoly 53 z53 2 3).eval t = (16381 * t + (-8164913 / 320) * t ^ 3 + (108173219 / 24000) * t ^ 5 + (35833891 / 9600) * t ^ 7 + (14060279 / 16000) * t ^ 9 + (-11530603 / 384000) * t ^ 11 + (24458363 / 384000) * t ^ 13 + (-16381 / 24) * d * t + (377083 / 320) * d * t ^ 3 + (-12143447 / 28800) * d * t ^ 5 + (-171553 / 5760) * d * t ^ 7 + (-42737 / 960) * d * t ^ 9 + (-76667 / 76800) * d * t ^ 11 + (81217 / 230400) * d * t ^ 13 + (114667 / 24) * alpha * t + (-2140443 / 320) * alpha * t ^ 3 + (-49041271 / 144000) * alpha * t ^ 5 + (56908597 / 28800) * alpha * t ^ 7 + (199613 / 750) * alpha * t ^ 9 + (-5374229 / 1152000) * alpha * t ^ 11 + (19371749 / 1152000) * alpha * t ^ 13 + (-135857 / 960) * alpha * d * t ^ 3 + (3874783 / 14400) * alpha * d * t ^ 5 + (-3651229 / 28800) * alpha * d * t ^ 7 + (-433 / 1920) * alpha * d * t ^ 9 + (-19067 / 76800) * alpha * d * t ^ 11 + (-19411 / 46080) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_03, v52_10, v52_11, v52_12, v52_13, v52_20, v52_21, v52_22, v52_23]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23]
  try simp only [star_one, star_neg]
  linear_combination ((135857 / 960) * t ^ 3 + (-1286411 / 4800) * t ^ 5 + (453403 / 3600) * t ^ 7 + (1424653 / 691200) * t ^ 11 + (-59059 / 46080) * t ^ 13 + (-311 / 864) * d * t ^ 5 + (12527 / 86400) * d * t ^ 7 + (17117 / 86400) * d * t ^ 9 + (221 / 32400) * d * t ^ 13) * alpha_sq
theorem v53_24 (t : ℂ) : (momentPoly 53 z53 2 4).eval t = ((1907509 / 6) * t ^ 2 + (-686301839 / 800) * t ^ 4 + (368158287871 / 480000) * t ^ 6 + (-906914403599 / 3840000) * t ^ 8 + (6983499389 / 384000) * t ^ 10 + (-232596012227 / 23040000) * t ^ 12 + (2079447889 / 1920000) * t ^ 14 + (5426545087 / 23040000) * t ^ 18 + (-911985647 / 3840000) * t ^ 20 + (-8035 / 3) * d * t ^ 2 + (84031 / 20) * d * t ^ 4 + (-10901637 / 16000) * d * t ^ 6 + (-1586908231 / 2304000) * d * t ^ 8 + (-13143659 / 76800) * d * t ^ 10 + (21921379 / 921600) * d * t ^ 12 + (-8208287 / 1152000) * d * t ^ 14 + (127801 / 1536000) * d * t ^ 18 + (-127523 / 1152000) * d * t ^ 20 + (2103563 / 6) * alpha * t ^ 2 + (-197821759 / 200) * alpha * t ^ 4 + (1337918764867 / 1440000) * alpha * t ^ 6 + (-3485942898773 / 11520000) * alpha * t ^ 8 + (603773551 / 25600) * alpha * t ^ 10 + (-283553765923 / 23040000) * alpha * t ^ 12 + (4157497843 / 5760000) * alpha * t ^ 14 + (3639795023 / 23040000) * alpha * t ^ 18 + (-550014983 / 3840000) * alpha * t ^ 20 + (-8035 / 9) * alpha * d * t ^ 2 + (1974947 / 2400) * alpha * d * t ^ 4 + (507217 / 640) * alpha * d * t ^ 6 + (-1358230427 / 2304000) * alpha * d * t ^ 8 + (-117510793 / 1152000) * alpha * d * t ^ 10 + (-360447583 / 13824000) * alpha * d * t ^ 12 + (-1658569 / 384000) * alpha * d * t ^ 14 + (-15735499 / 13824000) * alpha * d * t ^ 18 + (-4447 / 128000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_03, v52_04, v52_10, v52_11, v52_12, v52_13, v52_14, v52_20, v52_21, v52_22, v52_23, v52_24]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24]
  try simp only [star_one, star_neg]
  linear_combination ((-8035 / 9) * t ^ 2 + (197047 / 100) * t ^ 4 + (-534517499 / 432000) * t ^ 6 + (31616507 / 216000) * t ^ 8 + (-27359 / 32000) * t ^ 10 + (200311 / 10125) * t ^ 12 + (-4352371 / 648000) * t ^ 14 + (3125117 / 2592000) * t ^ 18 + (-4564147 / 2304000) * d * t ^ 8 + (12831001 / 3456000) * d * t ^ 10 + (-954493 / 512000) * d * t ^ 12 + (1695229 / 10368000) * d * t ^ 14 + (-25061 / 331776) * d * t ^ 18 + (127523 / 3456000) * d * t ^ 20) * alpha_sq
theorem v53_30 (t : ℂ) : (momentPoly 53 z53 3 0).eval t = ((183 / 320) * t ^ 3 + (847 / 320) * t ^ 5 + (-1177 / 960) * d * t ^ 3 + (1087 / 960) * d * t ^ 5 + (-47 / 1152) * d * t ^ 9 + (-57361 / 1600) * alpha * t ^ 3 + (154037 / 4800) * alpha * t ^ 5 + (60151 / 28800) * alpha * t ^ 9 + (1319 / 960) * alpha * d * t ^ 3 + (-1249 / 960) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_10, v52_20, v52_30]
  try simp only [phase53_00, phase53_10, phase53_20, phase53_30]
  try simp only [star_one, star_neg]
  linear_combination ((-1319 / 960) * t ^ 3 + (413 / 320) * t ^ 5 + (1 / 288) * d * t ^ 5) * alpha_sq
theorem v53_31 (t : ℂ) : (momentPoly 53 z53 3 1).eval t = ((15431 / 10) * t ^ 2 + (-3278507 / 1200) * t ^ 4 + (951667 / 800) * t ^ 6 + (70067 / 9600) * t ^ 10 + (-13) * d * t ^ 2 + (4943 / 480) * d * t ^ 4 + (1157 / 480) * d * t ^ 6 + (-47 / 1152) * d * t ^ 10 + (-17017 / 10) * alpha * t ^ 2 + (7731631 / 2400) * alpha * t ^ 4 + (-3633719 / 2400) * alpha * t ^ 6 + (-237209 / 28800) * alpha * t ^ 10 + (13 / 3) * alpha * d * t ^ 2 + (-457 / 200) * alpha * d * t ^ 4 + (-4439 / 2400) * alpha * d * t ^ 6 + (-2749 / 28800) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_10, v52_11, v52_20, v52_21, v52_30, v52_31]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21, phase53_30, phase53_31]
  try simp only [star_one, star_neg]
  linear_combination ((-13 / 3) * t ^ 2 + (11591 / 2400) * t ^ 4 + (-1139 / 2400) * t ^ 6 + (-3497 / 86400) * t ^ 10) * alpha_sq
theorem v53_32 (t : ℂ) : (momentPoly 53 z53 3 2).eval t = (16381 * t + (-8164913 / 320) * t ^ 3 + (108173219 / 24000) * t ^ 5 + (35833891 / 9600) * t ^ 7 + (14060279 / 16000) * t ^ 9 + (-11530603 / 384000) * t ^ 11 + (24458363 / 384000) * t ^ 13 + (-16381 / 24) * d * t + (377083 / 320) * d * t ^ 3 + (-12143447 / 28800) * d * t ^ 5 + (-171553 / 5760) * d * t ^ 7 + (-42737 / 960) * d * t ^ 9 + (-76667 / 76800) * d * t ^ 11 + (81217 / 230400) * d * t ^ 13 + (-114667 / 24) * alpha * t + (2140443 / 320) * alpha * t ^ 3 + (49041271 / 144000) * alpha * t ^ 5 + (-56908597 / 28800) * alpha * t ^ 7 + (-199613 / 750) * alpha * t ^ 9 + (5374229 / 1152000) * alpha * t ^ 11 + (-19371749 / 1152000) * alpha * t ^ 13 + (135857 / 960) * alpha * d * t ^ 3 + (-3874783 / 14400) * alpha * d * t ^ 5 + (3651229 / 28800) * alpha * d * t ^ 7 + (433 / 1920) * alpha * d * t ^ 9 + (19067 / 76800) * alpha * d * t ^ 11 + (19411 / 46080) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_10, v52_11, v52_12, v52_20, v52_21, v52_22, v52_30, v52_31, v52_32]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22, phase53_30, phase53_31, phase53_32]
  try simp only [star_one, star_neg]
  linear_combination ((135857 / 960) * t ^ 3 + (-1286411 / 4800) * t ^ 5 + (453403 / 3600) * t ^ 7 + (1424653 / 691200) * t ^ 11 + (-59059 / 46080) * t ^ 13 + (-311 / 864) * d * t ^ 5 + (12527 / 86400) * d * t ^ 7 + (17117 / 86400) * d * t ^ 9 + (221 / 32400) * d * t ^ 13) * alpha_sq
theorem v53_33 (t : ℂ) : (momentPoly 53 z53 3 3).eval t = (868193 + (-4893315 / 2) * t ^ 2 + (973286703 / 400) * t ^ 4 + (-68209663337 / 60000) * t ^ 6 + (101657326069 / 240000) * t ^ 8 + (-2831693159 / 20000) * t ^ 10 + (2176124987 / 1440000) * t ^ 12 + (-215369177 / 160000) * t ^ 14 + (-7012759 / 180000) * t ^ 18 + (-8035 / 2) * d * t ^ 2 + (31059 / 5) * d * t ^ 4 + (-3033671 / 4000) * d * t ^ 6 + (-12378779 / 9600) * d * t ^ 8 + (-558179 / 4000) * d * t ^ 10 + (1800209 / 288000) * d * t ^ 12 + (-1414013 / 96000) * d * t ^ 14) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_03, v52_10, v52_11, v52_12, v52_13, v52_20, v52_21, v52_22, v52_23, v52_30, v52_31, v52_32, v52_33]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23, phase53_30, phase53_31, phase53_32, phase53_33]
  try simp only [star_one, star_neg]
  linear_combination ((8035 / 6) * t ^ 2 + (-8041 / 4) * t ^ 4 + (4104751 / 24000) * t ^ 6 + (3001577 / 7200) * t ^ 8 + (5784217 / 72000) * t ^ 10 + (2359691 / 288000) * t ^ 12 + (-392657 / 96000) * t ^ 14 + (-31603 / 64800) * t ^ 18 + (-101563 / 2880) * d * t ^ 6 + (642173 / 9600) * d * t ^ 8 + (-453403 / 14400) * d * t ^ 10 + (-15049 / 86400) * d * t ^ 14) * alpha_sq
theorem v53_34 (t : ℂ) : (momentPoly 53 z53 3 4).eval t = (3375113 * t + (-624734751 / 80) * t ^ 3 + (35333266513 / 8000) * t ^ 5 + (11496121392779 / 19200000) * t ^ 7 + (-2511533830699 / 19200000) * t ^ 9 + (-16612838373907 / 38400000) * t ^ 11 + (93651606747 / 5120000) * t ^ 13 + (-423095476757 / 12800000) * t ^ 15 + (-443279311987 / 153600000) * t ^ 17 + (6168606793 / 6400000) * t ^ 19 + (-41635793393 / 38400000) * t ^ 21 + (-28778868233 / 460800000) * t ^ 25 + (-3375113 / 24) * d * t + (28852341 / 80) * d * t ^ 3 + (-698729381 / 2400) * d * t ^ 5 + (1009835491121 / 11520000) * d * t ^ 7 + (-51764985737 / 1280000) * d * t ^ 9 + (514090031863 / 23040000) * d * t ^ 11 + (235493579207 / 138240000) * d * t ^ 13 + (-3629112203 / 23040000) * d * t ^ 15 + (535032181 / 18432000) * d * t ^ 17 + (-46133591 / 1920000) * d * t ^ 19 + (629865169 / 23040000) * d * t ^ 21 + (16005103 / 55296000) * d * t ^ 25 + (23625791 / 24) * alpha * t + (-163775061 / 80) * alpha * t ^ 3 + (3388687051 / 6000) * alpha * t ^ 5 + (17713255238329 / 19200000) * alpha * t ^ 7 + (-1891752562723 / 6400000) * alpha * t ^ 9 + (-13222307176331 / 115200000) * alpha * t ^ 11 + (-679084279127 / 138240000) * alpha * t ^ 13 + (-895182029993 / 115200000) * alpha * t ^ 15 + (-685932259981 / 460800000) * alpha * t ^ 17 + (1576714829 / 7200000) * alpha * t ^ 19 + (-25784767649 / 115200000) * alpha * t ^ 21 + (-21207270199 / 1382400000) * alpha * t ^ 25 + (-3465013 / 80) * alpha * d * t ^ 3 + (589804361 / 4800) * alpha * d * t ^ 5 + (-1335748788017 / 11520000) * alpha * d * t ^ 7 + (145383037067 / 3840000) * alpha * d * t ^ 9 + (-12595110499 / 4608000) * alpha * d * t ^ 11 + (149916845411 / 138240000) * alpha * d * t ^ 13 + (1488891407 / 7680000) * alpha * d * t ^ 15 + (-380768651 / 18432000) * alpha * d * t ^ 17 + (-204883663 / 11520000) * alpha * d * t ^ 19 + (469116511 / 23040000) * alpha * d * t ^ 21 + (-22126801 / 55296000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_03, v52_04, v52_10, v52_11, v52_12, v52_13, v52_14, v52_20, v52_21, v52_22, v52_23, v52_24, v52_30, v52_31, v52_32, v52_33, v52_34]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24, phase53_30, phase53_31, phase53_32, phase53_33, phase53_34]
  try simp only [star_one, star_neg]
  linear_combination ((3465013 / 80) * t ^ 3 + (-196069237 / 1600) * t ^ 5 + (443297189339 / 3840000) * t ^ 7 + (-435465774451 / 11520000) * t ^ 9 + (2018738459 / 512000) * t ^ 11 + (-433021494551 / 138240000) * t ^ 13 + (49332381217 / 69120000) * t ^ 15 + (136492499 / 2048000) * t ^ 17 + (250803829 / 12960000) * t ^ 19 + (-156322477 / 7680000) * t ^ 21 + (67321969 / 55296000) * t ^ 25 + (-31933 / 288) * d * t ^ 5 + (764147 / 8640) * d * t ^ 7 + (86926823 / 691200) * d * t ^ 9 + (-151679587 / 1728000) * d * t ^ 11 + (-231307717 / 20736000) * d * t ^ 13 + (-20400907 / 5184000) * d * t ^ 15 + (-237937 / 648000) * d * t ^ 17 + (-211337 / 829440) * d * t ^ 19 + (437927 / 5184000) * d * t ^ 21 + (4199 / 311040) * d * t ^ 25) * alpha_sq
theorem v53_40 (t : ℂ) : (momentPoly 53 z53 4 0).eval t = ((-17140463 / 24000) * t ^ 4 + (22805129 / 16000) * t ^ 6 + (-2216273 / 3000) * t ^ 8 + (714971 / 18000) * t ^ 10 + (-4106063 / 576000) * t ^ 16 + (71 / 120) * d * t ^ 4 + (-491 / 384) * d * t ^ 6 + (413 / 640) * d * t ^ 8 + (-47 / 288) * d * t ^ 10 + (-13706641 / 24000) * alpha * t ^ 4 + (48219779 / 48000) * alpha * t ^ 6 + (-3804781 / 8000) * alpha * t ^ 8 + (107069 / 2250) * alpha * t ^ 10 + (-470783 / 48000) * alpha * t ^ 16 + (11123 / 1800) * alpha * d * t ^ 4 + (-56719 / 9600) * alpha * d * t ^ 6 + (1097 / 5760) * alpha * d * t ^ 8 + (-5897 / 21600) * alpha * d * t ^ 10 + (-95 / 13824) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_10, v52_20, v52_30, v52_40]
  try simp only [phase53_00, phase53_10, phase53_20, phase53_30, phase53_40]
  try simp only [star_one, star_neg]
  linear_combination ((-11123 / 1800) * t ^ 4 + (10267 / 1800) * t ^ 6 + (3497 / 21600) * t ^ 10 + (1319 / 5760) * d * t ^ 6 + (-413 / 1920) * d * t ^ 8) * alpha_sq
theorem v53_41 (t : ℂ) : (momentPoly 53 z53 4 1).eval t = ((18849 / 160) * t ^ 3 + (13172461 / 64000) * t ^ 5 + (1070339 / 32000) * t ^ 7 + (-131831167 / 384000) * t ^ 9 + (-446467 / 288000) * t ^ 11 + (1674317 / 1152000) * t ^ 17 + (-121231 / 480) * d * t ^ 3 + (290829623 / 576000) * d * t ^ 5 + (-26796341 / 96000) * d * t ^ 7 + (23579993 / 1152000) * d * t ^ 9 + (518117 / 96000) * d * t ^ 11 + (44011 / 128000) * d * t ^ 17 + (-5908183 / 800) * alpha * t ^ 3 + (1485702043 / 115200) * alpha * t ^ 5 + (-91586161 / 19200) * alpha * t ^ 7 + (-74484923 / 230400) * alpha * t ^ 9 + (-7901231 / 19200) * alpha * t ^ 11 + (-212147 / 15360) * alpha * t ^ 17 + (135857 / 480) * alpha * d * t ^ 3 + (-296290199 / 576000) * alpha * d * t ^ 5 + (20066893 / 96000) * alpha * d * t ^ 7 + (26262511 / 1152000) * alpha * d * t ^ 9 + (-491309 / 864000) * alpha * d * t ^ 11 + (1388599 / 3456000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_10, v52_11, v52_20, v52_21, v52_30, v52_31, v52_40, v52_41]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21, phase53_30, phase53_31, phase53_40, phase53_41]
  try simp only [star_one, star_neg]
  linear_combination ((-135857 / 480) * t ^ 3 + (107477027 / 192000) * t ^ 5 + (-85375481 / 288000) * t ^ 7 + (2863479 / 128000) * t ^ 9 + (-966383 / 288000) * t ^ 11 + (470783 / 1152000) * t ^ 17 + (311 / 432) * d * t ^ 5 + (-473 / 864) * d * t ^ 7 + (-137 / 864) * d * t ^ 9 + (-95 / 41472) * d * t ^ 17) * alpha_sq
theorem v53_42 (t : ℂ) : (momentPoly 53 z53 4 2).eval t = ((1907509 / 6) * t ^ 2 + (-686301839 / 800) * t ^ 4 + (368158287871 / 480000) * t ^ 6 + (-906914403599 / 3840000) * t ^ 8 + (6983499389 / 384000) * t ^ 10 + (-232596012227 / 23040000) * t ^ 12 + (2079447889 / 1920000) * t ^ 14 + (5426545087 / 23040000) * t ^ 18 + (-911985647 / 3840000) * t ^ 20 + (-8035 / 3) * d * t ^ 2 + (84031 / 20) * d * t ^ 4 + (-10901637 / 16000) * d * t ^ 6 + (-1586908231 / 2304000) * d * t ^ 8 + (-13143659 / 76800) * d * t ^ 10 + (21921379 / 921600) * d * t ^ 12 + (-8208287 / 1152000) * d * t ^ 14 + (127801 / 1536000) * d * t ^ 18 + (-127523 / 1152000) * d * t ^ 20 + (-2103563 / 6) * alpha * t ^ 2 + (197821759 / 200) * alpha * t ^ 4 + (-1337918764867 / 1440000) * alpha * t ^ 6 + (3485942898773 / 11520000) * alpha * t ^ 8 + (-603773551 / 25600) * alpha * t ^ 10 + (283553765923 / 23040000) * alpha * t ^ 12 + (-4157497843 / 5760000) * alpha * t ^ 14 + (-3639795023 / 23040000) * alpha * t ^ 18 + (550014983 / 3840000) * alpha * t ^ 20 + (8035 / 9) * alpha * d * t ^ 2 + (-1974947 / 2400) * alpha * d * t ^ 4 + (-507217 / 640) * alpha * d * t ^ 6 + (1358230427 / 2304000) * alpha * d * t ^ 8 + (117510793 / 1152000) * alpha * d * t ^ 10 + (360447583 / 13824000) * alpha * d * t ^ 12 + (1658569 / 384000) * alpha * d * t ^ 14 + (15735499 / 13824000) * alpha * d * t ^ 18 + (4447 / 128000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_10, v52_11, v52_12, v52_20, v52_21, v52_22, v52_30, v52_31, v52_32, v52_40, v52_41, v52_42]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22, phase53_30, phase53_31, phase53_32, phase53_40, phase53_41, phase53_42]
  try simp only [star_one, star_neg]
  linear_combination ((-8035 / 9) * t ^ 2 + (197047 / 100) * t ^ 4 + (-534517499 / 432000) * t ^ 6 + (31616507 / 216000) * t ^ 8 + (-27359 / 32000) * t ^ 10 + (200311 / 10125) * t ^ 12 + (-4352371 / 648000) * t ^ 14 + (3125117 / 2592000) * t ^ 18 + (-4564147 / 2304000) * d * t ^ 8 + (12831001 / 3456000) * d * t ^ 10 + (-954493 / 512000) * d * t ^ 12 + (1695229 / 10368000) * d * t ^ 14 + (-25061 / 331776) * d * t ^ 18 + (127523 / 3456000) * d * t ^ 20) * alpha_sq
theorem v53_43 (t : ℂ) : (momentPoly 53 z53 4 3).eval t = (3375113 * t + (-624734751 / 80) * t ^ 3 + (35333266513 / 8000) * t ^ 5 + (11496121392779 / 19200000) * t ^ 7 + (-2511533830699 / 19200000) * t ^ 9 + (-16612838373907 / 38400000) * t ^ 11 + (93651606747 / 5120000) * t ^ 13 + (-423095476757 / 12800000) * t ^ 15 + (-443279311987 / 153600000) * t ^ 17 + (6168606793 / 6400000) * t ^ 19 + (-41635793393 / 38400000) * t ^ 21 + (-28778868233 / 460800000) * t ^ 25 + (-3375113 / 24) * d * t + (28852341 / 80) * d * t ^ 3 + (-698729381 / 2400) * d * t ^ 5 + (1009835491121 / 11520000) * d * t ^ 7 + (-51764985737 / 1280000) * d * t ^ 9 + (514090031863 / 23040000) * d * t ^ 11 + (235493579207 / 138240000) * d * t ^ 13 + (-3629112203 / 23040000) * d * t ^ 15 + (535032181 / 18432000) * d * t ^ 17 + (-46133591 / 1920000) * d * t ^ 19 + (629865169 / 23040000) * d * t ^ 21 + (16005103 / 55296000) * d * t ^ 25 + (-23625791 / 24) * alpha * t + (163775061 / 80) * alpha * t ^ 3 + (-3388687051 / 6000) * alpha * t ^ 5 + (-17713255238329 / 19200000) * alpha * t ^ 7 + (1891752562723 / 6400000) * alpha * t ^ 9 + (13222307176331 / 115200000) * alpha * t ^ 11 + (679084279127 / 138240000) * alpha * t ^ 13 + (895182029993 / 115200000) * alpha * t ^ 15 + (685932259981 / 460800000) * alpha * t ^ 17 + (-1576714829 / 7200000) * alpha * t ^ 19 + (25784767649 / 115200000) * alpha * t ^ 21 + (21207270199 / 1382400000) * alpha * t ^ 25 + (3465013 / 80) * alpha * d * t ^ 3 + (-589804361 / 4800) * alpha * d * t ^ 5 + (1335748788017 / 11520000) * alpha * d * t ^ 7 + (-145383037067 / 3840000) * alpha * d * t ^ 9 + (12595110499 / 4608000) * alpha * d * t ^ 11 + (-149916845411 / 138240000) * alpha * d * t ^ 13 + (-1488891407 / 7680000) * alpha * d * t ^ 15 + (380768651 / 18432000) * alpha * d * t ^ 17 + (204883663 / 11520000) * alpha * d * t ^ 19 + (-469116511 / 23040000) * alpha * d * t ^ 21 + (22126801 / 55296000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_03, v52_10, v52_11, v52_12, v52_13, v52_20, v52_21, v52_22, v52_23, v52_30, v52_31, v52_32, v52_33, v52_40, v52_41, v52_42, v52_43]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23, phase53_30, phase53_31, phase53_32, phase53_33, phase53_40, phase53_41, phase53_42, phase53_43]
  try simp only [star_one, star_neg]
  linear_combination ((3465013 / 80) * t ^ 3 + (-196069237 / 1600) * t ^ 5 + (443297189339 / 3840000) * t ^ 7 + (-435465774451 / 11520000) * t ^ 9 + (2018738459 / 512000) * t ^ 11 + (-433021494551 / 138240000) * t ^ 13 + (49332381217 / 69120000) * t ^ 15 + (136492499 / 2048000) * t ^ 17 + (250803829 / 12960000) * t ^ 19 + (-156322477 / 7680000) * t ^ 21 + (67321969 / 55296000) * t ^ 25 + (-31933 / 288) * d * t ^ 5 + (764147 / 8640) * d * t ^ 7 + (86926823 / 691200) * d * t ^ 9 + (-151679587 / 1728000) * d * t ^ 11 + (-231307717 / 20736000) * d * t ^ 13 + (-20400907 / 5184000) * d * t ^ 15 + (-237937 / 648000) * d * t ^ 17 + (-211337 / 829440) * d * t ^ 19 + (437927 / 5184000) * d * t ^ 21 + (4199 / 311040) * d * t ^ 25) * alpha_sq
theorem v53_44 (t : ℂ) : (momentPoly 53 z53 4 4).eval t = (178880989 + (-665700742) * t ^ 2 + (98327402407 / 100) * t ^ 4 + (-762436353487 / 960) * t ^ 6 + (65977441597094753 / 144000000) * t ^ 8 + (-6777429259887911 / 32000000) * t ^ 10 + (3064929543313711 / 57600000) * t ^ 12 + (-2070868275196333 / 576000000) * t ^ 14 + (183592282500041 / 96000000) * t ^ 16 + (-14288539624049 / 72000000) * t ^ 18 + (177564643789847 / 2304000000) * t ^ 20 + (-26921572968403 / 384000000) * t ^ 22 + (17672432532001 / 512000000) * t ^ 24 + (-1014728799299 / 384000000) * t ^ 26 + (1320133122761 / 4608000000) * t ^ 32 + (-3279314 / 3) * d * t ^ 2 + (12551084 / 5) * d * t ^ 4 + (-405788853 / 320) * d * t ^ 6 + (-11951402891 / 25000) * d * t ^ 8 + (3966627945863 / 19200000) * d * t ^ 10 + (6387961928161 / 57600000) * d * t ^ 12 + (106850059289 / 69120000) * d * t ^ 14 + (112095817769 / 12800000) * d * t ^ 16 + (32633188 / 28125) * d * t ^ 18 + (-434699120081 / 1382400000) * d * t ^ 20 + (27768710027 / 76800000) * d * t ^ 22 + (109572709 / 61440000) * d * t ^ 24 + (11817630079 / 691200000) * d * t ^ 26 + (8944877 / 22118400) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_03, v52_04, v52_10, v52_11, v52_12, v52_13, v52_14, v52_20, v52_21, v52_22, v52_23, v52_24, v52_30, v52_31, v52_32, v52_33, v52_34, v52_40, v52_41, v52_42, v52_43, v52_44]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24, phase53_30, phase53_31, phase53_32, phase53_33, phase53_34, phase53_40, phase53_41, phase53_42, phase53_43, phase53_44]
  try simp only [star_one, star_neg]
  linear_combination ((3279314 / 9) * t ^ 2 + (-7311161 / 9) * t ^ 4 + (16528369 / 45) * t ^ 6 + (989534780161 / 5400000) * t ^ 8 + (-264224701361 / 5400000) * t ^ 10 + (-447349214503 / 10800000) * t ^ 12 + (-380813382001 / 25920000) * t ^ 14 + (137370412321 / 64800000) * t ^ 16 + (-616005341 / 86400000) * t ^ 18 + (88598741891 / 194400000) * t ^ 20 + (-2937511891 / 32400000) * t ^ 22 + (6968055083 / 777600000) * t ^ 26 + (-41309761 / 2880) * d * t ^ 6 + (146410271 / 3600) * d * t ^ 8 + (-1326989788817 / 34560000) * d * t ^ 10 + (435465774451 / 34560000) * d * t ^ 12 + (-42886730173 / 41472000) * d * t ^ 14 + (111297496633 / 207360000) * d * t ^ 16 + (-1659310933 / 51840000) * d * t ^ 18 + (-86718793 / 11059200) * d * t ^ 20 + (3185294009 / 414720000) * d * t ^ 22 + (-109572709 / 184320000) * d * t ^ 24 + (32209351 / 49766400) * d * t ^ 26 + (-8944877 / 66355200) * d * t ^ 32) * alpha_sq
#print axioms v53_00
#print axioms v53_11
#print axioms v53_22
#print axioms v53_33
#print axioms v53_44
end PhotonCertA
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z54 : Fin 54 → ℂ := Fin.snoc z53 (r ^ 3 * phiPlus)
theorem v54_00 (t : ℂ) : (momentPoly 54 z54 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00]
  try simp only [phase53_00]
  try simp only [star_one, star_neg]
  ring
theorem v54_01 (t : ℂ) : (momentPoly 54 z54 0 1).eval t = (1 * t + (-1 / 12) * d * t + (1 / 4) * alpha * t) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01]
  try simp only [phase53_00, phase53_01]
  try simp only [star_one, star_neg]
  ring
theorem v54_02 (t : ℂ) : (momentPoly 54 z54 0 2).eval t = ((2869 / 240) * t ^ 2 + (-573 / 80) * t ^ 4 + (-1 / 6) * d * t ^ 2 + (433 / 40) * alpha * t ^ 2 + (-413 / 40) * alpha * t ^ 4 + (-7 / 144) * alpha * d * t ^ 2 + (1 / 144) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02]
  try simp only [phase53_00, phase53_01, phase53_02]
  try simp only [star_one, star_neg]
  linear_combination ((-7 / 288) * t ^ 2) * alpha_sq + ((1 / 288) * t ^ 2) * d_sq
theorem v54_03 (t : ℂ) : (momentPoly 54 z54 0 3).eval t = ((1701 / 160) * t ^ 3 + (279 / 160) * t ^ 5 + (-1187 / 480) * d * t ^ 3 + (1939 / 960) * d * t ^ 5 + (-47 / 576) * d * t ^ 9 + (29283 / 800) * alpha * t ^ 3 + (-147377 / 4800) * alpha * t ^ 5 + (-10621 / 4800) * alpha * t ^ 9 + (-1309 / 480) * alpha * d * t ^ 3 + (1249 / 480) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_03]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03]
  try simp only [star_one, star_neg]
  linear_combination ((-1309 / 960) * t ^ 3 + (413 / 320) * t ^ 5 + (1 / 288) * d * t ^ 3 + (1 / 384) * d * t ^ 5) * alpha_sq + ((1 / 96) * t ^ 3 + (1 / 288) * alpha * t ^ 3 + (-1 / 1152) * alpha * t ^ 5) * d_sq
theorem v54_04 (t : ℂ) : (momentPoly 54 z54 0 4).eval t = ((-1737521 / 3000) * t ^ 4 + (5443471 / 4000) * t ^ 6 + (-75579361 / 96000) * t ^ 8 + (3377039 / 72000) * t ^ 10 + (-197441 / 32000) * t ^ 16 + (-61 / 320) * d * t ^ 4 + (-539 / 240) * d * t ^ 6 + (413 / 320) * d * t ^ 8 + (-47 / 144) * d * t ^ 10 + (2808911 / 4000) * alpha * t ^ 4 + (-12785951 / 12000) * alpha * t ^ 6 + (6628687 / 16000) * alpha * t ^ 8 + (-192331 / 4000) * alpha * t ^ 10 + (470783 / 48000) * alpha * t ^ 16 + (-57361 / 4800) * alpha * d * t ^ 4 + (13331 / 1200) * alpha * d * t ^ 6 + (-3913 / 11520) * alpha * d * t ^ 8 + (25963 / 43200) * alpha * d * t ^ 10 + (95 / 6912) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_03, v53_04]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04]
  try simp only [star_one, star_neg]
  linear_combination ((-57361 / 9600) * t ^ 4 + (154037 / 28800) * t ^ 6 + (17563 / 86400) * t ^ 10 + (1319 / 5760) * d * t ^ 4 + (1 / 96) * d * t ^ 6 + (-413 / 1920) * d * t ^ 8 + (-1 / 1728) * d ^ 2 * t ^ 6 + (1 / 13824) * d ^ 2 * t ^ 8) * alpha_sq + ((1177 / 5760) * t ^ 4 + (-359 / 1920) * t ^ 6 + (-1 / 4608) * t ^ 8 + (47 / 3456) * t ^ 10 + (1319 / 5760) * alpha * t ^ 4 + (-1259 / 5760) * alpha * t ^ 6) * d_sq
theorem v54_10 (t : ℂ) : (momentPoly 54 z54 1 0).eval t = (1 * t + (-1 / 12) * d * t + (-1 / 4) * alpha * t) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_10]
  try simp only [phase53_00, phase53_10]
  try simp only [star_one, star_neg]
  ring
theorem v54_11 (t : ℂ) : (momentPoly 54 z54 1 1).eval t = (54 + (-293 / 6) * t ^ 2 + (-1 / 6) * d * t ^ 2) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_10, v53_11]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11]
  try simp only [star_one, star_neg]
  linear_combination ((7 / 288) * t ^ 2) * alpha_sq + ((1 / 288) * t ^ 2) * d_sq
theorem v54_12 (t : ℂ) : (momentPoly 54 z54 1 2).eval t = (107 * t + (-2495 / 32) * t ^ 3 + (-509 / 32) * t ^ 5 + (-107 / 12) * d * t + (10993 / 1440) * d * t ^ 3 + (329 / 480) * d * t ^ 5 + (107 / 4) * alpha * t + (-23533 / 1440) * alpha * t ^ 3 + (-13127 / 1440) * alpha * t ^ 5 + (-1309 / 1440) * alpha * d * t ^ 3 + (1249 / 1440) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_10, v53_11, v53_12]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12]
  try simp only [star_one, star_neg]
  linear_combination ((1309 / 2880) * t ^ 3 + (-413 / 960) * t ^ 5 + (-1 / 864) * d * t ^ 3 + (-1 / 1152) * d * t ^ 5) * alpha_sq + ((1 / 96) * t ^ 3 + (1 / 864) * alpha * t ^ 3 + (-1 / 3456) * alpha * t ^ 5) * d_sq
theorem v54_13 (t : ℂ) : (momentPoly 54 z54 1 3).eval t = ((152057 / 80) * t ^ 2 + (-3425621 / 1200) * t ^ 4 + (4729181 / 4800) * t ^ 6 + (135349 / 14400) * t ^ 10 + (-53 / 2) * d * t ^ 2 + (4943 / 240) * d * t ^ 4 + (4153 / 960) * d * t ^ 6 + (-47 / 576) * d * t ^ 10 + (68847 / 40) * alpha * t ^ 2 + (-3811843 / 1200) * alpha * t ^ 4 + (6978293 / 4800) * alpha * t ^ 6 + (38939 / 4800) * alpha * t ^ 10 + (-371 / 48) * alpha * d * t ^ 2 + (12727 / 3600) * alpha * d * t ^ 4 + (53243 / 14400) * alpha * d * t ^ 6 + (2849 / 14400) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_03, v53_10, v53_11, v53_12, v53_13]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13]
  try simp only [star_one, star_neg]
  linear_combination ((-371 / 96) * t ^ 2 + (80633 / 19200) * t ^ 4 + (-17101 / 57600) * t ^ 6 + (-17563 / 345600) * t ^ 10) * alpha_sq + ((53 / 96) * t ^ 2 + (-4903 / 11520) * t ^ 4 + (-1097 / 11520) * t ^ 6 + (47 / 13824) * t ^ 10 + (1319 / 11520) * alpha * t ^ 4 + (-1259 / 11520) * alpha * t ^ 6) * d_sq
theorem v54_14 (t : ℂ) : (momentPoly 54 z54 1 4).eval t = ((35721 / 16) * t ^ 3 + (-176991649 / 96000) * t ^ 5 + (11639849 / 48000) * t ^ 7 + (-104002589 / 192000) * t ^ 9 + (3470591 / 144000) * t ^ 11 + (75901 / 64000) * t ^ 17 + (-8309 / 16) * d * t ^ 3 + (279485423 / 288000) * d * t ^ 5 + (-24604741 / 48000) * d * t ^ 7 + (26048543 / 576000) * d * t ^ 9 + (4674803 / 432000) * d * t ^ 11 + (349099 / 576000) * d * t ^ 17 + (614943 / 80) * alpha * t ^ 3 + (-3611002519 / 288000) * alpha * t ^ 5 + (203065853 / 48000) * alpha * t ^ 7 + (125241781 / 576000) * alpha * t ^ 9 + (182099281 / 432000) * alpha * t ^ 11 + (22303139 / 1728000) * alpha * t ^ 17 + (-9163 / 16) * alpha * d * t ^ 3 + (298313399 / 288000) * alpha * d * t ^ 5 + (-61114879 / 144000) * alpha * d * t ^ 7 + (-23265161 / 576000) * alpha * d * t ^ 9 + (527059 / 432000) * alpha * d * t ^ 11 + (-1388599 / 1728000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_03, v53_04, v53_10, v53_11, v53_12, v53_13, v53_14]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14]
  try simp only [star_one, star_neg]
  linear_combination ((-9163 / 32) * t ^ 3 + (324458681 / 576000) * t ^ 5 + (-112972433 / 384000) * t ^ 7 + (3804781 / 192000) * t ^ 9 + (-966383 / 288000) * t ^ 11 + (470783 / 1152000) * t ^ 17 + (35 / 48) * d * t ^ 3 + (5 / 1728) * d * t ^ 5 + (-11821 / 23040) * d * t ^ 7 + (-3133 / 17280) * d * t ^ 9 + (-47 / 10368) * d * t ^ 11 + (-95 / 55296) * d * t ^ 17 + (-1319 / 138240) * d ^ 2 * t ^ 7 + (1249 / 138240) * d ^ 2 * t ^ 9) * alpha_sq + ((35 / 16) * t ^ 3 + (-2507 / 1440) * t ^ 5 + (-7369 / 23040) * t ^ 7 + (-311 / 5760) * t ^ 9 + (47 / 1728) * t ^ 11 + (35 / 48) * alpha * t ^ 3 + (-9329 / 43200) * alpha * t ^ 5 + (-54719 / 115200) * alpha * t ^ 7 + (551 / 34560) * alpha * t ^ 9 + (-221 / 8100) * alpha * t ^ 11 + (-95 / 165888) * alpha * t ^ 17) * d_sq
theorem v54_20 (t : ℂ) : (momentPoly 54 z54 2 0).eval t = ((2869 / 240) * t ^ 2 + (-573 / 80) * t ^ 4 + (-1 / 6) * d * t ^ 2 + (-433 / 40) * alpha * t ^ 2 + (413 / 40) * alpha * t ^ 4 + (7 / 144) * alpha * d * t ^ 2 + (-1 / 144) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_10, v53_20]
  try simp only [phase53_00, phase53_10, phase53_20]
  try simp only [star_one, star_neg]
  linear_combination ((-7 / 288) * t ^ 2) * alpha_sq + ((1 / 288) * t ^ 2) * d_sq
theorem v54_21 (t : ℂ) : (momentPoly 54 z54 2 1).eval t = (107 * t + (-2495 / 32) * t ^ 3 + (-509 / 32) * t ^ 5 + (-107 / 12) * d * t + (10993 / 1440) * d * t ^ 3 + (329 / 480) * d * t ^ 5 + (-107 / 4) * alpha * t + (23533 / 1440) * alpha * t ^ 3 + (13127 / 1440) * alpha * t ^ 5 + (1309 / 1440) * alpha * d * t ^ 3 + (-1249 / 1440) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_10, v53_11, v53_20, v53_21]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21]
  try simp only [star_one, star_neg]
  linear_combination ((1309 / 2880) * t ^ 3 + (-413 / 960) * t ^ 5 + (-1 / 864) * d * t ^ 3 + (-1 / 1152) * d * t ^ 5) * alpha_sq + ((1 / 96) * t ^ 3 + (-1 / 864) * alpha * t ^ 3 + (1 / 3456) * alpha * t ^ 5) * d_sq
theorem v54_22 (t : ℂ) : (momentPoly 54 z54 2 2).eval t = (5778 + (-31058 / 3) * t ^ 2 + (23749229 / 4800) * t ^ 4 + (-1165823 / 1800) * t ^ 6 + (4567697 / 14400) * t ^ 8 + (-106 / 3) * d * t ^ 2 + (79271 / 2880) * d * t ^ 4 + (391 / 60) * d * t ^ 6 + (-413 / 960) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_10, v53_11, v53_12, v53_20, v53_21, v53_22]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22]
  try simp only [star_one, star_neg]
  linear_combination ((371 / 72) * t ^ 2 + (-2309 / 640) * t ^ 4 + (-2663 / 1920) * t ^ 6 + (-1319 / 17280) * d * t ^ 4 + (-1 / 288) * d * t ^ 6 + (413 / 5760) * d * t ^ 8 + (1 / 5184) * d ^ 2 * t ^ 6 + (-1 / 41472) * d ^ 2 * t ^ 8) * alpha_sq + ((53 / 72) * t ^ 2 + (-3661 / 5760) * t ^ 4 + (-1117 / 17280) * t ^ 6 + (1 / 13824) * t ^ 8) * d_sq
theorem v54_23 (t : ℂ) : (momentPoly 54 z54 2 3).eval t = (17014 * t + (-785925 / 32) * t ^ 3 + (97439909 / 24000) * t ^ 5 + (34782561 / 12800) * t ^ 7 + (164800073 / 192000) * t ^ 9 + (-18577537 / 576000) * t ^ 11 + (4322473 / 64000) * t ^ 13 + (-8507 / 6) * d * t + (76951 / 32) * d * t ^ 3 + (-6234977 / 7200) * d * t ^ 5 + (-1546577 / 38400) * d * t ^ 7 + (-1947161 / 23040) * d * t ^ 9 + (-699347 / 345600) * d * t ^ 11 + (71617 / 115200) * d * t ^ 13 + (8507 / 2) * alpha * t + (-164731 / 32) * alpha * t ^ 3 + (-13580651 / 9000) * alpha * t ^ 5 + (252408653 / 115200) * alpha * t ^ 7 + (125267999 / 576000) * alpha * t ^ 9 + (-18130111 / 1728000) * alpha * t ^ 11 + (27515311 / 1728000) * alpha * t ^ 13 + (-9163 / 32) * alpha * d * t ^ 3 + (2600167 / 4800) * alpha * d * t ^ 5 + (-3252043 / 12800) * alpha * d * t ^ 7 + (-1017 / 2560) * alpha * d * t ^ 9 + (-55601 / 115200) * alpha * d * t ^ 11 + (-19411 / 23040) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_03, v53_10, v53_11, v53_12, v53_13, v53_20, v53_21, v53_22, v53_23]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23]
  try simp only [star_one, star_neg]
  linear_combination ((9163 / 64) * t ^ 3 + (-7768801 / 28800) * t ^ 5 + (3633719 / 28800) * t ^ 7 + (1410353 / 691200) * t ^ 11 + (-59059 / 46080) * t ^ 13 + (-35 / 96) * d * t ^ 3 + (-703 / 5400) * d * t ^ 5 + (1837 / 7200) * d * t ^ 7 + (17117 / 86400) * d * t ^ 9 + (73 / 16200) * d * t ^ 11 + (10621 / 1382400) * d * t ^ 13 + (1319 / 138240) * d ^ 2 * t ^ 7 + (-1249 / 138240) * d ^ 2 * t ^ 9) * alpha_sq + ((105 / 32) * t ^ 3 + (-14687 / 5760) * t ^ 5 + (-5257 / 7680) * t ^ 7 + (311 / 5760) * t ^ 9 + (47 / 6912) * t ^ 11 + (35 / 96) * alpha * t ^ 3 + (-5113 / 21600) * alpha * t ^ 5 + (-9517 / 86400) * alpha * t ^ 7 + (1 / 13824) * alpha * t ^ 9 + (-4711 / 518400) * alpha * t ^ 11 + (47 / 165888) * alpha * t ^ 13) * d_sq
theorem v54_24 (t : ℂ) : (momentPoly 54 z54 2 4).eval t = ((47903693 / 120) * t ^ 2 + (-1143615061 / 1200) * t ^ 4 + (1406269525229 / 1920000) * t ^ 6 + (-363793228357 / 1920000) * t ^ 8 + (22602443509 / 1152000) * t ^ 10 + (-3020968771 / 320000) * t ^ 12 + (1161193241 / 1080000) * t ^ 14 + (121397167 / 540000) * t ^ 18 + (-4359445649 / 17280000) * t ^ 20 + (-16697 / 3) * d * t ^ 2 + (128518 / 15) * d * t ^ 4 + (-1750354487 / 1152000) * d * t ^ 6 + (-158452337 / 128000) * d * t ^ 8 + (-167654501 / 576000) * d * t ^ 10 + (54290399 / 1152000) * d * t ^ 12 + (-1563527 / 96000) * d * t ^ 14 + (239093 / 1152000) * d * t ^ 18 + (-127523 / 576000) * d * t ^ 20 + (7229801 / 20) * alpha * t ^ 2 + (-590008069 / 600) * alpha * t ^ 4 + (5125143132343 / 5760000) * alpha * t ^ 6 + (-538376520773 / 1920000) * alpha * t ^ 8 + (27170304953 / 1152000) * alpha * t ^ 10 + (-102302985103 / 8640000) * alpha * t ^ 12 + (101819573 / 135000) * alpha * t ^ 14 + (719278489 / 4320000) * alpha * t ^ 18 + (-79123343 / 640000) * alpha * t ^ 20 + (-116879 / 72) * alpha * d * t ^ 2 + (4475807 / 3600) * alpha * d * t ^ 4 + (6356761663 / 3456000) * alpha * d * t ^ 6 + (-4243426127 / 3456000) * alpha * d * t ^ 8 + (-96876749 / 576000) * alpha * d * t ^ 10 + (-63451949 / 1152000) * alpha * d * t ^ 12 + (-22284089 / 2592000) * alpha * d * t ^ 14 + (-898279 / 414720) * alpha * d * t ^ 18 + (-36023 / 576000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_03, v53_04, v53_10, v53_11, v53_12, v53_13, v53_14, v53_20, v53_21, v53_22, v53_23, v53_24]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24]
  try simp only [star_one, star_neg]
  linear_combination ((-116879 / 144) * t ^ 2 + (1048229 / 600) * t ^ 4 + (-2348129509 / 2304000) * t ^ 6 + (9424819 / 138240) * t ^ 8 + (-34387601 / 13824000) * t ^ 10 + (42029771 / 1728000) * t ^ 12 + (-5991553 / 864000) * t ^ 14 + (212147 / 184320) * t ^ 18 + (-4564147 / 2304000) * d * t ^ 6 + (3980387 / 2304000) * d * t ^ 8 + (5619217 / 3456000) * d * t ^ 10 + (-12372607 / 6912000) * d * t ^ 12 + (389467 / 864000) * d * t ^ 14 + (-749579 / 6912000) * d * t ^ 18 + (127523 / 3456000) * d * t ^ 20 + (11123 / 518400) * d ^ 2 * t ^ 8 + (-56719 / 2764800) * d ^ 2 * t ^ 10 + (1097 / 1658880) * d ^ 2 * t ^ 12 + (-5897 / 6220800) * d ^ 2 * t ^ 14 + (95 / 497664) * d ^ 2 * t ^ 18 + (-95 / 1990656) * d ^ 2 * t ^ 20) * alpha_sq + ((16697 / 144) * t ^ 2 + (-63739 / 360) * t ^ 4 + (64091819 / 2304000) * t ^ 6 + (32440621 / 1152000) * t ^ 8 + (2807831 / 432000) * t ^ 10 + (-464747 / 512000) * t ^ 12 + (-246001 / 2073600) * t ^ 14 + (-1212047 / 41472000) * t ^ 18 + (95 / 663552) * t ^ 20 + (17147 / 360) * alpha * t ^ 4 + (-611782439 / 6912000) * alpha * t ^ 6 + (44730853 / 1152000) * alpha * t ^ 8 + (6972959 / 3456000) * alpha * t ^ 10 + (-3627631 / 41472000) * alpha * t ^ 12 + (58703 / 414720) * alpha * t ^ 14 + (1364849 / 41472000) * alpha * t ^ 18) * d_sq
theorem v54_30 (t : ℂ) : (momentPoly 54 z54 3 0).eval t = ((1701 / 160) * t ^ 3 + (279 / 160) * t ^ 5 + (-1187 / 480) * d * t ^ 3 + (1939 / 960) * d * t ^ 5 + (-47 / 576) * d * t ^ 9 + (-29283 / 800) * alpha * t ^ 3 + (147377 / 4800) * alpha * t ^ 5 + (10621 / 4800) * alpha * t ^ 9 + (1309 / 480) * alpha * d * t ^ 3 + (-1249 / 480) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_10, v53_20, v53_30]
  try simp only [phase53_00, phase53_10, phase53_20, phase53_30]
  try simp only [star_one, star_neg]
  linear_combination ((-1309 / 960) * t ^ 3 + (413 / 320) * t ^ 5 + (1 / 288) * d * t ^ 3 + (1 / 384) * d * t ^ 5) * alpha_sq + ((1 / 96) * t ^ 3 + (-1 / 288) * alpha * t ^ 3 + (1 / 1152) * alpha * t ^ 5) * d_sq
theorem v54_31 (t : ℂ) : (momentPoly 54 z54 3 1).eval t = ((152057 / 80) * t ^ 2 + (-3425621 / 1200) * t ^ 4 + (4729181 / 4800) * t ^ 6 + (135349 / 14400) * t ^ 10 + (-53 / 2) * d * t ^ 2 + (4943 / 240) * d * t ^ 4 + (4153 / 960) * d * t ^ 6 + (-47 / 576) * d * t ^ 10 + (-68847 / 40) * alpha * t ^ 2 + (3811843 / 1200) * alpha * t ^ 4 + (-6978293 / 4800) * alpha * t ^ 6 + (-38939 / 4800) * alpha * t ^ 10 + (371 / 48) * alpha * d * t ^ 2 + (-12727 / 3600) * alpha * d * t ^ 4 + (-53243 / 14400) * alpha * d * t ^ 6 + (-2849 / 14400) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_10, v53_11, v53_20, v53_21, v53_30, v53_31]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21, phase53_30, phase53_31]
  try simp only [star_one, star_neg]
  linear_combination ((-371 / 96) * t ^ 2 + (80633 / 19200) * t ^ 4 + (-17101 / 57600) * t ^ 6 + (-17563 / 345600) * t ^ 10) * alpha_sq + ((53 / 96) * t ^ 2 + (-4903 / 11520) * t ^ 4 + (-1097 / 11520) * t ^ 6 + (47 / 13824) * t ^ 10 + (-1319 / 11520) * alpha * t ^ 4 + (1259 / 11520) * alpha * t ^ 6) * d_sq
theorem v54_32 (t : ℂ) : (momentPoly 54 z54 3 2).eval t = (17014 * t + (-785925 / 32) * t ^ 3 + (97439909 / 24000) * t ^ 5 + (34782561 / 12800) * t ^ 7 + (164800073 / 192000) * t ^ 9 + (-18577537 / 576000) * t ^ 11 + (4322473 / 64000) * t ^ 13 + (-8507 / 6) * d * t + (76951 / 32) * d * t ^ 3 + (-6234977 / 7200) * d * t ^ 5 + (-1546577 / 38400) * d * t ^ 7 + (-1947161 / 23040) * d * t ^ 9 + (-699347 / 345600) * d * t ^ 11 + (71617 / 115200) * d * t ^ 13 + (-8507 / 2) * alpha * t + (164731 / 32) * alpha * t ^ 3 + (13580651 / 9000) * alpha * t ^ 5 + (-252408653 / 115200) * alpha * t ^ 7 + (-125267999 / 576000) * alpha * t ^ 9 + (18130111 / 1728000) * alpha * t ^ 11 + (-27515311 / 1728000) * alpha * t ^ 13 + (9163 / 32) * alpha * d * t ^ 3 + (-2600167 / 4800) * alpha * d * t ^ 5 + (3252043 / 12800) * alpha * d * t ^ 7 + (1017 / 2560) * alpha * d * t ^ 9 + (55601 / 115200) * alpha * d * t ^ 11 + (19411 / 23040) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_10, v53_11, v53_12, v53_20, v53_21, v53_22, v53_30, v53_31, v53_32]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22, phase53_30, phase53_31, phase53_32]
  try simp only [star_one, star_neg]
  linear_combination ((9163 / 64) * t ^ 3 + (-7768801 / 28800) * t ^ 5 + (3633719 / 28800) * t ^ 7 + (1410353 / 691200) * t ^ 11 + (-59059 / 46080) * t ^ 13 + (-35 / 96) * d * t ^ 3 + (-703 / 5400) * d * t ^ 5 + (1837 / 7200) * d * t ^ 7 + (17117 / 86400) * d * t ^ 9 + (73 / 16200) * d * t ^ 11 + (10621 / 1382400) * d * t ^ 13 + (1319 / 138240) * d ^ 2 * t ^ 7 + (-1249 / 138240) * d ^ 2 * t ^ 9) * alpha_sq + ((105 / 32) * t ^ 3 + (-14687 / 5760) * t ^ 5 + (-5257 / 7680) * t ^ 7 + (311 / 5760) * t ^ 9 + (47 / 6912) * t ^ 11 + (-35 / 96) * alpha * t ^ 3 + (5113 / 21600) * alpha * t ^ 5 + (9517 / 86400) * alpha * t ^ 7 + (-1 / 13824) * alpha * t ^ 9 + (4711 / 518400) * alpha * t ^ 11 + (-47 / 165888) * alpha * t ^ 13) * d_sq
theorem v54_33 (t : ℂ) : (momentPoly 54 z54 3 3).eval t = (918756 + (-4892221 / 2) * t ^ 2 + (926219931 / 400) * t ^ 4 + (-16094436883 / 15000) * t ^ 6 + (33053448373 / 80000) * t ^ 8 + (-10262217401 / 80000) * t ^ 10 + (1215591311 / 720000) * t ^ 12 + (-1001844539 / 720000) * t ^ 14 + (-9584101 / 270000) * t ^ 18 + (-16697 / 2) * d * t ^ 2 + (1030523 / 80) * d * t ^ 4 + (-2012253 / 1000) * d * t ^ 6 + (-21795151 / 9600) * d * t ^ 8 + (-12006121 / 48000) * d * t ^ 10 + (716183 / 48000) * d * t ^ 12 + (-1499963 / 48000) * d * t ^ 14) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_03, v53_10, v53_11, v53_12, v53_13, v53_20, v53_21, v53_22, v53_23, v53_30, v53_31, v53_32, v53_33]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23, phase53_30, phase53_31, phase53_32, phase53_33]
  try simp only [star_one, star_neg]
  linear_combination ((116879 / 96) * t ^ 2 + (-270153 / 160) * t ^ 4 + (-52636321 / 576000) * t ^ 6 + (56908597 / 115200) * t ^ 8 + (199613 / 3000) * t ^ 10 + (17819443 / 2304000) * t ^ 12 + (-6502651 / 1728000) * t ^ 14 + (-8601593 / 16588800) * t ^ 18 + (-17147 / 480) * d * t ^ 4 + (153199 / 4800) * d * t ^ 6 + (684197 / 19200) * d * t ^ 8 + (-1820107 / 57600) * d * t ^ 10 + (-17417 / 43200) * d * t ^ 12 + (10621 / 230400) * d * t ^ 14 + (157 / 1728) * d ^ 2 * t ^ 6 + (-16477 / 345600) * d ^ 2 * t ^ 8 + (-4439 / 115200) * d ^ 2 * t ^ 10 + (-2749 / 1382400) * d ^ 2 * t ^ 14) * alpha_sq + ((16697 / 96) * t ^ 2 + (-47593 / 160) * t ^ 4 + (1342093 / 12800) * t ^ 6 + (48569 / 6400) * t ^ 8 + (431809 / 38400) * t ^ 10 + (483299 / 1382400) * t ^ 12 + (-241301 / 1382400) * t ^ 14 + (2209 / 663552) * t ^ 18) * d_sq
theorem v54_34 (t : ℂ) : (momentPoly 54 z54 3 4).eval t = (3573579 * t + (-122626755 / 16) * t ^ 3 + (1010439047 / 250) * t ^ 5 + (798429810999 / 3200000) * t ^ 7 + (8135254129237 / 38400000) * t ^ 9 + (-484312037101 / 1200000) * t ^ 11 + (441955059253 / 15360000) * t ^ 13 + (-969590008237 / 28800000) * t ^ 15 + (-208514630131 / 76800000) * t ^ 17 + (38709080969 / 43200000) * t ^ 19 + (-232150498103 / 230400000) * t ^ 21 + (-5076986243 / 76800000) * t ^ 25 + (-1191193 / 4) * d * t + (60032773 / 80) * d * t ^ 3 + (-1442912527 / 2400) * d * t ^ 5 + (1074692111071 / 5760000) * d * t ^ 7 + (-1923843121367 / 23040000) * d * t ^ 9 + (245837360549 / 5760000) * d * t ^ 11 + (418229973799 / 138240000) * d * t ^ 13 + (-1736684719 / 5760000) * d * t ^ 15 + (1724752543 / 27648000) * d * t ^ 17 + (-2594087309 / 51840000) * d * t ^ 19 + (8144284573 / 138240000) * d * t ^ 21 + (13701103 / 27648000) * d * t ^ 25 + (3573579 / 4) * alpha * t + (-128513713 / 80) * alpha * t ^ 3 + (-649803599 / 12000) * alpha * t ^ 5 + (36089667836861 / 28800000) * alpha * t ^ 7 + (-15163252628783 / 38400000) * alpha * t ^ 9 + (-759527763193 / 9600000) * alpha * t ^ 11 + (-184759661981 / 46080000) * alpha * t ^ 13 + (-180726170237 / 28800000) * alpha * t ^ 15 + (-1155309641959 / 691200000) * alpha * t ^ 17 + (78047402899 / 259200000) * alpha * t ^ 19 + (-122241576289 / 691200000) * alpha * t ^ 21 + (-30160705061 / 2073600000) * alpha * t ^ 25 + (-7148449 / 80) * alpha * d * t ^ 3 + (18839639 / 75) * alpha * d * t ^ 5 + (-1352817238967 / 5760000) * alpha * d * t ^ 7 + (582387657563 / 7680000) * alpha * d * t ^ 9 + (-2990329379 / 576000) * alpha * d * t ^ 11 + (279234901007 / 138240000) * alpha * d * t ^ 13 + (6816510479 / 17280000) * alpha * d * t ^ 15 + (-333191051 / 9216000) * alpha * d * t ^ 17 + (-8887121 / 270000) * alpha * d * t ^ 19 + (1650326039 / 46080000) * alpha * d * t ^ 21 + (-22126801 / 27648000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_03, v53_04, v53_10, v53_11, v53_12, v53_13, v53_14, v53_20, v53_21, v53_22, v53_23, v53_24, v53_30, v53_31, v53_32, v53_33, v53_34]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24, phase53_30, phase53_31, phase53_32, phase53_33, phase53_34]
  try simp only [star_one, star_neg]
  linear_combination ((7148449 / 160) * t ^ 3 + (-300604649 / 2400) * t ^ 5 + (1346639690467 / 11520000) * t ^ 7 + (-3485942898773 / 92160000) * t ^ 9 + (7006435967 / 1843200) * t ^ 11 + (-566028338303 / 184320000) * t ^ 13 + (198316571873 / 276480000) * t ^ 15 + (544083683 / 9216000) * t ^ 17 + (29743377727 / 1658880000) * t ^ 19 + (-550014983 / 30720000) * t ^ 21 + (67321969 / 55296000) * t ^ 25 + (-5461 / 48) * d * t ^ 3 + (91837 / 28800) * d * t ^ 5 + (37513021 / 230400) * d * t ^ 7 + (631661437 / 9216000) * d * t ^ 9 + (-1461475607 / 13824000) * d * t ^ 11 + (-651044887 / 55296000) * d * t ^ 13 + (-85090349 / 27648000) * d * t ^ 15 + (-31018511 / 82944000) * d * t ^ 17 + (-152967043 / 497664000) * d * t ^ 19 + (2999209 / 41472000) * d * t ^ 21 + (201799 / 13271040) * d * t ^ 25 + (410209 / 69120) * d ^ 2 * t ^ 7 + (-608271239 / 55296000) * d ^ 2 * t ^ 9 + (133225259 / 27648000) * d ^ 2 * t ^ 11 + (26782111 / 110592000) * d ^ 2 * t ^ 13 + (-124603 / 165888000) * d ^ 2 * t ^ 15 + (19411 / 2211840) * d ^ 2 * t ^ 17 + (25061 / 2654208) * d ^ 2 * t ^ 19 + (-98611 / 20736000) * d ^ 2 * t ^ 21) * alpha_sq + ((16383 / 16) * t ^ 3 + (-1512761 / 960) * t ^ 5 + (218687041 / 1152000) * t ^ 7 + (123187247 / 368640) * t ^ 9 + (149052181 / 4608000) * t ^ 11 + (-39605933 / 6144000) * t ^ 13 + (83126299 / 27648000) * t ^ 15 + (-19411 / 368640) * t ^ 17 + (-4215251 / 165888000) * t ^ 19 + (777013 / 27648000) * t ^ 21 + (5461 / 48) * alpha * t ^ 3 + (-3410137 / 28800) * alpha * t ^ 5 + (-50204711 / 691200) * alpha * t ^ 7 + (549689963 / 9216000) * alpha * t ^ 9 + (65800097 / 4608000) * alpha * t ^ 11 + (30352979 / 11059200) * alpha * t ^ 13 + (2895721 / 5529600) * alpha * t ^ 15 + (250723 / 16588800) * alpha * t ^ 17 + (68825683 / 497664000) * alpha * t ^ 19 + (708539 / 82944000) * alpha * t ^ 21 + (-4465 / 7962624) * alpha * t ^ 25) * d_sq
theorem v54_40 (t : ℂ) : (momentPoly 54 z54 4 0).eval t = ((-1737521 / 3000) * t ^ 4 + (5443471 / 4000) * t ^ 6 + (-75579361 / 96000) * t ^ 8 + (3377039 / 72000) * t ^ 10 + (-197441 / 32000) * t ^ 16 + (-61 / 320) * d * t ^ 4 + (-539 / 240) * d * t ^ 6 + (413 / 320) * d * t ^ 8 + (-47 / 144) * d * t ^ 10 + (-2808911 / 4000) * alpha * t ^ 4 + (12785951 / 12000) * alpha * t ^ 6 + (-6628687 / 16000) * alpha * t ^ 8 + (192331 / 4000) * alpha * t ^ 10 + (-470783 / 48000) * alpha * t ^ 16 + (57361 / 4800) * alpha * d * t ^ 4 + (-13331 / 1200) * alpha * d * t ^ 6 + (3913 / 11520) * alpha * d * t ^ 8 + (-25963 / 43200) * alpha * d * t ^ 10 + (-95 / 6912) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_10, v53_20, v53_30, v53_40]
  try simp only [phase53_00, phase53_10, phase53_20, phase53_30, phase53_40]
  try simp only [star_one, star_neg]
  linear_combination ((-57361 / 9600) * t ^ 4 + (154037 / 28800) * t ^ 6 + (17563 / 86400) * t ^ 10 + (1319 / 5760) * d * t ^ 4 + (1 / 96) * d * t ^ 6 + (-413 / 1920) * d * t ^ 8 + (-1 / 1728) * d ^ 2 * t ^ 6 + (1 / 13824) * d ^ 2 * t ^ 8) * alpha_sq + ((1177 / 5760) * t ^ 4 + (-359 / 1920) * t ^ 6 + (-1 / 4608) * t ^ 8 + (47 / 3456) * t ^ 10 + (-1319 / 5760) * alpha * t ^ 4 + (1259 / 5760) * alpha * t ^ 6) * d_sq
theorem v54_41 (t : ℂ) : (momentPoly 54 z54 4 1).eval t = ((35721 / 16) * t ^ 3 + (-176991649 / 96000) * t ^ 5 + (11639849 / 48000) * t ^ 7 + (-104002589 / 192000) * t ^ 9 + (3470591 / 144000) * t ^ 11 + (75901 / 64000) * t ^ 17 + (-8309 / 16) * d * t ^ 3 + (279485423 / 288000) * d * t ^ 5 + (-24604741 / 48000) * d * t ^ 7 + (26048543 / 576000) * d * t ^ 9 + (4674803 / 432000) * d * t ^ 11 + (349099 / 576000) * d * t ^ 17 + (-614943 / 80) * alpha * t ^ 3 + (3611002519 / 288000) * alpha * t ^ 5 + (-203065853 / 48000) * alpha * t ^ 7 + (-125241781 / 576000) * alpha * t ^ 9 + (-182099281 / 432000) * alpha * t ^ 11 + (-22303139 / 1728000) * alpha * t ^ 17 + (9163 / 16) * alpha * d * t ^ 3 + (-298313399 / 288000) * alpha * d * t ^ 5 + (61114879 / 144000) * alpha * d * t ^ 7 + (23265161 / 576000) * alpha * d * t ^ 9 + (-527059 / 432000) * alpha * d * t ^ 11 + (1388599 / 1728000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_10, v53_11, v53_20, v53_21, v53_30, v53_31, v53_40, v53_41]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21, phase53_30, phase53_31, phase53_40, phase53_41]
  try simp only [star_one, star_neg]
  linear_combination ((-9163 / 32) * t ^ 3 + (324458681 / 576000) * t ^ 5 + (-112972433 / 384000) * t ^ 7 + (3804781 / 192000) * t ^ 9 + (-966383 / 288000) * t ^ 11 + (470783 / 1152000) * t ^ 17 + (35 / 48) * d * t ^ 3 + (5 / 1728) * d * t ^ 5 + (-11821 / 23040) * d * t ^ 7 + (-3133 / 17280) * d * t ^ 9 + (-47 / 10368) * d * t ^ 11 + (-95 / 55296) * d * t ^ 17 + (-1319 / 138240) * d ^ 2 * t ^ 7 + (1249 / 138240) * d ^ 2 * t ^ 9) * alpha_sq + ((35 / 16) * t ^ 3 + (-2507 / 1440) * t ^ 5 + (-7369 / 23040) * t ^ 7 + (-311 / 5760) * t ^ 9 + (47 / 1728) * t ^ 11 + (-35 / 48) * alpha * t ^ 3 + (9329 / 43200) * alpha * t ^ 5 + (54719 / 115200) * alpha * t ^ 7 + (-551 / 34560) * alpha * t ^ 9 + (221 / 8100) * alpha * t ^ 11 + (95 / 165888) * alpha * t ^ 17) * d_sq
theorem v54_42 (t : ℂ) : (momentPoly 54 z54 4 2).eval t = ((47903693 / 120) * t ^ 2 + (-1143615061 / 1200) * t ^ 4 + (1406269525229 / 1920000) * t ^ 6 + (-363793228357 / 1920000) * t ^ 8 + (22602443509 / 1152000) * t ^ 10 + (-3020968771 / 320000) * t ^ 12 + (1161193241 / 1080000) * t ^ 14 + (121397167 / 540000) * t ^ 18 + (-4359445649 / 17280000) * t ^ 20 + (-16697 / 3) * d * t ^ 2 + (128518 / 15) * d * t ^ 4 + (-1750354487 / 1152000) * d * t ^ 6 + (-158452337 / 128000) * d * t ^ 8 + (-167654501 / 576000) * d * t ^ 10 + (54290399 / 1152000) * d * t ^ 12 + (-1563527 / 96000) * d * t ^ 14 + (239093 / 1152000) * d * t ^ 18 + (-127523 / 576000) * d * t ^ 20 + (-7229801 / 20) * alpha * t ^ 2 + (590008069 / 600) * alpha * t ^ 4 + (-5125143132343 / 5760000) * alpha * t ^ 6 + (538376520773 / 1920000) * alpha * t ^ 8 + (-27170304953 / 1152000) * alpha * t ^ 10 + (102302985103 / 8640000) * alpha * t ^ 12 + (-101819573 / 135000) * alpha * t ^ 14 + (-719278489 / 4320000) * alpha * t ^ 18 + (79123343 / 640000) * alpha * t ^ 20 + (116879 / 72) * alpha * d * t ^ 2 + (-4475807 / 3600) * alpha * d * t ^ 4 + (-6356761663 / 3456000) * alpha * d * t ^ 6 + (4243426127 / 3456000) * alpha * d * t ^ 8 + (96876749 / 576000) * alpha * d * t ^ 10 + (63451949 / 1152000) * alpha * d * t ^ 12 + (22284089 / 2592000) * alpha * d * t ^ 14 + (898279 / 414720) * alpha * d * t ^ 18 + (36023 / 576000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_10, v53_11, v53_12, v53_20, v53_21, v53_22, v53_30, v53_31, v53_32, v53_40, v53_41, v53_42]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22, phase53_30, phase53_31, phase53_32, phase53_40, phase53_41, phase53_42]
  try simp only [star_one, star_neg]
  linear_combination ((-116879 / 144) * t ^ 2 + (1048229 / 600) * t ^ 4 + (-2348129509 / 2304000) * t ^ 6 + (9424819 / 138240) * t ^ 8 + (-34387601 / 13824000) * t ^ 10 + (42029771 / 1728000) * t ^ 12 + (-5991553 / 864000) * t ^ 14 + (212147 / 184320) * t ^ 18 + (-4564147 / 2304000) * d * t ^ 6 + (3980387 / 2304000) * d * t ^ 8 + (5619217 / 3456000) * d * t ^ 10 + (-12372607 / 6912000) * d * t ^ 12 + (389467 / 864000) * d * t ^ 14 + (-749579 / 6912000) * d * t ^ 18 + (127523 / 3456000) * d * t ^ 20 + (11123 / 518400) * d ^ 2 * t ^ 8 + (-56719 / 2764800) * d ^ 2 * t ^ 10 + (1097 / 1658880) * d ^ 2 * t ^ 12 + (-5897 / 6220800) * d ^ 2 * t ^ 14 + (95 / 497664) * d ^ 2 * t ^ 18 + (-95 / 1990656) * d ^ 2 * t ^ 20) * alpha_sq + ((16697 / 144) * t ^ 2 + (-63739 / 360) * t ^ 4 + (64091819 / 2304000) * t ^ 6 + (32440621 / 1152000) * t ^ 8 + (2807831 / 432000) * t ^ 10 + (-464747 / 512000) * t ^ 12 + (-246001 / 2073600) * t ^ 14 + (-1212047 / 41472000) * t ^ 18 + (95 / 663552) * t ^ 20 + (-17147 / 360) * alpha * t ^ 4 + (611782439 / 6912000) * alpha * t ^ 6 + (-44730853 / 1152000) * alpha * t ^ 8 + (-6972959 / 3456000) * alpha * t ^ 10 + (3627631 / 41472000) * alpha * t ^ 12 + (-58703 / 414720) * alpha * t ^ 14 + (-1364849 / 41472000) * alpha * t ^ 18) * d_sq
theorem v54_43 (t : ℂ) : (momentPoly 54 z54 4 3).eval t = (3573579 * t + (-122626755 / 16) * t ^ 3 + (1010439047 / 250) * t ^ 5 + (798429810999 / 3200000) * t ^ 7 + (8135254129237 / 38400000) * t ^ 9 + (-484312037101 / 1200000) * t ^ 11 + (441955059253 / 15360000) * t ^ 13 + (-969590008237 / 28800000) * t ^ 15 + (-208514630131 / 76800000) * t ^ 17 + (38709080969 / 43200000) * t ^ 19 + (-232150498103 / 230400000) * t ^ 21 + (-5076986243 / 76800000) * t ^ 25 + (-1191193 / 4) * d * t + (60032773 / 80) * d * t ^ 3 + (-1442912527 / 2400) * d * t ^ 5 + (1074692111071 / 5760000) * d * t ^ 7 + (-1923843121367 / 23040000) * d * t ^ 9 + (245837360549 / 5760000) * d * t ^ 11 + (418229973799 / 138240000) * d * t ^ 13 + (-1736684719 / 5760000) * d * t ^ 15 + (1724752543 / 27648000) * d * t ^ 17 + (-2594087309 / 51840000) * d * t ^ 19 + (8144284573 / 138240000) * d * t ^ 21 + (13701103 / 27648000) * d * t ^ 25 + (-3573579 / 4) * alpha * t + (128513713 / 80) * alpha * t ^ 3 + (649803599 / 12000) * alpha * t ^ 5 + (-36089667836861 / 28800000) * alpha * t ^ 7 + (15163252628783 / 38400000) * alpha * t ^ 9 + (759527763193 / 9600000) * alpha * t ^ 11 + (184759661981 / 46080000) * alpha * t ^ 13 + (180726170237 / 28800000) * alpha * t ^ 15 + (1155309641959 / 691200000) * alpha * t ^ 17 + (-78047402899 / 259200000) * alpha * t ^ 19 + (122241576289 / 691200000) * alpha * t ^ 21 + (30160705061 / 2073600000) * alpha * t ^ 25 + (7148449 / 80) * alpha * d * t ^ 3 + (-18839639 / 75) * alpha * d * t ^ 5 + (1352817238967 / 5760000) * alpha * d * t ^ 7 + (-582387657563 / 7680000) * alpha * d * t ^ 9 + (2990329379 / 576000) * alpha * d * t ^ 11 + (-279234901007 / 138240000) * alpha * d * t ^ 13 + (-6816510479 / 17280000) * alpha * d * t ^ 15 + (333191051 / 9216000) * alpha * d * t ^ 17 + (8887121 / 270000) * alpha * d * t ^ 19 + (-1650326039 / 46080000) * alpha * d * t ^ 21 + (22126801 / 27648000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_03, v53_10, v53_11, v53_12, v53_13, v53_20, v53_21, v53_22, v53_23, v53_30, v53_31, v53_32, v53_33, v53_40, v53_41, v53_42, v53_43]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23, phase53_30, phase53_31, phase53_32, phase53_33, phase53_40, phase53_41, phase53_42, phase53_43]
  try simp only [star_one, star_neg]
  linear_combination ((7148449 / 160) * t ^ 3 + (-300604649 / 2400) * t ^ 5 + (1346639690467 / 11520000) * t ^ 7 + (-3485942898773 / 92160000) * t ^ 9 + (7006435967 / 1843200) * t ^ 11 + (-566028338303 / 184320000) * t ^ 13 + (198316571873 / 276480000) * t ^ 15 + (544083683 / 9216000) * t ^ 17 + (29743377727 / 1658880000) * t ^ 19 + (-550014983 / 30720000) * t ^ 21 + (67321969 / 55296000) * t ^ 25 + (-5461 / 48) * d * t ^ 3 + (91837 / 28800) * d * t ^ 5 + (37513021 / 230400) * d * t ^ 7 + (631661437 / 9216000) * d * t ^ 9 + (-1461475607 / 13824000) * d * t ^ 11 + (-651044887 / 55296000) * d * t ^ 13 + (-85090349 / 27648000) * d * t ^ 15 + (-31018511 / 82944000) * d * t ^ 17 + (-152967043 / 497664000) * d * t ^ 19 + (2999209 / 41472000) * d * t ^ 21 + (201799 / 13271040) * d * t ^ 25 + (410209 / 69120) * d ^ 2 * t ^ 7 + (-608271239 / 55296000) * d ^ 2 * t ^ 9 + (133225259 / 27648000) * d ^ 2 * t ^ 11 + (26782111 / 110592000) * d ^ 2 * t ^ 13 + (-124603 / 165888000) * d ^ 2 * t ^ 15 + (19411 / 2211840) * d ^ 2 * t ^ 17 + (25061 / 2654208) * d ^ 2 * t ^ 19 + (-98611 / 20736000) * d ^ 2 * t ^ 21) * alpha_sq + ((16383 / 16) * t ^ 3 + (-1512761 / 960) * t ^ 5 + (218687041 / 1152000) * t ^ 7 + (123187247 / 368640) * t ^ 9 + (149052181 / 4608000) * t ^ 11 + (-39605933 / 6144000) * t ^ 13 + (83126299 / 27648000) * t ^ 15 + (-19411 / 368640) * t ^ 17 + (-4215251 / 165888000) * t ^ 19 + (777013 / 27648000) * t ^ 21 + (-5461 / 48) * alpha * t ^ 3 + (3410137 / 28800) * alpha * t ^ 5 + (50204711 / 691200) * alpha * t ^ 7 + (-549689963 / 9216000) * alpha * t ^ 9 + (-65800097 / 4608000) * alpha * t ^ 11 + (-30352979 / 11059200) * alpha * t ^ 13 + (-2895721 / 5529600) * alpha * t ^ 15 + (-250723 / 16588800) * alpha * t ^ 17 + (-68825683 / 497664000) * alpha * t ^ 19 + (-708539 / 82944000) * alpha * t ^ 21 + (4465 / 7962624) * alpha * t ^ 25) * d_sq
theorem v54_44 (t : ℂ) : (momentPoly 54 z54 4 4).eval t = (192973266 + (-678593860) * t ^ 2 + (47712201061 / 50) * t ^ 4 + (-5648473781339 / 7500) * t ^ 6 + (31471781789819149 / 72000000) * t ^ 8 + (-4722908038209547 / 24000000) * t ^ 10 + (10660028806571021 / 230400000) * t ^ 12 + (-6540440829469349 / 1728000000) * t ^ 14 + (1433485726719173 / 768000000) * t ^ 16 + (-56262670572061 / 288000000) * t ^ 18 + (268489077642713 / 3456000000) * t ^ 20 + (-40042683008647 / 576000000) * t ^ 22 + (52311641647019 / 1728000000) * t ^ 24 + (-27391354157 / 10125000) * t ^ 26 + (5660583296237 / 20736000000) * t ^ 32 + (-2316020) * d * t ^ 2 + (159255439 / 30) * d * t ^ 4 + (-718402337 / 250) * d * t ^ 6 + (-19109638796779 / 28800000) * d * t ^ 8 + (4564481699117 / 14400000) * d * t ^ 10 + (16343836126321 / 76800000) * d * t ^ 12 + (-461953812763 / 69120000) * d * t ^ 14 + (8726461425953 / 460800000) * d * t ^ 16 + (402366123119 / 172800000) * d * t ^ 18 + (-1232660855263 / 2073600000) * d * t ^ 20 + (234833497913 / 345600000) * d * t ^ 22 + (78613013 / 23040000) * d * t ^ 24 + (1588167463 / 43200000) * d * t ^ 26 + (8944877 / 11059200) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_03, v53_04, v53_10, v53_11, v53_12, v53_13, v53_14, v53_20, v53_21, v53_22, v53_23, v53_24, v53_30, v53_31, v53_32, v53_33, v53_34, v53_40, v53_41, v53_42, v53_43, v53_44]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24, phase53_30, phase53_31, phase53_32, phase53_33, phase53_34, phase53_40, phase53_41, phase53_42, phase53_43, phase53_44]
  try simp only [star_one, star_neg]
  linear_combination ((4053035 / 12) * t ^ 2 + (-13916343 / 20) * t ^ 4 + (4501502861 / 24000) * t ^ 6 + (17940889626329 / 57600000) * t ^ 8 + (-627177459041 / 6400000) * t ^ 10 + (-10678617272231 / 345600000) * t ^ 12 + (-1497434449543 / 103680000) * t ^ 14 + (370960298941 / 172800000) * t ^ 16 + (-122496729053 / 691200000) * t ^ 18 + (166461941389 / 345600000) * t ^ 20 + (-25784767649 / 345600000) * t ^ 22 + (2229665261 / 259200000) * t ^ 26 + (-2649871 / 180) * d * t ^ 4 + (32040071 / 1200) * d * t ^ 6 + (92190404783 / 34560000) * d * t ^ 8 + (-50422177337 / 1920000) * d * t ^ 10 + (1051938656131 / 92160000) * d * t ^ 12 + (-45975920629 / 414720000) * d * t ^ 14 + (204504531731 / 552960000) * d * t ^ 16 + (-12358553047 / 207360000) * d * t ^ 18 + (-32878443421 / 2488320000) * d * t ^ 20 + (1162190311 / 82944000) * d * t ^ 22 + (-78613013 / 138240000) * d * t ^ 24 + (201799 / 1658880) * d * t ^ 26 + (-8944877 / 66355200) * d * t ^ 32 + (32557 / 864) * d ^ 2 * t ^ 6 + (-2984369 / 86400) * d ^ 2 * t ^ 8 + (-22966813 / 691200) * d ^ 2 * t ^ 10 + (1358230427 / 55296000) * d ^ 2 * t ^ 12 + (351652699 / 82944000) * d ^ 2 * t ^ 14 + (360447583 / 331776000) * d ^ 2 * t ^ 16 + (1658569 / 9216000) * d ^ 2 * t ^ 18 + (211337 / 2488320) * d ^ 2 * t ^ 20 + (-69173 / 2048000) * d ^ 2 * t ^ 22 + (4046203 / 995328000) * d ^ 2 * t ^ 24 + (-112043 / 29859840) * d ^ 2 * t ^ 26 + (-9025 / 95551488) * d ^ 2 * t ^ 32) * alpha_sq + ((579005 / 12) * t ^ 2 + (-7354949 / 60) * t ^ 4 + (1407963289 / 14400) * t ^ 6 + (-1004195612321 / 34560000) * t ^ 8 + (157468985861 / 11520000) * t ^ 10 + (-2053279515457 / 276480000) * t ^ 12 + (-309558979297 / 414720000) * t ^ 14 + (25869260263 / 184320000) * t ^ 16 + (-46678499 / 2764800) * t ^ 18 + (1242702541 / 207360000) * t ^ 20 + (-2491445611 / 276480000) * t ^ 22 + (-4046203 / 331776000) * t ^ 24 + (-49131559 / 248832000) * t ^ 26 + (9025 / 31850496) * t ^ 32) * d_sq
#print axioms v54_00
#print axioms v54_11
#print axioms v54_22
#print axioms v54_33
#print axioms v54_44
end PhotonCertA
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z55 : Fin 55 → ℂ := Fin.snoc z54 (r ^ 3 * phiPlus)
theorem v55_00 (t : ℂ) : (momentPoly 55 z55 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00]
  try simp only [phase53_00]
  try simp only [star_one, star_neg]
  ring
theorem v55_01 (t : ℂ) : (momentPoly 55 z55 0 1).eval t = (1 * t + (-1 / 8) * d * t + (5 / 24) * alpha * t) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01]
  try simp only [phase53_00, phase53_01]
  try simp only [star_one, star_neg]
  ring
theorem v55_02 (t : ℂ) : (momentPoly 55 z55 0 2).eval t = ((3839 / 240) * t ^ 2 + (-2963 / 480) * t ^ 4 + (-1 / 4) * d * t ^ 2 + (1289 / 120) * alpha * t ^ 2 + (-413 / 40) * alpha * t ^ 4 + (-1 / 16) * alpha * d * t ^ 2 + (1 / 96) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02]
  try simp only [phase53_00, phase53_01, phase53_02]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 48) * t ^ 2) * alpha_sq + ((1 / 144) * t ^ 2) * d_sq
theorem v55_03 (t : ℂ) : (momentPoly 55 z55 0 3).eval t = ((8521 / 320) * t ^ 3 + (269 / 320) * t ^ 5 + (-1913 / 480) * d * t ^ 3 + (213 / 80) * d * t ^ 5 + (-47 / 384) * d * t ^ 9 + (30873 / 800) * alpha * t ^ 3 + (-36073 / 1200) * alpha * t ^ 5 + (-67301 / 28800) * alpha * t ^ 9 + (-1299 / 320) * alpha * d * t ^ 3 + (1249 / 320) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_03]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03]
  try simp only [star_one, star_neg]
  linear_combination ((-433 / 320) * t ^ 3 + (413 / 320) * t ^ 5 + (7 / 1152) * d * t ^ 3 + (1 / 576) * d * t ^ 5) * alpha_sq + ((1 / 48) * t ^ 3 + (7 / 1152) * alpha * t ^ 3 + (-1 / 576) * alpha * t ^ 5) * d_sq
theorem v55_04 (t : ℂ) : (momentPoly 55 z55 0 4).eval t = ((-1298833 / 4000) * t ^ 4 + (9802757 / 8000) * t ^ 6 + (-79685861 / 96000) * t ^ 8 + (4446319 / 72000) * t ^ 10 + (-3001813 / 576000) * t ^ 16 + (-3193 / 960) * d * t ^ 4 + (-1857 / 640) * d * t ^ 6 + (1239 / 640) * d * t ^ 8 + (-47 / 96) * d * t ^ 10 + (2882677 / 3000) * alpha * t ^ 4 + (-60096079 / 48000) * alpha * t ^ 6 + (1411953 / 4000) * alpha * t ^ 8 + (-874427 / 18000) * alpha * t ^ 10 + (470783 / 48000) * alpha * t ^ 16 + (-253997 / 14400) * alpha * d * t ^ 4 + (76081 / 4800) * alpha * d * t ^ 6 + (-573 / 1280) * alpha * d * t ^ 8 + (4723 / 4800) * alpha * d * t ^ 10 + (95 / 4608) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_03, v54_04]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04]
  try simp only [star_one, star_neg]
  linear_combination ((-9761 / 1600) * t ^ 4 + (147377 / 28800) * t ^ 6 + (3523 / 14400) * t ^ 10 + (1309 / 2880) * d * t ^ 4 + (-1199 / 5760) * d * t ^ 6 + (-413 / 1920) * d * t ^ 8 + (-7 / 6912) * d ^ 2 * t ^ 6 + (1 / 6912) * d ^ 2 * t ^ 8) * alpha_sq + ((1187 / 2880) * t ^ 4 + (-427 / 1280) * t ^ 6 + (-1 / 2304) * t ^ 8 + (47 / 1728) * t ^ 10 + (1309 / 2880) * alpha * t ^ 4 + (-1259 / 2880) * alpha * t ^ 6) * d_sq
theorem v55_10 (t : ℂ) : (momentPoly 55 z55 1 0).eval t = (1 * t + (-1 / 8) * d * t + (-5 / 24) * alpha * t) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_10]
  try simp only [phase53_00, phase53_10]
  try simp only [star_one, star_neg]
  ring
theorem v55_11 (t : ℂ) : (momentPoly 55 z55 1 1).eval t = (55 + (-539 / 12) * t ^ 2 + (-1 / 4) * d * t ^ 2) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_10, v54_11]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 48) * t ^ 2) * alpha_sq + ((1 / 144) * t ^ 2) * d_sq
theorem v55_12 (t : ℂ) : (momentPoly 55 z55 1 2).eval t = (109 * t + (-21563 / 320) * t ^ 3 + (-13081 / 960) * t ^ 5 + (-109 / 8) * d * t + (10763 / 960) * d * t ^ 3 + (289 / 320) * d * t ^ 5 + (545 / 24) * alpha * t + (-30569 / 2880) * alpha * t ^ 3 + (-28781 / 2880) * alpha * t ^ 5 + (-433 / 320) * alpha * d * t ^ 3 + (1249 / 960) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_10, v54_11, v54_12]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12]
  try simp only [star_one, star_neg]
  linear_combination ((433 / 960) * t ^ 3 + (-413 / 960) * t ^ 5 + (-7 / 3456) * d * t ^ 3 + (-1 / 1728) * d * t ^ 5) * alpha_sq + ((1 / 48) * t ^ 3 + (7 / 3456) * alpha * t ^ 3 + (-1 / 1728) * alpha * t ^ 5) * d_sq
theorem v55_13 (t : ℂ) : (momentPoly 55 z55 1 3).eval t = ((103653 / 40) * t ^ 2 + (-3084787 / 960) * t ^ 4 + (713641 / 960) * t ^ 6 + (77639 / 5760) * t ^ 10 + (-81 / 2) * d * t ^ 2 + (28703 / 960) * d * t ^ 4 + (1839 / 320) * d * t ^ 6 + (-47 / 384) * d * t ^ 10 + (34803 / 20) * alpha * t ^ 2 + (-14722097 / 4800) * alpha * t ^ 4 + (6387013 / 4800) * alpha * t ^ 6 + (230059 / 28800) * alpha * t ^ 10 + (-81 / 8) * alpha * d * t ^ 2 + (51587 / 14400) * alpha * d * t ^ 4 + (26909 / 4800) * alpha * d * t ^ 6 + (983 / 3200) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_03, v54_10, v54_11, v54_12, v54_13]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13]
  try simp only [star_one, star_neg]
  linear_combination ((-27 / 8) * t ^ 2 + (102757 / 28800) * t ^ 4 + (-5369 / 38400) * t ^ 6 + (-3523 / 57600) * t ^ 10) * alpha_sq + ((9 / 8) * t ^ 2 + (-4903 / 5760) * t ^ 4 + (-3913 / 23040) * t ^ 6 + (47 / 6912) * t ^ 10 + (1309 / 5760) * alpha * t ^ 4 + (-1259 / 5760) * alpha * t ^ 6) * d_sq
theorem v55_14 (t : ℂ) : (momentPoly 55 z55 1 4).eval t = ((911747 / 160) * t ^ 3 + (-929963179 / 192000) * t ^ 5 + (30017929 / 96000) * t ^ 7 + (-287917889 / 384000) * t ^ 9 + (18817331 / 288000) * t ^ 11 + (1058119 / 1152000) * t ^ 17 + (-204691 / 240) * d * t ^ 3 + (822833269 / 576000) * d * t ^ 5 + (-65923273 / 96000) * d * t ^ 7 + (28235093 / 384000) * d * t ^ 9 + (4404553 / 288000) * d * t ^ 11 + (302099 / 384000) * d * t ^ 17 + (3303411 / 400) * alpha * t ^ 3 + (-7031905381 / 576000) * alpha * t ^ 5 + (111961479 / 32000) * alpha * t ^ 7 + (42627203 / 384000) * alpha * t ^ 9 + (356760989 / 864000) * alpha * t ^ 11 + (40621481 / 3456000) * alpha * t ^ 17 + (-138993 / 160) * alpha * d * t ^ 3 + (297170999 / 192000) * alpha * d * t ^ 5 + (-20164843 / 32000) * alpha * d * t ^ 7 + (-6755937 / 128000) * alpha * d * t ^ 9 + (187603 / 96000) * alpha * d * t ^ 11 + (-1388599 / 1152000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_03, v54_04, v54_10, v54_11, v54_12, v54_13, v54_14]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14]
  try simp only [star_one, star_neg]
  linear_combination ((-46331 / 160) * t ^ 3 + (161643853 / 288000) * t ^ 5 + (-82568881 / 288000) * t ^ 7 + (6628687 / 384000) * t ^ 9 + (-966383 / 288000) * t ^ 11 + (470783 / 1152000) * t ^ 17 + (749 / 576) * d * t ^ 3 + (-36503 / 69120) * d * t ^ 5 + (-34133 / 69120) * d * t ^ 7 + (-6269 / 30720) * d * t ^ 9 + (-329 / 41472) * d * t ^ 11 + (-95 / 82944) * d * t ^ 17 + (-1309 / 69120) * d ^ 2 * t ^ 7 + (1249 / 69120) * d ^ 2 * t ^ 9) * alpha_sq + ((107 / 24) * t ^ 3 + (-15781 / 4608) * t ^ 5 + (-13147 / 23040) * t ^ 7 + (-311 / 2880) * t ^ 9 + (47 / 864) * t ^ 11 + (749 / 576) * alpha * t ^ 3 + (-96749 / 345600) * alpha * t ^ 5 + (-11777 / 12800) * alpha * t ^ 7 + (7861 / 276480) * alpha * t ^ 9 + (-60151 / 1036800) * alpha * t ^ 11 + (-95 / 82944) * alpha * t ^ 17) * d_sq
theorem v55_20 (t : ℂ) : (momentPoly 55 z55 2 0).eval t = ((3839 / 240) * t ^ 2 + (-2963 / 480) * t ^ 4 + (-1 / 4) * d * t ^ 2 + (-1289 / 120) * alpha * t ^ 2 + (413 / 40) * alpha * t ^ 4 + (1 / 16) * alpha * d * t ^ 2 + (-1 / 96) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_10, v54_20]
  try simp only [phase53_00, phase53_10, phase53_20]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 48) * t ^ 2) * alpha_sq + ((1 / 144) * t ^ 2) * d_sq
theorem v55_21 (t : ℂ) : (momentPoly 55 z55 2 1).eval t = (109 * t + (-21563 / 320) * t ^ 3 + (-13081 / 960) * t ^ 5 + (-109 / 8) * d * t + (10763 / 960) * d * t ^ 3 + (289 / 320) * d * t ^ 5 + (-545 / 24) * alpha * t + (30569 / 2880) * alpha * t ^ 3 + (28781 / 2880) * alpha * t ^ 5 + (433 / 320) * alpha * d * t ^ 3 + (-1249 / 960) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_10, v54_11, v54_20, v54_21]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21]
  try simp only [star_one, star_neg]
  linear_combination ((433 / 960) * t ^ 3 + (-413 / 960) * t ^ 5 + (-7 / 3456) * d * t ^ 3 + (-1 / 1728) * d * t ^ 5) * alpha_sq + ((1 / 48) * t ^ 3 + (-7 / 3456) * alpha * t ^ 3 + (1 / 1728) * alpha * t ^ 5) * d_sq
theorem v55_22 (t : ℂ) : (momentPoly 55 z55 2 2).eval t = (5995 + (-9702) * t ^ 2 + (60867037 / 14400) * t ^ 4 + (-19742393 / 28800) * t ^ 6 + (8729519 / 28800) * t ^ 8 + (-54) * d * t ^ 2 + (7867 / 192) * d * t ^ 4 + (5523 / 640) * d * t ^ 6 + (-413 / 640) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_10, v54_11, v54_12, v54_20, v54_21, v54_22]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22]
  try simp only [star_one, star_neg]
  linear_combination ((9 / 2) * t ^ 2 + (-23533 / 8640) * t ^ 4 + (-13127 / 8640) * t ^ 6 + (-1309 / 8640) * d * t ^ 4 + (1199 / 17280) * d * t ^ 6 + (413 / 5760) * d * t ^ 8 + (7 / 20736) * d ^ 2 * t ^ 6 + (-1 / 20736) * d ^ 2 * t ^ 8) * alpha_sq + ((3 / 2) * t ^ 2 + (-10993 / 8640) * t ^ 4 + (-3983 / 34560) * t ^ 6 + (1 / 6912) * t ^ 8) * d_sq
theorem v55_23 (t : ℂ) : (momentPoly 55 z55 2 3).eval t = (17659 * t + (-6921723 / 320) * t ^ 3 + (408440767 / 192000) * t ^ 5 + (27400441 / 19200) * t ^ 7 + (167945023 / 192000) * t ^ 9 + (-35158339 / 1152000) * t ^ 11 + (27411313 / 384000) * t ^ 13 + (-17659 / 8) * d * t + (1151641 / 320) * d * t ^ 3 + (-146099167 / 115200) * d * t ^ 5 + (-1281989 / 57600) * d * t ^ 7 + (-927233 / 7680) * d * t ^ 9 + (-766291 / 230400) * d * t ^ 11 + (62017 / 76800) * d * t ^ 13 + (88295 / 24) * alpha * t + (-3270883 / 960) * alpha * t ^ 3 + (-1568840219 / 576000) * alpha * t ^ 5 + (133216319 / 57600) * alpha * t ^ 7 + (100558589 / 576000) * alpha * t ^ 9 + (-75258557 / 3456000) * alpha * t ^ 11 + (51657997 / 3456000) * alpha * t ^ 13 + (-138993 / 320) * alpha * d * t ^ 3 + (93577517 / 115200) * alpha * d * t ^ 5 + (-7229183 / 19200) * alpha * d * t ^ 7 + (-1319 / 2560) * alpha * d * t ^ 9 + (-54001 / 76800) * alpha * d * t ^ 11 + (-19411 / 15360) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_03, v54_10, v54_11, v54_12, v54_13, v54_20, v54_21, v54_22, v54_23]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23]
  try simp only [star_one, star_neg]
  linear_combination ((46331 / 320) * t ^ 3 + (-957607 / 3600) * t ^ 5 + (6978293 / 57600) * t ^ 7 + (155117 / 76800) * t ^ 11 + (-59059 / 46080) * t ^ 13 + (-749 / 1152) * d * t ^ 3 + (163 / 10800) * d * t ^ 5 + (60697 / 172800) * d * t ^ 7 + (278647 / 1382400) * d * t ^ 9 + (43351 / 4147200) * d * t ^ 11 + (17719 / 2073600) * d * t ^ 13 + (1309 / 69120) * d ^ 2 * t ^ 7 + (-1249 / 69120) * d ^ 2 * t ^ 9) * alpha_sq + ((107 / 16) * t ^ 3 + (-7921 / 1536) * t ^ 5 + (-9461 / 7680) * t ^ 7 + (311 / 2880) * t ^ 9 + (47 / 3456) * t ^ 11 + (749 / 1152) * alpha * t ^ 3 + (-8401 / 21600) * alpha * t ^ 5 + (-19009 / 86400) * alpha * t ^ 7 + (7 / 55296) * alpha * t ^ 9 + (-76601 / 4147200) * alpha * t ^ 11 + (47 / 82944) * alpha * t ^ 13) * d_sq
theorem v55_24 (t : ℂ) : (momentPoly 55 z55 2 4).eval t = ((8319113 / 15) * t ^ 2 + (-553200251 / 480) * t ^ 4 + (4128841096597 / 5760000) * t ^ 6 + (-508346962879 / 3840000) * t ^ 8 + (27688581881 / 1152000) * t ^ 10 + (-654004330741 / 69120000) * t ^ 12 + (17681896061 / 17280000) * t ^ 14 + (14067799841 / 69120000) * t ^ 18 + (-9161511773 / 34560000) * t ^ 20 + (-8668) * d * t ^ 2 + (1521259 / 120) * d * t ^ 4 + (-281519941 / 128000) * d * t ^ 6 + (-719489311 / 460800) * d * t ^ 8 + (-71406371 / 192000) * d * t ^ 10 + (103010701 / 1536000) * d * t ^ 12 + (-10554037 / 384000) * d * t ^ 14 + (572969 / 1536000) * d * t ^ 18 + (-127523 / 384000) * d * t ^ 20 + (5586526 / 15) * alpha * t ^ 2 + (-142393249 / 150) * alpha * t ^ 4 + (1533074577431 / 1920000) * alpha * t ^ 6 + (-903492274151 / 3840000) * alpha * t ^ 8 + (3123600469 / 128000) * alpha * t ^ 10 + (-794148682229 / 69120000) * alpha * t ^ 12 + (14955722909 / 17280000) * alpha * t ^ 14 + (13404938129 / 69120000) * alpha * t ^ 18 + (-399465133 / 3840000) * alpha * t ^ 20 + (-2167) * alpha * d * t ^ 2 + (8385619 / 7200) * alpha * d * t ^ 4 + (11000772629 / 3456000) * alpha * d * t ^ 6 + (-13051950989 / 6912000) * alpha * d * t ^ 8 + (-23172949 / 115200) * alpha * d * t ^ 10 + (-78032729 / 921600) * alpha * d * t ^ 12 + (-44066993 / 3456000) * alpha * d * t ^ 14 + (-42333403 / 13824000) * alpha * d * t ^ 18 + (-32023 / 384000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_03, v54_04, v54_10, v54_11, v54_12, v54_13, v54_14, v54_20, v54_21, v54_22, v54_23, v54_24]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24]
  try simp only [star_one, star_neg]
  linear_combination ((-2167 / 3) * t ^ 2 + (5446121 / 3600) * t ^ 4 + (-548754739 / 691200) * t ^ 6 + (-43648147 / 3456000) * t ^ 8 + (-3956473 / 768000) * t ^ 10 + (149099099 / 5184000) * t ^ 12 + (-4652771 / 648000) * t ^ 14 + (22303139 / 20736000) * t ^ 18 + (-13706641 / 3456000) * d * t ^ 6 + (3921361 / 864000) * d * t ^ 8 + (2764391 / 6912000) * d * t ^ 10 + (-23608117 / 13824000) * d * t ^ 12 + (7651979 / 10368000) * d * t ^ 14 + (-5862323 / 41472000) * d * t ^ 18 + (127523 / 3456000) * d * t ^ 20 + (57361 / 1382400) * d ^ 2 * t ^ 8 + (-13331 / 345600) * d ^ 2 * t ^ 10 + (3913 / 3317760) * d ^ 2 * t ^ 12 + (-25963 / 12441600) * d ^ 2 * t ^ 14 + (665 / 1990656) * d ^ 2 * t ^ 18 + (-95 / 995328) * d ^ 2 * t ^ 20) * alpha_sq + ((2167 / 9) * t ^ 2 + (-259859 / 720) * t ^ 4 + (216964937 / 3456000) * t ^ 6 + (113597929 / 2304000) * t ^ 8 + (82308367 / 6912000) * t ^ 10 + (-150450643 / 82944000) * t ^ 12 + (-867629 / 4147200) * t ^ 14 + (-4272313 / 82944000) * t ^ 18 + (95 / 331776) * t ^ 20 + (69377 / 720) * alpha * t ^ 4 + (-205297013 / 1152000) * alpha * t ^ 6 + (541111511 / 6912000) * alpha * t ^ 8 + (24715111 / 6912000) * alpha * t ^ 10 + (-3795131 / 20736000) * alpha * t ^ 12 + (58703 / 207360) * alpha * t ^ 14 + (1364849 / 20736000) * alpha * t ^ 18) * d_sq
theorem v55_30 (t : ℂ) : (momentPoly 55 z55 3 0).eval t = ((8521 / 320) * t ^ 3 + (269 / 320) * t ^ 5 + (-1913 / 480) * d * t ^ 3 + (213 / 80) * d * t ^ 5 + (-47 / 384) * d * t ^ 9 + (-30873 / 800) * alpha * t ^ 3 + (36073 / 1200) * alpha * t ^ 5 + (67301 / 28800) * alpha * t ^ 9 + (1299 / 320) * alpha * d * t ^ 3 + (-1249 / 320) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_10, v54_20, v54_30]
  try simp only [phase53_00, phase53_10, phase53_20, phase53_30]
  try simp only [star_one, star_neg]
  linear_combination ((-433 / 320) * t ^ 3 + (413 / 320) * t ^ 5 + (7 / 1152) * d * t ^ 3 + (1 / 576) * d * t ^ 5) * alpha_sq + ((1 / 48) * t ^ 3 + (-7 / 1152) * alpha * t ^ 3 + (1 / 576) * alpha * t ^ 5) * d_sq
theorem v55_31 (t : ℂ) : (momentPoly 55 z55 3 1).eval t = ((103653 / 40) * t ^ 2 + (-3084787 / 960) * t ^ 4 + (713641 / 960) * t ^ 6 + (77639 / 5760) * t ^ 10 + (-81 / 2) * d * t ^ 2 + (28703 / 960) * d * t ^ 4 + (1839 / 320) * d * t ^ 6 + (-47 / 384) * d * t ^ 10 + (-34803 / 20) * alpha * t ^ 2 + (14722097 / 4800) * alpha * t ^ 4 + (-6387013 / 4800) * alpha * t ^ 6 + (-230059 / 28800) * alpha * t ^ 10 + (81 / 8) * alpha * d * t ^ 2 + (-51587 / 14400) * alpha * d * t ^ 4 + (-26909 / 4800) * alpha * d * t ^ 6 + (-983 / 3200) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_10, v54_11, v54_20, v54_21, v54_30, v54_31]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21, phase53_30, phase53_31]
  try simp only [star_one, star_neg]
  linear_combination ((-27 / 8) * t ^ 2 + (102757 / 28800) * t ^ 4 + (-5369 / 38400) * t ^ 6 + (-3523 / 57600) * t ^ 10) * alpha_sq + ((9 / 8) * t ^ 2 + (-4903 / 5760) * t ^ 4 + (-3913 / 23040) * t ^ 6 + (47 / 6912) * t ^ 10 + (-1309 / 5760) * alpha * t ^ 4 + (1259 / 5760) * alpha * t ^ 6) * d_sq
theorem v55_32 (t : ℂ) : (momentPoly 55 z55 3 2).eval t = (17659 * t + (-6921723 / 320) * t ^ 3 + (408440767 / 192000) * t ^ 5 + (27400441 / 19200) * t ^ 7 + (167945023 / 192000) * t ^ 9 + (-35158339 / 1152000) * t ^ 11 + (27411313 / 384000) * t ^ 13 + (-17659 / 8) * d * t + (1151641 / 320) * d * t ^ 3 + (-146099167 / 115200) * d * t ^ 5 + (-1281989 / 57600) * d * t ^ 7 + (-927233 / 7680) * d * t ^ 9 + (-766291 / 230400) * d * t ^ 11 + (62017 / 76800) * d * t ^ 13 + (-88295 / 24) * alpha * t + (3270883 / 960) * alpha * t ^ 3 + (1568840219 / 576000) * alpha * t ^ 5 + (-133216319 / 57600) * alpha * t ^ 7 + (-100558589 / 576000) * alpha * t ^ 9 + (75258557 / 3456000) * alpha * t ^ 11 + (-51657997 / 3456000) * alpha * t ^ 13 + (138993 / 320) * alpha * d * t ^ 3 + (-93577517 / 115200) * alpha * d * t ^ 5 + (7229183 / 19200) * alpha * d * t ^ 7 + (1319 / 2560) * alpha * d * t ^ 9 + (54001 / 76800) * alpha * d * t ^ 11 + (19411 / 15360) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_10, v54_11, v54_12, v54_20, v54_21, v54_22, v54_30, v54_31, v54_32]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22, phase53_30, phase53_31, phase53_32]
  try simp only [star_one, star_neg]
  linear_combination ((46331 / 320) * t ^ 3 + (-957607 / 3600) * t ^ 5 + (6978293 / 57600) * t ^ 7 + (155117 / 76800) * t ^ 11 + (-59059 / 46080) * t ^ 13 + (-749 / 1152) * d * t ^ 3 + (163 / 10800) * d * t ^ 5 + (60697 / 172800) * d * t ^ 7 + (278647 / 1382400) * d * t ^ 9 + (43351 / 4147200) * d * t ^ 11 + (17719 / 2073600) * d * t ^ 13 + (1309 / 69120) * d ^ 2 * t ^ 7 + (-1249 / 69120) * d ^ 2 * t ^ 9) * alpha_sq + ((107 / 16) * t ^ 3 + (-7921 / 1536) * t ^ 5 + (-9461 / 7680) * t ^ 7 + (311 / 2880) * t ^ 9 + (47 / 3456) * t ^ 11 + (-749 / 1152) * alpha * t ^ 3 + (8401 / 21600) * alpha * t ^ 5 + (19009 / 86400) * alpha * t ^ 7 + (-7 / 55296) * alpha * t ^ 9 + (76601 / 4147200) * alpha * t ^ 11 + (-47 / 82944) * alpha * t ^ 13) * d_sq
theorem v55_33 (t : ℂ) : (momentPoly 55 z55 3 3).eval t = (971245 + (-2336026) * t ^ 2 + (3225952961 / 1600) * t ^ 4 + (-226273420783 / 240000) * t ^ 6 + (96788094769 / 240000) * t ^ 8 + (-26484514123 / 240000) * t ^ 10 + (331908273 / 160000) * t ^ 12 + (-2161616863 / 1440000) * t ^ 14 + (-16218127 / 540000) * t ^ 18 + (-13002) * d * t ^ 2 + (1250853 / 64) * d * t ^ 4 + (-163919201 / 48000) * d * t ^ 6 + (-27262931 / 9600) * d * t ^ 8 + (-5565823 / 16000) * d * t ^ 10 + (2352889 / 96000) * d * t ^ 12 + (-1585913 / 32000) * d * t ^ 14) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_03, v54_10, v54_11, v54_12, v54_13, v54_20, v54_21, v54_22, v54_23, v54_30, v54_31, v54_32, v54_33]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23, phase53_30, phase53_31, phase53_32, phase53_33]
  try simp only [star_one, star_neg]
  linear_combination ((2167 / 2) * t ^ 2 + (-1247249 / 960) * t ^ 4 + (-55307129 / 144000) * t ^ 6 + (252408653 / 460800) * t ^ 8 + (125267999 / 2304000) * t ^ 10 + (11170481 / 1728000) * t ^ 12 + (-16781311 / 4608000) * t ^ 14 + (-1518803 / 2764800) * t ^ 18 + (-69377 / 960) * d * t ^ 4 + (1919857 / 19200) * d * t ^ 6 + (1325477 / 460800) * d * t ^ 8 + (-14002351 / 460800) * d * t ^ 10 + (-551369 / 691200) * d * t ^ 12 + (92059 / 345600) * d * t ^ 14 + (35 / 216) * d ^ 2 * t ^ 6 + (-797 / 10800) * d ^ 2 * t ^ 8 + (-53243 / 691200) * d ^ 2 * t ^ 10 + (-2849 / 691200) * d ^ 2 * t ^ 14) * alpha_sq + ((2167 / 6) * t ^ 2 + (-582629 / 960) * t ^ 4 + (517181 / 2400) * t ^ 6 + (4741747 / 460800) * t ^ 8 + (9842291 / 460800) * t ^ 10 + (244573 / 345600) * t ^ 12 + (-851179 / 2764800) * t ^ 14 + (2209 / 331776) * t ^ 18) * d_sq
theorem v55_34 (t : ℂ) : (momentPoly 55 z55 3 4).eval t = (3779677 * t + (-137593503 / 20) * t ^ 3 + (17308300367 / 6400) * t ^ 5 + (1056067523481 / 12800000) * t ^ 7 + (26476645571447 / 38400000) * t ^ 9 + (-28263088340839 / 76800000) * t ^ 11 + (88408247 / 2560) * t ^ 13 + (-3690376104133 / 115200000) * t ^ 15 + (-129466776179 / 51200000) * t ^ 17 + (565262041339 / 691200000) * t ^ 19 + (-212852073523 / 230400000) * t ^ 21 + (-32144966683 / 460800000) * t ^ 25 + (-3779677 / 8) * d * t + (22892901 / 20) * d * t ^ 3 + (-1138431733 / 1280) * d * t ^ 5 + (6575644178731 / 23040000) * d * t ^ 7 + (-3045928583713 / 23040000) * d * t ^ 9 + (2757848222953 / 46080000) * d * t ^ 11 + (141494611499 / 34560000) * d * t ^ 13 + (-9080013619 / 23040000) * d * t ^ 15 + (1830584543 / 18432000) * d * t ^ 17 + (-3547924757 / 46080000) * d * t ^ 19 + (4330533559 / 46080000) * d * t ^ 21 + (11397103 / 18432000) * d * t ^ 25 + (18898385 / 24) * alpha * t + (-21673421 / 20) * alpha * t ^ 3 + (-13735478339 / 19200) * alpha * t ^ 5 + (173225750492489 / 115200000) * alpha * t ^ 7 + (-50862202624459 / 115200000) * alpha * t ^ 9 + (-3299498443759 / 76800000) * alpha * t ^ 11 + (-45234081611 / 34560000) * alpha * t ^ 13 + (-1486911721859 / 345600000) * alpha * t ^ 15 + (-2555178795893 / 1382400000) * alpha * t ^ 17 + (935291192057 / 2073600000) * alpha * t ^ 19 + (-91118072209 / 691200000) * alpha * t ^ 21 + (-57366609647 / 4147200000) * alpha * t ^ 25 + (-2762973 / 20) * alpha * d * t ^ 3 + (488311111 / 1280) * alpha * d * t ^ 5 + (-896660789193 / 2560000) * alpha * d * t ^ 7 + (2558898356731 / 23040000) * alpha * d * t ^ 9 + (-4636400881 / 614400) * alpha * d * t ^ 11 + (8181263651 / 2880000) * alpha * d * t ^ 13 + (13529815253 / 23040000) * alpha * d * t ^ 15 + (-285613451 / 6144000) * alpha * d * t ^ 17 + (-244372889 / 5120000) * alpha * d * t ^ 19 + (237364339 / 5120000) * alpha * d * t ^ 21 + (-22126801 / 18432000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_03, v54_04, v54_10, v54_11, v54_12, v54_13, v54_14, v54_20, v54_21, v54_22, v54_23, v54_24, v54_30, v54_31, v54_32, v54_33, v54_34]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24, phase53_30, phase53_31, phase53_32, phase53_33, phase53_34]
  try simp only [star_one, star_neg]
  linear_combination ((920991 / 20) * t ^ 3 + (-39842943 / 320) * t ^ 5 + (5158638938743 / 46080000) * t ^ 7 + (-538376520773 / 15360000) * t ^ 9 + (35120934593 / 9216000) * t ^ 11 + (-51390586577 / 17280000) * t ^ 13 + (47269292657 / 69120000) * t ^ 15 + (947902241 / 18432000) * t ^ 17 + (1304420833 / 69120000) * t ^ 19 + (-79123343 / 5120000) * t ^ 21 + (67321969 / 55296000) * t ^ 25 + (-4963 / 24) * d * t ^ 3 + (194249 / 2880) * d * t ^ 5 + (796000967 / 3072000) * d * t ^ 7 + (10792909 / 1152000) * d * t ^ 9 + (-3165570337 / 27648000) * d * t ^ 11 + (-2218826269 / 165888000) * d * t ^ 13 + (-168549847 / 82944000) * d * t ^ 15 + (-41350073 / 110592000) * d * t ^ 17 + (-34782149 / 99532800) * d * t ^ 19 + (22804141 / 331776000) * d * t ^ 21 + (336661 / 19906560) * d * t ^ 25 + (414953 / 34560) * d ^ 2 * t ^ 7 + (-22678957 / 1024000) * d ^ 2 * t ^ 9 + (268571693 / 27648000) * d ^ 2 * t ^ 11 + (23722811 / 55296000) * d ^ 2 * t ^ 13 + (-220103 / 82944000) * d ^ 2 * t ^ 15 + (19411 / 1105920) * d ^ 2 * t ^ 17 + (24871 / 1327104) * d ^ 2 * t ^ 19 + (-98611 / 10368000) * d ^ 2 * t ^ 21) * alpha_sq + (2127 * t ^ 3 + (-831705 / 256) * t ^ 5 + (888847019 / 1843200) * t ^ 7 + (691075079 / 1152000) * t ^ 9 + (491353181 / 9216000) * t ^ 11 + (-719844713 / 55296000) * t ^ 13 + (183517723 / 27648000) * t ^ 15 + (-19411 / 184320) * t ^ 17 + (-9212299 / 165888000) * t ^ 19 + (777013 / 13824000) * t ^ 21 + (4963 / 24) * alpha * t ^ 3 + (-538819 / 2880) * alpha * t ^ 5 + (-4863450943 / 27648000) * alpha * t ^ 7 + (54143071 / 432000) * alpha * t ^ 9 + (44527783 / 1843200) * alpha * t ^ 11 + (948830353 / 165888000) * alpha * t ^ 13 + (17749003 / 16588800) * alpha * t ^ 15 + (1778959 / 66355200) * alpha * t ^ 17 + (5206009 / 19906560) * alpha * t ^ 19 + (5104187 / 331776000) * alpha * t ^ 21 + (-4465 / 3981312) * alpha * t ^ 25) * d_sq
theorem v55_40 (t : ℂ) : (momentPoly 55 z55 4 0).eval t = ((-1298833 / 4000) * t ^ 4 + (9802757 / 8000) * t ^ 6 + (-79685861 / 96000) * t ^ 8 + (4446319 / 72000) * t ^ 10 + (-3001813 / 576000) * t ^ 16 + (-3193 / 960) * d * t ^ 4 + (-1857 / 640) * d * t ^ 6 + (1239 / 640) * d * t ^ 8 + (-47 / 96) * d * t ^ 10 + (-2882677 / 3000) * alpha * t ^ 4 + (60096079 / 48000) * alpha * t ^ 6 + (-1411953 / 4000) * alpha * t ^ 8 + (874427 / 18000) * alpha * t ^ 10 + (-470783 / 48000) * alpha * t ^ 16 + (253997 / 14400) * alpha * d * t ^ 4 + (-76081 / 4800) * alpha * d * t ^ 6 + (573 / 1280) * alpha * d * t ^ 8 + (-4723 / 4800) * alpha * d * t ^ 10 + (-95 / 4608) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_10, v54_20, v54_30, v54_40]
  try simp only [phase53_00, phase53_10, phase53_20, phase53_30, phase53_40]
  try simp only [star_one, star_neg]
  linear_combination ((-9761 / 1600) * t ^ 4 + (147377 / 28800) * t ^ 6 + (3523 / 14400) * t ^ 10 + (1309 / 2880) * d * t ^ 4 + (-1199 / 5760) * d * t ^ 6 + (-413 / 1920) * d * t ^ 8 + (-7 / 6912) * d ^ 2 * t ^ 6 + (1 / 6912) * d ^ 2 * t ^ 8) * alpha_sq + ((1187 / 2880) * t ^ 4 + (-427 / 1280) * t ^ 6 + (-1 / 2304) * t ^ 8 + (47 / 1728) * t ^ 10 + (-1309 / 2880) * alpha * t ^ 4 + (1259 / 2880) * alpha * t ^ 6) * d_sq
theorem v55_41 (t : ℂ) : (momentPoly 55 z55 4 1).eval t = ((911747 / 160) * t ^ 3 + (-929963179 / 192000) * t ^ 5 + (30017929 / 96000) * t ^ 7 + (-287917889 / 384000) * t ^ 9 + (18817331 / 288000) * t ^ 11 + (1058119 / 1152000) * t ^ 17 + (-204691 / 240) * d * t ^ 3 + (822833269 / 576000) * d * t ^ 5 + (-65923273 / 96000) * d * t ^ 7 + (28235093 / 384000) * d * t ^ 9 + (4404553 / 288000) * d * t ^ 11 + (302099 / 384000) * d * t ^ 17 + (-3303411 / 400) * alpha * t ^ 3 + (7031905381 / 576000) * alpha * t ^ 5 + (-111961479 / 32000) * alpha * t ^ 7 + (-42627203 / 384000) * alpha * t ^ 9 + (-356760989 / 864000) * alpha * t ^ 11 + (-40621481 / 3456000) * alpha * t ^ 17 + (138993 / 160) * alpha * d * t ^ 3 + (-297170999 / 192000) * alpha * d * t ^ 5 + (20164843 / 32000) * alpha * d * t ^ 7 + (6755937 / 128000) * alpha * d * t ^ 9 + (-187603 / 96000) * alpha * d * t ^ 11 + (1388599 / 1152000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_10, v54_11, v54_20, v54_21, v54_30, v54_31, v54_40, v54_41]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21, phase53_30, phase53_31, phase53_40, phase53_41]
  try simp only [star_one, star_neg]
  linear_combination ((-46331 / 160) * t ^ 3 + (161643853 / 288000) * t ^ 5 + (-82568881 / 288000) * t ^ 7 + (6628687 / 384000) * t ^ 9 + (-966383 / 288000) * t ^ 11 + (470783 / 1152000) * t ^ 17 + (749 / 576) * d * t ^ 3 + (-36503 / 69120) * d * t ^ 5 + (-34133 / 69120) * d * t ^ 7 + (-6269 / 30720) * d * t ^ 9 + (-329 / 41472) * d * t ^ 11 + (-95 / 82944) * d * t ^ 17 + (-1309 / 69120) * d ^ 2 * t ^ 7 + (1249 / 69120) * d ^ 2 * t ^ 9) * alpha_sq + ((107 / 24) * t ^ 3 + (-15781 / 4608) * t ^ 5 + (-13147 / 23040) * t ^ 7 + (-311 / 2880) * t ^ 9 + (47 / 864) * t ^ 11 + (-749 / 576) * alpha * t ^ 3 + (96749 / 345600) * alpha * t ^ 5 + (11777 / 12800) * alpha * t ^ 7 + (-7861 / 276480) * alpha * t ^ 9 + (60151 / 1036800) * alpha * t ^ 11 + (95 / 82944) * alpha * t ^ 17) * d_sq
theorem v55_42 (t : ℂ) : (momentPoly 55 z55 4 2).eval t = ((8319113 / 15) * t ^ 2 + (-553200251 / 480) * t ^ 4 + (4128841096597 / 5760000) * t ^ 6 + (-508346962879 / 3840000) * t ^ 8 + (27688581881 / 1152000) * t ^ 10 + (-654004330741 / 69120000) * t ^ 12 + (17681896061 / 17280000) * t ^ 14 + (14067799841 / 69120000) * t ^ 18 + (-9161511773 / 34560000) * t ^ 20 + (-8668) * d * t ^ 2 + (1521259 / 120) * d * t ^ 4 + (-281519941 / 128000) * d * t ^ 6 + (-719489311 / 460800) * d * t ^ 8 + (-71406371 / 192000) * d * t ^ 10 + (103010701 / 1536000) * d * t ^ 12 + (-10554037 / 384000) * d * t ^ 14 + (572969 / 1536000) * d * t ^ 18 + (-127523 / 384000) * d * t ^ 20 + (-5586526 / 15) * alpha * t ^ 2 + (142393249 / 150) * alpha * t ^ 4 + (-1533074577431 / 1920000) * alpha * t ^ 6 + (903492274151 / 3840000) * alpha * t ^ 8 + (-3123600469 / 128000) * alpha * t ^ 10 + (794148682229 / 69120000) * alpha * t ^ 12 + (-14955722909 / 17280000) * alpha * t ^ 14 + (-13404938129 / 69120000) * alpha * t ^ 18 + (399465133 / 3840000) * alpha * t ^ 20 + 2167 * alpha * d * t ^ 2 + (-8385619 / 7200) * alpha * d * t ^ 4 + (-11000772629 / 3456000) * alpha * d * t ^ 6 + (13051950989 / 6912000) * alpha * d * t ^ 8 + (23172949 / 115200) * alpha * d * t ^ 10 + (78032729 / 921600) * alpha * d * t ^ 12 + (44066993 / 3456000) * alpha * d * t ^ 14 + (42333403 / 13824000) * alpha * d * t ^ 18 + (32023 / 384000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_10, v54_11, v54_12, v54_20, v54_21, v54_22, v54_30, v54_31, v54_32, v54_40, v54_41, v54_42]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22, phase53_30, phase53_31, phase53_32, phase53_40, phase53_41, phase53_42]
  try simp only [star_one, star_neg]
  linear_combination ((-2167 / 3) * t ^ 2 + (5446121 / 3600) * t ^ 4 + (-548754739 / 691200) * t ^ 6 + (-43648147 / 3456000) * t ^ 8 + (-3956473 / 768000) * t ^ 10 + (149099099 / 5184000) * t ^ 12 + (-4652771 / 648000) * t ^ 14 + (22303139 / 20736000) * t ^ 18 + (-13706641 / 3456000) * d * t ^ 6 + (3921361 / 864000) * d * t ^ 8 + (2764391 / 6912000) * d * t ^ 10 + (-23608117 / 13824000) * d * t ^ 12 + (7651979 / 10368000) * d * t ^ 14 + (-5862323 / 41472000) * d * t ^ 18 + (127523 / 3456000) * d * t ^ 20 + (57361 / 1382400) * d ^ 2 * t ^ 8 + (-13331 / 345600) * d ^ 2 * t ^ 10 + (3913 / 3317760) * d ^ 2 * t ^ 12 + (-25963 / 12441600) * d ^ 2 * t ^ 14 + (665 / 1990656) * d ^ 2 * t ^ 18 + (-95 / 995328) * d ^ 2 * t ^ 20) * alpha_sq + ((2167 / 9) * t ^ 2 + (-259859 / 720) * t ^ 4 + (216964937 / 3456000) * t ^ 6 + (113597929 / 2304000) * t ^ 8 + (82308367 / 6912000) * t ^ 10 + (-150450643 / 82944000) * t ^ 12 + (-867629 / 4147200) * t ^ 14 + (-4272313 / 82944000) * t ^ 18 + (95 / 331776) * t ^ 20 + (-69377 / 720) * alpha * t ^ 4 + (205297013 / 1152000) * alpha * t ^ 6 + (-541111511 / 6912000) * alpha * t ^ 8 + (-24715111 / 6912000) * alpha * t ^ 10 + (3795131 / 20736000) * alpha * t ^ 12 + (-58703 / 207360) * alpha * t ^ 14 + (-1364849 / 20736000) * alpha * t ^ 18) * d_sq
theorem v55_43 (t : ℂ) : (momentPoly 55 z55 4 3).eval t = (3779677 * t + (-137593503 / 20) * t ^ 3 + (17308300367 / 6400) * t ^ 5 + (1056067523481 / 12800000) * t ^ 7 + (26476645571447 / 38400000) * t ^ 9 + (-28263088340839 / 76800000) * t ^ 11 + (88408247 / 2560) * t ^ 13 + (-3690376104133 / 115200000) * t ^ 15 + (-129466776179 / 51200000) * t ^ 17 + (565262041339 / 691200000) * t ^ 19 + (-212852073523 / 230400000) * t ^ 21 + (-32144966683 / 460800000) * t ^ 25 + (-3779677 / 8) * d * t + (22892901 / 20) * d * t ^ 3 + (-1138431733 / 1280) * d * t ^ 5 + (6575644178731 / 23040000) * d * t ^ 7 + (-3045928583713 / 23040000) * d * t ^ 9 + (2757848222953 / 46080000) * d * t ^ 11 + (141494611499 / 34560000) * d * t ^ 13 + (-9080013619 / 23040000) * d * t ^ 15 + (1830584543 / 18432000) * d * t ^ 17 + (-3547924757 / 46080000) * d * t ^ 19 + (4330533559 / 46080000) * d * t ^ 21 + (11397103 / 18432000) * d * t ^ 25 + (-18898385 / 24) * alpha * t + (21673421 / 20) * alpha * t ^ 3 + (13735478339 / 19200) * alpha * t ^ 5 + (-173225750492489 / 115200000) * alpha * t ^ 7 + (50862202624459 / 115200000) * alpha * t ^ 9 + (3299498443759 / 76800000) * alpha * t ^ 11 + (45234081611 / 34560000) * alpha * t ^ 13 + (1486911721859 / 345600000) * alpha * t ^ 15 + (2555178795893 / 1382400000) * alpha * t ^ 17 + (-935291192057 / 2073600000) * alpha * t ^ 19 + (91118072209 / 691200000) * alpha * t ^ 21 + (57366609647 / 4147200000) * alpha * t ^ 25 + (2762973 / 20) * alpha * d * t ^ 3 + (-488311111 / 1280) * alpha * d * t ^ 5 + (896660789193 / 2560000) * alpha * d * t ^ 7 + (-2558898356731 / 23040000) * alpha * d * t ^ 9 + (4636400881 / 614400) * alpha * d * t ^ 11 + (-8181263651 / 2880000) * alpha * d * t ^ 13 + (-13529815253 / 23040000) * alpha * d * t ^ 15 + (285613451 / 6144000) * alpha * d * t ^ 17 + (244372889 / 5120000) * alpha * d * t ^ 19 + (-237364339 / 5120000) * alpha * d * t ^ 21 + (22126801 / 18432000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_03, v54_10, v54_11, v54_12, v54_13, v54_20, v54_21, v54_22, v54_23, v54_30, v54_31, v54_32, v54_33, v54_40, v54_41, v54_42, v54_43]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23, phase53_30, phase53_31, phase53_32, phase53_33, phase53_40, phase53_41, phase53_42, phase53_43]
  try simp only [star_one, star_neg]
  linear_combination ((920991 / 20) * t ^ 3 + (-39842943 / 320) * t ^ 5 + (5158638938743 / 46080000) * t ^ 7 + (-538376520773 / 15360000) * t ^ 9 + (35120934593 / 9216000) * t ^ 11 + (-51390586577 / 17280000) * t ^ 13 + (47269292657 / 69120000) * t ^ 15 + (947902241 / 18432000) * t ^ 17 + (1304420833 / 69120000) * t ^ 19 + (-79123343 / 5120000) * t ^ 21 + (67321969 / 55296000) * t ^ 25 + (-4963 / 24) * d * t ^ 3 + (194249 / 2880) * d * t ^ 5 + (796000967 / 3072000) * d * t ^ 7 + (10792909 / 1152000) * d * t ^ 9 + (-3165570337 / 27648000) * d * t ^ 11 + (-2218826269 / 165888000) * d * t ^ 13 + (-168549847 / 82944000) * d * t ^ 15 + (-41350073 / 110592000) * d * t ^ 17 + (-34782149 / 99532800) * d * t ^ 19 + (22804141 / 331776000) * d * t ^ 21 + (336661 / 19906560) * d * t ^ 25 + (414953 / 34560) * d ^ 2 * t ^ 7 + (-22678957 / 1024000) * d ^ 2 * t ^ 9 + (268571693 / 27648000) * d ^ 2 * t ^ 11 + (23722811 / 55296000) * d ^ 2 * t ^ 13 + (-220103 / 82944000) * d ^ 2 * t ^ 15 + (19411 / 1105920) * d ^ 2 * t ^ 17 + (24871 / 1327104) * d ^ 2 * t ^ 19 + (-98611 / 10368000) * d ^ 2 * t ^ 21) * alpha_sq + (2127 * t ^ 3 + (-831705 / 256) * t ^ 5 + (888847019 / 1843200) * t ^ 7 + (691075079 / 1152000) * t ^ 9 + (491353181 / 9216000) * t ^ 11 + (-719844713 / 55296000) * t ^ 13 + (183517723 / 27648000) * t ^ 15 + (-19411 / 184320) * t ^ 17 + (-9212299 / 165888000) * t ^ 19 + (777013 / 13824000) * t ^ 21 + (-4963 / 24) * alpha * t ^ 3 + (538819 / 2880) * alpha * t ^ 5 + (4863450943 / 27648000) * alpha * t ^ 7 + (-54143071 / 432000) * alpha * t ^ 9 + (-44527783 / 1843200) * alpha * t ^ 11 + (-948830353 / 165888000) * alpha * t ^ 13 + (-17749003 / 16588800) * alpha * t ^ 15 + (-1778959 / 66355200) * alpha * t ^ 17 + (-5206009 / 19906560) * alpha * t ^ 19 + (-5104187 / 331776000) * alpha * t ^ 21 + (4465 / 3981312) * alpha * t ^ 25) * d_sq
theorem v55_44 (t : ℂ) : (momentPoly 55 z55 4 4).eval t = (207882235 + (-1981528934 / 3) * t ^ 2 + (1016418650863 / 1200) * t ^ 4 + (-77970100815403 / 120000) * t ^ 6 + (1186667434734841 / 3000000) * t ^ 8 + (-99959069422708783 / 576000000) * t ^ 10 + (920594127774807 / 25600000) * t ^ 12 + (-14878199505355673 / 3456000000) * t ^ 14 + (1457351335890443 / 768000000) * t ^ 16 + (-19497568696517 / 96000000) * t ^ 18 + (1705994563231333 / 20736000000) * t ^ 20 + (-43320050680627 / 576000000) * t ^ 22 + (356040908963527 / 13824000000) * t ^ 24 + (-29373659237213 / 10368000000) * t ^ 26 + (10844079080099 / 41472000000) * t ^ 32 + (-3676306) * d * t ^ 2 + (131371033 / 16) * d * t ^ 4 + (-108876809791 / 24000) * d * t ^ 6 + (-16521660794941 / 28800000) * d * t ^ 8 + (29792183677799 / 115200000) * d * t ^ 10 + (70057852486057 / 230400000) * d * t ^ 12 + (-3030896831387 / 138240000) * d * t ^ 14 + (13837851004607 / 460800000) * d * t ^ 16 + (199738056047 / 57600000) * d * t ^ 18 + (-388515355961 / 460800000) * d * t ^ 20 + (109968187229 / 115200000) * d * t ^ 22 + (300185977 / 61440000) * d * t ^ 24 + (4531016443 / 76800000) * d * t ^ 26 + (8944877 / 7372800) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_03, v54_04, v54_10, v54_11, v54_12, v54_13, v54_14, v54_20, v54_21, v54_22, v54_23, v54_24, v54_30, v54_31, v54_32, v54_33, v54_34, v54_40, v54_41, v54_42, v54_43, v54_44]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24, phase53_30, phase53_31, phase53_32, phase53_33, phase53_34, phase53_40, phase53_41, phase53_42, phase53_43, phase53_44]
  try simp only [star_one, star_neg]
  linear_combination ((1838153 / 6) * t ^ 2 + (-392977567 / 720) * t ^ 4 + (-759105157 / 36000) * t ^ 6 + (36468280816361 / 86400000) * t ^ 8 + (-5037715143061 / 38400000) * t ^ 10 + (-1617729331429 / 86400000) * t ^ 12 + (-5717450185433 / 414720000) * t ^ 14 + (121502694667 / 57600000) * t ^ 16 + (-178031670971 / 518400000) * t ^ 18 + (807099735373 / 1555200000) * t ^ 20 + (-122241576289 / 2073600000) * t ^ 22 + (1549156777 / 194400000) * t ^ 26 + (-21858991 / 720) * d * t ^ 4 + (1001708473 / 14400) * d * t ^ 6 + (-647481689467 / 17280000) * d * t ^ 8 + (-330651512113 / 27648000) * d * t ^ 10 + (1296776855599 / 138240000) * d * t ^ 12 + (49711253147 / 69120000) * d * t ^ 14 + (42174750049 / 207360000) * d * t ^ 16 + (-1444390051 / 17280000) * d * t ^ 18 + (-24151323641 / 1244160000) * d * t ^ 20 + (4073595443 / 207360000) * d * t ^ 22 + (-300185977 / 552960000) * d * t ^ 24 + (-20101411 / 49766400) * d * t ^ 26 + (-8944877 / 66355200) * d * t ^ 32 + (78911 / 1152) * d ^ 2 * t ^ 6 + (-422791 / 8100) * d ^ 2 * t ^ 8 + (-2130279061 / 27648000) * d ^ 2 * t ^ 10 + (4243426127 / 82944000) * d ^ 2 * t ^ 12 + (289718567 / 41472000) * d ^ 2 * t ^ 14 + (63451949 / 27648000) * d ^ 2 * t ^ 16 + (22284089 / 62208000) * d ^ 2 * t ^ 18 + (1089859 / 6635520) * d ^ 2 * t ^ 20 + (-124291 / 1990656) * d ^ 2 * t ^ 22 + (14480687 / 1990656000) * d ^ 2 * t ^ 24 + (-493297 / 59719680) * d ^ 2 * t ^ 26 + (-9025 / 47775744) * d ^ 2 * t ^ 32) * alpha_sq + ((1838153 / 18) * t ^ 2 + (-183572107 / 720) * t ^ 4 + (5815572119 / 28800) * t ^ 6 + (-356864776457 / 5760000) * t ^ 8 + (3903006360649 / 138240000) * t ^ 10 + (-1963813579427 / 138240000) * t ^ 12 + (-559068721019 / 414720000) * t ^ 14 + (12023385019 / 46080000) * t ^ 16 + (-50599357 / 1382400) * t ^ 18 + (31490675929 / 2488320000) * t ^ 20 + (-1344433783 / 69120000) * t ^ 22 + (-14480687 / 663552000) * t ^ 24 + (-168320111 / 497664000) * t ^ 26 + (9025 / 15925248) * t ^ 32) * d_sq
#print axioms v55_00
#print axioms v55_11
#print axioms v55_22
#print axioms v55_33
#print axioms v55_44
end PhotonCertA
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z56 : Fin 56 → ℂ := Fin.snoc z55 (r ^ 3 * phiPlus)
theorem v56_00 (t : ℂ) : (momentPoly 56 z56 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00]
  try simp only [phase53_00]
  try simp only [star_one, star_neg]
  ring
theorem v56_01 (t : ℂ) : (momentPoly 56 z56 0 1).eval t = (1 * t + (-1 / 6) * d * t + (1 / 6) * alpha * t) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01]
  try simp only [phase53_00, phase53_01]
  try simp only [star_one, star_neg]
  ring
theorem v56_02 (t : ℂ) : (momentPoly 56 z56 0 2).eval t = ((1321 / 60) * t ^ 2 + (-311 / 60) * t ^ 4 + (-1 / 3) * d * t ^ 2 + (1279 / 120) * alpha * t ^ 2 + (-413 / 40) * alpha * t ^ 4 + (-5 / 72) * alpha * d * t ^ 2 + (1 / 72) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02]
  try simp only [phase53_00, phase53_01, phase53_02]
  try simp only [star_one, star_neg]
  linear_combination ((-5 / 288) * t ^ 2) * alpha_sq + ((1 / 96) * t ^ 2) * d_sq
theorem v56_03 (t : ℂ) : (momentPoly 56 z56 0 3).eval t = ((777 / 16) * t ^ 3 + (-1 / 16) * t ^ 5 + (-721 / 120) * d * t ^ 3 + (1469 / 480) * d * t ^ 5 + (-47 / 288) * d * t ^ 9 + (24641 / 600) * alpha * t ^ 3 + (-72391 / 2400) * alpha * t ^ 5 + (-17719 / 7200) * alpha * t ^ 9 + (-1289 / 240) * alpha * d * t ^ 3 + (1249 / 240) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_03]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03]
  try simp only [star_one, star_neg]
  linear_combination ((-1289 / 960) * t ^ 3 + (413 / 320) * t ^ 5 + (1 / 128) * d * t ^ 3 + (1 / 1152) * d * t ^ 5) * alpha_sq + ((1 / 32) * t ^ 3 + (1 / 128) * alpha * t ^ 3 + (-1 / 384) * alpha * t ^ 5) * d_sq
theorem v56_04 (t : ℂ) : (momentPoly 56 z56 0 4).eval t = ((28198 / 375) * t ^ 4 + (1053259 / 1000) * t ^ 6 + (-20810059 / 24000) * t ^ 8 + (1516931 / 18000) * t ^ 10 + (-306211 / 72000) * t ^ 16 + (-1567 / 160) * d * t ^ 4 + (-779 / 240) * d * t ^ 6 + (413 / 160) * d * t ^ 8 + (-47 / 72) * d * t ^ 10 + (10752997 / 8000) * alpha * t ^ 4 + (-18769151 / 12000) * alpha * t ^ 6 + (4666937 / 16000) * alpha * t ^ 8 + (-1766729 / 36000) * alpha * t ^ 10 + (470783 / 48000) * alpha * t ^ 16 + (-337051 / 14400) * alpha * d * t ^ 4 + (16303 / 800) * alpha * d * t ^ 6 + (-2963 / 5760) * alpha * d * t ^ 8 + (30713 / 21600) * alpha * d * t ^ 10 + (95 / 3456) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_03, v55_04]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04]
  try simp only [star_one, star_neg]
  linear_combination ((-10291 / 1600) * t ^ 4 + (36073 / 7200) * t ^ 6 + (24713 / 86400) * t ^ 10 + (433 / 640) * d * t ^ 4 + (-1229 / 2880) * d * t ^ 6 + (-413 / 1920) * d * t ^ 8 + (-1 / 768) * d ^ 2 * t ^ 6 + (1 / 4608) * d ^ 2 * t ^ 8) * alpha_sq + ((1913 / 2880) * t ^ 4 + (-563 / 1280) * t ^ 6 + (-1 / 1536) * t ^ 8 + (47 / 1152) * t ^ 10 + (433 / 640) * alpha * t ^ 4 + (-1259 / 1920) * alpha * t ^ 6) * d_sq
theorem v56_10 (t : ℂ) : (momentPoly 56 z56 1 0).eval t = (1 * t + (-1 / 6) * d * t + (-1 / 6) * alpha * t) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_10]
  try simp only [phase53_00, phase53_10]
  try simp only [star_one, star_neg]
  ring
theorem v56_11 (t : ℂ) : (momentPoly 56 z56 1 1).eval t = (56 + (-39) * t ^ 2 + (-1 / 3) * d * t ^ 2) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_10, v55_11]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11]
  try simp only [star_one, star_neg]
  linear_combination ((5 / 288) * t ^ 2) * alpha_sq + ((1 / 96) * t ^ 2) * d_sq
theorem v56_12 (t : ℂ) : (momentPoly 56 z56 1 2).eval t = (111 * t + (-12197 / 240) * t ^ 3 + (-2723 / 240) * t ^ 5 + (-37 / 2) * d * t + (3431 / 240) * d * t ^ 3 + (83 / 80) * d * t ^ 5 + (37 / 2) * alpha * t + (-377 / 80) * alpha * t ^ 3 + (-2629 / 240) * alpha * t ^ 5 + (-1289 / 720) * alpha * d * t ^ 3 + (1249 / 720) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_10, v55_11, v55_12]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12]
  try simp only [star_one, star_neg]
  linear_combination ((1289 / 2880) * t ^ 3 + (-413 / 960) * t ^ 5 + (-1 / 384) * d * t ^ 3 + (-1 / 3456) * d * t ^ 5) * alpha_sq + ((1 / 32) * t ^ 3 + (1 / 384) * alpha * t ^ 3 + (-1 / 1152) * alpha * t ^ 5) * d_sq
theorem v56_13 (t : ℂ) : (momentPoly 56 z56 1 3).eval t = ((14531 / 4) * t ^ 2 + (-4541089 / 1200) * t ^ 4 + (385429 / 800) * t ^ 6 + (46891 / 2400) * t ^ 10 + (-55) * d * t ^ 2 + (2977 / 80) * d * t ^ 4 + (3203 / 480) * d * t ^ 6 + (-47 / 288) * d * t ^ 10 + (14069 / 8) * alpha * t ^ 2 + (-3473653 / 1200) * alpha * t ^ 4 + (2746799 / 2400) * alpha * t ^ 6 + (56621 / 7200) * alpha * t ^ 10 + (-275 / 24) * alpha * d * t ^ 2 + (8429 / 3600) * alpha * d * t ^ 4 + (18331 / 2400) * alpha * d * t ^ 6 + (3049 / 7200) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_03, v55_10, v55_11, v55_12, v55_13]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13]
  try simp only [star_one, star_neg]
  linear_combination ((-275 / 96) * t ^ 2 + (338083 / 115200) * t ^ 4 + (-43 / 12800) * t ^ 6 + (-24713 / 345600) * t ^ 10) * alpha_sq + ((55 / 32) * t ^ 2 + (-28463 / 23040) * t ^ 4 + (-573 / 2560) * t ^ 6 + (47 / 4608) * t ^ 10 + (433 / 1280) * alpha * t ^ 4 + (-1259 / 3840) * alpha * t ^ 6) * d_sq
theorem v56_14 (t : ℂ) : (momentPoly 56 z56 1 4).eval t = ((84693 / 8) * t ^ 3 + (-82813423 / 9600) * t ^ 5 + (485301 / 1600) * t ^ 7 + (-3715693 / 3840) * t ^ 9 + (1759099 / 14400) * t ^ 11 + (37501 / 57600) * t ^ 17 + (-78589 / 60) * d * t ^ 3 + (275182373 / 144000) * d * t ^ 5 + (-6348797 / 8000) * d * t ^ 7 + (30139643 / 288000) * d * t ^ 9 + (1284101 / 72000) * d * t ^ 11 + (85033 / 96000) * d * t ^ 17 + (2685869 / 300) * alpha * t ^ 3 + (-1692766661 / 144000) * alpha * t ^ 5 + (61991287 / 24000) * alpha * t ^ 7 + (511189 / 288000) * alpha * t ^ 9 + (3061747 / 8000) * alpha * t ^ 11 + (2981557 / 288000) * alpha * t ^ 17 + (-140501 / 120) * alpha * d * t ^ 3 + (292934749 / 144000) * alpha * d * t ^ 5 + (-6482181 / 8000) * alpha * d * t ^ 7 + (-17270461 / 288000) * alpha * d * t ^ 9 + (598559 / 216000) * alpha * d * t ^ 11 + (-1388599 / 864000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_03, v55_04, v55_10, v55_11, v55_12, v55_13, v55_14]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14]
  try simp only [star_one, star_neg]
  linear_combination ((-140501 / 480) * t ^ 3 + (26582513 / 48000) * t ^ 5 + (-315576599 / 1152000) * t ^ 7 + (470651 / 32000) * t ^ 9 + (-966383 / 288000) * t ^ 11 + (470783 / 1152000) * t ^ 17 + (109 / 64) * d * t ^ 3 + (-19783 / 23040) * d * t ^ 5 + (-13687 / 27648) * d * t ^ 7 + (-62719 / 276480) * d * t ^ 9 + (-47 / 4608) * d * t ^ 11 + (-95 / 165888) * d * t ^ 17 + (-433 / 15360) * d ^ 2 * t ^ 7 + (1249 / 46080) * d ^ 2 * t ^ 9) * alpha_sq + ((109 / 16) * t ^ 3 + (-111619 / 23040) * t ^ 5 + (-963 / 1280) * t ^ 7 + (-311 / 1920) * t ^ 9 + (47 / 576) * t ^ 11 + (109 / 64) * alpha * t ^ 3 + (-17317 / 115200) * alpha * t ^ 5 + (-313619 / 230400) * alpha * t ^ 7 + (1151 / 30720) * alpha * t ^ 9 + (-10621 / 115200) * alpha * t ^ 11 + (-95 / 55296) * alpha * t ^ 17) * d_sq
theorem v56_20 (t : ℂ) : (momentPoly 56 z56 2 0).eval t = ((1321 / 60) * t ^ 2 + (-311 / 60) * t ^ 4 + (-1 / 3) * d * t ^ 2 + (-1279 / 120) * alpha * t ^ 2 + (413 / 40) * alpha * t ^ 4 + (5 / 72) * alpha * d * t ^ 2 + (-1 / 72) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_10, v55_20]
  try simp only [phase53_00, phase53_10, phase53_20]
  try simp only [star_one, star_neg]
  linear_combination ((-5 / 288) * t ^ 2) * alpha_sq + ((1 / 96) * t ^ 2) * d_sq
theorem v56_21 (t : ℂ) : (momentPoly 56 z56 2 1).eval t = (111 * t + (-12197 / 240) * t ^ 3 + (-2723 / 240) * t ^ 5 + (-37 / 2) * d * t + (3431 / 240) * d * t ^ 3 + (83 / 80) * d * t ^ 5 + (-37 / 2) * alpha * t + (377 / 80) * alpha * t ^ 3 + (2629 / 240) * alpha * t ^ 5 + (1289 / 720) * alpha * d * t ^ 3 + (-1249 / 720) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_10, v55_11, v55_20, v55_21]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21]
  try simp only [star_one, star_neg]
  linear_combination ((1289 / 2880) * t ^ 3 + (-413 / 960) * t ^ 5 + (-1 / 384) * d * t ^ 3 + (-1 / 3456) * d * t ^ 5) * alpha_sq + ((1 / 32) * t ^ 3 + (-1 / 384) * alpha * t ^ 3 + (1 / 1152) * alpha * t ^ 5) * d_sq
theorem v56_22 (t : ℂ) : (momentPoly 56 z56 2 2).eval t = (6216 + (-8580) * t ^ 2 + (7587577 / 2400) * t ^ 4 + (-883007 / 1200) * t ^ 6 + (698437 / 2400) * t ^ 8 + (-220 / 3) * d * t ^ 2 + (8461 / 160) * d * t ^ 4 + (479 / 48) * d * t ^ 6 + (-413 / 480) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_10, v55_11, v55_12, v55_20, v55_21, v55_22]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22]
  try simp only [star_one, star_neg]
  linear_combination ((275 / 72) * t ^ 2 + (-30569 / 17280) * t ^ 4 + (-28781 / 17280) * t ^ 6 + (-433 / 1920) * d * t ^ 4 + (1229 / 8640) * d * t ^ 6 + (413 / 5760) * d * t ^ 8 + (1 / 2304) * d ^ 2 * t ^ 6 + (-1 / 13824) * d ^ 2 * t ^ 8) * alpha_sq + ((55 / 24) * t ^ 2 + (-10763 / 5760) * t ^ 4 + (-583 / 3840) * t ^ 6 + (1 / 4608) * t ^ 8) * d_sq
theorem v56_23 (t : ℂ) : (momentPoly 56 z56 2 3).eval t = (18316 * t + (-1329473 / 80) * t ^ 3 + (-19530799 / 16000) * t ^ 5 + (-388237 / 19200) * t ^ 7 + (29693033 / 32000) * t ^ 9 + (-794489 / 32000) * t ^ 11 + (7221947 / 96000) * t ^ 13 + (-9158 / 3) * d * t + (373979 / 80) * d * t ^ 3 + (-15009569 / 9600) * d * t ^ 5 + (566239 / 19200) * d * t ^ 7 + (-591097 / 3840) * d * t ^ 9 + (-59389 / 11520) * d * t ^ 11 + (52417 / 57600) * d * t ^ 13 + (9158 / 3) * alpha * t + (-123279 / 80) * alpha * t ^ 3 + (-187296277 / 48000) * alpha * t ^ 5 + (14958581 / 6400) * alpha * t ^ 7 + (13123759 / 96000) * alpha * t ^ 9 + (-11165141 / 288000) * alpha * t ^ 11 + (3999781 / 288000) * alpha * t ^ 13 + (-140501 / 240) * alpha * d * t ^ 3 + (30974569 / 28800) * alpha * d * t ^ 5 + (-28154867 / 57600) * alpha * d * t ^ 7 + (-445 / 768) * alpha * d * t ^ 9 + (-17467 / 19200) * alpha * d * t ^ 11 + (-19411 / 11520) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_03, v55_10, v55_11, v55_12, v55_13, v55_20, v55_21, v55_22, v55_23]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23]
  try simp only [star_one, star_neg]
  linear_combination ((140501 / 960) * t ^ 3 + (-14796437 / 57600) * t ^ 5 + (6387013 / 57600) * t ^ 7 + (1381753 / 691200) * t ^ 11 + (-59059 / 46080) * t ^ 13 + (-109 / 128) * d * t ^ 3 + (10687 / 172800) * d * t ^ 5 + (613423 / 1382400) * d * t ^ 7 + (288197 / 1382400) * d * t ^ 9 + (8221 / 460800) * d * t ^ 11 + (39013 / 4147200) * d * t ^ 13 + (433 / 15360) * d ^ 2 * t ^ 7 + (-1249 / 46080) * d ^ 2 * t ^ 9) * alpha_sq + ((327 / 32) * t ^ 3 + (-175411 / 23040) * t ^ 5 + (-1051 / 640) * t ^ 7 + (311 / 1920) * t ^ 9 + (47 / 2304) * t ^ 11 + (109 / 128) * alpha * t ^ 3 + (-76487 / 172800) * alpha * t ^ 5 + (-465241 / 1382400) * alpha * t ^ 7 + (1 / 6144) * alpha * t ^ 9 + (-12971 / 460800) * alpha * t ^ 11 + (47 / 55296) * alpha * t ^ 13) * d_sq
theorem v56_24 (t : ℂ) : (momentPoly 56 z56 2 4).eval t = ((23760827 / 30) * t ^ 2 + (-145181519 / 100) * t ^ 4 + (57510287981 / 80000) * t ^ 6 + (-8701724267 / 120000) * t ^ 8 + (23038103 / 750) * t ^ 10 + (-4821882209 / 480000) * t ^ 12 + (57061957 / 60000) * t ^ 14 + (127884611 / 720000) * t ^ 18 + (-397322177 / 1440000) * t ^ 20 + (-35974 / 3) * d * t ^ 2 + (80379 / 5) * d * t ^ 4 + (-69149929 / 28800) * d * t ^ 6 + (-12848171 / 8000) * d * t ^ 8 + (-1703189 / 4000) * d * t ^ 10 + (23224151 / 288000) * d * t ^ 12 + (-183233 / 4500) * d * t ^ 14 + (27823 / 48000) * d * t ^ 18 + (-127523 / 288000) * d * t ^ 20 + (23005373 / 60) * alpha * t ^ 2 + (-177206451 / 200) * alpha * t ^ 4 + (117989121049 / 180000) * alpha * t ^ 6 + (-40320535541 / 240000) * alpha * t ^ 8 + (2461796377 / 96000) * alpha * t ^ 10 + (-8107465229 / 720000) * alpha * t ^ 12 + (380019713 / 360000) * alpha * t ^ 14 + (115339111 / 480000) * alpha * t ^ 18 + (-158296 / 1875) * alpha * t ^ 20 + (-89935 / 36) * alpha * d * t ^ 2 + (312713 / 600) * alpha * d * t ^ 4 + (696423937 / 144000) * alpha * d * t ^ 6 + (-91696193 / 36000) * alpha * d * t ^ 8 + (-14598509 / 72000) * alpha * d * t ^ 10 + (-96912859 / 864000) * alpha * d * t ^ 12 + (-901621 / 54000) * alpha * d * t ^ 14 + (-548123 / 144000) * alpha * d * t ^ 18 + (-9341 / 96000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_03, v55_04, v55_10, v55_11, v55_12, v55_13, v55_14, v55_20, v55_21, v55_22, v55_23, v55_24]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24]
  try simp only [star_one, star_neg]
  linear_combination ((-89935 / 144) * t ^ 2 + (1014249 / 800) * t ^ 4 + (-1298105941 / 2304000) * t ^ 6 + (-324509879 / 3456000) * t ^ 8 + (-41050609 / 4608000) * t ^ 10 + (16987409 / 518400) * t ^ 12 + (-19318759 / 2592000) * t ^ 14 + (40621481 / 41472000) * t ^ 18 + (-44262173 / 6912000) * d * t ^ 6 + (4772239 / 691200) * d * t ^ 8 + (239873 / 6912000) * d * t ^ 10 + (-372667 / 230400) * d * t ^ 12 + (5315177 / 5184000) * d * t ^ 14 + (-1806793 / 10368000) * d * t ^ 18 + (127523 / 3456000) * d * t ^ 20 + (253997 / 4147200) * d ^ 2 * t ^ 8 + (-76081 / 1382400) * d ^ 2 * t ^ 10 + (191 / 122880) * d ^ 2 * t ^ 12 + (-4723 / 1382400) * d ^ 2 * t ^ 14 + (95 / 221184) * d ^ 2 * t ^ 18 + (-95 / 663552) * d ^ 2 * t ^ 20) * alpha_sq + ((17987 / 48) * t ^ 2 + (-85389 / 160) * t ^ 4 + (70218889 / 768000) * t ^ 6 + (139969811 / 2304000) * t ^ 8 + (75636017 / 4608000) * t ^ 10 + (-70625629 / 27648000) * t ^ 12 + (-125209 / 460800) * t ^ 14 + (-616073 / 9216000) * t ^ 18 + (95 / 221184) * t ^ 20 + (11691 / 80) * alpha * t ^ 4 + (-1844104967 / 6912000) * alpha * t ^ 6 + (802698229 / 6912000) * alpha * t ^ 8 + (1196577 / 256000) * alpha * t ^ 10 + (-1320877 / 4608000) * alpha * t ^ 12 + (58703 / 138240) * alpha * t ^ 14 + (1364849 / 13824000) * alpha * t ^ 18) * d_sq
theorem v56_30 (t : ℂ) : (momentPoly 56 z56 3 0).eval t = ((777 / 16) * t ^ 3 + (-1 / 16) * t ^ 5 + (-721 / 120) * d * t ^ 3 + (1469 / 480) * d * t ^ 5 + (-47 / 288) * d * t ^ 9 + (-24641 / 600) * alpha * t ^ 3 + (72391 / 2400) * alpha * t ^ 5 + (17719 / 7200) * alpha * t ^ 9 + (1289 / 240) * alpha * d * t ^ 3 + (-1249 / 240) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_10, v55_20, v55_30]
  try simp only [phase53_00, phase53_10, phase53_20, phase53_30]
  try simp only [star_one, star_neg]
  linear_combination ((-1289 / 960) * t ^ 3 + (413 / 320) * t ^ 5 + (1 / 128) * d * t ^ 3 + (1 / 1152) * d * t ^ 5) * alpha_sq + ((1 / 32) * t ^ 3 + (-1 / 128) * alpha * t ^ 3 + (1 / 384) * alpha * t ^ 5) * d_sq
theorem v56_31 (t : ℂ) : (momentPoly 56 z56 3 1).eval t = ((14531 / 4) * t ^ 2 + (-4541089 / 1200) * t ^ 4 + (385429 / 800) * t ^ 6 + (46891 / 2400) * t ^ 10 + (-55) * d * t ^ 2 + (2977 / 80) * d * t ^ 4 + (3203 / 480) * d * t ^ 6 + (-47 / 288) * d * t ^ 10 + (-14069 / 8) * alpha * t ^ 2 + (3473653 / 1200) * alpha * t ^ 4 + (-2746799 / 2400) * alpha * t ^ 6 + (-56621 / 7200) * alpha * t ^ 10 + (275 / 24) * alpha * d * t ^ 2 + (-8429 / 3600) * alpha * d * t ^ 4 + (-18331 / 2400) * alpha * d * t ^ 6 + (-3049 / 7200) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_10, v55_11, v55_20, v55_21, v55_30, v55_31]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21, phase53_30, phase53_31]
  try simp only [star_one, star_neg]
  linear_combination ((-275 / 96) * t ^ 2 + (338083 / 115200) * t ^ 4 + (-43 / 12800) * t ^ 6 + (-24713 / 345600) * t ^ 10) * alpha_sq + ((55 / 32) * t ^ 2 + (-28463 / 23040) * t ^ 4 + (-573 / 2560) * t ^ 6 + (47 / 4608) * t ^ 10 + (-433 / 1280) * alpha * t ^ 4 + (1259 / 3840) * alpha * t ^ 6) * d_sq
theorem v56_32 (t : ℂ) : (momentPoly 56 z56 3 2).eval t = (18316 * t + (-1329473 / 80) * t ^ 3 + (-19530799 / 16000) * t ^ 5 + (-388237 / 19200) * t ^ 7 + (29693033 / 32000) * t ^ 9 + (-794489 / 32000) * t ^ 11 + (7221947 / 96000) * t ^ 13 + (-9158 / 3) * d * t + (373979 / 80) * d * t ^ 3 + (-15009569 / 9600) * d * t ^ 5 + (566239 / 19200) * d * t ^ 7 + (-591097 / 3840) * d * t ^ 9 + (-59389 / 11520) * d * t ^ 11 + (52417 / 57600) * d * t ^ 13 + (-9158 / 3) * alpha * t + (123279 / 80) * alpha * t ^ 3 + (187296277 / 48000) * alpha * t ^ 5 + (-14958581 / 6400) * alpha * t ^ 7 + (-13123759 / 96000) * alpha * t ^ 9 + (11165141 / 288000) * alpha * t ^ 11 + (-3999781 / 288000) * alpha * t ^ 13 + (140501 / 240) * alpha * d * t ^ 3 + (-30974569 / 28800) * alpha * d * t ^ 5 + (28154867 / 57600) * alpha * d * t ^ 7 + (445 / 768) * alpha * d * t ^ 9 + (17467 / 19200) * alpha * d * t ^ 11 + (19411 / 11520) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_10, v55_11, v55_12, v55_20, v55_21, v55_22, v55_30, v55_31, v55_32]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22, phase53_30, phase53_31, phase53_32]
  try simp only [star_one, star_neg]
  linear_combination ((140501 / 960) * t ^ 3 + (-14796437 / 57600) * t ^ 5 + (6387013 / 57600) * t ^ 7 + (1381753 / 691200) * t ^ 11 + (-59059 / 46080) * t ^ 13 + (-109 / 128) * d * t ^ 3 + (10687 / 172800) * d * t ^ 5 + (613423 / 1382400) * d * t ^ 7 + (288197 / 1382400) * d * t ^ 9 + (8221 / 460800) * d * t ^ 11 + (39013 / 4147200) * d * t ^ 13 + (433 / 15360) * d ^ 2 * t ^ 7 + (-1249 / 46080) * d ^ 2 * t ^ 9) * alpha_sq + ((327 / 32) * t ^ 3 + (-175411 / 23040) * t ^ 5 + (-1051 / 640) * t ^ 7 + (311 / 1920) * t ^ 9 + (47 / 2304) * t ^ 11 + (-109 / 128) * alpha * t ^ 3 + (76487 / 172800) * alpha * t ^ 5 + (465241 / 1382400) * alpha * t ^ 7 + (-1 / 6144) * alpha * t ^ 9 + (12971 / 460800) * alpha * t ^ 11 + (-47 / 55296) * alpha * t ^ 13) * d_sq
theorem v56_33 (t : ℂ) : (momentPoly 56 z56 3 3).eval t = (1025696 + (-2104479) * t ^ 2 + (614593737 / 400) * t ^ 4 + (-15010187399 / 20000) * t ^ 6 + (15539133049 / 40000) * t ^ 8 + (-3542937903 / 40000) * t ^ 10 + (326975141 / 120000) * t ^ 12 + (-65562943 / 40000) * t ^ 14 + (-338557 / 15000) * t ^ 18 + (-17987) * d * t ^ 2 + (2056023 / 80) * d * t ^ 4 + (-55243187 / 12000) * d * t ^ 6 + (-14087507 / 4800) * d * t ^ 8 + (-3590957 / 8000) * d * t ^ 10 + (2413229 / 72000) * d * t ^ 12 + (-1671863 / 24000) * d * t ^ 14) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_03, v55_10, v55_11, v55_12, v55_13, v55_20, v55_21, v55_22, v55_23, v55_30, v55_31, v55_32, v55_33]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23, phase53_30, phase53_31, phase53_32, phase53_33]
  try simp only [star_one, star_neg]
  linear_combination ((89935 / 96) * t ^ 2 + (-275121 / 320) * t ^ 4 + (-1586108819 / 2304000) * t ^ 6 + (133216319 / 230400) * t ^ 8 + (100558589 / 2304000) * t ^ 10 + (57186613 / 13824000) * t ^ 12 + (-17170261 / 4608000) * t ^ 14 + (-9624043 / 16588800) * t ^ 18 + (-35073 / 320) * d * t ^ 4 + (77218597 / 460800) * d * t ^ 6 + (-1728973 / 57600) * d * t ^ 8 + (-12833381 / 460800) * d * t ^ 10 + (-90899 / 76800) * d * t ^ 12 + (336373 / 691200) * d * t ^ 14 + (163 / 768) * d ^ 2 * t ^ 6 + (-51737 / 691200) * d ^ 2 * t ^ 8 + (-26909 / 230400) * d ^ 2 * t ^ 10 + (-983 / 153600) * d ^ 2 * t ^ 14) * alpha_sq + ((17987 / 32) * t ^ 2 + (-290601 / 320) * t ^ 4 + (145493647 / 460800) * t ^ 6 + (666863 / 115200) * t ^ 8 + (4689983 / 153600) * t ^ 10 + (3197983 / 2764800) * t ^ 12 + (-40953 / 102400) * t ^ 14 + (2209 / 221184) * t ^ 18) * d_sq
theorem v56_34 (t : ℂ) : (momentPoly 56 z56 3 4).eval t = (3993551 * t + (-215411217 / 40) * t ^ 3 + (3166080821 / 8000) * t ^ 5 + (1276796294087 / 9600000) * t ^ 7 + (7850434069897 / 6400000) * t ^ 9 + (-6370747860941 / 19200000) * t ^ 11 + (830912778793 / 23040000) * t ^ 13 + (-22096294197 / 800000) * t ^ 15 + (-89348129203 / 38400000) * t ^ 17 + (41760360677 / 57600000) * t ^ 19 + (-10662193701 / 12800000) * t ^ 21 + (-8457003977 / 115200000) * t ^ 25 + (-3993551 / 6) * d * t + (60594891 / 40) * d * t ^ 3 + (-1778585863 / 1600) * d * t ^ 5 + (711564229549 / 1920000) * d * t ^ 7 + (-720607009219 / 3840000) * d * t ^ 9 + (280083750697 / 3840000) * d * t ^ 11 + (38610911401 / 7680000) * d * t ^ 13 + (-199391459 / 480000) * d * t ^ 15 + (640864181 / 4608000) * d * t ^ 17 + (-3623603587 / 34560000) * d * t ^ 19 + (3036243221 / 23040000) * d * t ^ 21 + (9093103 / 13824000) * d * t ^ 25 + (3993551 / 6) * alpha * t + (-19974591 / 40) * alpha * t ^ 3 + (-10930953739 / 8000) * alpha * t ^ 5 + (15771394868407 / 9600000) * alpha * t ^ 7 + (-8292356439649 / 19200000) * alpha * t ^ 9 + (-177725921381 / 19200000) * alpha * t ^ 11 + (14361938993 / 4608000) * alpha * t ^ 13 + (-1480153007 / 800000) * alpha * t ^ 15 + (-232709342989 / 115200000) * alpha * t ^ 17 + (113156734231 / 172800000) * alpha * t ^ 19 + (-10309415609 / 115200000) * alpha * t ^ 21 + (-4563117431 / 345600000) * alpha * t ^ 25 + (-7588343 / 40) * alpha * d * t ^ 3 + (816232301 / 1600) * alpha * d * t ^ 5 + (-874509585823 / 1920000) * alpha * d * t ^ 7 + (539951449733 / 3840000) * alpha * d * t ^ 9 + (-22811491517 / 2304000) * alpha * d * t ^ 11 + (247599418297 / 69120000) * alpha * d * t ^ 13 + (1090867129 / 1440000) * alpha * d * t ^ 15 + (-238035851 / 4608000) * alpha * d * t ^ 17 + (-743787677 / 11520000) * alpha * d * t ^ 19 + (1198046029 / 23040000) * alpha * d * t ^ 21 + (-22126801 / 13824000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_03, v55_04, v55_10, v55_11, v55_12, v55_13, v55_14, v55_20, v55_21, v55_22, v55_23, v55_24, v55_30, v55_31, v55_32, v55_33, v55_34]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24, phase53_30, phase53_31, phase53_32, phase53_33, phase53_34]
  try simp only [star_one, star_neg]
  linear_combination ((7588343 / 160) * t ^ 3 + (-1153892869 / 9600) * t ^ 5 + (514431266077 / 5120000) * t ^ 7 + (-903492274151 / 30720000) * t ^ 9 + (12049668487 / 3072000) * t ^ 11 + (-1572423104869 / 552960000) * t ^ 13 + (169611321133 / 276480000) * t ^ 15 + (67303093 / 1536000) * t ^ 17 + (36791056907 / 1658880000) * t ^ 19 + (-399465133 / 30720000) * t ^ 21 + (67321969 / 55296000) * t ^ 25 + (-17661 / 64) * d * t ^ 3 + (83741 / 1200) * d * t ^ 5 + (10659752989 / 27648000) * d * t ^ 7 + (-56725073 / 1105920) * d * t ^ 9 + (-3170397911 / 27648000) * d * t ^ 11 + (-65325521 / 4147200) * d * t ^ 13 + (-114519449 / 165888000) * d * t ^ 15 + (-121752269 / 331776000) * d * t ^ 17 + (-13762231 / 36864000) * d * t ^ 19 + (4891747 / 66355200) * d * t ^ 21 + (741247 / 39813120) * d * t ^ 25 + (139859 / 7680) * d ^ 2 * t ^ 7 + (-1833283367 / 55296000) * d ^ 2 * t ^ 9 + (132786359 / 9216000) * d ^ 2 * t ^ 11 + (6887837 / 12288000) * d ^ 2 * t ^ 13 + (-11689 / 2048000) * d ^ 2 * t ^ 15 + (19411 / 737280) * d ^ 2 * t ^ 17 + (8227 / 294912) * d ^ 2 * t ^ 19 + (-98611 / 6912000) * d ^ 2 * t ^ 21) * alpha_sq + ((52983 / 16) * t ^ 3 + (-18768977 / 3840) * t ^ 5 + (7189471501 / 9216000) * t ^ 7 + (7081894321 / 9216000) * t ^ 9 + (208718719 / 3072000) * t ^ 11 + (-261178987 / 13824000) * t ^ 13 + (65359 / 6000) * t ^ 15 + (-19411 / 122880) * t ^ 17 + (-624631 / 6912000) * t ^ 19 + (777013 / 9216000) * t ^ 21 + (17661 / 64) * alpha * t ^ 3 + (-1396321 / 7200) * alpha * t ^ 5 + (-8745241549 / 27648000) * alpha * t ^ 7 + (23929249 / 122880) * alpha * t ^ 9 + (829996339 / 27648000) * alpha * t ^ 11 + (357069821 / 41472000) * alpha * t ^ 13 + (3612971 / 2211840) * alpha * t ^ 15 + (258689 / 7372800) * alpha * t ^ 17 + (121226959 / 331776000) * alpha * t ^ 19 + (756677 / 36864000) * alpha * t ^ 21 + (-4465 / 2654208) * alpha * t ^ 25) * d_sq
theorem v56_40 (t : ℂ) : (momentPoly 56 z56 4 0).eval t = ((28198 / 375) * t ^ 4 + (1053259 / 1000) * t ^ 6 + (-20810059 / 24000) * t ^ 8 + (1516931 / 18000) * t ^ 10 + (-306211 / 72000) * t ^ 16 + (-1567 / 160) * d * t ^ 4 + (-779 / 240) * d * t ^ 6 + (413 / 160) * d * t ^ 8 + (-47 / 72) * d * t ^ 10 + (-10752997 / 8000) * alpha * t ^ 4 + (18769151 / 12000) * alpha * t ^ 6 + (-4666937 / 16000) * alpha * t ^ 8 + (1766729 / 36000) * alpha * t ^ 10 + (-470783 / 48000) * alpha * t ^ 16 + (337051 / 14400) * alpha * d * t ^ 4 + (-16303 / 800) * alpha * d * t ^ 6 + (2963 / 5760) * alpha * d * t ^ 8 + (-30713 / 21600) * alpha * d * t ^ 10 + (-95 / 3456) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_10, v55_20, v55_30, v55_40]
  try simp only [phase53_00, phase53_10, phase53_20, phase53_30, phase53_40]
  try simp only [star_one, star_neg]
  linear_combination ((-10291 / 1600) * t ^ 4 + (36073 / 7200) * t ^ 6 + (24713 / 86400) * t ^ 10 + (433 / 640) * d * t ^ 4 + (-1229 / 2880) * d * t ^ 6 + (-413 / 1920) * d * t ^ 8 + (-1 / 768) * d ^ 2 * t ^ 6 + (1 / 4608) * d ^ 2 * t ^ 8) * alpha_sq + ((1913 / 2880) * t ^ 4 + (-563 / 1280) * t ^ 6 + (-1 / 1536) * t ^ 8 + (47 / 1152) * t ^ 10 + (-433 / 640) * alpha * t ^ 4 + (1259 / 1920) * alpha * t ^ 6) * d_sq
theorem v56_41 (t : ℂ) : (momentPoly 56 z56 4 1).eval t = ((84693 / 8) * t ^ 3 + (-82813423 / 9600) * t ^ 5 + (485301 / 1600) * t ^ 7 + (-3715693 / 3840) * t ^ 9 + (1759099 / 14400) * t ^ 11 + (37501 / 57600) * t ^ 17 + (-78589 / 60) * d * t ^ 3 + (275182373 / 144000) * d * t ^ 5 + (-6348797 / 8000) * d * t ^ 7 + (30139643 / 288000) * d * t ^ 9 + (1284101 / 72000) * d * t ^ 11 + (85033 / 96000) * d * t ^ 17 + (-2685869 / 300) * alpha * t ^ 3 + (1692766661 / 144000) * alpha * t ^ 5 + (-61991287 / 24000) * alpha * t ^ 7 + (-511189 / 288000) * alpha * t ^ 9 + (-3061747 / 8000) * alpha * t ^ 11 + (-2981557 / 288000) * alpha * t ^ 17 + (140501 / 120) * alpha * d * t ^ 3 + (-292934749 / 144000) * alpha * d * t ^ 5 + (6482181 / 8000) * alpha * d * t ^ 7 + (17270461 / 288000) * alpha * d * t ^ 9 + (-598559 / 216000) * alpha * d * t ^ 11 + (1388599 / 864000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_10, v55_11, v55_20, v55_21, v55_30, v55_31, v55_40, v55_41]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21, phase53_30, phase53_31, phase53_40, phase53_41]
  try simp only [star_one, star_neg]
  linear_combination ((-140501 / 480) * t ^ 3 + (26582513 / 48000) * t ^ 5 + (-315576599 / 1152000) * t ^ 7 + (470651 / 32000) * t ^ 9 + (-966383 / 288000) * t ^ 11 + (470783 / 1152000) * t ^ 17 + (109 / 64) * d * t ^ 3 + (-19783 / 23040) * d * t ^ 5 + (-13687 / 27648) * d * t ^ 7 + (-62719 / 276480) * d * t ^ 9 + (-47 / 4608) * d * t ^ 11 + (-95 / 165888) * d * t ^ 17 + (-433 / 15360) * d ^ 2 * t ^ 7 + (1249 / 46080) * d ^ 2 * t ^ 9) * alpha_sq + ((109 / 16) * t ^ 3 + (-111619 / 23040) * t ^ 5 + (-963 / 1280) * t ^ 7 + (-311 / 1920) * t ^ 9 + (47 / 576) * t ^ 11 + (-109 / 64) * alpha * t ^ 3 + (17317 / 115200) * alpha * t ^ 5 + (313619 / 230400) * alpha * t ^ 7 + (-1151 / 30720) * alpha * t ^ 9 + (10621 / 115200) * alpha * t ^ 11 + (95 / 55296) * alpha * t ^ 17) * d_sq
theorem v56_42 (t : ℂ) : (momentPoly 56 z56 4 2).eval t = ((23760827 / 30) * t ^ 2 + (-145181519 / 100) * t ^ 4 + (57510287981 / 80000) * t ^ 6 + (-8701724267 / 120000) * t ^ 8 + (23038103 / 750) * t ^ 10 + (-4821882209 / 480000) * t ^ 12 + (57061957 / 60000) * t ^ 14 + (127884611 / 720000) * t ^ 18 + (-397322177 / 1440000) * t ^ 20 + (-35974 / 3) * d * t ^ 2 + (80379 / 5) * d * t ^ 4 + (-69149929 / 28800) * d * t ^ 6 + (-12848171 / 8000) * d * t ^ 8 + (-1703189 / 4000) * d * t ^ 10 + (23224151 / 288000) * d * t ^ 12 + (-183233 / 4500) * d * t ^ 14 + (27823 / 48000) * d * t ^ 18 + (-127523 / 288000) * d * t ^ 20 + (-23005373 / 60) * alpha * t ^ 2 + (177206451 / 200) * alpha * t ^ 4 + (-117989121049 / 180000) * alpha * t ^ 6 + (40320535541 / 240000) * alpha * t ^ 8 + (-2461796377 / 96000) * alpha * t ^ 10 + (8107465229 / 720000) * alpha * t ^ 12 + (-380019713 / 360000) * alpha * t ^ 14 + (-115339111 / 480000) * alpha * t ^ 18 + (158296 / 1875) * alpha * t ^ 20 + (89935 / 36) * alpha * d * t ^ 2 + (-312713 / 600) * alpha * d * t ^ 4 + (-696423937 / 144000) * alpha * d * t ^ 6 + (91696193 / 36000) * alpha * d * t ^ 8 + (14598509 / 72000) * alpha * d * t ^ 10 + (96912859 / 864000) * alpha * d * t ^ 12 + (901621 / 54000) * alpha * d * t ^ 14 + (548123 / 144000) * alpha * d * t ^ 18 + (9341 / 96000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_10, v55_11, v55_12, v55_20, v55_21, v55_22, v55_30, v55_31, v55_32, v55_40, v55_41, v55_42]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22, phase53_30, phase53_31, phase53_32, phase53_40, phase53_41, phase53_42]
  try simp only [star_one, star_neg]
  linear_combination ((-89935 / 144) * t ^ 2 + (1014249 / 800) * t ^ 4 + (-1298105941 / 2304000) * t ^ 6 + (-324509879 / 3456000) * t ^ 8 + (-41050609 / 4608000) * t ^ 10 + (16987409 / 518400) * t ^ 12 + (-19318759 / 2592000) * t ^ 14 + (40621481 / 41472000) * t ^ 18 + (-44262173 / 6912000) * d * t ^ 6 + (4772239 / 691200) * d * t ^ 8 + (239873 / 6912000) * d * t ^ 10 + (-372667 / 230400) * d * t ^ 12 + (5315177 / 5184000) * d * t ^ 14 + (-1806793 / 10368000) * d * t ^ 18 + (127523 / 3456000) * d * t ^ 20 + (253997 / 4147200) * d ^ 2 * t ^ 8 + (-76081 / 1382400) * d ^ 2 * t ^ 10 + (191 / 122880) * d ^ 2 * t ^ 12 + (-4723 / 1382400) * d ^ 2 * t ^ 14 + (95 / 221184) * d ^ 2 * t ^ 18 + (-95 / 663552) * d ^ 2 * t ^ 20) * alpha_sq + ((17987 / 48) * t ^ 2 + (-85389 / 160) * t ^ 4 + (70218889 / 768000) * t ^ 6 + (139969811 / 2304000) * t ^ 8 + (75636017 / 4608000) * t ^ 10 + (-70625629 / 27648000) * t ^ 12 + (-125209 / 460800) * t ^ 14 + (-616073 / 9216000) * t ^ 18 + (95 / 221184) * t ^ 20 + (-11691 / 80) * alpha * t ^ 4 + (1844104967 / 6912000) * alpha * t ^ 6 + (-802698229 / 6912000) * alpha * t ^ 8 + (-1196577 / 256000) * alpha * t ^ 10 + (1320877 / 4608000) * alpha * t ^ 12 + (-58703 / 138240) * alpha * t ^ 14 + (-1364849 / 13824000) * alpha * t ^ 18) * d_sq
theorem v56_43 (t : ℂ) : (momentPoly 56 z56 4 3).eval t = (3993551 * t + (-215411217 / 40) * t ^ 3 + (3166080821 / 8000) * t ^ 5 + (1276796294087 / 9600000) * t ^ 7 + (7850434069897 / 6400000) * t ^ 9 + (-6370747860941 / 19200000) * t ^ 11 + (830912778793 / 23040000) * t ^ 13 + (-22096294197 / 800000) * t ^ 15 + (-89348129203 / 38400000) * t ^ 17 + (41760360677 / 57600000) * t ^ 19 + (-10662193701 / 12800000) * t ^ 21 + (-8457003977 / 115200000) * t ^ 25 + (-3993551 / 6) * d * t + (60594891 / 40) * d * t ^ 3 + (-1778585863 / 1600) * d * t ^ 5 + (711564229549 / 1920000) * d * t ^ 7 + (-720607009219 / 3840000) * d * t ^ 9 + (280083750697 / 3840000) * d * t ^ 11 + (38610911401 / 7680000) * d * t ^ 13 + (-199391459 / 480000) * d * t ^ 15 + (640864181 / 4608000) * d * t ^ 17 + (-3623603587 / 34560000) * d * t ^ 19 + (3036243221 / 23040000) * d * t ^ 21 + (9093103 / 13824000) * d * t ^ 25 + (-3993551 / 6) * alpha * t + (19974591 / 40) * alpha * t ^ 3 + (10930953739 / 8000) * alpha * t ^ 5 + (-15771394868407 / 9600000) * alpha * t ^ 7 + (8292356439649 / 19200000) * alpha * t ^ 9 + (177725921381 / 19200000) * alpha * t ^ 11 + (-14361938993 / 4608000) * alpha * t ^ 13 + (1480153007 / 800000) * alpha * t ^ 15 + (232709342989 / 115200000) * alpha * t ^ 17 + (-113156734231 / 172800000) * alpha * t ^ 19 + (10309415609 / 115200000) * alpha * t ^ 21 + (4563117431 / 345600000) * alpha * t ^ 25 + (7588343 / 40) * alpha * d * t ^ 3 + (-816232301 / 1600) * alpha * d * t ^ 5 + (874509585823 / 1920000) * alpha * d * t ^ 7 + (-539951449733 / 3840000) * alpha * d * t ^ 9 + (22811491517 / 2304000) * alpha * d * t ^ 11 + (-247599418297 / 69120000) * alpha * d * t ^ 13 + (-1090867129 / 1440000) * alpha * d * t ^ 15 + (238035851 / 4608000) * alpha * d * t ^ 17 + (743787677 / 11520000) * alpha * d * t ^ 19 + (-1198046029 / 23040000) * alpha * d * t ^ 21 + (22126801 / 13824000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_03, v55_10, v55_11, v55_12, v55_13, v55_20, v55_21, v55_22, v55_23, v55_30, v55_31, v55_32, v55_33, v55_40, v55_41, v55_42, v55_43]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23, phase53_30, phase53_31, phase53_32, phase53_33, phase53_40, phase53_41, phase53_42, phase53_43]
  try simp only [star_one, star_neg]
  linear_combination ((7588343 / 160) * t ^ 3 + (-1153892869 / 9600) * t ^ 5 + (514431266077 / 5120000) * t ^ 7 + (-903492274151 / 30720000) * t ^ 9 + (12049668487 / 3072000) * t ^ 11 + (-1572423104869 / 552960000) * t ^ 13 + (169611321133 / 276480000) * t ^ 15 + (67303093 / 1536000) * t ^ 17 + (36791056907 / 1658880000) * t ^ 19 + (-399465133 / 30720000) * t ^ 21 + (67321969 / 55296000) * t ^ 25 + (-17661 / 64) * d * t ^ 3 + (83741 / 1200) * d * t ^ 5 + (10659752989 / 27648000) * d * t ^ 7 + (-56725073 / 1105920) * d * t ^ 9 + (-3170397911 / 27648000) * d * t ^ 11 + (-65325521 / 4147200) * d * t ^ 13 + (-114519449 / 165888000) * d * t ^ 15 + (-121752269 / 331776000) * d * t ^ 17 + (-13762231 / 36864000) * d * t ^ 19 + (4891747 / 66355200) * d * t ^ 21 + (741247 / 39813120) * d * t ^ 25 + (139859 / 7680) * d ^ 2 * t ^ 7 + (-1833283367 / 55296000) * d ^ 2 * t ^ 9 + (132786359 / 9216000) * d ^ 2 * t ^ 11 + (6887837 / 12288000) * d ^ 2 * t ^ 13 + (-11689 / 2048000) * d ^ 2 * t ^ 15 + (19411 / 737280) * d ^ 2 * t ^ 17 + (8227 / 294912) * d ^ 2 * t ^ 19 + (-98611 / 6912000) * d ^ 2 * t ^ 21) * alpha_sq + ((52983 / 16) * t ^ 3 + (-18768977 / 3840) * t ^ 5 + (7189471501 / 9216000) * t ^ 7 + (7081894321 / 9216000) * t ^ 9 + (208718719 / 3072000) * t ^ 11 + (-261178987 / 13824000) * t ^ 13 + (65359 / 6000) * t ^ 15 + (-19411 / 122880) * t ^ 17 + (-624631 / 6912000) * t ^ 19 + (777013 / 9216000) * t ^ 21 + (-17661 / 64) * alpha * t ^ 3 + (1396321 / 7200) * alpha * t ^ 5 + (8745241549 / 27648000) * alpha * t ^ 7 + (-23929249 / 122880) * alpha * t ^ 9 + (-829996339 / 27648000) * alpha * t ^ 11 + (-357069821 / 41472000) * alpha * t ^ 13 + (-3612971 / 2211840) * alpha * t ^ 15 + (-258689 / 7372800) * alpha * t ^ 17 + (-121226959 / 331776000) * alpha * t ^ 19 + (-756677 / 36864000) * alpha * t ^ 21 + (4465 / 2654208) * alpha * t ^ 25) * d_sq
theorem v56_44 (t : ℂ) : (momentPoly 56 z56 4 4).eval t = (223638856 + (-606260616) * t ^ 2 + (65776705013 / 100) * t ^ 4 + (-2431449252363 / 5000) * t ^ 6 + (31901941978266017 / 96000000) * t ^ 8 + (-3377077749213187 / 24000000) * t ^ 10 + (88465401628427 / 3840000) * t ^ 12 + (-81127243135653 / 16000000) * t ^ 14 + (2277213218216707 / 1152000000) * t ^ 16 + (-32186233084333 / 144000000) * t ^ 18 + (78967428491387 / 864000000) * t ^ 20 + (-12687173056183 / 144000000) * t ^ 22 + (1343966063547 / 64000000) * t ^ 24 + (-428815990589 / 144000000) * t ^ 26 + (870827963977 / 3456000000) * t ^ 32 + (-15545144 / 3) * d * t ^ 2 + (220045227 / 20) * d * t ^ 4 + (-17820063019 / 3000) * d * t ^ 6 + (-15273538646261 / 57600000) * d * t ^ 8 + (-73330779967 / 4800000) * d * t ^ 10 + (22321340102069 / 57600000) * d * t ^ 12 + (-47939951189 / 1152000) * d * t ^ 14 + (9505492450723 / 230400000) * d * t ^ 16 + (43591842341 / 9600000) * d * t ^ 18 + (-183497401913 / 172800000) * d * t ^ 20 + (34204503313 / 28800000) * d * t ^ 22 + (15884439 / 2560000) * d * t ^ 24 + (7240379477 / 86400000) * d * t ^ 26 + (8944877 / 5529600) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_03, v55_04, v55_10, v55_11, v55_12, v55_13, v55_14, v55_20, v55_21, v55_22, v55_23, v55_24, v55_30, v55_31, v55_32, v55_33, v55_34, v55_40, v55_41, v55_42, v55_43, v55_44]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24, phase53_30, phase53_31, phase53_32, phase53_33, phase53_34, phase53_40, phase53_41, phase53_42, phase53_43, phase53_44]
  try simp only [star_one, star_neg]
  linear_combination ((9715715 / 36) * t ^ 2 + (-265002661 / 720) * t ^ 4 + (-35125994057 / 144000) * t ^ 6 + (174824346320489 / 345600000) * t ^ 8 + (-50741532317659 / 345600000) * t ^ 10 + (-4233456444077 / 691200000) * t ^ 12 + (-1736243669393 / 138240000) * t ^ 14 + (1057724432483 / 518400000) * t ^ 16 + (-39030112717 / 76800000) * t ^ 18 + (3486132263407 / 6220800000) * t ^ 20 + (-91118072209 / 2073600000) * t ^ 22 + (2745474529 / 388800000) * t ^ 26 + (-3753677 / 80) * d * t ^ 4 + (1085564527 / 9600) * d * t ^ 6 + (-5364461748337 / 69120000) * d * t ^ 8 + (165997362523 / 46080000) * d * t ^ 10 + (197222372567 / 30720000) * d * t ^ 12 + (152159389847 / 103680000) * d * t ^ 14 + (80778130661 / 1658880000) * d * t ^ 16 + (-21559626427 / 207360000) * d * t ^ 18 + (-11270337433 / 414720000) * d * t ^ 20 + (5097006001 / 207360000) * d * t ^ 22 + (-5294813 / 10240000) * d * t ^ 24 + (-5782099 / 6220800) * d * t ^ 26 + (-8944877 / 66355200) * d * t ^ 32 + (35105 / 384) * d ^ 2 * t ^ 6 + (-2536343 / 51840) * d ^ 2 * t ^ 8 + (-11052437909 / 82944000) * d ^ 2 * t ^ 10 + (13051950989 / 165888000) * d ^ 2 * t ^ 12 + (23078581 / 2764800) * d ^ 2 * t ^ 14 + (78032729 / 22118400) * d ^ 2 * t ^ 16 + (44066993 / 82944000) * d ^ 2 * t ^ 18 + (4825943 / 19906560) * d ^ 2 * t ^ 20 + (-29943547 / 331776000) * d ^ 2 * t ^ 22 + (236603 / 24576000) * d ^ 2 * t ^ 24 + (-89737 / 6635520) * d ^ 2 * t ^ 26 + (-9025 / 31850496) * d ^ 2 * t ^ 32) * alpha_sq + ((1943143 / 12) * t ^ 2 + (-93304447 / 240) * t ^ 4 + (1075417117 / 3600) * t ^ 6 + (-6562422033131 / 69120000) * t ^ 8 + (2060166581657 / 46080000) * t ^ 10 + (-5501793642451 / 276480000) * t ^ 12 + (-256919935087 / 138240000) * t ^ 14 + (190723407517 / 552960000) * t ^ 16 + (-10811863 / 184320) * t ^ 18 + (16544025847 / 829440000) * t ^ 20 + (-17172416501 / 552960000) * t ^ 22 + (-236603 / 8192000) * t ^ 24 + (-23352331 / 55296000) * t ^ 26 + (9025 / 10616832) * t ^ 32) * d_sq
#print axioms v56_00
#print axioms v56_11
#print axioms v56_22
#print axioms v56_33
#print axioms v56_44
end PhotonCertA
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
theorem site57 : ((r ^ 3 * phiMinus) : ℂ) = ((1 / 24) * d + (1 / 24) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 64) * d + (-1 / 64) * alpha + (-1 / 192) * alpha * d + (-1 / 192) * alpha ^ 2) * alpha_sq
theorem phase57_00 : ((r ^ 3 * phiMinus) : ℂ) ^ 0 * star ((r ^ 3 * phiMinus) : ℂ) ^ 0 = (1) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase57_01 : ((r ^ 3 * phiMinus) : ℂ) ^ 0 * star ((r ^ 3 * phiMinus) : ℂ) ^ 1 = ((1 / 24) * d + (-1 / 24) * alpha) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase57_02 : ((r ^ 3 * phiMinus) : ℂ) ^ 0 * star ((r ^ 3 * phiMinus) : ℂ) ^ 2 = ((95 / 96) + (-1 / 288) * alpha * d) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 576)) * alpha_sq + ((1 / 576)) * d_sq
theorem phase57_03 : ((r ^ 3 * phiMinus) : ℂ) ^ 0 * star ((r ^ 3 * phiMinus) : ℂ) ^ 3 = ((47 / 1152) * d + (-143 / 1152) * alpha) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 4608) * d + (-1 / 13824) * alpha) * alpha_sq + ((1 / 13824) * d + (-1 / 4608) * alpha) * d_sq
theorem phase57_04 : ((r ^ 3 * phiMinus) : ℂ) ^ 0 * star ((r ^ 3 * phiMinus) : ℂ) ^ 4 = ((4417 / 4608) + (-95 / 13824) * alpha * d) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 110592) + (1 / 55296) * d ^ 2 + (-1 / 82944) * alpha * d + (1 / 331776) * alpha ^ 2) * alpha_sq + ((185 / 110592) + (1 / 331776) * d ^ 2 + (-1 / 82944) * alpha * d) * d_sq
theorem phase57_10 : ((r ^ 3 * phiMinus) : ℂ) ^ 1 * star ((r ^ 3 * phiMinus) : ℂ) ^ 0 = ((1 / 24) * d + (1 / 24) * alpha) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase57_11 : ((r ^ 3 * phiMinus) : ℂ) ^ 1 * star ((r ^ 3 * phiMinus) : ℂ) ^ 1 = (1) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 576)) * alpha_sq + ((1 / 576)) * d_sq
theorem phase57_12 : ((r ^ 3 * phiMinus) : ℂ) ^ 1 * star ((r ^ 3 * phiMinus) : ℂ) ^ 2 = ((1 / 24) * d + (-1 / 24) * alpha) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 13824) * d + (1 / 13824) * alpha) * alpha_sq + ((1 / 13824) * d + (-1 / 13824) * alpha) * d_sq
theorem phase57_13 : ((r ^ 3 * phiMinus) : ℂ) ^ 1 * star ((r ^ 3 * phiMinus) : ℂ) ^ 3 = ((95 / 96) + (-1 / 288) * alpha * d) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 110592) + (1 / 165888) * alpha * d + (-1 / 331776) * alpha ^ 2) * alpha_sq + ((191 / 110592) + (1 / 331776) * d ^ 2 + (-1 / 165888) * alpha * d) * d_sq
theorem phase57_14 : ((r ^ 3 * phiMinus) : ℂ) ^ 1 * star ((r ^ 3 * phiMinus) : ℂ) ^ 4 = ((47 / 1152) * d + (-143 / 1152) * alpha) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 884736) * d + (1 / 3981312) * d ^ 3 + (-1 / 2654208) * alpha + (1 / 3981312) * alpha * d ^ 2 + (-1 / 2654208) * alpha ^ 2 * d + (1 / 7962624) * alpha ^ 3) * alpha_sq + ((7 / 98304) * d + (1 / 7962624) * d ^ 3 + (-575 / 2654208) * alpha + (-1 / 2654208) * alpha * d ^ 2) * d_sq
theorem phase57_20 : ((r ^ 3 * phiMinus) : ℂ) ^ 2 * star ((r ^ 3 * phiMinus) : ℂ) ^ 0 = ((95 / 96) + (1 / 288) * alpha * d) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 576)) * alpha_sq + ((1 / 576)) * d_sq
theorem phase57_21 : ((r ^ 3 * phiMinus) : ℂ) ^ 2 * star ((r ^ 3 * phiMinus) : ℂ) ^ 1 = ((1 / 24) * d + (1 / 24) * alpha) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 13824) * d + (-1 / 13824) * alpha) * alpha_sq + ((1 / 13824) * d + (1 / 13824) * alpha) * d_sq
theorem phase57_22 : ((r ^ 3 * phiMinus) : ℂ) ^ 2 * star ((r ^ 3 * phiMinus) : ℂ) ^ 2 = (1) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 110592) + (-1 / 165888) * d ^ 2 + (1 / 331776) * alpha ^ 2) * alpha_sq + ((193 / 110592) + (1 / 331776) * d ^ 2) * d_sq
theorem phase57_23 : ((r ^ 3 * phiMinus) : ℂ) ^ 2 * star ((r ^ 3 * phiMinus) : ℂ) ^ 3 = ((1 / 24) * d + (-1 / 24) * alpha) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 2654208) * d + (-1 / 3981312) * d ^ 3 + (1 / 2654208) * alpha + (1 / 3981312) * alpha * d ^ 2 + (1 / 7962624) * alpha ^ 2 * d + (-1 / 7962624) * alpha ^ 3) * alpha_sq + ((193 / 2654208) * d + (1 / 7962624) * d ^ 3 + (-193 / 2654208) * alpha + (-1 / 7962624) * alpha * d ^ 2) * d_sq
theorem phase57_24 : ((r ^ 3 * phiMinus) : ℂ) ^ 2 * star ((r ^ 3 * phiMinus) : ℂ) ^ 4 = ((95 / 96) + (-1 / 288) * alpha * d) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 21233664) + (1 / 63700992) * d ^ 2 + (-1 / 191102976) * d ^ 4 + (1 / 31850496) * alpha * d + (1 / 47775744) * alpha * d ^ 3 + (-1 / 63700992) * alpha ^ 2 + (-1 / 191102976) * alpha ^ 2 * d ^ 2 + (-1 / 95551488) * alpha ^ 3 * d + (1 / 191102976) * alpha ^ 4) * alpha_sq + ((36671 / 21233664) + (1 / 331776) * d ^ 2 + (1 / 191102976) * d ^ 4 + (-193 / 31850496) * alpha * d + (-1 / 95551488) * alpha * d ^ 3) * d_sq
theorem phase57_30 : ((r ^ 3 * phiMinus) : ℂ) ^ 3 * star ((r ^ 3 * phiMinus) : ℂ) ^ 0 = ((47 / 1152) * d + (143 / 1152) * alpha) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 4608) * d + (1 / 13824) * alpha) * alpha_sq + ((1 / 13824) * d + (1 / 4608) * alpha) * d_sq
theorem phase57_31 : ((r ^ 3 * phiMinus) : ℂ) ^ 3 * star ((r ^ 3 * phiMinus) : ℂ) ^ 1 = ((95 / 96) + (1 / 288) * alpha * d) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 110592) + (-1 / 165888) * alpha * d + (-1 / 331776) * alpha ^ 2) * alpha_sq + ((191 / 110592) + (1 / 331776) * d ^ 2 + (1 / 165888) * alpha * d) * d_sq
theorem phase57_32 : ((r ^ 3 * phiMinus) : ℂ) ^ 3 * star ((r ^ 3 * phiMinus) : ℂ) ^ 2 = ((1 / 24) * d + (1 / 24) * alpha) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 2654208) * d + (-1 / 3981312) * d ^ 3 + (-1 / 2654208) * alpha + (-1 / 3981312) * alpha * d ^ 2 + (1 / 7962624) * alpha ^ 2 * d + (1 / 7962624) * alpha ^ 3) * alpha_sq + ((193 / 2654208) * d + (1 / 7962624) * d ^ 3 + (193 / 2654208) * alpha + (1 / 7962624) * alpha * d ^ 2) * d_sq
theorem phase57_33 : ((r ^ 3 * phiMinus) : ℂ) ^ 3 * star ((r ^ 3 * phiMinus) : ℂ) ^ 3 = (1) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 21233664) + (-1 / 21233664) * d ^ 2 + (-1 / 63700992) * d ^ 4 + (1 / 63700992) * alpha ^ 2 + (1 / 63700992) * alpha ^ 2 * d ^ 2 + (-1 / 191102976) * alpha ^ 4) * alpha_sq + ((37057 / 21233664) + (97 / 31850496) * d ^ 2 + (1 / 191102976) * d ^ 4) * d_sq
theorem phase57_34 : ((r ^ 3 * phiMinus) : ℂ) ^ 3 * star ((r ^ 3 * phiMinus) : ℂ) ^ 4 = ((1 / 24) * d + (-1 / 24) * alpha) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 509607936) * d + (-1 / 509607936) * d ^ 3 + (-1 / 1528823808) * d ^ 5 + (1 / 509607936) * alpha + (1 / 509607936) * alpha * d ^ 2 + (1 / 1528823808) * alpha * d ^ 4 + (1 / 1528823808) * alpha ^ 2 * d + (1 / 1528823808) * alpha ^ 2 * d ^ 3 + (-1 / 1528823808) * alpha ^ 3 + (-1 / 1528823808) * alpha ^ 3 * d ^ 2 + (-1 / 4586471424) * alpha ^ 4 * d + (1 / 4586471424) * alpha ^ 5) * alpha_sq + ((37057 / 509607936) * d + (97 / 764411904) * d ^ 3 + (1 / 4586471424) * d ^ 5 + (-37057 / 509607936) * alpha + (-97 / 764411904) * alpha * d ^ 2 + (-1 / 4586471424) * alpha * d ^ 4) * d_sq
theorem phase57_40 : ((r ^ 3 * phiMinus) : ℂ) ^ 4 * star ((r ^ 3 * phiMinus) : ℂ) ^ 0 = ((4417 / 4608) + (95 / 13824) * alpha * d) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 110592) + (1 / 55296) * d ^ 2 + (1 / 82944) * alpha * d + (1 / 331776) * alpha ^ 2) * alpha_sq + ((185 / 110592) + (1 / 331776) * d ^ 2 + (1 / 82944) * alpha * d) * d_sq
theorem phase57_41 : ((r ^ 3 * phiMinus) : ℂ) ^ 4 * star ((r ^ 3 * phiMinus) : ℂ) ^ 1 = ((47 / 1152) * d + (143 / 1152) * alpha) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 884736) * d + (1 / 3981312) * d ^ 3 + (1 / 2654208) * alpha + (-1 / 3981312) * alpha * d ^ 2 + (-1 / 2654208) * alpha ^ 2 * d + (-1 / 7962624) * alpha ^ 3) * alpha_sq + ((7 / 98304) * d + (1 / 7962624) * d ^ 3 + (575 / 2654208) * alpha + (1 / 2654208) * alpha * d ^ 2) * d_sq
theorem phase57_42 : ((r ^ 3 * phiMinus) : ℂ) ^ 4 * star ((r ^ 3 * phiMinus) : ℂ) ^ 2 = ((95 / 96) + (1 / 288) * alpha * d) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 21233664) + (1 / 63700992) * d ^ 2 + (-1 / 191102976) * d ^ 4 + (-1 / 31850496) * alpha * d + (-1 / 47775744) * alpha * d ^ 3 + (-1 / 63700992) * alpha ^ 2 + (-1 / 191102976) * alpha ^ 2 * d ^ 2 + (1 / 95551488) * alpha ^ 3 * d + (1 / 191102976) * alpha ^ 4) * alpha_sq + ((36671 / 21233664) + (1 / 331776) * d ^ 2 + (1 / 191102976) * d ^ 4 + (193 / 31850496) * alpha * d + (1 / 95551488) * alpha * d ^ 3) * d_sq
theorem phase57_43 : ((r ^ 3 * phiMinus) : ℂ) ^ 4 * star ((r ^ 3 * phiMinus) : ℂ) ^ 3 = ((1 / 24) * d + (1 / 24) * alpha) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 509607936) * d + (-1 / 509607936) * d ^ 3 + (-1 / 1528823808) * d ^ 5 + (-1 / 509607936) * alpha + (-1 / 509607936) * alpha * d ^ 2 + (-1 / 1528823808) * alpha * d ^ 4 + (1 / 1528823808) * alpha ^ 2 * d + (1 / 1528823808) * alpha ^ 2 * d ^ 3 + (1 / 1528823808) * alpha ^ 3 + (1 / 1528823808) * alpha ^ 3 * d ^ 2 + (-1 / 4586471424) * alpha ^ 4 * d + (-1 / 4586471424) * alpha ^ 5) * alpha_sq + ((37057 / 509607936) * d + (97 / 764411904) * d ^ 3 + (1 / 4586471424) * d ^ 5 + (37057 / 509607936) * alpha + (97 / 764411904) * alpha * d ^ 2 + (1 / 4586471424) * alpha * d ^ 4) * d_sq
theorem phase57_44 : ((r ^ 3 * phiMinus) : ℂ) ^ 4 * star ((r ^ 3 * phiMinus) : ℂ) ^ 4 = (1) := by
  rw [site57]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 4076863488) + (-1 / 3057647616) * d ^ 2 + (-1 / 6115295232) * d ^ 4 + (-1 / 27518828544) * d ^ 6 + (1 / 12230590464) * alpha ^ 2 + (1 / 9172942848) * alpha ^ 2 * d ^ 2 + (1 / 18345885696) * alpha ^ 2 * d ^ 4 + (-1 / 36691771392) * alpha ^ 4 + (-1 / 27518828544) * alpha ^ 4 * d ^ 2 + (1 / 110075314176) * alpha ^ 6) * alpha_sq + ((7114945 / 4076863488) + (4139 / 1358954496) * d ^ 2 + (65 / 12230590464) * d ^ 4 + (1 / 110075314176) * d ^ 6) * d_sq
noncomputable def z57 : Fin 57 → ℂ := Fin.snoc z56 (r ^ 3 * phiMinus)
theorem v57_00 (t : ℂ) : (momentPoly 57 z57 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00]
  try simp only [phase57_00]
  try simp only [star_one, star_neg]
  ring
theorem v57_01 (t : ℂ) : (momentPoly 57 z57 0 1).eval t = (1 * t + (-1 / 8) * d * t + (1 / 8) * alpha * t) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01]
  try simp only [phase57_00, phase57_01]
  try simp only [star_one, star_neg]
  ring
theorem v57_02 (t : ℂ) : (momentPoly 57 z57 0 2).eval t = ((141 / 10) * t ^ 2 + (-671 / 160) * t ^ 4 + (-1 / 4) * d * t ^ 2 + (423 / 40) * alpha * t ^ 2 + (-413 / 40) * alpha * t ^ 4 + (-1 / 24) * alpha * d * t ^ 2 + (1 / 96) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02]
  try simp only [phase57_00, phase57_01, phase57_02]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 72) * t ^ 2) * alpha_sq + ((-1 / 72) * t ^ 2) * d_sq
theorem v57_03 (t : ℂ) : (momentPoly 57 z57 0 3).eval t = ((9179 / 320) * t ^ 3 + (-309 / 320) * t ^ 5 + (-3151 / 960) * d * t ^ 3 + (617 / 320) * d * t ^ 5 + (-47 / 384) * d * t ^ 9 + (160043 / 4800) * alpha * t ^ 3 + (-43249 / 1600) * alpha * t ^ 5 + (-24817 / 9600) * alpha * t ^ 9 + (-1279 / 320) * alpha * d * t ^ 3 + (1249 / 320) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_03]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03]
  try simp only [star_one, star_neg]
  linear_combination ((-1279 / 960) * t ^ 3 + (413 / 320) * t ^ 5 + (5 / 576) * d * t ^ 3 + (-1 / 288) * d * t ^ 5) * alpha_sq + ((-1 / 24) * t ^ 3 + (-5 / 576) * alpha * t ^ 3 + (1 / 288) * alpha * t ^ 5) * d_sq
theorem v57_04 (t : ℂ) : (momentPoly 57 z57 0 4).eval t = ((-478067 / 1000) * t ^ 4 + (23338949 / 16000) * t ^ 6 + (-14357831 / 16000) * t ^ 8 + (625459 / 12000) * t ^ 10 + (-632521 / 192000) * t ^ 16 + (-421 / 96) * d * t ^ 4 + (-1259 / 640) * d * t ^ 6 + (1239 / 640) * d * t ^ 8 + (-47 / 96) * d * t ^ 10 + (19754791 / 24000) * alpha * t ^ 4 + (-15997193 / 16000) * alpha * t ^ 6 + (1843031 / 8000) * alpha * t ^ 8 + (-148717 / 3000) * alpha * t ^ 10 + (470783 / 48000) * alpha * t ^ 16 + (-74689 / 4800) * alpha * d * t ^ 4 + (134117 / 9600) * alpha * d * t ^ 6 + (-311 / 960) * alpha * d * t ^ 8 + (517 / 450) * alpha * d * t ^ 10 + (95 / 4608) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_03, v56_04]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04]
  try simp only [star_one, star_neg]
  linear_combination ((-24641 / 3600) * t ^ 4 + (72391 / 14400) * t ^ 6 + (221 / 675) * t ^ 10 + (1289 / 1440) * d * t ^ 4 + (-1255 / 1152) * d * t ^ 6 + (413 / 1920) * d * t ^ 8 + (5 / 3456) * d ^ 2 * t ^ 6 + (-1 / 3456) * d ^ 2 * t ^ 8) * alpha_sq + ((-721 / 720) * t ^ 4 + (971 / 1920) * t ^ 6 + (1 / 1152) * t ^ 8 + (-47 / 864) * t ^ 10 + (-1289 / 1440) * alpha * t ^ 4 + (1259 / 1440) * alpha * t ^ 6) * d_sq
theorem v57_10 (t : ℂ) : (momentPoly 57 z57 1 0).eval t = (1 * t + (-1 / 8) * d * t + (-1 / 8) * alpha * t) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_10]
  try simp only [phase57_00, phase57_10]
  try simp only [star_one, star_neg]
  ring
theorem v57_11 (t : ℂ) : (momentPoly 57 z57 1 1).eval t = (57 + (-47) * t ^ 2 + (-1 / 4) * d * t ^ 2) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_10, v56_11]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 72) * t ^ 2) * alpha_sq + ((-1 / 72) * t ^ 2) * d_sq
theorem v57_12 (t : ℂ) : (momentPoly 57 z57 1 2).eval t = (113 * t + (-24329 / 320) * t ^ 3 + (-2901 / 320) * t ^ 5 + (-113 / 8) * d * t + (3831 / 320) * d * t ^ 3 + (209 / 320) * d * t ^ 5 + (113 / 8) * alpha * t + (-141 / 64) * alpha * t ^ 3 + (-683 / 64) * alpha * t ^ 5 + (-1279 / 960) * alpha * d * t ^ 3 + (1249 / 960) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_10, v56_11, v56_12]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12]
  try simp only [star_one, star_neg]
  linear_combination ((1279 / 2880) * t ^ 3 + (-413 / 960) * t ^ 5 + (-5 / 1728) * d * t ^ 3 + (1 / 864) * d * t ^ 5) * alpha_sq + ((-1 / 24) * t ^ 3 + (-5 / 1728) * alpha * t ^ 3 + (1 / 864) * alpha * t ^ 5) * d_sq
theorem v57_13 (t : ℂ) : (momentPoly 57 z57 1 3).eval t = ((11844 / 5) * t ^ 2 + (-4414339 / 1600) * t ^ 4 + (1641747 / 3200) * t ^ 6 + (38371 / 3200) * t ^ 10 + (-42) * d * t ^ 2 + (1973 / 60) * d * t ^ 4 + (341 / 80) * d * t ^ 6 + (-47 / 384) * d * t ^ 10 + (8883 / 5) * alpha * t ^ 2 + (-7617041 / 2400) * alpha * t ^ 4 + (1117123 / 800) * alpha * t ^ 6 + (74303 / 9600) * alpha * t ^ 10 + (-7) * alpha * d * t ^ 2 + (4229 / 4800) * alpha * d * t ^ 4 + (17331 / 3200) * alpha * d * t ^ 6 + (3149 / 9600) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_03, v56_10, v56_11, v56_12, v56_13]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13]
  try simp only [star_one, star_neg]
  linear_combination ((-7 / 3) * t ^ 2 + (66247 / 28800) * t ^ 4 + (6479 / 57600) * t ^ 6 + (-221 / 2700) * t ^ 10) * alpha_sq + ((-7 / 3) * t ^ 2 + (8851 / 5760) * t ^ 4 + (2963 / 11520) * t ^ 6 + (-47 / 3456) * t ^ 10 + (-1289 / 2880) * alpha * t ^ 4 + (1259 / 2880) * alpha * t ^ 6) * d_sq
theorem v57_14 (t : ℂ) : (momentPoly 57 z57 1 4).eval t = ((1018869 / 160) * t ^ 3 + (-401073547 / 64000) * t ^ 5 + (40479397 / 32000) * t ^ 7 + (-121305937 / 128000) * t ^ 9 + (6709043 / 96000) * t ^ 11 + (147307 / 384000) * t ^ 17 + (-116587 / 160) * d * t ^ 3 + (228312473 / 192000) * d * t ^ 5 + (-18673841 / 32000) * d * t ^ 7 + (10571481 / 128000) * d * t ^ 9 + (1754101 / 96000) * d * t ^ 11 + (208099 / 384000) * d * t ^ 17 + (5921591 / 800) * alpha * t ^ 3 + (-2158348799 / 192000) * alpha * t ^ 5 + (114044323 / 32000) * alpha * t ^ 7 + (-20714783 / 128000) * alpha * t ^ 9 + (15255279 / 32000) * alpha * t ^ 11 + (4350043 / 384000) * alpha * t ^ 17 + (-141969 / 160) * alpha * d * t ^ 3 + (310487299 / 192000) * alpha * d * t ^ 5 + (-66769129 / 96000) * alpha * d * t ^ 7 + (-14273111 / 384000) * alpha * d * t ^ 9 + (634309 / 288000) * alpha * d * t ^ 11 + (-1388599 / 1152000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_03, v56_04, v56_10, v56_11, v56_12, v56_13, v56_14]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14]
  try simp only [star_one, star_neg]
  linear_combination ((-47323 / 160) * t ^ 3 + (311638031 / 576000) * t ^ 5 + (-8189459 / 32000) * t ^ 7 + (4666937 / 384000) * t ^ 9 + (-966383 / 288000) * t ^ 11 + (470783 / 1152000) * t ^ 17 + (185 / 96) * d * t ^ 3 + (-121423 / 69120) * d * t ^ 5 + (-469 / 1440) * d * t ^ 7 + (5717 / 27648) * d * t ^ 9 + (-235 / 20736) * d * t ^ 11 + (95 / 41472) * d * t ^ 17 + (1289 / 34560) * d ^ 2 * t ^ 7 + (-1249 / 34560) * d ^ 2 * t ^ 9) * alpha_sq + ((-37 / 4) * t ^ 3 + (22249 / 3840) * t ^ 5 + (1993 / 2304) * t ^ 7 + (311 / 1440) * t ^ 9 + (-47 / 432) * t ^ 11 + (-185 / 96) * alpha * t ^ 3 + (-2481 / 12800) * alpha * t ^ 5 + (17513 / 9600) * alpha * t ^ 7 + (-5951 / 138240) * alpha * t ^ 9 + (67301 / 518400) * alpha * t ^ 11 + (95 / 41472) * alpha * t ^ 17) * d_sq
theorem v57_20 (t : ℂ) : (momentPoly 57 z57 2 0).eval t = ((141 / 10) * t ^ 2 + (-671 / 160) * t ^ 4 + (-1 / 4) * d * t ^ 2 + (-423 / 40) * alpha * t ^ 2 + (413 / 40) * alpha * t ^ 4 + (1 / 24) * alpha * d * t ^ 2 + (-1 / 96) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_10, v56_20]
  try simp only [phase57_00, phase57_10, phase57_20]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 72) * t ^ 2) * alpha_sq + ((-1 / 72) * t ^ 2) * d_sq
theorem v57_21 (t : ℂ) : (momentPoly 57 z57 2 1).eval t = (113 * t + (-24329 / 320) * t ^ 3 + (-2901 / 320) * t ^ 5 + (-113 / 8) * d * t + (3831 / 320) * d * t ^ 3 + (209 / 320) * d * t ^ 5 + (-113 / 8) * alpha * t + (141 / 64) * alpha * t ^ 3 + (683 / 64) * alpha * t ^ 5 + (1279 / 960) * alpha * d * t ^ 3 + (-1249 / 960) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_10, v56_11, v56_20, v56_21]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21]
  try simp only [star_one, star_neg]
  linear_combination ((1279 / 2880) * t ^ 3 + (-413 / 960) * t ^ 5 + (-5 / 1728) * d * t ^ 3 + (1 / 864) * d * t ^ 5) * alpha_sq + ((-1 / 24) * t ^ 3 + (5 / 1728) * alpha * t ^ 3 + (-1 / 864) * alpha * t ^ 5) * d_sq
theorem v57_22 (t : ℂ) : (momentPoly 57 z57 2 2).eval t = (6441 + (-10528) * t ^ 2 + (3623279 / 800) * t ^ 4 + (-1878007 / 3200) * t ^ 6 + (897891 / 3200) * t ^ 8 + (-56) * d * t ^ 2 + (7249 / 160) * d * t ^ 4 + (4057 / 640) * d * t ^ 6 + (-413 / 640) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_10, v56_11, v56_12, v56_20, v56_21, v56_22]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22]
  try simp only [star_one, star_neg]
  linear_combination ((28 / 9) * t ^ 2 + (-377 / 480) * t ^ 4 + (-2629 / 1440) * t ^ 6 + (-1289 / 4320) * d * t ^ 4 + (1255 / 3456) * d * t ^ 6 + (-413 / 5760) * d * t ^ 8 + (-5 / 10368) * d ^ 2 * t ^ 6 + (1 / 10368) * d ^ 2 * t ^ 8) * alpha_sq + ((-28 / 9) * t ^ 2 + (3431 / 1440) * t ^ 4 + (3013 / 17280) * t ^ 6 + (-1 / 3456) * t ^ 8) * d_sq
theorem v57_23 (t : ℂ) : (momentPoly 57 z57 2 3).eval t = (18985 * t + (-8101557 / 320) * t ^ 3 + (170714447 / 32000) * t ^ 5 + (220269 / 320) * t ^ 7 + (24653133 / 32000) * t ^ 9 + (-5932541 / 128000) * t ^ 11 + (10121421 / 128000) * t ^ 13 + (-18985 / 8) * d * t + (1275723 / 320) * d * t ^ 3 + (-5892521 / 3840) * d * t ^ 5 + (229739 / 19200) * d * t ^ 7 + (-283621 / 2560) * d * t ^ 9 + (-208043 / 76800) * d * t ^ 11 + (42817 / 76800) * d * t ^ 13 + (18985 / 8) * alpha * t + (-46953 / 64) * alpha * t ^ 3 + (-432987739 / 96000) * alpha * t ^ 5 + (53596147 / 19200) * alpha * t ^ 7 + (6585391 / 64000) * alpha * t ^ 9 + (-6922913 / 384000) * alpha * t ^ 11 + (4395583 / 384000) * alpha * t ^ 13 + (-141969 / 320) * alpha * d * t ^ 3 + (16103527 / 19200) * alpha * d * t ^ 5 + (-629469 / 1600) * alpha * d * t ^ 7 + (-453 / 1280) * alpha * d * t ^ 9 + (-50801 / 76800) * alpha * d * t ^ 11 + (-19411 / 15360) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_03, v56_10, v56_11, v56_12, v56_13, v56_20, v56_21, v56_22, v56_23]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23]
  try simp only [star_one, star_neg]
  linear_combination ((47323 / 320) * t ^ 3 + (-1746119 / 7200) * t ^ 5 + (2746799 / 28800) * t ^ 7 + (1367453 / 691200) * t ^ 11 + (-59059 / 46080) * t ^ 13 + (-185 / 192) * d * t ^ 3 + (16879 / 43200) * d * t ^ 5 + (252289 / 345600) * d * t ^ 7 + (-151261 / 691200) * d * t ^ 9 + (55301 / 2073600) * d * t ^ 11 + (-221 / 32400) * d * t ^ 13 + (-1289 / 34560) * d ^ 2 * t ^ 7 + (1249 / 34560) * d ^ 2 * t ^ 9) * alpha_sq + ((-111 / 8) * t ^ 3 + (37291 / 3840) * t ^ 5 + (1471 / 768) * t ^ 7 + (-311 / 1440) * t ^ 9 + (-47 / 1728) * t ^ 11 + (-185 / 192) * alpha * t ^ 3 + (16879 / 43200) * alpha * t ^ 5 + (161297 / 345600) * alpha * t ^ 7 + (-5 / 27648) * alpha * t ^ 9 + (79051 / 2073600) * alpha * t ^ 11 + (-47 / 41472) * alpha * t ^ 13) * d_sq
theorem v57_24 (t : ℂ) : (momentPoly 57 z57 2 4).eval t = (525930 * t ^ 2 + (-169662251 / 160) * t ^ 4 + (49199372041 / 80000) * t ^ 6 + (-112747440663 / 1280000) * t ^ 8 + (2049301819 / 128000) * t ^ 10 + (-58249910219 / 7680000) * t ^ 12 + (789201073 / 640000) * t ^ 14 + (1837431239 / 7680000) * t ^ 18 + (-365341999 / 1280000) * t ^ 20 + (-9325) * d * t ^ 2 + (43406 / 3) * d * t ^ 4 + (-58952343 / 16000) * d * t ^ 6 + (-1025785139 / 768000) * d * t ^ 8 + (-95177149 / 384000) * d * t ^ 10 + (114146507 / 1536000) * d * t ^ 12 + (-4299929 / 128000) * d * t ^ 14 + (152507 / 307200) * d * t ^ 18 + (-127523 / 384000) * d * t ^ 20 + (788895 / 2) * alpha * t ^ 2 + (-122208917 / 120) * alpha * t ^ 4 + (34634529317 / 40000) * alpha * t ^ 6 + (-970234036151 / 3840000) * alpha * t ^ 8 + (1599270419 / 76800) * alpha * t ^ 10 + (-82206064361 / 7680000) * alpha * t ^ 12 + (1297366921 / 1920000) * alpha * t ^ 14 + (1188076781 / 7680000) * alpha * t ^ 18 + (-82971761 / 1280000) * alpha * t ^ 20 + (-9325 / 6) * alpha * d * t ^ 2 + (3001 / 480) * alpha * d * t ^ 4 + (61705413 / 16000) * alpha * d * t ^ 6 + (-107629411 / 51200) * alpha * d * t ^ 8 + (-37305667 / 384000) * alpha * d * t ^ 10 + (-462192257 / 4608000) * alpha * d * t ^ 12 + (-4439597 / 384000) * alpha * d * t ^ 14 + (-13614853 / 4608000) * alpha * d * t ^ 18 + (-24023 / 384000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_03, v56_04, v56_10, v56_11, v56_12, v56_13, v56_14, v56_20, v56_21, v56_22, v56_23, v56_24]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24]
  try simp only [star_one, star_neg]
  linear_combination ((-9325 / 18) * t ^ 2 + (728717 / 720) * t ^ 4 + (-568211519 / 1728000) * t ^ 6 + (-100396141 / 576000) * t ^ 8 + (-9551977 / 691200) * t ^ 10 + (31116631 / 864000) * t ^ 12 + (-558269 / 72000) * t ^ 14 + (2981557 / 3456000) * t ^ 18 + (-5603647 / 576000) * d * t ^ 6 + (128639299 / 6912000) * d * t ^ 8 + (-1983659 / 192000) * d * t ^ 10 + (7000699 / 13824000) * d * t ^ 12 + (10075271 / 10368000) * d * t ^ 14 + (-2516771 / 41472000) * d * t ^ 18 + (-127523 / 3456000) * d * t ^ 20 + (-337051 / 4147200) * d ^ 2 * t ^ 8 + (16303 / 230400) * d ^ 2 * t ^ 10 + (-2963 / 1658880) * d ^ 2 * t ^ 12 + (30713 / 6220800) * d ^ 2 * t ^ 14 + (-475 / 995328) * d ^ 2 * t ^ 18 + (95 / 497664) * d ^ 2 * t ^ 20) * alpha_sq + ((-9325 / 18) * t ^ 2 + (97361 / 144) * t ^ 4 + (-173326897 / 1728000) * t ^ 6 + (-421453789 / 6912000) * t ^ 8 + (-34916771 / 1728000) * t ^ 10 + (40993291 / 13824000) * t ^ 12 + (634879 / 2073600) * t ^ 14 + (3120563 / 41472000) * t ^ 18 + (-95 / 165888) * t ^ 20 + (-14179 / 72) * alpha * t ^ 4 + (67592671 / 192000) * alpha * t ^ 6 + (-518832161 / 3456000) * alpha * t ^ 8 + (-18361661 / 3456000) * alpha * t ^ 10 + (4130131 / 10368000) * alpha * t ^ 12 + (-58703 / 103680) * alpha * t ^ 14 + (-1364849 / 10368000) * alpha * t ^ 18) * d_sq
theorem v57_30 (t : ℂ) : (momentPoly 57 z57 3 0).eval t = ((9179 / 320) * t ^ 3 + (-309 / 320) * t ^ 5 + (-3151 / 960) * d * t ^ 3 + (617 / 320) * d * t ^ 5 + (-47 / 384) * d * t ^ 9 + (-160043 / 4800) * alpha * t ^ 3 + (43249 / 1600) * alpha * t ^ 5 + (24817 / 9600) * alpha * t ^ 9 + (1279 / 320) * alpha * d * t ^ 3 + (-1249 / 320) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_10, v56_20, v56_30]
  try simp only [phase57_00, phase57_10, phase57_20, phase57_30]
  try simp only [star_one, star_neg]
  linear_combination ((-1279 / 960) * t ^ 3 + (413 / 320) * t ^ 5 + (5 / 576) * d * t ^ 3 + (-1 / 288) * d * t ^ 5) * alpha_sq + ((-1 / 24) * t ^ 3 + (5 / 576) * alpha * t ^ 3 + (-1 / 288) * alpha * t ^ 5) * d_sq
theorem v57_31 (t : ℂ) : (momentPoly 57 z57 3 1).eval t = ((11844 / 5) * t ^ 2 + (-4414339 / 1600) * t ^ 4 + (1641747 / 3200) * t ^ 6 + (38371 / 3200) * t ^ 10 + (-42) * d * t ^ 2 + (1973 / 60) * d * t ^ 4 + (341 / 80) * d * t ^ 6 + (-47 / 384) * d * t ^ 10 + (-8883 / 5) * alpha * t ^ 2 + (7617041 / 2400) * alpha * t ^ 4 + (-1117123 / 800) * alpha * t ^ 6 + (-74303 / 9600) * alpha * t ^ 10 + 7 * alpha * d * t ^ 2 + (-4229 / 4800) * alpha * d * t ^ 4 + (-17331 / 3200) * alpha * d * t ^ 6 + (-3149 / 9600) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_10, v56_11, v56_20, v56_21, v56_30, v56_31]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21, phase57_30, phase57_31]
  try simp only [star_one, star_neg]
  linear_combination ((-7 / 3) * t ^ 2 + (66247 / 28800) * t ^ 4 + (6479 / 57600) * t ^ 6 + (-221 / 2700) * t ^ 10) * alpha_sq + ((-7 / 3) * t ^ 2 + (8851 / 5760) * t ^ 4 + (2963 / 11520) * t ^ 6 + (-47 / 3456) * t ^ 10 + (1289 / 2880) * alpha * t ^ 4 + (-1259 / 2880) * alpha * t ^ 6) * d_sq
theorem v57_32 (t : ℂ) : (momentPoly 57 z57 3 2).eval t = (18985 * t + (-8101557 / 320) * t ^ 3 + (170714447 / 32000) * t ^ 5 + (220269 / 320) * t ^ 7 + (24653133 / 32000) * t ^ 9 + (-5932541 / 128000) * t ^ 11 + (10121421 / 128000) * t ^ 13 + (-18985 / 8) * d * t + (1275723 / 320) * d * t ^ 3 + (-5892521 / 3840) * d * t ^ 5 + (229739 / 19200) * d * t ^ 7 + (-283621 / 2560) * d * t ^ 9 + (-208043 / 76800) * d * t ^ 11 + (42817 / 76800) * d * t ^ 13 + (-18985 / 8) * alpha * t + (46953 / 64) * alpha * t ^ 3 + (432987739 / 96000) * alpha * t ^ 5 + (-53596147 / 19200) * alpha * t ^ 7 + (-6585391 / 64000) * alpha * t ^ 9 + (6922913 / 384000) * alpha * t ^ 11 + (-4395583 / 384000) * alpha * t ^ 13 + (141969 / 320) * alpha * d * t ^ 3 + (-16103527 / 19200) * alpha * d * t ^ 5 + (629469 / 1600) * alpha * d * t ^ 7 + (453 / 1280) * alpha * d * t ^ 9 + (50801 / 76800) * alpha * d * t ^ 11 + (19411 / 15360) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_10, v56_11, v56_12, v56_20, v56_21, v56_22, v56_30, v56_31, v56_32]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22, phase57_30, phase57_31, phase57_32]
  try simp only [star_one, star_neg]
  linear_combination ((47323 / 320) * t ^ 3 + (-1746119 / 7200) * t ^ 5 + (2746799 / 28800) * t ^ 7 + (1367453 / 691200) * t ^ 11 + (-59059 / 46080) * t ^ 13 + (-185 / 192) * d * t ^ 3 + (16879 / 43200) * d * t ^ 5 + (252289 / 345600) * d * t ^ 7 + (-151261 / 691200) * d * t ^ 9 + (55301 / 2073600) * d * t ^ 11 + (-221 / 32400) * d * t ^ 13 + (-1289 / 34560) * d ^ 2 * t ^ 7 + (1249 / 34560) * d ^ 2 * t ^ 9) * alpha_sq + ((-111 / 8) * t ^ 3 + (37291 / 3840) * t ^ 5 + (1471 / 768) * t ^ 7 + (-311 / 1440) * t ^ 9 + (-47 / 1728) * t ^ 11 + (185 / 192) * alpha * t ^ 3 + (-16879 / 43200) * alpha * t ^ 5 + (-161297 / 345600) * alpha * t ^ 7 + (5 / 27648) * alpha * t ^ 9 + (-79051 / 2073600) * alpha * t ^ 11 + (47 / 41472) * alpha * t ^ 13) * d_sq
theorem v57_33 (t : ℂ) : (momentPoly 57 z57 3 3).eval t = (1082145 + (-2629650) * t ^ 2 + (358704621 / 160) * t ^ 4 + (-152894848387 / 160000) * t ^ 6 + (118715240217 / 320000) * t ^ 8 + (-34604669709 / 320000) * t ^ 10 + (545236631 / 320000) * t ^ 12 + (-801749373 / 640000) * t ^ 14 + (-18155357 / 640000) * t ^ 18 + (-27975 / 2) * d * t ^ 2 + (717651 / 32) * d * t ^ 4 + (-583403417 / 96000) * d * t ^ 6 + (-5577171 / 2560) * d * t ^ 8 + (-15895617 / 64000) * d * t ^ 10 + (1725847 / 48000) * d * t ^ 12 + (-1757813 / 32000) * d * t ^ 14) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_03, v56_10, v56_11, v56_12, v56_13, v56_20, v56_21, v56_22, v56_23, v56_30, v56_31, v56_32, v56_33]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23, phase57_30, phase57_31, phase57_32, phase57_33]
  try simp only [star_one, star_neg]
  linear_combination ((9325 / 12) * t ^ 2 + (-12441 / 32) * t ^ 4 + (-188873677 / 192000) * t ^ 6 + (14958581 / 25600) * t ^ 8 + (13123759 / 384000) * t ^ 10 + (1741207 / 3456000) * t ^ 12 + (-27760879 / 6912000) * t ^ 14 + (-2533817 / 4147200) * t ^ 18 + (-14179 / 96) * d * t ^ 4 + (3930081 / 12800) * d * t ^ 6 + (-4677671 / 25600) * d * t ^ 8 + (5460223 / 230400) * d * t ^ 10 + (-539419 / 345600) * d * t ^ 12 + (89389 / 86400) * d * t ^ 14 + (-415 / 1728) * d ^ 2 * t ^ 6 + (8479 / 172800) * d ^ 2 * t ^ 8 + (18331 / 115200) * d ^ 2 * t ^ 10 + (3049 / 345600) * d ^ 2 * t ^ 14) * alpha_sq + ((-9325 / 12) * t ^ 2 + (37741 / 32) * t ^ 4 + (-44856067 / 115200) * t ^ 6 + (1664801 / 230400) * t ^ 8 + (-2992147 / 76800) * t ^ 10 + (-245941 / 138240) * t ^ 12 + (623129 / 1382400) * t ^ 14 + (-2209 / 165888) * t ^ 18) * d_sq
theorem v57_34 (t : ℂ) : (momentPoly 57 z57 3 4).eval t = (4215345 * t + (-668487933 / 80) * t ^ 3 + (71468572119 / 16000) * t ^ 5 + (-74565507183 / 100000) * t ^ 7 + (5100152134857 / 6400000) * t ^ 9 + (-2496965939547 / 6400000) * t ^ 11 + (312171628563 / 5120000) * t ^ 13 + (-485905312867 / 12800000) * t ^ 15 + (-95643605029 / 51200000) * t ^ 17 + (7319534597 / 9600000) * t ^ 19 + (-5528739833 / 6400000) * t ^ 21 + (-11837021711 / 153600000) * t ^ 25 + (-4215345 / 8) * d * t + (105264387 / 80) * d * t ^ 3 + (-687369851 / 640) * d * t ^ 5 + (686262295823 / 1920000) * d * t ^ 7 + (-520786391893 / 3840000) * d * t ^ 9 + (57834449641 / 960000) * d * t ^ 11 + (140844975577 / 46080000) * d * t ^ 13 + (-3440694143 / 7680000) * d * t ^ 15 + (666177431 / 6144000) * d * t ^ 17 + (-1984235371 / 23040000) * d * t ^ 19 + (1584992243 / 15360000) * d * t ^ 21 + (6789103 / 18432000) * d * t ^ 25 + (4215345 / 8) * alpha * t + (-3874257 / 16) * alpha * t ^ 3 + (-28778739301 / 16000) * alpha * t ^ 5 + (21188739489217 / 9600000) * alpha * t ^ 7 + (-12832684578959 / 19200000) * alpha * t ^ 9 + (-84216460129 / 4800000) * alpha * t ^ 11 + (-170153339387 / 46080000) * alpha * t ^ 13 + (-56292756871 / 38400000) * alpha * t ^ 15 + (-342993283177 / 153600000) * alpha * t ^ 17 + (44567029909 / 115200000) * alpha * t ^ 19 + (-5995593311 / 76800000) * alpha * t ^ 21 + (-4648180133 / 460800000) * alpha * t ^ 25 + (-11714361 / 80) * alpha * d * t ^ 3 + (1306231473 / 3200) * alpha * d * t ^ 5 + (-362791608523 / 960000) * alpha * d * t ^ 7 + (152939048187 / 1280000) * alpha * d * t ^ 9 + (-1648991507 / 256000) * alpha * d * t ^ 11 + (37842560377 / 15360000) * alpha * d * t ^ 13 + (5046767531 / 7680000) * alpha * d * t ^ 15 + (-190458251 / 6144000) * alpha * d * t ^ 17 + (-379322759 / 11520000) * alpha * d * t ^ 19 + (121488253 / 3840000) * alpha * d * t ^ 21 + (-22126801 / 18432000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_03, v56_04, v56_10, v56_11, v56_12, v56_13, v56_14, v56_20, v56_21, v56_22, v56_23, v56_24, v56_30, v56_31, v56_32, v56_33, v56_34]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24, phase57_30, phase57_31, phase57_32, phase57_33, phase57_34]
  try simp only [star_one, star_neg]
  linear_combination ((3904787 / 80) * t ^ 3 + (-538579049 / 4800) * t ^ 5 + (118813160749 / 1440000) * t ^ 7 + (-40320535541 / 1920000) * t ^ 9 + (9415460341 / 2304000) * t ^ 11 + (-370738469531 / 138240000) * t ^ 13 + (34979755847 / 69120000) * t ^ 15 + (667371991 / 18432000) * t ^ 17 + (5774781059 / 207360000) * t ^ 19 + (-19787 / 1875) * t ^ 21 + (67321969 / 55296000) * t ^ 25 + (-15265 / 48) * d * t ^ 3 + (52277 / 400) * d * t ^ 5 + (2315115991 / 3456000) * d * t ^ 7 + (-7230062467 / 13824000) * d * t ^ 9 + (618639191 / 13824000) * d * t ^ 11 + (-44673451 / 3456000) * d * t ^ 13 + (948991 / 128000) * d * t ^ 15 + (37404647 / 165888000) * d * t ^ 17 + (6009089 / 31104000) * d * t ^ 19 + (-18514039 / 165888000) * d * t ^ 21 + (-4199 / 311040) * d * t ^ 25 + (-424081 / 17280) * d ^ 2 * t ^ 7 + (201559613 / 4608000) * d ^ 2 * t ^ 9 + (-257453593 / 13824000) * d ^ 2 * t ^ 11 + (-17604211 / 27648000) * d ^ 2 * t ^ 13 + (411103 / 41472000) * d ^ 2 * t ^ 15 + (-19411 / 552960) * d ^ 2 * t ^ 17 + (-24491 / 663552) * d ^ 2 * t ^ 19 + (98611 / 5184000) * d ^ 2 * t ^ 21) * alpha_sq + ((-9159 / 2) * t ^ 3 + (4064719 / 640) * t ^ 5 + (-1132358837 / 1152000) * t ^ 7 + (-3786721871 / 4608000) * t ^ 9 + (-74892299 / 921600) * t ^ 11 + (642804551 / 27648000) * t ^ 13 + (-218047973 / 13824000) * t ^ 15 + (19411 / 92160) * t ^ 17 + (10775893 / 82944000) * t ^ 19 + (-777013 / 6912000) * t ^ 21 + (-15265 / 48) * alpha * t ^ 3 + (52277 / 400) * alpha * t ^ 5 + (1716388631 / 3456000) * alpha * t ^ 7 + (-3675957821 / 13824000) * alpha * t ^ 9 + (-444241607 / 13824000) * alpha * t ^ 11 + (-458885377 / 41472000) * alpha * t ^ 13 + (-3053647 / 1382400) * alpha * t ^ 15 + (-1325309 / 33177600) * alpha * t ^ 17 + (-3465049 / 7776000) * alpha * t ^ 19 + (-3975937 / 165888000) * alpha * t ^ 21 + (4465 / 1990656) * alpha * t ^ 25) * d_sq
theorem v57_40 (t : ℂ) : (momentPoly 57 z57 4 0).eval t = ((-478067 / 1000) * t ^ 4 + (23338949 / 16000) * t ^ 6 + (-14357831 / 16000) * t ^ 8 + (625459 / 12000) * t ^ 10 + (-632521 / 192000) * t ^ 16 + (-421 / 96) * d * t ^ 4 + (-1259 / 640) * d * t ^ 6 + (1239 / 640) * d * t ^ 8 + (-47 / 96) * d * t ^ 10 + (-19754791 / 24000) * alpha * t ^ 4 + (15997193 / 16000) * alpha * t ^ 6 + (-1843031 / 8000) * alpha * t ^ 8 + (148717 / 3000) * alpha * t ^ 10 + (-470783 / 48000) * alpha * t ^ 16 + (74689 / 4800) * alpha * d * t ^ 4 + (-134117 / 9600) * alpha * d * t ^ 6 + (311 / 960) * alpha * d * t ^ 8 + (-517 / 450) * alpha * d * t ^ 10 + (-95 / 4608) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_10, v56_20, v56_30, v56_40]
  try simp only [phase57_00, phase57_10, phase57_20, phase57_30, phase57_40]
  try simp only [star_one, star_neg]
  linear_combination ((-24641 / 3600) * t ^ 4 + (72391 / 14400) * t ^ 6 + (221 / 675) * t ^ 10 + (1289 / 1440) * d * t ^ 4 + (-1255 / 1152) * d * t ^ 6 + (413 / 1920) * d * t ^ 8 + (5 / 3456) * d ^ 2 * t ^ 6 + (-1 / 3456) * d ^ 2 * t ^ 8) * alpha_sq + ((-721 / 720) * t ^ 4 + (971 / 1920) * t ^ 6 + (1 / 1152) * t ^ 8 + (-47 / 864) * t ^ 10 + (1289 / 1440) * alpha * t ^ 4 + (-1259 / 1440) * alpha * t ^ 6) * d_sq
theorem v57_41 (t : ℂ) : (momentPoly 57 z57 4 1).eval t = ((1018869 / 160) * t ^ 3 + (-401073547 / 64000) * t ^ 5 + (40479397 / 32000) * t ^ 7 + (-121305937 / 128000) * t ^ 9 + (6709043 / 96000) * t ^ 11 + (147307 / 384000) * t ^ 17 + (-116587 / 160) * d * t ^ 3 + (228312473 / 192000) * d * t ^ 5 + (-18673841 / 32000) * d * t ^ 7 + (10571481 / 128000) * d * t ^ 9 + (1754101 / 96000) * d * t ^ 11 + (208099 / 384000) * d * t ^ 17 + (-5921591 / 800) * alpha * t ^ 3 + (2158348799 / 192000) * alpha * t ^ 5 + (-114044323 / 32000) * alpha * t ^ 7 + (20714783 / 128000) * alpha * t ^ 9 + (-15255279 / 32000) * alpha * t ^ 11 + (-4350043 / 384000) * alpha * t ^ 17 + (141969 / 160) * alpha * d * t ^ 3 + (-310487299 / 192000) * alpha * d * t ^ 5 + (66769129 / 96000) * alpha * d * t ^ 7 + (14273111 / 384000) * alpha * d * t ^ 9 + (-634309 / 288000) * alpha * d * t ^ 11 + (1388599 / 1152000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_10, v56_11, v56_20, v56_21, v56_30, v56_31, v56_40, v56_41]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21, phase57_30, phase57_31, phase57_40, phase57_41]
  try simp only [star_one, star_neg]
  linear_combination ((-47323 / 160) * t ^ 3 + (311638031 / 576000) * t ^ 5 + (-8189459 / 32000) * t ^ 7 + (4666937 / 384000) * t ^ 9 + (-966383 / 288000) * t ^ 11 + (470783 / 1152000) * t ^ 17 + (185 / 96) * d * t ^ 3 + (-121423 / 69120) * d * t ^ 5 + (-469 / 1440) * d * t ^ 7 + (5717 / 27648) * d * t ^ 9 + (-235 / 20736) * d * t ^ 11 + (95 / 41472) * d * t ^ 17 + (1289 / 34560) * d ^ 2 * t ^ 7 + (-1249 / 34560) * d ^ 2 * t ^ 9) * alpha_sq + ((-37 / 4) * t ^ 3 + (22249 / 3840) * t ^ 5 + (1993 / 2304) * t ^ 7 + (311 / 1440) * t ^ 9 + (-47 / 432) * t ^ 11 + (185 / 96) * alpha * t ^ 3 + (2481 / 12800) * alpha * t ^ 5 + (-17513 / 9600) * alpha * t ^ 7 + (5951 / 138240) * alpha * t ^ 9 + (-67301 / 518400) * alpha * t ^ 11 + (-95 / 41472) * alpha * t ^ 17) * d_sq
theorem v57_42 (t : ℂ) : (momentPoly 57 z57 4 2).eval t = (525930 * t ^ 2 + (-169662251 / 160) * t ^ 4 + (49199372041 / 80000) * t ^ 6 + (-112747440663 / 1280000) * t ^ 8 + (2049301819 / 128000) * t ^ 10 + (-58249910219 / 7680000) * t ^ 12 + (789201073 / 640000) * t ^ 14 + (1837431239 / 7680000) * t ^ 18 + (-365341999 / 1280000) * t ^ 20 + (-9325) * d * t ^ 2 + (43406 / 3) * d * t ^ 4 + (-58952343 / 16000) * d * t ^ 6 + (-1025785139 / 768000) * d * t ^ 8 + (-95177149 / 384000) * d * t ^ 10 + (114146507 / 1536000) * d * t ^ 12 + (-4299929 / 128000) * d * t ^ 14 + (152507 / 307200) * d * t ^ 18 + (-127523 / 384000) * d * t ^ 20 + (-788895 / 2) * alpha * t ^ 2 + (122208917 / 120) * alpha * t ^ 4 + (-34634529317 / 40000) * alpha * t ^ 6 + (970234036151 / 3840000) * alpha * t ^ 8 + (-1599270419 / 76800) * alpha * t ^ 10 + (82206064361 / 7680000) * alpha * t ^ 12 + (-1297366921 / 1920000) * alpha * t ^ 14 + (-1188076781 / 7680000) * alpha * t ^ 18 + (82971761 / 1280000) * alpha * t ^ 20 + (9325 / 6) * alpha * d * t ^ 2 + (-3001 / 480) * alpha * d * t ^ 4 + (-61705413 / 16000) * alpha * d * t ^ 6 + (107629411 / 51200) * alpha * d * t ^ 8 + (37305667 / 384000) * alpha * d * t ^ 10 + (462192257 / 4608000) * alpha * d * t ^ 12 + (4439597 / 384000) * alpha * d * t ^ 14 + (13614853 / 4608000) * alpha * d * t ^ 18 + (24023 / 384000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_10, v56_11, v56_12, v56_20, v56_21, v56_22, v56_30, v56_31, v56_32, v56_40, v56_41, v56_42]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22, phase57_30, phase57_31, phase57_32, phase57_40, phase57_41, phase57_42]
  try simp only [star_one, star_neg]
  linear_combination ((-9325 / 18) * t ^ 2 + (728717 / 720) * t ^ 4 + (-568211519 / 1728000) * t ^ 6 + (-100396141 / 576000) * t ^ 8 + (-9551977 / 691200) * t ^ 10 + (31116631 / 864000) * t ^ 12 + (-558269 / 72000) * t ^ 14 + (2981557 / 3456000) * t ^ 18 + (-5603647 / 576000) * d * t ^ 6 + (128639299 / 6912000) * d * t ^ 8 + (-1983659 / 192000) * d * t ^ 10 + (7000699 / 13824000) * d * t ^ 12 + (10075271 / 10368000) * d * t ^ 14 + (-2516771 / 41472000) * d * t ^ 18 + (-127523 / 3456000) * d * t ^ 20 + (-337051 / 4147200) * d ^ 2 * t ^ 8 + (16303 / 230400) * d ^ 2 * t ^ 10 + (-2963 / 1658880) * d ^ 2 * t ^ 12 + (30713 / 6220800) * d ^ 2 * t ^ 14 + (-475 / 995328) * d ^ 2 * t ^ 18 + (95 / 497664) * d ^ 2 * t ^ 20) * alpha_sq + ((-9325 / 18) * t ^ 2 + (97361 / 144) * t ^ 4 + (-173326897 / 1728000) * t ^ 6 + (-421453789 / 6912000) * t ^ 8 + (-34916771 / 1728000) * t ^ 10 + (40993291 / 13824000) * t ^ 12 + (634879 / 2073600) * t ^ 14 + (3120563 / 41472000) * t ^ 18 + (-95 / 165888) * t ^ 20 + (14179 / 72) * alpha * t ^ 4 + (-67592671 / 192000) * alpha * t ^ 6 + (518832161 / 3456000) * alpha * t ^ 8 + (18361661 / 3456000) * alpha * t ^ 10 + (-4130131 / 10368000) * alpha * t ^ 12 + (58703 / 103680) * alpha * t ^ 14 + (1364849 / 10368000) * alpha * t ^ 18) * d_sq
theorem v57_43 (t : ℂ) : (momentPoly 57 z57 4 3).eval t = (4215345 * t + (-668487933 / 80) * t ^ 3 + (71468572119 / 16000) * t ^ 5 + (-74565507183 / 100000) * t ^ 7 + (5100152134857 / 6400000) * t ^ 9 + (-2496965939547 / 6400000) * t ^ 11 + (312171628563 / 5120000) * t ^ 13 + (-485905312867 / 12800000) * t ^ 15 + (-95643605029 / 51200000) * t ^ 17 + (7319534597 / 9600000) * t ^ 19 + (-5528739833 / 6400000) * t ^ 21 + (-11837021711 / 153600000) * t ^ 25 + (-4215345 / 8) * d * t + (105264387 / 80) * d * t ^ 3 + (-687369851 / 640) * d * t ^ 5 + (686262295823 / 1920000) * d * t ^ 7 + (-520786391893 / 3840000) * d * t ^ 9 + (57834449641 / 960000) * d * t ^ 11 + (140844975577 / 46080000) * d * t ^ 13 + (-3440694143 / 7680000) * d * t ^ 15 + (666177431 / 6144000) * d * t ^ 17 + (-1984235371 / 23040000) * d * t ^ 19 + (1584992243 / 15360000) * d * t ^ 21 + (6789103 / 18432000) * d * t ^ 25 + (-4215345 / 8) * alpha * t + (3874257 / 16) * alpha * t ^ 3 + (28778739301 / 16000) * alpha * t ^ 5 + (-21188739489217 / 9600000) * alpha * t ^ 7 + (12832684578959 / 19200000) * alpha * t ^ 9 + (84216460129 / 4800000) * alpha * t ^ 11 + (170153339387 / 46080000) * alpha * t ^ 13 + (56292756871 / 38400000) * alpha * t ^ 15 + (342993283177 / 153600000) * alpha * t ^ 17 + (-44567029909 / 115200000) * alpha * t ^ 19 + (5995593311 / 76800000) * alpha * t ^ 21 + (4648180133 / 460800000) * alpha * t ^ 25 + (11714361 / 80) * alpha * d * t ^ 3 + (-1306231473 / 3200) * alpha * d * t ^ 5 + (362791608523 / 960000) * alpha * d * t ^ 7 + (-152939048187 / 1280000) * alpha * d * t ^ 9 + (1648991507 / 256000) * alpha * d * t ^ 11 + (-37842560377 / 15360000) * alpha * d * t ^ 13 + (-5046767531 / 7680000) * alpha * d * t ^ 15 + (190458251 / 6144000) * alpha * d * t ^ 17 + (379322759 / 11520000) * alpha * d * t ^ 19 + (-121488253 / 3840000) * alpha * d * t ^ 21 + (22126801 / 18432000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_03, v56_10, v56_11, v56_12, v56_13, v56_20, v56_21, v56_22, v56_23, v56_30, v56_31, v56_32, v56_33, v56_40, v56_41, v56_42, v56_43]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23, phase57_30, phase57_31, phase57_32, phase57_33, phase57_40, phase57_41, phase57_42, phase57_43]
  try simp only [star_one, star_neg]
  linear_combination ((3904787 / 80) * t ^ 3 + (-538579049 / 4800) * t ^ 5 + (118813160749 / 1440000) * t ^ 7 + (-40320535541 / 1920000) * t ^ 9 + (9415460341 / 2304000) * t ^ 11 + (-370738469531 / 138240000) * t ^ 13 + (34979755847 / 69120000) * t ^ 15 + (667371991 / 18432000) * t ^ 17 + (5774781059 / 207360000) * t ^ 19 + (-19787 / 1875) * t ^ 21 + (67321969 / 55296000) * t ^ 25 + (-15265 / 48) * d * t ^ 3 + (52277 / 400) * d * t ^ 5 + (2315115991 / 3456000) * d * t ^ 7 + (-7230062467 / 13824000) * d * t ^ 9 + (618639191 / 13824000) * d * t ^ 11 + (-44673451 / 3456000) * d * t ^ 13 + (948991 / 128000) * d * t ^ 15 + (37404647 / 165888000) * d * t ^ 17 + (6009089 / 31104000) * d * t ^ 19 + (-18514039 / 165888000) * d * t ^ 21 + (-4199 / 311040) * d * t ^ 25 + (-424081 / 17280) * d ^ 2 * t ^ 7 + (201559613 / 4608000) * d ^ 2 * t ^ 9 + (-257453593 / 13824000) * d ^ 2 * t ^ 11 + (-17604211 / 27648000) * d ^ 2 * t ^ 13 + (411103 / 41472000) * d ^ 2 * t ^ 15 + (-19411 / 552960) * d ^ 2 * t ^ 17 + (-24491 / 663552) * d ^ 2 * t ^ 19 + (98611 / 5184000) * d ^ 2 * t ^ 21) * alpha_sq + ((-9159 / 2) * t ^ 3 + (4064719 / 640) * t ^ 5 + (-1132358837 / 1152000) * t ^ 7 + (-3786721871 / 4608000) * t ^ 9 + (-74892299 / 921600) * t ^ 11 + (642804551 / 27648000) * t ^ 13 + (-218047973 / 13824000) * t ^ 15 + (19411 / 92160) * t ^ 17 + (10775893 / 82944000) * t ^ 19 + (-777013 / 6912000) * t ^ 21 + (15265 / 48) * alpha * t ^ 3 + (-52277 / 400) * alpha * t ^ 5 + (-1716388631 / 3456000) * alpha * t ^ 7 + (3675957821 / 13824000) * alpha * t ^ 9 + (444241607 / 13824000) * alpha * t ^ 11 + (458885377 / 41472000) * alpha * t ^ 13 + (3053647 / 1382400) * alpha * t ^ 15 + (1325309 / 33177600) * alpha * t ^ 17 + (3465049 / 7776000) * alpha * t ^ 19 + (3975937 / 165888000) * alpha * t ^ 21 + (-4465 / 1990656) * alpha * t ^ 25) * d_sq
theorem v57_44 (t : ℂ) : (momentPoly 57 z57 4 4).eval t = (240274665 + (-771573432) * t ^ 2 + (195537497793 / 200) * t ^ 4 + (-28053686270667 / 40000) * t ^ 6 + (12489689040465499 / 32000000) * t ^ 8 + (-169512689881843 / 1000000) * t ^ 10 + (230814334887937 / 6400000) * t ^ 12 + (-161552711613209 / 48000000) * t ^ 14 + (208881213641243 / 128000000) * t ^ 16 + (-2612160601217 / 16000000) * t ^ 18 + (18843855097753 / 256000000) * t ^ 20 + (-7542535730161 / 128000000) * t ^ 22 + (8232844012251 / 512000000) * t ^ 24 + (-989287353689 / 384000000) * t ^ 26 + (124504544279 / 512000000) * t ^ 32 + (-4104114) * d * t ^ 2 + (391206783 / 40) * d * t ^ 4 + (-52745040699 / 8000) * d * t ^ 6 + (9491387872201 / 19200000) * d * t ^ 8 + (1315633229797 / 9600000) * d * t ^ 10 + (5687366713861 / 19200000) * d * t ^ 12 + (-590866748209 / 11520000) * d * t ^ 14 + (925957531959 / 25600000) * d * t ^ 16 + (29416588337 / 9600000) * d * t ^ 18 + (-367835466041 / 460800000) * d * t ^ 20 + (68591064991 / 76800000) * d * t ^ 22 + (271653827 / 61440000) * d * t ^ 24 + (15368468579 / 230400000) * d * t ^ 26 + (8944877 / 7372800) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_03, v56_04, v56_10, v56_11, v56_12, v56_13, v56_14, v56_20, v56_21, v56_22, v56_23, v56_24, v56_30, v56_31, v56_32, v56_33, v56_34, v56_40, v56_41, v56_42, v56_43, v56_44]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24, phase57_30, phase57_31, phase57_32, phase57_33, phase57_34, phase57_40, phase57_41, phase57_42, phase57_43, phase57_44]
  try simp only [star_one, star_neg]
  linear_combination ((684019 / 3) * t ^ 2 + (-6781853 / 40) * t ^ 4 + (-1389846977 / 3000) * t ^ 6 + (15906022097407 / 28800000) * t ^ 8 + (-8276607928849 / 57600000) * t ^ 10 + (332262820219 / 57600000) * t ^ 12 + (-441135740699 / 41472000) * t ^ 14 + (168333342773 / 86400000) * t ^ 16 + (-19412065147 / 28800000) * t ^ 18 + (310180153681 / 518400000) * t ^ 20 + (-10309415609 / 345600000) * t ^ 22 + (507995737 / 86400000) * t ^ 26 + (-23187821 / 360) * d * t ^ 4 + (2712595357 / 14400) * d * t ^ 6 + (-3283930180069 / 17280000) * d * t ^ 8 + (2568122145991 / 34560000) * d * t ^ 10 + (-396411165031 / 34560000) * d * t ^ 12 + (888611816497 / 207360000) * d * t ^ 14 + (-8824137479 / 8640000) * d * t ^ 16 + (-1699611067 / 51840000) * d * t ^ 18 + (-736135609 / 2488320000) * d * t ^ 20 + (485027489 / 82944000) * d * t ^ 22 + (271653827 / 552960000) * d * t ^ 24 + (-5581915 / 1990656) * d * t ^ 26 + (8944877 / 66355200) * d * t ^ 32 + (-182075 / 1728) * d ^ 2 * t ^ 6 + (178013 / 8100) * d ^ 2 * t ^ 8 + (699356897 / 3456000) * d ^ 2 * t ^ 10 + (-91696193 / 864000) * d ^ 2 * t ^ 12 + (-43551607 / 5184000) * d ^ 2 * t ^ 14 + (-96912859 / 20736000) * d ^ 2 * t ^ 16 + (-901621 / 1296000) * d ^ 2 * t ^ 18 + (-6403969 / 19906560) * d ^ 2 * t ^ 20 + (1119647 / 9216000) * d ^ 2 * t ^ 22 + (-11072437 / 995328000) * d ^ 2 * t ^ 24 + (583547 / 29859840) * d ^ 2 * t ^ 26 + (9025 / 23887872) * d ^ 2 * t ^ 32) * alpha_sq + ((-684019 / 3) * t ^ 2 + (61720259 / 120) * t ^ 4 + (-5376204541 / 14400) * t ^ 6 + (2134572635647 / 17280000) * t ^ 8 + (-243715720063 / 3840000) * t ^ 10 + (92895106139 / 3840000) * t ^ 12 + (482644642159 / 207360000) * t ^ 14 + (-13252634491 / 34560000) * t ^ 16 + (57058373 / 691200) * t ^ 18 + (-23360112811 / 829440000) * t ^ 20 + (6022102327 / 138240000) * t ^ 22 + (11072437 / 331776000) * t ^ 24 + (111907861 / 248832000) * t ^ 26 + (-9025 / 7962624) * t ^ 32) * d_sq
#print axioms v57_00
#print axioms v57_11
#print axioms v57_22
#print axioms v57_33
#print axioms v57_44
end PhotonCertA
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z58 : Fin 58 → ℂ := Fin.snoc z57 (r ^ 3 * phiMinus)
theorem v58_00 (t : ℂ) : (momentPoly 58 z58 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00]
  try simp only [phase57_00]
  try simp only [star_one, star_neg]
  ring
theorem v58_01 (t : ℂ) : (momentPoly 58 z58 0 1).eval t = (1 * t + (-1 / 12) * d * t + (1 / 12) * alpha * t) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01]
  try simp only [phase57_00, phase57_01]
  try simp only [star_one, star_neg]
  ring
theorem v58_02 (t : ℂ) : (momentPoly 58 z58 0 2).eval t = ((653 / 80) * t ^ 2 + (-769 / 240) * t ^ 4 + (-1 / 6) * d * t ^ 2 + (1259 / 120) * alpha * t ^ 2 + (-413 / 40) * alpha * t ^ 4 + (-1 / 48) * alpha * d * t ^ 2 + (1 / 144) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02]
  try simp only [phase57_00, phase57_01, phase57_02]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 96) * t ^ 2) * alpha_sq + ((-1 / 96) * t ^ 2) * d_sq
theorem v58_03 (t : ℂ) : (momentPoly 58 z58 0 3).eval t = ((2359 / 160) * t ^ 3 + (-299 / 160) * t ^ 5 + (-737 / 480) * d * t ^ 3 + (333 / 320) * d * t ^ 5 + (-47 / 576) * d * t ^ 9 + (68629 / 2400) * alpha * t ^ 3 + (-39429 / 1600) * alpha * t ^ 5 + (-39013 / 14400) * alpha * t ^ 9 + (-423 / 160) * alpha * d * t ^ 3 + (1249 / 480) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_03]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03]
  try simp only [star_one, star_neg]
  linear_combination ((-423 / 320) * t ^ 3 + (413 / 320) * t ^ 5 + (1 / 192) * d * t ^ 3 + (-1 / 384) * d * t ^ 5) * alpha_sq + ((-1 / 32) * t ^ 3 + (-1 / 192) * alpha * t ^ 3 + (1 / 384) * alpha * t ^ 5) * d_sq
theorem v58_04 (t : ℂ) : (momentPoly 58 z58 0 4).eval t = ((-18596513 / 24000) * t ^ 4 + (3423063 / 2000) * t ^ 6 + (-29500537 / 32000) * t ^ 8 + (221101 / 8000) * t ^ 10 + (-672719 / 288000) * t ^ 16 + (-513 / 320) * d * t ^ 4 + (-1) * d * t ^ 6 + (413 / 320) * d * t ^ 8 + (-47 / 144) * d * t ^ 10 + (218317 / 500) * alpha * t ^ 4 + (-2244567 / 4000) * alpha * t ^ 6 + (2705187 / 16000) * alpha * t ^ 8 + (-1802479 / 36000) * alpha * t ^ 10 + (470783 / 48000) * alpha * t ^ 16 + (-17021 / 1800) * alpha * d * t ^ 4 + (20647 / 2400) * alpha * d * t ^ 6 + (-671 / 3840) * alpha * d * t ^ 8 + (11821 / 14400) * alpha * d * t ^ 10 + (95 / 6912) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_03, v57_04]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04]
  try simp only [star_one, star_neg]
  linear_combination ((-160043 / 28800) * t ^ 4 + (43249 / 9600) * t ^ 6 + (10621 / 28800) * t ^ 10 + (1279 / 1920) * d * t ^ 4 + (-209 / 240) * d * t ^ 6 + (413 / 1920) * d * t ^ 8 + (1 / 1152) * d ^ 2 * t ^ 6 + (-1 / 4608) * d ^ 2 * t ^ 8) * alpha_sq + ((-3151 / 5760) * t ^ 4 + (51 / 160) * t ^ 6 + (1 / 1536) * t ^ 8 + (-47 / 1152) * t ^ 10 + (-1279 / 1920) * alpha * t ^ 4 + (1259 / 1920) * alpha * t ^ 6) * d_sq
theorem v58_10 (t : ℂ) : (momentPoly 58 z58 1 0).eval t = (1 * t + (-1 / 12) * d * t + (-1 / 12) * alpha * t) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_10]
  try simp only [phase57_00, phase57_10]
  try simp only [star_one, star_neg]
  ring
theorem v58_11 (t : ℂ) : (momentPoly 58 z58 1 1).eval t = (58 + (-53) * t ^ 2 + (-1 / 6) * d * t ^ 2) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_10, v57_11]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 96) * t ^ 2) * alpha_sq + ((-1 / 96) * t ^ 2) * d_sq
theorem v58_12 (t : ℂ) : (momentPoly 58 z58 1 2).eval t = (115 * t + (-15241 / 160) * t ^ 3 + (-3257 / 480) * t ^ 5 + (-115 / 12) * d * t + (4151 / 480) * d * t ^ 3 + (169 / 480) * d * t ^ 5 + (115 / 12) * alpha * t + (209 / 160) * alpha * t ^ 3 + (-5027 / 480) * alpha * t ^ 5 + (-141 / 160) * alpha * d * t ^ 3 + (1249 / 1440) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_10, v57_11, v57_12]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12]
  try simp only [star_one, star_neg]
  linear_combination ((141 / 320) * t ^ 3 + (-413 / 960) * t ^ 5 + (-1 / 576) * d * t ^ 3 + (1 / 1152) * d * t ^ 5) * alpha_sq + ((-1 / 32) * t ^ 3 + (-1 / 576) * alpha * t ^ 3 + (1 / 1152) * alpha * t ^ 5) * d_sq
theorem v58_13 (t : ℂ) : (momentPoly 58 z58 1 3).eval t = ((111663 / 80) * t ^ 2 + (-4385299 / 2400) * t ^ 4 + (745129 / 1600) * t ^ 6 + (10277 / 1600) * t ^ 10 + (-57 / 2) * d * t ^ 2 + (983 / 40) * d * t ^ 4 + (751 / 320) * d * t ^ 6 + (-47 / 576) * d * t ^ 10 + (71763 / 40) * alpha * t ^ 2 + (-4061873 / 1200) * alpha * t ^ 4 + (2536581 / 1600) * alpha * t ^ 6 + (109667 / 14400) * alpha * t ^ 10 + (-57 / 16) * alpha * d * t ^ 2 + (-1471 / 7200) * alpha * d * t ^ 4 + (16531 / 4800) * alpha * d * t ^ 6 + (361 / 1600) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_03, v57_10, v57_11, v57_12, v57_13]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13]
  try simp only [star_one, star_neg]
  linear_combination ((-57 / 32) * t ^ 2 + (23971 / 14400) * t ^ 4 + (997 / 4800) * t ^ 6 + (-10621 / 115200) * t ^ 10) * alpha_sq + ((-57 / 32) * t ^ 2 + (979 / 720) * t ^ 4 + (311 / 1920) * t ^ 6 + (-47 / 4608) * t ^ 10 + (-1279 / 3840) * alpha * t ^ 4 + (1259 / 3840) * alpha * t ^ 6) * d_sq
theorem v58_14 (t : ℂ) : (momentPoly 58 z58 1 4).eval t = ((266567 / 80) * t ^ 3 + (-136243237 / 32000) * t ^ 5 + (31186137 / 16000) * t ^ 7 + (-60000837 / 64000) * t ^ 9 + (1593463 / 48000) * t ^ 11 + (66911 / 576000) * t ^ 17 + (-83281 / 240) * d * t ^ 3 + (60956591 / 96000) * d * t ^ 5 + (-17537491 / 48000) * d * t ^ 7 + (33007243 / 576000) * d * t ^ 9 + (2130101 / 144000) * d * t ^ 11 + (161099 / 576000) * d * t ^ 17 + (7755077 / 1200) * alpha * t ^ 3 + (-210056849 / 19200) * alpha * t ^ 5 + (40645717 / 9600) * alpha * t ^ 7 + (-1460213 / 4608) * alpha * t ^ 9 + (1073267 / 1920) * alpha * t ^ 11 + (1388803 / 115200) * alpha * t ^ 17 + (-47799 / 80) * alpha * d * t ^ 3 + (36078611 / 32000) * alpha * d * t ^ 5 + (-24554693 / 48000) * alpha * d * t ^ 7 + (-3758587 / 192000) * alpha * d * t ^ 9 + (24817 / 16000) * alpha * d * t ^ 11 + (-1388599 / 1728000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_03, v57_04, v57_10, v57_11, v57_12, v57_13, v57_14]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14]
  try simp only [star_one, star_neg]
  linear_combination ((-47799 / 160) * t ^ 3 + (108641077 / 192000) * t ^ 5 + (-105367033 / 384000) * t ^ 7 + (1843031 / 192000) * t ^ 9 + (-966383 / 288000) * t ^ 11 + (470783 / 1152000) * t ^ 17 + (113 / 96) * d * t ^ 3 + (-25201 / 23040) * d * t ^ 5 + (-791 / 2880) * d * t ^ 7 + (9623 / 46080) * d * t ^ 9 + (-47 / 6912) * d * t ^ 11 + (95 / 55296) * d * t ^ 17 + (1279 / 46080) * d ^ 2 * t ^ 7 + (-1249 / 46080) * d ^ 2 * t ^ 9) * alpha_sq + ((-113 / 16) * t ^ 3 + (61031 / 11520) * t ^ 5 + (4187 / 7680) * t ^ 7 + (311 / 1920) * t ^ 9 + (-47 / 576) * t ^ 11 + (-113 / 96) * alpha * t ^ 3 + (-2597 / 12800) * alpha * t ^ 5 + (17789 / 14400) * alpha * t ^ 7 + (-1249 / 46080) * alpha * t ^ 9 + (17719 / 172800) * alpha * t ^ 11 + (95 / 55296) * alpha * t ^ 17) * d_sq
theorem v58_20 (t : ℂ) : (momentPoly 58 z58 2 0).eval t = ((653 / 80) * t ^ 2 + (-769 / 240) * t ^ 4 + (-1 / 6) * d * t ^ 2 + (-1259 / 120) * alpha * t ^ 2 + (413 / 40) * alpha * t ^ 4 + (1 / 48) * alpha * d * t ^ 2 + (-1 / 144) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_10, v57_20]
  try simp only [phase57_00, phase57_10, phase57_20]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 96) * t ^ 2) * alpha_sq + ((-1 / 96) * t ^ 2) * d_sq
theorem v58_21 (t : ℂ) : (momentPoly 58 z58 2 1).eval t = (115 * t + (-15241 / 160) * t ^ 3 + (-3257 / 480) * t ^ 5 + (-115 / 12) * d * t + (4151 / 480) * d * t ^ 3 + (169 / 480) * d * t ^ 5 + (-115 / 12) * alpha * t + (-209 / 160) * alpha * t ^ 3 + (5027 / 480) * alpha * t ^ 5 + (141 / 160) * alpha * d * t ^ 3 + (-1249 / 1440) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_10, v57_11, v57_20, v57_21]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21]
  try simp only [star_one, star_neg]
  linear_combination ((141 / 320) * t ^ 3 + (-413 / 960) * t ^ 5 + (-1 / 576) * d * t ^ 3 + (1 / 1152) * d * t ^ 5) * alpha_sq + ((-1 / 32) * t ^ 3 + (1 / 576) * alpha * t ^ 3 + (-1 / 1152) * alpha * t ^ 5) * d_sq
theorem v58_22 (t : ℂ) : (momentPoly 58 z58 2 2).eval t = (6670 + (-12084) * t ^ 2 + (9077623 / 1600) * t ^ 4 + (-588917 / 1200) * t ^ 6 + (1306399 / 4800) * t ^ 8 + (-38) * d * t ^ 2 + (31969 / 960) * d * t ^ 4 + (277 / 80) * d * t ^ 6 + (-413 / 960) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_10, v57_11, v57_12, v57_20, v57_21, v57_22]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22]
  try simp only [star_one, star_neg]
  linear_combination ((19 / 8) * t ^ 2 + (-47 / 128) * t ^ 4 + (-683 / 384) * t ^ 6 + (-1279 / 5760) * d * t ^ 4 + (209 / 720) * d * t ^ 6 + (-413 / 5760) * d * t ^ 8 + (-1 / 3456) * d ^ 2 * t ^ 6 + (1 / 13824) * d ^ 2 * t ^ 8) * alpha_sq + ((-19 / 8) * t ^ 2 + (1277 / 640) * t ^ 4 + (79 / 720) * t ^ 6 + (-1 / 4608) * t ^ 8) * d_sq
theorem v58_23 (t : ℂ) : (momentPoly 58 z58 2 3).eval t = (19666 * t + (-5166699 / 160) * t ^ 3 + (539060813 / 48000) * t ^ 5 + (32532449 / 38400) * t ^ 7 + (41582541 / 64000) * t ^ 9 + (-12270689 / 192000) * t ^ 11 + (15920369 / 192000) * t ^ 13 + (-9833 / 6) * d * t + (469063 / 160) * d * t ^ 3 + (-5941159 / 4800) * d * t ^ 5 + (30773 / 2560) * d * t ^ 7 + (-182409 / 2560) * d * t ^ 9 + (-138341 / 115200) * d * t ^ 11 + (33217 / 115200) * d * t ^ 13 + (9833 / 6) * alpha * t + (70851 / 160) * alpha * t ^ 3 + (-63425453 / 12000) * alpha * t ^ 5 + (120105157 / 38400) * alpha * t ^ 7 + (4652401 / 64000) * alpha * t ^ 9 + (-1234007 / 576000) * alpha * t ^ 11 + (5139187 / 576000) * alpha * t ^ 13 + (-47799 / 160) * alpha * d * t ^ 3 + (16607617 / 28800) * alpha * d * t ^ 5 + (-31863947 / 115200) * alpha * d * t ^ 7 + (-1399 / 7680) * alpha * d * t ^ 9 + (-49201 / 115200) * alpha * d * t ^ 11 + (-19411 / 23040) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_03, v57_10, v57_11, v57_12, v57_13, v57_20, v57_21, v57_22, v57_23]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23]
  try simp only [star_one, star_neg]
  linear_combination ((47799 / 320) * t ^ 3 + (-7654211 / 28800) * t ^ 5 + (1117123 / 9600) * t ^ 7 + (451051 / 230400) * t ^ 11 + (-59059 / 46080) * t ^ 13 + (-113 / 192) * d * t ^ 3 + (12829 / 57600) * d * t ^ 5 + (376117 / 691200) * d * t ^ 7 + (-47237 / 230400) * d * t ^ 9 + (15319 / 691200) * d * t ^ 11 + (-10621 / 1382400) * d * t ^ 13 + (-1279 / 46080) * d ^ 2 * t ^ 7 + (1249 / 46080) * d ^ 2 * t ^ 9) * alpha_sq + ((-339 / 32) * t ^ 3 + (96809 / 11520) * t ^ 5 + (3151 / 2560) * t ^ 7 + (-311 / 1920) * t ^ 9 + (-47 / 2304) * t ^ 11 + (-113 / 192) * alpha * t ^ 3 + (12829 / 57600) * alpha * t ^ 5 + (217883 / 691200) * alpha * t ^ 7 + (-1 / 9216) * alpha * t ^ 9 + (20069 / 691200) * alpha * t ^ 11 + (-47 / 55296) * alpha * t ^ 13) * d_sq
theorem v58_24 (t : ℂ) : (momentPoly 58 z58 2 4).eval t = ((2523845 / 8) * t ^ 2 + (-836377691 / 1200) * t ^ 4 + (299119021233 / 640000) * t ^ 6 + (-56185615689 / 640000) * t ^ 8 + (2334175163 / 384000) * t ^ 10 + (-831413503 / 160000) * t ^ 12 + (1017924799 / 720000) * t ^ 14 + (795748229 / 2880000) * t ^ 18 + (-1687389283 / 5760000) * t ^ 20 + (-19325 / 3) * d * t ^ 2 + (55048 / 5) * d * t ^ 4 + (-461773497 / 128000) * d * t ^ 6 + (-338787197 / 384000) * d * t ^ 8 + (-14476663 / 115200) * d * t ^ 10 + (4361747 / 76800) * d * t ^ 12 + (-7036331 / 288000) * d * t ^ 14 + (428659 / 1152000) * d * t ^ 18 + (-127523 / 576000) * d * t ^ 20 + (4866035 / 12) * alpha * t ^ 2 + (-674740717 / 600) * alpha * t ^ 4 + (1985973616601 / 1920000) * alpha * t ^ 6 + (-206842602091 / 640000) * alpha * t ^ 8 + (20441524831 / 1152000) * alpha * t ^ 10 + (-14754962393 / 1440000) * alpha * t ^ 12 + (29972519 / 80000) * alpha * t ^ 14 + (28166489 / 320000) * alpha * t ^ 18 + (-86820179 / 1920000) * alpha * t ^ 20 + (-19325 / 24) * alpha * d * t ^ 2 + (-1278329 / 3600) * alpha * d * t ^ 4 + (213277903 / 76800) * alpha * d * t ^ 6 + (-1730235497 / 1152000) * alpha * d * t ^ 8 + (-17349673 / 576000) * alpha * d * t ^ 10 + (-88096153 / 1152000) * alpha * d * t ^ 12 + (-6057823 / 864000) * alpha * d * t ^ 14 + (-6989377 / 3456000) * alpha * d * t ^ 18 + (-20023 / 576000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_03, v57_04, v57_10, v57_11, v57_12, v57_13, v57_14, v57_20, v57_21, v57_22, v57_23, v57_24]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24]
  try simp only [star_one, star_neg]
  linear_combination ((-19325 / 48) * t ^ 2 + (167797 / 225) * t ^ 4 + (-424483603 / 2304000) * t ^ 6 + (-193828501 / 1152000) * t ^ 8 + (-110693401 / 4608000) * t ^ 10 + (23983553 / 576000) * t ^ 12 + (-115307 / 16000) * t ^ 14 + (4350043 / 4608000) * t ^ 18 + (-11583241 / 2304000) * d * t ^ 6 + (72357697 / 6912000) * d * t ^ 8 + (-3749813 / 576000) * d * t ^ 10 + (995767 / 2304000) * d * t ^ 12 + (1369 / 2000) * d * t ^ 14 + (-191987 / 6912000) * d * t ^ 18 + (-127523 / 3456000) * d * t ^ 20 + (-74689 / 1382400) * d ^ 2 * t ^ 8 + (134117 / 2764800) * d ^ 2 * t ^ 10 + (-311 / 276480) * d ^ 2 * t ^ 12 + (517 / 129600) * d ^ 2 * t ^ 14 + (-95 / 331776) * d ^ 2 * t ^ 18 + (95 / 663552) * d ^ 2 * t ^ 20) * alpha_sq + ((-19325 / 48) * t ^ 2 + (27412 / 45) * t ^ 4 + (-119815609 / 768000) * t ^ 6 + (-35691607 / 768000) * t ^ 8 + (-10800907 / 768000) * t ^ 10 + (775243 / 256000) * t ^ 12 + (64813 / 345600) * t ^ 14 + (159043 / 3456000) * t ^ 18 + (-95 / 221184) * t ^ 20 + (-8953 / 60) * alpha * t ^ 4 + (638259439 / 2304000) * alpha * t ^ 6 + (-215115451 / 1728000) * alpha * t ^ 8 + (-1898117 / 576000) * alpha * t ^ 10 + (4297631 / 13824000) * alpha * t ^ 12 + (-58703 / 138240) * alpha * t ^ 14 + (-1364849 / 13824000) * alpha * t ^ 18) * d_sq
theorem v58_30 (t : ℂ) : (momentPoly 58 z58 3 0).eval t = ((2359 / 160) * t ^ 3 + (-299 / 160) * t ^ 5 + (-737 / 480) * d * t ^ 3 + (333 / 320) * d * t ^ 5 + (-47 / 576) * d * t ^ 9 + (-68629 / 2400) * alpha * t ^ 3 + (39429 / 1600) * alpha * t ^ 5 + (39013 / 14400) * alpha * t ^ 9 + (423 / 160) * alpha * d * t ^ 3 + (-1249 / 480) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_10, v57_20, v57_30]
  try simp only [phase57_00, phase57_10, phase57_20, phase57_30]
  try simp only [star_one, star_neg]
  linear_combination ((-423 / 320) * t ^ 3 + (413 / 320) * t ^ 5 + (1 / 192) * d * t ^ 3 + (-1 / 384) * d * t ^ 5) * alpha_sq + ((-1 / 32) * t ^ 3 + (1 / 192) * alpha * t ^ 3 + (-1 / 384) * alpha * t ^ 5) * d_sq
theorem v58_31 (t : ℂ) : (momentPoly 58 z58 3 1).eval t = ((111663 / 80) * t ^ 2 + (-4385299 / 2400) * t ^ 4 + (745129 / 1600) * t ^ 6 + (10277 / 1600) * t ^ 10 + (-57 / 2) * d * t ^ 2 + (983 / 40) * d * t ^ 4 + (751 / 320) * d * t ^ 6 + (-47 / 576) * d * t ^ 10 + (-71763 / 40) * alpha * t ^ 2 + (4061873 / 1200) * alpha * t ^ 4 + (-2536581 / 1600) * alpha * t ^ 6 + (-109667 / 14400) * alpha * t ^ 10 + (57 / 16) * alpha * d * t ^ 2 + (1471 / 7200) * alpha * d * t ^ 4 + (-16531 / 4800) * alpha * d * t ^ 6 + (-361 / 1600) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_10, v57_11, v57_20, v57_21, v57_30, v57_31]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21, phase57_30, phase57_31]
  try simp only [star_one, star_neg]
  linear_combination ((-57 / 32) * t ^ 2 + (23971 / 14400) * t ^ 4 + (997 / 4800) * t ^ 6 + (-10621 / 115200) * t ^ 10) * alpha_sq + ((-57 / 32) * t ^ 2 + (979 / 720) * t ^ 4 + (311 / 1920) * t ^ 6 + (-47 / 4608) * t ^ 10 + (1279 / 3840) * alpha * t ^ 4 + (-1259 / 3840) * alpha * t ^ 6) * d_sq
theorem v58_32 (t : ℂ) : (momentPoly 58 z58 3 2).eval t = (19666 * t + (-5166699 / 160) * t ^ 3 + (539060813 / 48000) * t ^ 5 + (32532449 / 38400) * t ^ 7 + (41582541 / 64000) * t ^ 9 + (-12270689 / 192000) * t ^ 11 + (15920369 / 192000) * t ^ 13 + (-9833 / 6) * d * t + (469063 / 160) * d * t ^ 3 + (-5941159 / 4800) * d * t ^ 5 + (30773 / 2560) * d * t ^ 7 + (-182409 / 2560) * d * t ^ 9 + (-138341 / 115200) * d * t ^ 11 + (33217 / 115200) * d * t ^ 13 + (-9833 / 6) * alpha * t + (-70851 / 160) * alpha * t ^ 3 + (63425453 / 12000) * alpha * t ^ 5 + (-120105157 / 38400) * alpha * t ^ 7 + (-4652401 / 64000) * alpha * t ^ 9 + (1234007 / 576000) * alpha * t ^ 11 + (-5139187 / 576000) * alpha * t ^ 13 + (47799 / 160) * alpha * d * t ^ 3 + (-16607617 / 28800) * alpha * d * t ^ 5 + (31863947 / 115200) * alpha * d * t ^ 7 + (1399 / 7680) * alpha * d * t ^ 9 + (49201 / 115200) * alpha * d * t ^ 11 + (19411 / 23040) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_10, v57_11, v57_12, v57_20, v57_21, v57_22, v57_30, v57_31, v57_32]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22, phase57_30, phase57_31, phase57_32]
  try simp only [star_one, star_neg]
  linear_combination ((47799 / 320) * t ^ 3 + (-7654211 / 28800) * t ^ 5 + (1117123 / 9600) * t ^ 7 + (451051 / 230400) * t ^ 11 + (-59059 / 46080) * t ^ 13 + (-113 / 192) * d * t ^ 3 + (12829 / 57600) * d * t ^ 5 + (376117 / 691200) * d * t ^ 7 + (-47237 / 230400) * d * t ^ 9 + (15319 / 691200) * d * t ^ 11 + (-10621 / 1382400) * d * t ^ 13 + (-1279 / 46080) * d ^ 2 * t ^ 7 + (1249 / 46080) * d ^ 2 * t ^ 9) * alpha_sq + ((-339 / 32) * t ^ 3 + (96809 / 11520) * t ^ 5 + (3151 / 2560) * t ^ 7 + (-311 / 1920) * t ^ 9 + (-47 / 2304) * t ^ 11 + (113 / 192) * alpha * t ^ 3 + (-12829 / 57600) * alpha * t ^ 5 + (-217883 / 691200) * alpha * t ^ 7 + (1 / 9216) * alpha * t ^ 9 + (-20069 / 691200) * alpha * t ^ 11 + (47 / 55296) * alpha * t ^ 13) * d_sq
theorem v58_33 (t : ℂ) : (momentPoly 58 z58 3 3).eval t = (1140628 + (-3072675) * t ^ 2 + (571890249 / 200) * t ^ 4 + (-93008423541 / 80000) * t ^ 6 + (57070840171 / 160000) * t ^ 8 + (-38795232819 / 320000) * t ^ 10 + (552498979 / 480000) * t ^ 12 + (-80937901 / 80000) * t ^ 14 + (-30878423 / 960000) * t ^ 18 + (-19325 / 2) * d * t ^ 2 + (671349 / 40) * d * t ^ 4 + (-273009079 / 48000) * d * t ^ 6 + (-4233571 / 3200) * d * t ^ 8 + (-939741 / 8000) * d * t ^ 10 + (4346159 / 144000) * d * t ^ 12 + (-1843763 / 48000) * d * t ^ 14) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_03, v57_10, v57_11, v57_12, v57_13, v57_20, v57_21, v57_22, v57_23, v57_30, v57_31, v57_32, v57_33]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23, phase57_30, phase57_31, phase57_32, phase57_33]
  try simp only [star_one, star_neg]
  linear_combination ((19325 / 32) * t ^ 2 + (-2961 / 16) * t ^ 4 + (-436061239 / 384000) * t ^ 6 + (53596147 / 76800) * t ^ 8 + (6585391 / 256000) * t ^ 10 + (3257783 / 864000) * t ^ 12 + (-8868143 / 2304000) * t ^ 14 + (-3548831 / 5529600) * t ^ 18 + (-8953 / 80) * d * t ^ 4 + (19037947 / 76800) * d * t ^ 6 + (-18972263 / 115200) * d * t ^ 8 + (2227451 / 76800) * d * t ^ 10 + (-133361 / 115200) * d * t ^ 12 + (187619 / 230400) * d * t ^ 14 + (-169 / 1152) * d ^ 2 * t ^ 6 + (4279 / 230400) * d ^ 2 * t ^ 8 + (5777 / 51200) * d ^ 2 * t ^ 10 + (3149 / 460800) * d ^ 2 * t ^ 14) * alpha_sq + ((-19325 / 32) * t ^ 2 + (80451 / 80) * t ^ 4 + (-5878237 / 15360) * t ^ 6 + (11273 / 3840) * t ^ 8 + (-358859 / 12800) * t ^ 10 + (-326609 / 345600) * t ^ 12 + (31819 / 115200) * t ^ 14 + (-2209 / 221184) * t ^ 18) * d_sq
theorem v58_34 (t : ℂ) : (momentPoly 58 z58 3 4).eval t = (4445203 * t + (-868142601 / 80) * t ^ 3 + (65906635393 / 8000) * t ^ 5 + (-6415201400791 / 3200000) * t ^ 7 + (7048632938909 / 12800000) * t ^ 9 + (-2638413932747 / 6400000) * t ^ 11 + (432816199417 / 5120000) * t ^ 13 + (-151377362883 / 3200000) * t ^ 15 + (-107045116681 / 76800000) * t ^ 17 + (46007969287 / 57600000) * t ^ 19 + (-68171873011 / 76800000) * t ^ 21 + (-18597057179 / 230400000) * t ^ 25 + (-4445203 / 12) * d * t + (78815037 / 80) * d * t ^ 3 + (-172742351 / 200) * d * t ^ 5 + (566385493687 / 1920000) * d * t ^ 7 + (-691674032459 / 7680000) * d * t ^ 9 + (81951739763 / 1920000) * d * t ^ 11 + (71726528693 / 46080000) * d * t ^ 13 + (-247652233 / 720000) * d * t ^ 15 + (686882681 / 9216000) * d * t ^ 17 + (-522736829 / 8640000) * d * t ^ 19 + (364520639 / 5120000) * d * t ^ 21 + (4485103 / 27648000) * d * t ^ 25 + (4445203 / 12) * alpha * t + (11904849 / 80) * alpha * t ^ 3 + (-9395412241 / 4000) * alpha * t ^ 5 + (26203306308877 / 9600000) * alpha * t ^ 7 + (-33481318330963 / 38400000) * alpha * t ^ 9 + (-70748313919 / 4800000) * alpha * t ^ 11 + (-478921009099 / 46080000) * alpha * t ^ 13 + (-7501128971 / 14400000) * alpha * t ^ 15 + (-559092100303 / 230400000) * alpha * t ^ 17 + (16203632323 / 86400000) * alpha * t ^ 19 + (-4841724191 / 76800000) * alpha * t ^ 21 + (-4875905537 / 691200000) * alpha * t ^ 25 + (-8031501 / 80) * alpha * d * t ^ 3 + (1377830777 / 4800) * alpha * d * t ^ 5 + (-1569892770197 / 5760000) * alpha * d * t ^ 7 + (673825609123 / 7680000) * alpha * d * t ^ 9 + (-588661613 / 153600) * alpha * d * t ^ 11 + (7759861921 / 5120000) * alpha * d * t ^ 13 + (936333091 / 1920000) * alpha * d * t ^ 15 + (-142880651 / 9216000) * alpha * d * t ^ 17 + (-151828841 / 11520000) * alpha * d * t ^ 19 + (82862891 / 5120000) * alpha * d * t ^ 21 + (-22126801 / 27648000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_03, v57_04, v57_10, v57_11, v57_12, v57_13, v57_14, v57_20, v57_21, v57_22, v57_23, v57_24, v57_30, v57_31, v57_32, v57_33, v57_34]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24, phase57_30, phase57_31, phase57_32, phase57_33, phase57_34]
  try simp only [star_one, star_neg]
  linear_combination ((8031501 / 160) * t ^ 3 + (-6444521 / 50) * t ^ 5 + (34857953917 / 320000) * t ^ 7 + (-970234036151 / 30720000) * t ^ 9 + (143069941 / 40960) * t ^ 11 + (-1556871491389 / 552960000) * t ^ 13 + (6693960459 / 10240000) * t ^ 15 + (263553433 / 9216000) * t ^ 17 + (348707847 / 20480000) * t ^ 19 + (-82971761 / 10240000) * t ^ 21 + (67321969 / 55296000) * t ^ 25 + (-6329 / 32) * d * t ^ 3 + (123011 / 2400) * d * t ^ 5 + (1890337541 / 3456000) * d * t ^ 7 + (-874873909 / 1843200) * d * t ^ 9 + (367756979 / 4608000) * d * t ^ 11 + (-250784707 / 18432000) * d * t ^ 13 + (104626793 / 13824000) * d * t ^ 15 + (10963099 / 55296000) * d * t ^ 17 + (13709857 / 82944000) * d * t ^ 19 + (-4178987 / 55296000) * d * t ^ 21 + (-201799 / 13271040) * d * t ^ 25 + (-85693 / 4608) * d ^ 2 * t ^ 7 + (634556239 / 18432000) * d ^ 2 * t ^ 9 + (-142305409 / 9216000) * d ^ 2 * t ^ 11 + (-14544911 / 36864000) * d ^ 2 * t ^ 13 + (506603 / 55296000) * d ^ 2 * t ^ 15 + (-19411 / 737280) * d ^ 2 * t ^ 17 + (-24301 / 884736) * d ^ 2 * t ^ 19 + (98611 / 6912000) * d ^ 2 * t ^ 21) * alpha_sq + ((-56961 / 16) * t ^ 3 + (3581933 / 640) * t ^ 5 + (-1625176021 / 1152000) * t ^ 7 + (-649030563 / 1024000) * t ^ 9 + (-25343669 / 768000) * t ^ 11 + (239463941 / 11059200) * t ^ 13 + (-117656549 / 9216000) * t ^ 15 + (19411 / 122880) * t ^ 17 + (1155769 / 11059200) * t ^ 19 + (-777013 / 9216000) * t ^ 21 + (-6329 / 32) * alpha * t ^ 3 + (123011 / 2400) * alpha * t ^ 5 + (1360253641 / 3456000) * alpha * t ^ 7 + (-2012883461 / 9216000) * alpha * t ^ 9 + (-79074697 / 4608000) * alpha * t ^ 11 + (-561306121 / 55296000) * alpha * t ^ 13 + (-4181171 / 2764800) * alpha * t ^ 15 + (-274621 / 11059200) * alpha * t ^ 17 + (-29314763 / 82944000) * alpha * t ^ 19 + (-852953 / 55296000) * alpha * t ^ 21 + (4465 / 2654208) * alpha * t ^ 25) * d_sq
theorem v58_40 (t : ℂ) : (momentPoly 58 z58 4 0).eval t = ((-18596513 / 24000) * t ^ 4 + (3423063 / 2000) * t ^ 6 + (-29500537 / 32000) * t ^ 8 + (221101 / 8000) * t ^ 10 + (-672719 / 288000) * t ^ 16 + (-513 / 320) * d * t ^ 4 + (-1) * d * t ^ 6 + (413 / 320) * d * t ^ 8 + (-47 / 144) * d * t ^ 10 + (-218317 / 500) * alpha * t ^ 4 + (2244567 / 4000) * alpha * t ^ 6 + (-2705187 / 16000) * alpha * t ^ 8 + (1802479 / 36000) * alpha * t ^ 10 + (-470783 / 48000) * alpha * t ^ 16 + (17021 / 1800) * alpha * d * t ^ 4 + (-20647 / 2400) * alpha * d * t ^ 6 + (671 / 3840) * alpha * d * t ^ 8 + (-11821 / 14400) * alpha * d * t ^ 10 + (-95 / 6912) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_10, v57_20, v57_30, v57_40]
  try simp only [phase57_00, phase57_10, phase57_20, phase57_30, phase57_40]
  try simp only [star_one, star_neg]
  linear_combination ((-160043 / 28800) * t ^ 4 + (43249 / 9600) * t ^ 6 + (10621 / 28800) * t ^ 10 + (1279 / 1920) * d * t ^ 4 + (-209 / 240) * d * t ^ 6 + (413 / 1920) * d * t ^ 8 + (1 / 1152) * d ^ 2 * t ^ 6 + (-1 / 4608) * d ^ 2 * t ^ 8) * alpha_sq + ((-3151 / 5760) * t ^ 4 + (51 / 160) * t ^ 6 + (1 / 1536) * t ^ 8 + (-47 / 1152) * t ^ 10 + (1279 / 1920) * alpha * t ^ 4 + (-1259 / 1920) * alpha * t ^ 6) * d_sq
theorem v58_41 (t : ℂ) : (momentPoly 58 z58 4 1).eval t = ((266567 / 80) * t ^ 3 + (-136243237 / 32000) * t ^ 5 + (31186137 / 16000) * t ^ 7 + (-60000837 / 64000) * t ^ 9 + (1593463 / 48000) * t ^ 11 + (66911 / 576000) * t ^ 17 + (-83281 / 240) * d * t ^ 3 + (60956591 / 96000) * d * t ^ 5 + (-17537491 / 48000) * d * t ^ 7 + (33007243 / 576000) * d * t ^ 9 + (2130101 / 144000) * d * t ^ 11 + (161099 / 576000) * d * t ^ 17 + (-7755077 / 1200) * alpha * t ^ 3 + (210056849 / 19200) * alpha * t ^ 5 + (-40645717 / 9600) * alpha * t ^ 7 + (1460213 / 4608) * alpha * t ^ 9 + (-1073267 / 1920) * alpha * t ^ 11 + (-1388803 / 115200) * alpha * t ^ 17 + (47799 / 80) * alpha * d * t ^ 3 + (-36078611 / 32000) * alpha * d * t ^ 5 + (24554693 / 48000) * alpha * d * t ^ 7 + (3758587 / 192000) * alpha * d * t ^ 9 + (-24817 / 16000) * alpha * d * t ^ 11 + (1388599 / 1728000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_10, v57_11, v57_20, v57_21, v57_30, v57_31, v57_40, v57_41]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21, phase57_30, phase57_31, phase57_40, phase57_41]
  try simp only [star_one, star_neg]
  linear_combination ((-47799 / 160) * t ^ 3 + (108641077 / 192000) * t ^ 5 + (-105367033 / 384000) * t ^ 7 + (1843031 / 192000) * t ^ 9 + (-966383 / 288000) * t ^ 11 + (470783 / 1152000) * t ^ 17 + (113 / 96) * d * t ^ 3 + (-25201 / 23040) * d * t ^ 5 + (-791 / 2880) * d * t ^ 7 + (9623 / 46080) * d * t ^ 9 + (-47 / 6912) * d * t ^ 11 + (95 / 55296) * d * t ^ 17 + (1279 / 46080) * d ^ 2 * t ^ 7 + (-1249 / 46080) * d ^ 2 * t ^ 9) * alpha_sq + ((-113 / 16) * t ^ 3 + (61031 / 11520) * t ^ 5 + (4187 / 7680) * t ^ 7 + (311 / 1920) * t ^ 9 + (-47 / 576) * t ^ 11 + (113 / 96) * alpha * t ^ 3 + (2597 / 12800) * alpha * t ^ 5 + (-17789 / 14400) * alpha * t ^ 7 + (1249 / 46080) * alpha * t ^ 9 + (-17719 / 172800) * alpha * t ^ 11 + (-95 / 55296) * alpha * t ^ 17) * d_sq
theorem v58_42 (t : ℂ) : (momentPoly 58 z58 4 2).eval t = ((2523845 / 8) * t ^ 2 + (-836377691 / 1200) * t ^ 4 + (299119021233 / 640000) * t ^ 6 + (-56185615689 / 640000) * t ^ 8 + (2334175163 / 384000) * t ^ 10 + (-831413503 / 160000) * t ^ 12 + (1017924799 / 720000) * t ^ 14 + (795748229 / 2880000) * t ^ 18 + (-1687389283 / 5760000) * t ^ 20 + (-19325 / 3) * d * t ^ 2 + (55048 / 5) * d * t ^ 4 + (-461773497 / 128000) * d * t ^ 6 + (-338787197 / 384000) * d * t ^ 8 + (-14476663 / 115200) * d * t ^ 10 + (4361747 / 76800) * d * t ^ 12 + (-7036331 / 288000) * d * t ^ 14 + (428659 / 1152000) * d * t ^ 18 + (-127523 / 576000) * d * t ^ 20 + (-4866035 / 12) * alpha * t ^ 2 + (674740717 / 600) * alpha * t ^ 4 + (-1985973616601 / 1920000) * alpha * t ^ 6 + (206842602091 / 640000) * alpha * t ^ 8 + (-20441524831 / 1152000) * alpha * t ^ 10 + (14754962393 / 1440000) * alpha * t ^ 12 + (-29972519 / 80000) * alpha * t ^ 14 + (-28166489 / 320000) * alpha * t ^ 18 + (86820179 / 1920000) * alpha * t ^ 20 + (19325 / 24) * alpha * d * t ^ 2 + (1278329 / 3600) * alpha * d * t ^ 4 + (-213277903 / 76800) * alpha * d * t ^ 6 + (1730235497 / 1152000) * alpha * d * t ^ 8 + (17349673 / 576000) * alpha * d * t ^ 10 + (88096153 / 1152000) * alpha * d * t ^ 12 + (6057823 / 864000) * alpha * d * t ^ 14 + (6989377 / 3456000) * alpha * d * t ^ 18 + (20023 / 576000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_10, v57_11, v57_12, v57_20, v57_21, v57_22, v57_30, v57_31, v57_32, v57_40, v57_41, v57_42]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22, phase57_30, phase57_31, phase57_32, phase57_40, phase57_41, phase57_42]
  try simp only [star_one, star_neg]
  linear_combination ((-19325 / 48) * t ^ 2 + (167797 / 225) * t ^ 4 + (-424483603 / 2304000) * t ^ 6 + (-193828501 / 1152000) * t ^ 8 + (-110693401 / 4608000) * t ^ 10 + (23983553 / 576000) * t ^ 12 + (-115307 / 16000) * t ^ 14 + (4350043 / 4608000) * t ^ 18 + (-11583241 / 2304000) * d * t ^ 6 + (72357697 / 6912000) * d * t ^ 8 + (-3749813 / 576000) * d * t ^ 10 + (995767 / 2304000) * d * t ^ 12 + (1369 / 2000) * d * t ^ 14 + (-191987 / 6912000) * d * t ^ 18 + (-127523 / 3456000) * d * t ^ 20 + (-74689 / 1382400) * d ^ 2 * t ^ 8 + (134117 / 2764800) * d ^ 2 * t ^ 10 + (-311 / 276480) * d ^ 2 * t ^ 12 + (517 / 129600) * d ^ 2 * t ^ 14 + (-95 / 331776) * d ^ 2 * t ^ 18 + (95 / 663552) * d ^ 2 * t ^ 20) * alpha_sq + ((-19325 / 48) * t ^ 2 + (27412 / 45) * t ^ 4 + (-119815609 / 768000) * t ^ 6 + (-35691607 / 768000) * t ^ 8 + (-10800907 / 768000) * t ^ 10 + (775243 / 256000) * t ^ 12 + (64813 / 345600) * t ^ 14 + (159043 / 3456000) * t ^ 18 + (-95 / 221184) * t ^ 20 + (8953 / 60) * alpha * t ^ 4 + (-638259439 / 2304000) * alpha * t ^ 6 + (215115451 / 1728000) * alpha * t ^ 8 + (1898117 / 576000) * alpha * t ^ 10 + (-4297631 / 13824000) * alpha * t ^ 12 + (58703 / 138240) * alpha * t ^ 14 + (1364849 / 13824000) * alpha * t ^ 18) * d_sq
theorem v58_43 (t : ℂ) : (momentPoly 58 z58 4 3).eval t = (4445203 * t + (-868142601 / 80) * t ^ 3 + (65906635393 / 8000) * t ^ 5 + (-6415201400791 / 3200000) * t ^ 7 + (7048632938909 / 12800000) * t ^ 9 + (-2638413932747 / 6400000) * t ^ 11 + (432816199417 / 5120000) * t ^ 13 + (-151377362883 / 3200000) * t ^ 15 + (-107045116681 / 76800000) * t ^ 17 + (46007969287 / 57600000) * t ^ 19 + (-68171873011 / 76800000) * t ^ 21 + (-18597057179 / 230400000) * t ^ 25 + (-4445203 / 12) * d * t + (78815037 / 80) * d * t ^ 3 + (-172742351 / 200) * d * t ^ 5 + (566385493687 / 1920000) * d * t ^ 7 + (-691674032459 / 7680000) * d * t ^ 9 + (81951739763 / 1920000) * d * t ^ 11 + (71726528693 / 46080000) * d * t ^ 13 + (-247652233 / 720000) * d * t ^ 15 + (686882681 / 9216000) * d * t ^ 17 + (-522736829 / 8640000) * d * t ^ 19 + (364520639 / 5120000) * d * t ^ 21 + (4485103 / 27648000) * d * t ^ 25 + (-4445203 / 12) * alpha * t + (-11904849 / 80) * alpha * t ^ 3 + (9395412241 / 4000) * alpha * t ^ 5 + (-26203306308877 / 9600000) * alpha * t ^ 7 + (33481318330963 / 38400000) * alpha * t ^ 9 + (70748313919 / 4800000) * alpha * t ^ 11 + (478921009099 / 46080000) * alpha * t ^ 13 + (7501128971 / 14400000) * alpha * t ^ 15 + (559092100303 / 230400000) * alpha * t ^ 17 + (-16203632323 / 86400000) * alpha * t ^ 19 + (4841724191 / 76800000) * alpha * t ^ 21 + (4875905537 / 691200000) * alpha * t ^ 25 + (8031501 / 80) * alpha * d * t ^ 3 + (-1377830777 / 4800) * alpha * d * t ^ 5 + (1569892770197 / 5760000) * alpha * d * t ^ 7 + (-673825609123 / 7680000) * alpha * d * t ^ 9 + (588661613 / 153600) * alpha * d * t ^ 11 + (-7759861921 / 5120000) * alpha * d * t ^ 13 + (-936333091 / 1920000) * alpha * d * t ^ 15 + (142880651 / 9216000) * alpha * d * t ^ 17 + (151828841 / 11520000) * alpha * d * t ^ 19 + (-82862891 / 5120000) * alpha * d * t ^ 21 + (22126801 / 27648000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_03, v57_10, v57_11, v57_12, v57_13, v57_20, v57_21, v57_22, v57_23, v57_30, v57_31, v57_32, v57_33, v57_40, v57_41, v57_42, v57_43]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23, phase57_30, phase57_31, phase57_32, phase57_33, phase57_40, phase57_41, phase57_42, phase57_43]
  try simp only [star_one, star_neg]
  linear_combination ((8031501 / 160) * t ^ 3 + (-6444521 / 50) * t ^ 5 + (34857953917 / 320000) * t ^ 7 + (-970234036151 / 30720000) * t ^ 9 + (143069941 / 40960) * t ^ 11 + (-1556871491389 / 552960000) * t ^ 13 + (6693960459 / 10240000) * t ^ 15 + (263553433 / 9216000) * t ^ 17 + (348707847 / 20480000) * t ^ 19 + (-82971761 / 10240000) * t ^ 21 + (67321969 / 55296000) * t ^ 25 + (-6329 / 32) * d * t ^ 3 + (123011 / 2400) * d * t ^ 5 + (1890337541 / 3456000) * d * t ^ 7 + (-874873909 / 1843200) * d * t ^ 9 + (367756979 / 4608000) * d * t ^ 11 + (-250784707 / 18432000) * d * t ^ 13 + (104626793 / 13824000) * d * t ^ 15 + (10963099 / 55296000) * d * t ^ 17 + (13709857 / 82944000) * d * t ^ 19 + (-4178987 / 55296000) * d * t ^ 21 + (-201799 / 13271040) * d * t ^ 25 + (-85693 / 4608) * d ^ 2 * t ^ 7 + (634556239 / 18432000) * d ^ 2 * t ^ 9 + (-142305409 / 9216000) * d ^ 2 * t ^ 11 + (-14544911 / 36864000) * d ^ 2 * t ^ 13 + (506603 / 55296000) * d ^ 2 * t ^ 15 + (-19411 / 737280) * d ^ 2 * t ^ 17 + (-24301 / 884736) * d ^ 2 * t ^ 19 + (98611 / 6912000) * d ^ 2 * t ^ 21) * alpha_sq + ((-56961 / 16) * t ^ 3 + (3581933 / 640) * t ^ 5 + (-1625176021 / 1152000) * t ^ 7 + (-649030563 / 1024000) * t ^ 9 + (-25343669 / 768000) * t ^ 11 + (239463941 / 11059200) * t ^ 13 + (-117656549 / 9216000) * t ^ 15 + (19411 / 122880) * t ^ 17 + (1155769 / 11059200) * t ^ 19 + (-777013 / 9216000) * t ^ 21 + (6329 / 32) * alpha * t ^ 3 + (-123011 / 2400) * alpha * t ^ 5 + (-1360253641 / 3456000) * alpha * t ^ 7 + (2012883461 / 9216000) * alpha * t ^ 9 + (79074697 / 4608000) * alpha * t ^ 11 + (561306121 / 55296000) * alpha * t ^ 13 + (4181171 / 2764800) * alpha * t ^ 15 + (274621 / 11059200) * alpha * t ^ 17 + (29314763 / 82944000) * alpha * t ^ 19 + (852953 / 55296000) * alpha * t ^ 21 + (-4465 / 2654208) * alpha * t ^ 25) * d_sq
theorem v58_44 (t : ℂ) : (momentPoly 58 z58 4 4).eval t = (257821774 + (-917946008) * t ^ 2 + (126986868147 / 100) * t ^ 4 + (-228822114379 / 250) * t ^ 6 + (43164201267915577 / 96000000) * t ^ 8 + (-4549531654820227 / 24000000) * t ^ 10 + (1191903330613451 / 25600000) * t ^ 12 + (-1350112862654533 / 576000000) * t ^ 14 + (1033069826113453 / 768000000) * t ^ 16 + (-10501139618507 / 96000000) * t ^ 18 + (22356813781687 / 384000000) * t ^ 20 + (-19364948390717 / 576000000) * t ^ 22 + (1581432041387 / 144000000) * t ^ 24 + (-1017554259127 / 432000000) * t ^ 26 + (1633790767579 / 6912000000) * t ^ 32 + (-8659868 / 3) * d * t ^ 2 + (149071447 / 20) * d * t ^ 4 + (-432431998 / 75) * d * t ^ 6 + (17160439366949 / 19200000) * d * t ^ 8 + (616542602219 / 4800000) * d * t ^ 10 + (44596215641513 / 230400000) * d * t ^ 12 + (-357669038093 / 7680000) * d * t ^ 14 + (12701809893493 / 460800000) * d * t ^ 16 + (103137339673 / 57600000) * d * t ^ 18 + (-371363991431 / 691200000) * d * t ^ 20 + (68835712981 / 115200000) * d * t ^ 22 + (32173469 / 11520000) * d * t ^ 24 + (1354681517 / 28800000) * d * t ^ 26 + (8944877 / 11059200) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_03, v57_04, v57_10, v57_11, v57_12, v57_13, v57_14, v57_20, v57_21, v57_22, v57_23, v57_24, v57_30, v57_31, v57_32, v57_33, v57_34, v57_40, v57_41, v57_42, v57_43, v57_44]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24, phase57_30, phase57_31, phase57_32, phase57_33, phase57_34, phase57_40, phase57_41, phase57_42, phase57_43, phase57_44]
  try simp only [star_one, star_neg]
  linear_combination ((2164967 / 12) * t ^ 2 + (-657483 / 8) * t ^ 4 + (-1460637577 / 2400) * t ^ 6 + (21349527930217 / 28800000) * t ^ 8 + (-12820830875159 / 57600000) * t ^ 10 + (129537331751 / 86400000) * t ^ 12 + (-214239834389 / 17280000) * t ^ 14 + (175707848927 / 57600000) * t ^ 16 + (-627347364103 / 691200000) * t ^ 18 + (6505621787 / 10800000) * t ^ 20 + (-5995593311 / 230400000) * t ^ 22 + (50477887 / 6400000) * t ^ 26 + (-5963977 / 120) * d * t ^ 4 + (9880255 / 64) * d * t ^ 6 + (-1464850375169 / 8640000) * d * t ^ 8 + (175242147833 / 2304000) * d * t ^ 10 + (-138867444599 / 10240000) * d * t ^ 12 + (50641854349 / 15360000) * d * t ^ 14 + (-507415190219 / 552960000) * d * t ^ 16 + (-1319486651 / 69120000) * d * t ^ 18 + (2093903249 / 829440000) * d * t ^ 20 + (449249953 / 138240000) * d * t ^ 22 + (32173469 / 69120000) * d * t ^ 24 + (-2099861 / 921600) * d * t ^ 26 + (8944877 / 66355200) * d * t ^ 32 + (-12583 / 192) * d ^ 2 * t ^ 6 + (31003 / 86400) * d ^ 2 * t ^ 8 + (61936493 / 384000) * d ^ 2 * t ^ 10 + (-107629411 / 1228800) * d ^ 2 * t ^ 12 + (-110909321 / 27648000) * d ^ 2 * t ^ 14 + (-462192257 / 110592000) * d ^ 2 * t ^ 16 + (-4439597 / 9216000) * d ^ 2 * t ^ 18 + (-1419091 / 6635520) * d ^ 2 * t ^ 20 + (2857627 / 41472000) * d ^ 2 * t ^ 22 + (-1171039 / 165888000) * d ^ 2 * t ^ 24 + (9823 / 622080) * d ^ 2 * t ^ 26 + (9025 / 31850496) * d ^ 2 * t ^ 32) * alpha_sq + ((-2164967 / 12) * t ^ 2 + (17863953 / 40) * t ^ 4 + (-346441187 / 960) * t ^ 6 + (228797979541 / 1920000) * t ^ 8 + (-528913265263 / 11520000) * t ^ 10 + (5557207846361 / 276480000) * t ^ 12 + (21822576083 / 15360000) * t ^ 14 + (-60321412939 / 184320000) * t ^ 16 + (178340743 / 2764800) * t ^ 18 + (-6110700169 / 276480000) * t ^ 20 + (4726400459 / 138240000) * t ^ 22 + (1171039 / 55296000) * t ^ 24 + (10462717 / 41472000) * t ^ 26 + (-9025 / 10616832) * t ^ 32) * d_sq
#print axioms v58_00
#print axioms v58_11
#print axioms v58_22
#print axioms v58_33
#print axioms v58_44
end PhotonCertA
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z59 : Fin 59 → ℂ := Fin.snoc z58 (r ^ 3 * phiMinus)
theorem v59_00 (t : ℂ) : (momentPoly 59 z59 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00]
  try simp only [phase57_00]
  try simp only [star_one, star_neg]
  ring
theorem v59_01 (t : ℂ) : (momentPoly 59 z59 0 1).eval t = (1 * t + (-1 / 24) * d * t + (1 / 24) * alpha * t) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01]
  try simp only [phase57_00, phase57_01]
  try simp only [star_one, star_neg]
  ring
theorem v59_02 (t : ℂ) : (momentPoly 59 z59 0 2).eval t = ((1009 / 240) * t ^ 2 + (-1063 / 480) * t ^ 4 + (-1 / 12) * d * t ^ 2 + (1249 / 120) * alpha * t ^ 2 + (-413 / 40) * alpha * t ^ 4 + (-1 / 144) * alpha * d * t ^ 2 + (1 / 288) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02]
  try simp only [phase57_00, phase57_01, phase57_02]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 144) * t ^ 2) * alpha_sq + ((-1 / 144) * t ^ 2) * d_sq
theorem v59_03 (t : ℂ) : (momentPoly 59 z59 0 3).eval t = ((2157 / 320) * t ^ 3 + (-887 / 320) * t ^ 5 + (-251 / 480) * d * t ^ 3 + (191 / 480) * d * t ^ 5 + (-47 / 1152) * d * t ^ 9 + (62599 / 2400) * alpha * t ^ 3 + (-55201 / 2400) * alpha * t ^ 5 + (-81601 / 28800) * alpha * t ^ 9 + (-1259 / 960) * alpha * d * t ^ 3 + (1249 / 960) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_03]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03]
  try simp only [star_one, star_neg]
  linear_combination ((-1259 / 960) * t ^ 3 + (413 / 320) * t ^ 5 + (1 / 384) * d * t ^ 3 + (-1 / 576) * d * t ^ 5) * alpha_sq + ((-1 / 48) * t ^ 3 + (-1 / 384) * alpha * t ^ 3 + (1 / 576) * alpha * t ^ 5) * d_sq
theorem v59_04 (t : ℂ) : (momentPoly 59 z59 0 4).eval t = ((-21772543 / 24000) * t ^ 4 + (14770467 / 8000) * t ^ 6 + (-90304111 / 96000) * t ^ 8 + (779189 / 72000) * t ^ 10 + (-793313 / 576000) * t ^ 16 + (-449 / 960) * d * t ^ 4 + (-661 / 1920) * d * t ^ 6 + (413 / 640) * d * t ^ 8 + (-47 / 288) * d * t ^ 10 + (2180383 / 12000) * alpha * t ^ 4 + (-11906279 / 48000) * alpha * t ^ 6 + (215539 / 2000) * alpha * t ^ 8 + (-910177 / 18000) * alpha * t ^ 10 + (470783 / 48000) * alpha * t ^ 16 + (-31927 / 7200) * alpha * d * t ^ 4 + (19337 / 4800) * alpha * d * t ^ 6 + (-769 / 11520) * alpha * d * t ^ 8 + (18919 / 43200) * alpha * d * t ^ 10 + (95 / 13824) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_03, v58_04]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04]
  try simp only [star_one, star_neg]
  linear_combination ((-68629 / 14400) * t ^ 4 + (13143 / 3200) * t ^ 6 + (17719 / 43200) * t ^ 10 + (141 / 320) * d * t ^ 4 + (-3757 / 5760) * d * t ^ 6 + (413 / 1920) * d * t ^ 8 + (1 / 2304) * d ^ 2 * t ^ 6 + (-1 / 6912) * d ^ 2 * t ^ 8) * alpha_sq + ((-737 / 2880) * t ^ 4 + (661 / 3840) * t ^ 6 + (1 / 2304) * t ^ 8 + (-47 / 1728) * t ^ 10 + (-141 / 320) * alpha * t ^ 4 + (1259 / 2880) * alpha * t ^ 6) * d_sq
theorem v59_10 (t : ℂ) : (momentPoly 59 z59 1 0).eval t = (1 * t + (-1 / 24) * d * t + (-1 / 24) * alpha * t) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_10]
  try simp only [phase57_00, phase57_10]
  try simp only [star_one, star_neg]
  ring
theorem v59_11 (t : ℂ) : (momentPoly 59 z59 1 1).eval t = (59 + (-57) * t ^ 2 + (-1 / 12) * d * t ^ 2) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_10, v58_11]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 144) * t ^ 2) * alpha_sq + ((-1 / 144) * t ^ 2) * d_sq
theorem v59_12 (t : ℂ) : (momentPoly 59 z59 1 2).eval t = (117 * t + (-20833 / 192) * t ^ 3 + (-865 / 192) * t ^ 5 + (-39 / 8) * d * t + (4391 / 960) * d * t ^ 3 + (43 / 320) * d * t ^ 5 + (39 / 8) * alpha * t + (1781 / 320) * alpha * t ^ 3 + (-9943 / 960) * alpha * t ^ 5 + (-1259 / 2880) * alpha * d * t ^ 3 + (1249 / 2880) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_10, v58_11, v58_12]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12]
  try simp only [star_one, star_neg]
  linear_combination ((1259 / 2880) * t ^ 3 + (-413 / 960) * t ^ 5 + (-1 / 1152) * d * t ^ 3 + (1 / 1728) * d * t ^ 5) * alpha_sq + ((-1 / 48) * t ^ 3 + (-1 / 1152) * alpha * t ^ 3 + (1 / 1728) * alpha * t ^ 5) * d_sq
theorem v59_13 (t : ℂ) : (momentPoly 59 z59 1 3).eval t = ((29261 / 40) * t ^ 2 + (-5203099 / 4800) * t ^ 4 + (1144249 / 3200) * t ^ 6 + (27211 / 9600) * t ^ 10 + (-29 / 2) * d * t ^ 2 + (12751 / 960) * d * t ^ 4 + (889 / 960) * d * t ^ 6 + (-47 / 1152) * d * t ^ 10 + (36221 / 20) * alpha * t ^ 2 + (-5647339 / 1600) * alpha * t ^ 4 + (8214613 / 4800) * alpha * t ^ 6 + (215759 / 28800) * alpha * t ^ 10 + (-29 / 24) * alpha * d * t ^ 2 + (-8371 / 14400) * alpha * d * t ^ 4 + (15931 / 9600) * alpha * d * t ^ 6 + (3349 / 28800) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_03, v58_10, v58_11, v58_12, v58_13]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13]
  try simp only [star_one, star_neg]
  linear_combination ((-29 / 24) * t ^ 2 + (7403 / 7200) * t ^ 4 + (10841 / 38400) * t ^ 6 + (-17719 / 172800) * t ^ 10) * alpha_sq + ((-29 / 24) * t ^ 2 + (2929 / 2880) * t ^ 4 + (671 / 7680) * t ^ 6 + (-47 / 6912) * t ^ 10 + (-141 / 640) * alpha * t ^ 4 + (1259 / 5760) * alpha * t ^ 6) * d_sq
theorem v59_14 (t : ℂ) : (momentPoly 59 z59 1 4).eval t = ((49611 / 32) * t ^ 3 + (-193564001 / 64000) * t ^ 5 + (77282101 / 32000) * t ^ 7 + (-359830933 / 384000) * t ^ 9 + (3482927 / 288000) * t ^ 11 + (-174277 / 1152000) * t ^ 17 + (-5773 / 48) * d * t ^ 3 + (141674273 / 576000) * d * t ^ 5 + (-5259447 / 32000) * d * t ^ 7 + (34018043 / 1152000) * d * t ^ 9 + (2412101 / 288000) * d * t ^ 11 + (38033 / 384000) * d * t ^ 17 + (1439777 / 240) * alpha * t ^ 3 + (-6242670263 / 576000) * alpha * t ^ 5 + (447978151 / 96000) * alpha * t ^ 7 + (-536389853 / 1152000) * alpha * t ^ 9 + (60147503 / 96000) * alpha * t ^ 11 + (14439931 / 1152000) * alpha * t ^ 17 + (-28957 / 96) * alpha * d * t ^ 3 + (111889033 / 192000) * alpha * d * t ^ 5 + (-26341493 / 96000) * alpha * d * t ^ 7 + (-8278411 / 1152000) * alpha * d * t ^ 9 + (705809 / 864000) * alpha * d * t ^ 11 + (-1388599 / 3456000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_03, v58_04, v58_10, v58_11, v58_12, v58_13, v58_14]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14]
  try simp only [star_one, star_neg]
  linear_combination ((-28957 / 96) * t ^ 3 + (21057241 / 36000) * t ^ 5 + (-9203459 / 32000) * t ^ 7 + (901729 / 128000) * t ^ 9 + (-966383 / 288000) * t ^ 11 + (470783 / 1152000) * t ^ 17 + (115 / 192) * d * t ^ 3 + (-9 / 16) * d * t ^ 5 + (-5593 / 23040) * d * t ^ 7 + (6479 / 30720) * d * t ^ 9 + (-47 / 13824) * d * t ^ 11 + (95 / 82944) * d * t ^ 17 + (47 / 2560) * d ^ 2 * t ^ 7 + (-1249 / 69120) * d ^ 2 * t ^ 9) * alpha_sq + ((-115 / 24) * t ^ 3 + (30943 / 7680) * t ^ 5 + (2261 / 7680) * t ^ 7 + (311 / 2880) * t ^ 9 + (-47 / 864) * t ^ 11 + (-115 / 192) * alpha * t ^ 3 + (-4871 / 21600) * alpha * t ^ 5 + (86663 / 115200) * alpha * t ^ 7 + (-449 / 30720) * alpha * t ^ 9 + (24817 / 345600) * alpha * t ^ 11 + (95 / 82944) * alpha * t ^ 17) * d_sq
theorem v59_20 (t : ℂ) : (momentPoly 59 z59 2 0).eval t = ((1009 / 240) * t ^ 2 + (-1063 / 480) * t ^ 4 + (-1 / 12) * d * t ^ 2 + (-1249 / 120) * alpha * t ^ 2 + (413 / 40) * alpha * t ^ 4 + (1 / 144) * alpha * d * t ^ 2 + (-1 / 288) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_10, v58_20]
  try simp only [phase57_00, phase57_10, phase57_20]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 144) * t ^ 2) * alpha_sq + ((-1 / 144) * t ^ 2) * d_sq
theorem v59_21 (t : ℂ) : (momentPoly 59 z59 2 1).eval t = (117 * t + (-20833 / 192) * t ^ 3 + (-865 / 192) * t ^ 5 + (-39 / 8) * d * t + (4391 / 960) * d * t ^ 3 + (43 / 320) * d * t ^ 5 + (-39 / 8) * alpha * t + (-1781 / 320) * alpha * t ^ 3 + (9943 / 960) * alpha * t ^ 5 + (1259 / 2880) * alpha * d * t ^ 3 + (-1249 / 2880) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_10, v58_11, v58_20, v58_21]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21]
  try simp only [star_one, star_neg]
  linear_combination ((1259 / 2880) * t ^ 3 + (-413 / 960) * t ^ 5 + (-1 / 1152) * d * t ^ 3 + (1 / 1728) * d * t ^ 5) * alpha_sq + ((-1 / 48) * t ^ 3 + (1 / 1152) * alpha * t ^ 3 + (-1 / 1728) * alpha * t ^ 5) * d_sq
theorem v59_22 (t : ℂ) : (momentPoly 59 z59 2 2).eval t = (6903 + (-13224) * t ^ 2 + (31193939 / 4800) * t ^ 4 + (-4180801 / 9600) * t ^ 6 + (2551123 / 9600) * t ^ 8 + (-58 / 3) * d * t ^ 2 + (5717 / 320) * d * t ^ 4 + (2591 / 1920) * d * t ^ 6 + (-413 / 1920) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_10, v58_11, v58_12, v58_20, v58_21, v58_22]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22]
  try simp only [star_one, star_neg]
  linear_combination ((29 / 18) * t ^ 2 + (209 / 960) * t ^ 4 + (-5027 / 2880) * t ^ 6 + (-47 / 320) * d * t ^ 4 + (3757 / 17280) * d * t ^ 6 + (-413 / 5760) * d * t ^ 8 + (-1 / 6912) * d ^ 2 * t ^ 6 + (1 / 20736) * d ^ 2 * t ^ 8) * alpha_sq + ((-29 / 18) * t ^ 2 + (4151 / 2880) * t ^ 4 + (227 / 3840) * t ^ 6 + (-1 / 6912) * t ^ 8) * d_sq
theorem v59_23 (t : ℂ) : (momentPoly 59 z59 2 3).eval t = (20359 * t + (-2395795 / 64) * t ^ 3 + (1020278099 / 64000) * t ^ 5 + (11026199 / 19200) * t ^ 7 + (36214891 / 64000) * t ^ 9 + (-9921711 / 128000) * t ^ 11 + (33317213 / 384000) * t ^ 13 + (-20359 / 24) * d * t + (100993 / 64) * d * t ^ 3 + (-9062089 / 12800) * d * t ^ 5 + (238817 / 19200) * d * t ^ 7 + (-132763 / 3840) * d * t ^ 9 + (-87839 / 230400) * d * t ^ 11 + (23617 / 230400) * d * t ^ 13 + (20359 / 24) * alpha * t + (122889 / 64) * alpha * t ^ 3 + (-1188574193 / 192000) * alpha * t ^ 5 + (12910423 / 3840) * alpha * t ^ 7 + (544163 / 12000) * alpha * t ^ 9 + (9953611 / 1152000) * alpha * t ^ 11 + (7273999 / 1152000) * alpha * t ^ 13 + (-28957 / 192) * alpha * d * t ^ 3 + (34003909 / 115200) * alpha * d * t ^ 5 + (-8275793 / 57600) * alpha * d * t ^ 7 + (-493 / 7680) * alpha * d * t ^ 9 + (-5289 / 25600) * alpha * d * t ^ 11 + (-19411 / 46080) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_03, v58_10, v58_11, v58_12, v58_13, v58_20, v58_21, v58_22, v58_23]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23]
  try simp only [star_one, star_neg]
  linear_combination ((28957 / 192) * t ^ 3 + (-2040229 / 7200) * t ^ 5 + (845527 / 6400) * t ^ 7 + (1338853 / 691200) * t ^ 11 + (-59059 / 46080) * t ^ 13 + (-115 / 384) * d * t ^ 3 + (7279 / 86400) * d * t ^ 5 + (138203 / 345600) * d * t ^ 7 + (-89699 / 460800) * d * t ^ 9 + (22417 / 1382400) * d * t ^ 11 + (-17719 / 2073600) * d * t ^ 13 + (-47 / 2560) * d ^ 2 * t ^ 7 + (1249 / 69120) * d ^ 2 * t ^ 9) * alpha_sq + ((-115 / 16) * t ^ 3 + (15899 / 2560) * t ^ 5 + (5249 / 7680) * t ^ 7 + (-311 / 2880) * t ^ 9 + (-47 / 3456) * t ^ 11 + (-115 / 384) * alpha * t ^ 3 + (7279 / 86400) * alpha * t ^ 5 + (66211 / 345600) * alpha * t ^ 7 + (-1 / 18432) * alpha * t ^ 9 + (27167 / 1382400) * alpha * t ^ 11 + (-47 / 82944) * alpha * t ^ 13) * d_sq
theorem v59_24 (t : ℂ) : (momentPoly 59 z59 2 4).eval t = ((5048027 / 30) * t ^ 2 + (-325782449 / 800) * t ^ 4 + (597763736089 / 1920000) * t ^ 6 + (-271129577429 / 3840000) * t ^ 8 + (-5863421 / 384000) * t ^ 10 + (-24837388319 / 7680000) * t ^ 12 + (2912171359 / 1920000) * t ^ 14 + (6790183897 / 23040000) * t ^ 18 + (-3438679141 / 11520000) * t ^ 20 + (-10006 / 3) * d * t ^ 2 + (242269 / 40) * d * t ^ 4 + (-2645081491 / 1152000) * d * t ^ 6 + (-305241431 / 768000) * d * t ^ 8 + (-9041351 / 192000) * d * t ^ 10 + (143014313 / 4608000) * d * t ^ 12 + (-15245537 / 1152000) * d * t ^ 14 + (105789 / 512000) * d * t ^ 18 + (-127523 / 1152000) * d * t ^ 20 + (6248747 / 15) * alpha * t ^ 2 + (-30089106 / 25) * alpha * t ^ 4 + (6650959280033 / 5760000) * alpha * t ^ 6 + (-1436086147591 / 3840000) * alpha * t ^ 8 + (6148137029 / 384000) * alpha * t ^ 10 + (-227982822943 / 23040000) * alpha * t ^ 12 + (878077223 / 5760000) * alpha * t ^ 14 + (309182641 / 7680000) * alpha * t ^ 18 + (-98365433 / 3840000) * alpha * t ^ 20 + (-5003 / 18) * alpha * d * t ^ 2 + (-963821 / 2400) * alpha * d * t ^ 4 + (1745364643 / 1152000) * alpha * d * t ^ 6 + (-1821358459 / 2304000) * alpha * d * t ^ 8 + (844973 / 576000) * alpha * d * t ^ 10 + (-585653419 / 13824000) * alpha * d * t ^ 12 + (-10816501 / 3456000) * alpha * d * t ^ 14 + (-949777 / 921600) * alpha * d * t ^ 18 + (-5341 / 384000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_03, v58_04, v58_10, v58_11, v58_12, v58_13, v58_14, v58_20, v58_21, v58_22, v58_23, v58_24]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24]
  try simp only [star_one, star_neg]
  linear_combination ((-5003 / 18) * t ^ 2 + (140657 / 300) * t ^ 4 + (-34176077 / 1152000) * t ^ 6 + (-38813723 / 230400) * t ^ 8 + (-26261987 / 768000) * t ^ 10 + (82232791 / 1728000) * t ^ 12 + (-2888839 / 432000) * t ^ 14 + (1388803 / 1382400) * t ^ 18 + (-7444841 / 3456000) * d * t ^ 6 + (3446237 / 691200) * d * t ^ 8 + (-8177771 / 2304000) * d * t ^ 10 + (967501 / 2764800) * d * t ^ 12 + (4118521 / 10368000) * d * t ^ 14 + (212927 / 41472000) * d * t ^ 18 + (-127523 / 3456000) * d * t ^ 20 + (-17021 / 518400) * d ^ 2 * t ^ 8 + (20647 / 691200) * d ^ 2 * t ^ 10 + (-671 / 1105920) * d ^ 2 * t ^ 12 + (11821 / 4147200) * d ^ 2 * t ^ 14 + (-95 / 663552) * d ^ 2 * t ^ 18 + (95 / 995328) * d ^ 2 * t ^ 20) * alpha_sq + ((-5003 / 18) * t ^ 2 + (55651 / 120) * t ^ 4 + (-176287169 / 1152000) * t ^ 6 + (-97960601 / 3456000) * t ^ 8 + (-20215739 / 2304000) * t ^ 10 + (67617701 / 27648000) * t ^ 12 + (44681 / 460800) * t ^ 14 + (72919 / 3072000) * t ^ 18 + (-95 / 331776) * t ^ 20 + (-8037 / 80) * alpha * t ^ 4 + (73623271 / 384000) * alpha * t ^ 6 + (-618129611 / 6912000) * alpha * t ^ 8 + (-4002737 / 2304000) * alpha * t ^ 10 + (1488377 / 6912000) * alpha * t ^ 12 + (-58703 / 207360) * alpha * t ^ 14 + (-1364849 / 20736000) * alpha * t ^ 18) * d_sq
theorem v59_30 (t : ℂ) : (momentPoly 59 z59 3 0).eval t = ((2157 / 320) * t ^ 3 + (-887 / 320) * t ^ 5 + (-251 / 480) * d * t ^ 3 + (191 / 480) * d * t ^ 5 + (-47 / 1152) * d * t ^ 9 + (-62599 / 2400) * alpha * t ^ 3 + (55201 / 2400) * alpha * t ^ 5 + (81601 / 28800) * alpha * t ^ 9 + (1259 / 960) * alpha * d * t ^ 3 + (-1249 / 960) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_10, v58_20, v58_30]
  try simp only [phase57_00, phase57_10, phase57_20, phase57_30]
  try simp only [star_one, star_neg]
  linear_combination ((-1259 / 960) * t ^ 3 + (413 / 320) * t ^ 5 + (1 / 384) * d * t ^ 3 + (-1 / 576) * d * t ^ 5) * alpha_sq + ((-1 / 48) * t ^ 3 + (1 / 384) * alpha * t ^ 3 + (-1 / 576) * alpha * t ^ 5) * d_sq
theorem v59_31 (t : ℂ) : (momentPoly 59 z59 3 1).eval t = ((29261 / 40) * t ^ 2 + (-5203099 / 4800) * t ^ 4 + (1144249 / 3200) * t ^ 6 + (27211 / 9600) * t ^ 10 + (-29 / 2) * d * t ^ 2 + (12751 / 960) * d * t ^ 4 + (889 / 960) * d * t ^ 6 + (-47 / 1152) * d * t ^ 10 + (-36221 / 20) * alpha * t ^ 2 + (5647339 / 1600) * alpha * t ^ 4 + (-8214613 / 4800) * alpha * t ^ 6 + (-215759 / 28800) * alpha * t ^ 10 + (29 / 24) * alpha * d * t ^ 2 + (8371 / 14400) * alpha * d * t ^ 4 + (-15931 / 9600) * alpha * d * t ^ 6 + (-3349 / 28800) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_10, v58_11, v58_20, v58_21, v58_30, v58_31]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21, phase57_30, phase57_31]
  try simp only [star_one, star_neg]
  linear_combination ((-29 / 24) * t ^ 2 + (7403 / 7200) * t ^ 4 + (10841 / 38400) * t ^ 6 + (-17719 / 172800) * t ^ 10) * alpha_sq + ((-29 / 24) * t ^ 2 + (2929 / 2880) * t ^ 4 + (671 / 7680) * t ^ 6 + (-47 / 6912) * t ^ 10 + (141 / 640) * alpha * t ^ 4 + (-1259 / 5760) * alpha * t ^ 6) * d_sq
theorem v59_32 (t : ℂ) : (momentPoly 59 z59 3 2).eval t = (20359 * t + (-2395795 / 64) * t ^ 3 + (1020278099 / 64000) * t ^ 5 + (11026199 / 19200) * t ^ 7 + (36214891 / 64000) * t ^ 9 + (-9921711 / 128000) * t ^ 11 + (33317213 / 384000) * t ^ 13 + (-20359 / 24) * d * t + (100993 / 64) * d * t ^ 3 + (-9062089 / 12800) * d * t ^ 5 + (238817 / 19200) * d * t ^ 7 + (-132763 / 3840) * d * t ^ 9 + (-87839 / 230400) * d * t ^ 11 + (23617 / 230400) * d * t ^ 13 + (-20359 / 24) * alpha * t + (-122889 / 64) * alpha * t ^ 3 + (1188574193 / 192000) * alpha * t ^ 5 + (-12910423 / 3840) * alpha * t ^ 7 + (-544163 / 12000) * alpha * t ^ 9 + (-9953611 / 1152000) * alpha * t ^ 11 + (-7273999 / 1152000) * alpha * t ^ 13 + (28957 / 192) * alpha * d * t ^ 3 + (-34003909 / 115200) * alpha * d * t ^ 5 + (8275793 / 57600) * alpha * d * t ^ 7 + (493 / 7680) * alpha * d * t ^ 9 + (5289 / 25600) * alpha * d * t ^ 11 + (19411 / 46080) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_10, v58_11, v58_12, v58_20, v58_21, v58_22, v58_30, v58_31, v58_32]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22, phase57_30, phase57_31, phase57_32]
  try simp only [star_one, star_neg]
  linear_combination ((28957 / 192) * t ^ 3 + (-2040229 / 7200) * t ^ 5 + (845527 / 6400) * t ^ 7 + (1338853 / 691200) * t ^ 11 + (-59059 / 46080) * t ^ 13 + (-115 / 384) * d * t ^ 3 + (7279 / 86400) * d * t ^ 5 + (138203 / 345600) * d * t ^ 7 + (-89699 / 460800) * d * t ^ 9 + (22417 / 1382400) * d * t ^ 11 + (-17719 / 2073600) * d * t ^ 13 + (-47 / 2560) * d ^ 2 * t ^ 7 + (1249 / 69120) * d ^ 2 * t ^ 9) * alpha_sq + ((-115 / 16) * t ^ 3 + (15899 / 2560) * t ^ 5 + (5249 / 7680) * t ^ 7 + (-311 / 2880) * t ^ 9 + (-47 / 3456) * t ^ 11 + (115 / 384) * alpha * t ^ 3 + (-7279 / 86400) * alpha * t ^ 5 + (-66211 / 345600) * alpha * t ^ 7 + (1 / 18432) * alpha * t ^ 9 + (-27167 / 1382400) * alpha * t ^ 11 + (47 / 82944) * alpha * t ^ 13) * d_sq
theorem v59_33 (t : ℂ) : (momentPoly 59 z59 3 3).eval t = (1201181 + (-3422052) * t ^ 2 + (5334163569 / 1600) * t ^ 4 + (-213076062677 / 160000) * t ^ 6 + (55625185171 / 160000) * t ^ 8 + (-20616783777 / 160000) * t ^ 10 + (426016499 / 480000) * t ^ 12 + (-563228593 / 640000) * t ^ 14 + (-65207621 / 1920000) * t ^ 18 + (-5003) * d * t ^ 2 + (2932821 / 320) * d * t ^ 4 + (-171429247 / 48000) * d * t ^ 6 + (-21100807 / 38400) * d * t ^ 8 + (-2563189 / 64000) * d * t ^ 10 + (318539 / 18000) * d * t ^ 12 + (-1929713 / 96000) * d * t ^ 14) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_03, v58_10, v58_11, v58_12, v58_13, v58_20, v58_21, v58_22, v58_23, v58_30, v58_31, v58_32, v58_33]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23, phase57_30, phase57_31, phase57_32, phase57_33]
  try simp only [star_one, star_neg]
  linear_combination ((5003 / 12) * t ^ 2 + (35739 / 320) * t ^ 4 + (-31901239 / 24000) * t ^ 6 + (120105157 / 153600) * t ^ 8 + (4652401 / 256000) * t ^ 10 + (22683857 / 3456000) * t ^ 12 + (-17913361 / 4608000) * t ^ 14 + (-5578859 / 8294400) * t ^ 18 + (-24111 / 320) * d * t ^ 4 + (21013517 / 115200) * d * t ^ 6 + (-21486017 / 153600) * d * t ^ 8 + (5066167 / 153600) * d * t ^ 10 + (-175823 / 230400) * d * t ^ 12 + (205301 / 345600) * d * t ^ 14 + (-43 / 576) * d ^ 2 * t ^ 6 + (-1421 / 345600) * d ^ 2 * t ^ 8 + (16531 / 230400) * d ^ 2 * t ^ 10 + (361 / 76800) * d ^ 2 * t ^ 14) * alpha_sq + ((-5003 / 12) * t ^ 2 + (236607 / 320) * t ^ 4 + (-1977263 / 6400) * t ^ 6 + (1390469 / 460800) * t ^ 8 + (-2769197 / 153600) * t ^ 10 + (-294109 / 691200) * t ^ 12 + (131693 / 921600) * t ^ 14 + (-2209 / 331776) * t ^ 18) * d_sq
theorem v59_34 (t : ℂ) : (momentPoly 59 z59 3 4).eval t = (4683269 * t + (-102435861 / 8) * t ^ 3 + (362581318061 / 32000) * t ^ 5 + (-42824270228129 / 12800000) * t ^ 7 + (6437562202929 / 12800000) * t ^ 9 + (-31903139255789 / 76800000) * t ^ 11 + (75531737231 / 720000) * t ^ 13 + (-705459663147 / 12800000) * t ^ 15 + (-138870771637 / 153600000) * t ^ 17 + (191185435493 / 230400000) * t ^ 19 + (-23151382417 / 25600000) * t ^ 21 + (-38877163583 / 460800000) * t ^ 25 + (-4683269 / 24) * d * t + (21590547 / 40) * d * t ^ 3 + (-3171710991 / 6400) * d * t ^ 5 + (1342856770579 / 7680000) * d * t ^ 7 + (-118926199229 / 2560000) * d * t ^ 9 + (113305319199 / 5120000) * d * t ^ 11 + (12829288207 / 23040000) * d * t ^ 13 + (-1353867421 / 7680000) * d * t ^ 15 + (702979931 / 18432000) * d * t ^ 17 + (-4298435257 / 138240000) * d * t ^ 19 + (421043377 / 11520000) * d * t ^ 21 + (2181103 / 55296000) * d * t ^ 25 + (4683269 / 24) * alpha * t + (26271531 / 40) * alpha * t ^ 3 + (-95900069109 / 32000) * alpha * t ^ 5 + (122845257181223 / 38400000) * alpha * t ^ 7 + (-39619011679783 / 38400000) * alpha * t ^ 9 + (-351441394519 / 76800000) * alpha * t ^ 11 + (-372930044233 / 23040000) * alpha * t ^ 13 + (36763817759 / 38400000) * alpha * t ^ 15 + (-1198796025181 / 460800000) * alpha * t ^ 17 + (41165612539 / 691200000) * alpha * t ^ 19 + (-5203404569 / 115200000) * alpha * t ^ 21 + (-5674281749 / 1382400000) * alpha * t ^ 25 + (-2063501 / 40) * alpha * d * t ^ 3 + (959163099 / 6400) * alpha * d * t ^ 5 + (-3331006756849 / 23040000) * alpha * d * t ^ 7 + (361668967679 / 7680000) * alpha * d * t ^ 9 + (-3254100967 / 1843200) * alpha * d * t ^ 11 + (24381408389 / 34560000) * alpha * d * t ^ 13 + (6077161561 / 23040000) * alpha * d * t ^ 15 + (-95303051 / 18432000) * alpha * d * t ^ 17 + (-45823229 / 15360000) * alpha * d * t ^ 19 + (259813007 / 46080000) * alpha * d * t ^ 21 + (-22126801 / 55296000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_03, v58_04, v58_10, v58_11, v58_12, v58_13, v58_14, v58_20, v58_21, v58_22, v58_23, v58_24, v58_30, v58_31, v58_32, v58_33, v58_34]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24, phase57_30, phase57_31, phase57_32, phase57_33, phase57_34]
  try simp only [star_one, star_neg]
  linear_combination ((2063501 / 40) * t ^ 3 + (-682876853 / 4800) * t ^ 5 + (1998149205401 / 15360000) * t ^ 7 + (-206842602091 / 5120000) * t ^ 9 + (28722312871 / 9216000) * t ^ 11 + (-100609393969 / 34560000) * t ^ 13 + (1956744381 / 2560000) * t ^ 15 + (128947247 / 6144000) * t ^ 17 + (888416087 / 103680000) * t ^ 19 + (-86820179 / 15360000) * t ^ 21 + (67321969 / 55296000) * t ^ 25 + (-1639 / 16) * d * t ^ 3 + (-71599 / 7200) * d * t ^ 5 + (2354776487 / 5529600) * d * t ^ 7 + (-126750097 / 307200) * d * t ^ 9 + (318983263 / 3072000) * d * t ^ 11 + (-419888507 / 33177600) * d * t ^ 13 + (7864023 / 1024000) * d * t ^ 15 + (2017547 / 12288000) * d * t ^ 17 + (968549 / 6144000) * d * t ^ 19 + (-5321297 / 110592000) * d * t ^ 21 + (-336661 / 19906560) * d * t ^ 25 + (-16027 / 1280) * d ^ 2 * t ^ 7 + (24402157 / 1024000) * d ^ 2 * t ^ 9 + (-306647893 / 27648000) * d ^ 2 * t ^ 11 + (-425393 / 2048000) * d ^ 2 * t ^ 13 + (200701 / 27648000) * d ^ 2 * t ^ 15 + (-19411 / 1105920) * d ^ 2 * t ^ 17 + (-893 / 49152) * d ^ 2 * t ^ 19 + (98611 / 10368000) * d ^ 2 * t ^ 21) * alpha_sq + ((-4917 / 2) * t ^ 3 + (5389761 / 1280) * t ^ 5 + (-12511321601 / 9216000) * t ^ 7 + (-41225639 / 102400) * t ^ 9 + (-20659003 / 3072000) * t ^ 11 + (923316389 / 55296000) * t ^ 13 + (-9354749 / 1024000) * t ^ 15 + (19411 / 184320) * t ^ 17 + (12339487 / 165888000) * t ^ 19 + (-777013 / 13824000) * t ^ 21 + (-1639 / 16) * alpha * t ^ 3 + (-71599 / 7200) * alpha * t ^ 5 + (1569199783 / 5529600) * alpha * t ^ 7 + (-715817273 / 4608000) * alpha * t ^ 9 + (-21887041 / 3072000) * alpha * t ^ 11 + (-3464677 / 442368) * alpha * t ^ 13 + (-5022887 / 5529600) * alpha * t ^ 15 + (-96851 / 7372800) * alpha * t ^ 17 + (-13579379 / 55296000) * alpha * t ^ 19 + (-949229 / 110592000) * alpha * t ^ 21 + (4465 / 3981312) * alpha * t ^ 25) * d_sq
theorem v59_40 (t : ℂ) : (momentPoly 59 z59 4 0).eval t = ((-21772543 / 24000) * t ^ 4 + (14770467 / 8000) * t ^ 6 + (-90304111 / 96000) * t ^ 8 + (779189 / 72000) * t ^ 10 + (-793313 / 576000) * t ^ 16 + (-449 / 960) * d * t ^ 4 + (-661 / 1920) * d * t ^ 6 + (413 / 640) * d * t ^ 8 + (-47 / 288) * d * t ^ 10 + (-2180383 / 12000) * alpha * t ^ 4 + (11906279 / 48000) * alpha * t ^ 6 + (-215539 / 2000) * alpha * t ^ 8 + (910177 / 18000) * alpha * t ^ 10 + (-470783 / 48000) * alpha * t ^ 16 + (31927 / 7200) * alpha * d * t ^ 4 + (-19337 / 4800) * alpha * d * t ^ 6 + (769 / 11520) * alpha * d * t ^ 8 + (-18919 / 43200) * alpha * d * t ^ 10 + (-95 / 13824) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_10, v58_20, v58_30, v58_40]
  try simp only [phase57_00, phase57_10, phase57_20, phase57_30, phase57_40]
  try simp only [star_one, star_neg]
  linear_combination ((-68629 / 14400) * t ^ 4 + (13143 / 3200) * t ^ 6 + (17719 / 43200) * t ^ 10 + (141 / 320) * d * t ^ 4 + (-3757 / 5760) * d * t ^ 6 + (413 / 1920) * d * t ^ 8 + (1 / 2304) * d ^ 2 * t ^ 6 + (-1 / 6912) * d ^ 2 * t ^ 8) * alpha_sq + ((-737 / 2880) * t ^ 4 + (661 / 3840) * t ^ 6 + (1 / 2304) * t ^ 8 + (-47 / 1728) * t ^ 10 + (141 / 320) * alpha * t ^ 4 + (-1259 / 2880) * alpha * t ^ 6) * d_sq
theorem v59_41 (t : ℂ) : (momentPoly 59 z59 4 1).eval t = ((49611 / 32) * t ^ 3 + (-193564001 / 64000) * t ^ 5 + (77282101 / 32000) * t ^ 7 + (-359830933 / 384000) * t ^ 9 + (3482927 / 288000) * t ^ 11 + (-174277 / 1152000) * t ^ 17 + (-5773 / 48) * d * t ^ 3 + (141674273 / 576000) * d * t ^ 5 + (-5259447 / 32000) * d * t ^ 7 + (34018043 / 1152000) * d * t ^ 9 + (2412101 / 288000) * d * t ^ 11 + (38033 / 384000) * d * t ^ 17 + (-1439777 / 240) * alpha * t ^ 3 + (6242670263 / 576000) * alpha * t ^ 5 + (-447978151 / 96000) * alpha * t ^ 7 + (536389853 / 1152000) * alpha * t ^ 9 + (-60147503 / 96000) * alpha * t ^ 11 + (-14439931 / 1152000) * alpha * t ^ 17 + (28957 / 96) * alpha * d * t ^ 3 + (-111889033 / 192000) * alpha * d * t ^ 5 + (26341493 / 96000) * alpha * d * t ^ 7 + (8278411 / 1152000) * alpha * d * t ^ 9 + (-705809 / 864000) * alpha * d * t ^ 11 + (1388599 / 3456000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_10, v58_11, v58_20, v58_21, v58_30, v58_31, v58_40, v58_41]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21, phase57_30, phase57_31, phase57_40, phase57_41]
  try simp only [star_one, star_neg]
  linear_combination ((-28957 / 96) * t ^ 3 + (21057241 / 36000) * t ^ 5 + (-9203459 / 32000) * t ^ 7 + (901729 / 128000) * t ^ 9 + (-966383 / 288000) * t ^ 11 + (470783 / 1152000) * t ^ 17 + (115 / 192) * d * t ^ 3 + (-9 / 16) * d * t ^ 5 + (-5593 / 23040) * d * t ^ 7 + (6479 / 30720) * d * t ^ 9 + (-47 / 13824) * d * t ^ 11 + (95 / 82944) * d * t ^ 17 + (47 / 2560) * d ^ 2 * t ^ 7 + (-1249 / 69120) * d ^ 2 * t ^ 9) * alpha_sq + ((-115 / 24) * t ^ 3 + (30943 / 7680) * t ^ 5 + (2261 / 7680) * t ^ 7 + (311 / 2880) * t ^ 9 + (-47 / 864) * t ^ 11 + (115 / 192) * alpha * t ^ 3 + (4871 / 21600) * alpha * t ^ 5 + (-86663 / 115200) * alpha * t ^ 7 + (449 / 30720) * alpha * t ^ 9 + (-24817 / 345600) * alpha * t ^ 11 + (-95 / 82944) * alpha * t ^ 17) * d_sq
theorem v59_42 (t : ℂ) : (momentPoly 59 z59 4 2).eval t = ((5048027 / 30) * t ^ 2 + (-325782449 / 800) * t ^ 4 + (597763736089 / 1920000) * t ^ 6 + (-271129577429 / 3840000) * t ^ 8 + (-5863421 / 384000) * t ^ 10 + (-24837388319 / 7680000) * t ^ 12 + (2912171359 / 1920000) * t ^ 14 + (6790183897 / 23040000) * t ^ 18 + (-3438679141 / 11520000) * t ^ 20 + (-10006 / 3) * d * t ^ 2 + (242269 / 40) * d * t ^ 4 + (-2645081491 / 1152000) * d * t ^ 6 + (-305241431 / 768000) * d * t ^ 8 + (-9041351 / 192000) * d * t ^ 10 + (143014313 / 4608000) * d * t ^ 12 + (-15245537 / 1152000) * d * t ^ 14 + (105789 / 512000) * d * t ^ 18 + (-127523 / 1152000) * d * t ^ 20 + (-6248747 / 15) * alpha * t ^ 2 + (30089106 / 25) * alpha * t ^ 4 + (-6650959280033 / 5760000) * alpha * t ^ 6 + (1436086147591 / 3840000) * alpha * t ^ 8 + (-6148137029 / 384000) * alpha * t ^ 10 + (227982822943 / 23040000) * alpha * t ^ 12 + (-878077223 / 5760000) * alpha * t ^ 14 + (-309182641 / 7680000) * alpha * t ^ 18 + (98365433 / 3840000) * alpha * t ^ 20 + (5003 / 18) * alpha * d * t ^ 2 + (963821 / 2400) * alpha * d * t ^ 4 + (-1745364643 / 1152000) * alpha * d * t ^ 6 + (1821358459 / 2304000) * alpha * d * t ^ 8 + (-844973 / 576000) * alpha * d * t ^ 10 + (585653419 / 13824000) * alpha * d * t ^ 12 + (10816501 / 3456000) * alpha * d * t ^ 14 + (949777 / 921600) * alpha * d * t ^ 18 + (5341 / 384000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_10, v58_11, v58_12, v58_20, v58_21, v58_22, v58_30, v58_31, v58_32, v58_40, v58_41, v58_42]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22, phase57_30, phase57_31, phase57_32, phase57_40, phase57_41, phase57_42]
  try simp only [star_one, star_neg]
  linear_combination ((-5003 / 18) * t ^ 2 + (140657 / 300) * t ^ 4 + (-34176077 / 1152000) * t ^ 6 + (-38813723 / 230400) * t ^ 8 + (-26261987 / 768000) * t ^ 10 + (82232791 / 1728000) * t ^ 12 + (-2888839 / 432000) * t ^ 14 + (1388803 / 1382400) * t ^ 18 + (-7444841 / 3456000) * d * t ^ 6 + (3446237 / 691200) * d * t ^ 8 + (-8177771 / 2304000) * d * t ^ 10 + (967501 / 2764800) * d * t ^ 12 + (4118521 / 10368000) * d * t ^ 14 + (212927 / 41472000) * d * t ^ 18 + (-127523 / 3456000) * d * t ^ 20 + (-17021 / 518400) * d ^ 2 * t ^ 8 + (20647 / 691200) * d ^ 2 * t ^ 10 + (-671 / 1105920) * d ^ 2 * t ^ 12 + (11821 / 4147200) * d ^ 2 * t ^ 14 + (-95 / 663552) * d ^ 2 * t ^ 18 + (95 / 995328) * d ^ 2 * t ^ 20) * alpha_sq + ((-5003 / 18) * t ^ 2 + (55651 / 120) * t ^ 4 + (-176287169 / 1152000) * t ^ 6 + (-97960601 / 3456000) * t ^ 8 + (-20215739 / 2304000) * t ^ 10 + (67617701 / 27648000) * t ^ 12 + (44681 / 460800) * t ^ 14 + (72919 / 3072000) * t ^ 18 + (-95 / 331776) * t ^ 20 + (8037 / 80) * alpha * t ^ 4 + (-73623271 / 384000) * alpha * t ^ 6 + (618129611 / 6912000) * alpha * t ^ 8 + (4002737 / 2304000) * alpha * t ^ 10 + (-1488377 / 6912000) * alpha * t ^ 12 + (58703 / 207360) * alpha * t ^ 14 + (1364849 / 20736000) * alpha * t ^ 18) * d_sq
theorem v59_43 (t : ℂ) : (momentPoly 59 z59 4 3).eval t = (4683269 * t + (-102435861 / 8) * t ^ 3 + (362581318061 / 32000) * t ^ 5 + (-42824270228129 / 12800000) * t ^ 7 + (6437562202929 / 12800000) * t ^ 9 + (-31903139255789 / 76800000) * t ^ 11 + (75531737231 / 720000) * t ^ 13 + (-705459663147 / 12800000) * t ^ 15 + (-138870771637 / 153600000) * t ^ 17 + (191185435493 / 230400000) * t ^ 19 + (-23151382417 / 25600000) * t ^ 21 + (-38877163583 / 460800000) * t ^ 25 + (-4683269 / 24) * d * t + (21590547 / 40) * d * t ^ 3 + (-3171710991 / 6400) * d * t ^ 5 + (1342856770579 / 7680000) * d * t ^ 7 + (-118926199229 / 2560000) * d * t ^ 9 + (113305319199 / 5120000) * d * t ^ 11 + (12829288207 / 23040000) * d * t ^ 13 + (-1353867421 / 7680000) * d * t ^ 15 + (702979931 / 18432000) * d * t ^ 17 + (-4298435257 / 138240000) * d * t ^ 19 + (421043377 / 11520000) * d * t ^ 21 + (2181103 / 55296000) * d * t ^ 25 + (-4683269 / 24) * alpha * t + (-26271531 / 40) * alpha * t ^ 3 + (95900069109 / 32000) * alpha * t ^ 5 + (-122845257181223 / 38400000) * alpha * t ^ 7 + (39619011679783 / 38400000) * alpha * t ^ 9 + (351441394519 / 76800000) * alpha * t ^ 11 + (372930044233 / 23040000) * alpha * t ^ 13 + (-36763817759 / 38400000) * alpha * t ^ 15 + (1198796025181 / 460800000) * alpha * t ^ 17 + (-41165612539 / 691200000) * alpha * t ^ 19 + (5203404569 / 115200000) * alpha * t ^ 21 + (5674281749 / 1382400000) * alpha * t ^ 25 + (2063501 / 40) * alpha * d * t ^ 3 + (-959163099 / 6400) * alpha * d * t ^ 5 + (3331006756849 / 23040000) * alpha * d * t ^ 7 + (-361668967679 / 7680000) * alpha * d * t ^ 9 + (3254100967 / 1843200) * alpha * d * t ^ 11 + (-24381408389 / 34560000) * alpha * d * t ^ 13 + (-6077161561 / 23040000) * alpha * d * t ^ 15 + (95303051 / 18432000) * alpha * d * t ^ 17 + (45823229 / 15360000) * alpha * d * t ^ 19 + (-259813007 / 46080000) * alpha * d * t ^ 21 + (22126801 / 55296000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_03, v58_10, v58_11, v58_12, v58_13, v58_20, v58_21, v58_22, v58_23, v58_30, v58_31, v58_32, v58_33, v58_40, v58_41, v58_42, v58_43]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23, phase57_30, phase57_31, phase57_32, phase57_33, phase57_40, phase57_41, phase57_42, phase57_43]
  try simp only [star_one, star_neg]
  linear_combination ((2063501 / 40) * t ^ 3 + (-682876853 / 4800) * t ^ 5 + (1998149205401 / 15360000) * t ^ 7 + (-206842602091 / 5120000) * t ^ 9 + (28722312871 / 9216000) * t ^ 11 + (-100609393969 / 34560000) * t ^ 13 + (1956744381 / 2560000) * t ^ 15 + (128947247 / 6144000) * t ^ 17 + (888416087 / 103680000) * t ^ 19 + (-86820179 / 15360000) * t ^ 21 + (67321969 / 55296000) * t ^ 25 + (-1639 / 16) * d * t ^ 3 + (-71599 / 7200) * d * t ^ 5 + (2354776487 / 5529600) * d * t ^ 7 + (-126750097 / 307200) * d * t ^ 9 + (318983263 / 3072000) * d * t ^ 11 + (-419888507 / 33177600) * d * t ^ 13 + (7864023 / 1024000) * d * t ^ 15 + (2017547 / 12288000) * d * t ^ 17 + (968549 / 6144000) * d * t ^ 19 + (-5321297 / 110592000) * d * t ^ 21 + (-336661 / 19906560) * d * t ^ 25 + (-16027 / 1280) * d ^ 2 * t ^ 7 + (24402157 / 1024000) * d ^ 2 * t ^ 9 + (-306647893 / 27648000) * d ^ 2 * t ^ 11 + (-425393 / 2048000) * d ^ 2 * t ^ 13 + (200701 / 27648000) * d ^ 2 * t ^ 15 + (-19411 / 1105920) * d ^ 2 * t ^ 17 + (-893 / 49152) * d ^ 2 * t ^ 19 + (98611 / 10368000) * d ^ 2 * t ^ 21) * alpha_sq + ((-4917 / 2) * t ^ 3 + (5389761 / 1280) * t ^ 5 + (-12511321601 / 9216000) * t ^ 7 + (-41225639 / 102400) * t ^ 9 + (-20659003 / 3072000) * t ^ 11 + (923316389 / 55296000) * t ^ 13 + (-9354749 / 1024000) * t ^ 15 + (19411 / 184320) * t ^ 17 + (12339487 / 165888000) * t ^ 19 + (-777013 / 13824000) * t ^ 21 + (1639 / 16) * alpha * t ^ 3 + (71599 / 7200) * alpha * t ^ 5 + (-1569199783 / 5529600) * alpha * t ^ 7 + (715817273 / 4608000) * alpha * t ^ 9 + (21887041 / 3072000) * alpha * t ^ 11 + (3464677 / 442368) * alpha * t ^ 13 + (5022887 / 5529600) * alpha * t ^ 15 + (96851 / 7372800) * alpha * t ^ 17 + (13579379 / 55296000) * alpha * t ^ 19 + (949229 / 110592000) * alpha * t ^ 21 + (-4465 / 3981312) * alpha * t ^ 25) * d_sq
theorem v59_44 (t : ℂ) : (momentPoly 59 z59 4 4).eval t = (276312871 + (-1040566920) * t ^ 2 + (602885259053 / 400) * t ^ 4 + (-43762607610923 / 40000) * t ^ 6 + (16020606456766419 / 32000000) * t ^ 8 + (-38889659551732501 / 192000000) * t ^ 10 + (1375322999935189 / 25600000) * t ^ 12 + (-2103604352777291 / 1152000000) * t ^ 14 + (2632996934708369 / 2304000000) * t ^ 16 + (-18516826639511 / 288000000) * t ^ 18 + (320139928600201 / 6912000000) * t ^ 20 + (-484361048767 / 36000000) * t ^ 22 + (8820710739253 / 1536000000) * t ^ 24 + (-290231090503 / 128000000) * t ^ 26 + (3201188374783 / 13824000000) * t ^ 32 + (-4563890 / 3) * d * t ^ 2 + (331477377 / 80) * d * t ^ 4 + (-84174742081 / 24000) * d * t ^ 6 + (43399410170071 / 57600000) * d * t ^ 8 + (1962173648881 / 38400000) * d * t ^ 10 + (21458313412319 / 230400000) * d * t ^ 12 + (-1328254578941 / 46080000) * d * t ^ 14 + (7107363410339 / 460800000) * d * t ^ 16 + (14531414333 / 19200000) * d * t ^ 18 + (-376990851121 / 1382400000) * d * t ^ 20 + (17285737649 / 57600000) * d * t ^ 22 + (81040559 / 61440000) * d * t ^ 24 + (17143887829 / 691200000) * d * t ^ 26 + (8944877 / 22118400) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_03, v58_04, v58_10, v58_11, v58_12, v58_13, v58_14, v58_20, v58_21, v58_22, v58_23, v58_24, v58_30, v58_31, v58_32, v58_33, v58_34, v58_40, v58_41, v58_42, v58_43, v58_44]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24, phase57_30, phase57_31, phase57_32, phase57_33, phase57_34, phase57_40, phase57_41, phase57_42, phase57_43, phase57_44]
  try simp only [star_one, star_neg]
  linear_combination ((2281945 / 18) * t ^ 2 + (4039343 / 80) * t ^ 4 + (-3174171499 / 4000) * t ^ 6 + (26383464044377 / 28800000) * t ^ 8 + (-33464569687363 / 115200000) * t ^ 10 + (33020351659 / 21600000) * t ^ 12 + (-660581225963 / 46080000) * t ^ 14 + (696537675491 / 172800000) * t ^ 16 + (-583846961071 / 518400000) * t ^ 18 + (320176979021 / 518400000) * t ^ 20 + (-4841724191 / 230400000) * t ^ 22 + (2493618511 / 259200000) * t ^ 26 + (-2725107 / 80) * d * t ^ 4 + (1640641939 / 14400) * d * t ^ 6 + (-2395647245497 / 17280000) * d * t ^ 8 + (3341725106047 / 46080000) * d * t ^ 10 + (-706895334373 / 46080000) * d * t ^ 12 + (490597324151 / 207360000) * d * t ^ 14 + (-13346784671 / 17280000) * d * t ^ 16 + (-155471449 / 17280000) * d * t ^ 18 + (18134129 / 5760000) * d * t ^ 20 + (7774729 / 5760000) * d * t ^ 22 + (81040559 / 184320000) * d * t ^ 24 + (-87237113 / 49766400) * d * t ^ 26 + (8944877 / 66355200) * d * t ^ 32 + (-39107 / 1152) * d ^ 2 * t ^ 6 + (-960199 / 64800) * d ^ 2 * t ^ 8 + (641949677 / 5529600) * d ^ 2 * t ^ 10 + (-1730235497 / 27648000) * d ^ 2 * t ^ 12 + (-17003113 / 13824000) * d ^ 2 * t ^ 14 + (-88096153 / 27648000) * d ^ 2 * t ^ 16 + (-6057823 / 20736000) * d ^ 2 * t ^ 18 + (-323399 / 2488320) * d ^ 2 * t ^ 20 + (234829 / 6912000) * d ^ 2 * t ^ 22 + (-2554729 / 663552000) * d ^ 2 * t ^ 24 + (224599 / 19906560) * d ^ 2 * t ^ 26 + (9025 / 47775744) * d ^ 2 * t ^ 32) * alpha_sq + ((-2281945 / 18) * t ^ 2 + (80226377 / 240) * t ^ 4 + (-928885939 / 3200) * t ^ 6 + (1700340075761 / 17280000) * t ^ 8 + (-468654510281 / 15360000) * t ^ 10 + (1976737162367 / 138240000) * t ^ 12 + (33670964551 / 46080000) * t ^ 14 + (-31013542157 / 138240000) * t ^ 16 + (184123667 / 4147200) * t ^ 18 + (-774974353 / 51840000) * t ^ 20 + (1088865337 / 46080000) * t ^ 22 + (2554729 / 221184000) * t ^ 24 + (228377 / 2048000) * t ^ 26 + (-9025 / 15925248) * t ^ 32) * d_sq
#print axioms v59_00
#print axioms v59_11
#print axioms v59_22
#print axioms v59_33
#print axioms v59_44
end PhotonCertA
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z60 : Fin 60 → ℂ := Fin.snoc z59 (r ^ 3 * phiMinus)
theorem v60_00 (t : ℂ) : (momentPoly 60 z60 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00]
  try simp only [phase57_00]
  try simp only [star_one, star_neg]
  ring
theorem v60_01 (t : ℂ) : (momentPoly 60 z60 0 1).eval t = (1 * t) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01]
  try simp only [phase57_00, phase57_01]
  try simp only [star_one, star_neg]
  ring
theorem v60_02 (t : ℂ) : (momentPoly 60 z60 0 2).eval t = ((89 / 40) * t ^ 2 + (-49 / 40) * t ^ 4 + (413 / 40) * alpha * t ^ 2 + (-413 / 40) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02]
  try simp only [phase57_00, phase57_01, phase57_02]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 288) * t ^ 2) * alpha_sq + ((-1 / 288) * t ^ 2) * d_sq
theorem v60_03 (t : ℂ) : (momentPoly 60 z60 0 3).eval t = ((187 / 40) * t ^ 3 + (-147 / 40) * t ^ 5 + (1253 / 50) * alpha * t ^ 3 + (-8841 / 400) * alpha * t ^ 5 + (-1183 / 400) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_03]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03]
  try simp only [star_one, star_neg]
  linear_combination ((-1249 / 960) * t ^ 3 + (413 / 320) * t ^ 5 + (1 / 1152) * d * t ^ 3 + (-1 / 1152) * d * t ^ 5) * alpha_sq + ((-1 / 96) * t ^ 3 + (-1 / 1152) * alpha * t ^ 3 + (1 / 1152) * alpha * t ^ 5) * d_sq
theorem v60_04 (t : ℂ) : (momentPoly 60 z60 0 4).eval t = ((-7552691 / 8000) * t ^ 4 + (7590091 / 4000) * t ^ 6 + (-15259081 / 16000) * t ^ 8 + (20099 / 12000) * t ^ 10 + (-20099 / 48000) * t ^ 16 + (442647 / 8000) * alpha * t ^ 4 + (-242167 / 4000) * alpha * t ^ 6 + (743437 / 16000) * alpha * t ^ 8 + (-612743 / 12000) * alpha * t ^ 10 + (470783 / 48000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_03, v59_04]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04]
  try simp only [star_one, star_neg]
  linear_combination ((-62599 / 14400) * t ^ 4 + (55201 / 14400) * t ^ 6 + (39013 / 86400) * t ^ 10 + (1259 / 5760) * d * t ^ 4 + (-1249 / 2880) * d * t ^ 6 + (413 / 1920) * d * t ^ 8 + (1 / 6912) * d ^ 2 * t ^ 6 + (-1 / 13824) * d ^ 2 * t ^ 8) * alpha_sq + ((-251 / 2880) * t ^ 4 + (253 / 3840) * t ^ 6 + (1 / 4608) * t ^ 8 + (-47 / 3456) * t ^ 10 + (-1259 / 5760) * alpha * t ^ 4 + (1259 / 5760) * alpha * t ^ 6) * d_sq
theorem v60_10 (t : ℂ) : (momentPoly 60 z60 1 0).eval t = (1 * t) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_10]
  try simp only [phase57_00, phase57_10]
  try simp only [star_one, star_neg]
  ring
theorem v60_11 (t : ℂ) : (momentPoly 60 z60 1 1).eval t = (60 + (-59) * t ^ 2) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_10, v59_11]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 288) * t ^ 2) * alpha_sq + ((-1 / 288) * t ^ 2) * d_sq
theorem v60_12 (t : ℂ) : (momentPoly 60 z60 1 2).eval t = (119 * t + (-4631 / 40) * t ^ 3 + (-89 / 40) * t ^ 5 + (413 / 40) * alpha * t ^ 3 + (-413 / 40) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_10, v59_11, v59_12]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12]
  try simp only [star_one, star_neg]
  linear_combination ((1249 / 2880) * t ^ 3 + (-413 / 960) * t ^ 5 + (-1 / 3456) * d * t ^ 3 + (1 / 3456) * d * t ^ 5) * alpha_sq + ((-1 / 96) * t ^ 3 + (-1 / 3456) * alpha * t ^ 3 + (1 / 3456) * alpha * t ^ 5) * d_sq
theorem v60_13 (t : ℂ) : (momentPoly 60 z60 1 3).eval t = ((15753 / 40) * t ^ 2 + (-24021 / 40) * t ^ 4 + (8259 / 40) * t ^ 6 + (49 / 40) * t ^ 10 + (73101 / 40) * alpha * t ^ 2 + (-180467 / 50) * alpha * t ^ 4 + (709779 / 400) * alpha * t ^ 6 + (2947 / 400) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_03, v59_10, v59_11, v59_12, v59_13]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13]
  try simp only [star_one, star_neg]
  linear_combination ((-59 / 96) * t ^ 2 + (45053 / 115200) * t ^ 4 + (38743 / 115200) * t ^ 6 + (-39013 / 345600) * t ^ 10) * alpha_sq + ((-59 / 96) * t ^ 2 + (12671 / 23040) * t ^ 4 + (769 / 23040) * t ^ 6 + (-47 / 13824) * t ^ 10 + (-1259 / 11520) * alpha * t ^ 4 + (1259 / 11520) * alpha * t ^ 6) * d_sq
theorem v60_14 (t : ℂ) : (momentPoly 60 z60 1 4).eval t = ((21879 / 20) * t ^ 3 + (-22998691 / 8000) * t ^ 5 + (10888291 / 4000) * t ^ 7 + (-15141481 / 16000) * t ^ 9 + (78899 / 12000) * t ^ 11 + (-20099 / 48000) * t ^ 17 + (146601 / 25) * alpha * t ^ 3 + (-86878433 / 8000) * alpha * t ^ 5 + (19667513 / 4000) * alpha * t ^ 7 + (-9764123 / 16000) * alpha * t ^ 9 + (8116537 / 12000) * alpha * t ^ 11 + (612743 / 48000) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_03, v59_04, v59_10, v59_11, v59_12, v59_13, v59_14]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14]
  try simp only [star_one, star_neg]
  linear_combination ((-48711 / 160) * t ^ 3 + (172343953 / 288000) * t ^ 5 + (-37832311 / 128000) * t ^ 7 + (215539 / 48000) * t ^ 9 + (-966383 / 288000) * t ^ 11 + (470783 / 1152000) * t ^ 17 + (13 / 64) * d * t ^ 3 + (-733 / 3840) * d * t ^ 5 + (-3451 / 15360) * d * t ^ 7 + (58889 / 276480) * d * t ^ 9 + (-47 / 41472) * d * t ^ 11 + (95 / 165888) * d * t ^ 17 + (1259 / 138240) * d ^ 2 * t ^ 7 + (-1249 / 138240) * d ^ 2 * t ^ 9) * alpha_sq + ((-39 / 16) * t ^ 3 + (10111 / 4608) * t ^ 5 + (649 / 5760) * t ^ 7 + (311 / 5760) * t ^ 9 + (-47 / 1728) * t ^ 11 + (-13 / 64) * alpha * t ^ 3 + (-30869 / 172800) * alpha * t ^ 5 + (80443 / 230400) * alpha * t ^ 7 + (-1543 / 276480) * alpha * t ^ 9 + (39013 / 1036800) * alpha * t ^ 11 + (95 / 165888) * alpha * t ^ 17) * d_sq
theorem v60_20 (t : ℂ) : (momentPoly 60 z60 2 0).eval t = ((89 / 40) * t ^ 2 + (-49 / 40) * t ^ 4 + (-413 / 40) * alpha * t ^ 2 + (413 / 40) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_10, v59_20]
  try simp only [phase57_00, phase57_10, phase57_20]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 288) * t ^ 2) * alpha_sq + ((-1 / 288) * t ^ 2) * d_sq
theorem v60_21 (t : ℂ) : (momentPoly 60 z60 2 1).eval t = (119 * t + (-4631 / 40) * t ^ 3 + (-89 / 40) * t ^ 5 + (-413 / 40) * alpha * t ^ 3 + (413 / 40) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_10, v59_11, v59_20, v59_21]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21]
  try simp only [star_one, star_neg]
  linear_combination ((1249 / 2880) * t ^ 3 + (-413 / 960) * t ^ 5 + (-1 / 3456) * d * t ^ 3 + (1 / 3456) * d * t ^ 5) * alpha_sq + ((-1 / 96) * t ^ 3 + (1 / 3456) * alpha * t ^ 3 + (-1 / 3456) * alpha * t ^ 5) * d_sq
theorem v60_22 (t : ℂ) : (momentPoly 60 z60 2 2).eval t = (7140 + (-13924) * t ^ 2 + (2773107 / 400) * t ^ 4 + (-81817 / 200) * t ^ 6 + (104527 / 400) * t ^ 8) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_10, v59_11, v59_12, v59_20, v59_21, v59_22]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22]
  try simp only [star_one, star_neg]
  linear_combination ((59 / 72) * t ^ 2 + (1781 / 1920) * t ^ 4 + (-9943 / 5760) * t ^ 6 + (-1259 / 17280) * d * t ^ 4 + (1249 / 8640) * d * t ^ 6 + (-413 / 5760) * d * t ^ 8 + (-1 / 20736) * d ^ 2 * t ^ 6 + (1 / 41472) * d ^ 2 * t ^ 8) * alpha_sq + ((-59 / 72) * t ^ 2 + (4391 / 5760) * t ^ 4 + (779 / 34560) * t ^ 6 + (-1 / 13824) * t ^ 8) * d_sq
theorem v60_23 (t : ℂ) : (momentPoly 60 z60 2 3).eval t = (21064 * t + (-1625481 / 40) * t ^ 3 + (152514083 / 8000) * t ^ 5 + (-39959 / 3200) * t ^ 7 + (8300829 / 16000) * t ^ 9 + (-1394537 / 16000) * t ^ 11 + (1449737 / 16000) * t ^ 13 + (144963 / 40) * alpha * t ^ 3 + (-57347087 / 8000) * alpha * t ^ 5 + (11220839 / 3200) * alpha * t ^ 7 + (321699 / 16000) * alpha * t ^ 9 + (225113 / 16000) * alpha * t ^ 11 + (57967 / 16000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_03, v59_10, v59_11, v59_12, v59_13, v59_20, v59_21, v59_22, v59_23]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23]
  try simp only [star_one, star_neg]
  linear_combination ((48711 / 320) * t ^ 3 + (-5672119 / 19200) * t ^ 5 + (8214613 / 57600) * t ^ 7 + (1324553 / 691200) * t ^ 11 + (-59059 / 46080) * t ^ 13 + (-13 / 128) * d * t ^ 3 + (529 / 172800) * d * t ^ 5 + (79303 / 276480) * d * t ^ 7 + (-259547 / 1382400) * d * t ^ 9 + (36613 / 4147200) * d * t ^ 11 + (-39013 / 4147200) * d * t ^ 13 + (-1259 / 138240) * d ^ 2 * t ^ 7 + (1249 / 138240) * d ^ 2 * t ^ 9) * alpha_sq + ((-117 / 32) * t ^ 3 + (15391 / 4608) * t ^ 5 + (1049 / 3840) * t ^ 7 + (-311 / 5760) * t ^ 9 + (-47 / 6912) * t ^ 11 + (-13 / 128) * alpha * t ^ 3 + (529 / 172800) * alpha * t ^ 5 + (122797 / 1382400) * alpha * t ^ 7 + (-1 / 55296) * alpha * t ^ 9 + (41363 / 4147200) * alpha * t ^ 11 + (-47 / 165888) * alpha * t ^ 13) * d_sq
theorem v60_24 (t : ℂ) : (momentPoly 60 z60 2 4).eval t = ((1843279 / 20) * t ^ 2 + (-1830279 / 8) * t ^ 4 + (28647501067 / 160000) * t ^ 6 + (-6245993701 / 160000) * t ^ 8 + (-38343719 / 12800) * t ^ 10 + (-1877798743 / 960000) * t ^ 12 + (375789863 / 240000) * t ^ 14 + (288403663 / 960000) * t ^ 18 + (-289981643 / 960000) * t ^ 20 + (8553643 / 20) * alpha * t ^ 2 + (-250899187 / 200) * alpha * t ^ 4 + (195513667683 / 160000) * alpha * t ^ 6 + (-64117267189 / 160000) * alpha * t ^ 8 + (974620221 / 64000) * alpha * t ^ 10 + (-9270366127 / 960000) * alpha * t ^ 12 + (725949 / 80000) * alpha * t ^ 14 + (10954687 / 960000) * alpha * t ^ 18 + (-1924209 / 320000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_03, v59_04, v59_10, v59_11, v59_12, v59_13, v59_14, v59_20, v59_21, v59_22, v59_23, v59_24]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24]
  try simp only [star_one, star_neg]
  linear_combination ((-20711 / 144) * t ^ 2 + (1306537 / 7200) * t ^ 4 + (179614643 / 1382400) * t ^ 6 + (-197542999 / 1152000) * t ^ 8 + (-613792229 / 13824000) * t ^ 10 + (46254079 / 864000) * t ^ 12 + (-111511 / 18000) * t ^ 14 + (14439931 / 13824000) * t ^ 18 + (-4371991 / 6912000) * d * t ^ 6 + (985639 / 576000) * d * t ^ 8 + (-222631 / 153600) * d * t ^ 10 + (112169 / 432000) * d * t ^ 12 + (570073 / 5184000) * d * t ^ 14 + (98611 / 2592000) * d * t ^ 18 + (-127523 / 3456000) * d * t ^ 20 + (-31927 / 2073600) * d ^ 2 * t ^ 8 + (19337 / 1382400) * d ^ 2 * t ^ 10 + (-769 / 3317760) * d ^ 2 * t ^ 12 + (18919 / 12441600) * d ^ 2 * t ^ 14 + (-95 / 1990656) * d ^ 2 * t ^ 18 + (95 / 1990656) * d ^ 2 * t ^ 20) * alpha_sq + ((-20711 / 144) * t ^ 2 + (367459 / 1440) * t ^ 4 + (-672990937 / 6912000) * t ^ 6 + (-20005439 / 1728000) * t ^ 8 + (-57358867 / 13824000) * t ^ 10 + (38196953 / 27648000) * t ^ 12 + (142877 / 4147200) * t ^ 14 + (696469 / 82944000) * t ^ 18 + (-95 / 663552) * t ^ 20 + (-36511 / 720) * alpha * t ^ 4 + (681503789 / 6912000) * alpha * t ^ 6 + (-108716231 / 2304000) * alpha * t ^ 8 + (-4415743 / 6912000) * alpha * t ^ 10 + (4632631 / 41472000) * alpha * t ^ 12 + (-58703 / 414720) * alpha * t ^ 14 + (-1364849 / 41472000) * alpha * t ^ 18) * d_sq
theorem v60_30 (t : ℂ) : (momentPoly 60 z60 3 0).eval t = ((187 / 40) * t ^ 3 + (-147 / 40) * t ^ 5 + (-1253 / 50) * alpha * t ^ 3 + (8841 / 400) * alpha * t ^ 5 + (1183 / 400) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_10, v59_20, v59_30]
  try simp only [phase57_00, phase57_10, phase57_20, phase57_30]
  try simp only [star_one, star_neg]
  linear_combination ((-1249 / 960) * t ^ 3 + (413 / 320) * t ^ 5 + (1 / 1152) * d * t ^ 3 + (-1 / 1152) * d * t ^ 5) * alpha_sq + ((-1 / 96) * t ^ 3 + (1 / 1152) * alpha * t ^ 3 + (-1 / 1152) * alpha * t ^ 5) * d_sq
theorem v60_31 (t : ℂ) : (momentPoly 60 z60 3 1).eval t = ((15753 / 40) * t ^ 2 + (-24021 / 40) * t ^ 4 + (8259 / 40) * t ^ 6 + (49 / 40) * t ^ 10 + (-73101 / 40) * alpha * t ^ 2 + (180467 / 50) * alpha * t ^ 4 + (-709779 / 400) * alpha * t ^ 6 + (-2947 / 400) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_10, v59_11, v59_20, v59_21, v59_30, v59_31]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21, phase57_30, phase57_31]
  try simp only [star_one, star_neg]
  linear_combination ((-59 / 96) * t ^ 2 + (45053 / 115200) * t ^ 4 + (38743 / 115200) * t ^ 6 + (-39013 / 345600) * t ^ 10) * alpha_sq + ((-59 / 96) * t ^ 2 + (12671 / 23040) * t ^ 4 + (769 / 23040) * t ^ 6 + (-47 / 13824) * t ^ 10 + (1259 / 11520) * alpha * t ^ 4 + (-1259 / 11520) * alpha * t ^ 6) * d_sq
theorem v60_32 (t : ℂ) : (momentPoly 60 z60 3 2).eval t = (21064 * t + (-1625481 / 40) * t ^ 3 + (152514083 / 8000) * t ^ 5 + (-39959 / 3200) * t ^ 7 + (8300829 / 16000) * t ^ 9 + (-1394537 / 16000) * t ^ 11 + (1449737 / 16000) * t ^ 13 + (-144963 / 40) * alpha * t ^ 3 + (57347087 / 8000) * alpha * t ^ 5 + (-11220839 / 3200) * alpha * t ^ 7 + (-321699 / 16000) * alpha * t ^ 9 + (-225113 / 16000) * alpha * t ^ 11 + (-57967 / 16000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_10, v59_11, v59_12, v59_20, v59_21, v59_22, v59_30, v59_31, v59_32]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22, phase57_30, phase57_31, phase57_32]
  try simp only [star_one, star_neg]
  linear_combination ((48711 / 320) * t ^ 3 + (-5672119 / 19200) * t ^ 5 + (8214613 / 57600) * t ^ 7 + (1324553 / 691200) * t ^ 11 + (-59059 / 46080) * t ^ 13 + (-13 / 128) * d * t ^ 3 + (529 / 172800) * d * t ^ 5 + (79303 / 276480) * d * t ^ 7 + (-259547 / 1382400) * d * t ^ 9 + (36613 / 4147200) * d * t ^ 11 + (-39013 / 4147200) * d * t ^ 13 + (-1259 / 138240) * d ^ 2 * t ^ 7 + (1249 / 138240) * d ^ 2 * t ^ 9) * alpha_sq + ((-117 / 32) * t ^ 3 + (15391 / 4608) * t ^ 5 + (1049 / 3840) * t ^ 7 + (-311 / 5760) * t ^ 9 + (-47 / 6912) * t ^ 11 + (13 / 128) * alpha * t ^ 3 + (-529 / 172800) * alpha * t ^ 5 + (-122797 / 1382400) * alpha * t ^ 7 + (1 / 55296) * alpha * t ^ 9 + (-41363 / 4147200) * alpha * t ^ 11 + (47 / 165888) * alpha * t ^ 13) * d_sq
theorem v60_33 (t : ℂ) : (momentPoly 60 z60 3 3).eval t = (1263840 + (-3665847) * t ^ 2 + (723780927 / 200) * t ^ 4 + (-57117063143 / 40000) * t ^ 6 + (6857614737 / 20000) * t ^ 8 + (-21084464457 / 160000) * t ^ 10 + (7825653 / 10000) * t ^ 12 + (-65735691 / 80000) * t ^ 14 + (-5401533 / 160000) * t ^ 18) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_03, v59_10, v59_11, v59_12, v59_13, v59_20, v59_21, v59_22, v59_23, v59_30, v59_31, v59_32, v59_33]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23, phase57_30, phase57_31, phase57_32, phase57_33]
  try simp only [star_one, star_neg]
  linear_combination ((20711 / 96) * t ^ 2 + (154947 / 320) * t ^ 4 + (-1194539993 / 768000) * t ^ 6 + (12910423 / 15360) * t ^ 8 + (544163 / 48000) * t ^ 10 + (119377403 / 13824000) * t ^ 12 + (-57115433 / 13824000) * t ^ 14 + (-11668943 / 16588800) * t ^ 18 + (-36511 / 960) * d * t ^ 4 + (17213263 / 153600) * d * t ^ 6 + (-2526737 / 23040) * d * t ^ 8 + (16421831 / 460800) * d * t ^ 10 + (-260747 / 691200) * d * t ^ 12 + (258347 / 691200) * d * t ^ 14 + (-175 / 6912) * d ^ 2 * t ^ 6 + (-8321 / 691200) * d ^ 2 * t ^ 8 + (15931 / 460800) * d ^ 2 * t ^ 10 + (3349 / 1382400) * d ^ 2 * t ^ 14) * alpha_sq + ((-20711 / 96) * t ^ 2 + (127339 / 320) * t ^ 4 + (-81477361 / 460800) * t ^ 6 + (181193 / 57600) * t ^ 8 + (-1343561 / 153600) * t ^ 10 + (-381487 / 2764800) * t ^ 12 + (140527 / 2764800) * t ^ 14 + (-2209 / 663552) * t ^ 18) * d_sq
theorem v60_34 (t : ℂ) : (momentPoly 60 z60 3 4).eval t = (4929687 * t + (-282875373 / 20) * t ^ 3 + (10737087747 / 800) * t ^ 5 + (-7179314374793 / 1600000) * t ^ 7 + (2027116958081 / 3200000) * t ^ 9 + (-1321577656661 / 3200000) * t ^ 11 + (18541277311 / 153600) * t ^ 13 + (-24339452741 / 400000) * t ^ 15 + (-2553017913 / 6400000) * t ^ 17 + (8174348237 / 9600000) * t ^ 19 + (-5849308393 / 6400000) * t ^ 21 + (-563336289 / 6400000) * t ^ 25 + (25227279 / 20) * alpha * t ^ 3 + (-2965674663 / 800) * alpha * t ^ 5 + (5754538739237 / 1600000) * alpha * t ^ 7 + (-3648824664769 / 3200000) * alpha * t ^ 9 + (30885179809 / 3200000) * alpha * t ^ 11 + (-78313777679 / 3840000) * alpha * t ^ 13 + (1169358869 / 400000) * alpha * t ^ 15 + (-17655012823 / 6400000) * alpha * t ^ 17 + (14716109 / 3200000) * alpha * t ^ 19 + (-161235823 / 6400000) * alpha * t ^ 21 + (-23777117 / 19200000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_03, v59_04, v59_10, v59_11, v59_12, v59_13, v59_14, v59_20, v59_21, v59_22, v59_23, v59_24, v59_30, v59_31, v59_32, v59_33, v59_34]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24, phase57_30, phase57_31, phase57_32, phase57_33, phase57_34]
  try simp only [star_one, star_neg]
  linear_combination ((8476963 / 160) * t ^ 3 + (-97416259 / 640) * t ^ 5 + (6690389422433 / 46080000) * t ^ 7 + (-1436086147591 / 30720000) * t ^ 9 + (26802018727 / 9216000) * t ^ 11 + (-1642686174469 / 552960000) * t ^ 13 + (231693405653 / 276480000) * t ^ 15 + (30822077 / 2304000) * t ^ 17 + (4106213827 / 1658880000) * t ^ 19 + (-98365433 / 30720000) * t ^ 21 + (67321969 / 55296000) * t ^ 25 + (-6787 / 192) * d * t ^ 3 + (-2609 / 80) * d * t ^ 5 + (8109195409 / 27648000) * d * t ^ 7 + (-9439859159 / 27648000) * d * t ^ 9 + (3270515761 / 27648000) * d * t ^ 11 + (-417963221 / 41472000) * d * t ^ 13 + (422420197 / 55296000) * d * t ^ 15 + (40894819 / 331776000) * d * t ^ 17 + (32352887 / 199065600) * d * t ^ 19 + (-1939597 / 66355200) * d * t ^ 21 + (-741247 / 39813120) * d * t ^ 25 + (-436873 / 69120) * d ^ 2 * t ^ 7 + (677704589 / 55296000) * d ^ 2 * t ^ 9 + (-161782409 / 27648000) * d ^ 2 * t ^ 11 + (-8426311 / 110592000) * d ^ 2 * t ^ 13 + (697603 / 165888000) * d ^ 2 * t ^ 15 + (-19411 / 2211840) * d ^ 2 * t ^ 17 + (-23921 / 2654208) * d ^ 2 * t ^ 19 + (98611 / 20736000) * d ^ 2 * t ^ 21) * alpha_sq + ((-20361 / 16) * t ^ 3 + (1769965 / 768) * t ^ 5 + (-1588494679 / 1843200) * t ^ 7 + (-1642233521 / 9216000) * t ^ 9 + (23927767 / 9216000) * t ^ 11 + (28280953 / 3072000) * t ^ 13 + (-67460837 / 13824000) * t ^ 15 + (19411 / 368640) * t ^ 17 + (3280321 / 82944000) * t ^ 19 + (-777013 / 27648000) * t ^ 21 + (-6787 / 192) * alpha * t ^ 3 + (-2609 / 80) * alpha * t ^ 5 + (4309989569 / 27648000) * alpha * t ^ 7 + (-2253408547 / 27648000) * alpha * t ^ 9 + (-1693867 / 1105920) * alpha * t ^ 11 + (-6688933 / 1536000) * alpha * t ^ 13 + (-1483757 / 3686400) * alpha * t ^ 15 + (-322417 / 66355200) * alpha * t ^ 17 + (-25149529 / 199065600) * alpha * t ^ 19 + (-1141781 / 331776000) * alpha * t ^ 21 + (4465 / 7962624) * alpha * t ^ 25) * d_sq
theorem v60_40 (t : ℂ) : (momentPoly 60 z60 4 0).eval t = ((-7552691 / 8000) * t ^ 4 + (7590091 / 4000) * t ^ 6 + (-15259081 / 16000) * t ^ 8 + (20099 / 12000) * t ^ 10 + (-20099 / 48000) * t ^ 16 + (-442647 / 8000) * alpha * t ^ 4 + (242167 / 4000) * alpha * t ^ 6 + (-743437 / 16000) * alpha * t ^ 8 + (612743 / 12000) * alpha * t ^ 10 + (-470783 / 48000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_10, v59_20, v59_30, v59_40]
  try simp only [phase57_00, phase57_10, phase57_20, phase57_30, phase57_40]
  try simp only [star_one, star_neg]
  linear_combination ((-62599 / 14400) * t ^ 4 + (55201 / 14400) * t ^ 6 + (39013 / 86400) * t ^ 10 + (1259 / 5760) * d * t ^ 4 + (-1249 / 2880) * d * t ^ 6 + (413 / 1920) * d * t ^ 8 + (1 / 6912) * d ^ 2 * t ^ 6 + (-1 / 13824) * d ^ 2 * t ^ 8) * alpha_sq + ((-251 / 2880) * t ^ 4 + (253 / 3840) * t ^ 6 + (1 / 4608) * t ^ 8 + (-47 / 3456) * t ^ 10 + (1259 / 5760) * alpha * t ^ 4 + (-1259 / 5760) * alpha * t ^ 6) * d_sq
theorem v60_41 (t : ℂ) : (momentPoly 60 z60 4 1).eval t = ((21879 / 20) * t ^ 3 + (-22998691 / 8000) * t ^ 5 + (10888291 / 4000) * t ^ 7 + (-15141481 / 16000) * t ^ 9 + (78899 / 12000) * t ^ 11 + (-20099 / 48000) * t ^ 17 + (-146601 / 25) * alpha * t ^ 3 + (86878433 / 8000) * alpha * t ^ 5 + (-19667513 / 4000) * alpha * t ^ 7 + (9764123 / 16000) * alpha * t ^ 9 + (-8116537 / 12000) * alpha * t ^ 11 + (-612743 / 48000) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_10, v59_11, v59_20, v59_21, v59_30, v59_31, v59_40, v59_41]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21, phase57_30, phase57_31, phase57_40, phase57_41]
  try simp only [star_one, star_neg]
  linear_combination ((-48711 / 160) * t ^ 3 + (172343953 / 288000) * t ^ 5 + (-37832311 / 128000) * t ^ 7 + (215539 / 48000) * t ^ 9 + (-966383 / 288000) * t ^ 11 + (470783 / 1152000) * t ^ 17 + (13 / 64) * d * t ^ 3 + (-733 / 3840) * d * t ^ 5 + (-3451 / 15360) * d * t ^ 7 + (58889 / 276480) * d * t ^ 9 + (-47 / 41472) * d * t ^ 11 + (95 / 165888) * d * t ^ 17 + (1259 / 138240) * d ^ 2 * t ^ 7 + (-1249 / 138240) * d ^ 2 * t ^ 9) * alpha_sq + ((-39 / 16) * t ^ 3 + (10111 / 4608) * t ^ 5 + (649 / 5760) * t ^ 7 + (311 / 5760) * t ^ 9 + (-47 / 1728) * t ^ 11 + (13 / 64) * alpha * t ^ 3 + (30869 / 172800) * alpha * t ^ 5 + (-80443 / 230400) * alpha * t ^ 7 + (1543 / 276480) * alpha * t ^ 9 + (-39013 / 1036800) * alpha * t ^ 11 + (-95 / 165888) * alpha * t ^ 17) * d_sq
theorem v60_42 (t : ℂ) : (momentPoly 60 z60 4 2).eval t = ((1843279 / 20) * t ^ 2 + (-1830279 / 8) * t ^ 4 + (28647501067 / 160000) * t ^ 6 + (-6245993701 / 160000) * t ^ 8 + (-38343719 / 12800) * t ^ 10 + (-1877798743 / 960000) * t ^ 12 + (375789863 / 240000) * t ^ 14 + (288403663 / 960000) * t ^ 18 + (-289981643 / 960000) * t ^ 20 + (-8553643 / 20) * alpha * t ^ 2 + (250899187 / 200) * alpha * t ^ 4 + (-195513667683 / 160000) * alpha * t ^ 6 + (64117267189 / 160000) * alpha * t ^ 8 + (-974620221 / 64000) * alpha * t ^ 10 + (9270366127 / 960000) * alpha * t ^ 12 + (-725949 / 80000) * alpha * t ^ 14 + (-10954687 / 960000) * alpha * t ^ 18 + (1924209 / 320000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_10, v59_11, v59_12, v59_20, v59_21, v59_22, v59_30, v59_31, v59_32, v59_40, v59_41, v59_42]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22, phase57_30, phase57_31, phase57_32, phase57_40, phase57_41, phase57_42]
  try simp only [star_one, star_neg]
  linear_combination ((-20711 / 144) * t ^ 2 + (1306537 / 7200) * t ^ 4 + (179614643 / 1382400) * t ^ 6 + (-197542999 / 1152000) * t ^ 8 + (-613792229 / 13824000) * t ^ 10 + (46254079 / 864000) * t ^ 12 + (-111511 / 18000) * t ^ 14 + (14439931 / 13824000) * t ^ 18 + (-4371991 / 6912000) * d * t ^ 6 + (985639 / 576000) * d * t ^ 8 + (-222631 / 153600) * d * t ^ 10 + (112169 / 432000) * d * t ^ 12 + (570073 / 5184000) * d * t ^ 14 + (98611 / 2592000) * d * t ^ 18 + (-127523 / 3456000) * d * t ^ 20 + (-31927 / 2073600) * d ^ 2 * t ^ 8 + (19337 / 1382400) * d ^ 2 * t ^ 10 + (-769 / 3317760) * d ^ 2 * t ^ 12 + (18919 / 12441600) * d ^ 2 * t ^ 14 + (-95 / 1990656) * d ^ 2 * t ^ 18 + (95 / 1990656) * d ^ 2 * t ^ 20) * alpha_sq + ((-20711 / 144) * t ^ 2 + (367459 / 1440) * t ^ 4 + (-672990937 / 6912000) * t ^ 6 + (-20005439 / 1728000) * t ^ 8 + (-57358867 / 13824000) * t ^ 10 + (38196953 / 27648000) * t ^ 12 + (142877 / 4147200) * t ^ 14 + (696469 / 82944000) * t ^ 18 + (-95 / 663552) * t ^ 20 + (36511 / 720) * alpha * t ^ 4 + (-681503789 / 6912000) * alpha * t ^ 6 + (108716231 / 2304000) * alpha * t ^ 8 + (4415743 / 6912000) * alpha * t ^ 10 + (-4632631 / 41472000) * alpha * t ^ 12 + (58703 / 414720) * alpha * t ^ 14 + (1364849 / 41472000) * alpha * t ^ 18) * d_sq
theorem v60_43 (t : ℂ) : (momentPoly 60 z60 4 3).eval t = (4929687 * t + (-282875373 / 20) * t ^ 3 + (10737087747 / 800) * t ^ 5 + (-7179314374793 / 1600000) * t ^ 7 + (2027116958081 / 3200000) * t ^ 9 + (-1321577656661 / 3200000) * t ^ 11 + (18541277311 / 153600) * t ^ 13 + (-24339452741 / 400000) * t ^ 15 + (-2553017913 / 6400000) * t ^ 17 + (8174348237 / 9600000) * t ^ 19 + (-5849308393 / 6400000) * t ^ 21 + (-563336289 / 6400000) * t ^ 25 + (-25227279 / 20) * alpha * t ^ 3 + (2965674663 / 800) * alpha * t ^ 5 + (-5754538739237 / 1600000) * alpha * t ^ 7 + (3648824664769 / 3200000) * alpha * t ^ 9 + (-30885179809 / 3200000) * alpha * t ^ 11 + (78313777679 / 3840000) * alpha * t ^ 13 + (-1169358869 / 400000) * alpha * t ^ 15 + (17655012823 / 6400000) * alpha * t ^ 17 + (-14716109 / 3200000) * alpha * t ^ 19 + (161235823 / 6400000) * alpha * t ^ 21 + (23777117 / 19200000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_03, v59_10, v59_11, v59_12, v59_13, v59_20, v59_21, v59_22, v59_23, v59_30, v59_31, v59_32, v59_33, v59_40, v59_41, v59_42, v59_43]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23, phase57_30, phase57_31, phase57_32, phase57_33, phase57_40, phase57_41, phase57_42, phase57_43]
  try simp only [star_one, star_neg]
  linear_combination ((8476963 / 160) * t ^ 3 + (-97416259 / 640) * t ^ 5 + (6690389422433 / 46080000) * t ^ 7 + (-1436086147591 / 30720000) * t ^ 9 + (26802018727 / 9216000) * t ^ 11 + (-1642686174469 / 552960000) * t ^ 13 + (231693405653 / 276480000) * t ^ 15 + (30822077 / 2304000) * t ^ 17 + (4106213827 / 1658880000) * t ^ 19 + (-98365433 / 30720000) * t ^ 21 + (67321969 / 55296000) * t ^ 25 + (-6787 / 192) * d * t ^ 3 + (-2609 / 80) * d * t ^ 5 + (8109195409 / 27648000) * d * t ^ 7 + (-9439859159 / 27648000) * d * t ^ 9 + (3270515761 / 27648000) * d * t ^ 11 + (-417963221 / 41472000) * d * t ^ 13 + (422420197 / 55296000) * d * t ^ 15 + (40894819 / 331776000) * d * t ^ 17 + (32352887 / 199065600) * d * t ^ 19 + (-1939597 / 66355200) * d * t ^ 21 + (-741247 / 39813120) * d * t ^ 25 + (-436873 / 69120) * d ^ 2 * t ^ 7 + (677704589 / 55296000) * d ^ 2 * t ^ 9 + (-161782409 / 27648000) * d ^ 2 * t ^ 11 + (-8426311 / 110592000) * d ^ 2 * t ^ 13 + (697603 / 165888000) * d ^ 2 * t ^ 15 + (-19411 / 2211840) * d ^ 2 * t ^ 17 + (-23921 / 2654208) * d ^ 2 * t ^ 19 + (98611 / 20736000) * d ^ 2 * t ^ 21) * alpha_sq + ((-20361 / 16) * t ^ 3 + (1769965 / 768) * t ^ 5 + (-1588494679 / 1843200) * t ^ 7 + (-1642233521 / 9216000) * t ^ 9 + (23927767 / 9216000) * t ^ 11 + (28280953 / 3072000) * t ^ 13 + (-67460837 / 13824000) * t ^ 15 + (19411 / 368640) * t ^ 17 + (3280321 / 82944000) * t ^ 19 + (-777013 / 27648000) * t ^ 21 + (6787 / 192) * alpha * t ^ 3 + (2609 / 80) * alpha * t ^ 5 + (-4309989569 / 27648000) * alpha * t ^ 7 + (2253408547 / 27648000) * alpha * t ^ 9 + (1693867 / 1105920) * alpha * t ^ 11 + (6688933 / 1536000) * alpha * t ^ 13 + (1483757 / 3686400) * alpha * t ^ 15 + (322417 / 66355200) * alpha * t ^ 17 + (25149529 / 199065600) * alpha * t ^ 19 + (1141781 / 331776000) * alpha * t ^ 21 + (-4465 / 7962624) * alpha * t ^ 25) * d_sq
theorem v60_44 (t : ℂ) : (momentPoly 60 z60 4 4).eval t = (295781220 + (-1134245736) * t ^ 2 + (83251445247 / 50) * t ^ 4 + (-1507224746313 / 1250) * t ^ 6 + (8505060496477527 / 16000000) * t ^ 8 + (-835574202968657 / 4000000) * t ^ 10 + (182868121904739 / 3200000) * t ^ 12 + (-39343060464017 / 24000000) * t ^ 14 + (197405918570617 / 192000000) * t ^ 16 + (-715333545323 / 24000000) * t ^ 18 + (5527213972507 / 144000000) * t ^ 20 + (14146679377 / 24000000) * t ^ 22 + (38133433133 / 96000000) * t ^ 24 + (-163023214477 / 72000000) * t ^ 26 + (131768467267 / 576000000) * t ^ 32) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_03, v59_04, v59_10, v59_11, v59_12, v59_13, v59_14, v59_20, v59_21, v59_22, v59_23, v59_24, v59_30, v59_31, v59_32, v59_33, v59_34, v59_40, v59_41, v59_42, v59_43, v59_44]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24, phase57_30, phase57_31, phase57_32, phase57_33, phase57_34, phase57_40, phase57_41, phase57_42, phase57_43, phase57_44]
  try simp only [star_one, star_neg]
  linear_combination ((267007 / 4) * t ^ 2 + (17822467 / 80) * t ^ 4 + (-48545315951 / 48000) * t ^ 6 + (123619882561223 / 115200000) * t ^ 8 + (-39608563750183 / 115200000) * t ^ 10 + (1031095227881 / 230400000) * t ^ 12 + (-6705324715763 / 414720000) * t ^ 14 + (855906671551 / 172800000) * t ^ 16 + (-920941790503 / 691200000) * t ^ 18 + (1331329551889 / 2073600000) * t ^ 20 + (-5203404569 / 345600000) * t ^ 22 + (1914519649 / 172800000) * t ^ 26 + (-12598813 / 720) * d * t ^ 4 + (1961479193 / 28800) * d * t ^ 6 + (-6844270634449 / 69120000) * d * t ^ 8 + (8847242099707 / 138240000) * d * t ^ 10 + (-4554254827523 / 276480000) * d * t ^ 12 + (307362706523 / 207360000) * d * t ^ 14 + (-22002591361 / 36864000) * d * t ^ 16 + (-520036573 / 207360000) * d * t ^ 18 + (1439562731 / 622080000) * d * t ^ 20 + (15307333 / 103680000) * d * t ^ 22 + (114427801 / 276480000) * d * t ^ 24 + (-15270433 / 12441600) * d * t ^ 26 + (8944877 / 66355200) * d * t ^ 32 + (-40489 / 3456) * d ^ 2 * t ^ 6 + (-4353899 / 259200) * d ^ 2 * t ^ 8 + (583487521 / 9216000) * d ^ 2 * t ^ 10 + (-1821358459 / 55296000) * d ^ 2 * t ^ 12 + (3070759 / 41472000) * d ^ 2 * t ^ 14 + (-585653419 / 331776000) * d ^ 2 * t ^ 16 + (-10816501 / 82944000) * d ^ 2 * t ^ 18 + (-606613 / 9953280) * d ^ 2 * t ^ 20 + (824699 / 66355200) * d ^ 2 * t ^ 22 + (-2980031 / 1990656000) * d ^ 2 * t ^ 24 + (359461 / 59719680) * d ^ 2 * t ^ 26 + (9025 / 95551488) * d ^ 2 * t ^ 32) * alpha_sq + ((-267007 / 4) * t ^ 2 + (43940737 / 240) * t ^ 4 + (-2398662961 / 14400) * t ^ 6 + (4033772913337 / 69120000) * t ^ 8 + (-241831940063 / 15360000) * t ^ 10 + (685234960289 / 92160000) * t ^ 12 + (110315943827 / 414720000) * t ^ 14 + (-59227832089 / 552960000) * t ^ 16 + (20947099 / 921600) * t ^ 18 + (-1544460581 / 207360000) * t ^ 20 + (6716076557 / 552960000) * t ^ 22 + (2980031 / 663552000) * t ^ 24 + (13644743 / 497664000) * t ^ 26 + (-9025 / 31850496) * t ^ 32) * d_sq
#print axioms v60_00
#print axioms v60_11
#print axioms v60_22
#print axioms v60_33
#print axioms v60_44
end PhotonCertA
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
theorem site61 : ((r ^ 3 * 1) : ℂ) = ((-1)) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((3 / 8) + (1 / 8) * alpha) * alpha_sq
theorem phase61_00 : ((r ^ 3 * 1) : ℂ) ^ 0 * star ((r ^ 3 * 1) : ℂ) ^ 0 = (1) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_01 : ((r ^ 3 * 1) : ℂ) ^ 0 * star ((r ^ 3 * 1) : ℂ) ^ 1 = ((-1)) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_02 : ((r ^ 3 * 1) : ℂ) ^ 0 * star ((r ^ 3 * 1) : ℂ) ^ 2 = (1) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_03 : ((r ^ 3 * 1) : ℂ) ^ 0 * star ((r ^ 3 * 1) : ℂ) ^ 3 = ((-1)) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_04 : ((r ^ 3 * 1) : ℂ) ^ 0 * star ((r ^ 3 * 1) : ℂ) ^ 4 = (1) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_10 : ((r ^ 3 * 1) : ℂ) ^ 1 * star ((r ^ 3 * 1) : ℂ) ^ 0 = ((-1)) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_11 : ((r ^ 3 * 1) : ℂ) ^ 1 * star ((r ^ 3 * 1) : ℂ) ^ 1 = (1) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_12 : ((r ^ 3 * 1) : ℂ) ^ 1 * star ((r ^ 3 * 1) : ℂ) ^ 2 = ((-1)) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_13 : ((r ^ 3 * 1) : ℂ) ^ 1 * star ((r ^ 3 * 1) : ℂ) ^ 3 = (1) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_14 : ((r ^ 3 * 1) : ℂ) ^ 1 * star ((r ^ 3 * 1) : ℂ) ^ 4 = ((-1)) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_20 : ((r ^ 3 * 1) : ℂ) ^ 2 * star ((r ^ 3 * 1) : ℂ) ^ 0 = (1) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_21 : ((r ^ 3 * 1) : ℂ) ^ 2 * star ((r ^ 3 * 1) : ℂ) ^ 1 = ((-1)) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_22 : ((r ^ 3 * 1) : ℂ) ^ 2 * star ((r ^ 3 * 1) : ℂ) ^ 2 = (1) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_23 : ((r ^ 3 * 1) : ℂ) ^ 2 * star ((r ^ 3 * 1) : ℂ) ^ 3 = ((-1)) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_24 : ((r ^ 3 * 1) : ℂ) ^ 2 * star ((r ^ 3 * 1) : ℂ) ^ 4 = (1) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_30 : ((r ^ 3 * 1) : ℂ) ^ 3 * star ((r ^ 3 * 1) : ℂ) ^ 0 = ((-1)) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_31 : ((r ^ 3 * 1) : ℂ) ^ 3 * star ((r ^ 3 * 1) : ℂ) ^ 1 = (1) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_32 : ((r ^ 3 * 1) : ℂ) ^ 3 * star ((r ^ 3 * 1) : ℂ) ^ 2 = ((-1)) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_33 : ((r ^ 3 * 1) : ℂ) ^ 3 * star ((r ^ 3 * 1) : ℂ) ^ 3 = (1) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_34 : ((r ^ 3 * 1) : ℂ) ^ 3 * star ((r ^ 3 * 1) : ℂ) ^ 4 = ((-1)) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_40 : ((r ^ 3 * 1) : ℂ) ^ 4 * star ((r ^ 3 * 1) : ℂ) ^ 0 = (1) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_41 : ((r ^ 3 * 1) : ℂ) ^ 4 * star ((r ^ 3 * 1) : ℂ) ^ 1 = ((-1)) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_42 : ((r ^ 3 * 1) : ℂ) ^ 4 * star ((r ^ 3 * 1) : ℂ) ^ 2 = (1) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_43 : ((r ^ 3 * 1) : ℂ) ^ 4 * star ((r ^ 3 * 1) : ℂ) ^ 3 = ((-1)) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase61_44 : ((r ^ 3 * 1) : ℂ) ^ 4 * star ((r ^ 3 * 1) : ℂ) ^ 4 = (1) := by
  rw [site61]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
noncomputable def z61 : Fin 61 → ℂ := Fin.snoc z60 (r ^ 3 * 1)
theorem v61_00 (t : ℂ) : (momentPoly 61 z61 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00]
  try simp only [phase61_00]
  try simp only [star_one, star_neg]
  ring
theorem v61_01 (t : ℂ) : (momentPoly 61 z61 0 1).eval t = 0 := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01]
  try simp only [phase61_00, phase61_01]
  try simp only [star_one, star_neg]
  ring
theorem v61_02 (t : ℂ) : (momentPoly 61 z61 0 2).eval t = ((9 / 40) * t ^ 2 + (-9 / 40) * t ^ 4 + (413 / 40) * alpha * t ^ 2 + (-413 / 40) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02]
  try simp only [phase61_00, phase61_01, phase61_02]
  try simp only [star_one, star_neg]
  ring
theorem v61_03 (t : ℂ) : (momentPoly 61 z61 0 3).eval t = ((-2) * t ^ 3 + 3 * t ^ 5 + (-1) * t ^ 9 + (-1183 / 200) * alpha * t ^ 3 + (3549 / 400) * alpha * t ^ 5 + (-1183 / 400) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_03]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03]
  try simp only [star_one, star_neg]
  ring
theorem v61_04 (t : ℂ) : (momentPoly 61 z61 0 4).eval t = ((-7702291 / 8000) * t ^ 4 + (7702291 / 4000) * t ^ 6 + (-15376681 / 16000) * t ^ 8 + (-27901 / 12000) * t ^ 10 + (27901 / 48000) * t ^ 16 + (-359273 / 8000) * alpha * t ^ 4 + (359273 / 4000) * alpha * t ^ 6 + (-247763 / 16000) * alpha * t ^ 8 + (-470783 / 12000) * alpha * t ^ 10 + (470783 / 48000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_03, v60_04]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_04]
  try simp only [star_one, star_neg]
  ring
theorem v61_10 (t : ℂ) : (momentPoly 61 z61 1 0).eval t = 0 := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_10]
  try simp only [phase61_00, phase61_10]
  try simp only [star_one, star_neg]
  ring
theorem v61_11 (t : ℂ) : (momentPoly 61 z61 1 1).eval t = (61 + (-61) * t ^ 2) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_10, v60_11]
  try simp only [phase61_00, phase61_01, phase61_10, phase61_11]
  try simp only [star_one, star_neg]
  ring
theorem v61_12 (t : ℂ) : (momentPoly 61 z61 1 2).eval t = 0 := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_10, v60_11, v60_12]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_10, phase61_11, phase61_12]
  try simp only [star_one, star_neg]
  ring
theorem v61_13 (t : ℂ) : (momentPoly 61 z61 1 3).eval t = ((81 / 2) * t ^ 2 + (-1611 / 20) * t ^ 4 + (1593 / 40) * t ^ 6 + (9 / 40) * t ^ 10 + (3717 / 2) * alpha * t ^ 2 + (-73927 / 20) * alpha * t ^ 4 + (73101 / 40) * alpha * t ^ 6 + (413 / 40) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_03, v60_10, v60_11, v60_12, v60_13]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_10, phase61_11, phase61_12, phase61_13]
  try simp only [star_one, star_neg]
  ring
theorem v61_14 (t : ℂ) : (momentPoly 61 z61 1 4).eval t = ((-476) * t ^ 3 + 1182 * t ^ 5 + (-696) * t ^ 7 + (-247) * t ^ 9 + 236 * t ^ 11 + 1 * t ^ 17 + (-140777 / 100) * alpha * t ^ 3 + (699153 / 200) * alpha * t ^ 5 + (-102921 / 50) * alpha * t ^ 7 + (-292201 / 400) * alpha * t ^ 9 + (69797 / 100) * alpha * t ^ 11 + (1183 / 400) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_03, v60_04, v60_10, v60_11, v60_12, v60_13, v60_14]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_04, phase61_10, phase61_11, phase61_12, phase61_13, phase61_14]
  try simp only [star_one, star_neg]
  ring
theorem v61_20 (t : ℂ) : (momentPoly 61 z61 2 0).eval t = ((9 / 40) * t ^ 2 + (-9 / 40) * t ^ 4 + (-413 / 40) * alpha * t ^ 2 + (413 / 40) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_10, v60_20]
  try simp only [phase61_00, phase61_10, phase61_20]
  try simp only [star_one, star_neg]
  ring
theorem v61_21 (t : ℂ) : (momentPoly 61 z61 2 1).eval t = 0 := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_10, v60_11, v60_20, v60_21]
  try simp only [phase61_00, phase61_01, phase61_10, phase61_11, phase61_20, phase61_21]
  try simp only [star_one, star_neg]
  ring
theorem v61_22 (t : ℂ) : (momentPoly 61 z61 2 2).eval t = (7381 + (-14640) * t ^ 2 + (2958347 / 400) * t ^ 4 + (-79147 / 200) * t ^ 6 + (103547 / 400) * t ^ 8) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_10, v60_11, v60_12, v60_20, v60_21, v60_22]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_10, phase61_11, phase61_12, phase61_20, phase61_21, phase61_22]
  try simp only [star_one, star_neg]
  ring
theorem v61_23 (t : ℂ) : (momentPoly 61 z61 2 3).eval t = ((-1469337 / 8000) * t ^ 5 + (1469337 / 3200) * t ^ 7 + (-4408011 / 16000) * t ^ 9 + (-1469337 / 16000) * t ^ 11 + (1469337 / 16000) * t ^ 13 + (154553 / 8000) * alpha * t ^ 5 + (-154553 / 3200) * alpha * t ^ 7 + (463659 / 16000) * alpha * t ^ 9 + (154553 / 16000) * alpha * t ^ 11 + (-154553 / 16000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_03, v60_10, v60_11, v60_12, v60_13, v60_20, v60_21, v60_22, v60_23]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_10, phase61_11, phase61_12, phase61_13, phase61_20, phase61_21, phase61_22, phase61_23]
  try simp only [star_one, star_neg]
  ring
theorem v61_24 (t : ℂ) : (momentPoly 61 z61 2 4).eval t = ((96399 / 10) * t ^ 2 + (-228357 / 8) * t ^ 4 + (4194674067 / 160000) * t ^ 6 + (-604662201 / 160000) * t ^ 8 + (-53802399 / 12800) * t ^ 10 + (-173837921 / 320000) * t ^ 12 + (97114541 / 80000) * t ^ 14 + (97114541 / 320000) * t ^ 18 + (-97186541 / 320000) * t ^ 20 + (4423643 / 10) * alpha * t ^ 2 + (-10479049 / 8) * alpha * t ^ 4 + (205881834363 / 160000) * alpha * t ^ 6 + (-67925983089 / 160000) * alpha * t ^ 8 + (1048240629 / 64000) * alpha * t ^ 10 + (-10538784947 / 960000) * alpha * t ^ 12 + (-23467033 / 240000) * alpha * t ^ 14 + (-23467033 / 960000) * alpha * t ^ 18 + (13555033 / 960000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_03, v60_04, v60_10, v60_11, v60_12, v60_13, v60_14, v60_20, v60_21, v60_22, v60_23, v60_24]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_04, phase61_10, phase61_11, phase61_12, phase61_13, phase61_14, phase61_20, phase61_21, phase61_22, phase61_23, phase61_24]
  try simp only [star_one, star_neg]
  ring
theorem v61_30 (t : ℂ) : (momentPoly 61 z61 3 0).eval t = ((-2) * t ^ 3 + 3 * t ^ 5 + (-1) * t ^ 9 + (1183 / 200) * alpha * t ^ 3 + (-3549 / 400) * alpha * t ^ 5 + (1183 / 400) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_10, v60_20, v60_30]
  try simp only [phase61_00, phase61_10, phase61_20, phase61_30]
  try simp only [star_one, star_neg]
  ring
theorem v61_31 (t : ℂ) : (momentPoly 61 z61 3 1).eval t = ((81 / 2) * t ^ 2 + (-1611 / 20) * t ^ 4 + (1593 / 40) * t ^ 6 + (9 / 40) * t ^ 10 + (-3717 / 2) * alpha * t ^ 2 + (73927 / 20) * alpha * t ^ 4 + (-73101 / 40) * alpha * t ^ 6 + (-413 / 40) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_10, v60_11, v60_20, v60_21, v60_30, v60_31]
  try simp only [phase61_00, phase61_01, phase61_10, phase61_11, phase61_20, phase61_21, phase61_30, phase61_31]
  try simp only [star_one, star_neg]
  ring
theorem v61_32 (t : ℂ) : (momentPoly 61 z61 3 2).eval t = ((-1469337 / 8000) * t ^ 5 + (1469337 / 3200) * t ^ 7 + (-4408011 / 16000) * t ^ 9 + (-1469337 / 16000) * t ^ 11 + (1469337 / 16000) * t ^ 13 + (-154553 / 8000) * alpha * t ^ 5 + (154553 / 3200) * alpha * t ^ 7 + (-463659 / 16000) * alpha * t ^ 9 + (-154553 / 16000) * alpha * t ^ 11 + (154553 / 16000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_10, v60_11, v60_12, v60_20, v60_21, v60_22, v60_30, v60_31, v60_32]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_10, phase61_11, phase61_12, phase61_20, phase61_21, phase61_22, phase61_30, phase61_31, phase61_32]
  try simp only [star_one, star_neg]
  ring
theorem v61_33 (t : ℂ) : (momentPoly 61 z61 3 3).eval t = (1328641 + (-3920226) * t ^ 2 + (1570882257 / 400) * t ^ 4 + (-61743102233 / 40000) * t ^ 6 + (13667880699 / 40000) * t ^ 8 + (-21384298197 / 160000) * t ^ 10 + (51846667 / 40000) * t ^ 12 + (-108051801 / 80000) * t ^ 14 + (-5401533 / 160000) * t ^ 18) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_03, v60_10, v60_11, v60_12, v60_13, v60_20, v60_21, v60_22, v60_23, v60_30, v60_31, v60_32, v60_33]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_10, phase61_11, phase61_12, phase61_13, phase61_20, phase61_21, phase61_22, phase61_23, phase61_30, phase61_31, phase61_32, phase61_33]
  try simp only [star_one, star_neg]
  ring
theorem v61_34 (t : ℂ) : (momentPoly 61 z61 3 4).eval t = ((-515737287 / 4000) * t ^ 5 + (720510830077 / 1600000) * t ^ 7 + (-1643823859939 / 3200000) * t ^ 9 + (411373184749 / 3200000) * t ^ 11 + (492135352363 / 3840000) * t ^ 13 + (-13097173993 / 200000) * t ^ 15 + (7029983287 / 6400000) * t ^ 17 + (800367067 / 9600000) * t ^ 19 + (-81235133 / 6400000) * t ^ 21 + (-1681969267 / 19200000) * t ^ 25 + (54248103 / 4000) * alpha * t ^ 5 + (-84297233253 / 1600000) * alpha * t ^ 7 + (232475901371 / 3200000) * alpha * t ^ 9 + (-111682056941 / 3200000) * alpha * t ^ 11 + (-1208486339 / 153600) * alpha * t ^ 13 + (1199922271 / 100000) * alpha * t ^ 15 + (-18091508423 / 6400000) * alpha * t ^ 17 + (248038117 / 9600000) * alpha * t ^ 19 + (340769917 / 6400000) * alpha * t ^ 21 + (-155306317 / 19200000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_03, v60_04, v60_10, v60_11, v60_12, v60_13, v60_14, v60_20, v60_21, v60_22, v60_23, v60_24, v60_30, v60_31, v60_32, v60_33, v60_34]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_04, phase61_10, phase61_11, phase61_12, phase61_13, phase61_14, phase61_20, phase61_21, phase61_22, phase61_23, phase61_24, phase61_30, phase61_31, phase61_32, phase61_33, phase61_34]
  try simp only [star_one, star_neg]
  ring
theorem v61_40 (t : ℂ) : (momentPoly 61 z61 4 0).eval t = ((-7702291 / 8000) * t ^ 4 + (7702291 / 4000) * t ^ 6 + (-15376681 / 16000) * t ^ 8 + (-27901 / 12000) * t ^ 10 + (27901 / 48000) * t ^ 16 + (359273 / 8000) * alpha * t ^ 4 + (-359273 / 4000) * alpha * t ^ 6 + (247763 / 16000) * alpha * t ^ 8 + (470783 / 12000) * alpha * t ^ 10 + (-470783 / 48000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_10, v60_20, v60_30, v60_40]
  try simp only [phase61_00, phase61_10, phase61_20, phase61_30, phase61_40]
  try simp only [star_one, star_neg]
  ring
theorem v61_41 (t : ℂ) : (momentPoly 61 z61 4 1).eval t = ((-476) * t ^ 3 + 1182 * t ^ 5 + (-696) * t ^ 7 + (-247) * t ^ 9 + 236 * t ^ 11 + 1 * t ^ 17 + (140777 / 100) * alpha * t ^ 3 + (-699153 / 200) * alpha * t ^ 5 + (102921 / 50) * alpha * t ^ 7 + (292201 / 400) * alpha * t ^ 9 + (-69797 / 100) * alpha * t ^ 11 + (-1183 / 400) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_10, v60_11, v60_20, v60_21, v60_30, v60_31, v60_40, v60_41]
  try simp only [phase61_00, phase61_01, phase61_10, phase61_11, phase61_20, phase61_21, phase61_30, phase61_31, phase61_40, phase61_41]
  try simp only [star_one, star_neg]
  ring
theorem v61_42 (t : ℂ) : (momentPoly 61 z61 4 2).eval t = ((96399 / 10) * t ^ 2 + (-228357 / 8) * t ^ 4 + (4194674067 / 160000) * t ^ 6 + (-604662201 / 160000) * t ^ 8 + (-53802399 / 12800) * t ^ 10 + (-173837921 / 320000) * t ^ 12 + (97114541 / 80000) * t ^ 14 + (97114541 / 320000) * t ^ 18 + (-97186541 / 320000) * t ^ 20 + (-4423643 / 10) * alpha * t ^ 2 + (10479049 / 8) * alpha * t ^ 4 + (-205881834363 / 160000) * alpha * t ^ 6 + (67925983089 / 160000) * alpha * t ^ 8 + (-1048240629 / 64000) * alpha * t ^ 10 + (10538784947 / 960000) * alpha * t ^ 12 + (23467033 / 240000) * alpha * t ^ 14 + (23467033 / 960000) * alpha * t ^ 18 + (-13555033 / 960000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_10, v60_11, v60_12, v60_20, v60_21, v60_22, v60_30, v60_31, v60_32, v60_40, v60_41, v60_42]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_10, phase61_11, phase61_12, phase61_20, phase61_21, phase61_22, phase61_30, phase61_31, phase61_32, phase61_40, phase61_41, phase61_42]
  try simp only [star_one, star_neg]
  ring
theorem v61_43 (t : ℂ) : (momentPoly 61 z61 4 3).eval t = ((-515737287 / 4000) * t ^ 5 + (720510830077 / 1600000) * t ^ 7 + (-1643823859939 / 3200000) * t ^ 9 + (411373184749 / 3200000) * t ^ 11 + (492135352363 / 3840000) * t ^ 13 + (-13097173993 / 200000) * t ^ 15 + (7029983287 / 6400000) * t ^ 17 + (800367067 / 9600000) * t ^ 19 + (-81235133 / 6400000) * t ^ 21 + (-1681969267 / 19200000) * t ^ 25 + (-54248103 / 4000) * alpha * t ^ 5 + (84297233253 / 1600000) * alpha * t ^ 7 + (-232475901371 / 3200000) * alpha * t ^ 9 + (111682056941 / 3200000) * alpha * t ^ 11 + (1208486339 / 153600) * alpha * t ^ 13 + (-1199922271 / 100000) * alpha * t ^ 15 + (18091508423 / 6400000) * alpha * t ^ 17 + (-248038117 / 9600000) * alpha * t ^ 19 + (-340769917 / 6400000) * alpha * t ^ 21 + (155306317 / 19200000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_03, v60_10, v60_11, v60_12, v60_13, v60_20, v60_21, v60_22, v60_23, v60_30, v60_31, v60_32, v60_33, v60_40, v60_41, v60_42, v60_43]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_10, phase61_11, phase61_12, phase61_13, phase61_20, phase61_21, phase61_22, phase61_23, phase61_30, phase61_31, phase61_32, phase61_33, phase61_40, phase61_41, phase61_42, phase61_43]
  try simp only [star_one, star_neg]
  ring
theorem v61_44 (t : ℂ) : (momentPoly 61 z61 4 4).eval t = (316260661 + (-1233855784) * t ^ 2 + (183828724233 / 100) * t ^ 4 + (-3339521520089 / 2500) * t ^ 6 + (9123108824134567 / 16000000) * t ^ 8 + (-855758089160167 / 4000000) * t ^ 10 + (191967034768347 / 3200000) * t ^ 12 + (-63248688177067 / 24000000) * t ^ 14 + (282181596368857 / 192000000) * t ^ 16 + (-19061079533 / 24000000) * t ^ 18 + (4266821004067 / 144000000) * t ^ 20 + (367228122067 / 24000000) * t ^ 22 + (-492953510467 / 96000000) * t ^ 24 + (-111840572467 / 72000000) * t ^ 26 + (131286091267 / 576000000) * t ^ 32) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_03, v60_04, v60_10, v60_11, v60_12, v60_13, v60_14, v60_20, v60_21, v60_22, v60_23, v60_24, v60_30, v60_31, v60_32, v60_33, v60_34, v60_40, v60_41, v60_42, v60_43, v60_44]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_04, phase61_10, phase61_11, phase61_12, phase61_13, phase61_14, phase61_20, phase61_21, phase61_22, phase61_23, phase61_24, phase61_30, phase61_31, phase61_32, phase61_33, phase61_34, phase61_40, phase61_41, phase61_42, phase61_43, phase61_44]
  try simp only [star_one, star_neg]
  ring
#print axioms v61_00
#print axioms v61_11
#print axioms v61_22
#print axioms v61_33
#print axioms v61_44
end PhotonCertA
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z62 : Fin 62 → ℂ := Fin.snoc z61 (r ^ 3 * 1)
theorem v62_00 (t : ℂ) : (momentPoly 62 z62 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00]
  try simp only [phase61_00]
  try simp only [star_one, star_neg]
  ring
theorem v62_01 (t : ℂ) : (momentPoly 62 z62 0 1).eval t = ((-1) * t) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01]
  try simp only [phase61_00, phase61_01]
  try simp only [star_one, star_neg]
  ring
theorem v62_02 (t : ℂ) : (momentPoly 62 z62 0 2).eval t = ((9 / 40) * t ^ 2 + (31 / 40) * t ^ 4 + (413 / 40) * alpha * t ^ 2 + (-413 / 40) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02]
  try simp only [phase61_00, phase61_01, phase61_02]
  try simp only [star_one, star_neg]
  ring
theorem v62_03 (t : ℂ) : (momentPoly 62 z62 0 3).eval t = ((-107 / 40) * t ^ 3 + (147 / 40) * t ^ 5 + (-2) * t ^ 9 + (-3689 / 100) * alpha * t ^ 3 + (15939 / 400) * alpha * t ^ 5 + (-1183 / 400) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_03]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03]
  try simp only [star_one, star_neg]
  ring
theorem v62_04 (t : ℂ) : (momentPoly 62 z62 0 4).eval t = ((-7638291 / 8000) * t ^ 4 + (7659691 / 4000) * t ^ 6 + (-15398281 / 16000) * t ^ 8 + (20099 / 12000) * t ^ 10 + (75901 / 48000) * t ^ 16 + (-169993 / 8000) * alpha * t ^ 4 + (465113 / 4000) * alpha * t ^ 6 + (-1238963 / 16000) * alpha * t ^ 8 + (-328823 / 12000) * alpha * t ^ 10 + (470783 / 48000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_03, v61_04]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_04]
  try simp only [star_one, star_neg]
  ring
theorem v62_10 (t : ℂ) : (momentPoly 62 z62 1 0).eval t = ((-1) * t) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_10]
  try simp only [phase61_00, phase61_10]
  try simp only [star_one, star_neg]
  ring
theorem v62_11 (t : ℂ) : (momentPoly 62 z62 1 1).eval t = (62 + (-61) * t ^ 2) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_10, v61_11]
  try simp only [phase61_00, phase61_01, phase61_10, phase61_11]
  try simp only [star_one, star_neg]
  ring
theorem v62_12 (t : ℂ) : (momentPoly 62 z62 1 2).eval t = ((-123) * t + (4871 / 40) * t ^ 3 + (9 / 40) * t ^ 5 + (-413 / 40) * alpha * t ^ 3 + (413 / 40) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_10, v61_11, v61_12]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_10, phase61_11, phase61_12]
  try simp only [star_one, star_neg]
  ring
theorem v62_13 (t : ℂ) : (momentPoly 62 z62 1 3).eval t = ((1647 / 40) * t ^ 2 + (4191 / 40) * t ^ 4 + (-5847 / 40) * t ^ 6 + (49 / 40) * t ^ 10 + (75579 / 40) * alpha * t ^ 2 + (-372141 / 100) * alpha * t ^ 4 + (727461 / 400) * alpha * t ^ 6 + (5313 / 400) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_03, v61_10, v61_11, v61_12, v61_13]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_10, phase61_11, phase61_12, phase61_13]
  try simp only [star_one, star_neg]
  ring
theorem v62_14 (t : ℂ) : (momentPoly 62 z62 1 4).eval t = ((-12947 / 20) * t ^ 3 + (19842691 / 8000) * t ^ 5 + (-11123491 / 4000) * t ^ 7 + (7440681 / 16000) * t ^ 9 + (5777101 / 12000) * t ^ 11 + (20099 / 48000) * t ^ 17 + (-446369 / 50) * alpha * t ^ 3 + (147388113 / 8000) * alpha * t ^ 5 + (-37833353 / 4000) * alpha * t ^ 7 + (-11629557 / 16000) * alpha * t ^ 9 + (8350823 / 12000) * alpha * t ^ 11 + (-328823 / 48000) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_03, v61_04, v61_10, v61_11, v61_12, v61_13, v61_14]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_04, phase61_10, phase61_11, phase61_12, phase61_13, phase61_14]
  try simp only [star_one, star_neg]
  ring
theorem v62_20 (t : ℂ) : (momentPoly 62 z62 2 0).eval t = ((9 / 40) * t ^ 2 + (31 / 40) * t ^ 4 + (-413 / 40) * alpha * t ^ 2 + (413 / 40) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_10, v61_20]
  try simp only [phase61_00, phase61_10, phase61_20]
  try simp only [star_one, star_neg]
  ring
theorem v62_21 (t : ℂ) : (momentPoly 62 z62 2 1).eval t = ((-123) * t + (4871 / 40) * t ^ 3 + (9 / 40) * t ^ 5 + (413 / 40) * alpha * t ^ 3 + (-413 / 40) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_10, v61_11, v61_20, v61_21]
  try simp only [phase61_00, phase61_01, phase61_10, phase61_11, phase61_20, phase61_21]
  try simp only [star_one, star_neg]
  ring
theorem v62_22 (t : ℂ) : (momentPoly 62 z62 2 2).eval t = (7626 + (-14884) * t ^ 2 + (2958347 / 400) * t ^ 4 + (-79057 / 200) * t ^ 6 + (103367 / 400) * t ^ 8) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_10, v61_11, v61_12, v61_20, v61_21, v61_22]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_10, phase61_11, phase61_12, phase61_20, phase61_21, phase61_22]
  try simp only [star_one, star_neg]
  ring
theorem v62_23 (t : ℂ) : (momentPoly 62 z62 2 3).eval t = ((-22510) * t + (1768173 / 40) * t ^ 3 + (-177675957 / 8000) * t ^ 5 + (5007113 / 3200) * t ^ 7 + (-16785651 / 16000) * t ^ 9 + (-1480137 / 16000) * t ^ 11 + (1456937 / 16000) * t ^ 13 + (-149919 / 40) * alpha * t ^ 3 + (59543953 / 8000) * alpha * t ^ 5 + (-11869641 / 3200) * alpha * t ^ 7 + (605619 / 16000) * alpha * t ^ 9 + (-10647 / 16000) * alpha * t ^ 11 + (-367073 / 16000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_03, v61_10, v61_11, v61_12, v61_13, v61_20, v61_21, v61_22, v61_23]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_10, phase61_11, phase61_12, phase61_13, phase61_20, phase61_21, phase61_22, phase61_23]
  try simp only [star_one, star_neg]
  ring
theorem v62_24 (t : ℂ) : (momentPoly 62 z62 2 4).eval t = ((39861 / 4) * t ^ 2 + (132357 / 8) * t ^ 4 + (-10149442973 / 160000) * t ^ 6 + (6270177379 / 160000) * t ^ 8 + (-195222203 / 64000) * t ^ 10 + (-17838981 / 320000) * t ^ 12 + (202625383 / 240000) * t ^ 14 + (96546541 / 320000) * t ^ 18 + (-291217603 / 960000) * t ^ 20 + (1829177 / 4) * alpha * t ^ 2 + (-53466987 / 40) * alpha * t ^ 4 + (207084378923 / 160000) * alpha * t ^ 6 + (-67243563549 / 160000) * alpha * t ^ 8 + (1146118293 / 64000) * alpha * t ^ 10 + (-11930845847 / 960000) * alpha * t ^ 12 + (-23609513 / 240000) * alpha * t ^ 14 + (-39057433 / 960000) * alpha * t ^ 18 + (32882693 / 960000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_03, v61_04, v61_10, v61_11, v61_12, v61_13, v61_14, v61_20, v61_21, v61_22, v61_23, v61_24]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_04, phase61_10, phase61_11, phase61_12, phase61_13, phase61_14, phase61_20, phase61_21, phase61_22, phase61_23, phase61_24]
  try simp only [star_one, star_neg]
  ring
theorem v62_30 (t : ℂ) : (momentPoly 62 z62 3 0).eval t = ((-107 / 40) * t ^ 3 + (147 / 40) * t ^ 5 + (-2) * t ^ 9 + (3689 / 100) * alpha * t ^ 3 + (-15939 / 400) * alpha * t ^ 5 + (1183 / 400) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_10, v61_20, v61_30]
  try simp only [phase61_00, phase61_10, phase61_20, phase61_30]
  try simp only [star_one, star_neg]
  ring
theorem v62_31 (t : ℂ) : (momentPoly 62 z62 3 1).eval t = ((1647 / 40) * t ^ 2 + (4191 / 40) * t ^ 4 + (-5847 / 40) * t ^ 6 + (49 / 40) * t ^ 10 + (-75579 / 40) * alpha * t ^ 2 + (372141 / 100) * alpha * t ^ 4 + (-727461 / 400) * alpha * t ^ 6 + (-5313 / 400) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_10, v61_11, v61_20, v61_21, v61_30, v61_31]
  try simp only [phase61_00, phase61_01, phase61_10, phase61_11, phase61_20, phase61_21, phase61_30, phase61_31]
  try simp only [star_one, star_neg]
  ring
theorem v62_32 (t : ℂ) : (momentPoly 62 z62 3 2).eval t = ((-22510) * t + (1768173 / 40) * t ^ 3 + (-177675957 / 8000) * t ^ 5 + (5007113 / 3200) * t ^ 7 + (-16785651 / 16000) * t ^ 9 + (-1480137 / 16000) * t ^ 11 + (1456937 / 16000) * t ^ 13 + (149919 / 40) * alpha * t ^ 3 + (-59543953 / 8000) * alpha * t ^ 5 + (11869641 / 3200) * alpha * t ^ 7 + (-605619 / 16000) * alpha * t ^ 9 + (10647 / 16000) * alpha * t ^ 11 + (367073 / 16000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_10, v61_11, v61_12, v61_20, v61_21, v61_22, v61_30, v61_31, v61_32]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_10, phase61_11, phase61_12, phase61_20, phase61_21, phase61_22, phase61_30, phase61_31, phase61_32]
  try simp only [star_one, star_neg]
  ring
theorem v62_33 (t : ℂ) : (momentPoly 62 z62 3 3).eval t = (1395620 + (-4052535) * t ^ 2 + (79875369 / 20) * t ^ 4 + (-61831712723 / 40000) * t ^ 6 + (3407871681 / 10000) * t ^ 8 + (-21081585537 / 160000) * t ^ 10 + (37023361 / 20000) * t ^ 12 + (-152503911 / 80000) * t ^ 14 + (-5081533 / 160000) * t ^ 18) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_03, v61_10, v61_11, v61_12, v61_13, v61_20, v61_21, v61_22, v61_23, v61_30, v61_31, v61_32, v61_33]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_10, phase61_11, phase61_12, phase61_13, phase61_20, phase61_21, phase61_22, phase61_23, phase61_30, phase61_31, phase61_32, phase61_33]
  try simp only [star_one, star_neg]
  ring
theorem v62_34 (t : ℂ) : (momentPoly 62 z62 3 4).eval t = ((-5448155) * t + (318314979 / 20) * t ^ 3 + (-63545938749 / 4000) * t ^ 5 + (10490717915347 / 1600000) * t ^ 7 + (-5998896754759 / 3200000) * t ^ 9 + (2160547652959 / 3200000) * t ^ 11 + (478444691791 / 3840000) * t ^ 13 + (-26261179731 / 400000) * t ^ 15 + (16707064487 / 6400000) * t ^ 17 + (-2216364301 / 3200000) * t ^ 19 + (5788357327 / 6400000) * t ^ 21 + (-1712329667 / 19200000) * t ^ 25 + (-26989137 / 20) * alpha * t ^ 3 + (15951421521 / 4000) * alpha * t ^ 5 + (-6303563214143 / 1600000) * alpha * t ^ 7 + (4342449653111 / 3200000) * alpha * t ^ 9 + (-263889298091 / 3200000) * alpha * t ^ 11 + (29957234329 / 3840000) * alpha * t ^ 13 + (8619517999 / 400000) * alpha * t ^ 15 + (-17621476023 / 6400000) * alpha * t ^ 17 + (1781939507 / 9600000) * alpha * t ^ 19 + (69669257 / 6400000) * alpha * t ^ 21 + (-95611839 / 6400000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_03, v61_04, v61_10, v61_11, v61_12, v61_13, v61_14, v61_20, v61_21, v61_22, v61_23, v61_24, v61_30, v61_31, v61_32, v61_33, v61_34]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_04, phase61_10, phase61_11, phase61_12, phase61_13, phase61_14, phase61_20, phase61_21, phase61_22, phase61_23, phase61_24, phase61_30, phase61_31, phase61_32, phase61_33, phase61_34]
  try simp only [star_one, star_neg]
  ring
theorem v62_40 (t : ℂ) : (momentPoly 62 z62 4 0).eval t = ((-7638291 / 8000) * t ^ 4 + (7659691 / 4000) * t ^ 6 + (-15398281 / 16000) * t ^ 8 + (20099 / 12000) * t ^ 10 + (75901 / 48000) * t ^ 16 + (169993 / 8000) * alpha * t ^ 4 + (-465113 / 4000) * alpha * t ^ 6 + (1238963 / 16000) * alpha * t ^ 8 + (328823 / 12000) * alpha * t ^ 10 + (-470783 / 48000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_10, v61_20, v61_30, v61_40]
  try simp only [phase61_00, phase61_10, phase61_20, phase61_30, phase61_40]
  try simp only [star_one, star_neg]
  ring
theorem v62_41 (t : ℂ) : (momentPoly 62 z62 4 1).eval t = ((-12947 / 20) * t ^ 3 + (19842691 / 8000) * t ^ 5 + (-11123491 / 4000) * t ^ 7 + (7440681 / 16000) * t ^ 9 + (5777101 / 12000) * t ^ 11 + (20099 / 48000) * t ^ 17 + (446369 / 50) * alpha * t ^ 3 + (-147388113 / 8000) * alpha * t ^ 5 + (37833353 / 4000) * alpha * t ^ 7 + (11629557 / 16000) * alpha * t ^ 9 + (-8350823 / 12000) * alpha * t ^ 11 + (328823 / 48000) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_10, v61_11, v61_20, v61_21, v61_30, v61_31, v61_40, v61_41]
  try simp only [phase61_00, phase61_01, phase61_10, phase61_11, phase61_20, phase61_21, phase61_30, phase61_31, phase61_40, phase61_41]
  try simp only [star_one, star_neg]
  ring
theorem v62_42 (t : ℂ) : (momentPoly 62 z62 4 2).eval t = ((39861 / 4) * t ^ 2 + (132357 / 8) * t ^ 4 + (-10149442973 / 160000) * t ^ 6 + (6270177379 / 160000) * t ^ 8 + (-195222203 / 64000) * t ^ 10 + (-17838981 / 320000) * t ^ 12 + (202625383 / 240000) * t ^ 14 + (96546541 / 320000) * t ^ 18 + (-291217603 / 960000) * t ^ 20 + (-1829177 / 4) * alpha * t ^ 2 + (53466987 / 40) * alpha * t ^ 4 + (-207084378923 / 160000) * alpha * t ^ 6 + (67243563549 / 160000) * alpha * t ^ 8 + (-1146118293 / 64000) * alpha * t ^ 10 + (11930845847 / 960000) * alpha * t ^ 12 + (23609513 / 240000) * alpha * t ^ 14 + (39057433 / 960000) * alpha * t ^ 18 + (-32882693 / 960000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_10, v61_11, v61_12, v61_20, v61_21, v61_22, v61_30, v61_31, v61_32, v61_40, v61_41, v61_42]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_10, phase61_11, phase61_12, phase61_20, phase61_21, phase61_22, phase61_30, phase61_31, phase61_32, phase61_40, phase61_41, phase61_42]
  try simp only [star_one, star_neg]
  ring
theorem v62_43 (t : ℂ) : (momentPoly 62 z62 4 3).eval t = ((-5448155) * t + (318314979 / 20) * t ^ 3 + (-63545938749 / 4000) * t ^ 5 + (10490717915347 / 1600000) * t ^ 7 + (-5998896754759 / 3200000) * t ^ 9 + (2160547652959 / 3200000) * t ^ 11 + (478444691791 / 3840000) * t ^ 13 + (-26261179731 / 400000) * t ^ 15 + (16707064487 / 6400000) * t ^ 17 + (-2216364301 / 3200000) * t ^ 19 + (5788357327 / 6400000) * t ^ 21 + (-1712329667 / 19200000) * t ^ 25 + (26989137 / 20) * alpha * t ^ 3 + (-15951421521 / 4000) * alpha * t ^ 5 + (6303563214143 / 1600000) * alpha * t ^ 7 + (-4342449653111 / 3200000) * alpha * t ^ 9 + (263889298091 / 3200000) * alpha * t ^ 11 + (-29957234329 / 3840000) * alpha * t ^ 13 + (-8619517999 / 400000) * alpha * t ^ 15 + (17621476023 / 6400000) * alpha * t ^ 17 + (-1781939507 / 9600000) * alpha * t ^ 19 + (-69669257 / 6400000) * alpha * t ^ 21 + (95611839 / 6400000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_03, v61_10, v61_11, v61_12, v61_13, v61_20, v61_21, v61_22, v61_23, v61_30, v61_31, v61_32, v61_33, v61_40, v61_41, v61_42, v61_43]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_10, phase61_11, phase61_12, phase61_13, phase61_20, phase61_21, phase61_22, phase61_23, phase61_30, phase61_31, phase61_32, phase61_33, phase61_40, phase61_41, phase61_42, phase61_43]
  try simp only [star_one, star_neg]
  ring
theorem v62_44 (t : ℂ) : (momentPoly 62 z62 4 4).eval t = (337785610 + (-1297107416) * t ^ 2 + (47534719596 / 25) * t ^ 4 + (-849601767058 / 625) * t ^ 6 + (9147217008202007 / 16000000) * t ^ 8 + (-846557173887477 / 4000000) * t ^ 10 + (7544945461243 / 128000) * t ^ 12 + (-29972599293839 / 8000000) * t ^ 14 + (382585315603897 / 192000000) * t ^ 16 + (154304090257 / 24000000) * t ^ 18 + (3621622480027 / 144000000) * t ^ 20 + (549495754957 / 24000000) * t ^ 22 + (-1027345230067 / 96000000) * t ^ 24 + (-62292306457 / 72000000) * t ^ 26 + (131955715267 / 576000000) * t ^ 32) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_03, v61_04, v61_10, v61_11, v61_12, v61_13, v61_14, v61_20, v61_21, v61_22, v61_23, v61_24, v61_30, v61_31, v61_32, v61_33, v61_34, v61_40, v61_41, v61_42, v61_43, v61_44]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_04, phase61_10, phase61_11, phase61_12, phase61_13, phase61_14, phase61_20, phase61_21, phase61_22, phase61_23, phase61_24, phase61_30, phase61_31, phase61_32, phase61_33, phase61_34, phase61_40, phase61_41, phase61_42, phase61_43, phase61_44]
  try simp only [star_one, star_neg]
  ring
#print axioms v62_00
#print axioms v62_11
#print axioms v62_22
#print axioms v62_33
#print axioms v62_44
end PhotonCertA
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
theorem site63 : ((r ^ 3 * (-1)) : ℂ) = (1) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-3 / 8) + (-1 / 8) * alpha) * alpha_sq
theorem phase63_00 : ((r ^ 3 * (-1)) : ℂ) ^ 0 * star ((r ^ 3 * (-1)) : ℂ) ^ 0 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_01 : ((r ^ 3 * (-1)) : ℂ) ^ 0 * star ((r ^ 3 * (-1)) : ℂ) ^ 1 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_02 : ((r ^ 3 * (-1)) : ℂ) ^ 0 * star ((r ^ 3 * (-1)) : ℂ) ^ 2 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_03 : ((r ^ 3 * (-1)) : ℂ) ^ 0 * star ((r ^ 3 * (-1)) : ℂ) ^ 3 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_04 : ((r ^ 3 * (-1)) : ℂ) ^ 0 * star ((r ^ 3 * (-1)) : ℂ) ^ 4 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_10 : ((r ^ 3 * (-1)) : ℂ) ^ 1 * star ((r ^ 3 * (-1)) : ℂ) ^ 0 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_11 : ((r ^ 3 * (-1)) : ℂ) ^ 1 * star ((r ^ 3 * (-1)) : ℂ) ^ 1 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_12 : ((r ^ 3 * (-1)) : ℂ) ^ 1 * star ((r ^ 3 * (-1)) : ℂ) ^ 2 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_13 : ((r ^ 3 * (-1)) : ℂ) ^ 1 * star ((r ^ 3 * (-1)) : ℂ) ^ 3 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_14 : ((r ^ 3 * (-1)) : ℂ) ^ 1 * star ((r ^ 3 * (-1)) : ℂ) ^ 4 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_20 : ((r ^ 3 * (-1)) : ℂ) ^ 2 * star ((r ^ 3 * (-1)) : ℂ) ^ 0 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_21 : ((r ^ 3 * (-1)) : ℂ) ^ 2 * star ((r ^ 3 * (-1)) : ℂ) ^ 1 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_22 : ((r ^ 3 * (-1)) : ℂ) ^ 2 * star ((r ^ 3 * (-1)) : ℂ) ^ 2 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_23 : ((r ^ 3 * (-1)) : ℂ) ^ 2 * star ((r ^ 3 * (-1)) : ℂ) ^ 3 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_24 : ((r ^ 3 * (-1)) : ℂ) ^ 2 * star ((r ^ 3 * (-1)) : ℂ) ^ 4 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_30 : ((r ^ 3 * (-1)) : ℂ) ^ 3 * star ((r ^ 3 * (-1)) : ℂ) ^ 0 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_31 : ((r ^ 3 * (-1)) : ℂ) ^ 3 * star ((r ^ 3 * (-1)) : ℂ) ^ 1 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_32 : ((r ^ 3 * (-1)) : ℂ) ^ 3 * star ((r ^ 3 * (-1)) : ℂ) ^ 2 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_33 : ((r ^ 3 * (-1)) : ℂ) ^ 3 * star ((r ^ 3 * (-1)) : ℂ) ^ 3 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_34 : ((r ^ 3 * (-1)) : ℂ) ^ 3 * star ((r ^ 3 * (-1)) : ℂ) ^ 4 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_40 : ((r ^ 3 * (-1)) : ℂ) ^ 4 * star ((r ^ 3 * (-1)) : ℂ) ^ 0 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_41 : ((r ^ 3 * (-1)) : ℂ) ^ 4 * star ((r ^ 3 * (-1)) : ℂ) ^ 1 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_42 : ((r ^ 3 * (-1)) : ℂ) ^ 4 * star ((r ^ 3 * (-1)) : ℂ) ^ 2 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_43 : ((r ^ 3 * (-1)) : ℂ) ^ 4 * star ((r ^ 3 * (-1)) : ℂ) ^ 3 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase63_44 : ((r ^ 3 * (-1)) : ℂ) ^ 4 * star ((r ^ 3 * (-1)) : ℂ) ^ 4 = (1) := by
  rw [site63]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
noncomputable def z63 : Fin 63 → ℂ := Fin.snoc z62 (r ^ 3 * (-1))
theorem v63_00 (t : ℂ) : (momentPoly 63 z63 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00]
  try simp only [phase63_00]
  try simp only [star_one, star_neg]
  ring
theorem v63_01 (t : ℂ) : (momentPoly 63 z63 0 1).eval t = 0 := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01]
  try simp only [phase63_00, phase63_01]
  try simp only [star_one, star_neg]
  ring
theorem v63_02 (t : ℂ) : (momentPoly 63 z63 0 2).eval t = ((-71 / 40) * t ^ 2 + (71 / 40) * t ^ 4 + (413 / 40) * alpha * t ^ 2 + (-413 / 40) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02]
  try simp only [phase63_00, phase63_01, phase63_02]
  try simp only [star_one, star_neg]
  ring
theorem v63_03 (t : ℂ) : (momentPoly 63 z63 0 3).eval t = ((-2) * t ^ 3 + 3 * t ^ 5 + (-1) * t ^ 9 + (-1183 / 200) * alpha * t ^ 3 + (3549 / 400) * alpha * t ^ 5 + (-1183 / 400) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_03]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_03]
  try simp only [star_one, star_neg]
  ring
theorem v63_04 (t : ℂ) : (momentPoly 63 z63 0 4).eval t = ((-7723891 / 8000) * t ^ 4 + (7723891 / 4000) * t ^ 6 + (-15323881 / 16000) * t ^ 8 + (-123901 / 12000) * t ^ 10 + (123901 / 48000) * t ^ 16 + (-1350473 / 8000) * alpha * t ^ 4 + (1350473 / 4000) * alpha * t ^ 6 + (-2230163 / 16000) * alpha * t ^ 8 + (-470783 / 12000) * alpha * t ^ 10 + (470783 / 48000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_03, v62_04]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_03, phase63_04]
  try simp only [star_one, star_neg]
  ring
theorem v63_10 (t : ℂ) : (momentPoly 63 z63 1 0).eval t = 0 := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_10]
  try simp only [phase63_00, phase63_10]
  try simp only [star_one, star_neg]
  ring
theorem v63_11 (t : ℂ) : (momentPoly 63 z63 1 1).eval t = (63 + (-63) * t ^ 2) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_10, v62_11]
  try simp only [phase63_00, phase63_01, phase63_10, phase63_11]
  try simp only [star_one, star_neg]
  ring
theorem v63_12 (t : ℂ) : (momentPoly 63 z63 1 2).eval t = 0 := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_10, v62_11, v62_12]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_10, phase63_11, phase63_12]
  try simp only [star_one, star_neg]
  ring
theorem v63_13 (t : ℂ) : (momentPoly 63 z63 1 3).eval t = ((-6603 / 20) * t ^ 2 + (2627 / 4) * t ^ 4 + (-12993 / 40) * t ^ 6 + (-71 / 40) * t ^ 10 + (38409 / 20) * alpha * t ^ 2 + (-15281 / 4) * alpha * t ^ 4 + (75579 / 40) * alpha * t ^ 6 + (413 / 40) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_03, v62_10, v62_11, v62_12, v62_13]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_03, phase63_10, phase63_11, phase63_12, phase63_13]
  try simp only [star_one, star_neg]
  ring
theorem v63_14 (t : ℂ) : (momentPoly 63 z63 1 4).eval t = ((-492) * t ^ 3 + 1222 * t ^ 5 + (-720) * t ^ 7 + (-255) * t ^ 9 + 244 * t ^ 11 + 1 * t ^ 17 + (-145509 / 100) * alpha * t ^ 3 + (722813 / 200) * alpha * t ^ 5 + (-10647 / 5) * alpha * t ^ 7 + (-60333 / 80) * alpha * t ^ 9 + (72163 / 100) * alpha * t ^ 11 + (1183 / 400) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_03, v62_04, v62_10, v62_11, v62_12, v62_13, v62_14]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_03, phase63_04, phase63_10, phase63_11, phase63_12, phase63_13, phase63_14]
  try simp only [star_one, star_neg]
  ring
theorem v63_20 (t : ℂ) : (momentPoly 63 z63 2 0).eval t = ((-71 / 40) * t ^ 2 + (71 / 40) * t ^ 4 + (-413 / 40) * alpha * t ^ 2 + (413 / 40) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_10, v62_20]
  try simp only [phase63_00, phase63_10, phase63_20]
  try simp only [star_one, star_neg]
  ring
theorem v63_21 (t : ℂ) : (momentPoly 63 z63 2 1).eval t = 0 := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_10, v62_11, v62_20, v62_21]
  try simp only [phase63_00, phase63_01, phase63_10, phase63_11, phase63_20, phase63_21]
  try simp only [star_one, star_neg]
  ring
theorem v63_22 (t : ℂ) : (momentPoly 63 z63 2 2).eval t = (7875 + (-15624) * t ^ 2 + (3153187 / 400) * t ^ 4 + (-78787 / 200) * t ^ 6 + (103987 / 400) * t ^ 8) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_10, v62_11, v62_12, v62_20, v62_21, v62_22]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_10, phase63_11, phase63_12, phase63_20, phase63_21, phase63_22]
  try simp only [star_one, star_neg]
  ring
theorem v63_23 (t : ℂ) : (momentPoly 63 z63 2 3).eval t = ((-1437337 / 8000) * t ^ 5 + (1437337 / 3200) * t ^ 7 + (-4312011 / 16000) * t ^ 9 + (-1437337 / 16000) * t ^ 11 + (1437337 / 16000) * t ^ 13 + (249193 / 8000) * alpha * t ^ 5 + (-249193 / 3200) * alpha * t ^ 7 + (747579 / 16000) * alpha * t ^ 9 + (249193 / 16000) * alpha * t ^ 11 + (-249193 / 16000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_03, v62_10, v62_11, v62_12, v62_13, v62_20, v62_21, v62_22, v62_23]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_03, phase63_10, phase63_11, phase63_12, phase63_13, phase63_20, phase63_21, phase63_22, phase63_23]
  try simp only [star_one, star_neg]
  ring
theorem v63_24 (t : ℂ) : (momentPoly 63 z63 2 4).eval t = ((-81224) * t ^ 2 + (9624547 / 40) * t ^ 4 + (-38120851893 / 160000) * t ^ 6 + (13328987679 / 160000) * t ^ 8 + (-93000471 / 12800) * t ^ 10 + (1547790277 / 960000) * t ^ 12 + (290659583 / 240000) * t ^ 14 + (290659583 / 960000) * t ^ 18 + (-288955583 / 960000) * t ^ 20 + 472472 * alpha * t ^ 2 + (-55985041 / 40) * alpha * t ^ 4 + (220116621283 / 160000) * alpha * t ^ 6 + (-72647559849 / 160000) * alpha * t ^ 8 + (1076257069 / 64000) * alpha * t ^ 10 + (-3543986409 / 320000) * alpha * t ^ 12 + (-20707451 / 80000) * alpha * t ^ 14 + (-20707451 / 320000) * alpha * t ^ 18 + (17403451 / 320000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_03, v62_04, v62_10, v62_11, v62_12, v62_13, v62_14, v62_20, v62_21, v62_22, v62_23, v62_24]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_03, phase63_04, phase63_10, phase63_11, phase63_12, phase63_13, phase63_14, phase63_20, phase63_21, phase63_22, phase63_23, phase63_24]
  try simp only [star_one, star_neg]
  ring
theorem v63_30 (t : ℂ) : (momentPoly 63 z63 3 0).eval t = ((-2) * t ^ 3 + 3 * t ^ 5 + (-1) * t ^ 9 + (1183 / 200) * alpha * t ^ 3 + (-3549 / 400) * alpha * t ^ 5 + (1183 / 400) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_10, v62_20, v62_30]
  try simp only [phase63_00, phase63_10, phase63_20, phase63_30]
  try simp only [star_one, star_neg]
  ring
theorem v63_31 (t : ℂ) : (momentPoly 63 z63 3 1).eval t = ((-6603 / 20) * t ^ 2 + (2627 / 4) * t ^ 4 + (-12993 / 40) * t ^ 6 + (-71 / 40) * t ^ 10 + (-38409 / 20) * alpha * t ^ 2 + (15281 / 4) * alpha * t ^ 4 + (-75579 / 40) * alpha * t ^ 6 + (-413 / 40) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_10, v62_11, v62_20, v62_21, v62_30, v62_31]
  try simp only [phase63_00, phase63_01, phase63_10, phase63_11, phase63_20, phase63_21, phase63_30, phase63_31]
  try simp only [star_one, star_neg]
  ring
theorem v63_32 (t : ℂ) : (momentPoly 63 z63 3 2).eval t = ((-1437337 / 8000) * t ^ 5 + (1437337 / 3200) * t ^ 7 + (-4312011 / 16000) * t ^ 9 + (-1437337 / 16000) * t ^ 11 + (1437337 / 16000) * t ^ 13 + (-249193 / 8000) * alpha * t ^ 5 + (249193 / 3200) * alpha * t ^ 7 + (-747579 / 16000) * alpha * t ^ 9 + (-249193 / 16000) * alpha * t ^ 11 + (249193 / 16000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_10, v62_11, v62_12, v62_20, v62_21, v62_22, v62_30, v62_31, v62_32]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_10, phase63_11, phase63_12, phase63_20, phase63_21, phase63_22, phase63_30, phase63_31, phase63_32]
  try simp only [star_one, star_neg]
  ring
theorem v63_33 (t : ℂ) : (momentPoly 63 z63 3 3).eval t = (1464813 + (-4324320) * t ^ 2 + (1731099663 / 400) * t ^ 4 + (-67294196033 / 40000) * t ^ 6 + (14125382499 / 40000) * t ^ 8 + (-22229052597 / 160000) * t ^ 10 + (51630667 / 40000) * t ^ 12 + (-107619801 / 80000) * t ^ 14 + (-5721533 / 160000) * t ^ 18) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_03, v62_10, v62_11, v62_12, v62_13, v62_20, v62_21, v62_22, v62_23, v62_30, v62_31, v62_32, v62_33]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_03, phase63_10, phase63_11, phase63_12, phase63_13, phase63_20, phase63_21, phase63_22, phase63_23, phase63_30, phase63_31, phase63_32, phase63_33]
  try simp only [star_one, star_neg]
  ring
theorem v63_34 (t : ℂ) : (momentPoly 63 z63 3 4).eval t = ((-521753331 / 4000) * t ^ 5 + (732587700477 / 1600000) * t ^ 7 + (-1688566462339 / 3200000) * t ^ 9 + (445107690349 / 3200000) * t ^ 11 + (489539533483 / 3840000) * t ^ 13 + (-13705176193 / 200000) * t ^ 15 + (14044400887 / 6400000) * t ^ 17 + (857967067 / 9600000) * t ^ 19 + (-4435133 / 6400000) * t ^ 21 + (-1720369267 / 19200000) * t ^ 25 + (90457059 / 4000) * alpha * t ^ 5 + (-134240284453 / 1600000) * alpha * t ^ 7 + (343363142171 / 3200000) * alpha * t ^ 9 + (-135353660141 / 3200000) * alpha * t ^ 11 + (-13272536143 / 768000) * alpha * t ^ 13 + (1618704271 / 100000) * alpha * t ^ 15 + (-17236086023 / 6400000) * alpha * t ^ 17 + (191254117 / 9600000) * alpha * t ^ 19 + (340769917 / 6400000) * alpha * t ^ 21 + (-41738317 / 19200000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_03, v62_04, v62_10, v62_11, v62_12, v62_13, v62_14, v62_20, v62_21, v62_22, v62_23, v62_24, v62_30, v62_31, v62_32, v62_33, v62_34]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_03, phase63_04, phase63_10, phase63_11, phase63_12, phase63_13, phase63_14, phase63_20, phase63_21, phase63_22, phase63_23, phase63_24, phase63_30, phase63_31, phase63_32, phase63_33, phase63_34]
  try simp only [star_one, star_neg]
  ring
theorem v63_40 (t : ℂ) : (momentPoly 63 z63 4 0).eval t = ((-7723891 / 8000) * t ^ 4 + (7723891 / 4000) * t ^ 6 + (-15323881 / 16000) * t ^ 8 + (-123901 / 12000) * t ^ 10 + (123901 / 48000) * t ^ 16 + (1350473 / 8000) * alpha * t ^ 4 + (-1350473 / 4000) * alpha * t ^ 6 + (2230163 / 16000) * alpha * t ^ 8 + (470783 / 12000) * alpha * t ^ 10 + (-470783 / 48000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_10, v62_20, v62_30, v62_40]
  try simp only [phase63_00, phase63_10, phase63_20, phase63_30, phase63_40]
  try simp only [star_one, star_neg]
  ring
theorem v63_41 (t : ℂ) : (momentPoly 63 z63 4 1).eval t = ((-492) * t ^ 3 + 1222 * t ^ 5 + (-720) * t ^ 7 + (-255) * t ^ 9 + 244 * t ^ 11 + 1 * t ^ 17 + (145509 / 100) * alpha * t ^ 3 + (-722813 / 200) * alpha * t ^ 5 + (10647 / 5) * alpha * t ^ 7 + (60333 / 80) * alpha * t ^ 9 + (-72163 / 100) * alpha * t ^ 11 + (-1183 / 400) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_10, v62_11, v62_20, v62_21, v62_30, v62_31, v62_40, v62_41]
  try simp only [phase63_00, phase63_01, phase63_10, phase63_11, phase63_20, phase63_21, phase63_30, phase63_31, phase63_40, phase63_41]
  try simp only [star_one, star_neg]
  ring
theorem v63_42 (t : ℂ) : (momentPoly 63 z63 4 2).eval t = ((-81224) * t ^ 2 + (9624547 / 40) * t ^ 4 + (-38120851893 / 160000) * t ^ 6 + (13328987679 / 160000) * t ^ 8 + (-93000471 / 12800) * t ^ 10 + (1547790277 / 960000) * t ^ 12 + (290659583 / 240000) * t ^ 14 + (290659583 / 960000) * t ^ 18 + (-288955583 / 960000) * t ^ 20 + (-472472) * alpha * t ^ 2 + (55985041 / 40) * alpha * t ^ 4 + (-220116621283 / 160000) * alpha * t ^ 6 + (72647559849 / 160000) * alpha * t ^ 8 + (-1076257069 / 64000) * alpha * t ^ 10 + (3543986409 / 320000) * alpha * t ^ 12 + (20707451 / 80000) * alpha * t ^ 14 + (20707451 / 320000) * alpha * t ^ 18 + (-17403451 / 320000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_10, v62_11, v62_12, v62_20, v62_21, v62_22, v62_30, v62_31, v62_32, v62_40, v62_41, v62_42]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_10, phase63_11, phase63_12, phase63_20, phase63_21, phase63_22, phase63_30, phase63_31, phase63_32, phase63_40, phase63_41, phase63_42]
  try simp only [star_one, star_neg]
  ring
theorem v63_43 (t : ℂ) : (momentPoly 63 z63 4 3).eval t = ((-521753331 / 4000) * t ^ 5 + (732587700477 / 1600000) * t ^ 7 + (-1688566462339 / 3200000) * t ^ 9 + (445107690349 / 3200000) * t ^ 11 + (489539533483 / 3840000) * t ^ 13 + (-13705176193 / 200000) * t ^ 15 + (14044400887 / 6400000) * t ^ 17 + (857967067 / 9600000) * t ^ 19 + (-4435133 / 6400000) * t ^ 21 + (-1720369267 / 19200000) * t ^ 25 + (-90457059 / 4000) * alpha * t ^ 5 + (134240284453 / 1600000) * alpha * t ^ 7 + (-343363142171 / 3200000) * alpha * t ^ 9 + (135353660141 / 3200000) * alpha * t ^ 11 + (13272536143 / 768000) * alpha * t ^ 13 + (-1618704271 / 100000) * alpha * t ^ 15 + (17236086023 / 6400000) * alpha * t ^ 17 + (-191254117 / 9600000) * alpha * t ^ 19 + (-340769917 / 6400000) * alpha * t ^ 21 + (41738317 / 19200000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_03, v62_10, v62_11, v62_12, v62_13, v62_20, v62_21, v62_22, v62_23, v62_30, v62_31, v62_32, v62_33, v62_40, v62_41, v62_42, v62_43]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_03, phase63_10, phase63_11, phase63_12, phase63_13, phase63_20, phase63_21, phase63_22, phase63_23, phase63_30, phase63_31, phase63_32, phase63_33, phase63_40, phase63_41, phase63_42, phase63_43]
  try simp only [star_one, star_neg]
  ring
theorem v63_44 (t : ℂ) : (momentPoly 63 z63 4 4).eval t = (360391059 + (-1407156408) * t ^ 2 + (209500897467 / 100) * t ^ 4 + (-756073380891 / 500) * t ^ 6 + (10078296873663367 / 16000000) * t ^ 8 + (-918243746753767 / 4000000) * t ^ 10 + (207476790174667 / 3200000) * t ^ 12 + (-67023311530267 / 24000000) * t ^ 14 + (277342524229657 / 192000000) * t ^ 16 + (975374977267 / 24000000) * t ^ 18 + (3103354551667 / 144000000) * t ^ 20 + (901954653667 / 24000000) * t ^ 22 + (-1561585725667 / 96000000) * t ^ 24 + (-113179820467 / 72000000) * t ^ 26 + (133777339267 / 576000000) * t ^ 32) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_03, v62_04, v62_10, v62_11, v62_12, v62_13, v62_14, v62_20, v62_21, v62_22, v62_23, v62_24, v62_30, v62_31, v62_32, v62_33, v62_34, v62_40, v62_41, v62_42, v62_43, v62_44]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_03, phase63_04, phase63_10, phase63_11, phase63_12, phase63_13, phase63_14, phase63_20, phase63_21, phase63_22, phase63_23, phase63_24, phase63_30, phase63_31, phase63_32, phase63_33, phase63_34, phase63_40, phase63_41, phase63_42, phase63_43, phase63_44]
  try simp only [star_one, star_neg]
  ring
#print axioms v63_00
#print axioms v63_11
#print axioms v63_22
#print axioms v63_33
#print axioms v63_44
end PhotonCertA
