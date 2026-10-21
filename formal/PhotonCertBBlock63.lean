import PhotonCertBBlock42
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v43_02 (t : ℂ) : (momentPoly 43 z43 0 2).eval t = ((-413 / 40) * t ^ 2 + (5903 / 600) * t ^ 4 + (-1 / 75) * c * t ^ 4 + (-71 / 120) * alpha * t ^ 2 + (21 / 200) * alpha * t ^ 4 + (1 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02]
  try simp only [phase43_00, phase43_01, phase43_02]
  try simp only [star_one, star_neg]
  ring
theorem v43_03 (t : ℂ) : (momentPoly 43 z43 0 3).eval t = ((27 / 25) * t ^ 3 + (-77 / 25) * t ^ 5 + 2 * t ^ 9 + (121 / 100) * c * t ^ 3 + (-121 / 100) * c * t ^ 5 + (71 / 1125) * c * t ^ 9 + (531 / 50) * alpha * t ^ 3 + (-3307 / 200) * alpha * t ^ 5 + (51467 / 9000) * alpha * t ^ 9 + (-73 / 75) * alpha * c * t ^ 3 + (73 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_03]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03]
  try simp only [star_one, star_neg]
  linear_combination ((-71 / 1200) * t ^ 3 + (71 / 1200) * t ^ 5 + (-71 / 1200) * c * t ^ 3 + (71 / 1200) * c * t ^ 5) * alpha_sq
theorem v43_04 (t : ℂ) : (momentPoly 43 z43 0 4).eval t = ((2037491 / 8000) * t ^ 4 + (-1943891 / 4000) * t ^ 6 + (4196421 / 16000) * t ^ 8 + (-19583 / 480) * t ^ 10 + (6739633 / 720000) * t ^ 16 + (-3949 / 750) * c * t ^ 4 + (13157 / 1500) * c * t ^ 6 + (-131 / 150) * c * t ^ 8 + (-3949 / 1500) * c * t ^ 10 + (146 / 5625) * c * t ^ 16 + (376653 / 8000) * alpha * t ^ 4 + (-715847 / 12000) * alpha * t ^ 6 + (353201 / 48000) * alpha * t ^ 8 + (218677 / 36000) * alpha * t ^ 10 + (-99131 / 240000) * alpha * t ^ 16 + (-261 / 250) * alpha * c * t ^ 4 + (669 / 500) * alpha * c * t ^ 6 + (57 / 250) * alpha * c * t ^ 8 + (-261 / 500) * alpha * c * t ^ 10 + (146 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_03, v42_04]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04]
  try simp only [star_one, star_neg]
  linear_combination ((1183 / 750) * t ^ 4 + (-383 / 600) * t ^ 6 + (-5183 / 3000) * t ^ 8 + (1183 / 1500) * t ^ 10 + (1183 / 750) * c * t ^ 4 + (-5359 / 2250) * c * t ^ 6 + (71 / 4500) * c * t ^ 8 + (1183 / 1500) * c * t ^ 10) * alpha_sq
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
theorem v43_12 (t : ℂ) : (momentPoly 43 z43 1 2).eval t = ((17 / 2) * t + (-1139 / 120) * t ^ 3 + (131 / 120) * t ^ 5 + (-17 / 6) * c * t + (617 / 200) * c * t ^ 3 + (-57 / 200) * c * t ^ 5 + (17 / 6) * alpha * t + (-503 / 200) * alpha * t ^ 3 + (-57 / 200) * alpha * t ^ 5 + (17 / 6) * alpha * c * t + (-877 / 360) * alpha * c * t ^ 3 + (-131 / 360) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_10, v42_11, v42_12]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12]
  try simp only [star_one, star_neg]
  linear_combination ((71 / 3600) * t ^ 3 + (-71 / 3600) * t ^ 5 + (71 / 3600) * c * t ^ 3 + (-71 / 3600) * c * t ^ 5) * alpha_sq
theorem v43_13 (t : ℂ) : (momentPoly 43 z43 1 3).eval t = ((-26019 / 20) * t ^ 2 + (3735077 / 1500) * t ^ 4 + (-2360109 / 2000) * t ^ 6 + (-19067 / 2000) * t ^ 10 + (-1931 / 3000) * c * t ^ 4 + (211 / 2000) * c * t ^ 6 + (3149 / 6000) * c * t ^ 10 + (-1491 / 20) * alpha * t ^ 2 + (128077 / 1500) * alpha * t ^ 4 + (-22509 / 2000) * alpha * t ^ 6 + (-401 / 6000) * alpha * t ^ 10 + (331 / 9000) * alpha * c * t ^ 4 + (463 / 2000) * alpha * c * t ^ 6 + (-1583 / 6000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_03, v42_10, v42_11, v42_12, v42_13]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13]
  try simp only [star_one, star_neg]
  linear_combination ((-1183 / 3000) * t ^ 4 + (1183 / 2000) * t ^ 6 + (-1183 / 6000) * t ^ 10 + (-1183 / 3000) * c * t ^ 4 + (1183 / 2000) * c * t ^ 6 + (-1183 / 6000) * c * t ^ 10) * alpha_sq
theorem v43_14 (t : ℂ) : (momentPoly 43 z43 1 4).eval t = ((4482 / 25) * t ^ 3 + (-802779 / 1250) * t ^ 5 + (766637 / 1875) * t ^ 7 + (1434929 / 3750) * t ^ 9 + (-1842032 / 5625) * t ^ 11 + (-6217 / 5625) * t ^ 17 + (10043 / 50) * c * t ^ 3 + (-8009713 / 20000) * c * t ^ 5 + (6072739 / 30000) * c * t ^ 7 + (1805233 / 360000) * c * t ^ 9 + (-220123 / 30000) * c * t ^ 11 + (-16519 / 40000) * c * t ^ 17 + (44073 / 25) * alpha * t ^ 3 + (-265388939 / 60000) * alpha * t ^ 5 + (77503339 / 30000) * alpha * t ^ 7 + (358658873 / 360000) * alpha * t ^ 9 + (-27400763 / 30000) * alpha * t ^ 11 + (-253119 / 40000) * alpha * t ^ 17 + (-12118 / 75) * alpha * c * t ^ 3 + (3471937 / 11250) * alpha * c * t ^ 5 + (-763637 / 5625) * alpha * c * t ^ 7 + (-122429 / 11250) * alpha * c * t ^ 9 + (-1768 / 16875) * alpha * c * t ^ 11 + (-5033 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_03, v42_04, v42_10, v42_11, v42_12, v42_13, v42_14]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14]
  try simp only [star_one, star_neg]
  linear_combination ((-5893 / 600) * t ^ 3 + (4313603 / 240000) * t ^ 5 + (-2404409 / 360000) * t ^ 7 + (-1883281 / 1440000) * t ^ 9 + (-209101 / 1080000) * t ^ 11 + (123901 / 4320000) * t ^ 17 + (-5893 / 600) * c * t ^ 3 + (4313603 / 240000) * c * t ^ 5 + (-2404409 / 360000) * c * t ^ 7 + (-1883281 / 1440000) * c * t ^ 9 + (-209101 / 1080000) * c * t ^ 11 + (123901 / 4320000) * c * t ^ 17) * alpha_sq
theorem v43_20 (t : ℂ) : (momentPoly 43 z43 2 0).eval t = ((-413 / 40) * t ^ 2 + (5903 / 600) * t ^ 4 + (-1 / 75) * c * t ^ 4 + (71 / 120) * alpha * t ^ 2 + (-21 / 200) * alpha * t ^ 4 + (-1 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_10, v42_20]
  try simp only [phase43_00, phase43_10, phase43_20]
  try simp only [star_one, star_neg]
  ring
theorem v43_21 (t : ℂ) : (momentPoly 43 z43 2 1).eval t = ((17 / 2) * t + (-1139 / 120) * t ^ 3 + (131 / 120) * t ^ 5 + (-17 / 6) * c * t + (617 / 200) * c * t ^ 3 + (-57 / 200) * c * t ^ 5 + (-17 / 6) * alpha * t + (503 / 200) * alpha * t ^ 3 + (57 / 200) * alpha * t ^ 5 + (-17 / 6) * alpha * c * t + (877 / 360) * alpha * c * t ^ 3 + (131 / 360) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_10, v42_11, v42_20, v42_21]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21]
  try simp only [star_one, star_neg]
  linear_combination ((71 / 3600) * t ^ 3 + (-71 / 3600) * t ^ 5 + (71 / 3600) * c * t ^ 3 + (-71 / 3600) * c * t ^ 5) * alpha_sq
theorem v43_22 (t : ℂ) : (momentPoly 43 z43 2 2).eval t = (3655 + (-7056) * t ^ 2 + (4060387 / 1200) * t ^ 4 + (-106603 / 3000) * t ^ 6 + (107757 / 2000) * t ^ 8 + (292 / 1125) * c * t ^ 6 + (-292 / 1125) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_10, v42_11, v42_12, v42_20, v42_21, v42_22]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22]
  try simp only [star_one, star_neg]
  linear_combination ((-5183 / 9000) * t ^ 6 + (5183 / 9000) * t ^ 8 + (71 / 13500) * c * t ^ 6 + (-71 / 13500) * c * t ^ 8) * alpha_sq
theorem v43_23 (t : ℂ) : (momentPoly 43 z43 2 3).eval t = ((10711 / 10) * t + (-94537 / 40) * t ^ 3 + (8932841 / 6000) * t ^ 5 + (-16759961 / 120000) * t ^ 7 + (-1796917 / 40000) * t ^ 9 + (-11874157 / 360000) * t ^ 11 + (7628833 / 360000) * t ^ 13 + (-10711 / 30) * c * t + (153633 / 200) * c * t ^ 3 + (-5739607 / 12000) * c * t ^ 5 + (2197067 / 30000) * c * t ^ 7 + (-403331 / 60000) * c * t ^ 9 + (-3673 / 45000) * c * t ^ 11 + (3959 / 5625) * c * t ^ 13 + (10711 / 30) * alpha * t + (-125247 / 200) * alpha * t ^ 3 + (31461 / 400) * alpha * t ^ 5 + (43116413 / 120000) * alpha * t ^ 7 + (-20086277 / 120000) * alpha * t ^ 9 + (-20624671 / 360000) * alpha * t ^ 11 + (20143963 / 360000) * alpha * t ^ 13 + (10711 / 30) * alpha * c * t + (-72791 / 120) * alpha * c * t ^ 3 + (5749061 / 36000) * alpha * c * t ^ 5 + (7418399 / 90000) * alpha * c * t ^ 7 + (136577 / 20000) * alpha * c * t ^ 9 + (103291 / 135000) * alpha * c * t ^ 11 + (-2111 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_03, v42_10, v42_11, v42_12, v42_13, v42_20, v42_21, v42_22, v42_23]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23]
  try simp only [star_one, star_neg]
  linear_combination ((5893 / 1200) * t ^ 3 + (-34861 / 3600) * t ^ 5 + (52453 / 5000) * t ^ 7 + (-86359 / 10000) * t ^ 9 + (-5183 / 67500) * t ^ 11 + (808613 / 270000) * t ^ 13 + (5893 / 1200) * c * t ^ 3 + (-34861 / 3600) * c * t ^ 5 + (105317 / 22500) * c * t ^ 7 + (1183 / 15000) * c * t ^ 9 + (71 / 1800) * c * t ^ 11 + (-1183 / 45000) * c * t ^ 13) * alpha_sq
theorem v43_24 (t : ℂ) : (momentPoly 43 z43 2 4).eval t = ((-215999) * t ^ 2 + (1848015967 / 3000) * t ^ 4 + (-92285406513 / 160000) * t ^ 6 + (413484387977 / 2400000) * t ^ 8 + (6312611707 / 4800000) * t ^ 10 + (50187688051 / 14400000) * t ^ 12 + (-1129638623 / 3600000) * t ^ 14 + (-1106611963 / 14400000) * t ^ 18 + (1181851991 / 14400000) * t ^ 20 + (22844 / 375) * c * t ^ 4 + (-236393 / 1000) * c * t ^ 6 + (13882921 / 180000) * c * t ^ 8 + (1549484 / 5625) * c * t ^ 10 + (-53422943 / 360000) * c * t ^ 12 + (-92947 / 3375) * c * t ^ 14 + (-179957 / 135000) * c * t ^ 18 + (50797 / 360000) * c * t ^ 20 + (-37133 / 3) * alpha * t ^ 2 + (77591567 / 3000) * alpha * t ^ 4 + (-7148357923 / 480000) * alpha * t ^ 6 + (2353343279 / 1440000) * alpha * t ^ 8 + (-727096403 / 2880000) * alpha * t ^ 10 + (-148669849 / 2880000) * alpha * t ^ 12 + (152975639 / 2160000) * alpha * t ^ 14 + (85853267 / 8640000) * alpha * t ^ 18 + (-44951887 / 8640000) * alpha * t ^ 20 + (-88444 / 1125) * alpha * c * t ^ 4 + (11198039 / 45000) * alpha * c * t ^ 6 + (-159822479 / 900000) * alpha * c * t ^ 8 + (-2183771 / 28125) * alpha * c * t ^ 10 + (52925827 / 600000) * alpha * c * t ^ 12 + (-312484 / 84375) * alpha * c * t ^ 14 + (34027 / 75000) * alpha * c * t ^ 18 + (45203 / 1080000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_03, v42_04, v42_10, v42_11, v42_12, v42_13, v42_14, v42_20, v42_21, v42_22, v42_23, v42_24]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24]
  try simp only [star_one, star_neg]
  linear_combination ((-48503 / 375) * t ^ 4 + (27238583 / 90000) * t ^ 6 + (-447376957 / 3600000) * t ^ 8 + (-239177653 / 1800000) * t ^ 10 + (178086011 / 2400000) * t ^ 12 + (52164883 / 5400000) * t ^ 14 + (889693 / 1350000) * t ^ 18 + (-14762261 / 21600000) * t ^ 20 + (-48503 / 375) * c * t ^ 4 + (27238583 / 90000) * c * t ^ 6 + (-781962241 / 5400000) * c * t ^ 8 + (-123934837 / 1350000) * c * t ^ 10 + (593284499 / 10800000) * c * t ^ 12 + (8069533 / 1012500) * c * t ^ 14 + (808891 / 2025000) * c * t ^ 18 + (-2797 / 2160000) * c * t ^ 20) * alpha_sq
theorem v43_30 (t : ℂ) : (momentPoly 43 z43 3 0).eval t = ((27 / 25) * t ^ 3 + (-77 / 25) * t ^ 5 + 2 * t ^ 9 + (121 / 100) * c * t ^ 3 + (-121 / 100) * c * t ^ 5 + (71 / 1125) * c * t ^ 9 + (-531 / 50) * alpha * t ^ 3 + (3307 / 200) * alpha * t ^ 5 + (-51467 / 9000) * alpha * t ^ 9 + (73 / 75) * alpha * c * t ^ 3 + (-73 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_10, v42_20, v42_30]
  try simp only [phase43_00, phase43_10, phase43_20, phase43_30]
  try simp only [star_one, star_neg]
  linear_combination ((-71 / 1200) * t ^ 3 + (71 / 1200) * t ^ 5 + (-71 / 1200) * c * t ^ 3 + (71 / 1200) * c * t ^ 5) * alpha_sq
theorem v43_31 (t : ℂ) : (momentPoly 43 z43 3 1).eval t = ((-26019 / 20) * t ^ 2 + (3735077 / 1500) * t ^ 4 + (-2360109 / 2000) * t ^ 6 + (-19067 / 2000) * t ^ 10 + (-1931 / 3000) * c * t ^ 4 + (211 / 2000) * c * t ^ 6 + (3149 / 6000) * c * t ^ 10 + (1491 / 20) * alpha * t ^ 2 + (-128077 / 1500) * alpha * t ^ 4 + (22509 / 2000) * alpha * t ^ 6 + (401 / 6000) * alpha * t ^ 10 + (-331 / 9000) * alpha * c * t ^ 4 + (-463 / 2000) * alpha * c * t ^ 6 + (1583 / 6000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_10, v42_11, v42_20, v42_21, v42_30, v42_31]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21, phase43_30, phase43_31]
  try simp only [star_one, star_neg]
  linear_combination ((-1183 / 3000) * t ^ 4 + (1183 / 2000) * t ^ 6 + (-1183 / 6000) * t ^ 10 + (-1183 / 3000) * c * t ^ 4 + (1183 / 2000) * c * t ^ 6 + (-1183 / 6000) * c * t ^ 10) * alpha_sq
theorem v43_32 (t : ℂ) : (momentPoly 43 z43 3 2).eval t = ((10711 / 10) * t + (-94537 / 40) * t ^ 3 + (8932841 / 6000) * t ^ 5 + (-16759961 / 120000) * t ^ 7 + (-1796917 / 40000) * t ^ 9 + (-11874157 / 360000) * t ^ 11 + (7628833 / 360000) * t ^ 13 + (-10711 / 30) * c * t + (153633 / 200) * c * t ^ 3 + (-5739607 / 12000) * c * t ^ 5 + (2197067 / 30000) * c * t ^ 7 + (-403331 / 60000) * c * t ^ 9 + (-3673 / 45000) * c * t ^ 11 + (3959 / 5625) * c * t ^ 13 + (-10711 / 30) * alpha * t + (125247 / 200) * alpha * t ^ 3 + (-31461 / 400) * alpha * t ^ 5 + (-43116413 / 120000) * alpha * t ^ 7 + (20086277 / 120000) * alpha * t ^ 9 + (20624671 / 360000) * alpha * t ^ 11 + (-20143963 / 360000) * alpha * t ^ 13 + (-10711 / 30) * alpha * c * t + (72791 / 120) * alpha * c * t ^ 3 + (-5749061 / 36000) * alpha * c * t ^ 5 + (-7418399 / 90000) * alpha * c * t ^ 7 + (-136577 / 20000) * alpha * c * t ^ 9 + (-103291 / 135000) * alpha * c * t ^ 11 + (2111 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_10, v42_11, v42_12, v42_20, v42_21, v42_22, v42_30, v42_31, v42_32]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22, phase43_30, phase43_31, phase43_32]
  try simp only [star_one, star_neg]
  linear_combination ((5893 / 1200) * t ^ 3 + (-34861 / 3600) * t ^ 5 + (52453 / 5000) * t ^ 7 + (-86359 / 10000) * t ^ 9 + (-5183 / 67500) * t ^ 11 + (808613 / 270000) * t ^ 13 + (5893 / 1200) * c * t ^ 3 + (-34861 / 3600) * c * t ^ 5 + (105317 / 22500) * c * t ^ 7 + (1183 / 15000) * c * t ^ 9 + (71 / 1800) * c * t ^ 11 + (-1183 / 45000) * c * t ^ 13) * alpha_sq
theorem v43_33 (t : ℂ) : (momentPoly 43 z43 3 3).eval t = (460573 + (-1317960) * t ^ 2 + (499427601 / 400) * t ^ 4 + (-4040224661 / 10000) * t ^ 6 + (311107619 / 10000) * t ^ 8 + (-145229349 / 8000) * t ^ 10 + (19095569 / 37500) * t ^ 12 + (-68483471 / 100000) * t ^ 14 + (35993917 / 600000) * t ^ 18 + (139303 / 3750) * c * t ^ 6 + (-63383 / 1500) * c * t ^ 8 + (10823 / 2500) * c * t ^ 10 + (-656971 / 22500) * c * t ^ 12 + (222937 / 7500) * c * t ^ 14 + (284 / 1125) * c * t ^ 18) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_03, v42_10, v42_11, v42_12, v42_13, v42_20, v42_21, v42_22, v42_23, v42_30, v42_31, v42_32, v42_33]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23, phase43_30, phase43_31, phase43_32, phase43_33]
  try simp only [star_one, star_neg]
  linear_combination ((-3805501 / 20000) * t ^ 6 + (8721343 / 24000) * t ^ 8 + (-6855463 / 40000) * t ^ 10 + (29926231 / 1800000) * t ^ 12 + (-12406373 / 600000) * t ^ 14 + (261443 / 112500) * t ^ 18 + (4664171 / 180000) * c * t ^ 6 + (-4590331 / 72000) * c * t ^ 8 + (4539211 / 120000) * c * t ^ 10 + (1437337 / 120000) * c * t ^ 12 + (-4306331 / 360000) * c * t ^ 14) * alpha_sq
theorem v43_34 (t : ℂ) : (momentPoly 43 z43 3 4).eval t = ((1778533 / 10) * t + (-2907867 / 5) * t ^ 3 + (329179073 / 500) * t ^ 5 + (-304328583407 / 1200000) * t ^ 7 + (-8396208873 / 320000) * t ^ 9 + (4155401001 / 400000) * t ^ 11 + (3673861069619 / 144000000) * t ^ 13 + (-202371202351 / 18000000) * t ^ 15 + (91008592427 / 144000000) * t ^ 17 + (-1002862223 / 54000000) * t ^ 19 + (-1224861231 / 16000000) * t ^ 21 + (5140273297 / 432000000) * t ^ 25 + (-1778533 / 30) * c * t + (4725603 / 25) * c * t ^ 3 + (-430863777 / 2000) * c * t ^ 5 + (49609285169 / 480000) * c * t ^ 7 + (-48698062703 / 2400000) * c * t ^ 9 + (4143862429 / 1600000) * c * t ^ 11 + (18022630711 / 72000000) * c * t ^ 13 + (-3886234103 / 18000000) * c * t ^ 15 + (122564249 / 6000000) * c * t ^ 17 + (-200818201 / 216000000) * c * t ^ 19 + (-1029456461 / 72000000) * c * t ^ 21 + (44519257 / 54000000) * c * t ^ 25 + (1778533 / 30) * alpha * t + (-3852477 / 25) * alpha * t ^ 3 + (5524731 / 100) * alpha * t ^ 5 + (15171159421 / 80000) * alpha * t ^ 7 + (-347020183567 / 1600000) * alpha * t ^ 9 + (13123261151 / 400000) * alpha * t ^ 11 + (8387911845617 / 144000000) * alpha * t ^ 13 + (-409992017813 / 18000000) * alpha * t ^ 15 + (-71050585133 / 48000000) * alpha * t ^ 17 + (957610243 / 10800000) * alpha * t ^ 19 + (-2720760493 / 144000000) * alpha * t ^ 21 + (-23443484773 / 432000000) * alpha * t ^ 25 + (1778533 / 30) * alpha * c * t + (-746327 / 5) * alpha * c * t ^ 3 + (596077891 / 6000) * alpha * c * t ^ 5 + (57499265137 / 7200000) * alpha * c * t ^ 7 + (-33161284577 / 2400000) * alpha * c * t ^ 9 + (-14720301767 / 4800000) * alpha * c * t ^ 11 + (-32561499559 / 72000000) * alpha * c * t ^ 13 + (-1709626379 / 54000000) * alpha * c * t ^ 15 + (437288351 / 54000000) * alpha * c * t ^ 17 + (1988625919 / 129600000) * alpha * c * t ^ 19 + (-485403619 / 72000000) * alpha * c * t ^ 21 + (-30865163 / 162000000) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_03, v42_04, v42_10, v42_11, v42_12, v42_13, v42_14, v42_20, v42_21, v42_22, v42_23, v42_24, v42_30, v42_31, v42_32, v42_33, v42_34]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24, phase43_30, phase43_31, phase43_32, phase43_33, phase43_34]
  try simp only [star_one, star_neg]
  linear_combination ((60421 / 50) * t ^ 3 + (-4233943 / 1200) * t ^ 5 + (29851752323 / 4800000) * t ^ 7 + (-8052528581 / 960000) * t ^ 9 + (9381071357 / 1920000) * t ^ 11 + (459684113611 / 432000000) * t ^ 13 + (-176600248363 / 108000000) * t ^ 15 + (9859509191 / 54000000) * t ^ 17 + (-8642145341 / 1296000000) * t ^ 19 + (39872551 / 48000000) * t ^ 21 + (-456072929 / 162000000) * t ^ 25 + (60421 / 50) * c * t ^ 3 + (-4233943 / 1200) * c * t ^ 5 + (48560994569 / 14400000) * c * t ^ 7 + (-14558437243 / 14400000) * c * t ^ 9 + (-100037849 / 5760000) * c * t ^ 11 + (-174789791 / 5760000) * c * t ^ 13 + (56646743 / 7200000) * c * t ^ 15 + (-1437337 / 900000) * c * t ^ 17 + (-729811103 / 432000000) * c * t ^ 19 + (253476469 / 144000000) * c * t ^ 21 + (-86359 / 1687500) * c * t ^ 25) * alpha_sq
theorem v43_40 (t : ℂ) : (momentPoly 43 z43 4 0).eval t = ((2037491 / 8000) * t ^ 4 + (-1943891 / 4000) * t ^ 6 + (4196421 / 16000) * t ^ 8 + (-19583 / 480) * t ^ 10 + (6739633 / 720000) * t ^ 16 + (-3949 / 750) * c * t ^ 4 + (13157 / 1500) * c * t ^ 6 + (-131 / 150) * c * t ^ 8 + (-3949 / 1500) * c * t ^ 10 + (146 / 5625) * c * t ^ 16 + (-376653 / 8000) * alpha * t ^ 4 + (715847 / 12000) * alpha * t ^ 6 + (-353201 / 48000) * alpha * t ^ 8 + (-218677 / 36000) * alpha * t ^ 10 + (99131 / 240000) * alpha * t ^ 16 + (261 / 250) * alpha * c * t ^ 4 + (-669 / 500) * alpha * c * t ^ 6 + (-57 / 250) * alpha * c * t ^ 8 + (261 / 500) * alpha * c * t ^ 10 + (-146 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_10, v42_20, v42_30, v42_40]
  try simp only [phase43_00, phase43_10, phase43_20, phase43_30, phase43_40]
  try simp only [star_one, star_neg]
  linear_combination ((1183 / 750) * t ^ 4 + (-383 / 600) * t ^ 6 + (-5183 / 3000) * t ^ 8 + (1183 / 1500) * t ^ 10 + (1183 / 750) * c * t ^ 4 + (-5359 / 2250) * c * t ^ 6 + (71 / 4500) * c * t ^ 8 + (1183 / 1500) * c * t ^ 10) * alpha_sq
theorem v43_41 (t : ℂ) : (momentPoly 43 z43 4 1).eval t = ((4482 / 25) * t ^ 3 + (-802779 / 1250) * t ^ 5 + (766637 / 1875) * t ^ 7 + (1434929 / 3750) * t ^ 9 + (-1842032 / 5625) * t ^ 11 + (-6217 / 5625) * t ^ 17 + (10043 / 50) * c * t ^ 3 + (-8009713 / 20000) * c * t ^ 5 + (6072739 / 30000) * c * t ^ 7 + (1805233 / 360000) * c * t ^ 9 + (-220123 / 30000) * c * t ^ 11 + (-16519 / 40000) * c * t ^ 17 + (-44073 / 25) * alpha * t ^ 3 + (265388939 / 60000) * alpha * t ^ 5 + (-77503339 / 30000) * alpha * t ^ 7 + (-358658873 / 360000) * alpha * t ^ 9 + (27400763 / 30000) * alpha * t ^ 11 + (253119 / 40000) * alpha * t ^ 17 + (12118 / 75) * alpha * c * t ^ 3 + (-3471937 / 11250) * alpha * c * t ^ 5 + (763637 / 5625) * alpha * c * t ^ 7 + (122429 / 11250) * alpha * c * t ^ 9 + (1768 / 16875) * alpha * c * t ^ 11 + (5033 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_10, v42_11, v42_20, v42_21, v42_30, v42_31, v42_40, v42_41]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21, phase43_30, phase43_31, phase43_40, phase43_41]
  try simp only [star_one, star_neg]
  linear_combination ((-5893 / 600) * t ^ 3 + (4313603 / 240000) * t ^ 5 + (-2404409 / 360000) * t ^ 7 + (-1883281 / 1440000) * t ^ 9 + (-209101 / 1080000) * t ^ 11 + (123901 / 4320000) * t ^ 17 + (-5893 / 600) * c * t ^ 3 + (4313603 / 240000) * c * t ^ 5 + (-2404409 / 360000) * c * t ^ 7 + (-1883281 / 1440000) * c * t ^ 9 + (-209101 / 1080000) * c * t ^ 11 + (123901 / 4320000) * c * t ^ 17) * alpha_sq
theorem v43_42 (t : ℂ) : (momentPoly 43 z43 4 2).eval t = ((-215999) * t ^ 2 + (1848015967 / 3000) * t ^ 4 + (-92285406513 / 160000) * t ^ 6 + (413484387977 / 2400000) * t ^ 8 + (6312611707 / 4800000) * t ^ 10 + (50187688051 / 14400000) * t ^ 12 + (-1129638623 / 3600000) * t ^ 14 + (-1106611963 / 14400000) * t ^ 18 + (1181851991 / 14400000) * t ^ 20 + (22844 / 375) * c * t ^ 4 + (-236393 / 1000) * c * t ^ 6 + (13882921 / 180000) * c * t ^ 8 + (1549484 / 5625) * c * t ^ 10 + (-53422943 / 360000) * c * t ^ 12 + (-92947 / 3375) * c * t ^ 14 + (-179957 / 135000) * c * t ^ 18 + (50797 / 360000) * c * t ^ 20 + (37133 / 3) * alpha * t ^ 2 + (-77591567 / 3000) * alpha * t ^ 4 + (7148357923 / 480000) * alpha * t ^ 6 + (-2353343279 / 1440000) * alpha * t ^ 8 + (727096403 / 2880000) * alpha * t ^ 10 + (148669849 / 2880000) * alpha * t ^ 12 + (-152975639 / 2160000) * alpha * t ^ 14 + (-85853267 / 8640000) * alpha * t ^ 18 + (44951887 / 8640000) * alpha * t ^ 20 + (88444 / 1125) * alpha * c * t ^ 4 + (-11198039 / 45000) * alpha * c * t ^ 6 + (159822479 / 900000) * alpha * c * t ^ 8 + (2183771 / 28125) * alpha * c * t ^ 10 + (-52925827 / 600000) * alpha * c * t ^ 12 + (312484 / 84375) * alpha * c * t ^ 14 + (-34027 / 75000) * alpha * c * t ^ 18 + (-45203 / 1080000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_10, v42_11, v42_12, v42_20, v42_21, v42_22, v42_30, v42_31, v42_32, v42_40, v42_41, v42_42]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22, phase43_30, phase43_31, phase43_32, phase43_40, phase43_41, phase43_42]
  try simp only [star_one, star_neg]
  linear_combination ((-48503 / 375) * t ^ 4 + (27238583 / 90000) * t ^ 6 + (-447376957 / 3600000) * t ^ 8 + (-239177653 / 1800000) * t ^ 10 + (178086011 / 2400000) * t ^ 12 + (52164883 / 5400000) * t ^ 14 + (889693 / 1350000) * t ^ 18 + (-14762261 / 21600000) * t ^ 20 + (-48503 / 375) * c * t ^ 4 + (27238583 / 90000) * c * t ^ 6 + (-781962241 / 5400000) * c * t ^ 8 + (-123934837 / 1350000) * c * t ^ 10 + (593284499 / 10800000) * c * t ^ 12 + (8069533 / 1012500) * c * t ^ 14 + (808891 / 2025000) * c * t ^ 18 + (-2797 / 2160000) * c * t ^ 20) * alpha_sq
theorem v43_43 (t : ℂ) : (momentPoly 43 z43 4 3).eval t = ((1778533 / 10) * t + (-2907867 / 5) * t ^ 3 + (329179073 / 500) * t ^ 5 + (-304328583407 / 1200000) * t ^ 7 + (-8396208873 / 320000) * t ^ 9 + (4155401001 / 400000) * t ^ 11 + (3673861069619 / 144000000) * t ^ 13 + (-202371202351 / 18000000) * t ^ 15 + (91008592427 / 144000000) * t ^ 17 + (-1002862223 / 54000000) * t ^ 19 + (-1224861231 / 16000000) * t ^ 21 + (5140273297 / 432000000) * t ^ 25 + (-1778533 / 30) * c * t + (4725603 / 25) * c * t ^ 3 + (-430863777 / 2000) * c * t ^ 5 + (49609285169 / 480000) * c * t ^ 7 + (-48698062703 / 2400000) * c * t ^ 9 + (4143862429 / 1600000) * c * t ^ 11 + (18022630711 / 72000000) * c * t ^ 13 + (-3886234103 / 18000000) * c * t ^ 15 + (122564249 / 6000000) * c * t ^ 17 + (-200818201 / 216000000) * c * t ^ 19 + (-1029456461 / 72000000) * c * t ^ 21 + (44519257 / 54000000) * c * t ^ 25 + (-1778533 / 30) * alpha * t + (3852477 / 25) * alpha * t ^ 3 + (-5524731 / 100) * alpha * t ^ 5 + (-15171159421 / 80000) * alpha * t ^ 7 + (347020183567 / 1600000) * alpha * t ^ 9 + (-13123261151 / 400000) * alpha * t ^ 11 + (-8387911845617 / 144000000) * alpha * t ^ 13 + (409992017813 / 18000000) * alpha * t ^ 15 + (71050585133 / 48000000) * alpha * t ^ 17 + (-957610243 / 10800000) * alpha * t ^ 19 + (2720760493 / 144000000) * alpha * t ^ 21 + (23443484773 / 432000000) * alpha * t ^ 25 + (-1778533 / 30) * alpha * c * t + (746327 / 5) * alpha * c * t ^ 3 + (-596077891 / 6000) * alpha * c * t ^ 5 + (-57499265137 / 7200000) * alpha * c * t ^ 7 + (33161284577 / 2400000) * alpha * c * t ^ 9 + (14720301767 / 4800000) * alpha * c * t ^ 11 + (32561499559 / 72000000) * alpha * c * t ^ 13 + (1709626379 / 54000000) * alpha * c * t ^ 15 + (-437288351 / 54000000) * alpha * c * t ^ 17 + (-1988625919 / 129600000) * alpha * c * t ^ 19 + (485403619 / 72000000) * alpha * c * t ^ 21 + (30865163 / 162000000) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_03, v42_10, v42_11, v42_12, v42_13, v42_20, v42_21, v42_22, v42_23, v42_30, v42_31, v42_32, v42_33, v42_40, v42_41, v42_42, v42_43]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23, phase43_30, phase43_31, phase43_32, phase43_33, phase43_40, phase43_41, phase43_42, phase43_43]
  try simp only [star_one, star_neg]
  linear_combination ((60421 / 50) * t ^ 3 + (-4233943 / 1200) * t ^ 5 + (29851752323 / 4800000) * t ^ 7 + (-8052528581 / 960000) * t ^ 9 + (9381071357 / 1920000) * t ^ 11 + (459684113611 / 432000000) * t ^ 13 + (-176600248363 / 108000000) * t ^ 15 + (9859509191 / 54000000) * t ^ 17 + (-8642145341 / 1296000000) * t ^ 19 + (39872551 / 48000000) * t ^ 21 + (-456072929 / 162000000) * t ^ 25 + (60421 / 50) * c * t ^ 3 + (-4233943 / 1200) * c * t ^ 5 + (48560994569 / 14400000) * c * t ^ 7 + (-14558437243 / 14400000) * c * t ^ 9 + (-100037849 / 5760000) * c * t ^ 11 + (-174789791 / 5760000) * c * t ^ 13 + (56646743 / 7200000) * c * t ^ 15 + (-1437337 / 900000) * c * t ^ 17 + (-729811103 / 432000000) * c * t ^ 19 + (253476469 / 144000000) * c * t ^ 21 + (-86359 / 1687500) * c * t ^ 25) * alpha_sq
theorem v43_44 (t : ℂ) : (momentPoly 43 z43 4 4).eval t = (76476919 + (-288334032) * t ^ 2 + (40469877229 / 100) * t ^ 4 + (-127216852289 / 500) * t ^ 6 + (3402260045812123 / 48000000) * t ^ 8 + (-1358186898551 / 96000) * t ^ 10 + (235678574353529 / 48000000) * t ^ 12 + (-3517699140413 / 8000000) * t ^ 14 + (227904297541121 / 576000000) * t ^ 16 + (2009564126039 / 72000000) * t ^ 18 + (-68838909063499 / 2160000000) * t ^ 20 + (-705732971249 / 120000000) * t ^ 22 + (6102594736597 / 1440000000) * t ^ 24 + (-1035843251063 / 1080000000) * t ^ 26 + (391669270031 / 8640000000) * t ^ 32 + (-808824 / 125) * c * t ^ 6 + (5016866188 / 140625) * c * t ^ 8 + (-1748818261 / 37500) * c * t ^ 10 + (-3679221229 / 562500) * c * t ^ 12 + (9190159613 / 225000) * c * t ^ 14 + (-17264754179 / 1125000) * c * t ^ 16 + (-31519219 / 22500) * c * t ^ 18 + (-370068793 / 4218750) * c * t ^ 20 + (204403919 / 16875000) * c * t ^ 22 + (3321079 / 16875000) * c * t ^ 24 + (-1311570247 / 25312500) * c * t ^ 26 + (2939272 / 6328125) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z43, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v42_00, v42_01, v42_02, v42_03, v42_04, v42_10, v42_11, v42_12, v42_13, v42_14, v42_20, v42_21, v42_22, v42_23, v42_24, v42_30, v42_31, v42_32, v42_33, v42_34, v42_40, v42_41, v42_42, v42_43, v42_44]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24, phase43_30, phase43_31, phase43_32, phase43_33, phase43_34, phase43_40, phase43_41, phase43_42, phase43_43, phase43_44]
  try simp only [star_one, star_neg]
  linear_combination ((-16401001 / 300) * t ^ 6 + (1375766183303 / 9000000) * t ^ 8 + (-1275741662329 / 9000000) * t ^ 10 + (167900042137 / 3000000) * t ^ 12 + (-68691257963 / 2700000) * t ^ 14 + (436389836867 / 36000000) * t ^ 16 + (28821000343 / 12000000) * t ^ 18 + (-138656143447 / 90000000) * t ^ 20 + (45261785777 / 270000000) * t ^ 22 + (-67139683081 / 540000000) * t ^ 24 + (5757672341 / 1620000000) * t ^ 26 + (623593733 / 810000000) * t ^ 32 + (11978159 / 750) * c * t ^ 6 + (-1456186890091 / 27000000) * c * t ^ 8 + (4636135749 / 80000) * c * t ^ 10 + (-190438419247 / 18000000) * c * t ^ 12 + (-352955038733 / 21600000) * c * t ^ 14 + (39010781413 / 6000000) * c * t ^ 16 + (3087114293 / 7200000) * c * t ^ 18 + (-13455603149 / 810000000) * c * t ^ 20 + (1172778971 / 1620000000) * c * t ^ 22 + (110117243 / 810000000) * c * t ^ 24 + (77127184279 / 4860000000) * c * t ^ 26 + (9044773 / 607500000) * c * t ^ 32) * alpha_sq
#print axioms v43_00
#print axioms v43_11
#print axioms v43_22
#print axioms v43_33
#print axioms v43_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v44_02 (t : ℂ) : (momentPoly 44 z44 0 2).eval t = ((-6779 / 600) * t ^ 2 + (5611 / 600) * t ^ 4 + (-2 / 75) * c * t ^ 2 + (-2 / 75) * c * t ^ 4 + (-313 / 200) * alpha * t ^ 2 + (-229 / 600) * alpha * t ^ 4 + (2 / 225) * alpha * c * t ^ 2 + (2 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02]
  try simp only [phase43_00, phase43_01, phase43_02]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 450) * t ^ 2 + (1 / 225) * c * t ^ 2 + (1 / 450) * c ^ 2 * t ^ 2) * alpha_sq + ((-1 / 225) * t ^ 2 + (-1 / 225) * alpha * t ^ 2) * c_sq
theorem v44_03 (t : ℂ) : (momentPoly 44 z44 0 3).eval t = ((-46 / 25) * t ^ 3 + (-4 / 25) * t ^ 5 + 2 * t ^ 9 + (121 / 50) * c * t ^ 3 + (-1531 / 750) * c * t ^ 5 + (142 / 1125) * c * t ^ 9 + (941 / 100) * alpha * t ^ 3 + (-49511 / 3000) * alpha * t ^ 5 + (49699 / 9000) * alpha * t ^ 9 + (-146 / 75) * alpha * c * t ^ 3 + (146 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_03]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03]
  try simp only [star_one, star_neg]
  linear_combination ((-71 / 1200) * t ^ 3 + (-229 / 6000) * t ^ 5 + (-71 / 1200) * c * t ^ 3 + (-671 / 18000) * c * t ^ 5 + (1 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-4 / 1125) * alpha * t ^ 5) * c_sq
theorem v44_04 (t : ℂ) : (momentPoly 44 z44 0 4).eval t = ((2411891 / 8000) * t ^ 4 + (-2024963 / 4000) * t ^ 6 + (56310251 / 240000) * t ^ 8 + (-8269729 / 180000) * t ^ 10 + (6417521 / 720000) * t ^ 16 + (-1098 / 125) * c * t ^ 4 + (3949 / 250) * c * t ^ 6 + (-2983 / 1875) * c * t ^ 8 + (-56899 / 11250) * c * t ^ 10 + (292 / 5625) * c * t ^ 16 + (2786407 / 24000) * alpha * t ^ 4 + (-1193143 / 12000) * alpha * t ^ 6 + (-5240171 / 240000) * alpha * t ^ 8 + (245721 / 20000) * alpha * t ^ 10 + (24719 / 720000) * alpha * t ^ 16 + (-318 / 125) * alpha * c * t ^ 4 + (783 / 250) * alpha * c * t ^ 6 + (2857 / 5625) * alpha * c * t ^ 8 + (-32899 / 33750) * alpha * c * t ^ 10 + (292 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_03, v43_04]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04]
  try simp only [star_one, star_neg]
  linear_combination ((177 / 125) * t ^ 4 + (-477 / 1000) * t ^ 6 + (-1533 / 5000) * t ^ 8 + (49699 / 67500) * t ^ 10 + (1447 / 1125) * c * t ^ 4 + (-784 / 375) * c * t ^ 6 + (-229 / 22500) * c * t ^ 8 + (49699 / 67500) * c * t ^ 10 + (-146 / 1125) * c ^ 2 * t ^ 4 + (146 / 1125) * c ^ 2 * t ^ 6 + (2 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((57 / 250) * t ^ 4 + (-57 / 250) * t ^ 6 + (4 / 5625) * t ^ 8 + (-284 / 16875) * t ^ 10 + (131 / 450) * alpha * t ^ 4 + (-131 / 450) * alpha * t ^ 6 + (-4 / 5625) * alpha * t ^ 8 + (284 / 16875) * alpha * t ^ 10) * c_sq
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
theorem v44_12 (t : ℂ) : (momentPoly 44 z44 1 2).eval t = ((87 / 5) * t + (-1139 / 60) * t ^ 3 + (143 / 60) * t ^ 5 + (-29 / 5) * c * t + (617 / 100) * c * t ^ 3 + (-191 / 300) * c * t ^ 5 + (29 / 5) * alpha * t + (-503 / 100) * alpha * t ^ 3 + (-151 / 300) * alpha * t ^ 5 + (29 / 5) * alpha * c * t + (-877 / 180) * alpha * c * t ^ 3 + (-119 / 180) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_10, v43_11, v43_12]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12]
  try simp only [star_one, star_neg]
  linear_combination ((71 / 3600) * t ^ 3 + (229 / 18000) * t ^ 5 + (71 / 3600) * c * t ^ 3 + (671 / 54000) * c * t ^ 5 + (-1 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((2 / 1125) * t ^ 5 + (2 / 3375) * alpha * t ^ 5) * c_sq
theorem v44_13 (t : ℂ) : (momentPoly 44 z44 1 3).eval t = ((-291497 / 200) * t ^ 2 + (3777859 / 1500) * t ^ 4 + (-1059159 / 1000) * t ^ 6 + (-14573 / 1500) * t ^ 10 + (-86 / 25) * c * t ^ 2 + (2989 / 1500) * c * t ^ 4 + (211 / 1000) * c * t ^ 6 + (1023 / 1000) * c * t ^ 10 + (-40377 / 200) * alpha * t ^ 2 + (213859 / 1500) * alpha * t ^ 4 + (52041 / 1000) * alpha * t ^ 6 + (-773 / 1500) * alpha * t ^ 10 + (86 / 75) * alpha * c * t ^ 2 + (-4589 / 4500) * alpha * c * t ^ 4 + (463 / 1000) * alpha * c * t ^ 6 + (-4669 / 9000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_03, v43_10, v43_11, v43_12, v43_13]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13]
  try simp only [star_one, star_neg]
  linear_combination ((43 / 150) * t ^ 2 + (-1211 / 2000) * t ^ 4 + (196 / 375) * t ^ 6 + (-49699 / 270000) * t ^ 10 + (43 / 75) * c * t ^ 2 + (-49 / 60) * c * t ^ 4 + (2723 / 6000) * c * t ^ 6 + (-49699 / 270000) * c * t ^ 10 + (43 / 150) * c ^ 2 * t ^ 2 + (-1267 / 6000) * c ^ 2 * t ^ 4 + (-413 / 6000) * c ^ 2 * t ^ 6) * alpha_sq + ((-43 / 75) * t ^ 2 + (427 / 1500) * t ^ 4 + (413 / 1500) * t ^ 6 + (-71 / 16875) * t ^ 10 + (-43 / 75) * alpha * t ^ 2 + (2449 / 4500) * alpha * t ^ 4 + (71 / 4500) * alpha * t ^ 6 + (-71 / 16875) * alpha * t ^ 10) * c_sq
theorem v44_14 (t : ℂ) : (momentPoly 44 z44 1 4).eval t = ((-1564 / 5) * t ^ 3 + (234321 / 625) * t ^ 5 + (-333626 / 1875) * t ^ 7 + (815579 / 1875) * t ^ 9 + (-1794064 / 5625) * t ^ 11 + (-1184 / 5625) * t ^ 17 + (2057 / 5) * c * t ^ 3 + (-67119577 / 90000) * c * t ^ 5 + (5191099 / 15000) * c * t ^ 7 + (1024913 / 180000) * c * t ^ 9 + (-220123 / 15000) * c * t ^ 11 + (-125951 / 180000) * c * t ^ 17 + (15997 / 10) * alpha * t ^ 3 + (-378008357 / 90000) * alpha * t ^ 5 + (36748279 / 15000) * alpha * t ^ 7 + (177183493 / 180000) * alpha * t ^ 9 + (-12494963 / 15000) * alpha * t ^ 11 + (-1284091 / 180000) * alpha * t ^ 17 + (-4964 / 15) * alpha * c * t ^ 3 + (3515737 / 5625) * alpha * c * t ^ 5 + (-1549174 / 5625) * alpha * c * t ^ 7 + (-100529 / 5625) * alpha * c * t ^ 9 + (-3536 / 16875) * alpha * c * t ^ 11 + (-10066 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_03, v43_04, v43_10, v43_11, v43_12, v43_13, v43_14]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14]
  try simp only [star_one, star_neg]
  linear_combination ((-1207 / 120) * t ^ 3 + (119841 / 80000) * t ^ 5 + (2819399 / 360000) * t ^ 7 + (845167 / 1440000) * t ^ 9 + (-228301 / 1080000) * t ^ 11 + (-24719 / 21600000) * t ^ 17 + (-1207 / 120) * c * t ^ 3 + (3487867 / 2160000) * c * t ^ 5 + (902461 / 120000) * c * t ^ 7 + (384997 / 480000) * c * t ^ 9 + (-247501 / 1080000) * c * t ^ 11 + (-111533 / 64800000) * c * t ^ 17 + (394 / 3375) * c ^ 2 * t ^ 5 + (-1328 / 16875) * c ^ 2 * t ^ 7 + (-292 / 16875) * c ^ 2 * t ^ 9 + (-4 / 225) * c ^ 2 * t ^ 11 + (-146 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((32 / 225) * t ^ 5 + (-1784 / 5625) * t ^ 7 + (584 / 5625) * t ^ 9 + (16 / 225) * t ^ 11 + (-3182 / 16875) * alpha * t ^ 5 + (-431 / 5625) * alpha * t ^ 7 + (242 / 5625) * alpha * t ^ 9 + (1183 / 5625) * alpha * t ^ 11 + (-584 / 253125) * alpha * t ^ 17) * c_sq
theorem v44_20 (t : ℂ) : (momentPoly 44 z44 2 0).eval t = ((-6779 / 600) * t ^ 2 + (5611 / 600) * t ^ 4 + (-2 / 75) * c * t ^ 2 + (-2 / 75) * c * t ^ 4 + (313 / 200) * alpha * t ^ 2 + (229 / 600) * alpha * t ^ 4 + (-2 / 225) * alpha * c * t ^ 2 + (-2 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_10, v43_20]
  try simp only [phase43_00, phase43_10, phase43_20]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 450) * t ^ 2 + (1 / 225) * c * t ^ 2 + (1 / 450) * c ^ 2 * t ^ 2) * alpha_sq + ((-1 / 225) * t ^ 2 + (1 / 225) * alpha * t ^ 2) * c_sq
theorem v44_21 (t : ℂ) : (momentPoly 44 z44 2 1).eval t = ((87 / 5) * t + (-1139 / 60) * t ^ 3 + (143 / 60) * t ^ 5 + (-29 / 5) * c * t + (617 / 100) * c * t ^ 3 + (-191 / 300) * c * t ^ 5 + (-29 / 5) * alpha * t + (503 / 100) * alpha * t ^ 3 + (151 / 300) * alpha * t ^ 5 + (-29 / 5) * alpha * c * t + (877 / 180) * alpha * c * t ^ 3 + (119 / 180) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_10, v43_11, v43_20, v43_21]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21]
  try simp only [star_one, star_neg]
  linear_combination ((71 / 3600) * t ^ 3 + (229 / 18000) * t ^ 5 + (71 / 3600) * c * t ^ 3 + (671 / 54000) * c * t ^ 5 + (-1 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((2 / 1125) * t ^ 5 + (-2 / 3375) * alpha * t ^ 5) * c_sq
theorem v44_22 (t : ℂ) : (momentPoly 44 z44 2 2).eval t = (3828 + (-6880) * t ^ 2 + (6142421 / 2000) * t ^ 4 + (-28387 / 600) * t ^ 6 + (264607 / 6000) * t ^ 8 + (584 / 1125) * c * t ^ 4 + (-584 / 1125) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_10, v43_11, v43_12, v43_20, v43_21, v43_22]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22]
  try simp only [star_one, star_neg]
  linear_combination ((-86 / 225) * t ^ 2 + (503 / 1500) * t ^ 4 + (-4841 / 9000) * t ^ 6 + (511 / 5000) * t ^ 8 + (-172 / 225) * c * t ^ 2 + (2228 / 3375) * c * t ^ 4 + (413 / 4500) * c * t ^ 6 + (229 / 67500) * c * t ^ 8 + (-86 / 225) * c ^ 2 * t ^ 2 + (877 / 2700) * c ^ 2 * t ^ 4 + (131 / 2700) * c ^ 2 * t ^ 6 + (-2 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((344 / 225) * t ^ 2 + (-1559 / 1125) * t ^ 4 + (-121 / 1125) * t ^ 6 + (8 / 16875) * t ^ 8) * c_sq
theorem v44_23 (t : ℂ) : (momentPoly 44 z44 2 3).eval t = ((11224 / 5) * t + (-19363 / 4) * t ^ 3 + (183958499 / 60000) * t ^ 5 + (-17291231 / 40000) * t ^ 7 + (967127 / 120000) * t ^ 9 + (-19453277 / 360000) * t ^ 11 + (4115981 / 360000) * t ^ 13 + (-11224 / 15) * c * t + (31467 / 20) * c * t ^ 3 + (-9769457 / 10000) * c * t ^ 5 + (803791 / 5000) * c * t ^ 7 + (-337339 / 30000) * c * t ^ 9 + (-331 / 5625) * c * t ^ 11 + (7543 / 5625) * c * t ^ 13 + (11224 / 15) * alpha * t + (-25653 / 20) * alpha * t ^ 3 + (16990513 / 60000) * alpha * t ^ 5 + (10264157 / 24000) * alpha * t ^ 7 + (-20278067 / 120000) * alpha * t ^ 9 + (-21061103 / 360000) * alpha * t ^ 11 + (18751871 / 360000) * alpha * t ^ 13 + (11224 / 15) * alpha * c * t + (-14909 / 12) * alpha * c * t ^ 3 + (29862713 / 90000) * alpha * c * t ^ 5 + (271777 / 1800) * alpha * c * t ^ 7 + (1012529 / 90000) * alpha * c * t ^ 9 + (22861 / 16875) * alpha * c * t ^ 11 + (-3097 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_03, v43_10, v43_11, v43_12, v43_13, v43_20, v43_21, v43_22, v43_23]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23]
  try simp only [star_one, star_neg]
  linear_combination ((1207 / 240) * t ^ 3 + (-15337 / 10000) * t ^ 5 + (5617 / 2500) * t ^ 7 + (-126947 / 15000) * t ^ 9 + (-30179 / 270000) * t ^ 11 + (3784937 / 1350000) * t ^ 13 + (1207 / 240) * c * t ^ 3 + (-425161 / 270000) * c * t ^ 5 + (-297829 / 90000) * c * t ^ 7 + (197 / 10000) * c * t ^ 9 + (124 / 5625) * c * t ^ 11 + (-49699 / 2025000) * c * t ^ 13 + (-5531 / 135000) * c ^ 2 * t ^ 5 + (5771 / 270000) * c ^ 2 * t ^ 7 + (71 / 135000) * c ^ 2 * t ^ 9 + (1583 / 90000) * c ^ 2 * t ^ 11) * alpha_sq + ((6331 / 22500) * t ^ 5 + (-10649 / 45000) * t ^ 7 + (292 / 5625) * t ^ 9 + (-3949 / 45000) * t ^ 11 + (-142 / 84375) * t ^ 13 + (7931 / 67500) * alpha * t ^ 5 + (-407 / 9000) * alpha * t ^ 7 + (-292 / 5625) * alpha * t ^ 9 + (-87 / 5000) * alpha * t ^ 11 + (-142 / 253125) * alpha * t ^ 13) * c_sq
theorem v44_24 (t : ℂ) : (momentPoly 44 z44 2 4).eval t = ((-74345293 / 300) * t ^ 2 + (646067991 / 1000) * t ^ 4 + (-1310547483911 / 2400000) * t ^ 6 + (115290228087 / 800000) * t ^ 8 + (1334929329 / 1600000) * t ^ 10 + (45737406767 / 14400000) * t ^ 12 + (-80516429 / 240000) * t ^ 14 + (-235123111 / 2880000) * t ^ 18 + (354036689 / 4800000) * t ^ 20 + (-43868 / 75) * c * t ^ 2 + (155042 / 125) * c * t ^ 4 + (-91641869 / 90000) * c * t ^ 6 + (16356779 / 90000) * c * t ^ 8 + (93382277 / 180000) * c * t ^ 10 + (-10341463 / 36000) * c * t ^ 12 + (-1640731 / 33750) * c * t ^ 14 + (-1593281 / 540000) * c * t ^ 18 + (45997 / 180000) * c * t ^ 20 + (-3432671 / 100) * alpha * t ^ 2 + (56073991 / 1000) * alpha * t ^ 4 + (-711037097 / 57600) * alpha * t ^ 6 + (-12644476237 / 1440000) * alpha * t ^ 8 + (-2152920107 / 2880000) * alpha * t ^ 10 + (-391609639 / 8640000) * alpha * t ^ 12 + (87431561 / 720000) * alpha * t ^ 14 + (1657393 / 115200) * alpha * t ^ 18 + (6738737 / 1728000) * alpha * t ^ 20 + (43868 / 225) * alpha * c * t ^ 2 + (-66614 / 125) * alpha * c * t ^ 4 + (101767417 / 150000) * alpha * c * t ^ 6 + (-53263807 / 150000) * alpha * c * t ^ 8 + (-45204433 / 300000) * alpha * c * t ^ 10 + (468562751 / 2700000) * alpha * c * t ^ 12 + (-1506247 / 168750) * alpha * c * t ^ 14 + (2276503 / 2700000) * alpha * c * t ^ 18 + (50003 / 540000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_03, v43_04, v43_10, v43_11, v43_12, v43_13, v43_14, v43_20, v43_21, v43_22, v43_23, v43_24]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24]
  try simp only [star_one, star_neg]
  linear_combination ((10967 / 225) * t ^ 2 + (-25431 / 125) * t ^ 4 + (276708839 / 900000) * t ^ 6 + (-121691351 / 1200000) * t ^ 8 + (-52330939 / 450000) * t ^ 10 + (1184903683 / 21600000) * t ^ 12 + (3669469 / 360000) * t ^ 14 + (3707443 / 5400000) * t ^ 18 + (-8927651 / 36000000) * t ^ 20 + (21934 / 225) * c * t ^ 2 + (-1372 / 5) * c * t ^ 4 + (166264547 / 540000) * c * t ^ 6 + (-20999823 / 200000) * c * t ^ 8 + (-457418317 / 5400000) * c * t ^ 10 + (556468187 / 10800000) * c * t ^ 12 + (3481519 / 506250) * c * t ^ 14 + (7239253 / 16200000) * c * t ^ 18 + (6803 / 2160000) * c * t ^ 20 + (10967 / 225) * c ^ 2 * t ^ 2 + (-8869 / 125) * c ^ 2 * t ^ 4 + (598109 / 1350000) * c ^ 2 * t ^ 6 + (1503403 / 75000) * c ^ 2 * t ^ 8 + (2200597 / 1350000) * c ^ 2 * t ^ 10 + (109337 / 1012500) * c ^ 2 * t ^ 12 + (-14539 / 1012500) * c ^ 2 * t ^ 14 + (5033 / 253125) * c ^ 2 * t ^ 18 + (-292 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-21934 / 225) * t ^ 2 + (11956 / 125) * t ^ 4 + (26825597 / 300000) * t ^ 6 + (-2499769 / 30000) * t ^ 8 + (-9348883 / 1800000) * t ^ 10 + (1332833 / 1350000) * t ^ 12 + (-2464 / 28125) * t ^ 14 + (-173441 / 5400000) * t ^ 18 + (-584 / 1265625) * t ^ 20 + (-21934 / 225) * alpha * t ^ 2 + (68572 / 375) * alpha * t ^ 4 + (-4732711 / 60000) * alpha * t ^ 6 + (-281631 / 50000) * alpha * t ^ 8 + (-11844281 / 5400000) * alpha * t ^ 10 + (4018211 / 4050000) * alpha * t ^ 12 + (55952 / 253125) * alpha * t ^ 14 + (1229 / 25920) * alpha * t ^ 18 + (-584 / 1265625) * alpha * t ^ 20) * c_sq
theorem v44_30 (t : ℂ) : (momentPoly 44 z44 3 0).eval t = ((-46 / 25) * t ^ 3 + (-4 / 25) * t ^ 5 + 2 * t ^ 9 + (121 / 50) * c * t ^ 3 + (-1531 / 750) * c * t ^ 5 + (142 / 1125) * c * t ^ 9 + (-941 / 100) * alpha * t ^ 3 + (49511 / 3000) * alpha * t ^ 5 + (-49699 / 9000) * alpha * t ^ 9 + (146 / 75) * alpha * c * t ^ 3 + (-146 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_10, v43_20, v43_30]
  try simp only [phase43_00, phase43_10, phase43_20, phase43_30]
  try simp only [star_one, star_neg]
  linear_combination ((-71 / 1200) * t ^ 3 + (-229 / 6000) * t ^ 5 + (-71 / 1200) * c * t ^ 3 + (-671 / 18000) * c * t ^ 5 + (1 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((4 / 1125) * alpha * t ^ 5) * c_sq
theorem v44_31 (t : ℂ) : (momentPoly 44 z44 3 1).eval t = ((-291497 / 200) * t ^ 2 + (3777859 / 1500) * t ^ 4 + (-1059159 / 1000) * t ^ 6 + (-14573 / 1500) * t ^ 10 + (-86 / 25) * c * t ^ 2 + (2989 / 1500) * c * t ^ 4 + (211 / 1000) * c * t ^ 6 + (1023 / 1000) * c * t ^ 10 + (40377 / 200) * alpha * t ^ 2 + (-213859 / 1500) * alpha * t ^ 4 + (-52041 / 1000) * alpha * t ^ 6 + (773 / 1500) * alpha * t ^ 10 + (-86 / 75) * alpha * c * t ^ 2 + (4589 / 4500) * alpha * c * t ^ 4 + (-463 / 1000) * alpha * c * t ^ 6 + (4669 / 9000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_10, v43_11, v43_20, v43_21, v43_30, v43_31]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21, phase43_30, phase43_31]
  try simp only [star_one, star_neg]
  linear_combination ((43 / 150) * t ^ 2 + (-1211 / 2000) * t ^ 4 + (196 / 375) * t ^ 6 + (-49699 / 270000) * t ^ 10 + (43 / 75) * c * t ^ 2 + (-49 / 60) * c * t ^ 4 + (2723 / 6000) * c * t ^ 6 + (-49699 / 270000) * c * t ^ 10 + (43 / 150) * c ^ 2 * t ^ 2 + (-1267 / 6000) * c ^ 2 * t ^ 4 + (-413 / 6000) * c ^ 2 * t ^ 6) * alpha_sq + ((-43 / 75) * t ^ 2 + (427 / 1500) * t ^ 4 + (413 / 1500) * t ^ 6 + (-71 / 16875) * t ^ 10 + (43 / 75) * alpha * t ^ 2 + (-2449 / 4500) * alpha * t ^ 4 + (-71 / 4500) * alpha * t ^ 6 + (71 / 16875) * alpha * t ^ 10) * c_sq
theorem v44_32 (t : ℂ) : (momentPoly 44 z44 3 2).eval t = ((11224 / 5) * t + (-19363 / 4) * t ^ 3 + (183958499 / 60000) * t ^ 5 + (-17291231 / 40000) * t ^ 7 + (967127 / 120000) * t ^ 9 + (-19453277 / 360000) * t ^ 11 + (4115981 / 360000) * t ^ 13 + (-11224 / 15) * c * t + (31467 / 20) * c * t ^ 3 + (-9769457 / 10000) * c * t ^ 5 + (803791 / 5000) * c * t ^ 7 + (-337339 / 30000) * c * t ^ 9 + (-331 / 5625) * c * t ^ 11 + (7543 / 5625) * c * t ^ 13 + (-11224 / 15) * alpha * t + (25653 / 20) * alpha * t ^ 3 + (-16990513 / 60000) * alpha * t ^ 5 + (-10264157 / 24000) * alpha * t ^ 7 + (20278067 / 120000) * alpha * t ^ 9 + (21061103 / 360000) * alpha * t ^ 11 + (-18751871 / 360000) * alpha * t ^ 13 + (-11224 / 15) * alpha * c * t + (14909 / 12) * alpha * c * t ^ 3 + (-29862713 / 90000) * alpha * c * t ^ 5 + (-271777 / 1800) * alpha * c * t ^ 7 + (-1012529 / 90000) * alpha * c * t ^ 9 + (-22861 / 16875) * alpha * c * t ^ 11 + (3097 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_10, v43_11, v43_12, v43_20, v43_21, v43_22, v43_30, v43_31, v43_32]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22, phase43_30, phase43_31, phase43_32]
  try simp only [star_one, star_neg]
  linear_combination ((1207 / 240) * t ^ 3 + (-15337 / 10000) * t ^ 5 + (5617 / 2500) * t ^ 7 + (-126947 / 15000) * t ^ 9 + (-30179 / 270000) * t ^ 11 + (3784937 / 1350000) * t ^ 13 + (1207 / 240) * c * t ^ 3 + (-425161 / 270000) * c * t ^ 5 + (-297829 / 90000) * c * t ^ 7 + (197 / 10000) * c * t ^ 9 + (124 / 5625) * c * t ^ 11 + (-49699 / 2025000) * c * t ^ 13 + (-5531 / 135000) * c ^ 2 * t ^ 5 + (5771 / 270000) * c ^ 2 * t ^ 7 + (71 / 135000) * c ^ 2 * t ^ 9 + (1583 / 90000) * c ^ 2 * t ^ 11) * alpha_sq + ((6331 / 22500) * t ^ 5 + (-10649 / 45000) * t ^ 7 + (292 / 5625) * t ^ 9 + (-3949 / 45000) * t ^ 11 + (-142 / 84375) * t ^ 13 + (-7931 / 67500) * alpha * t ^ 5 + (407 / 9000) * alpha * t ^ 7 + (292 / 5625) * alpha * t ^ 9 + (87 / 5000) * alpha * t ^ 11 + (142 / 253125) * alpha * t ^ 13) * c_sq
theorem v44_33 (t : ℂ) : (momentPoly 44 z44 3 3).eval t = (493856 + (-1316040) * t ^ 2 + (1160917569 / 1000) * t ^ 4 + (-3565125599 / 10000) * t ^ 6 + (1570942757 / 50000) * t ^ 8 + (-2705279937 / 200000) * t ^ 10 + (87296497 / 150000) * t ^ 12 + (-2745837 / 4000) * t ^ 14 + (33010829 / 600000) * t ^ 18 + (24528 / 125) * c * t ^ 4 + (-191059 / 625) * c * t ^ 6 + (15109 / 150) * c * t ^ 8 + (5143 / 1250) * c * t ^ 10 + (-621931 / 11250) * c * t ^ 12 + (74259 / 1250) * c * t ^ 14 + (568 / 1125) * c * t ^ 18) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_03, v43_10, v43_11, v43_12, v43_13, v43_20, v43_21, v43_22, v43_23, v43_30, v43_31, v43_32, v43_33]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23, phase43_30, phase43_31, phase43_32, phase43_33]
  try simp only [star_one, star_neg]
  linear_combination ((-10967 / 150) * t ^ 2 + (31689 / 250) * t ^ 4 + (-1409839 / 6000) * t ^ 6 + (106661483 / 600000) * t ^ 8 + (368393 / 600000) * t ^ 10 + (5627027 / 360000) * t ^ 12 + (-10729597 / 600000) * t ^ 14 + (11374207 / 5062500) * t ^ 18 + (-10967 / 75) * c * t ^ 2 + (31192 / 125) * c * t ^ 4 + (-2716597 / 60000) * c * t ^ 6 + (-724043 / 8000) * c * t ^ 8 + (794099 / 24000) * c * t ^ 10 + (2184543 / 200000) * c * t ^ 12 + (-20794087 / 1800000) * c * t ^ 14 + (-10967 / 150) * c ^ 2 * t ^ 2 + (6139 / 50) * c ^ 2 * t ^ 4 + (-5709761 / 180000) * c ^ 2 * t ^ 6 + (-22256681 / 1350000) * c ^ 2 * t ^ 8 + (-411583 / 300000) * c ^ 2 * t ^ 10 + (-103291 / 675000) * c ^ 2 * t ^ 12 + (21637 / 675000) * c ^ 2 * t ^ 14) * alpha_sq + ((21934 / 75) * t ^ 2 + (-65478 / 125) * t ^ 4 + (954969 / 5000) * t ^ 6 + (3922283 / 112500) * t ^ 8 + (408887 / 75000) * t ^ 10 + (17666 / 28125) * t ^ 12 + (-2428 / 5625) * t ^ 14 + (10082 / 1265625) * t ^ 18) * c_sq
theorem v44_34 (t : ℂ) : (momentPoly 44 z44 3 4).eval t = ((1908599 / 5) * t + (-12202107 / 10) * t ^ 3 + (13774276917 / 10000) * t ^ 5 + (-478853068789 / 800000) * t ^ 7 + (469701839513 / 8000000) * t ^ 9 + (-619395539467 / 24000000) * t ^ 11 + (4814125838189 / 144000000) * t ^ 13 + (-422389973 / 62500) * t ^ 15 + (7007318947 / 144000000) * t ^ 17 + (9056217737 / 216000000) * t ^ 19 + (-6576009157 / 144000000) * t ^ 21 + (8488722329 / 432000000) * t ^ 25 + (-1908599 / 15) * c * t + (19829763 / 50) * c * t ^ 3 + (-2233009343 / 5000) * c * t ^ 5 + (258633840917 / 1200000) * c * t ^ 7 + (-84734608989 / 2000000) * c * t ^ 9 + (16107987009 / 4000000) * c * t ^ 11 + (5509796681 / 12000000) * c * t ^ 13 + (-1260070417 / 3000000) * c * t ^ 15 + (38667379 / 1000000) * c * t ^ 17 + (-434295577 / 108000000) * c * t ^ 19 + (-755003689 / 36000000) * c * t ^ 21 + (42719257 / 27000000) * c * t ^ 25 + (1908599 / 15) * alpha * t + (-16165917 / 50) * alpha * t ^ 3 + (1725787479 / 10000) * alpha * t ^ 5 + (460586846059 / 2400000) * alpha * t ^ 7 + (-1845297030541 / 8000000) * alpha * t ^ 9 + (216194503341 / 8000000) * alpha * t ^ 11 + (8074029677263 / 144000000) * alpha * t ^ 13 + (-1224051301 / 62500) * alpha * t ^ 15 + (-63458248309 / 48000000) * alpha * t ^ 17 + (33359316067 / 216000000) * alpha * t ^ 19 + (-5462746903 / 144000000) * alpha * t ^ 21 + (-21052630541 / 432000000) * alpha * t ^ 25 + (1908599 / 15) * alpha * c * t + (-3131767 / 10) * alpha * c * t ^ 3 + (1033450143 / 5000) * alpha * c * t ^ 5 + (40072581137 / 3600000) * alpha * c * t ^ 7 + (-467246959211 / 18000000) * alpha * c * t ^ 9 + (-62106076531 / 12000000) * alpha * c * t ^ 11 + (-76454019809 / 108000000) * alpha * c * t ^ 13 + (-195003103 / 3000000) * alpha * c * t ^ 15 + (297320159 / 27000000) * alpha * c * t ^ 17 + (9605763323 / 324000000) * alpha * c * t ^ 19 + (-1515595541 / 108000000) * alpha * c * t ^ 21 + (-25465163 / 81000000) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_03, v43_04, v43_10, v43_11, v43_12, v43_13, v43_14, v43_20, v43_21, v43_22, v43_23, v43_24, v43_30, v43_31, v43_32, v43_33, v43_34]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24, phase43_30, phase43_31, phase43_32, phase43_33, phase43_34]
  try simp only [star_one, star_neg]
  linear_combination ((253541 / 200) * t ^ 3 + (-46842833 / 30000) * t ^ 5 + (10775932963 / 4800000) * t ^ 7 + (-462629618323 / 72000000) * t ^ 9 + (689376949679 / 144000000) * t ^ 11 + (152423043493 / 144000000) * t ^ 13 + (-55023739901 / 36000000) * t ^ 15 + (1780222643 / 10800000) * t ^ 17 + (-5966869181 / 1296000000) * t ^ 19 + (-114149561 / 86400000) * t ^ 21 + (-2137991141 / 810000000) * t ^ 25 + (253541 / 200) * c * t ^ 3 + (-140692871 / 90000) * c * t ^ 5 + (-8083600439 / 14400000) * c * t ^ 7 + (59629042829 / 72000000) * c * t ^ 9 + (4549743871 / 144000000) * c * t ^ 11 + (-11278339987 / 1296000000) * c * t ^ 13 + (38079791 / 4000000) * c * t ^ 15 + (-24470603 / 13500000) * c * t ^ 17 + (-434304607 / 432000000) * c * t ^ 19 + (-55025149 / 432000000) * c * t ^ 21 + (-3628027 / 75937500) * c * t ^ 25 + (-41093 / 22500) * c ^ 2 * t ^ 5 + (-8774747 / 1350000) * c ^ 2 * t ^ 7 + (253441033 / 27000000) * c ^ 2 * t ^ 9 + (6313031 / 843750) * c ^ 2 * t ^ 11 + (-478330531 / 54000000) * c ^ 2 * t ^ 13 + (118579 / 337500) * c ^ 2 * t ^ 15 + (4222 / 1265625) * c ^ 2 * t ^ 17 + (-748201 / 20250000) * c ^ 2 * t ^ 19 + (-93203 / 10800000) * c ^ 2 * t ^ 21) * alpha_sq + ((35831 / 1250) * t ^ 5 + (-7213033 / 225000) * t ^ 7 + (3418669 / 140625) * t ^ 9 + (-48551779 / 750000) * t ^ 11 + (22571649 / 500000) * t ^ 13 + (-3112079 / 2250000) * t ^ 15 + (-102457 / 843750) * t ^ 17 + (234263 / 1125000) * t ^ 19 + (-2797 / 900000) * t ^ 21 + (20732 / 6328125) * t ^ 25 + (240293 / 11250) * alpha * t ^ 5 + (-518107 / 25000) * alpha * t ^ 7 + (-44252 / 15625) * alpha * t ^ 9 + (-18068947 / 2250000) * alpha * t ^ 11 + (112749179 / 40500000) * alpha * t ^ 13 + (49104353 / 6750000) * alpha * t ^ 15 + (6511 / 281250) * alpha * t ^ 17 + (644567 / 3375000) * alpha * t ^ 19 + (-98797 / 2700000) * alpha * t ^ 21 + (20732 / 18984375) * alpha * t ^ 25) * c_sq
theorem v44_40 (t : ℂ) : (momentPoly 44 z44 4 0).eval t = ((2411891 / 8000) * t ^ 4 + (-2024963 / 4000) * t ^ 6 + (56310251 / 240000) * t ^ 8 + (-8269729 / 180000) * t ^ 10 + (6417521 / 720000) * t ^ 16 + (-1098 / 125) * c * t ^ 4 + (3949 / 250) * c * t ^ 6 + (-2983 / 1875) * c * t ^ 8 + (-56899 / 11250) * c * t ^ 10 + (292 / 5625) * c * t ^ 16 + (-2786407 / 24000) * alpha * t ^ 4 + (1193143 / 12000) * alpha * t ^ 6 + (5240171 / 240000) * alpha * t ^ 8 + (-245721 / 20000) * alpha * t ^ 10 + (-24719 / 720000) * alpha * t ^ 16 + (318 / 125) * alpha * c * t ^ 4 + (-783 / 250) * alpha * c * t ^ 6 + (-2857 / 5625) * alpha * c * t ^ 8 + (32899 / 33750) * alpha * c * t ^ 10 + (-292 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_10, v43_20, v43_30, v43_40]
  try simp only [phase43_00, phase43_10, phase43_20, phase43_30, phase43_40]
  try simp only [star_one, star_neg]
  linear_combination ((177 / 125) * t ^ 4 + (-477 / 1000) * t ^ 6 + (-1533 / 5000) * t ^ 8 + (49699 / 67500) * t ^ 10 + (1447 / 1125) * c * t ^ 4 + (-784 / 375) * c * t ^ 6 + (-229 / 22500) * c * t ^ 8 + (49699 / 67500) * c * t ^ 10 + (-146 / 1125) * c ^ 2 * t ^ 4 + (146 / 1125) * c ^ 2 * t ^ 6 + (2 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((57 / 250) * t ^ 4 + (-57 / 250) * t ^ 6 + (4 / 5625) * t ^ 8 + (-284 / 16875) * t ^ 10 + (-131 / 450) * alpha * t ^ 4 + (131 / 450) * alpha * t ^ 6 + (4 / 5625) * alpha * t ^ 8 + (-284 / 16875) * alpha * t ^ 10) * c_sq
theorem v44_41 (t : ℂ) : (momentPoly 44 z44 4 1).eval t = ((-1564 / 5) * t ^ 3 + (234321 / 625) * t ^ 5 + (-333626 / 1875) * t ^ 7 + (815579 / 1875) * t ^ 9 + (-1794064 / 5625) * t ^ 11 + (-1184 / 5625) * t ^ 17 + (2057 / 5) * c * t ^ 3 + (-67119577 / 90000) * c * t ^ 5 + (5191099 / 15000) * c * t ^ 7 + (1024913 / 180000) * c * t ^ 9 + (-220123 / 15000) * c * t ^ 11 + (-125951 / 180000) * c * t ^ 17 + (-15997 / 10) * alpha * t ^ 3 + (378008357 / 90000) * alpha * t ^ 5 + (-36748279 / 15000) * alpha * t ^ 7 + (-177183493 / 180000) * alpha * t ^ 9 + (12494963 / 15000) * alpha * t ^ 11 + (1284091 / 180000) * alpha * t ^ 17 + (4964 / 15) * alpha * c * t ^ 3 + (-3515737 / 5625) * alpha * c * t ^ 5 + (1549174 / 5625) * alpha * c * t ^ 7 + (100529 / 5625) * alpha * c * t ^ 9 + (3536 / 16875) * alpha * c * t ^ 11 + (10066 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_10, v43_11, v43_20, v43_21, v43_30, v43_31, v43_40, v43_41]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21, phase43_30, phase43_31, phase43_40, phase43_41]
  try simp only [star_one, star_neg]
  linear_combination ((-1207 / 120) * t ^ 3 + (119841 / 80000) * t ^ 5 + (2819399 / 360000) * t ^ 7 + (845167 / 1440000) * t ^ 9 + (-228301 / 1080000) * t ^ 11 + (-24719 / 21600000) * t ^ 17 + (-1207 / 120) * c * t ^ 3 + (3487867 / 2160000) * c * t ^ 5 + (902461 / 120000) * c * t ^ 7 + (384997 / 480000) * c * t ^ 9 + (-247501 / 1080000) * c * t ^ 11 + (-111533 / 64800000) * c * t ^ 17 + (394 / 3375) * c ^ 2 * t ^ 5 + (-1328 / 16875) * c ^ 2 * t ^ 7 + (-292 / 16875) * c ^ 2 * t ^ 9 + (-4 / 225) * c ^ 2 * t ^ 11 + (-146 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((32 / 225) * t ^ 5 + (-1784 / 5625) * t ^ 7 + (584 / 5625) * t ^ 9 + (16 / 225) * t ^ 11 + (3182 / 16875) * alpha * t ^ 5 + (431 / 5625) * alpha * t ^ 7 + (-242 / 5625) * alpha * t ^ 9 + (-1183 / 5625) * alpha * t ^ 11 + (584 / 253125) * alpha * t ^ 17) * c_sq
theorem v44_42 (t : ℂ) : (momentPoly 44 z44 4 2).eval t = ((-74345293 / 300) * t ^ 2 + (646067991 / 1000) * t ^ 4 + (-1310547483911 / 2400000) * t ^ 6 + (115290228087 / 800000) * t ^ 8 + (1334929329 / 1600000) * t ^ 10 + (45737406767 / 14400000) * t ^ 12 + (-80516429 / 240000) * t ^ 14 + (-235123111 / 2880000) * t ^ 18 + (354036689 / 4800000) * t ^ 20 + (-43868 / 75) * c * t ^ 2 + (155042 / 125) * c * t ^ 4 + (-91641869 / 90000) * c * t ^ 6 + (16356779 / 90000) * c * t ^ 8 + (93382277 / 180000) * c * t ^ 10 + (-10341463 / 36000) * c * t ^ 12 + (-1640731 / 33750) * c * t ^ 14 + (-1593281 / 540000) * c * t ^ 18 + (45997 / 180000) * c * t ^ 20 + (3432671 / 100) * alpha * t ^ 2 + (-56073991 / 1000) * alpha * t ^ 4 + (711037097 / 57600) * alpha * t ^ 6 + (12644476237 / 1440000) * alpha * t ^ 8 + (2152920107 / 2880000) * alpha * t ^ 10 + (391609639 / 8640000) * alpha * t ^ 12 + (-87431561 / 720000) * alpha * t ^ 14 + (-1657393 / 115200) * alpha * t ^ 18 + (-6738737 / 1728000) * alpha * t ^ 20 + (-43868 / 225) * alpha * c * t ^ 2 + (66614 / 125) * alpha * c * t ^ 4 + (-101767417 / 150000) * alpha * c * t ^ 6 + (53263807 / 150000) * alpha * c * t ^ 8 + (45204433 / 300000) * alpha * c * t ^ 10 + (-468562751 / 2700000) * alpha * c * t ^ 12 + (1506247 / 168750) * alpha * c * t ^ 14 + (-2276503 / 2700000) * alpha * c * t ^ 18 + (-50003 / 540000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_10, v43_11, v43_12, v43_20, v43_21, v43_22, v43_30, v43_31, v43_32, v43_40, v43_41, v43_42]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22, phase43_30, phase43_31, phase43_32, phase43_40, phase43_41, phase43_42]
  try simp only [star_one, star_neg]
  linear_combination ((10967 / 225) * t ^ 2 + (-25431 / 125) * t ^ 4 + (276708839 / 900000) * t ^ 6 + (-121691351 / 1200000) * t ^ 8 + (-52330939 / 450000) * t ^ 10 + (1184903683 / 21600000) * t ^ 12 + (3669469 / 360000) * t ^ 14 + (3707443 / 5400000) * t ^ 18 + (-8927651 / 36000000) * t ^ 20 + (21934 / 225) * c * t ^ 2 + (-1372 / 5) * c * t ^ 4 + (166264547 / 540000) * c * t ^ 6 + (-20999823 / 200000) * c * t ^ 8 + (-457418317 / 5400000) * c * t ^ 10 + (556468187 / 10800000) * c * t ^ 12 + (3481519 / 506250) * c * t ^ 14 + (7239253 / 16200000) * c * t ^ 18 + (6803 / 2160000) * c * t ^ 20 + (10967 / 225) * c ^ 2 * t ^ 2 + (-8869 / 125) * c ^ 2 * t ^ 4 + (598109 / 1350000) * c ^ 2 * t ^ 6 + (1503403 / 75000) * c ^ 2 * t ^ 8 + (2200597 / 1350000) * c ^ 2 * t ^ 10 + (109337 / 1012500) * c ^ 2 * t ^ 12 + (-14539 / 1012500) * c ^ 2 * t ^ 14 + (5033 / 253125) * c ^ 2 * t ^ 18 + (-292 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-21934 / 225) * t ^ 2 + (11956 / 125) * t ^ 4 + (26825597 / 300000) * t ^ 6 + (-2499769 / 30000) * t ^ 8 + (-9348883 / 1800000) * t ^ 10 + (1332833 / 1350000) * t ^ 12 + (-2464 / 28125) * t ^ 14 + (-173441 / 5400000) * t ^ 18 + (-584 / 1265625) * t ^ 20 + (21934 / 225) * alpha * t ^ 2 + (-68572 / 375) * alpha * t ^ 4 + (4732711 / 60000) * alpha * t ^ 6 + (281631 / 50000) * alpha * t ^ 8 + (11844281 / 5400000) * alpha * t ^ 10 + (-4018211 / 4050000) * alpha * t ^ 12 + (-55952 / 253125) * alpha * t ^ 14 + (-1229 / 25920) * alpha * t ^ 18 + (584 / 1265625) * alpha * t ^ 20) * c_sq
theorem v44_43 (t : ℂ) : (momentPoly 44 z44 4 3).eval t = ((1908599 / 5) * t + (-12202107 / 10) * t ^ 3 + (13774276917 / 10000) * t ^ 5 + (-478853068789 / 800000) * t ^ 7 + (469701839513 / 8000000) * t ^ 9 + (-619395539467 / 24000000) * t ^ 11 + (4814125838189 / 144000000) * t ^ 13 + (-422389973 / 62500) * t ^ 15 + (7007318947 / 144000000) * t ^ 17 + (9056217737 / 216000000) * t ^ 19 + (-6576009157 / 144000000) * t ^ 21 + (8488722329 / 432000000) * t ^ 25 + (-1908599 / 15) * c * t + (19829763 / 50) * c * t ^ 3 + (-2233009343 / 5000) * c * t ^ 5 + (258633840917 / 1200000) * c * t ^ 7 + (-84734608989 / 2000000) * c * t ^ 9 + (16107987009 / 4000000) * c * t ^ 11 + (5509796681 / 12000000) * c * t ^ 13 + (-1260070417 / 3000000) * c * t ^ 15 + (38667379 / 1000000) * c * t ^ 17 + (-434295577 / 108000000) * c * t ^ 19 + (-755003689 / 36000000) * c * t ^ 21 + (42719257 / 27000000) * c * t ^ 25 + (-1908599 / 15) * alpha * t + (16165917 / 50) * alpha * t ^ 3 + (-1725787479 / 10000) * alpha * t ^ 5 + (-460586846059 / 2400000) * alpha * t ^ 7 + (1845297030541 / 8000000) * alpha * t ^ 9 + (-216194503341 / 8000000) * alpha * t ^ 11 + (-8074029677263 / 144000000) * alpha * t ^ 13 + (1224051301 / 62500) * alpha * t ^ 15 + (63458248309 / 48000000) * alpha * t ^ 17 + (-33359316067 / 216000000) * alpha * t ^ 19 + (5462746903 / 144000000) * alpha * t ^ 21 + (21052630541 / 432000000) * alpha * t ^ 25 + (-1908599 / 15) * alpha * c * t + (3131767 / 10) * alpha * c * t ^ 3 + (-1033450143 / 5000) * alpha * c * t ^ 5 + (-40072581137 / 3600000) * alpha * c * t ^ 7 + (467246959211 / 18000000) * alpha * c * t ^ 9 + (62106076531 / 12000000) * alpha * c * t ^ 11 + (76454019809 / 108000000) * alpha * c * t ^ 13 + (195003103 / 3000000) * alpha * c * t ^ 15 + (-297320159 / 27000000) * alpha * c * t ^ 17 + (-9605763323 / 324000000) * alpha * c * t ^ 19 + (1515595541 / 108000000) * alpha * c * t ^ 21 + (25465163 / 81000000) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_03, v43_10, v43_11, v43_12, v43_13, v43_20, v43_21, v43_22, v43_23, v43_30, v43_31, v43_32, v43_33, v43_40, v43_41, v43_42, v43_43]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23, phase43_30, phase43_31, phase43_32, phase43_33, phase43_40, phase43_41, phase43_42, phase43_43]
  try simp only [star_one, star_neg]
  linear_combination ((253541 / 200) * t ^ 3 + (-46842833 / 30000) * t ^ 5 + (10775932963 / 4800000) * t ^ 7 + (-462629618323 / 72000000) * t ^ 9 + (689376949679 / 144000000) * t ^ 11 + (152423043493 / 144000000) * t ^ 13 + (-55023739901 / 36000000) * t ^ 15 + (1780222643 / 10800000) * t ^ 17 + (-5966869181 / 1296000000) * t ^ 19 + (-114149561 / 86400000) * t ^ 21 + (-2137991141 / 810000000) * t ^ 25 + (253541 / 200) * c * t ^ 3 + (-140692871 / 90000) * c * t ^ 5 + (-8083600439 / 14400000) * c * t ^ 7 + (59629042829 / 72000000) * c * t ^ 9 + (4549743871 / 144000000) * c * t ^ 11 + (-11278339987 / 1296000000) * c * t ^ 13 + (38079791 / 4000000) * c * t ^ 15 + (-24470603 / 13500000) * c * t ^ 17 + (-434304607 / 432000000) * c * t ^ 19 + (-55025149 / 432000000) * c * t ^ 21 + (-3628027 / 75937500) * c * t ^ 25 + (-41093 / 22500) * c ^ 2 * t ^ 5 + (-8774747 / 1350000) * c ^ 2 * t ^ 7 + (253441033 / 27000000) * c ^ 2 * t ^ 9 + (6313031 / 843750) * c ^ 2 * t ^ 11 + (-478330531 / 54000000) * c ^ 2 * t ^ 13 + (118579 / 337500) * c ^ 2 * t ^ 15 + (4222 / 1265625) * c ^ 2 * t ^ 17 + (-748201 / 20250000) * c ^ 2 * t ^ 19 + (-93203 / 10800000) * c ^ 2 * t ^ 21) * alpha_sq + ((35831 / 1250) * t ^ 5 + (-7213033 / 225000) * t ^ 7 + (3418669 / 140625) * t ^ 9 + (-48551779 / 750000) * t ^ 11 + (22571649 / 500000) * t ^ 13 + (-3112079 / 2250000) * t ^ 15 + (-102457 / 843750) * t ^ 17 + (234263 / 1125000) * t ^ 19 + (-2797 / 900000) * t ^ 21 + (20732 / 6328125) * t ^ 25 + (-240293 / 11250) * alpha * t ^ 5 + (518107 / 25000) * alpha * t ^ 7 + (44252 / 15625) * alpha * t ^ 9 + (18068947 / 2250000) * alpha * t ^ 11 + (-112749179 / 40500000) * alpha * t ^ 13 + (-49104353 / 6750000) * alpha * t ^ 15 + (-6511 / 281250) * alpha * t ^ 17 + (-644567 / 3375000) * alpha * t ^ 19 + (98797 / 2700000) * alpha * t ^ 21 + (-20732 / 18984375) * alpha * t ^ 25) * c_sq
theorem v44_44 (t : ℂ) : (momentPoly 44 z44 4 4).eval t = (83978356 + (-294929600) * t ^ 2 + (96393012753 / 250) * t ^ 4 + (-570203937911 / 2500) * t ^ 6 + (1001493487492489 / 16000000) * t ^ 8 + (-146535924350059 / 12000000) * t ^ 10 + (258045959852543 / 80000000) * t ^ 12 + (-186705052844089 / 360000000) * t ^ 14 + (1080210811628101 / 2880000000) * t ^ 16 + (9253520909083 / 360000000) * t ^ 18 + (-55563936584011 / 2160000000) * t ^ 20 + (-223159433291 / 40000000) * t ^ 22 + (208735206781 / 57600000) * t ^ 24 + (-232340965459 / 216000000) * t ^ 26 + (313171843727 / 8640000000) * t ^ 32 + (24439232 / 375) * c * t ^ 4 + (-125334704 / 625) * c * t ^ 6 + (7864881741 / 31250) * c * t ^ 8 + (-7204079711 / 46875) * c * t ^ 10 + (-2474405083 / 312500) * c * t ^ 12 + (332928243037 / 4218750) * c * t ^ 14 + (-262967183737 / 8437500) * c * t ^ 16 + (-9255674189 / 4218750) * c * t ^ 18 + (-3735393137 / 25312500) * c * t ^ 20 + (-77114573 / 4218750) * c * t ^ 22 + (4113 / 62500) * c * t ^ 24 + (-27532931 / 281250) * c * t ^ 26 + (5878544 / 6328125) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z44, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v43_00, v43_01, v43_02, v43_03, v43_04, v43_10, v43_11, v43_12, v43_13, v43_14, v43_20, v43_21, v43_22, v43_23, v43_24, v43_30, v43_31, v43_32, v43_33, v43_34, v43_40, v43_41, v43_42, v43_43, v43_44]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24, phase43_30, phase43_31, phase43_32, phase43_33, phase43_34, phase43_40, phase43_41, phase43_42, phase43_43, phase43_44]
  try simp only [star_one, star_neg]
  linear_combination ((-737324 / 45) * t ^ 2 + (5262386 / 125) * t ^ 4 + (-132462037 / 1500) * t ^ 6 + (91106853533 / 900000) * t ^ 8 + (-43563665783 / 1500000) * t ^ 10 + (13226959751 / 3600000) * t ^ 12 + (-2166780562553 / 90000000) * t ^ 14 + (5309557111481 / 540000000) * t ^ 16 + (3860483099833 / 1620000000) * t ^ 18 + (-607971941179 / 405000000) * t ^ 20 + (15720016639 / 135000000) * t ^ 22 + (-19962760021 / 540000000) * t ^ 24 + (-490614689 / 540000000) * t ^ 26 + (498926323 / 1350000000) * t ^ 32 + (-1474648 / 45) * c * t ^ 2 + (93237344 / 1125) * c * t ^ 4 + (-76752206 / 1875) * c * t ^ 6 + (-1491938479627 / 27000000) * c * t ^ 8 + (230511239201 / 3600000) * c * t ^ 10 + (-2489477624273 / 270000000) * c * t ^ 12 + (-25044301095823 / 1620000000) * c * t ^ 14 + (5173425879427 / 810000000) * c * t ^ 16 + (567093555461 / 1620000000) * c * t ^ 18 + (-67509614551 / 2430000000) * c * t ^ 20 + (14241254651 / 1620000000) * c * t ^ 22 + (51456809 / 270000000) * c * t ^ 24 + (288306557 / 20000000) * c * t ^ 26 + (-1804487 / 3037500000) * c * t ^ 32 + (-737324 / 45) * c ^ 2 * t ^ 2 + (9175174 / 225) * c ^ 2 * t ^ 4 + (-150453463 / 5625) * c ^ 2 * t ^ 6 + (-182841107891 / 81000000) * c ^ 2 * t ^ 8 + (98829621203 / 27000000) * c ^ 2 * t ^ 10 + (8260413147 / 10000000) * c ^ 2 * t ^ 12 + (11247921037 / 90000000) * c ^ 2 * t ^ 14 + (756961493 / 202500000) * c ^ 2 * t ^ 16 + (-132430133 / 67500000) * c ^ 2 * t ^ 18 + (-9899231483 / 2430000000) * c ^ 2 * t ^ 20 + (472619299 / 270000000) * c ^ 2 * t ^ 22 + (-625471 / 101250000) * c ^ 2 * t ^ 24 + (36352427 / 607500000) * c ^ 2 * t ^ 26 + (-42632 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((2949296 / 45) * t ^ 2 + (-65241032 / 375) * t ^ 4 + (259605164 / 1875) * t ^ 6 + (-141179409091 / 6750000) * t ^ 8 + (-828245971 / 150000) * t ^ 10 + (-69276477671 / 22500000) * t ^ 12 + (-46569405043 / 67500000) * t ^ 14 + (2907648101 / 16875000) * t ^ 16 + (187527851 / 25312500) * t ^ 18 + (573161351 / 67500000) * t ^ 20 + (-51969047 / 67500000) * t ^ 22 + (-416641 / 8437500) * t ^ 24 + (-1256407 / 1687500) * t ^ 26 + (170528 / 94921875) * t ^ 32) * c_sq
#print axioms v44_00
#print axioms v44_11
#print axioms v44_22
#print axioms v44_33
#print axioms v44_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v45_02 (t : ℂ) : (momentPoly 45 z45 0 2).eval t = ((-2649 / 200) * t ^ 2 + (1773 / 200) * t ^ 4 + (-2 / 25) * c * t ^ 2 + (-1 / 25) * c * t ^ 4 + (-2107 / 600) * alpha * t ^ 2 + (-521 / 600) * alpha * t ^ 4 + (2 / 75) * alpha * c * t ^ 2 + (1 / 75) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02]
  try simp only [phase43_00, phase43_01, phase43_02]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 225) * t ^ 2 + (2 / 225) * c * t ^ 2 + (1 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((-2 / 225) * t ^ 2 + (-2 / 225) * alpha * t ^ 2) * c_sq
theorem v45_03 (t : ℂ) : (momentPoly 45 z45 0 3).eval t = ((-119 / 25) * t ^ 3 + (69 / 25) * t ^ 5 + 2 * t ^ 9 + (6013 / 1500) * c * t ^ 3 + (-1247 / 500) * c * t ^ 5 + (71 / 375) * c * t ^ 9 + (2633 / 375) * alpha * t ^ 3 + (-17651 / 1000) * alpha * t ^ 5 + (15977 / 3000) * alpha * t ^ 9 + (-73 / 25) * alpha * c * t ^ 3 + (73 / 25) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_03]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03]
  try simp only [star_one, star_neg]
  linear_combination ((-313 / 2000) * t ^ 3 + (-271 / 2000) * t ^ 5 + (-2801 / 18000) * c * t ^ 3 + (-2407 / 18000) * c * t ^ 5 + (1 / 1125) * c ^ 2 * t ^ 3 + (2 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-4 / 1125) * alpha * t ^ 3 + (-8 / 1125) * alpha * t ^ 5) * c_sq
theorem v45_04 (t : ℂ) : (momentPoly 45 z45 0 4).eval t = ((3185747 / 8000) * t ^ 4 + (-11850927 / 20000) * t ^ 6 + (16343321 / 80000) * t ^ 8 + (-3280019 / 60000) * t ^ 10 + (2031803 / 240000) * t ^ 16 + (-2639 / 250) * c * t ^ 4 + (55021 / 2500) * c * t ^ 6 + (-2691 / 1250) * c * t ^ 8 + (-54563 / 7500) * c * t ^ 10 + (146 / 1875) * c * t ^ 16 + (1194587 / 4800) * alpha * t ^ 4 + (-11211059 / 60000) * alpha * t ^ 6 + (-11602123 / 240000) * alpha * t ^ 8 + (3973817 / 180000) * alpha * t ^ 10 + (346831 / 720000) * alpha * t ^ 16 + (-9 / 2) * alpha * c * t ^ 4 + (42701 / 7500) * alpha * c * t ^ 6 + (3149 / 3750) * alpha * c * t ^ 8 + (-30563 / 22500) * alpha * c * t ^ 10 + (146 / 5625) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_03, v44_04]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04]
  try simp only [star_one, star_neg]
  linear_combination ((941 / 750) * t ^ 4 + (106619 / 45000) * t ^ 6 + (16717 / 15000) * t ^ 8 + (46163 / 67500) * t ^ 10 + (2239 / 2250) * c * t ^ 4 + (-22597 / 11250) * c * t ^ 6 + (-271 / 7500) * c * t ^ 8 + (46163 / 67500) * c * t ^ 10 + (-292 / 1125) * c ^ 2 * t ^ 4 + (4384 / 16875) * c ^ 2 * t ^ 6 + (4 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((57 / 125) * t ^ 4 + (-947 / 1875) * t ^ 6 + (8 / 5625) * t ^ 8 + (-568 / 16875) * t ^ 10 + (131 / 225) * alpha * t ^ 4 + (-2999 / 5625) * alpha * t ^ 6 + (-8 / 5625) * alpha * t ^ 8 + (568 / 16875) * alpha * t ^ 10) * c_sq
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
theorem v45_12 (t : ℂ) : (momentPoly 45 z45 1 2).eval t = ((267 / 10) * t + (-223 / 8) * t ^ 3 + (31 / 8) * t ^ 5 + (-89 / 10) * c * t + (1811 / 200) * c * t ^ 3 + (-211 / 200) * c * t ^ 5 + (89 / 10) * alpha * t + (-1469 / 200) * alpha * t ^ 3 + (-131 / 200) * alpha * t ^ 5 + (89 / 10) * alpha * c * t + (-853 / 120) * alpha * c * t ^ 3 + (-107 / 120) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_10, v44_11, v44_12]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12]
  try simp only [star_one, star_neg]
  linear_combination ((313 / 6000) * t ^ 3 + (271 / 6000) * t ^ 5 + (2801 / 54000) * c * t ^ 3 + (2407 / 54000) * c * t ^ 5 + (-1 / 3375) * c ^ 2 * t ^ 3 + (-2 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((2 / 1125) * t ^ 3 + (4 / 1125) * t ^ 5 + (2 / 3375) * alpha * t ^ 3 + (4 / 3375) * alpha * t ^ 5) * c_sq
theorem v45_13 (t : ℂ) : (momentPoly 45 z45 1 3).eval t = ((-87417 / 50) * t ^ 2 + (325608 / 125) * t ^ 4 + (-1770147 / 2000) * t ^ 6 + (-21741 / 2000) * t ^ 10 + (-264 / 25) * c * t ^ 2 + (7909 / 1000) * c * t ^ 4 + (153 / 2000) * c * t ^ 6 + (2989 / 2000) * c * t ^ 10 + (-23177 / 50) * alpha * t ^ 2 + (118474 / 375) * alpha * t ^ 4 + (220253 / 2000) * alpha * t ^ 6 + (-11623 / 6000) * alpha * t ^ 10 + (88 / 25) * alpha * c * t ^ 2 + (-9509 / 3000) * alpha * c * t ^ 4 + (1549 / 2000) * alpha * c * t ^ 6 + (-4589 / 6000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_03, v44_10, v44_11, v44_12, v44_13]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13]
  try simp only [star_one, star_neg]
  linear_combination ((44 / 75) * t ^ 2 + (-49 / 60) * t ^ 4 + (44981 / 90000) * t ^ 6 + (-46163 / 270000) * t ^ 10 + (88 / 75) * c * t ^ 2 + (-1239 / 1000) * c * t ^ 4 + (33191 / 90000) * c * t ^ 6 + (-46163 / 270000) * c * t ^ 10 + (44 / 75) * c ^ 2 * t ^ 2 + (-1267 / 3000) * c ^ 2 * t ^ 4 + (-131 / 1000) * c ^ 2 * t ^ 6) * alpha_sq + ((-88 / 75) * t ^ 2 + (427 / 750) * t ^ 4 + (5903 / 11250) * t ^ 6 + (-142 / 16875) * t ^ 10 + (-88 / 75) * alpha * t ^ 2 + (2449 / 2250) * alpha * t ^ 4 + (7 / 1250) * alpha * t ^ 6 + (-142 / 16875) * alpha * t ^ 10) * c_sq
theorem v45_14 (t : ℂ) : (momentPoly 45 z45 1 4).eval t = ((-20706 / 25) * t ^ 3 + (1765463 / 1250) * t ^ 5 + (-493363 / 625) * t ^ 7 + (623729 / 1250) * t ^ 9 + (-552032 / 1875) * t ^ 11 + (1283 / 1875) * t ^ 17 + (174377 / 250) * c * t ^ 3 + (-64824857 / 60000) * c * t ^ 5 + (4164259 / 10000) * c * t ^ 7 + (126971 / 40000) * c * t ^ 9 + (-614929 / 30000) * c * t ^ 11 + (-103231 / 120000) * c * t ^ 17 + (152714 / 125) * alpha * t ^ 3 + (-234318577 / 60000) * alpha * t ^ 5 + (23820619 / 10000) * alpha * t ^ 7 + (38886531 / 40000) * alpha * t ^ 9 + (-21300929 / 30000) * alpha * t ^ 11 + (-999911 / 120000) * alpha * t ^ 17 + (-12702 / 25) * alpha * c * t ^ 3 + (3515737 / 3750) * alpha * c * t ^ 5 + (-763637 / 1875) * alpha * c * t ^ 7 + (-78629 / 3750) * alpha * c * t ^ 9 + (-1768 / 5625) * alpha * c * t ^ 11 + (-5033 / 5625) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_03, v44_04, v44_10, v44_11, v44_12, v44_13, v44_14]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14]
  try simp only [star_one, star_neg]
  linear_combination ((-27231 / 1000) * t ^ 3 + (-1441751 / 720000) * t ^ 5 + (8978647 / 360000) * t ^ 7 + (15822251 / 7200000) * t ^ 9 + (-860843 / 1800000) * t ^ 11 + (-74327 / 2400000) * t ^ 17 + (-81229 / 3000) * c * t ^ 3 + (-4095301 / 2160000) * c * t ^ 5 + (972127 / 40000) * c * t ^ 7 + (56762497 / 21600000) * c * t ^ 9 + (-8341763 / 16200000) * c * t ^ 11 + (-2081581 / 64800000) * c * t ^ 17 + (58 / 375) * c ^ 2 * t ^ 3 + (3593 / 33750) * c ^ 2 * t ^ 5 + (-233 / 1350) * c ^ 2 * t ^ 7 + (-108 / 3125) * c ^ 2 * t ^ 9 + (-9284 / 253125) * c ^ 2 * t ^ 11 + (-292 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((1016 / 5625) * t ^ 5 + (-2984 / 5625) * t ^ 7 + (1168 / 5625) * t ^ 9 + (32 / 225) * t ^ 11 + (-232 / 375) * alpha * t ^ 3 + (502 / 3375) * alpha * t ^ 5 + (-124 / 1125) * alpha * t ^ 7 + (6076 / 84375) * alpha * t ^ 9 + (102934 / 253125) * alpha * t ^ 11 + (-1168 / 253125) * alpha * t ^ 17) * c_sq
theorem v45_20 (t : ℂ) : (momentPoly 45 z45 2 0).eval t = ((-2649 / 200) * t ^ 2 + (1773 / 200) * t ^ 4 + (-2 / 25) * c * t ^ 2 + (-1 / 25) * c * t ^ 4 + (2107 / 600) * alpha * t ^ 2 + (521 / 600) * alpha * t ^ 4 + (-2 / 75) * alpha * c * t ^ 2 + (-1 / 75) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_10, v44_20]
  try simp only [phase43_00, phase43_10, phase43_20]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 225) * t ^ 2 + (2 / 225) * c * t ^ 2 + (1 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((-2 / 225) * t ^ 2 + (2 / 225) * alpha * t ^ 2) * c_sq
theorem v45_21 (t : ℂ) : (momentPoly 45 z45 2 1).eval t = ((267 / 10) * t + (-223 / 8) * t ^ 3 + (31 / 8) * t ^ 5 + (-89 / 10) * c * t + (1811 / 200) * c * t ^ 3 + (-211 / 200) * c * t ^ 5 + (-89 / 10) * alpha * t + (1469 / 200) * alpha * t ^ 3 + (131 / 200) * alpha * t ^ 5 + (-89 / 10) * alpha * c * t + (853 / 120) * alpha * c * t ^ 3 + (107 / 120) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_10, v44_11, v44_20, v44_21]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21]
  try simp only [star_one, star_neg]
  linear_combination ((313 / 6000) * t ^ 3 + (271 / 6000) * t ^ 5 + (2801 / 54000) * c * t ^ 3 + (2407 / 54000) * c * t ^ 5 + (-1 / 3375) * c ^ 2 * t ^ 3 + (-2 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((2 / 1125) * t ^ 3 + (4 / 1125) * t ^ 5 + (-2 / 3375) * alpha * t ^ 3 + (-4 / 3375) * alpha * t ^ 5) * c_sq
theorem v45_22 (t : ℂ) : (momentPoly 45 z45 2 2).eval t = (4005 + (-6336) * t ^ 2 + (14677919 / 6000) * t ^ 4 + (-211931 / 3000) * t ^ 6 + (217943 / 6000) * t ^ 8 + (584 / 375) * c * t ^ 4 + (-292 / 375) * c * t ^ 6 + (-292 / 375) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_10, v44_11, v44_12, v44_20, v44_21, v44_22]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22]
  try simp only [star_one, star_neg]
  linear_combination ((-176 / 225) * t ^ 2 + (503 / 750) * t ^ 4 + (-65527 / 45000) * t ^ 6 + (-16717 / 45000) * t ^ 8 + (-352 / 225) * c * t ^ 2 + (4456 / 3375) * c * t ^ 4 + (4001 / 22500) * c * t ^ 6 + (271 / 22500) * c * t ^ 8 + (-176 / 225) * c ^ 2 * t ^ 2 + (877 / 1350) * c ^ 2 * t ^ 4 + (8917 / 101250) * c ^ 2 * t ^ 6 + (-4 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((704 / 225) * t ^ 2 + (-3118 / 1125) * t ^ 4 + (-3014 / 16875) * t ^ 6 + (16 / 16875) * t ^ 8) * c_sq
theorem v45_23 (t : ℂ) : (momentPoly 45 z45 2 3).eval t = ((35247 / 10) * t + (-58203 / 8) * t ^ 3 + (2702429 / 600) * t ^ 5 + (-84544777 / 120000) * t ^ 7 + (2691983 / 40000) * t ^ 9 + (-2249003 / 24000) * t ^ 11 + (225043 / 120000) * t ^ 13 + (-11749 / 10) * c * t + (472671 / 200) * c * t ^ 3 + (-17346181 / 12000) * c * t ^ 5 + (7840429 / 30000) * c * t ^ 7 + (-283347 / 20000) * c * t ^ 9 + (-79 / 600) * c * t ^ 11 + (3584 / 1875) * c * t ^ 13 + (11749 / 10) * alpha * t + (-383409 / 200) * alpha * t ^ 3 + (2309449 / 5000) * alpha * t ^ 5 + (19490191 / 40000) * alpha * t ^ 7 + (-294179 / 1600) * alpha * t ^ 9 + (-2533039 / 40000) * alpha * t ^ 11 + (1931531 / 40000) * alpha * t ^ 13 + (11749 / 10) * alpha * c * t + (-74211 / 40) * alpha * c * t ^ 3 + (85303691 / 180000) * alpha * c * t ^ 5 + (17901689 / 90000) * alpha * c * t ^ 7 + (166373 / 12000) * alpha * c * t ^ 9 + (88597 / 45000) * alpha * c * t ^ 11 + (-986 / 5625) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_03, v44_10, v44_11, v44_12, v44_13, v44_20, v44_21, v44_22, v44_23]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23]
  try simp only [star_one, star_neg]
  linear_combination ((27231 / 2000) * t ^ 3 + (-84041 / 90000) * t ^ 5 + (-18701 / 3000) * t ^ 7 + (-3944993 / 450000) * t ^ 9 + (-6827 / 25000) * t ^ 11 + (1175603 / 450000) * t ^ 13 + (81229 / 6000) * c * t ^ 3 + (-255047 / 270000) * c * t ^ 5 + (-519113 / 45000) * c * t ^ 7 + (10499 / 168750) * c * t ^ 9 + (143141 / 2025000) * c * t ^ 11 + (-46163 / 2025000) * c * t ^ 13 + (-29 / 375) * c ^ 2 * t ^ 3 + (-731 / 67500) * c ^ 2 * t ^ 5 + (5771 / 135000) * c ^ 2 * t ^ 7 + (11 / 67500) * c ^ 2 * t ^ 9 + (4669 / 135000) * c ^ 2 * t ^ 11) * alpha_sq + ((58 / 125) * t ^ 3 + (947 / 11250) * t ^ 5 + (-9481 / 22500) * t ^ 7 + (976 / 9375) * t ^ 9 + (-58603 / 337500) * t ^ 11 + (-284 / 84375) * t ^ 13 + (58 / 375) * alpha * t ^ 3 + (4883 / 33750) * alpha * t ^ 5 + (-3203 / 22500) * alpha * t ^ 7 + (-8752 / 84375) * alpha * t ^ 9 + (-34603 / 1012500) * alpha * t ^ 11 + (-284 / 253125) * alpha * t ^ 13) * c_sq
theorem v45_24 (t : ℂ) : (momentPoly 45 z45 2 4).eval t = ((-15213207 / 50) * t ^ 2 + (697222401 / 1000) * t ^ 4 + (-1188569254583 / 2400000) * t ^ 6 + (79545712923 / 800000) * t ^ 8 + (-1352971309 / 4800000) * t ^ 10 + (46064500363 / 14400000) * t ^ 12 + (-1415269351 / 3600000) * t ^ 14 + (-1387956691 / 14400000) * t ^ 18 + (928352143 / 14400000) * t ^ 20 + (-45944 / 25) * c * t ^ 2 + (452242 / 125) * c * t ^ 4 + (-72106739 / 30000) * c * t ^ 6 + (831589 / 2400) * c * t ^ 8 + (14790807 / 20000) * c * t ^ 10 + (-48508967 / 120000) * c * t ^ 12 + (-79429 / 1250) * c * t ^ 14 + (-295951 / 60000) * c * t ^ 18 + (41197 / 120000) * c * t ^ 20 + (-12100501 / 150) * alpha * t ^ 2 + (384473203 / 3000) * alpha * t ^ 4 + (-13909870619 / 480000) * alpha * t ^ 6 + (-8534722931 / 480000) * alpha * t ^ 8 + (-1500555001 / 960000) * alpha * t ^ 10 + (137189971 / 576000) * alpha * t ^ 12 + (146615797 / 720000) * alpha * t ^ 14 + (75747961 / 2880000) * alpha * t ^ 18 + (34643219 / 2880000) * alpha * t ^ 20 + (45944 / 75) * alpha * c * t ^ 2 + (-521042 / 375) * alpha * c * t ^ 4 + (65194087 / 50000) * alpha * c * t ^ 6 + (-6516979 / 12000) * alpha * c * t ^ 8 + (-12973943 / 60000) * alpha * c * t ^ 10 + (449539459 / 1800000) * alpha * c * t ^ 12 + (-875279 / 56250) * alpha * c * t ^ 14 + (1075531 / 900000) * alpha * c * t ^ 18 + (54803 / 360000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_03, v44_04, v44_10, v44_11, v44_12, v44_13, v44_14, v44_20, v44_21, v44_22, v44_23, v44_24]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24]
  try simp only [star_one, star_neg]
  linear_combination ((22972 / 225) * t ^ 2 + (-4214 / 15) * t ^ 4 + (107919689 / 337500) * t ^ 6 + (-179281613 / 3600000) * t ^ 8 + (-5732461 / 43200) * t ^ 10 + (3580674751 / 108000000) * t ^ 12 + (338278687 / 27000000) * t ^ 14 + (15872429 / 13500000) * t ^ 18 + (20245399 / 108000000) * t ^ 20 + (45944 / 225) * c * t ^ 2 + (-53277 / 125) * c * t ^ 4 + (43444499 / 135000) * c * t ^ 6 + (-375648089 / 5400000) * c * t ^ 8 + (-23894891 / 300000) * c * t ^ 10 + (19199419 / 432000) * c * t ^ 12 + (1981861 / 337500) * c * t ^ 14 + (1417283 / 2700000) * c * t ^ 18 + (16403 / 2160000) * c * t ^ 20 + (22972 / 225) * c ^ 2 * t ^ 2 + (-54481 / 375) * c ^ 2 * t ^ 4 + (461039 / 225000) * c ^ 2 * t ^ 6 + (12994937 / 337500) * c ^ 2 * t ^ 8 + (120491 / 45000) * c ^ 2 * t ^ 10 + (243433 / 1265625) * c ^ 2 * t ^ 12 + (-152921 / 7593750) * c ^ 2 * t ^ 14 + (150698 / 3796875) * c ^ 2 * t ^ 18 + (-584 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-45944 / 225) * t ^ 2 + (73444 / 375) * t ^ 4 + (235382341 / 1350000) * t ^ 6 + (-35986711 / 225000) * t ^ 8 + (-23255321 / 2700000) * t ^ 10 + (2283151 / 1125000) * t ^ 12 + (-267896 / 1265625) * t ^ 14 + (-2961103 / 40500000) * t ^ 18 + (-1168 / 1265625) * t ^ 20 + (-45944 / 225) * alpha * t ^ 2 + (421228 / 1125) * alpha * t ^ 4 + (-224677627 / 1350000) * alpha * t ^ 6 + (-89677 / 27000) * alpha * t ^ 8 + (-1136657 / 300000) * alpha * t ^ 10 + (20454919 / 10125000) * alpha * t ^ 12 + (171128 / 421875) * alpha * t ^ 14 + (42977 / 500000) * alpha * t ^ 18 + (-1168 / 1265625) * alpha * t ^ 20) * c_sq
theorem v45_30 (t : ℂ) : (momentPoly 45 z45 3 0).eval t = ((-119 / 25) * t ^ 3 + (69 / 25) * t ^ 5 + 2 * t ^ 9 + (6013 / 1500) * c * t ^ 3 + (-1247 / 500) * c * t ^ 5 + (71 / 375) * c * t ^ 9 + (-2633 / 375) * alpha * t ^ 3 + (17651 / 1000) * alpha * t ^ 5 + (-15977 / 3000) * alpha * t ^ 9 + (73 / 25) * alpha * c * t ^ 3 + (-73 / 25) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_10, v44_20, v44_30]
  try simp only [phase43_00, phase43_10, phase43_20, phase43_30]
  try simp only [star_one, star_neg]
  linear_combination ((-313 / 2000) * t ^ 3 + (-271 / 2000) * t ^ 5 + (-2801 / 18000) * c * t ^ 3 + (-2407 / 18000) * c * t ^ 5 + (1 / 1125) * c ^ 2 * t ^ 3 + (2 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((4 / 1125) * alpha * t ^ 3 + (8 / 1125) * alpha * t ^ 5) * c_sq
theorem v45_31 (t : ℂ) : (momentPoly 45 z45 3 1).eval t = ((-87417 / 50) * t ^ 2 + (325608 / 125) * t ^ 4 + (-1770147 / 2000) * t ^ 6 + (-21741 / 2000) * t ^ 10 + (-264 / 25) * c * t ^ 2 + (7909 / 1000) * c * t ^ 4 + (153 / 2000) * c * t ^ 6 + (2989 / 2000) * c * t ^ 10 + (23177 / 50) * alpha * t ^ 2 + (-118474 / 375) * alpha * t ^ 4 + (-220253 / 2000) * alpha * t ^ 6 + (11623 / 6000) * alpha * t ^ 10 + (-88 / 25) * alpha * c * t ^ 2 + (9509 / 3000) * alpha * c * t ^ 4 + (-1549 / 2000) * alpha * c * t ^ 6 + (4589 / 6000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_10, v44_11, v44_20, v44_21, v44_30, v44_31]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21, phase43_30, phase43_31]
  try simp only [star_one, star_neg]
  linear_combination ((44 / 75) * t ^ 2 + (-49 / 60) * t ^ 4 + (44981 / 90000) * t ^ 6 + (-46163 / 270000) * t ^ 10 + (88 / 75) * c * t ^ 2 + (-1239 / 1000) * c * t ^ 4 + (33191 / 90000) * c * t ^ 6 + (-46163 / 270000) * c * t ^ 10 + (44 / 75) * c ^ 2 * t ^ 2 + (-1267 / 3000) * c ^ 2 * t ^ 4 + (-131 / 1000) * c ^ 2 * t ^ 6) * alpha_sq + ((-88 / 75) * t ^ 2 + (427 / 750) * t ^ 4 + (5903 / 11250) * t ^ 6 + (-142 / 16875) * t ^ 10 + (88 / 75) * alpha * t ^ 2 + (-2449 / 2250) * alpha * t ^ 4 + (-7 / 1250) * alpha * t ^ 6 + (142 / 16875) * alpha * t ^ 10) * c_sq
theorem v45_32 (t : ℂ) : (momentPoly 45 z45 3 2).eval t = ((35247 / 10) * t + (-58203 / 8) * t ^ 3 + (2702429 / 600) * t ^ 5 + (-84544777 / 120000) * t ^ 7 + (2691983 / 40000) * t ^ 9 + (-2249003 / 24000) * t ^ 11 + (225043 / 120000) * t ^ 13 + (-11749 / 10) * c * t + (472671 / 200) * c * t ^ 3 + (-17346181 / 12000) * c * t ^ 5 + (7840429 / 30000) * c * t ^ 7 + (-283347 / 20000) * c * t ^ 9 + (-79 / 600) * c * t ^ 11 + (3584 / 1875) * c * t ^ 13 + (-11749 / 10) * alpha * t + (383409 / 200) * alpha * t ^ 3 + (-2309449 / 5000) * alpha * t ^ 5 + (-19490191 / 40000) * alpha * t ^ 7 + (294179 / 1600) * alpha * t ^ 9 + (2533039 / 40000) * alpha * t ^ 11 + (-1931531 / 40000) * alpha * t ^ 13 + (-11749 / 10) * alpha * c * t + (74211 / 40) * alpha * c * t ^ 3 + (-85303691 / 180000) * alpha * c * t ^ 5 + (-17901689 / 90000) * alpha * c * t ^ 7 + (-166373 / 12000) * alpha * c * t ^ 9 + (-88597 / 45000) * alpha * c * t ^ 11 + (986 / 5625) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_10, v44_11, v44_12, v44_20, v44_21, v44_22, v44_30, v44_31, v44_32]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22, phase43_30, phase43_31, phase43_32]
  try simp only [star_one, star_neg]
  linear_combination ((27231 / 2000) * t ^ 3 + (-84041 / 90000) * t ^ 5 + (-18701 / 3000) * t ^ 7 + (-3944993 / 450000) * t ^ 9 + (-6827 / 25000) * t ^ 11 + (1175603 / 450000) * t ^ 13 + (81229 / 6000) * c * t ^ 3 + (-255047 / 270000) * c * t ^ 5 + (-519113 / 45000) * c * t ^ 7 + (10499 / 168750) * c * t ^ 9 + (143141 / 2025000) * c * t ^ 11 + (-46163 / 2025000) * c * t ^ 13 + (-29 / 375) * c ^ 2 * t ^ 3 + (-731 / 67500) * c ^ 2 * t ^ 5 + (5771 / 135000) * c ^ 2 * t ^ 7 + (11 / 67500) * c ^ 2 * t ^ 9 + (4669 / 135000) * c ^ 2 * t ^ 11) * alpha_sq + ((58 / 125) * t ^ 3 + (947 / 11250) * t ^ 5 + (-9481 / 22500) * t ^ 7 + (976 / 9375) * t ^ 9 + (-58603 / 337500) * t ^ 11 + (-284 / 84375) * t ^ 13 + (-58 / 375) * alpha * t ^ 3 + (-4883 / 33750) * alpha * t ^ 5 + (3203 / 22500) * alpha * t ^ 7 + (8752 / 84375) * alpha * t ^ 9 + (34603 / 1012500) * alpha * t ^ 11 + (284 / 253125) * alpha * t ^ 13) * c_sq
theorem v45_33 (t : ℂ) : (momentPoly 45 z45 3 3).eval t = (528705 + (-1240488) * t ^ 2 + (1893451551 / 2000) * t ^ 4 + (-13068925123 / 50000) * t ^ 6 + (1805341663 / 50000) * t ^ 8 + (-1796761821 / 200000) * t ^ 10 + (18855881 / 25000) * t ^ 12 + (-76457867 / 100000) * t ^ 14 + (10409247 / 200000) * t ^ 18 + (75336 / 125) * c * t ^ 4 + (-3898171 / 3750) * c * t ^ 6 + (219209 / 500) * c * t ^ 8 + (-36651 / 2500) * c * t ^ 10 + (-575531 / 7500) * c * t ^ 12 + (222617 / 2500) * c * t ^ 14 + (284 / 375) * c * t ^ 18) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_03, v44_10, v44_11, v44_12, v44_13, v44_20, v44_21, v44_22, v44_23, v44_30, v44_31, v44_32, v44_33]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23, phase43_30, phase43_31, phase43_32, phase43_33]
  try simp only [star_one, star_neg]
  linear_combination ((-11486 / 75) * t ^ 2 + (64887 / 250) * t ^ 4 + (-195122113 / 300000) * t ^ 6 + (197797847 / 600000) * t ^ 8 + (111453899 / 600000) * t ^ 10 + (5543171 / 360000) * t ^ 12 + (-496977841 / 27000000) * t ^ 14 + (10983479 / 5062500) * t ^ 18 + (-22972 / 75) * c * t ^ 2 + (191608 / 375) * c * t ^ 4 + (-20429713 / 180000) * c * t ^ 6 + (-14697077 / 120000) * c * t ^ 8 + (11343929 / 360000) * c * t ^ 10 + (19196719 / 1800000) * c * t ^ 12 + (-20011079 / 1800000) * c * t ^ 14 + (-11486 / 75) * c ^ 2 * t ^ 2 + (37711 / 150) * c ^ 2 * t ^ 4 + (-89094239 / 1350000) * c ^ 2 * t ^ 6 + (-20365079 / 675000) * c ^ 2 * t ^ 8 + (-203617 / 90000) * c ^ 2 * t ^ 10 + (-22861 / 84375) * c ^ 2 * t ^ 12 + (17057 / 337500) * c ^ 2 * t ^ 14) * alpha_sq + ((45944 / 75) * t ^ 2 + (-134074 / 125) * t ^ 4 + (44329013 / 112500) * t ^ 6 + (3273893 / 56250) * t ^ 8 + (112741 / 12500) * t ^ 10 + (31783 / 28125) * t ^ 12 + (-320336 / 421875) * t ^ 14 + (20164 / 1265625) * t ^ 18) * c_sq
theorem v45_34 (t : ℂ) : (momentPoly 45 z45 3 4).eval t = ((6134571 / 10) * t + (-3755097 / 2) * t ^ 3 + (81693041 / 40) * t ^ 5 + (-1314459799111 / 1500000) * t ^ 7 + (592462030037 / 4800000) * t ^ 9 + (-865429765229 / 12000000) * t ^ 11 + (7280447319991 / 144000000) * t ^ 13 + (-19581870011 / 6000000) * t ^ 15 + (-4584158027 / 9600000) * t ^ 17 + (5295355921 / 36000000) * t ^ 19 + (-577406833 / 48000000) * t ^ 21 + (3974523787 / 144000000) * t ^ 25 + (-2044857 / 10) * c * t + (30495429 / 50) * c * t ^ 3 + (-267143219 / 400) * c * t ^ 5 + (1294977702177 / 4000000) * c * t ^ 7 + (-6324272717 / 96000) * c * t ^ 9 + (34785156507 / 8000000) * c * t ^ 11 + (49153123549 / 72000000) * c * t ^ 13 + (-3387322543 / 6000000) * c * t ^ 15 + (4329601 / 80000) * c * t ^ 17 + (-457968209 / 72000000) * c * t ^ 19 + (-164983639 / 8000000) * c * t ^ 21 + (40919257 / 18000000) * c * t ^ 25 + (2044857 / 10) * alpha * t + (-24736491 / 50) * alpha * t ^ 3 + (278622843 / 1000) * alpha * t ^ 5 + (293766232277 / 1500000) * alpha * t ^ 7 + (-5843273353981 / 24000000) * alpha * t ^ 9 + (251226310921 / 12000000) * alpha * t ^ 11 + (2609943053087 / 48000000) * alpha * t ^ 13 + (-30026581747 / 2000000) * alpha * t ^ 15 + (-54981464893 / 48000000) * alpha * t ^ 17 + (3231148481 / 12000000) * alpha * t ^ 19 + (-109414483 / 1920000) * alpha * t ^ 21 + (-2070330701 / 48000000) * alpha * t ^ 25 + (2044857 / 10) * alpha * c * t + (-4787889 / 10) * alpha * c * t ^ 3 + (1801866397 / 6000) * alpha * c * t ^ 5 + (57600826127 / 4000000) * alpha * c * t ^ 7 + (-1194179310149 / 36000000) * alpha * c * t ^ 9 + (-446763398819 / 72000000) * alpha * c * t ^ 11 + (-186304764551 / 216000000) * alpha * c * t ^ 13 + (-2286627043 / 18000000) * alpha * c * t ^ 15 + (168151967 / 18000000) * alpha * c * t ^ 17 + (9370821283 / 216000000) * alpha * c * t ^ 19 + (-61271209 / 2880000) * alpha * c * t ^ 21 + (-20065163 / 54000000) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_03, v44_04, v44_10, v44_11, v44_12, v44_13, v44_14, v44_20, v44_21, v44_22, v44_23, v44_24, v44_30, v44_31, v44_32, v44_33, v44_34]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24, phase43_30, phase43_31, phase43_32, phase43_33, phase43_34]
  try simp only [star_one, star_neg]
  linear_combination ((1756869 / 500) * t ^ 3 + (-20672663 / 6000) * t ^ 5 + (-596764979 / 2880000) * t ^ 7 + (-321281417759 / 72000000) * t ^ 9 + (682709689159 / 144000000) * t ^ 11 + (472442554931 / 432000000) * t ^ 13 + (-148801120099 / 108000000) * t ^ 15 + (39908519699 / 270000000) * t ^ 17 + (-7862281859 / 2160000000) * t ^ 19 + (-2463843071 / 720000000) * t ^ 21 + (-221735293 / 90000000) * t ^ 25 + (5240671 / 1500) * c * t ^ 3 + (-6824021 / 2000) * c * t ^ 5 + (-214897976491 / 72000000) * c * t ^ 7 + (614240236691 / 216000000) * c * t ^ 9 + (37090845109 / 432000000) * c * t ^ 11 + (-20834558663 / 1296000000) * c * t ^ 13 + (652858193 / 108000000) * c * t ^ 15 + (-369592241 / 202500000) * c * t ^ 17 + (-25907257003 / 19440000000) * c * t ^ 19 + (-12332209207 / 6480000000) * c * t ^ 21 + (-3369899 / 75937500) * c * t ^ 25 + (-7484 / 375) * c ^ 2 * t ^ 3 + (1003 / 30) * c ^ 2 * t ^ 5 + (-407593753 / 13500000) * c ^ 2 * t ^ 7 + (82476209 / 4500000) * c ^ 2 * t ^ 9 + (44764337 / 3000000) * c ^ 2 * t ^ 11 + (-470229127 / 27000000) * c ^ 2 * t ^ 13 + (161111 / 187500) * c ^ 2 * t ^ 15 + (6194 / 1265625) * c ^ 2 * t ^ 17 + (-1093057 / 16200000) * c ^ 2 * t ^ 19 + (-98003 / 5400000) * c ^ 2 * t ^ 21) * alpha_sq + ((14968 / 125) * t ^ 3 + (-23851 / 125) * t ^ 5 + (201679369 / 2250000) * t ^ 7 + (24660251 / 1125000) * t ^ 9 + (-563301949 / 4500000) * t ^ 11 + (600437489 / 6750000) * t ^ 13 + (-13484609 / 3375000) * t ^ 15 + (-52117 / 234375) * t ^ 17 + (87483691 / 202500000) * t ^ 19 + (131537 / 33750000) * t ^ 21 + (41464 / 6328125) * t ^ 25 + (14968 / 375) * alpha * t ^ 3 + (-1547 / 375) * alpha * t ^ 5 + (-42843391 / 750000) * alpha * t ^ 7 + (52927051 / 3375000) * alpha * t ^ 9 + (-188827901 / 13500000) * alpha * t ^ 11 + (107996369 / 20250000) * alpha * t ^ 13 + (47474821 / 3375000) * alpha * t ^ 15 + (336227 / 6328125) * alpha * t ^ 17 + (254519851 / 607500000) * alpha * t ^ 19 + (-7068463 / 101250000) * alpha * t ^ 21 + (41464 / 18984375) * alpha * t ^ 25) * c_sq
theorem v45_40 (t : ℂ) : (momentPoly 45 z45 4 0).eval t = ((3185747 / 8000) * t ^ 4 + (-11850927 / 20000) * t ^ 6 + (16343321 / 80000) * t ^ 8 + (-3280019 / 60000) * t ^ 10 + (2031803 / 240000) * t ^ 16 + (-2639 / 250) * c * t ^ 4 + (55021 / 2500) * c * t ^ 6 + (-2691 / 1250) * c * t ^ 8 + (-54563 / 7500) * c * t ^ 10 + (146 / 1875) * c * t ^ 16 + (-1194587 / 4800) * alpha * t ^ 4 + (11211059 / 60000) * alpha * t ^ 6 + (11602123 / 240000) * alpha * t ^ 8 + (-3973817 / 180000) * alpha * t ^ 10 + (-346831 / 720000) * alpha * t ^ 16 + (9 / 2) * alpha * c * t ^ 4 + (-42701 / 7500) * alpha * c * t ^ 6 + (-3149 / 3750) * alpha * c * t ^ 8 + (30563 / 22500) * alpha * c * t ^ 10 + (-146 / 5625) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_10, v44_20, v44_30, v44_40]
  try simp only [phase43_00, phase43_10, phase43_20, phase43_30, phase43_40]
  try simp only [star_one, star_neg]
  linear_combination ((941 / 750) * t ^ 4 + (106619 / 45000) * t ^ 6 + (16717 / 15000) * t ^ 8 + (46163 / 67500) * t ^ 10 + (2239 / 2250) * c * t ^ 4 + (-22597 / 11250) * c * t ^ 6 + (-271 / 7500) * c * t ^ 8 + (46163 / 67500) * c * t ^ 10 + (-292 / 1125) * c ^ 2 * t ^ 4 + (4384 / 16875) * c ^ 2 * t ^ 6 + (4 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((57 / 125) * t ^ 4 + (-947 / 1875) * t ^ 6 + (8 / 5625) * t ^ 8 + (-568 / 16875) * t ^ 10 + (-131 / 225) * alpha * t ^ 4 + (2999 / 5625) * alpha * t ^ 6 + (8 / 5625) * alpha * t ^ 8 + (-568 / 16875) * alpha * t ^ 10) * c_sq
theorem v45_41 (t : ℂ) : (momentPoly 45 z45 4 1).eval t = ((-20706 / 25) * t ^ 3 + (1765463 / 1250) * t ^ 5 + (-493363 / 625) * t ^ 7 + (623729 / 1250) * t ^ 9 + (-552032 / 1875) * t ^ 11 + (1283 / 1875) * t ^ 17 + (174377 / 250) * c * t ^ 3 + (-64824857 / 60000) * c * t ^ 5 + (4164259 / 10000) * c * t ^ 7 + (126971 / 40000) * c * t ^ 9 + (-614929 / 30000) * c * t ^ 11 + (-103231 / 120000) * c * t ^ 17 + (-152714 / 125) * alpha * t ^ 3 + (234318577 / 60000) * alpha * t ^ 5 + (-23820619 / 10000) * alpha * t ^ 7 + (-38886531 / 40000) * alpha * t ^ 9 + (21300929 / 30000) * alpha * t ^ 11 + (999911 / 120000) * alpha * t ^ 17 + (12702 / 25) * alpha * c * t ^ 3 + (-3515737 / 3750) * alpha * c * t ^ 5 + (763637 / 1875) * alpha * c * t ^ 7 + (78629 / 3750) * alpha * c * t ^ 9 + (1768 / 5625) * alpha * c * t ^ 11 + (5033 / 5625) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_10, v44_11, v44_20, v44_21, v44_30, v44_31, v44_40, v44_41]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21, phase43_30, phase43_31, phase43_40, phase43_41]
  try simp only [star_one, star_neg]
  linear_combination ((-27231 / 1000) * t ^ 3 + (-1441751 / 720000) * t ^ 5 + (8978647 / 360000) * t ^ 7 + (15822251 / 7200000) * t ^ 9 + (-860843 / 1800000) * t ^ 11 + (-74327 / 2400000) * t ^ 17 + (-81229 / 3000) * c * t ^ 3 + (-4095301 / 2160000) * c * t ^ 5 + (972127 / 40000) * c * t ^ 7 + (56762497 / 21600000) * c * t ^ 9 + (-8341763 / 16200000) * c * t ^ 11 + (-2081581 / 64800000) * c * t ^ 17 + (58 / 375) * c ^ 2 * t ^ 3 + (3593 / 33750) * c ^ 2 * t ^ 5 + (-233 / 1350) * c ^ 2 * t ^ 7 + (-108 / 3125) * c ^ 2 * t ^ 9 + (-9284 / 253125) * c ^ 2 * t ^ 11 + (-292 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((1016 / 5625) * t ^ 5 + (-2984 / 5625) * t ^ 7 + (1168 / 5625) * t ^ 9 + (32 / 225) * t ^ 11 + (232 / 375) * alpha * t ^ 3 + (-502 / 3375) * alpha * t ^ 5 + (124 / 1125) * alpha * t ^ 7 + (-6076 / 84375) * alpha * t ^ 9 + (-102934 / 253125) * alpha * t ^ 11 + (1168 / 253125) * alpha * t ^ 17) * c_sq
theorem v45_42 (t : ℂ) : (momentPoly 45 z45 4 2).eval t = ((-15213207 / 50) * t ^ 2 + (697222401 / 1000) * t ^ 4 + (-1188569254583 / 2400000) * t ^ 6 + (79545712923 / 800000) * t ^ 8 + (-1352971309 / 4800000) * t ^ 10 + (46064500363 / 14400000) * t ^ 12 + (-1415269351 / 3600000) * t ^ 14 + (-1387956691 / 14400000) * t ^ 18 + (928352143 / 14400000) * t ^ 20 + (-45944 / 25) * c * t ^ 2 + (452242 / 125) * c * t ^ 4 + (-72106739 / 30000) * c * t ^ 6 + (831589 / 2400) * c * t ^ 8 + (14790807 / 20000) * c * t ^ 10 + (-48508967 / 120000) * c * t ^ 12 + (-79429 / 1250) * c * t ^ 14 + (-295951 / 60000) * c * t ^ 18 + (41197 / 120000) * c * t ^ 20 + (12100501 / 150) * alpha * t ^ 2 + (-384473203 / 3000) * alpha * t ^ 4 + (13909870619 / 480000) * alpha * t ^ 6 + (8534722931 / 480000) * alpha * t ^ 8 + (1500555001 / 960000) * alpha * t ^ 10 + (-137189971 / 576000) * alpha * t ^ 12 + (-146615797 / 720000) * alpha * t ^ 14 + (-75747961 / 2880000) * alpha * t ^ 18 + (-34643219 / 2880000) * alpha * t ^ 20 + (-45944 / 75) * alpha * c * t ^ 2 + (521042 / 375) * alpha * c * t ^ 4 + (-65194087 / 50000) * alpha * c * t ^ 6 + (6516979 / 12000) * alpha * c * t ^ 8 + (12973943 / 60000) * alpha * c * t ^ 10 + (-449539459 / 1800000) * alpha * c * t ^ 12 + (875279 / 56250) * alpha * c * t ^ 14 + (-1075531 / 900000) * alpha * c * t ^ 18 + (-54803 / 360000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_10, v44_11, v44_12, v44_20, v44_21, v44_22, v44_30, v44_31, v44_32, v44_40, v44_41, v44_42]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22, phase43_30, phase43_31, phase43_32, phase43_40, phase43_41, phase43_42]
  try simp only [star_one, star_neg]
  linear_combination ((22972 / 225) * t ^ 2 + (-4214 / 15) * t ^ 4 + (107919689 / 337500) * t ^ 6 + (-179281613 / 3600000) * t ^ 8 + (-5732461 / 43200) * t ^ 10 + (3580674751 / 108000000) * t ^ 12 + (338278687 / 27000000) * t ^ 14 + (15872429 / 13500000) * t ^ 18 + (20245399 / 108000000) * t ^ 20 + (45944 / 225) * c * t ^ 2 + (-53277 / 125) * c * t ^ 4 + (43444499 / 135000) * c * t ^ 6 + (-375648089 / 5400000) * c * t ^ 8 + (-23894891 / 300000) * c * t ^ 10 + (19199419 / 432000) * c * t ^ 12 + (1981861 / 337500) * c * t ^ 14 + (1417283 / 2700000) * c * t ^ 18 + (16403 / 2160000) * c * t ^ 20 + (22972 / 225) * c ^ 2 * t ^ 2 + (-54481 / 375) * c ^ 2 * t ^ 4 + (461039 / 225000) * c ^ 2 * t ^ 6 + (12994937 / 337500) * c ^ 2 * t ^ 8 + (120491 / 45000) * c ^ 2 * t ^ 10 + (243433 / 1265625) * c ^ 2 * t ^ 12 + (-152921 / 7593750) * c ^ 2 * t ^ 14 + (150698 / 3796875) * c ^ 2 * t ^ 18 + (-584 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-45944 / 225) * t ^ 2 + (73444 / 375) * t ^ 4 + (235382341 / 1350000) * t ^ 6 + (-35986711 / 225000) * t ^ 8 + (-23255321 / 2700000) * t ^ 10 + (2283151 / 1125000) * t ^ 12 + (-267896 / 1265625) * t ^ 14 + (-2961103 / 40500000) * t ^ 18 + (-1168 / 1265625) * t ^ 20 + (45944 / 225) * alpha * t ^ 2 + (-421228 / 1125) * alpha * t ^ 4 + (224677627 / 1350000) * alpha * t ^ 6 + (89677 / 27000) * alpha * t ^ 8 + (1136657 / 300000) * alpha * t ^ 10 + (-20454919 / 10125000) * alpha * t ^ 12 + (-171128 / 421875) * alpha * t ^ 14 + (-42977 / 500000) * alpha * t ^ 18 + (1168 / 1265625) * alpha * t ^ 20) * c_sq
theorem v45_43 (t : ℂ) : (momentPoly 45 z45 4 3).eval t = ((6134571 / 10) * t + (-3755097 / 2) * t ^ 3 + (81693041 / 40) * t ^ 5 + (-1314459799111 / 1500000) * t ^ 7 + (592462030037 / 4800000) * t ^ 9 + (-865429765229 / 12000000) * t ^ 11 + (7280447319991 / 144000000) * t ^ 13 + (-19581870011 / 6000000) * t ^ 15 + (-4584158027 / 9600000) * t ^ 17 + (5295355921 / 36000000) * t ^ 19 + (-577406833 / 48000000) * t ^ 21 + (3974523787 / 144000000) * t ^ 25 + (-2044857 / 10) * c * t + (30495429 / 50) * c * t ^ 3 + (-267143219 / 400) * c * t ^ 5 + (1294977702177 / 4000000) * c * t ^ 7 + (-6324272717 / 96000) * c * t ^ 9 + (34785156507 / 8000000) * c * t ^ 11 + (49153123549 / 72000000) * c * t ^ 13 + (-3387322543 / 6000000) * c * t ^ 15 + (4329601 / 80000) * c * t ^ 17 + (-457968209 / 72000000) * c * t ^ 19 + (-164983639 / 8000000) * c * t ^ 21 + (40919257 / 18000000) * c * t ^ 25 + (-2044857 / 10) * alpha * t + (24736491 / 50) * alpha * t ^ 3 + (-278622843 / 1000) * alpha * t ^ 5 + (-293766232277 / 1500000) * alpha * t ^ 7 + (5843273353981 / 24000000) * alpha * t ^ 9 + (-251226310921 / 12000000) * alpha * t ^ 11 + (-2609943053087 / 48000000) * alpha * t ^ 13 + (30026581747 / 2000000) * alpha * t ^ 15 + (54981464893 / 48000000) * alpha * t ^ 17 + (-3231148481 / 12000000) * alpha * t ^ 19 + (109414483 / 1920000) * alpha * t ^ 21 + (2070330701 / 48000000) * alpha * t ^ 25 + (-2044857 / 10) * alpha * c * t + (4787889 / 10) * alpha * c * t ^ 3 + (-1801866397 / 6000) * alpha * c * t ^ 5 + (-57600826127 / 4000000) * alpha * c * t ^ 7 + (1194179310149 / 36000000) * alpha * c * t ^ 9 + (446763398819 / 72000000) * alpha * c * t ^ 11 + (186304764551 / 216000000) * alpha * c * t ^ 13 + (2286627043 / 18000000) * alpha * c * t ^ 15 + (-168151967 / 18000000) * alpha * c * t ^ 17 + (-9370821283 / 216000000) * alpha * c * t ^ 19 + (61271209 / 2880000) * alpha * c * t ^ 21 + (20065163 / 54000000) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_03, v44_10, v44_11, v44_12, v44_13, v44_20, v44_21, v44_22, v44_23, v44_30, v44_31, v44_32, v44_33, v44_40, v44_41, v44_42, v44_43]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23, phase43_30, phase43_31, phase43_32, phase43_33, phase43_40, phase43_41, phase43_42, phase43_43]
  try simp only [star_one, star_neg]
  linear_combination ((1756869 / 500) * t ^ 3 + (-20672663 / 6000) * t ^ 5 + (-596764979 / 2880000) * t ^ 7 + (-321281417759 / 72000000) * t ^ 9 + (682709689159 / 144000000) * t ^ 11 + (472442554931 / 432000000) * t ^ 13 + (-148801120099 / 108000000) * t ^ 15 + (39908519699 / 270000000) * t ^ 17 + (-7862281859 / 2160000000) * t ^ 19 + (-2463843071 / 720000000) * t ^ 21 + (-221735293 / 90000000) * t ^ 25 + (5240671 / 1500) * c * t ^ 3 + (-6824021 / 2000) * c * t ^ 5 + (-214897976491 / 72000000) * c * t ^ 7 + (614240236691 / 216000000) * c * t ^ 9 + (37090845109 / 432000000) * c * t ^ 11 + (-20834558663 / 1296000000) * c * t ^ 13 + (652858193 / 108000000) * c * t ^ 15 + (-369592241 / 202500000) * c * t ^ 17 + (-25907257003 / 19440000000) * c * t ^ 19 + (-12332209207 / 6480000000) * c * t ^ 21 + (-3369899 / 75937500) * c * t ^ 25 + (-7484 / 375) * c ^ 2 * t ^ 3 + (1003 / 30) * c ^ 2 * t ^ 5 + (-407593753 / 13500000) * c ^ 2 * t ^ 7 + (82476209 / 4500000) * c ^ 2 * t ^ 9 + (44764337 / 3000000) * c ^ 2 * t ^ 11 + (-470229127 / 27000000) * c ^ 2 * t ^ 13 + (161111 / 187500) * c ^ 2 * t ^ 15 + (6194 / 1265625) * c ^ 2 * t ^ 17 + (-1093057 / 16200000) * c ^ 2 * t ^ 19 + (-98003 / 5400000) * c ^ 2 * t ^ 21) * alpha_sq + ((14968 / 125) * t ^ 3 + (-23851 / 125) * t ^ 5 + (201679369 / 2250000) * t ^ 7 + (24660251 / 1125000) * t ^ 9 + (-563301949 / 4500000) * t ^ 11 + (600437489 / 6750000) * t ^ 13 + (-13484609 / 3375000) * t ^ 15 + (-52117 / 234375) * t ^ 17 + (87483691 / 202500000) * t ^ 19 + (131537 / 33750000) * t ^ 21 + (41464 / 6328125) * t ^ 25 + (-14968 / 375) * alpha * t ^ 3 + (1547 / 375) * alpha * t ^ 5 + (42843391 / 750000) * alpha * t ^ 7 + (-52927051 / 3375000) * alpha * t ^ 9 + (188827901 / 13500000) * alpha * t ^ 11 + (-107996369 / 20250000) * alpha * t ^ 13 + (-47474821 / 3375000) * alpha * t ^ 15 + (-336227 / 6328125) * alpha * t ^ 17 + (-254519851 / 607500000) * alpha * t ^ 19 + (7068463 / 101250000) * alpha * t ^ 21 + (-41464 / 18984375) * alpha * t ^ 25) * c_sq
theorem v45_44 (t : ℂ) : (momentPoly 45 z45 4 4).eval t = (92018565 + (-284611104) * t ^ 2 + (161002093511 / 500) * t ^ 4 + (-2082191037389 / 12500) * t ^ 6 + (2266995192809819 / 48000000) * t ^ 8 + (-670349891316599 / 60000000) * t ^ 10 + (338679858037309 / 240000000) * t ^ 12 + (-248668452661289 / 360000000) * t ^ 14 + (226467140618113 / 576000000) * t ^ 16 + (8085345005699 / 360000000) * t ^ 18 + (-38598555086251 / 2160000000) * t ^ 20 + (-2207862695587 / 360000000) * t ^ 22 + (4086715856149 / 1440000000) * t ^ 24 + (-1391740297031 / 1080000000) * t ^ 26 + (251954417423 / 8640000000) * t ^ 32 + (25623584 / 125) * c * t ^ 4 + (-374104232 / 625) * c * t ^ 6 + (20583735631 / 31250) * c * t ^ 8 + (-308801223149 / 937500) * c * t ^ 10 + (109292421 / 156250) * c * t ^ 12 + (632522238901 / 5625000) * c * t ^ 14 + (-51851045921 / 1125000) * c * t ^ 16 + (-6745641253 / 2812500) * c * t ^ 18 + (-1282780379 / 8437500) * c * t ^ 20 + (-471365507 / 5625000) * c * t ^ 22 + (-2210569 / 5625000) * c * t ^ 24 + (-1166393543 / 8437500) * c * t ^ 26 + (2939272 / 2109375) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z45, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v44_00, v44_01, v44_02, v44_03, v44_04, v44_10, v44_11, v44_12, v44_13, v44_14, v44_20, v44_21, v44_22, v44_23, v44_24, v44_30, v44_31, v44_32, v44_33, v44_34, v44_40, v44_41, v44_42, v44_43, v44_44]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24, phase43_30, phase43_31, phase43_32, phase43_33, phase43_34, phase43_40, phase43_41, phase43_42, phase43_43, phase43_44]
  try simp only [star_one, star_neg]
  linear_combination ((-2635288 / 75) * t ^ 2 + (11034814 / 125) * t ^ 4 + (-9378540857 / 37500) * t ^ 6 + (2500466551261 / 9000000) * t ^ 8 + (-427524036251 / 45000000) * t ^ 10 + (-52372920593 / 937500) * t ^ 12 + (-2108878185697 / 81000000) * t ^ 14 + (1585449103991 / 180000000) * t ^ 16 + (52347124993 / 20000000) * t ^ 18 + (-235575154937 / 162000000) * t ^ 20 + (9887459003 / 54000000) * t ^ 22 + (38079512137 / 900000000) * t ^ 24 + (-24863718637 / 2700000000) * t ^ 26 + (-124410727 / 4050000000) * t ^ 32 + (-5270576 / 75) * c * t ^ 2 + (195511456 / 1125) * c * t ^ 4 + (-123880461 / 1250) * c * t ^ 6 + (-550884755417 / 9000000) * c * t ^ 8 + (19792288823467 / 270000000) * c * t ^ 10 + (-78634741011 / 10000000) * c * t ^ 12 + (-58835932787 / 4000000) * c * t ^ 14 + (1572219078241 / 270000000) * c * t ^ 16 + (425928863477 / 1620000000) * c * t ^ 18 + (-119440163591 / 2430000000) * c * t ^ 20 + (5486356031 / 324000000) * c * t ^ 22 + (38421157 / 150000000) * c * t ^ 24 + (34563910843 / 2700000000) * c * t ^ 26 + (-5425871 / 337500000) * c * t ^ 32 + (-2635288 / 75) * c ^ 2 * t ^ 2 + (19239626 / 225) * c ^ 2 * t ^ 4 + (-4696121623 / 84375) * c ^ 2 * t ^ 6 + (-128844770771 / 40500000) * c ^ 2 * t ^ 8 + (463585061603 / 67500000) * c ^ 2 * t ^ 10 + (188582271529 / 135000000) * c ^ 2 * t ^ 12 + (5323836359 / 27000000) * c ^ 2 * t ^ 14 + (32716097 / 4050000) * c ^ 2 * t ^ 16 + (-16608017 / 6750000) * c ^ 2 * t ^ 18 + (-9552278267 / 1215000000) * c ^ 2 * t ^ 20 + (491811487 / 135000000) * c ^ 2 * t ^ 22 + (-10424177 / 759375000) * c ^ 2 * t ^ 24 + (458829509 / 4556250000) * c ^ 2 * t ^ 26 + (-85264 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((10541152 / 75) * t ^ 2 + (-136805368 / 375) * t ^ 4 + (8092300324 / 28125) * t ^ 6 + (-32660983751 / 675000) * t ^ 8 + (-5703132741 / 625000) * t ^ 10 + (-6355792991 / 1250000) * t ^ 12 + (-119184311197 / 101250000) * t ^ 14 + (173510279 / 562500) * t ^ 16 + (32850841 / 4218750) * t ^ 18 + (566765191 / 33750000) * t ^ 20 + (-15166699 / 3750000) * t ^ 22 + (-5207503 / 63281250) * t ^ 24 + (-254364727 / 189843750) * t ^ 26 + (341056 / 94921875) * t ^ 32) * c_sq
#print axioms v45_00
#print axioms v45_11
#print axioms v45_22
#print axioms v45_33
#print axioms v45_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v46_02 (t : ℂ) : (momentPoly 46 z46 0 2).eval t = ((-3233 / 200) * t ^ 2 + (5027 / 600) * t ^ 4 + (-4 / 25) * c * t ^ 2 + (-4 / 75) * c * t ^ 4 + (-3859 / 600) * alpha * t ^ 2 + (-271 / 200) * alpha * t ^ 4 + (4 / 75) * alpha * c * t ^ 2 + (4 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02]
  try simp only [phase43_00, phase43_01, phase43_02]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 150) * t ^ 2 + (1 / 75) * c * t ^ 2 + (1 / 150) * c ^ 2 * t ^ 2) * alpha_sq + ((-1 / 75) * t ^ 2 + (-1 / 75) * alpha * t ^ 2) * c_sq
theorem v46_03 (t : ℂ) : (momentPoly 46 z46 0 3).eval t = ((-192 / 25) * t ^ 3 + (142 / 25) * t ^ 5 + 2 * t ^ 9 + (2383 / 375) * c * t ^ 3 + (-321 / 125) * c * t ^ 5 + (284 / 1125) * c * t ^ 9 + (3413 / 1500) * alpha * t ^ 3 + (-19977 / 1000) * alpha * t ^ 5 + (46163 / 9000) * alpha * t ^ 9 + (-292 / 75) * alpha * c * t ^ 3 + (292 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_03]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03]
  try simp only [star_one, star_neg]
  linear_combination ((-2107 / 6000) * t ^ 3 + (-1397 / 6000) * t ^ 5 + (-697 / 2000) * c * t ^ 3 + (-1381 / 6000) * c * t ^ 5 + (1 / 375) * c ^ 2 * t ^ 3 + (1 / 375) * c ^ 2 * t ^ 5) * alpha_sq + ((-4 / 375) * alpha * t ^ 3 + (-4 / 375) * alpha * t ^ 5) * c_sq
theorem v46_04 (t : ℂ) : (momentPoly 46 z46 0 4).eval t = ((64097437 / 120000) * t ^ 4 + (-15219903 / 20000) * t ^ 6 + (13701817 / 80000) * t ^ 8 + (-1339401 / 20000) * t ^ 10 + (5773297 / 720000) * t ^ 16 + (-6224 / 625) * c * t ^ 4 + (53143 / 1875) * c * t ^ 6 + (-4798 / 1875) * c * t ^ 8 + (-5803 / 625) * c * t ^ 10 + (584 / 5625) * c * t ^ 16 + (54736163 / 120000) * alpha * t ^ 4 + (-18348931 / 60000) * alpha * t ^ 6 + (-17319851 / 240000) * alpha * t ^ 8 + (6380369 / 180000) * alpha * t ^ 10 + (74327 / 80000) * alpha * t ^ 16 + (-37712 / 5625) * alpha * c * t ^ 4 + (17501 / 1875) * alpha * c * t ^ 6 + (2294 / 1875) * alpha * c * t ^ 8 + (-9409 / 5625) * alpha * c * t ^ 10 + (584 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_03, v45_04]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04]
  try simp only [star_one, star_neg]
  linear_combination ((5266 / 5625) * t ^ 4 + (39503 / 5000) * t ^ 6 + (38033 / 15000) * t ^ 8 + (14209 / 22500) * t ^ 10 + (3076 / 5625) * c * t ^ 4 + (-12013 / 5625) * c * t ^ 6 + (-1397 / 22500) * c * t ^ 8 + (14209 / 22500) * c * t ^ 10 + (-146 / 375) * c ^ 2 * t ^ 4 + (2194 / 5625) * c ^ 2 * t ^ 6 + (2 / 5625) * c ^ 2 * t ^ 8) * alpha_sq + ((7127 / 11250) * t ^ 4 + (-1039 / 1250) * t ^ 6 + (4 / 1875) * t ^ 8 + (-284 / 5625) * t ^ 10 + (10393 / 11250) * alpha * t ^ 4 + (-2723 / 3750) * alpha * t ^ 6 + (-4 / 1875) * alpha * t ^ 8 + (284 / 5625) * alpha * t ^ 10) * c_sq
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
theorem v46_12 (t : ℂ) : (momentPoly 46 z46 1 2).eval t = ((182 / 5) * t + (-1067 / 30) * t ^ 3 + (167 / 30) * t ^ 5 + (-182 / 15) * c * t + (577 / 50) * c * t ^ 3 + (-77 / 50) * c * t ^ 5 + (182 / 15) * alpha * t + (-463 / 50) * alpha * t ^ 3 + (-37 / 50) * alpha * t ^ 5 + (182 / 15) * alpha * c * t + (-161 / 18) * alpha * c * t ^ 3 + (-19 / 18) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_10, v45_11, v45_12]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12]
  try simp only [star_one, star_neg]
  linear_combination ((2107 / 18000) * t ^ 3 + (1397 / 18000) * t ^ 5 + (697 / 6000) * c * t ^ 3 + (1381 / 18000) * c * t ^ 5 + (-1 / 1125) * c ^ 2 * t ^ 3 + (-1 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((2 / 375) * t ^ 3 + (2 / 375) * t ^ 5 + (2 / 1125) * alpha * t ^ 3 + (2 / 1125) * alpha * t ^ 5) * c_sq
theorem v46_13 (t : ℂ) : (momentPoly 46 z46 1 3).eval t = ((-87291 / 40) * t ^ 2 + (1026467 / 375) * t ^ 4 + (-333279 / 500) * t ^ 6 + (-12999 / 1000) * t ^ 10 + (-108 / 5) * c * t ^ 2 + (12589 / 750) * c * t ^ 4 + (-269 / 500) * c * t ^ 6 + (2909 / 1500) * c * t ^ 10 + (-34731 / 40) * alpha * t ^ 2 + (222667 / 375) * alpha * t ^ 4 + (77121 / 500) * alpha * t ^ 6 + (-12997 / 3000) * alpha * t ^ 10 + (36 / 5) * alpha * c * t ^ 2 + (-14189 / 2250) * alpha * c * t ^ 4 + (623 / 500) * alpha * c * t ^ 6 + (-501 / 500) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_03, v45_10, v45_11, v45_12, v45_13]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13]
  try simp only [star_one, star_neg]
  linear_combination ((9 / 10) * t ^ 2 + (-87169 / 90000) * t ^ 4 + (7843 / 15000) * t ^ 6 + (-14209 / 90000) * t ^ 10 + (9 / 5) * c * t ^ 2 + (-8899 / 5625) * c * t ^ 4 + (10091 / 30000) * c * t ^ 6 + (-14209 / 90000) * c * t ^ 10 + (9 / 10) * c ^ 2 * t ^ 2 + (-1227 / 2000) * c ^ 2 * t ^ 4 + (-373 / 2000) * c ^ 2 * t ^ 6) * alpha_sq + ((-9 / 5) * t ^ 2 + (18031 / 22500) * t ^ 4 + (5611 / 7500) * t ^ 6 + (-71 / 5625) * t ^ 10 + (-9 / 5) * alpha * t ^ 2 + (35551 / 22500) * alpha * t ^ 4 + (-229 / 7500) * alpha * t ^ 6 + (-71 / 5625) * alpha * t ^ 10) * c_sq
theorem v46_14 (t : ℂ) : (momentPoly 46 z46 1 4).eval t = ((-34176 / 25) * t ^ 3 + (1521942 / 625) * t ^ 5 + (-2607052 / 1875) * t ^ 7 + (1077508 / 1875) * t ^ 9 + (-1428128 / 5625) * t ^ 11 + (8882 / 5625) * t ^ 17 + (424174 / 375) * c * t ^ 3 + (-21734419 / 15000) * c * t ^ 5 + (3060379 / 7500) * c * t ^ 7 + (-126767 / 90000) * c * t ^ 9 + (-174683 / 7500) * c * t ^ 11 + (-26837 / 30000) * c * t ^ 17 + (303757 / 750) * alpha * t ^ 3 + (-50541709 / 15000) * alpha * t ^ 5 + (17746549 / 7500) * alpha * t ^ 7 + (86055323 / 90000) * alpha * t ^ 9 + (-4118803 / 7500) * alpha * t ^ 11 + (-297727 / 30000) * alpha * t ^ 17 + (-51976 / 75) * alpha * c * t ^ 3 + (6943874 / 5625) * alpha * c * t ^ 5 + (-2923148 / 5625) * alpha * c * t ^ 7 + (-113458 / 5625) * alpha * c * t ^ 9 + (-7072 / 16875) * alpha * c * t ^ 11 + (-20132 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_03, v45_04, v45_10, v45_11, v45_12, v45_13, v45_14]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14]
  try simp only [star_one, star_neg]
  linear_combination ((-187523 / 3000) * t ^ 3 + (597761 / 80000) * t ^ 5 + (76246739 / 1800000) * t ^ 7 + (25372843 / 7200000) * t ^ 9 + (-5368577 / 5400000) * t ^ 11 + (-1313167 / 21600000) * t ^ 17 + (-62033 / 1000) * c * t ^ 3 + (5357641 / 720000) * c * t ^ 5 + (74494531 / 1800000) * c * t ^ 7 + (30021227 / 7200000) * c * t ^ 9 + (-5674753 / 5400000) * c * t ^ 11 + (-450181 / 7200000) * c * t ^ 17 + (178 / 375) * c ^ 2 * t ^ 3 + (-347 / 11250) * c ^ 2 * t ^ 5 + (-15529 / 56250) * c ^ 2 * t ^ 7 + (-1456 / 28125) * c ^ 2 * t ^ 9 + (-4784 / 84375) * c ^ 2 * t ^ 11 + (-146 / 84375) * c ^ 2 * t ^ 17) * alpha_sq + ((72 / 625) * t ^ 5 + (-16 / 25) * t ^ 7 + (584 / 1875) * t ^ 9 + (16 / 75) * t ^ 11 + (-712 / 375) * alpha * t ^ 3 + (5692 / 5625) * alpha * t ^ 5 + (-5803 / 28125) * alpha * t ^ 7 + (2446 / 28125) * alpha * t ^ 9 + (49699 / 84375) * alpha * t ^ 11 + (-584 / 84375) * alpha * t ^ 17) * c_sq
theorem v46_20 (t : ℂ) : (momentPoly 46 z46 2 0).eval t = ((-3233 / 200) * t ^ 2 + (5027 / 600) * t ^ 4 + (-4 / 25) * c * t ^ 2 + (-4 / 75) * c * t ^ 4 + (3859 / 600) * alpha * t ^ 2 + (271 / 200) * alpha * t ^ 4 + (-4 / 75) * alpha * c * t ^ 2 + (-4 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_10, v45_20]
  try simp only [phase43_00, phase43_10, phase43_20]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 150) * t ^ 2 + (1 / 75) * c * t ^ 2 + (1 / 150) * c ^ 2 * t ^ 2) * alpha_sq + ((-1 / 75) * t ^ 2 + (1 / 75) * alpha * t ^ 2) * c_sq
theorem v46_21 (t : ℂ) : (momentPoly 46 z46 2 1).eval t = ((182 / 5) * t + (-1067 / 30) * t ^ 3 + (167 / 30) * t ^ 5 + (-182 / 15) * c * t + (577 / 50) * c * t ^ 3 + (-77 / 50) * c * t ^ 5 + (-182 / 15) * alpha * t + (463 / 50) * alpha * t ^ 3 + (37 / 50) * alpha * t ^ 5 + (-182 / 15) * alpha * c * t + (161 / 18) * alpha * c * t ^ 3 + (19 / 18) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_10, v45_11, v45_20, v45_21]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21]
  try simp only [star_one, star_neg]
  linear_combination ((2107 / 18000) * t ^ 3 + (1397 / 18000) * t ^ 5 + (697 / 6000) * c * t ^ 3 + (1381 / 18000) * c * t ^ 5 + (-1 / 1125) * c ^ 2 * t ^ 3 + (-1 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((2 / 375) * t ^ 3 + (2 / 375) * t ^ 5 + (-2 / 1125) * alpha * t ^ 3 + (-2 / 1125) * alpha * t ^ 5) * c_sq
theorem v46_22 (t : ℂ) : (momentPoly 46 z46 2 2).eval t = (4186 + (-5400) * t ^ 2 + (9197903 / 6000) * t ^ 4 + (-280591 / 3000) * t ^ 6 + (61093 / 2000) * t ^ 8 + (1168 / 375) * c * t ^ 4 + (-2336 / 1125) * c * t ^ 6 + (-1168 / 1125) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_10, v45_11, v45_12, v45_20, v45_21, v45_22]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22]
  try simp only [star_one, star_neg]
  linear_combination ((-6 / 5) * t ^ 2 + (1469 / 1500) * t ^ 4 + (-149881 / 45000) * t ^ 6 + (-38033 / 45000) * t ^ 8 + (-12 / 5) * c * t ^ 2 + (2168 / 1125) * c * t ^ 4 + (17779 / 67500) * c * t ^ 6 + (1397 / 67500) * c * t ^ 8 + (-6 / 5) * c ^ 2 * t ^ 2 + (853 / 900) * c ^ 2 * t ^ 4 + (8009 / 67500) * c ^ 2 * t ^ 6 + (-2 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((24 / 5) * t ^ 2 + (-1519 / 375) * t ^ 4 + (-1199 / 5625) * t ^ 6 + (8 / 5625) * t ^ 8) * c_sq
theorem v46_23 (t : ℂ) : (momentPoly 46 z46 2 3).eval t = ((24572 / 5) * t + (-94963 / 10) * t ^ 3 + (338272141 / 60000) * t ^ 5 + (-37171423 / 40000) * t ^ 7 + (1076781 / 8000) * t ^ 9 + (-54503461 / 360000) * t ^ 11 + (-2693723 / 360000) * t ^ 13 + (-24572 / 15) * c * t + (154059 / 50) * c * t ^ 3 + (-27503827 / 15000) * c * t ^ 5 + (926459 / 2500) * c * t ^ 7 + (-48271 / 3000) * c * t ^ 9 + (-2813 / 5625) * c * t ^ 11 + (13586 / 5625) * c * t ^ 13 + (24572 / 15) * alpha * t + (-123621 / 50) * alpha * t ^ 3 + (34973759 / 60000) * alpha * t ^ 5 + (62873809 / 120000) * alpha * t ^ 7 + (-25370351 / 120000) * alpha * t ^ 9 + (-5152283 / 72000) * alpha * t ^ 11 + (16039687 / 360000) * alpha * t ^ 13 + (24572 / 15) * alpha * c * t + (-14329 / 6) * alpha * c * t ^ 3 + (2717873 / 5000) * alpha * c * t ^ 5 + (5008813 / 22500) * alpha * c * t ^ 7 + (229067 / 15000) * alpha * c * t ^ 9 + (379 / 135) * alpha * c * t ^ 11 + (-1694 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_03, v45_10, v45_11, v45_12, v45_13, v45_20, v45_21, v45_22, v45_23]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23]
  try simp only [star_one, star_neg]
  linear_combination ((187523 / 6000) * t ^ 3 + (-709549 / 90000) * t ^ 5 + (-1647947 / 112500) * t ^ 7 + (-89498 / 9375) * t ^ 9 + (-756949 / 1350000) * t ^ 11 + (3268681 / 1350000) * t ^ 13 + (62033 / 2000) * c * t ^ 3 + (-701411 / 90000) * c * t ^ 5 + (-25819973 / 1350000) * c * t ^ 7 + (92887 / 450000) * c * t ^ 9 + (62563 / 337500) * c * t ^ 11 + (-14209 / 675000) * c * t ^ 13 + (-89 / 375) * c ^ 2 * t ^ 3 + (4069 / 45000) * c ^ 2 * t ^ 5 + (5051 / 90000) * c ^ 2 * t ^ 7 + (-49 / 45000) * c ^ 2 * t ^ 9 + (4589 / 90000) * c ^ 2 * t ^ 11) * alpha_sq + ((178 / 125) * t ^ 3 + (-1479 / 2500) * t ^ 5 + (-115031 / 225000) * t ^ 7 + (1468 / 9375) * t ^ 9 + (-57971 / 225000) * t ^ 11 + (-142 / 28125) * t ^ 13 + (178 / 375) * alpha * t ^ 3 + (367 / 4500) * alpha * t ^ 5 + (-187031 / 675000) * alpha * t ^ 7 + (-4372 / 28125) * alpha * t ^ 9 + (-33971 / 675000) * alpha * t ^ 11 + (-142 / 84375) * alpha * t ^ 13) * c_sq
theorem v46_24 (t : ℂ) : (momentPoly 46 z46 2 4).eval t = ((-38850961 / 100) * t ^ 2 + (2300336137 / 3000) * t ^ 4 + (-338859080101 / 800000) * t ^ 6 + (20121073321 / 480000) * t ^ 8 + (-1494004801 / 960000) * t ^ 10 + (50643599239 / 14400000) * t ^ 12 + (-1794255371 / 3600000) * t ^ 14 + (-1785683371 / 14400000) * t ^ 18 + (780578219 / 14400000) * t ^ 20 + (-96136 / 25) * c * t ^ 2 + (2685284 / 375) * c * t ^ 4 + (-196078783 / 45000) * c * t ^ 6 + (1099511 / 1800) * c * t ^ 8 + (84995471 / 90000) * c * t ^ 10 + (-43943099 / 90000) * c * t ^ 12 + (-1225913 / 16875) * c * t ^ 14 + (-1986931 / 270000) * c * t ^ 18 + (36397 / 90000) * c * t ^ 20 + (-46373603 / 300) * alpha * t ^ 2 + (722480537 / 3000) * alpha * t ^ 4 + (-92564038873 / 1440000) * alpha * t ^ 6 + (-10788253351 / 480000) * alpha * t ^ 8 + (-7514305427 / 2880000) * alpha * t ^ 10 + (145152229 / 192000) * alpha * t ^ 12 + (660404963 / 2160000) * alpha * t ^ 14 + (369442691 / 8640000) * alpha * t ^ 18 + (165756029 / 8640000) * alpha * t ^ 20 + (96136 / 75) * alpha * c * t ^ 2 + (-2966884 / 1125) * alpha * c * t ^ 4 + (473660137 / 225000) * alpha * c * t ^ 6 + (-33764437 / 45000) * alpha * c * t ^ 8 + (-121707737 / 450000) * alpha * c * t ^ 10 + (139946189 / 450000) * alpha * c * t ^ 12 + (-1982869 / 84375) * alpha * c * t ^ 14 + (691207 / 450000) * alpha * c * t ^ 18 + (59603 / 270000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_03, v45_04, v45_10, v45_11, v45_12, v45_13, v45_14, v45_20, v45_21, v45_22, v45_23, v45_24]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24]
  try simp only [star_one, star_neg]
  linear_combination ((12017 / 75) * t ^ 2 + (-1917718 / 5625) * t ^ 4 + (291627673 / 900000) * t ^ 6 + (98211691 / 3600000) * t ^ 8 + (-260905987 / 1500000) * t ^ 10 + (345379301 / 36000000) * t ^ 12 + (450029951 / 27000000) * t ^ 14 + (57416789 / 27000000) * t ^ 18 + (67273751 / 108000000) * t ^ 20 + (24034 / 75) * c * t ^ 2 + (-3132448 / 5625) * c * t ^ 4 + (34988833 / 108000) * c * t ^ 6 + (-15645731 / 360000) * c * t ^ 8 + (-411239551 / 5400000) * c * t ^ 10 + (369504203 / 10800000) * c * t ^ 12 + (1254292 / 253125) * c * t ^ 14 + (10264463 / 16200000) * c * t ^ 18 + (26003 / 2160000) * c * t ^ 20 + (12017 / 75) * c ^ 2 * t ^ 2 + (-26994 / 125) * c ^ 2 * t ^ 4 + (-81097 / 1350000) * c ^ 2 * t ^ 6 + (36242477 / 675000) * c ^ 2 * t ^ 8 + (21742651 / 6750000) * c ^ 2 * t ^ 10 + (157349 / 562500) * c ^ 2 * t ^ 12 + (-87757 / 5062500) * c ^ 2 * t ^ 14 + (75203 / 1265625) * c ^ 2 * t ^ 18 + (-292 / 1265625) * c ^ 2 * t ^ 20) * alpha_sq + ((-24034 / 75) * t ^ 2 + (1586728 / 5625) * t ^ 4 + (239127941 / 900000) * t ^ 6 + (-33550439 / 150000) * t ^ 8 + (-10501813 / 1000000) * t ^ 10 + (6573941 / 2250000) * t ^ 12 + (-157016 / 421875) * t ^ 14 + (-3320591 / 27000000) * t ^ 18 + (-584 / 421875) * t ^ 20 + (-24034 / 75) * alpha * t ^ 2 + (3128488 / 5625) * alpha * t ^ 4 + (-665603377 / 2700000) * alpha * t ^ 6 + (10615841 / 1350000) * alpha * t ^ 8 + (-5030453 / 1000000) * alpha * t ^ 10 + (19436383 / 6750000) * alpha * t ^ 12 + (233624 / 421875) * alpha * t ^ 14 + (3121649 / 27000000) * alpha * t ^ 18 + (-584 / 421875) * alpha * t ^ 20) * c_sq
theorem v46_30 (t : ℂ) : (momentPoly 46 z46 3 0).eval t = ((-192 / 25) * t ^ 3 + (142 / 25) * t ^ 5 + 2 * t ^ 9 + (2383 / 375) * c * t ^ 3 + (-321 / 125) * c * t ^ 5 + (284 / 1125) * c * t ^ 9 + (-3413 / 1500) * alpha * t ^ 3 + (19977 / 1000) * alpha * t ^ 5 + (-46163 / 9000) * alpha * t ^ 9 + (292 / 75) * alpha * c * t ^ 3 + (-292 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_10, v45_20, v45_30]
  try simp only [phase43_00, phase43_10, phase43_20, phase43_30]
  try simp only [star_one, star_neg]
  linear_combination ((-2107 / 6000) * t ^ 3 + (-1397 / 6000) * t ^ 5 + (-697 / 2000) * c * t ^ 3 + (-1381 / 6000) * c * t ^ 5 + (1 / 375) * c ^ 2 * t ^ 3 + (1 / 375) * c ^ 2 * t ^ 5) * alpha_sq + ((4 / 375) * alpha * t ^ 3 + (4 / 375) * alpha * t ^ 5) * c_sq
theorem v46_31 (t : ℂ) : (momentPoly 46 z46 3 1).eval t = ((-87291 / 40) * t ^ 2 + (1026467 / 375) * t ^ 4 + (-333279 / 500) * t ^ 6 + (-12999 / 1000) * t ^ 10 + (-108 / 5) * c * t ^ 2 + (12589 / 750) * c * t ^ 4 + (-269 / 500) * c * t ^ 6 + (2909 / 1500) * c * t ^ 10 + (34731 / 40) * alpha * t ^ 2 + (-222667 / 375) * alpha * t ^ 4 + (-77121 / 500) * alpha * t ^ 6 + (12997 / 3000) * alpha * t ^ 10 + (-36 / 5) * alpha * c * t ^ 2 + (14189 / 2250) * alpha * c * t ^ 4 + (-623 / 500) * alpha * c * t ^ 6 + (501 / 500) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_10, v45_11, v45_20, v45_21, v45_30, v45_31]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21, phase43_30, phase43_31]
  try simp only [star_one, star_neg]
  linear_combination ((9 / 10) * t ^ 2 + (-87169 / 90000) * t ^ 4 + (7843 / 15000) * t ^ 6 + (-14209 / 90000) * t ^ 10 + (9 / 5) * c * t ^ 2 + (-8899 / 5625) * c * t ^ 4 + (10091 / 30000) * c * t ^ 6 + (-14209 / 90000) * c * t ^ 10 + (9 / 10) * c ^ 2 * t ^ 2 + (-1227 / 2000) * c ^ 2 * t ^ 4 + (-373 / 2000) * c ^ 2 * t ^ 6) * alpha_sq + ((-9 / 5) * t ^ 2 + (18031 / 22500) * t ^ 4 + (5611 / 7500) * t ^ 6 + (-71 / 5625) * t ^ 10 + (9 / 5) * alpha * t ^ 2 + (-35551 / 22500) * alpha * t ^ 4 + (229 / 7500) * alpha * t ^ 6 + (71 / 5625) * alpha * t ^ 10) * c_sq
theorem v46_32 (t : ℂ) : (momentPoly 46 z46 3 2).eval t = ((24572 / 5) * t + (-94963 / 10) * t ^ 3 + (338272141 / 60000) * t ^ 5 + (-37171423 / 40000) * t ^ 7 + (1076781 / 8000) * t ^ 9 + (-54503461 / 360000) * t ^ 11 + (-2693723 / 360000) * t ^ 13 + (-24572 / 15) * c * t + (154059 / 50) * c * t ^ 3 + (-27503827 / 15000) * c * t ^ 5 + (926459 / 2500) * c * t ^ 7 + (-48271 / 3000) * c * t ^ 9 + (-2813 / 5625) * c * t ^ 11 + (13586 / 5625) * c * t ^ 13 + (-24572 / 15) * alpha * t + (123621 / 50) * alpha * t ^ 3 + (-34973759 / 60000) * alpha * t ^ 5 + (-62873809 / 120000) * alpha * t ^ 7 + (25370351 / 120000) * alpha * t ^ 9 + (5152283 / 72000) * alpha * t ^ 11 + (-16039687 / 360000) * alpha * t ^ 13 + (-24572 / 15) * alpha * c * t + (14329 / 6) * alpha * c * t ^ 3 + (-2717873 / 5000) * alpha * c * t ^ 5 + (-5008813 / 22500) * alpha * c * t ^ 7 + (-229067 / 15000) * alpha * c * t ^ 9 + (-379 / 135) * alpha * c * t ^ 11 + (1694 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_10, v45_11, v45_12, v45_20, v45_21, v45_22, v45_30, v45_31, v45_32]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22, phase43_30, phase43_31, phase43_32]
  try simp only [star_one, star_neg]
  linear_combination ((187523 / 6000) * t ^ 3 + (-709549 / 90000) * t ^ 5 + (-1647947 / 112500) * t ^ 7 + (-89498 / 9375) * t ^ 9 + (-756949 / 1350000) * t ^ 11 + (3268681 / 1350000) * t ^ 13 + (62033 / 2000) * c * t ^ 3 + (-701411 / 90000) * c * t ^ 5 + (-25819973 / 1350000) * c * t ^ 7 + (92887 / 450000) * c * t ^ 9 + (62563 / 337500) * c * t ^ 11 + (-14209 / 675000) * c * t ^ 13 + (-89 / 375) * c ^ 2 * t ^ 3 + (4069 / 45000) * c ^ 2 * t ^ 5 + (5051 / 90000) * c ^ 2 * t ^ 7 + (-49 / 45000) * c ^ 2 * t ^ 9 + (4589 / 90000) * c ^ 2 * t ^ 11) * alpha_sq + ((178 / 125) * t ^ 3 + (-1479 / 2500) * t ^ 5 + (-115031 / 225000) * t ^ 7 + (1468 / 9375) * t ^ 9 + (-57971 / 225000) * t ^ 11 + (-142 / 28125) * t ^ 13 + (-178 / 375) * alpha * t ^ 3 + (-367 / 4500) * alpha * t ^ 5 + (187031 / 675000) * alpha * t ^ 7 + (4372 / 28125) * alpha * t ^ 9 + (33971 / 675000) * alpha * t ^ 11 + (142 / 84375) * alpha * t ^ 13) * c_sq
theorem v46_33 (t : ℂ) : (momentPoly 46 z46 3 3).eval t = (565156 + (-1081530) * t ^ 2 + (303530799 / 500) * t ^ 4 + (-6122598177 / 50000) * t ^ 6 + (406061969 / 10000) * t ^ 8 + (-989174577 / 200000) * t ^ 10 + (154824011 / 150000) * t ^ 12 + (-88319297 / 100000) * t ^ 14 + (30644653 / 600000) * t ^ 18 + (154176 / 125) * c * t ^ 4 + (-1347878 / 625) * c * t ^ 6 + (360601 / 375) * c * t ^ 8 + (-41257 / 625) * c * t ^ 10 + (-517771 / 5625) * c * t ^ 12 + (222457 / 1875) * c * t ^ 14 + (1136 / 1125) * c * t ^ 18) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_03, v45_10, v45_11, v45_12, v45_13, v45_20, v45_21, v45_22, v45_23, v45_30, v45_31, v45_32, v45_33]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23, phase43_30, phase43_31, phase43_32, phase43_33]
  try simp only [star_one, star_neg]
  linear_combination ((-12017 / 50) * t ^ 2 + (48477 / 125) * t ^ 4 + (-109183187 / 75000) * t ^ 6 + (98703727 / 120000) * t ^ 8 + (71668351 / 200000) * t ^ 10 + (416442569 / 27000000) * t ^ 12 + (-200241571 / 9000000) * t ^ 14 + (3530917 / 1687500) * t ^ 18 + (-12017 / 25) * c * t ^ 2 + (95392 / 125) * c * t ^ 4 + (-5883151 / 36000) * c * t ^ 6 + (-18582077 / 120000) * c * t ^ 8 + (1332973 / 40000) * c * t ^ 10 + (2224839 / 200000) * c * t ^ 12 + (-19182631 / 1800000) * c * t ^ 14 + (-12017 / 50) * c ^ 2 * t ^ 2 + (9383 / 25) * c ^ 2 * t ^ 4 + (-28302437 / 300000) * c ^ 2 * t ^ 6 + (-17863813 / 450000) * c ^ 2 * t ^ 8 + (-838061 / 300000) * c ^ 2 * t ^ 10 + (-88597 / 225000) * c ^ 2 * t ^ 12 + (4159 / 75000) * c ^ 2 * t ^ 14) * alpha_sq + ((24034 / 25) * t ^ 2 + (-200508 / 125) * t ^ 4 + (43020869 / 75000) * t ^ 6 + (827413 / 12500) * t ^ 8 + (280199 / 25000) * t ^ 10 + (722929 / 421875) * t ^ 12 + (-138236 / 140625) * t ^ 14 + (10082 / 421875) * t ^ 18) * c_sq
theorem v46_34 (t : ℂ) : (momentPoly 46 z46 3 4).eval t = ((4374902 / 5) * t + (-12538317 / 5) * t ^ 3 + (25596859267 / 10000) * t ^ 5 + (-822794701451 / 800000) * t ^ 7 + (751276106123 / 4800000) * t ^ 9 + (-612187541861 / 4800000) * t ^ 11 + (1213921047177 / 16000000) * t ^ 13 + (-10259537441 / 9000000) * t ^ 15 + (-136041275629 / 144000000) * t ^ 17 + (65830275379 / 216000000) * t ^ 19 + (251120993 / 9600000) * t ^ 21 + (15444820393 / 432000000) * t ^ 25 + (-4374902 / 15) * c * t + (20340981 / 25) * c * t ^ 3 + (-2127748899 / 2500) * c * t ^ 5 + (248098390781 / 600000) * c * t ^ 7 + (-53420484019 / 600000) * c * t ^ 9 + (295839569 / 80000) * c * t ^ 11 + (17636935043 / 18000000) * c * t ^ 13 + (-2772367979 / 4500000) * c * t ^ 15 + (99277913 / 1500000) * c * t ^ 17 + (-315036097 / 54000000) * c * t ^ 19 + (-49859629 / 3600000) * c * t ^ 21 + (39119257 / 13500000) * c * t ^ 25 + (4374902 / 15) * alpha * t + (-16322139 / 25) * alpha * t ^ 3 + (3552229233 / 10000) * alpha * t ^ 5 + (2372290630793 / 12000000) * alpha * t ^ 7 + (-5957825706563 / 24000000) * alpha * t ^ 9 + (4454265063 / 320000) * alpha * t ^ 11 + (7633684639963 / 144000000) * alpha * t ^ 13 + (-82929123643 / 9000000) * alpha * t ^ 15 + (-9118286977 / 9600000) * alpha * t ^ 17 + (19279781533 / 43200000) * alpha * t ^ 19 + (-10864378459 / 144000000) * alpha * t ^ 21 + (-16184522077 / 432000000) * alpha * t ^ 25 + (4374902 / 15) * alpha * c * t + (-630637) * alpha * c * t ^ 3 + (2673180809 / 7500) * alpha * c * t ^ 5 + (72275655487 / 3000000) * alpha * c * t ^ 7 + (-301766385203 / 9000000) * alpha * c * t ^ 9 + (-22500719629 / 3600000) * alpha * c * t ^ 11 + (-54869874137 / 54000000) * alpha * c * t ^ 13 + (-3110023727 / 13500000) * alpha * c * t ^ 15 + (1991351 / 540000) * alpha * c * t ^ 17 + (374716139 / 6480000) * alpha * c * t ^ 19 + (-167196101 / 6000000) * alpha * c * t ^ 21 + (-14665163 / 40500000) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_03, v45_04, v45_10, v45_11, v45_12, v45_13, v45_14, v45_20, v45_21, v45_22, v45_23, v45_24, v45_30, v45_31, v45_32, v45_33, v45_34]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24, phase43_30, phase43_31, phase43_32, phase43_33, phase43_34]
  try simp only [star_one, star_neg]
  linear_combination ((8253119 / 1000) * t ^ 3 + (-283774261 / 30000) * t ^ 5 + (-14248214959 / 14400000) * t ^ 7 + (-20905218883 / 8000000) * t ^ 9 + (75061888367 / 16000000) * t ^ 11 + (503565309847 / 432000000) * t ^ 13 + (-643729272107 / 540000000) * t ^ 15 + (35506406827 / 270000000) * t ^ 17 + (-153272813 / 51840000) * t ^ 19 + (-3939701923 / 720000000) * t ^ 21 + (-1853244133 / 810000000) * t ^ 25 + (8190447 / 1000) * c * t ^ 3 + (-280522169 / 30000) * c * t ^ 5 + (-744801907409 / 216000000) * c * t ^ 7 + (333040598533 / 72000000) * c * t ^ 9 + (17745248903 / 144000000) * c * t ^ 11 + (-21790762441 / 432000000) * c * t ^ 13 + (-342565151 / 540000000) * c * t ^ 15 + (-110333471 / 67500000) * c * t ^ 17 + (-3073951093 / 1296000000) * c * t ^ 19 + (-7704684937 / 2160000000) * c * t ^ 21 + (-1037257 / 25312500) * c * t ^ 25 + (-7834 / 125) * c ^ 2 * t ^ 3 + (813023 / 7500) * c ^ 2 * t ^ 5 + (-333083483 / 4500000) * c ^ 2 * t ^ 7 + (787477159 / 27000000) * c ^ 2 * t ^ 9 + (595492427 / 27000000) * c ^ 2 * t ^ 11 + (-451162123 / 18000000) * c ^ 2 * t ^ 13 + (212026 / 140625) * c ^ 2 * t ^ 15 + (1972 / 421875) * c ^ 2 * t ^ 17 + (-2544481 / 27000000) * c ^ 2 * t ^ 19 + (-102803 / 3600000) * c ^ 2 * t ^ 21) * alpha_sq + ((47004 / 125) * t ^ 3 + (-845039 / 1250) * t ^ 5 + (95704593 / 250000) * t ^ 7 + (-23597939 / 1125000) * t ^ 9 + (-805539361 / 4500000) * t ^ 11 + (7690117 / 60000) * t ^ 13 + (-87784681 / 11250000) * t ^ 15 + (-425821 / 1406250) * t ^ 17 + (1882391 / 2700000) * t ^ 19 + (472849 / 22500000) * t ^ 21 + (20732 / 2109375) * t ^ 25 + (15668 / 125) * alpha * t ^ 3 + (-479 / 6) * alpha * t ^ 5 + (-704616647 / 6750000) * alpha * t ^ 7 + (60307687 / 1125000) * alpha * t ^ 9 + (-6555173 / 300000) * alpha * t ^ 11 + (97957079 / 13500000) * alpha * t ^ 13 + (688059559 / 33750000) * alpha * t ^ 15 + (379459 / 4218750) * alpha * t ^ 17 + (28048243 / 40500000) * alpha * t ^ 19 + (-6727151 / 67500000) * alpha * t ^ 21 + (20732 / 6328125) * alpha * t ^ 25) * c_sq
theorem v46_40 (t : ℂ) : (momentPoly 46 z46 4 0).eval t = ((64097437 / 120000) * t ^ 4 + (-15219903 / 20000) * t ^ 6 + (13701817 / 80000) * t ^ 8 + (-1339401 / 20000) * t ^ 10 + (5773297 / 720000) * t ^ 16 + (-6224 / 625) * c * t ^ 4 + (53143 / 1875) * c * t ^ 6 + (-4798 / 1875) * c * t ^ 8 + (-5803 / 625) * c * t ^ 10 + (584 / 5625) * c * t ^ 16 + (-54736163 / 120000) * alpha * t ^ 4 + (18348931 / 60000) * alpha * t ^ 6 + (17319851 / 240000) * alpha * t ^ 8 + (-6380369 / 180000) * alpha * t ^ 10 + (-74327 / 80000) * alpha * t ^ 16 + (37712 / 5625) * alpha * c * t ^ 4 + (-17501 / 1875) * alpha * c * t ^ 6 + (-2294 / 1875) * alpha * c * t ^ 8 + (9409 / 5625) * alpha * c * t ^ 10 + (-584 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_10, v45_20, v45_30, v45_40]
  try simp only [phase43_00, phase43_10, phase43_20, phase43_30, phase43_40]
  try simp only [star_one, star_neg]
  linear_combination ((5266 / 5625) * t ^ 4 + (39503 / 5000) * t ^ 6 + (38033 / 15000) * t ^ 8 + (14209 / 22500) * t ^ 10 + (3076 / 5625) * c * t ^ 4 + (-12013 / 5625) * c * t ^ 6 + (-1397 / 22500) * c * t ^ 8 + (14209 / 22500) * c * t ^ 10 + (-146 / 375) * c ^ 2 * t ^ 4 + (2194 / 5625) * c ^ 2 * t ^ 6 + (2 / 5625) * c ^ 2 * t ^ 8) * alpha_sq + ((7127 / 11250) * t ^ 4 + (-1039 / 1250) * t ^ 6 + (4 / 1875) * t ^ 8 + (-284 / 5625) * t ^ 10 + (-10393 / 11250) * alpha * t ^ 4 + (2723 / 3750) * alpha * t ^ 6 + (4 / 1875) * alpha * t ^ 8 + (-284 / 5625) * alpha * t ^ 10) * c_sq
theorem v46_41 (t : ℂ) : (momentPoly 46 z46 4 1).eval t = ((-34176 / 25) * t ^ 3 + (1521942 / 625) * t ^ 5 + (-2607052 / 1875) * t ^ 7 + (1077508 / 1875) * t ^ 9 + (-1428128 / 5625) * t ^ 11 + (8882 / 5625) * t ^ 17 + (424174 / 375) * c * t ^ 3 + (-21734419 / 15000) * c * t ^ 5 + (3060379 / 7500) * c * t ^ 7 + (-126767 / 90000) * c * t ^ 9 + (-174683 / 7500) * c * t ^ 11 + (-26837 / 30000) * c * t ^ 17 + (-303757 / 750) * alpha * t ^ 3 + (50541709 / 15000) * alpha * t ^ 5 + (-17746549 / 7500) * alpha * t ^ 7 + (-86055323 / 90000) * alpha * t ^ 9 + (4118803 / 7500) * alpha * t ^ 11 + (297727 / 30000) * alpha * t ^ 17 + (51976 / 75) * alpha * c * t ^ 3 + (-6943874 / 5625) * alpha * c * t ^ 5 + (2923148 / 5625) * alpha * c * t ^ 7 + (113458 / 5625) * alpha * c * t ^ 9 + (7072 / 16875) * alpha * c * t ^ 11 + (20132 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_10, v45_11, v45_20, v45_21, v45_30, v45_31, v45_40, v45_41]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21, phase43_30, phase43_31, phase43_40, phase43_41]
  try simp only [star_one, star_neg]
  linear_combination ((-187523 / 3000) * t ^ 3 + (597761 / 80000) * t ^ 5 + (76246739 / 1800000) * t ^ 7 + (25372843 / 7200000) * t ^ 9 + (-5368577 / 5400000) * t ^ 11 + (-1313167 / 21600000) * t ^ 17 + (-62033 / 1000) * c * t ^ 3 + (5357641 / 720000) * c * t ^ 5 + (74494531 / 1800000) * c * t ^ 7 + (30021227 / 7200000) * c * t ^ 9 + (-5674753 / 5400000) * c * t ^ 11 + (-450181 / 7200000) * c * t ^ 17 + (178 / 375) * c ^ 2 * t ^ 3 + (-347 / 11250) * c ^ 2 * t ^ 5 + (-15529 / 56250) * c ^ 2 * t ^ 7 + (-1456 / 28125) * c ^ 2 * t ^ 9 + (-4784 / 84375) * c ^ 2 * t ^ 11 + (-146 / 84375) * c ^ 2 * t ^ 17) * alpha_sq + ((72 / 625) * t ^ 5 + (-16 / 25) * t ^ 7 + (584 / 1875) * t ^ 9 + (16 / 75) * t ^ 11 + (712 / 375) * alpha * t ^ 3 + (-5692 / 5625) * alpha * t ^ 5 + (5803 / 28125) * alpha * t ^ 7 + (-2446 / 28125) * alpha * t ^ 9 + (-49699 / 84375) * alpha * t ^ 11 + (584 / 84375) * alpha * t ^ 17) * c_sq
theorem v46_42 (t : ℂ) : (momentPoly 46 z46 4 2).eval t = ((-38850961 / 100) * t ^ 2 + (2300336137 / 3000) * t ^ 4 + (-338859080101 / 800000) * t ^ 6 + (20121073321 / 480000) * t ^ 8 + (-1494004801 / 960000) * t ^ 10 + (50643599239 / 14400000) * t ^ 12 + (-1794255371 / 3600000) * t ^ 14 + (-1785683371 / 14400000) * t ^ 18 + (780578219 / 14400000) * t ^ 20 + (-96136 / 25) * c * t ^ 2 + (2685284 / 375) * c * t ^ 4 + (-196078783 / 45000) * c * t ^ 6 + (1099511 / 1800) * c * t ^ 8 + (84995471 / 90000) * c * t ^ 10 + (-43943099 / 90000) * c * t ^ 12 + (-1225913 / 16875) * c * t ^ 14 + (-1986931 / 270000) * c * t ^ 18 + (36397 / 90000) * c * t ^ 20 + (46373603 / 300) * alpha * t ^ 2 + (-722480537 / 3000) * alpha * t ^ 4 + (92564038873 / 1440000) * alpha * t ^ 6 + (10788253351 / 480000) * alpha * t ^ 8 + (7514305427 / 2880000) * alpha * t ^ 10 + (-145152229 / 192000) * alpha * t ^ 12 + (-660404963 / 2160000) * alpha * t ^ 14 + (-369442691 / 8640000) * alpha * t ^ 18 + (-165756029 / 8640000) * alpha * t ^ 20 + (-96136 / 75) * alpha * c * t ^ 2 + (2966884 / 1125) * alpha * c * t ^ 4 + (-473660137 / 225000) * alpha * c * t ^ 6 + (33764437 / 45000) * alpha * c * t ^ 8 + (121707737 / 450000) * alpha * c * t ^ 10 + (-139946189 / 450000) * alpha * c * t ^ 12 + (1982869 / 84375) * alpha * c * t ^ 14 + (-691207 / 450000) * alpha * c * t ^ 18 + (-59603 / 270000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_10, v45_11, v45_12, v45_20, v45_21, v45_22, v45_30, v45_31, v45_32, v45_40, v45_41, v45_42]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22, phase43_30, phase43_31, phase43_32, phase43_40, phase43_41, phase43_42]
  try simp only [star_one, star_neg]
  linear_combination ((12017 / 75) * t ^ 2 + (-1917718 / 5625) * t ^ 4 + (291627673 / 900000) * t ^ 6 + (98211691 / 3600000) * t ^ 8 + (-260905987 / 1500000) * t ^ 10 + (345379301 / 36000000) * t ^ 12 + (450029951 / 27000000) * t ^ 14 + (57416789 / 27000000) * t ^ 18 + (67273751 / 108000000) * t ^ 20 + (24034 / 75) * c * t ^ 2 + (-3132448 / 5625) * c * t ^ 4 + (34988833 / 108000) * c * t ^ 6 + (-15645731 / 360000) * c * t ^ 8 + (-411239551 / 5400000) * c * t ^ 10 + (369504203 / 10800000) * c * t ^ 12 + (1254292 / 253125) * c * t ^ 14 + (10264463 / 16200000) * c * t ^ 18 + (26003 / 2160000) * c * t ^ 20 + (12017 / 75) * c ^ 2 * t ^ 2 + (-26994 / 125) * c ^ 2 * t ^ 4 + (-81097 / 1350000) * c ^ 2 * t ^ 6 + (36242477 / 675000) * c ^ 2 * t ^ 8 + (21742651 / 6750000) * c ^ 2 * t ^ 10 + (157349 / 562500) * c ^ 2 * t ^ 12 + (-87757 / 5062500) * c ^ 2 * t ^ 14 + (75203 / 1265625) * c ^ 2 * t ^ 18 + (-292 / 1265625) * c ^ 2 * t ^ 20) * alpha_sq + ((-24034 / 75) * t ^ 2 + (1586728 / 5625) * t ^ 4 + (239127941 / 900000) * t ^ 6 + (-33550439 / 150000) * t ^ 8 + (-10501813 / 1000000) * t ^ 10 + (6573941 / 2250000) * t ^ 12 + (-157016 / 421875) * t ^ 14 + (-3320591 / 27000000) * t ^ 18 + (-584 / 421875) * t ^ 20 + (24034 / 75) * alpha * t ^ 2 + (-3128488 / 5625) * alpha * t ^ 4 + (665603377 / 2700000) * alpha * t ^ 6 + (-10615841 / 1350000) * alpha * t ^ 8 + (5030453 / 1000000) * alpha * t ^ 10 + (-19436383 / 6750000) * alpha * t ^ 12 + (-233624 / 421875) * alpha * t ^ 14 + (-3121649 / 27000000) * alpha * t ^ 18 + (584 / 421875) * alpha * t ^ 20) * c_sq
theorem v46_43 (t : ℂ) : (momentPoly 46 z46 4 3).eval t = ((4374902 / 5) * t + (-12538317 / 5) * t ^ 3 + (25596859267 / 10000) * t ^ 5 + (-822794701451 / 800000) * t ^ 7 + (751276106123 / 4800000) * t ^ 9 + (-612187541861 / 4800000) * t ^ 11 + (1213921047177 / 16000000) * t ^ 13 + (-10259537441 / 9000000) * t ^ 15 + (-136041275629 / 144000000) * t ^ 17 + (65830275379 / 216000000) * t ^ 19 + (251120993 / 9600000) * t ^ 21 + (15444820393 / 432000000) * t ^ 25 + (-4374902 / 15) * c * t + (20340981 / 25) * c * t ^ 3 + (-2127748899 / 2500) * c * t ^ 5 + (248098390781 / 600000) * c * t ^ 7 + (-53420484019 / 600000) * c * t ^ 9 + (295839569 / 80000) * c * t ^ 11 + (17636935043 / 18000000) * c * t ^ 13 + (-2772367979 / 4500000) * c * t ^ 15 + (99277913 / 1500000) * c * t ^ 17 + (-315036097 / 54000000) * c * t ^ 19 + (-49859629 / 3600000) * c * t ^ 21 + (39119257 / 13500000) * c * t ^ 25 + (-4374902 / 15) * alpha * t + (16322139 / 25) * alpha * t ^ 3 + (-3552229233 / 10000) * alpha * t ^ 5 + (-2372290630793 / 12000000) * alpha * t ^ 7 + (5957825706563 / 24000000) * alpha * t ^ 9 + (-4454265063 / 320000) * alpha * t ^ 11 + (-7633684639963 / 144000000) * alpha * t ^ 13 + (82929123643 / 9000000) * alpha * t ^ 15 + (9118286977 / 9600000) * alpha * t ^ 17 + (-19279781533 / 43200000) * alpha * t ^ 19 + (10864378459 / 144000000) * alpha * t ^ 21 + (16184522077 / 432000000) * alpha * t ^ 25 + (-4374902 / 15) * alpha * c * t + 630637 * alpha * c * t ^ 3 + (-2673180809 / 7500) * alpha * c * t ^ 5 + (-72275655487 / 3000000) * alpha * c * t ^ 7 + (301766385203 / 9000000) * alpha * c * t ^ 9 + (22500719629 / 3600000) * alpha * c * t ^ 11 + (54869874137 / 54000000) * alpha * c * t ^ 13 + (3110023727 / 13500000) * alpha * c * t ^ 15 + (-1991351 / 540000) * alpha * c * t ^ 17 + (-374716139 / 6480000) * alpha * c * t ^ 19 + (167196101 / 6000000) * alpha * c * t ^ 21 + (14665163 / 40500000) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_03, v45_10, v45_11, v45_12, v45_13, v45_20, v45_21, v45_22, v45_23, v45_30, v45_31, v45_32, v45_33, v45_40, v45_41, v45_42, v45_43]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23, phase43_30, phase43_31, phase43_32, phase43_33, phase43_40, phase43_41, phase43_42, phase43_43]
  try simp only [star_one, star_neg]
  linear_combination ((8253119 / 1000) * t ^ 3 + (-283774261 / 30000) * t ^ 5 + (-14248214959 / 14400000) * t ^ 7 + (-20905218883 / 8000000) * t ^ 9 + (75061888367 / 16000000) * t ^ 11 + (503565309847 / 432000000) * t ^ 13 + (-643729272107 / 540000000) * t ^ 15 + (35506406827 / 270000000) * t ^ 17 + (-153272813 / 51840000) * t ^ 19 + (-3939701923 / 720000000) * t ^ 21 + (-1853244133 / 810000000) * t ^ 25 + (8190447 / 1000) * c * t ^ 3 + (-280522169 / 30000) * c * t ^ 5 + (-744801907409 / 216000000) * c * t ^ 7 + (333040598533 / 72000000) * c * t ^ 9 + (17745248903 / 144000000) * c * t ^ 11 + (-21790762441 / 432000000) * c * t ^ 13 + (-342565151 / 540000000) * c * t ^ 15 + (-110333471 / 67500000) * c * t ^ 17 + (-3073951093 / 1296000000) * c * t ^ 19 + (-7704684937 / 2160000000) * c * t ^ 21 + (-1037257 / 25312500) * c * t ^ 25 + (-7834 / 125) * c ^ 2 * t ^ 3 + (813023 / 7500) * c ^ 2 * t ^ 5 + (-333083483 / 4500000) * c ^ 2 * t ^ 7 + (787477159 / 27000000) * c ^ 2 * t ^ 9 + (595492427 / 27000000) * c ^ 2 * t ^ 11 + (-451162123 / 18000000) * c ^ 2 * t ^ 13 + (212026 / 140625) * c ^ 2 * t ^ 15 + (1972 / 421875) * c ^ 2 * t ^ 17 + (-2544481 / 27000000) * c ^ 2 * t ^ 19 + (-102803 / 3600000) * c ^ 2 * t ^ 21) * alpha_sq + ((47004 / 125) * t ^ 3 + (-845039 / 1250) * t ^ 5 + (95704593 / 250000) * t ^ 7 + (-23597939 / 1125000) * t ^ 9 + (-805539361 / 4500000) * t ^ 11 + (7690117 / 60000) * t ^ 13 + (-87784681 / 11250000) * t ^ 15 + (-425821 / 1406250) * t ^ 17 + (1882391 / 2700000) * t ^ 19 + (472849 / 22500000) * t ^ 21 + (20732 / 2109375) * t ^ 25 + (-15668 / 125) * alpha * t ^ 3 + (479 / 6) * alpha * t ^ 5 + (704616647 / 6750000) * alpha * t ^ 7 + (-60307687 / 1125000) * alpha * t ^ 9 + (6555173 / 300000) * alpha * t ^ 11 + (-97957079 / 13500000) * alpha * t ^ 13 + (-688059559 / 33750000) * alpha * t ^ 15 + (-379459 / 4218750) * alpha * t ^ 17 + (-28048243 / 40500000) * alpha * t ^ 19 + (6727151 / 67500000) * alpha * t ^ 21 + (-20732 / 6328125) * alpha * t ^ 25) * c_sq
theorem v46_44 (t : ℂ) : (momentPoly 46 z46 4 4).eval t = (100622746 + (-253906320) * t ^ 2 + (26416377416 / 125) * t ^ 4 + (-895766527519 / 12500) * t ^ 6 + (5813334575770951 / 240000000) * t ^ 8 + (-196881054500173 / 20000000) * t ^ 10 + (-3258816819949 / 16000000) * t ^ 12 + (-110521360926787 / 120000000) * t ^ 14 + (1224663449960389 / 2880000000) * t ^ 16 + (5993966558443 / 360000000) * t ^ 18 + (-17856440097643 / 2160000000) * t ^ 20 + (-323122520123 / 40000000) * t ^ 22 + (2759441796469 / 1440000000) * t ^ 24 + (-1674109660271 / 1080000000) * t ^ 26 + (208016991119 / 8640000000) * t ^ 32 + (53671936 / 125) * c * t ^ 4 + (-2258125472 / 1875) * c * t ^ 6 + (874283215483 / 703125) * c * t ^ 8 + (-401739464968 / 703125) * c * t ^ 10 + (6903832079 / 281250) * c * t ^ 12 + (294351598024 / 2109375) * c * t ^ 14 + (-82617576763 / 1406250) * c * t ^ 16 + (-1429869439 / 703125) * c * t ^ 18 + (-263414441 / 4218750) * c * t ^ 20 + (-373502582 / 2109375) * c * t ^ 22 + (-4976393 / 4218750) * c * t ^ 24 + (-1093805191 / 6328125) * c * t ^ 26 + (11757088 / 6328125) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z46, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v45_00, v45_01, v45_02, v45_03, v45_04, v45_10, v45_11, v45_12, v45_13, v45_14, v45_20, v45_21, v45_22, v45_23, v45_24, v45_30, v45_31, v45_32, v45_33, v45_34, v45_40, v45_41, v45_42, v45_43, v45_44]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24, phase43_30, phase43_31, phase43_32, phase43_33, phase43_34, phase43_40, phase43_41, phase43_42, phase43_43, phase43_44]
  try simp only [star_one, star_neg]
  linear_combination ((-4231772 / 75) * t ^ 2 + (16875872 / 125) * t ^ 4 + (-6917370131 / 12500) * t ^ 6 + (164144877052 / 234375) * t ^ 8 + (-575450347589 / 5625000) * t ^ 10 + (-28995189744661 / 270000000) * t ^ 12 + (-8073172750837 / 270000000) * t ^ 14 + (65793893171 / 7200000) * t ^ 16 + (327331560199 / 108000000) * t ^ 18 + (-95197698593 / 67500000) * t ^ 20 + (113394074647 / 337500000) * t ^ 22 + (306458594143 / 2700000000) * t ^ 24 + (-172907445023 / 8100000000) * t ^ 26 + (-1745600423 / 4050000000) * t ^ 32 + (-8463544 / 75) * c * t ^ 2 + (99623936 / 375) * c * t ^ 4 + (-831803549 / 5625) * c * t ^ 6 + (-9747895494791 / 135000000) * c * t ^ 8 + (22463902190443 / 270000000) * c * t ^ 10 + (-1851205049377 / 270000000) * c * t ^ 12 + (-22776807570287 / 1620000000) * c * t ^ 14 + (52306246409 / 10800000) * c * t ^ 16 + (30289615997 / 180000000) * c * t ^ 18 + (-68158409453 / 810000000) * c * t ^ 20 + (199137935623 / 8100000000) * c * t ^ 22 + (1347143527 / 4050000000) * c * t ^ 24 + (267984113891 / 24300000000) * c * t ^ 26 + (-95861191 / 3037500000) * c * t ^ 32 + (-4231772 / 75) * c ^ 2 * t ^ 2 + (9799264 / 75) * c ^ 2 * t ^ 4 + (-2274551794 / 28125) * c ^ 2 * t ^ 6 + (-551306720743 / 135000000) * c ^ 2 * t ^ 8 + (1181781777221 / 135000000) * c ^ 2 * t ^ 10 + (453733242419 / 270000000) * c ^ 2 * t ^ 12 + (195961286711 / 810000000) * c ^ 2 * t ^ 14 + (2220077 / 108000) * c ^ 2 * t ^ 16 + (-37378037 / 22500000) * c ^ 2 * t ^ 18 + (-9307749283 / 810000000) * c ^ 2 * t ^ 20 + (22319577791 / 4050000000) * c ^ 2 * t ^ 22 + (-11466289 / 506250000) * c ^ 2 * t ^ 24 + (372372613 / 3037500000) * c ^ 2 * t ^ 26 + (-42632 / 94921875) * c ^ 2 * t ^ 32) * alpha_sq + ((16927088 / 75) * t ^ 2 + (-69801088 / 125) * t ^ 4 + (3968694464 / 9375) * t ^ 6 + (-844661029847 / 11250000) * t ^ 8 + (-93230872459 / 11250000) * t ^ 10 + (-79677355291 / 13500000) * t ^ 12 + (-106420632641 / 67500000) * t ^ 14 + (2046410413 / 5625000) * t ^ 16 + (4078511 / 1687500) * t ^ 18 + (341176361 / 13500000) * t ^ 20 + (-3071885441 / 337500000) * t ^ 22 + (-4165391 / 42187500) * t ^ 24 + (-226037879 / 126562500) * t ^ 26 + (170528 / 31640625) * t ^ 32) * c_sq
#print axioms v46_00
#print axioms v46_11
#print axioms v46_22
#print axioms v46_33
#print axioms v46_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v47_02 (t : ℂ) : (momentPoly 47 z47 0 2).eval t = ((-2407 / 120) * t ^ 2 + (947 / 120) * t ^ 4 + (-4 / 15) * c * t ^ 2 + (-1 / 15) * c * t ^ 4 + (-413 / 40) * alpha * t ^ 2 + (-221 / 120) * alpha * t ^ 4 + (4 / 45) * alpha * c * t ^ 2 + (1 / 45) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02]
  try simp only [phase43_00, phase43_01, phase43_02]
  try simp only [star_one, star_neg]
  linear_combination ((2 / 225) * t ^ 2 + (4 / 225) * c * t ^ 2 + (2 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((-4 / 225) * t ^ 2 + (-4 / 225) * alpha * t ^ 2) * c_sq
theorem v47_03 (t : ℂ) : (momentPoly 47 z47 0 3).eval t = ((-53 / 5) * t ^ 3 + (43 / 5) * t ^ 5 + 2 * t ^ 9 + (2951 / 300) * c * t ^ 3 + (-679 / 300) * c * t ^ 5 + (71 / 225) * c * t ^ 9 + (-901 / 150) * alpha * t ^ 3 + (-14089 / 600) * alpha * t ^ 5 + (8879 / 1800) * alpha * t ^ 9 + (-73 / 15) * alpha * c * t ^ 3 + (73 / 15) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_03]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03]
  try simp only [star_one, star_neg]
  linear_combination ((-3859 / 6000) * t ^ 3 + (-1981 / 6000) * t ^ 5 + (-3827 / 6000) * c * t ^ 3 + (-5879 / 18000) * c * t ^ 5 + (2 / 375) * c ^ 2 * t ^ 3 + (4 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-8 / 375) * alpha * t ^ 3 + (-16 / 1125) * alpha * t ^ 5) * c_sq
theorem v47_04 (t : ℂ) : (momentPoly 47 z47 0 4).eval t = ((16507033 / 24000) * t ^ 4 + (-4110771 / 4000) * t ^ 6 + (6507343 / 48000) * t ^ 8 + (-2982677 / 36000) * t ^ 10 + (1090237 / 144000) * t ^ 16 + (-4309 / 750) * c * t ^ 4 + (17867 / 500) * c * t ^ 6 + (-2107 / 750) * c * t ^ 8 + (-49891 / 4500) * c * t ^ 10 + (146 / 1125) * c * t ^ 16 + (6074893 / 8000) * alpha * t ^ 4 + (-5282599 / 12000) * alpha * t ^ 6 + (-4478671 / 48000) * alpha * t ^ 8 + (209581 / 4000) * alpha * t ^ 10 + (198211 / 144000) * alpha * t ^ 16 + (-19669 / 2250) * alpha * c * t ^ 4 + (21547 / 1500) * alpha * c * t ^ 6 + (3733 / 2250) * alpha * c * t ^ 8 + (-25891 / 13500) * alpha * c * t ^ 10 + (146 / 3375) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_03, v46_04]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04]
  try simp only [star_one, star_neg]
  linear_combination ((3413 / 11250) * t ^ 4 + (241753 / 15000) * t ^ 6 + (19783 / 5000) * t ^ 8 + (39091 / 67500) * t ^ 10 + (-809 / 3750) * c * t ^ 4 + (-9269 / 3750) * c * t ^ 6 + (-1981 / 22500) * c * t ^ 8 + (39091 / 67500) * c * t ^ 10 + (-584 / 1125) * c ^ 2 * t ^ 4 + (976 / 1875) * c ^ 2 * t ^ 6 + (8 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((3994 / 5625) * t ^ 4 + (-754 / 625) * t ^ 6 + (16 / 5625) * t ^ 8 + (-1136 / 16875) * t ^ 10 + (854 / 625) * alpha * t ^ 4 + (-4894 / 5625) * alpha * t ^ 6 + (-16 / 5625) * alpha * t ^ 8 + (1136 / 16875) * alpha * t ^ 10) * c_sq
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
theorem v47_12 (t : ℂ) : (momentPoly 47 z47 1 2).eval t = ((93 / 2) * t + (-995 / 24) * t ^ 3 + (179 / 24) * t ^ 5 + (-31 / 2) * c * t + (537 / 40) * c * t ^ 3 + (-251 / 120) * c * t ^ 5 + (31 / 2) * alpha * t + (-423 / 40) * alpha * t ^ 3 + (-91 / 120) * alpha * t ^ 5 + (31 / 2) * alpha * c * t + (-733 / 72) * alpha * c * t ^ 3 + (-83 / 72) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_10, v46_11, v46_12]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12]
  try simp only [star_one, star_neg]
  linear_combination ((3859 / 18000) * t ^ 3 + (1981 / 18000) * t ^ 5 + (3827 / 18000) * c * t ^ 3 + (5879 / 54000) * c * t ^ 5 + (-2 / 1125) * c ^ 2 * t ^ 3 + (-4 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((4 / 375) * t ^ 3 + (8 / 1125) * t ^ 5 + (4 / 1125) * alpha * t ^ 3 + (8 / 3375) * alpha * t ^ 5) * c_sq
theorem v47_13 (t : ℂ) : (momentPoly 47 z47 1 3).eval t = ((-55361 / 20) * t ^ 2 + (867707 / 300) * t ^ 4 + (-164949 / 400) * t ^ 6 + (-19321 / 1200) * t ^ 10 + (-184 / 5) * c * t ^ 2 + (16789 / 600) * c * t ^ 4 + (-749 / 400) * c * t ^ 6 + (943 / 400) * c * t ^ 10 + (-28497 / 20) * alpha * t ^ 2 + (285827 / 300) * alpha * t ^ 4 + (70251 / 400) * alpha * t ^ 6 + (-9241 / 1200) * alpha * t ^ 10 + (184 / 15) * alpha * c * t ^ 2 + (-18389 / 1800) * alpha * c * t ^ 4 + (783 / 400) * alpha * c * t ^ 6 + (-4429 / 3600) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_03, v46_10, v46_11, v46_12, v46_13]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13]
  try simp only [star_one, star_neg]
  linear_combination ((92 / 75) * t ^ 2 + (-45083 / 45000) * t ^ 4 + (5919 / 10000) * t ^ 6 + (-39091 / 270000) * t ^ 10 + (184 / 75) * c * t ^ 2 + (-79493 / 45000) * c * t ^ 4 + (10697 / 30000) * c * t ^ 6 + (-39091 / 270000) * c * t ^ 10 + (92 / 75) * c ^ 2 * t ^ 2 + (-1147 / 1500) * c ^ 2 * t ^ 4 + (-353 / 1500) * c ^ 2 * t ^ 6) * alpha_sq + ((-184 / 75) * t ^ 2 + (5221 / 5625) * t ^ 4 + (591 / 625) * t ^ 6 + (-284 / 16875) * t ^ 10 + (-184 / 75) * alpha * t ^ 2 + (1229 / 625) * alpha * t ^ 4 + (-521 / 5625) * alpha * t ^ 6 + (-284 / 16875) * alpha * t ^ 10) * c_sq
theorem v47_14 (t : ℂ) : (momentPoly 47 z47 1 4).eval t = ((-9646 / 5) * t ^ 3 + (852021 / 250) * t ^ 5 + (-729763 / 375) * t ^ 7 + (496529 / 750) * t ^ 9 + (-222032 / 1125) * t ^ 11 + (2783 / 1125) * t ^ 17 + (268541 / 150) * c * t ^ 3 + (-67982137 / 36000) * c * t ^ 5 + (1947619 / 6000) * c * t ^ 7 + (-498127 / 72000) * c * t ^ 9 + (-43081 / 2000) * c * t ^ 11 + (-57791 / 72000) * c * t ^ 17 + (-81991 / 75) * alpha * t ^ 3 + (-88082177 / 36000) * alpha * t ^ 5 + (14161579 / 6000) * alpha * t ^ 7 + (67164313 / 72000) * alpha * t ^ 9 + (-710281 / 2000) * alpha * t ^ 11 + (-857431 / 72000) * alpha * t ^ 17 + (-13286 / 15) * alpha * c * t ^ 3 + (3384337 / 2250) * alpha * c * t ^ 5 + (-676037 / 1125) * alpha * c * t ^ 7 + (-34829 / 2250) * alpha * c * t ^ 9 + (-1768 / 3375) * alpha * c * t ^ 11 + (-5033 / 3375) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_03, v46_04, v46_10, v46_11, v46_12, v46_13, v46_14]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14]
  try simp only [star_one, star_neg]
  linear_combination ((-351169 / 3000) * t ^ 3 + (100821997 / 3600000) * t ^ 5 + (104037571 / 1800000) * t ^ 7 + (32877611 / 7200000) * t ^ 9 + (-9499649 / 5400000) * t ^ 11 + (-1957391 / 21600000) * t ^ 17 + (-348257 / 3000) * c * t ^ 3 + (299356999 / 10800000) * c * t ^ 5 + (101673539 / 1800000) * c * t ^ 7 + (39076139 / 7200000) * c * t ^ 9 + (-3306667 / 1800000) * c * t ^ 11 + (-6021677 / 64800000) * c * t ^ 17 + (364 / 375) * c ^ 2 * t ^ 3 + (-24289 / 84375) * c ^ 2 * t ^ 5 + (-32359 / 84375) * c ^ 2 * t ^ 7 + (-5816 / 84375) * c ^ 2 * t ^ 9 + (-6568 / 84375) * c ^ 2 * t ^ 11 + (-584 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((-304 / 5625) * t ^ 5 + (-3632 / 5625) * t ^ 7 + (2336 / 5625) * t ^ 9 + (64 / 225) * t ^ 11 + (-1456 / 375) * alpha * t ^ 3 + (21716 / 9375) * alpha * t ^ 5 + (-13232 / 28125) * alpha * t ^ 7 + (824 / 9375) * alpha * t ^ 9 + (63908 / 84375) * alpha * t ^ 11 + (-2336 / 253125) * alpha * t ^ 17) * c_sq
theorem v47_20 (t : ℂ) : (momentPoly 47 z47 2 0).eval t = ((-2407 / 120) * t ^ 2 + (947 / 120) * t ^ 4 + (-4 / 15) * c * t ^ 2 + (-1 / 15) * c * t ^ 4 + (413 / 40) * alpha * t ^ 2 + (221 / 120) * alpha * t ^ 4 + (-4 / 45) * alpha * c * t ^ 2 + (-1 / 45) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_10, v46_20]
  try simp only [phase43_00, phase43_10, phase43_20]
  try simp only [star_one, star_neg]
  linear_combination ((2 / 225) * t ^ 2 + (4 / 225) * c * t ^ 2 + (2 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((-4 / 225) * t ^ 2 + (4 / 225) * alpha * t ^ 2) * c_sq
theorem v47_21 (t : ℂ) : (momentPoly 47 z47 2 1).eval t = ((93 / 2) * t + (-995 / 24) * t ^ 3 + (179 / 24) * t ^ 5 + (-31 / 2) * c * t + (537 / 40) * c * t ^ 3 + (-251 / 120) * c * t ^ 5 + (-31 / 2) * alpha * t + (423 / 40) * alpha * t ^ 3 + (91 / 120) * alpha * t ^ 5 + (-31 / 2) * alpha * c * t + (733 / 72) * alpha * c * t ^ 3 + (83 / 72) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_10, v46_11, v46_20, v46_21]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21]
  try simp only [star_one, star_neg]
  linear_combination ((3859 / 18000) * t ^ 3 + (1981 / 18000) * t ^ 5 + (3827 / 18000) * c * t ^ 3 + (5879 / 54000) * c * t ^ 5 + (-2 / 1125) * c ^ 2 * t ^ 3 + (-4 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((4 / 375) * t ^ 3 + (8 / 1125) * t ^ 5 + (-4 / 1125) * alpha * t ^ 3 + (-8 / 3375) * alpha * t ^ 5) * c_sq
theorem v47_22 (t : ℂ) : (momentPoly 47 z47 2 2).eval t = (4371 + (-4048) * t ^ 2 + (151681 / 400) * t ^ 4 + (-62383 / 600) * t ^ 6 + (32123 / 1200) * t ^ 8 + (1168 / 225) * c * t ^ 4 + (-292 / 75) * c * t ^ 6 + (-292 / 225) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_10, v46_11, v46_12, v46_20, v46_21, v46_22]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22]
  try simp only [star_one, star_neg]
  linear_combination ((-368 / 225) * t ^ 2 + (463 / 375) * t ^ 4 + (-277267 / 45000) * t ^ 6 + (-19783 / 15000) * t ^ 8 + (-736 / 225) * c * t ^ 2 + (8192 / 3375) * c * t ^ 4 + (7841 / 22500) * c * t ^ 6 + (1981 / 67500) * c * t ^ 8 + (-368 / 225) * c ^ 2 * t ^ 2 + (161 / 135) * c ^ 2 * t ^ 4 + (263 / 1875) * c ^ 2 * t ^ 6 + (-8 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((1472 / 225) * t ^ 2 + (-5756 / 1125) * t ^ 4 + (-132 / 625) * t ^ 6 + (32 / 16875) * t ^ 8) * c_sq
theorem v47_23 (t : ℂ) : (momentPoly 47 z47 2 3).eval t = ((12835 / 2) * t + (-90545 / 8) * t ^ 3 + (1515427 / 240) * t ^ 5 + (-5134849 / 4800) * t ^ 7 + (1016417 / 4800) * t ^ 9 + (-3261701 / 14400) * t ^ 11 + (-239623 / 14400) * t ^ 13 + (-12835 / 6) * c * t + (146601 / 40) * c * t ^ 3 + (-25136947 / 12000) * c * t ^ 5 + (115403 / 240) * c * t ^ 7 + (-211363 / 12000) * c * t ^ 9 + (-12277 / 9000) * c * t ^ 11 + (3209 / 1125) * c * t ^ 13 + (12835 / 6) * alpha * t + (-115479 / 40) * alpha * t ^ 3 + (1236587 / 2000) * alpha * t ^ 5 + (842967 / 1600) * alpha * t ^ 7 + (-6025369 / 24000) * alpha * t ^ 9 + (-5976259 / 72000) * alpha * t ^ 11 + (2943919 / 72000) * alpha * t ^ 13 + (12835 / 6) * alpha * c * t + (-66703 / 24) * alpha * c * t ^ 3 + (6028531 / 12000) * alpha * c * t ^ 5 + (159647 / 720) * alpha * c * t ^ 7 + (578537 / 36000) * alpha * c * t ^ 9 + (109903 / 27000) * alpha * c * t ^ 11 + (139 / 3375) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_03, v46_10, v46_11, v46_12, v46_13, v46_20, v46_21, v46_22, v46_23]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23]
  try simp only [star_one, star_neg]
  linear_combination ((351169 / 6000) * t ^ 3 + (-216053 / 10000) * t ^ 5 + (-5106391 / 225000) * t ^ 7 + (-540127 / 50000) * t ^ 9 + (-164471 / 168750) * t ^ 11 + (3010553 / 1350000) * t ^ 13 + (348257 / 6000) * c * t ^ 3 + (-5764399 / 270000) * c * t ^ 5 + (-4253539 / 168750) * c * t ^ 7 + (101767 / 225000) * c * t ^ 9 + (247117 / 675000) * c * t ^ 11 + (-39091 / 2025000) * c * t ^ 13 + (-182 / 375) * c ^ 2 * t ^ 3 + (8629 / 33750) * c ^ 2 * t ^ 5 + (3611 / 67500) * c ^ 2 * t ^ 7 + (-109 / 33750) * c ^ 2 * t ^ 9 + (167 / 2500) * c ^ 2 * t ^ 11) * alpha_sq + ((364 / 125) * t ^ 3 + (-9581 / 5625) * t ^ 5 + (-8687 / 18750) * t ^ 7 + (5888 / 28125) * t ^ 9 + (-6371 / 18750) * t ^ 11 + (-568 / 84375) * t ^ 13 + (364 / 375) * alpha * t ^ 3 + (-973 / 16875) * alpha * t ^ 5 + (-73421 / 168750) * alpha * t ^ 7 + (-5824 / 28125) * alpha * t ^ 9 + (-11113 / 168750) * alpha * t ^ 11 + (-568 / 253125) * alpha * t ^ 13) * c_sq
theorem v47_24 (t : ℂ) : (momentPoly 47 z47 2 4).eval t = ((-1511596 / 3) * t ^ 2 + (33898741 / 40) * t ^ 4 + (-157480856611 / 480000) * t ^ 6 + (-3802409449 / 160000) * t ^ 8 + (-167470719 / 64000) * t ^ 10 + (11655313159 / 2880000) * t ^ 12 + (-159116833 / 240000) * t ^ 14 + (-482168719 / 2880000) * t ^ 18 + (13750851 / 320000) * t ^ 20 + (-20096 / 3) * c * t ^ 2 + (58552 / 5) * c * t ^ 4 + (-81017 / 12) * c * t ^ 6 + (807861 / 800) * c * t ^ 8 + (20468741 / 18000) * c * t ^ 10 + (-38124911 / 72000) * c * t ^ 12 + (-257326 / 3375) * c * t ^ 14 + (-556739 / 54000) * c * t ^ 18 + (31597 / 72000) * c * t ^ 20 + (-259364) * alpha * t ^ 2 + (15528581 / 40) * alpha * t ^ 4 + (-164581004569 / 1440000) * alpha * t ^ 6 + (-29062472993 / 1440000) * alpha * t ^ 8 + (-2246912263 / 576000) * alpha * t ^ 10 + (12256214021 / 8640000) * alpha * t ^ 12 + (299579533 / 720000) * alpha * t ^ 14 + (19469337 / 320000) * alpha * t ^ 18 + (219172801 / 8640000) * alpha * t ^ 20 + (20096 / 9) * alpha * c * t ^ 2 + (-63352 / 15) * alpha * c * t ^ 4 + (4540847 / 1500) * alpha * c * t ^ 6 + (-3920291 / 4000) * alpha * c * t ^ 8 + (-1851437 / 6000) * alpha * c * t ^ 10 + (15201443 / 43200) * alpha * c * t ^ 12 + (-110159 / 3375) * alpha * c * t ^ 14 + (102209 / 54000) * alpha * c * t ^ 18 + (64403 / 216000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_03, v46_04, v46_10, v46_11, v46_12, v46_13, v46_14, v46_20, v46_21, v46_22, v46_23, v46_24]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24]
  try simp only [star_one, star_neg]
  linear_combination ((10048 / 45) * t ^ 2 + (-45083 / 125) * t ^ 4 + (137122597 / 450000) * t ^ 6 + (268196471 / 2000000) * t ^ 8 + (-2086754293 / 9000000) * t ^ 10 + (-1655293729 / 108000000) * t ^ 12 + (203487989 / 9000000) * t ^ 14 + (5972063 / 1687500) * t ^ 18 + (38100701 / 36000000) * t ^ 20 + (20096 / 45) * c * t ^ 2 + (-79493 / 125) * c * t ^ 4 + (79367687 / 270000) * c * t ^ 6 + (-155794289 / 5400000) * c * t ^ 8 + (-49780487 / 675000) * c * t ^ 10 + (230692211 / 10800000) * c * t ^ 12 + (4177793 / 1012500) * c * t ^ 14 + (3130387 / 4050000) * c * t ^ 18 + (35603 / 2160000) * c * t ^ 20 + (10048 / 45) * c ^ 2 * t ^ 2 + (-6882 / 25) * c ^ 2 * t ^ 4 + (-3632339 / 337500) * c ^ 2 * t ^ 6 + (162902059 / 2531250) * c ^ 2 * t ^ 8 + (626129 / 187500) * c ^ 2 * t ^ 10 + (502228 / 1265625) * c ^ 2 * t ^ 12 + (-7531 / 1265625) * c ^ 2 * t ^ 14 + (100076 / 1265625) * c ^ 2 * t ^ 18 + (-1168 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-20096 / 45) * t ^ 2 + (41768 / 125) * t ^ 4 + (84222391 / 225000) * t ^ 6 + (-455287529 / 1687500) * t ^ 8 + (-24984127 / 2250000) * t ^ 10 + (5837629 / 1687500) * t ^ 12 + (-240112 / 421875) * t ^ 14 + (-1226693 / 6750000) * t ^ 18 + (-2336 / 1265625) * t ^ 20 + (-20096 / 45) * alpha * t ^ 2 + (88488 / 125) * alpha * t ^ 4 + (-204542491 / 675000) * alpha * t ^ 6 + (46216151 / 1687500) * alpha * t ^ 8 + (-41594941 / 6750000) * alpha * t ^ 10 + (17035447 / 5062500) * alpha * t ^ 12 + (842224 / 1265625) * alpha * t ^ 14 + (2762161 / 20250000) * alpha * t ^ 18 + (-2336 / 1265625) * alpha * t ^ 20) * c_sq
theorem v47_30 (t : ℂ) : (momentPoly 47 z47 3 0).eval t = ((-53 / 5) * t ^ 3 + (43 / 5) * t ^ 5 + 2 * t ^ 9 + (2951 / 300) * c * t ^ 3 + (-679 / 300) * c * t ^ 5 + (71 / 225) * c * t ^ 9 + (901 / 150) * alpha * t ^ 3 + (14089 / 600) * alpha * t ^ 5 + (-8879 / 1800) * alpha * t ^ 9 + (73 / 15) * alpha * c * t ^ 3 + (-73 / 15) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_10, v46_20, v46_30]
  try simp only [phase43_00, phase43_10, phase43_20, phase43_30]
  try simp only [star_one, star_neg]
  linear_combination ((-3859 / 6000) * t ^ 3 + (-1981 / 6000) * t ^ 5 + (-3827 / 6000) * c * t ^ 3 + (-5879 / 18000) * c * t ^ 5 + (2 / 375) * c ^ 2 * t ^ 3 + (4 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((8 / 375) * alpha * t ^ 3 + (16 / 1125) * alpha * t ^ 5) * c_sq
theorem v47_31 (t : ℂ) : (momentPoly 47 z47 3 1).eval t = ((-55361 / 20) * t ^ 2 + (867707 / 300) * t ^ 4 + (-164949 / 400) * t ^ 6 + (-19321 / 1200) * t ^ 10 + (-184 / 5) * c * t ^ 2 + (16789 / 600) * c * t ^ 4 + (-749 / 400) * c * t ^ 6 + (943 / 400) * c * t ^ 10 + (28497 / 20) * alpha * t ^ 2 + (-285827 / 300) * alpha * t ^ 4 + (-70251 / 400) * alpha * t ^ 6 + (9241 / 1200) * alpha * t ^ 10 + (-184 / 15) * alpha * c * t ^ 2 + (18389 / 1800) * alpha * c * t ^ 4 + (-783 / 400) * alpha * c * t ^ 6 + (4429 / 3600) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_10, v46_11, v46_20, v46_21, v46_30, v46_31]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21, phase43_30, phase43_31]
  try simp only [star_one, star_neg]
  linear_combination ((92 / 75) * t ^ 2 + (-45083 / 45000) * t ^ 4 + (5919 / 10000) * t ^ 6 + (-39091 / 270000) * t ^ 10 + (184 / 75) * c * t ^ 2 + (-79493 / 45000) * c * t ^ 4 + (10697 / 30000) * c * t ^ 6 + (-39091 / 270000) * c * t ^ 10 + (92 / 75) * c ^ 2 * t ^ 2 + (-1147 / 1500) * c ^ 2 * t ^ 4 + (-353 / 1500) * c ^ 2 * t ^ 6) * alpha_sq + ((-184 / 75) * t ^ 2 + (5221 / 5625) * t ^ 4 + (591 / 625) * t ^ 6 + (-284 / 16875) * t ^ 10 + (184 / 75) * alpha * t ^ 2 + (-1229 / 625) * alpha * t ^ 4 + (521 / 5625) * alpha * t ^ 6 + (284 / 16875) * alpha * t ^ 10) * c_sq
theorem v47_32 (t : ℂ) : (momentPoly 47 z47 3 2).eval t = ((12835 / 2) * t + (-90545 / 8) * t ^ 3 + (1515427 / 240) * t ^ 5 + (-5134849 / 4800) * t ^ 7 + (1016417 / 4800) * t ^ 9 + (-3261701 / 14400) * t ^ 11 + (-239623 / 14400) * t ^ 13 + (-12835 / 6) * c * t + (146601 / 40) * c * t ^ 3 + (-25136947 / 12000) * c * t ^ 5 + (115403 / 240) * c * t ^ 7 + (-211363 / 12000) * c * t ^ 9 + (-12277 / 9000) * c * t ^ 11 + (3209 / 1125) * c * t ^ 13 + (-12835 / 6) * alpha * t + (115479 / 40) * alpha * t ^ 3 + (-1236587 / 2000) * alpha * t ^ 5 + (-842967 / 1600) * alpha * t ^ 7 + (6025369 / 24000) * alpha * t ^ 9 + (5976259 / 72000) * alpha * t ^ 11 + (-2943919 / 72000) * alpha * t ^ 13 + (-12835 / 6) * alpha * c * t + (66703 / 24) * alpha * c * t ^ 3 + (-6028531 / 12000) * alpha * c * t ^ 5 + (-159647 / 720) * alpha * c * t ^ 7 + (-578537 / 36000) * alpha * c * t ^ 9 + (-109903 / 27000) * alpha * c * t ^ 11 + (-139 / 3375) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_10, v46_11, v46_12, v46_20, v46_21, v46_22, v46_30, v46_31, v46_32]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22, phase43_30, phase43_31, phase43_32]
  try simp only [star_one, star_neg]
  linear_combination ((351169 / 6000) * t ^ 3 + (-216053 / 10000) * t ^ 5 + (-5106391 / 225000) * t ^ 7 + (-540127 / 50000) * t ^ 9 + (-164471 / 168750) * t ^ 11 + (3010553 / 1350000) * t ^ 13 + (348257 / 6000) * c * t ^ 3 + (-5764399 / 270000) * c * t ^ 5 + (-4253539 / 168750) * c * t ^ 7 + (101767 / 225000) * c * t ^ 9 + (247117 / 675000) * c * t ^ 11 + (-39091 / 2025000) * c * t ^ 13 + (-182 / 375) * c ^ 2 * t ^ 3 + (8629 / 33750) * c ^ 2 * t ^ 5 + (3611 / 67500) * c ^ 2 * t ^ 7 + (-109 / 33750) * c ^ 2 * t ^ 9 + (167 / 2500) * c ^ 2 * t ^ 11) * alpha_sq + ((364 / 125) * t ^ 3 + (-9581 / 5625) * t ^ 5 + (-8687 / 18750) * t ^ 7 + (5888 / 28125) * t ^ 9 + (-6371 / 18750) * t ^ 11 + (-568 / 84375) * t ^ 13 + (-364 / 375) * alpha * t ^ 3 + (973 / 16875) * alpha * t ^ 5 + (73421 / 168750) * alpha * t ^ 7 + (5824 / 28125) * alpha * t ^ 9 + (11113 / 168750) * alpha * t ^ 11 + (568 / 253125) * alpha * t ^ 13) * c_sq
theorem v47_33 (t : ℂ) : (momentPoly 47 z47 3 3).eval t = (603245 + (-828960) * t ^ 2 + (12286161 / 80) * t ^ 4 + (486433551 / 10000) * t ^ 6 + (402204787 / 10000) * t ^ 8 + (-64662681 / 40000) * t ^ 10 + (5512201 / 3750) * t ^ 12 + (-20126043 / 20000) * t ^ 14 + (6252313 / 120000) * t ^ 18 + (10512 / 5) * c * t ^ 4 + (-2722937 / 750) * c * t ^ 6 + (492713 / 300) * c * t ^ 8 + (-81977 / 500) * c * t ^ 10 + (-448651 / 4500) * c * t ^ 12 + (74099 / 500) * c * t ^ 14 + (284 / 225) * c * t ^ 18) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_03, v46_10, v46_11, v46_12, v46_13, v46_20, v46_21, v46_22, v46_23, v46_30, v46_31, v46_32, v46_33]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23, phase43_30, phase43_31, phase43_32, phase43_33]
  try simp only [star_one, star_neg]
  linear_combination ((-5024 / 15) * t ^ 2 + (12501 / 25) * t ^ 4 + (-801083599 / 300000) * t ^ 6 + (65003497 / 40000) * t ^ 8 + (59120467 / 120000) * t ^ 10 + (410557961 / 27000000) * t ^ 12 + (-264690827 / 9000000) * t ^ 14 + (10202023 / 5062500) * t ^ 18 + (-10048 / 15) * c * t ^ 2 + (24576 / 25) * c * t ^ 4 + (-32348077 / 180000) * c * t ^ 6 + (-66050167 / 360000) * c * t ^ 8 + (4650587 / 120000) * c * t ^ 10 + (7332461 / 600000) * c * t ^ 12 + (-18308743 / 1800000) * c * t ^ 14 + (-5024 / 15) * c ^ 2 * t ^ 2 + 483 * c ^ 2 * t ^ 4 + (-24361877 / 225000) * c ^ 2 * t ^ 6 + (-14969843 / 337500) * c ^ 2 * t ^ 8 + (-231559 / 75000) * c ^ 2 * t ^ 10 + (-379 / 675) * c ^ 2 * t ^ 12 + (7897 / 168750) * c ^ 2 * t ^ 14) * alpha_sq + ((20096 / 15) * t ^ 2 + (-51804 / 25) * t ^ 4 + (4338797 / 6250) * t ^ 6 + (1620281 / 28125) * t ^ 8 + (46963 / 3750) * t ^ 10 + (1091206 / 421875) * t ^ 12 + (-155072 / 140625) * t ^ 14 + (40328 / 1265625) * t ^ 18) * c_sq
theorem v47_34 (t : ℂ) : (momentPoly 47 z47 3 4).eval t = ((2336525 / 2) * t + (-3056640) * t ^ 3 + (14172671 / 5) * t ^ 5 + (-79883156711 / 80000) * t ^ 7 + (138494933917 / 960000) * t ^ 9 + (-11418211697 / 60000) * t ^ 11 + (206724964753 / 1920000) * t ^ 13 + (-34792229 / 48000) * t ^ 15 + (-7782807869 / 5760000) * t ^ 17 + (567215041 / 1080000) * t ^ 19 + (407211881 / 5760000) * t ^ 21 + (762098777 / 17280000) * t ^ 25 + (-2336525 / 6) * c * t + (4948992 / 5) * c * t ^ 3 + (-1935825133 / 2000) * c * t ^ 5 + (376284456691 / 800000) * c * t ^ 7 + (-260595973883 / 2400000) * c * t ^ 9 + (3591879777 / 1600000) * c * t ^ 11 + (4009684507 / 2880000) * c * t ^ 13 + (-666715853 / 1200000) * c * t ^ 15 + (29705267 / 400000) * c * t ^ 17 + (-48699241 / 43200000) * c * t ^ 19 + (-18045373 / 14400000) * c * t ^ 21 + (37319257 / 10800000) * c * t ^ 25 + (2336525 / 6) * alpha * t + (-3898368 / 5) * alpha * t ^ 3 + (48099788 / 125) * alpha * t ^ 5 + (232166654549 / 1200000) * alpha * t ^ 7 + (-1147673959621 / 4800000) * alpha * t ^ 9 + (220373791 / 50000) * alpha * t ^ 11 + (19876762879 / 384000) * alpha * t ^ 13 + (-2790230383 / 1200000) * alpha * t ^ 15 + (-7051871657 / 9600000) * alpha * t ^ 17 + (3777236353 / 5400000) * alpha * t ^ 19 + (-2670244721 / 28800000) * alpha * t ^ 21 + (-2741453569 / 86400000) * alpha * t ^ 25 + (2336525 / 6) * alpha * c * t + (-750592) * alpha * c * t ^ 3 + (2107887527 / 6000) * alpha * c * t ^ 5 + (333298679813 / 7200000) * alpha * c * t ^ 7 + (-64086225301 / 2400000) * alpha * c * t ^ 9 + (-79746386809 / 14400000) * alpha * c * t ^ 11 + (-3609169867 / 2880000) * alpha * c * t ^ 13 + (-1343605993 / 3600000) * alpha * c * t ^ 15 + (-57784417 / 10800000) * alpha * c * t ^ 17 + (9726609899 / 129600000) * alpha * c * t ^ 19 + (-1434549593 / 43200000) * alpha * c * t ^ 21 + (-9265163 / 32400000) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_03, v46_04, v46_10, v46_11, v46_12, v46_13, v46_14, v46_20, v46_21, v46_22, v46_23, v46_24, v46_30, v46_31, v46_32, v46_33, v46_34]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24, phase43_30, phase43_31, phase43_32, phase43_33, phase43_34]
  try simp only [star_one, star_neg]
  linear_combination ((1975808 / 125) * t ^ 3 + (-583965671 / 30000) * t ^ 5 + (-1494913933 / 4800000) * t ^ 7 + (-24311858797 / 24000000) * t ^ 9 + (656809288079 / 144000000) * t ^ 11 + (2739814832263 / 2160000000) * t ^ 13 + (-176435545901 / 180000000) * t ^ 15 + (31299227459 / 270000000) * t ^ 17 + (-11241989953 / 6480000000) * t ^ 19 + (-16136468693 / 2160000000) * t ^ 21 + (-1710870629 / 810000000) * t ^ 25 + (1959424 / 125) * c * t ^ 3 + (-1731925157 / 90000) * c * t ^ 5 + (-395005416617 / 216000000) * c * t ^ 7 + (413520122249 / 72000000) * c * t ^ 9 + (2265188007 / 16000000) * c * t ^ 11 + (-226843912921 / 2160000000) * c * t ^ 13 + (-4641424979 / 540000000) * c * t ^ 15 + (-83761187 / 67500000) * c * t ^ 17 + (-8258539243 / 2160000000) * c * t ^ 19 + (-11056971349 / 2160000000) * c * t ^ 21 + (-2853643 / 75937500) * c * t ^ 25 + (-16384 / 125) * c ^ 2 * t ^ 3 + (1248241 / 5625) * c ^ 2 * t ^ 5 + (-928416211 / 6750000) * c ^ 2 * t ^ 7 + (297433943 / 6750000) * c ^ 2 * t ^ 9 + (127977913 / 4500000) * c ^ 2 * t ^ 11 + (-421705519 / 13500000) * c ^ 2 * t ^ 13 + (1924417 / 843750) * c ^ 2 * t ^ 15 + (3388 / 1265625) * c ^ 2 * t ^ 17 + (-4856639 / 40500000) * c ^ 2 * t ^ 19 + (-107603 / 2700000) * c ^ 2 * t ^ 21) * alpha_sq + ((98304 / 125) * t ^ 3 + (-888646 / 625) * t ^ 5 + (948873923 / 1125000) * t ^ 7 + (-13031851 / 112500) * t ^ 9 + (-502164143 / 2250000) * t ^ 11 + (2695612129 / 16875000) * t ^ 13 + (-35922031 / 2812500) * t ^ 15 + (-765178 / 2109375) * t ^ 17 + (11582473 / 11250000) * t ^ 19 + (271387 / 5625000) * t ^ 21 + (82928 / 6328125) * t ^ 25 + (32768 / 125) * alpha * t ^ 3 + (-1133714 / 5625) * alpha * t ^ 5 + (-542808253 / 3375000) * alpha * t ^ 7 + (59432051 / 562500) * alpha * t ^ 9 + (-79559717 / 2250000) * alpha * t ^ 11 + (416776769 / 50625000) * alpha * t ^ 13 + (221459009 / 8437500) * alpha * t ^ 15 + (281794 / 2109375) * alpha * t ^ 17 + (34436873 / 33750000) * alpha * t ^ 19 + (-2128613 / 16875000) * alpha * t ^ 21 + (82928 / 18984375) * alpha * t ^ 25) * c_sq
theorem v47_40 (t : ℂ) : (momentPoly 47 z47 4 0).eval t = ((16507033 / 24000) * t ^ 4 + (-4110771 / 4000) * t ^ 6 + (6507343 / 48000) * t ^ 8 + (-2982677 / 36000) * t ^ 10 + (1090237 / 144000) * t ^ 16 + (-4309 / 750) * c * t ^ 4 + (17867 / 500) * c * t ^ 6 + (-2107 / 750) * c * t ^ 8 + (-49891 / 4500) * c * t ^ 10 + (146 / 1125) * c * t ^ 16 + (-6074893 / 8000) * alpha * t ^ 4 + (5282599 / 12000) * alpha * t ^ 6 + (4478671 / 48000) * alpha * t ^ 8 + (-209581 / 4000) * alpha * t ^ 10 + (-198211 / 144000) * alpha * t ^ 16 + (19669 / 2250) * alpha * c * t ^ 4 + (-21547 / 1500) * alpha * c * t ^ 6 + (-3733 / 2250) * alpha * c * t ^ 8 + (25891 / 13500) * alpha * c * t ^ 10 + (-146 / 3375) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_10, v46_20, v46_30, v46_40]
  try simp only [phase43_00, phase43_10, phase43_20, phase43_30, phase43_40]
  try simp only [star_one, star_neg]
  linear_combination ((3413 / 11250) * t ^ 4 + (241753 / 15000) * t ^ 6 + (19783 / 5000) * t ^ 8 + (39091 / 67500) * t ^ 10 + (-809 / 3750) * c * t ^ 4 + (-9269 / 3750) * c * t ^ 6 + (-1981 / 22500) * c * t ^ 8 + (39091 / 67500) * c * t ^ 10 + (-584 / 1125) * c ^ 2 * t ^ 4 + (976 / 1875) * c ^ 2 * t ^ 6 + (8 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((3994 / 5625) * t ^ 4 + (-754 / 625) * t ^ 6 + (16 / 5625) * t ^ 8 + (-1136 / 16875) * t ^ 10 + (-854 / 625) * alpha * t ^ 4 + (4894 / 5625) * alpha * t ^ 6 + (16 / 5625) * alpha * t ^ 8 + (-1136 / 16875) * alpha * t ^ 10) * c_sq
theorem v47_41 (t : ℂ) : (momentPoly 47 z47 4 1).eval t = ((-9646 / 5) * t ^ 3 + (852021 / 250) * t ^ 5 + (-729763 / 375) * t ^ 7 + (496529 / 750) * t ^ 9 + (-222032 / 1125) * t ^ 11 + (2783 / 1125) * t ^ 17 + (268541 / 150) * c * t ^ 3 + (-67982137 / 36000) * c * t ^ 5 + (1947619 / 6000) * c * t ^ 7 + (-498127 / 72000) * c * t ^ 9 + (-43081 / 2000) * c * t ^ 11 + (-57791 / 72000) * c * t ^ 17 + (81991 / 75) * alpha * t ^ 3 + (88082177 / 36000) * alpha * t ^ 5 + (-14161579 / 6000) * alpha * t ^ 7 + (-67164313 / 72000) * alpha * t ^ 9 + (710281 / 2000) * alpha * t ^ 11 + (857431 / 72000) * alpha * t ^ 17 + (13286 / 15) * alpha * c * t ^ 3 + (-3384337 / 2250) * alpha * c * t ^ 5 + (676037 / 1125) * alpha * c * t ^ 7 + (34829 / 2250) * alpha * c * t ^ 9 + (1768 / 3375) * alpha * c * t ^ 11 + (5033 / 3375) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_10, v46_11, v46_20, v46_21, v46_30, v46_31, v46_40, v46_41]
  try simp only [phase43_00, phase43_01, phase43_10, phase43_11, phase43_20, phase43_21, phase43_30, phase43_31, phase43_40, phase43_41]
  try simp only [star_one, star_neg]
  linear_combination ((-351169 / 3000) * t ^ 3 + (100821997 / 3600000) * t ^ 5 + (104037571 / 1800000) * t ^ 7 + (32877611 / 7200000) * t ^ 9 + (-9499649 / 5400000) * t ^ 11 + (-1957391 / 21600000) * t ^ 17 + (-348257 / 3000) * c * t ^ 3 + (299356999 / 10800000) * c * t ^ 5 + (101673539 / 1800000) * c * t ^ 7 + (39076139 / 7200000) * c * t ^ 9 + (-3306667 / 1800000) * c * t ^ 11 + (-6021677 / 64800000) * c * t ^ 17 + (364 / 375) * c ^ 2 * t ^ 3 + (-24289 / 84375) * c ^ 2 * t ^ 5 + (-32359 / 84375) * c ^ 2 * t ^ 7 + (-5816 / 84375) * c ^ 2 * t ^ 9 + (-6568 / 84375) * c ^ 2 * t ^ 11 + (-584 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((-304 / 5625) * t ^ 5 + (-3632 / 5625) * t ^ 7 + (2336 / 5625) * t ^ 9 + (64 / 225) * t ^ 11 + (1456 / 375) * alpha * t ^ 3 + (-21716 / 9375) * alpha * t ^ 5 + (13232 / 28125) * alpha * t ^ 7 + (-824 / 9375) * alpha * t ^ 9 + (-63908 / 84375) * alpha * t ^ 11 + (2336 / 253125) * alpha * t ^ 17) * c_sq
theorem v47_42 (t : ℂ) : (momentPoly 47 z47 4 2).eval t = ((-1511596 / 3) * t ^ 2 + (33898741 / 40) * t ^ 4 + (-157480856611 / 480000) * t ^ 6 + (-3802409449 / 160000) * t ^ 8 + (-167470719 / 64000) * t ^ 10 + (11655313159 / 2880000) * t ^ 12 + (-159116833 / 240000) * t ^ 14 + (-482168719 / 2880000) * t ^ 18 + (13750851 / 320000) * t ^ 20 + (-20096 / 3) * c * t ^ 2 + (58552 / 5) * c * t ^ 4 + (-81017 / 12) * c * t ^ 6 + (807861 / 800) * c * t ^ 8 + (20468741 / 18000) * c * t ^ 10 + (-38124911 / 72000) * c * t ^ 12 + (-257326 / 3375) * c * t ^ 14 + (-556739 / 54000) * c * t ^ 18 + (31597 / 72000) * c * t ^ 20 + 259364 * alpha * t ^ 2 + (-15528581 / 40) * alpha * t ^ 4 + (164581004569 / 1440000) * alpha * t ^ 6 + (29062472993 / 1440000) * alpha * t ^ 8 + (2246912263 / 576000) * alpha * t ^ 10 + (-12256214021 / 8640000) * alpha * t ^ 12 + (-299579533 / 720000) * alpha * t ^ 14 + (-19469337 / 320000) * alpha * t ^ 18 + (-219172801 / 8640000) * alpha * t ^ 20 + (-20096 / 9) * alpha * c * t ^ 2 + (63352 / 15) * alpha * c * t ^ 4 + (-4540847 / 1500) * alpha * c * t ^ 6 + (3920291 / 4000) * alpha * c * t ^ 8 + (1851437 / 6000) * alpha * c * t ^ 10 + (-15201443 / 43200) * alpha * c * t ^ 12 + (110159 / 3375) * alpha * c * t ^ 14 + (-102209 / 54000) * alpha * c * t ^ 18 + (-64403 / 216000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_10, v46_11, v46_12, v46_20, v46_21, v46_22, v46_30, v46_31, v46_32, v46_40, v46_41, v46_42]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_10, phase43_11, phase43_12, phase43_20, phase43_21, phase43_22, phase43_30, phase43_31, phase43_32, phase43_40, phase43_41, phase43_42]
  try simp only [star_one, star_neg]
  linear_combination ((10048 / 45) * t ^ 2 + (-45083 / 125) * t ^ 4 + (137122597 / 450000) * t ^ 6 + (268196471 / 2000000) * t ^ 8 + (-2086754293 / 9000000) * t ^ 10 + (-1655293729 / 108000000) * t ^ 12 + (203487989 / 9000000) * t ^ 14 + (5972063 / 1687500) * t ^ 18 + (38100701 / 36000000) * t ^ 20 + (20096 / 45) * c * t ^ 2 + (-79493 / 125) * c * t ^ 4 + (79367687 / 270000) * c * t ^ 6 + (-155794289 / 5400000) * c * t ^ 8 + (-49780487 / 675000) * c * t ^ 10 + (230692211 / 10800000) * c * t ^ 12 + (4177793 / 1012500) * c * t ^ 14 + (3130387 / 4050000) * c * t ^ 18 + (35603 / 2160000) * c * t ^ 20 + (10048 / 45) * c ^ 2 * t ^ 2 + (-6882 / 25) * c ^ 2 * t ^ 4 + (-3632339 / 337500) * c ^ 2 * t ^ 6 + (162902059 / 2531250) * c ^ 2 * t ^ 8 + (626129 / 187500) * c ^ 2 * t ^ 10 + (502228 / 1265625) * c ^ 2 * t ^ 12 + (-7531 / 1265625) * c ^ 2 * t ^ 14 + (100076 / 1265625) * c ^ 2 * t ^ 18 + (-1168 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-20096 / 45) * t ^ 2 + (41768 / 125) * t ^ 4 + (84222391 / 225000) * t ^ 6 + (-455287529 / 1687500) * t ^ 8 + (-24984127 / 2250000) * t ^ 10 + (5837629 / 1687500) * t ^ 12 + (-240112 / 421875) * t ^ 14 + (-1226693 / 6750000) * t ^ 18 + (-2336 / 1265625) * t ^ 20 + (20096 / 45) * alpha * t ^ 2 + (-88488 / 125) * alpha * t ^ 4 + (204542491 / 675000) * alpha * t ^ 6 + (-46216151 / 1687500) * alpha * t ^ 8 + (41594941 / 6750000) * alpha * t ^ 10 + (-17035447 / 5062500) * alpha * t ^ 12 + (-842224 / 1265625) * alpha * t ^ 14 + (-2762161 / 20250000) * alpha * t ^ 18 + (2336 / 1265625) * alpha * t ^ 20) * c_sq
theorem v47_43 (t : ℂ) : (momentPoly 47 z47 4 3).eval t = ((2336525 / 2) * t + (-3056640) * t ^ 3 + (14172671 / 5) * t ^ 5 + (-79883156711 / 80000) * t ^ 7 + (138494933917 / 960000) * t ^ 9 + (-11418211697 / 60000) * t ^ 11 + (206724964753 / 1920000) * t ^ 13 + (-34792229 / 48000) * t ^ 15 + (-7782807869 / 5760000) * t ^ 17 + (567215041 / 1080000) * t ^ 19 + (407211881 / 5760000) * t ^ 21 + (762098777 / 17280000) * t ^ 25 + (-2336525 / 6) * c * t + (4948992 / 5) * c * t ^ 3 + (-1935825133 / 2000) * c * t ^ 5 + (376284456691 / 800000) * c * t ^ 7 + (-260595973883 / 2400000) * c * t ^ 9 + (3591879777 / 1600000) * c * t ^ 11 + (4009684507 / 2880000) * c * t ^ 13 + (-666715853 / 1200000) * c * t ^ 15 + (29705267 / 400000) * c * t ^ 17 + (-48699241 / 43200000) * c * t ^ 19 + (-18045373 / 14400000) * c * t ^ 21 + (37319257 / 10800000) * c * t ^ 25 + (-2336525 / 6) * alpha * t + (3898368 / 5) * alpha * t ^ 3 + (-48099788 / 125) * alpha * t ^ 5 + (-232166654549 / 1200000) * alpha * t ^ 7 + (1147673959621 / 4800000) * alpha * t ^ 9 + (-220373791 / 50000) * alpha * t ^ 11 + (-19876762879 / 384000) * alpha * t ^ 13 + (2790230383 / 1200000) * alpha * t ^ 15 + (7051871657 / 9600000) * alpha * t ^ 17 + (-3777236353 / 5400000) * alpha * t ^ 19 + (2670244721 / 28800000) * alpha * t ^ 21 + (2741453569 / 86400000) * alpha * t ^ 25 + (-2336525 / 6) * alpha * c * t + 750592 * alpha * c * t ^ 3 + (-2107887527 / 6000) * alpha * c * t ^ 5 + (-333298679813 / 7200000) * alpha * c * t ^ 7 + (64086225301 / 2400000) * alpha * c * t ^ 9 + (79746386809 / 14400000) * alpha * c * t ^ 11 + (3609169867 / 2880000) * alpha * c * t ^ 13 + (1343605993 / 3600000) * alpha * c * t ^ 15 + (57784417 / 10800000) * alpha * c * t ^ 17 + (-9726609899 / 129600000) * alpha * c * t ^ 19 + (1434549593 / 43200000) * alpha * c * t ^ 21 + (9265163 / 32400000) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_03, v46_10, v46_11, v46_12, v46_13, v46_20, v46_21, v46_22, v46_23, v46_30, v46_31, v46_32, v46_33, v46_40, v46_41, v46_42, v46_43]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_10, phase43_11, phase43_12, phase43_13, phase43_20, phase43_21, phase43_22, phase43_23, phase43_30, phase43_31, phase43_32, phase43_33, phase43_40, phase43_41, phase43_42, phase43_43]
  try simp only [star_one, star_neg]
  linear_combination ((1975808 / 125) * t ^ 3 + (-583965671 / 30000) * t ^ 5 + (-1494913933 / 4800000) * t ^ 7 + (-24311858797 / 24000000) * t ^ 9 + (656809288079 / 144000000) * t ^ 11 + (2739814832263 / 2160000000) * t ^ 13 + (-176435545901 / 180000000) * t ^ 15 + (31299227459 / 270000000) * t ^ 17 + (-11241989953 / 6480000000) * t ^ 19 + (-16136468693 / 2160000000) * t ^ 21 + (-1710870629 / 810000000) * t ^ 25 + (1959424 / 125) * c * t ^ 3 + (-1731925157 / 90000) * c * t ^ 5 + (-395005416617 / 216000000) * c * t ^ 7 + (413520122249 / 72000000) * c * t ^ 9 + (2265188007 / 16000000) * c * t ^ 11 + (-226843912921 / 2160000000) * c * t ^ 13 + (-4641424979 / 540000000) * c * t ^ 15 + (-83761187 / 67500000) * c * t ^ 17 + (-8258539243 / 2160000000) * c * t ^ 19 + (-11056971349 / 2160000000) * c * t ^ 21 + (-2853643 / 75937500) * c * t ^ 25 + (-16384 / 125) * c ^ 2 * t ^ 3 + (1248241 / 5625) * c ^ 2 * t ^ 5 + (-928416211 / 6750000) * c ^ 2 * t ^ 7 + (297433943 / 6750000) * c ^ 2 * t ^ 9 + (127977913 / 4500000) * c ^ 2 * t ^ 11 + (-421705519 / 13500000) * c ^ 2 * t ^ 13 + (1924417 / 843750) * c ^ 2 * t ^ 15 + (3388 / 1265625) * c ^ 2 * t ^ 17 + (-4856639 / 40500000) * c ^ 2 * t ^ 19 + (-107603 / 2700000) * c ^ 2 * t ^ 21) * alpha_sq + ((98304 / 125) * t ^ 3 + (-888646 / 625) * t ^ 5 + (948873923 / 1125000) * t ^ 7 + (-13031851 / 112500) * t ^ 9 + (-502164143 / 2250000) * t ^ 11 + (2695612129 / 16875000) * t ^ 13 + (-35922031 / 2812500) * t ^ 15 + (-765178 / 2109375) * t ^ 17 + (11582473 / 11250000) * t ^ 19 + (271387 / 5625000) * t ^ 21 + (82928 / 6328125) * t ^ 25 + (-32768 / 125) * alpha * t ^ 3 + (1133714 / 5625) * alpha * t ^ 5 + (542808253 / 3375000) * alpha * t ^ 7 + (-59432051 / 562500) * alpha * t ^ 9 + (79559717 / 2250000) * alpha * t ^ 11 + (-416776769 / 50625000) * alpha * t ^ 13 + (-221459009 / 8437500) * alpha * t ^ 15 + (-281794 / 2109375) * alpha * t ^ 17 + (-34436873 / 33750000) * alpha * t ^ 19 + (2128613 / 16875000) * alpha * t ^ 21 + (-82928 / 18984375) * alpha * t ^ 25) * c_sq
theorem v47_44 (t : ℂ) : (momentPoly 47 z47 4 4).eval t = (109816675 + (-199030832) * t ^ 2 + (5469161817 / 100) * t ^ 4 + (122226447251 / 2500) * t ^ 6 + (-240296425014757 / 48000000) * t ^ 8 + (-81914726795963 / 12000000) * t ^ 10 + (-529429711379 / 384000) * t ^ 12 + (-86848618218053 / 72000000) * t ^ 14 + (254413927136513 / 576000000) * t ^ 16 + (527483841143 / 72000000) * t ^ 18 + (1504381659313 / 432000000) * t ^ 20 + (-279873015709 / 24000000) * t ^ 22 + (257679598097 / 288000000) * t ^ 24 + (-391394583403 / 216000000) * t ^ 26 + (36271912963 / 1728000000) * t ^ 32 + (56152768 / 75) * c * t ^ 4 + (-752815304 / 375) * c * t ^ 6 + (276674299493 / 140625) * c * t ^ 8 + (-486947356723 / 562500) * c * t ^ 10 + (7644953657 / 112500) * c * t ^ 12 + (534252284107 / 3375000) * c * t ^ 14 + (-228776965789 / 3375000) * c * t ^ 16 + (-1887575381 / 1687500) * c * t ^ 18 + (216455528 / 1265625) * c * t ^ 20 + (-981148117 / 3375000) * c * t ^ 22 + (-2580739 / 1125000) * c * t ^ 24 + (-340405613 / 1687500) * c * t ^ 26 + (2939272 / 1265625) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z47, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v46_00, v46_01, v46_02, v46_03, v46_04, v46_10, v46_11, v46_12, v46_13, v46_14, v46_20, v46_21, v46_22, v46_23, v46_24, v46_30, v46_31, v46_32, v46_33, v46_34, v46_40, v46_41, v46_42, v46_43, v46_44]
  try simp only [phase43_00, phase43_01, phase43_02, phase43_03, phase43_04, phase43_10, phase43_11, phase43_12, phase43_13, phase43_14, phase43_20, phase43_21, phase43_22, phase43_23, phase43_24, phase43_30, phase43_31, phase43_32, phase43_33, phase43_34, phase43_40, phase43_41, phase43_42, phase43_43, phase43_44]
  try simp only [star_one, star_neg]
  linear_combination ((-18093712 / 225) * t ^ 2 + (22259188 / 125) * t ^ 4 + (-12649456639 / 12500) * t ^ 6 + (61295044120607 / 45000000) * t ^ 8 + (-4596903078947 / 15000000) * t ^ 10 + (-724757783389 / 5400000) * t ^ 12 + (-97985304851 / 2812500) * t ^ 14 + (5719048852061 / 540000000) * t ^ 16 + (5750288218369 / 1620000000) * t ^ 18 + (-5630298166519 / 4050000000) * t ^ 20 + (733678080577 / 1350000000) * t ^ 22 + (476846373091 / 2700000000) * t ^ 24 + (-33589787519 / 900000000) * t ^ 26 + (-374087791 / 450000000) * t ^ 32 + (-36187424 / 225) * c * t ^ 2 + (393838592 / 1125) * c * t ^ 4 + (-1975564859 / 11250) * c * t ^ 6 + (-3994405931741 / 45000000) * c * t ^ 8 + (24616711252139 / 270000000) * c * t ^ 10 + (-335532811469 / 54000000) * c * t ^ 12 + (-7260730274693 / 540000000) * c * t ^ 14 + (563398869863 / 162000000) * c * t ^ 16 + (108626500949 / 1620000000) * c * t ^ 18 + (-1664356625027 / 12150000000) * c * t ^ 20 + (252559536007 / 8100000000) * c * t ^ 22 + (567056333 / 1350000000) * c * t ^ 24 + (73673071889 / 8100000000) * c * t ^ 26 + (-142889543 / 3037500000) * c * t ^ 32 + (-18093712 / 225) * c ^ 2 * t ^ 2 + (7740236 / 45) * c ^ 2 * t ^ 4 + (-2699545766 / 28125) * c ^ 2 * t ^ 6 + (-672212596183 / 101250000) * c ^ 2 * t ^ 8 + (99048827369 / 11250000) * c ^ 2 * t ^ 10 + (22980310621 / 13500000) * c ^ 2 * t ^ 12 + (2314089689 / 8100000) * c ^ 2 * t ^ 14 + (2270346593 / 50625000) * c ^ 2 * t ^ 16 + (4556011 / 16875000) * c ^ 2 * t ^ 18 + (-5165237383 / 337500000) * c ^ 2 * t ^ 20 + (7277350361 / 1012500000) * c ^ 2 * t ^ 22 + (-4169467 / 126562500) * c ^ 2 * t ^ 24 + (10589471 / 84375000) * c ^ 2 * t ^ 26 + (-170528 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((72374848 / 225) * t ^ 2 + (-276725456 / 375) * t ^ 4 + (1620225464 / 3125) * t ^ 6 + (-777046072583 / 8437500) * t ^ 8 + (-1825725191 / 937500) * t ^ 10 + (-18952305929 / 3375000) * t ^ 12 + (-33868363799 / 16875000) * t ^ 14 + (52969049 / 168750) * t ^ 16 + (-46952053 / 6328125) * t ^ 18 + (8908127537 / 253125000) * t ^ 20 + (-428075437 / 28125000) * t ^ 22 + (-38559 / 390625) * t ^ 24 + (-65903677 / 31640625) * t ^ 26 + (682112 / 94921875) * t ^ 32) * c_sq
#print axioms v47_00
#print axioms v47_11
#print axioms v47_22
#print axioms v47_33
#print axioms v47_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v48_02 (t : ℂ) : (momentPoly 48 z48 0 2).eval t = ((-1807 / 120) * t ^ 2 + (1481 / 200) * t ^ 4 + (-4 / 15) * c * t ^ 2 + (-4 / 75) * c * t ^ 4 + (-213 / 40) * alpha * t ^ 2 + (-1397 / 600) * alpha * t ^ 4 + (4 / 45) * alpha * c * t ^ 2 + (4 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02]
  try simp only [phase48_00, phase48_01, phase48_02]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 90) * t ^ 2 + (-1 / 90) * c ^ 2 * t ^ 2) * alpha_sq + ((1 / 45) * t ^ 2 + (1 / 45) * alpha * t ^ 2) * c_sq
theorem v48_03 (t : ℂ) : (momentPoly 48 z48 0 3).eval t = ((-338 / 25) * t ^ 3 + (288 / 25) * t ^ 5 + 2 * t ^ 9 + (347 / 75) * c * t ^ 3 + (-79 / 75) * c * t ^ 5 + (284 / 1125) * c * t ^ 9 + (-193 / 60) * alpha * t ^ 3 + (-12163 / 600) * alpha * t ^ 5 + (14209 / 3000) * alpha * t ^ 9 + (-292 / 75) * alpha * c * t ^ 3 + (292 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_03]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03]
  try simp only [star_one, star_neg]
  linear_combination ((-413 / 400) * t ^ 3 + (-171 / 400) * t ^ 5 + (3749 / 3600) * c * t ^ 3 + (-71 / 1200) * c * t ^ 5 + (-2 / 225) * c ^ 2 * t ^ 3 + (-1 / 225) * c ^ 2 * t ^ 5) * alpha_sq + ((8 / 225) * alpha * t ^ 3 + (4 / 225) * alpha * t ^ 5) * c_sq
theorem v48_04 (t : ℂ) : (momentPoly 48 z48 0 4).eval t = ((2615813 / 4800) * t ^ 4 + (-547783 / 800) * t ^ 6 + (183559 / 1920) * t ^ 8 + (-2338253 / 36000) * t ^ 10 + (569897 / 80000) * t ^ 16 + (-92 / 25) * c * t ^ 4 + (8911 / 375) * c * t ^ 6 + (-242 / 125) * c * t ^ 8 + (-9511 / 1125) * c * t ^ 10 + (584 / 5625) * c * t ^ 16 + (7687847 / 24000) * alpha * t ^ 4 + (-349291 / 2400) * alpha * t ^ 6 + (-1762917 / 16000) * alpha * t ^ 8 + (28449 / 800) * alpha * t ^ 10 + (1313167 / 720000) * alpha * t ^ 16 + (-1972 / 225) * alpha * c * t ^ 4 + (299 / 25) * alpha * c * t ^ 6 + (322 / 225) * alpha * c * t ^ 8 + (-4711 / 3375) * alpha * c * t ^ 10 + (584 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_03, v47_04]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04]
  try simp only [star_one, star_neg]
  linear_combination ((-901 / 1125) * t ^ 4 + (243163 / 9000) * t ^ 6 + (16133 / 3000) * t ^ 8 + (7111 / 13500) * t ^ 10 + (19 / 125) * c * t ^ 4 + (854 / 225) * c * t ^ 6 + (-71 / 4500) * c * t ^ 8 + (-1183 / 1500) * c * t ^ 10 + (146 / 225) * c ^ 2 * t ^ 4 + (-2198 / 3375) * c ^ 2 * t ^ 6 + (-2 / 3375) * c ^ 2 * t ^ 8) * alpha_sq + ((-1429 / 2250) * t ^ 4 + (1223 / 750) * t ^ 6 + (-4 / 1125) * t ^ 8 + (284 / 3375) * t ^ 10 + (-4411 / 2250) * alpha * t ^ 4 + (2171 / 2250) * alpha * t ^ 6 + (4 / 1125) * alpha * t ^ 8 + (-284 / 3375) * alpha * t ^ 10) * c_sq
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
theorem v48_12 (t : ℂ) : (momentPoly 48 z48 1 2).eval t = (57 * t + (-15853 / 300) * t ^ 3 + (1681 / 300) * t ^ 5 + (-38 / 3) * c * t + (5537 / 450) * c * t ^ 3 + (-271 / 150) * c * t ^ 5 + 19 * alpha * t + (-12349 / 900) * alpha * t ^ 3 + (-1823 / 900) * alpha * t ^ 5 + (38 / 3) * alpha * c * t + (-4369 / 450) * alpha * c * t ^ 3 + (-71 / 90) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_10, v47_11, v47_12]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12]
  try simp only [star_one, star_neg]
  linear_combination ((413 / 1200) * t ^ 3 + (57 / 400) * t ^ 5 + (-3749 / 10800) * c * t ^ 3 + (71 / 3600) * c * t ^ 5 + (2 / 675) * c ^ 2 * t ^ 3 + (1 / 675) * c ^ 2 * t ^ 5) * alpha_sq + ((-4 / 225) * t ^ 3 + (-2 / 225) * t ^ 5 + (-4 / 675) * alpha * t ^ 3 + (-2 / 675) * alpha * t ^ 5) * c_sq
theorem v48_13 (t : ℂ) : (momentPoly 48 z48 1 3).eval t = ((-84929 / 40) * t ^ 2 + (3955261 / 1500) * t ^ 4 + (-1881823 / 3000) * t ^ 6 + (-2438 / 225) * t ^ 10 + (-188 / 5) * c * t ^ 2 + (22637 / 750) * c * t ^ 4 + (569 / 1500) * c * t ^ 6 + (2749 / 1500) * c * t ^ 10 + (-30033 / 40) * alpha * t ^ 2 + (191647 / 500) * alpha * t ^ 4 + (245739 / 1000) * alpha * t ^ 6 + (-608 / 225) * alpha * t ^ 10 + (188 / 15) * alpha * c * t ^ 2 + (-2693 / 250) * alpha * c * t ^ 4 + (4231 / 4500) * alpha * c * t ^ 6 + (-4349 / 4500) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_03, v47_10, v47_11, v47_12, v47_13]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13]
  try simp only [star_one, star_neg]
  linear_combination ((47 / 30) * t ^ 2 + (-15431 / 18000) * t ^ 4 + (3181 / 4500) * t ^ 6 + (-7111 / 54000) * t ^ 10 + (13 / 9000) * c * t ^ 4 + (-17719 / 18000) * c * t ^ 6 + (1183 / 6000) * c * t ^ 10 + (-47 / 30) * c ^ 2 * t ^ 2 + (1027 / 1200) * c ^ 2 * t ^ 4 + (111 / 400) * c ^ 2 * t ^ 6) * alpha_sq + ((47 / 15) * t ^ 2 + (-4037 / 4500) * t ^ 4 + (-5027 / 4500) * t ^ 6 + (71 / 3375) * t ^ 10 + (47 / 15) * alpha * t ^ 2 + (-9877 / 4500) * alpha * t ^ 4 + (271 / 1500) * alpha * t ^ 6 + (71 / 3375) * alpha * t ^ 10) * c_sq
theorem v48_14 (t : ℂ) : (momentPoly 48 z48 1 4).eval t = ((-62868 / 25) * t ^ 3 + (8327809 / 1875) * t ^ 5 + (-4083838 / 1875) * t ^ 7 + (994877 / 1875) * t ^ 9 + (-176688 / 625) * t ^ 11 + (6316 / 1875) * t ^ 17 + (21514 / 25) * c * t ^ 3 + (-4910609 / 5000) * c * t ^ 5 + (1654267 / 7500) * c * t ^ 7 + (-657391 / 90000) * c * t ^ 9 + (-1962931 / 67500) * c * t ^ 11 + (-35071 / 90000) * c * t ^ 17 + (-5983 / 10) * alpha * t ^ 3 + (-83009981 / 30000) * alpha * t ^ 5 + (41122781 / 15000) * alpha * t ^ 7 + (155776487 / 180000) * alpha * t ^ 9 + (-72564193 / 135000) * alpha * t ^ 11 + (-989743 / 108000) * alpha * t ^ 17 + (-18104 / 25) * alpha * c * t ^ 3 + (7370194 / 5625) * alpha * c * t ^ 5 + (-3261868 / 5625) * alpha * c * t ^ 7 + (-25858 / 5625) * alpha * c * t ^ 9 + (-7072 / 16875) * alpha * c * t ^ 11 + (-20132 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_03, v47_04, v47_10, v47_11, v47_12, v47_13, v47_14]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14]
  try simp only [star_one, star_neg]
  linear_combination ((-38409 / 200) * t ^ 3 + (40153961 / 720000) * t ^ 5 + (24829159 / 360000) * t ^ 7 + (7667311 / 1440000) * t ^ 9 + (-998383 / 360000) * t ^ 11 + (-173441 / 1440000) * t ^ 17 + (116219 / 600) * c * t ^ 3 + (-64117823 / 432000) * c * t ^ 5 + (-597563 / 72000) * c * t ^ 7 + (190807 / 864000) * c * t ^ 9 + (1732219 / 648000) * c * t ^ 11 + (-123901 / 4320000) * c * t ^ 17 + (-124 / 75) * c ^ 2 * t ^ 3 + (10969 / 16875) * c ^ 2 * t ^ 5 + (8257 / 16875) * c ^ 2 * t ^ 7 + (484 / 5625) * c ^ 2 * t ^ 9 + (5068 / 50625) * c ^ 2 * t ^ 11 + (146 / 50625) * c ^ 2 * t ^ 17) * alpha_sq + ((368 / 1125) * t ^ 5 + (616 / 1125) * t ^ 7 + (-584 / 1125) * t ^ 9 + (-16 / 45) * t ^ 11 + (496 / 75) * alpha * t ^ 3 + (-21898 / 5625) * alpha * t ^ 5 + (5671 / 5625) * alpha * t ^ 7 + (-1262 / 16875) * alpha * t ^ 9 + (-46163 / 50625) * alpha * t ^ 11 + (584 / 50625) * alpha * t ^ 17) * c_sq
theorem v48_20 (t : ℂ) : (momentPoly 48 z48 2 0).eval t = ((-1807 / 120) * t ^ 2 + (1481 / 200) * t ^ 4 + (-4 / 15) * c * t ^ 2 + (-4 / 75) * c * t ^ 4 + (213 / 40) * alpha * t ^ 2 + (1397 / 600) * alpha * t ^ 4 + (-4 / 45) * alpha * c * t ^ 2 + (-4 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_10, v47_20]
  try simp only [phase48_00, phase48_10, phase48_20]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 90) * t ^ 2 + (-1 / 90) * c ^ 2 * t ^ 2) * alpha_sq + ((1 / 45) * t ^ 2 + (-1 / 45) * alpha * t ^ 2) * c_sq
theorem v48_21 (t : ℂ) : (momentPoly 48 z48 2 1).eval t = (57 * t + (-15853 / 300) * t ^ 3 + (1681 / 300) * t ^ 5 + (-38 / 3) * c * t + (5537 / 450) * c * t ^ 3 + (-271 / 150) * c * t ^ 5 + (-19) * alpha * t + (12349 / 900) * alpha * t ^ 3 + (1823 / 900) * alpha * t ^ 5 + (-38 / 3) * alpha * c * t + (4369 / 450) * alpha * c * t ^ 3 + (71 / 90) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_10, v47_11, v47_20, v47_21]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21]
  try simp only [star_one, star_neg]
  linear_combination ((413 / 1200) * t ^ 3 + (57 / 400) * t ^ 5 + (-3749 / 10800) * c * t ^ 3 + (71 / 3600) * c * t ^ 5 + (2 / 675) * c ^ 2 * t ^ 3 + (1 / 675) * c ^ 2 * t ^ 5) * alpha_sq + ((-4 / 225) * t ^ 3 + (-2 / 225) * t ^ 5 + (4 / 675) * alpha * t ^ 3 + (2 / 675) * alpha * t ^ 5) * c_sq
theorem v48_22 (t : ℂ) : (momentPoly 48 z48 2 2).eval t = (4560 + (-89488 / 15) * t ^ 2 + (663921 / 400) * t ^ 4 + (-119437 / 9000) * t ^ 6 + (430909 / 18000) * t ^ 8 + (1168 / 225) * c * t ^ 4 + (-4672 / 1125) * c * t ^ 6 + (-1168 / 1125) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_10, v47_11, v47_12, v47_20, v47_21, v47_22]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22]
  try simp only [star_one, star_neg]
  linear_combination ((-94 / 45) * t ^ 2 + (141 / 100) * t ^ 4 + (-89537 / 9000) * t ^ 6 + (-16133 / 9000) * t ^ 8 + (-71 / 1350) * c * t ^ 4 + (71 / 1500) * c * t ^ 6 + (71 / 13500) * c * t ^ 8 + (94 / 45) * c ^ 2 * t ^ 2 + (-733 / 540) * c ^ 2 * t ^ 4 + (-6193 / 40500) * c ^ 2 * t ^ 6 + (2 / 10125) * c ^ 2 * t ^ 8) * alpha_sq + ((-376 / 45) * t ^ 2 + (1319 / 225) * t ^ 4 + (583 / 3375) * t ^ 6 + (-8 / 3375) * t ^ 8) * c_sq
theorem v48_23 (t : ℂ) : (momentPoly 48 z48 2 3).eval t = ((40188 / 5) * t + (-1474329 / 100) * t ^ 3 + (93715531 / 12000) * t ^ 5 + (-117053213 / 120000) * t ^ 7 + (7362469 / 40000) * t ^ 9 + (-47495149 / 360000) * t ^ 11 + (-7870403 / 360000) * t ^ 13 + (-26792 / 15) * c * t + (171647 / 50) * c * t ^ 3 + (-6314999 / 3000) * c * t ^ 5 + (9735583 / 22500) * c * t ^ 7 + (-561169 / 45000) * c * t ^ 9 + (1828 / 3375) * c * t ^ 11 + (12086 / 5625) * c * t ^ 13 + (13396 / 5) * alpha * t + (-382819 / 100) * alpha * t ^ 3 + (23642939 / 36000) * alpha * t ^ 5 + (272010227 / 360000) * alpha * t ^ 7 + (-67446913 / 360000) * alpha * t ^ 9 + (-13305977 / 216000) * alpha * t ^ 11 + (41615533 / 1080000) * alpha * t ^ 13 + (26792 / 15) * alpha * c * t + (-135439 / 50) * alpha * c * t ^ 3 + (6799013 / 9000) * alpha * c * t ^ 5 + (475033 / 2500) * alpha * c * t ^ 7 + (486929 / 45000) * alpha * c * t ^ 9 + (8332 / 5625) * alpha * c * t ^ 11 + (2806 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_03, v47_10, v47_11, v47_12, v47_13, v47_20, v47_21, v47_22, v47_23]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23]
  try simp only [star_one, star_neg]
  linear_combination ((38409 / 400) * t ^ 3 + (-729733 / 18000) * t ^ 5 + (-676603 / 22500) * t ^ 7 + (-564071 / 45000) * t ^ 9 + (-15149 / 10000) * t ^ 11 + (12233 / 6000) * t ^ 13 + (-116219 / 1200) * c * t ^ 3 + (522073 / 6000) * c * t ^ 5 + (-1571873 / 270000) * c * t ^ 7 + (154147 / 270000) * c * t ^ 9 + (-167633 / 405000) * c * t ^ 11 + (1183 / 45000) * c * t ^ 13 + (62 / 75) * c ^ 2 * t ^ 3 + (-12709 / 27000) * c ^ 2 * t ^ 5 + (-1451 / 54000) * c ^ 2 * t ^ 7 + (169 / 27000) * c ^ 2 * t ^ 9 + (-4429 / 54000) * c ^ 2 * t ^ 11) * alpha_sq + ((-124 / 25) * t ^ 3 + (2849 / 900) * t ^ 5 + (1173 / 5000) * t ^ 7 + (-164 / 625) * t ^ 9 + (56707 / 135000) * t ^ 11 + (142 / 16875) * t ^ 13 + (-124 / 75) * alpha * t ^ 3 + (3301 / 13500) * alpha * t ^ 5 + (81277 / 135000) * alpha * t ^ 7 + (4364 / 16875) * alpha * t ^ 9 + (32707 / 405000) * alpha * t ^ 11 + (142 / 50625) * alpha * t ^ 13) * c_sq
theorem v48_24 (t : ℂ) : (momentPoly 48 z48 2 4).eval t = ((-4739761 / 12) * t ^ 2 + (2341190701 / 3000) * t ^ 4 + (-619374971777 / 1440000) * t ^ 6 + (278189469599 / 7200000) * t ^ 8 + (22153436969 / 14400000) * t ^ 10 + (45115005919 / 14400000) * t ^ 12 + (-5855914681 / 10800000) * t ^ 14 + (-5133608761 / 43200000) * t ^ 18 + (1373200297 / 43200000) * t ^ 20 + (-20984 / 3) * c * t ^ 2 + (4678268 / 375) * c * t ^ 4 + (-95849723 / 15000) * c * t ^ 6 + (41573237 / 75000) * c * t ^ 8 + (373579261 / 450000) * c * t ^ 10 + (-224657359 / 450000) * c * t ^ 12 + (-4535731 / 84375) * c * t ^ 14 + (-9713081 / 1350000) * c * t ^ 18 + (26797 / 90000) * c * t ^ 20 + (-558699 / 4) * alpha * t ^ 2 + (200780927 / 1000) * alpha * t ^ 4 + (-14049045179 / 480000) * alpha * t ^ 6 + (-233827496977 / 7200000) * alpha * t ^ 8 + (-10850565709 / 4800000) * alpha * t ^ 10 + (27503509069 / 43200000) * alpha * t ^ 12 + (698774941 / 3600000) * alpha * t ^ 14 + (56527967 / 4800000) * alpha * t ^ 18 + (1365153049 / 43200000) * alpha * t ^ 20 + (20984 / 9) * alpha * c * t ^ 2 + (-1657556 / 375) * alpha * c * t ^ 4 + (377916017 / 135000) * alpha * c * t ^ 6 + (-498976703 / 675000) * alpha * c * t ^ 8 + (-12059399 / 50000) * alpha * c * t ^ 10 + (437405327 / 1350000) * alpha * c * t ^ 12 + (-6898217 / 253125) * alpha * c * t ^ 14 + (3422393 / 4050000) * alpha * c * t ^ 18 + (69203 / 270000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_03, v47_04, v47_10, v47_11, v47_12, v47_13, v47_14, v47_20, v47_21, v47_22, v47_23, v47_24]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24]
  try simp only [star_one, star_neg]
  linear_combination ((2623 / 9) * t ^ 2 + (-354913 / 1125) * t ^ 4 + (134126189 / 540000) * t ^ 6 + (1016828507 / 3600000) * t ^ 8 + (-201362527 / 675000) * t ^ 10 + (-887964349 / 21600000) * t ^ 12 + (163916147 / 5400000) * t ^ 14 + (29230703 / 5400000) * t ^ 18 + (32266091 / 21600000) * t ^ 20 + (598 / 1125) * c * t ^ 4 + (-10180253 / 36000) * c * t ^ 6 + (841589717 / 5400000) * c * t ^ 8 + (630585961 / 5400000) * c * t ^ 10 + (-70697321 / 3600000) * c * t ^ 12 + (-793409 / 112500) * c * t ^ 14 + (-4447427 / 5400000) * c * t ^ 18 + (2797 / 2160000) * c * t ^ 20 + (-2623 / 9) * c ^ 2 * t ^ 2 + (23621 / 75) * c ^ 2 * t ^ 4 + (9288803 / 270000) * c ^ 2 * t ^ 6 + (-141070741 / 2025000) * c ^ 2 * t ^ 8 + (-4199657 / 1350000) * c ^ 2 * t ^ 10 + (-577409 / 1012500) * c ^ 2 * t ^ 12 + (-42571 / 3037500) * c ^ 2 * t ^ 14 + (-74911 / 759375) * c ^ 2 * t ^ 18 + (292 / 759375) * c ^ 2 * t ^ 20) * alpha_sq + ((5246 / 9) * t ^ 2 + (-371404 / 1125) * t ^ 4 + (-275151397 / 540000) * t ^ 6 + (398365241 / 1350000) * t ^ 8 + (57584797 / 5400000) * t ^ 10 + (-171871 / 50000) * t ^ 12 + (203152 / 253125) * t ^ 14 + (4039567 / 16200000) * t ^ 18 + (584 / 253125) * t ^ 20 + (5246 / 9) * alpha * t ^ 2 + (-908684 / 1125) * alpha * t ^ 4 + (57850121 / 180000) * alpha * t ^ 6 + (-71887879 / 1350000) * alpha * t ^ 8 + (13370719 / 1800000) * alpha * t ^ 10 + (-13252111 / 4050000) * alpha * t ^ 12 + (-6944 / 9375) * alpha * t ^ 14 + (-800891 / 5400000) * alpha * t ^ 18 + (584 / 253125) * alpha * t ^ 20) * c_sq
theorem v48_30 (t : ℂ) : (momentPoly 48 z48 3 0).eval t = ((-338 / 25) * t ^ 3 + (288 / 25) * t ^ 5 + 2 * t ^ 9 + (347 / 75) * c * t ^ 3 + (-79 / 75) * c * t ^ 5 + (284 / 1125) * c * t ^ 9 + (193 / 60) * alpha * t ^ 3 + (12163 / 600) * alpha * t ^ 5 + (-14209 / 3000) * alpha * t ^ 9 + (292 / 75) * alpha * c * t ^ 3 + (-292 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_10, v47_20, v47_30]
  try simp only [phase48_00, phase48_10, phase48_20, phase48_30]
  try simp only [star_one, star_neg]
  linear_combination ((-413 / 400) * t ^ 3 + (-171 / 400) * t ^ 5 + (3749 / 3600) * c * t ^ 3 + (-71 / 1200) * c * t ^ 5 + (-2 / 225) * c ^ 2 * t ^ 3 + (-1 / 225) * c ^ 2 * t ^ 5) * alpha_sq + ((-8 / 225) * alpha * t ^ 3 + (-4 / 225) * alpha * t ^ 5) * c_sq
theorem v48_31 (t : ℂ) : (momentPoly 48 z48 3 1).eval t = ((-84929 / 40) * t ^ 2 + (3955261 / 1500) * t ^ 4 + (-1881823 / 3000) * t ^ 6 + (-2438 / 225) * t ^ 10 + (-188 / 5) * c * t ^ 2 + (22637 / 750) * c * t ^ 4 + (569 / 1500) * c * t ^ 6 + (2749 / 1500) * c * t ^ 10 + (30033 / 40) * alpha * t ^ 2 + (-191647 / 500) * alpha * t ^ 4 + (-245739 / 1000) * alpha * t ^ 6 + (608 / 225) * alpha * t ^ 10 + (-188 / 15) * alpha * c * t ^ 2 + (2693 / 250) * alpha * c * t ^ 4 + (-4231 / 4500) * alpha * c * t ^ 6 + (4349 / 4500) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_10, v47_11, v47_20, v47_21, v47_30, v47_31]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21, phase48_30, phase48_31]
  try simp only [star_one, star_neg]
  linear_combination ((47 / 30) * t ^ 2 + (-15431 / 18000) * t ^ 4 + (3181 / 4500) * t ^ 6 + (-7111 / 54000) * t ^ 10 + (13 / 9000) * c * t ^ 4 + (-17719 / 18000) * c * t ^ 6 + (1183 / 6000) * c * t ^ 10 + (-47 / 30) * c ^ 2 * t ^ 2 + (1027 / 1200) * c ^ 2 * t ^ 4 + (111 / 400) * c ^ 2 * t ^ 6) * alpha_sq + ((47 / 15) * t ^ 2 + (-4037 / 4500) * t ^ 4 + (-5027 / 4500) * t ^ 6 + (71 / 3375) * t ^ 10 + (-47 / 15) * alpha * t ^ 2 + (9877 / 4500) * alpha * t ^ 4 + (-271 / 1500) * alpha * t ^ 6 + (-71 / 3375) * alpha * t ^ 10) * c_sq
theorem v48_32 (t : ℂ) : (momentPoly 48 z48 3 2).eval t = ((40188 / 5) * t + (-1474329 / 100) * t ^ 3 + (93715531 / 12000) * t ^ 5 + (-117053213 / 120000) * t ^ 7 + (7362469 / 40000) * t ^ 9 + (-47495149 / 360000) * t ^ 11 + (-7870403 / 360000) * t ^ 13 + (-26792 / 15) * c * t + (171647 / 50) * c * t ^ 3 + (-6314999 / 3000) * c * t ^ 5 + (9735583 / 22500) * c * t ^ 7 + (-561169 / 45000) * c * t ^ 9 + (1828 / 3375) * c * t ^ 11 + (12086 / 5625) * c * t ^ 13 + (-13396 / 5) * alpha * t + (382819 / 100) * alpha * t ^ 3 + (-23642939 / 36000) * alpha * t ^ 5 + (-272010227 / 360000) * alpha * t ^ 7 + (67446913 / 360000) * alpha * t ^ 9 + (13305977 / 216000) * alpha * t ^ 11 + (-41615533 / 1080000) * alpha * t ^ 13 + (-26792 / 15) * alpha * c * t + (135439 / 50) * alpha * c * t ^ 3 + (-6799013 / 9000) * alpha * c * t ^ 5 + (-475033 / 2500) * alpha * c * t ^ 7 + (-486929 / 45000) * alpha * c * t ^ 9 + (-8332 / 5625) * alpha * c * t ^ 11 + (-2806 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_10, v47_11, v47_12, v47_20, v47_21, v47_22, v47_30, v47_31, v47_32]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22, phase48_30, phase48_31, phase48_32]
  try simp only [star_one, star_neg]
  linear_combination ((38409 / 400) * t ^ 3 + (-729733 / 18000) * t ^ 5 + (-676603 / 22500) * t ^ 7 + (-564071 / 45000) * t ^ 9 + (-15149 / 10000) * t ^ 11 + (12233 / 6000) * t ^ 13 + (-116219 / 1200) * c * t ^ 3 + (522073 / 6000) * c * t ^ 5 + (-1571873 / 270000) * c * t ^ 7 + (154147 / 270000) * c * t ^ 9 + (-167633 / 405000) * c * t ^ 11 + (1183 / 45000) * c * t ^ 13 + (62 / 75) * c ^ 2 * t ^ 3 + (-12709 / 27000) * c ^ 2 * t ^ 5 + (-1451 / 54000) * c ^ 2 * t ^ 7 + (169 / 27000) * c ^ 2 * t ^ 9 + (-4429 / 54000) * c ^ 2 * t ^ 11) * alpha_sq + ((-124 / 25) * t ^ 3 + (2849 / 900) * t ^ 5 + (1173 / 5000) * t ^ 7 + (-164 / 625) * t ^ 9 + (56707 / 135000) * t ^ 11 + (142 / 16875) * t ^ 13 + (124 / 75) * alpha * t ^ 3 + (-3301 / 13500) * alpha * t ^ 5 + (-81277 / 135000) * alpha * t ^ 7 + (-4364 / 16875) * alpha * t ^ 9 + (-32707 / 405000) * alpha * t ^ 11 + (-142 / 50625) * alpha * t ^ 13) * c_sq
theorem v48_33 (t : ℂ) : (momentPoly 48 z48 3 3).eval t = (643008 + (-1248548) * t ^ 2 + (137431647 / 200) * t ^ 4 + (-2640794209 / 30000) * t ^ 6 + (474857731 / 30000) * t ^ 8 + (-39721353 / 8000) * t ^ 10 + (185806159 / 450000) * t ^ 12 + (-541169797 / 900000) * t ^ 14 + (202209589 / 5400000) * t ^ 18 + (53728 / 25) * c * t ^ 4 + (-2398374 / 625) * c * t ^ 6 + (210739 / 125) * c * t ^ 8 + (-57403 / 1875) * c * t ^ 10 + (-486571 / 5625) * c * t ^ 12 + (222137 / 1875) * c * t ^ 14 + (1136 / 1125) * c * t ^ 18) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_03, v47_10, v47_11, v47_12, v47_13, v47_20, v47_21, v47_22, v47_23, v47_30, v47_31, v47_32, v47_33]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23, phase48_30, phase48_31, phase48_32, phase48_33]
  try simp only [star_one, star_neg]
  linear_combination ((-2623 / 6) * t ^ 2 + (29187 / 50) * t ^ 4 + (-43139147 / 10000) * t ^ 6 + (106852037 / 40000) * t ^ 8 + (13513049 / 24000) * t ^ 10 + (76900141 / 5400000) * t ^ 12 + (-215404229 / 5400000) * t ^ 14 + (1962259 / 1012500) * t ^ 18 + (-1633 / 75) * c * t ^ 4 + (3820813 / 180000) * c * t ^ 6 + (20381783 / 360000) * c * t ^ 8 + (-15489433 / 360000) * c * t ^ 10 + (-30923 / 1600) * c * t ^ 12 + (754033 / 120000) * c * t ^ 14 + (2623 / 6) * c ^ 2 * t ^ 2 + (-16859 / 30) * c ^ 2 * t ^ 4 + (54061199 / 540000) * c ^ 2 * t ^ 6 + (11900129 / 270000) * c ^ 2 * t ^ 8 + (587933 / 180000) * c ^ 2 * t ^ 10 + (109903 / 135000) * c ^ 2 * t ^ 12 + (-3317 / 135000) * c ^ 2 * t ^ 14) * alpha_sq + ((-5246 / 3) * t ^ 2 + (60674 / 25) * t ^ 4 + (-1302317 / 1800) * t ^ 6 + (-760979 / 22500) * t ^ 8 + (-67357 / 5000) * t ^ 10 + (-333848 / 84375) * t ^ 12 + (94372 / 84375) * t ^ 14 + (-10082 / 253125) * t ^ 18) * c_sq
theorem v48_34 (t : ℂ) : (momentPoly 48 z48 3 4).eval t = ((7476669 / 5) * t + (-203504961 / 50) * t ^ 3 + (7684284941 / 2000) * t ^ 5 + (-220738717133 / 160000) * t ^ 7 + (183839838811 / 960000) * t ^ 9 + (-231823015881 / 1600000) * t ^ 11 + (9123493741813 / 144000000) * t ^ 13 + (27293109647 / 4500000) * t ^ 15 + (-24263868629 / 16000000) * t ^ 17 + (7560911897 / 43200000) * t ^ 19 + (12295105763 / 144000000) * t ^ 21 + (19604542393 / 432000000) * t ^ 25 + (-1661482 / 5) * c * t + (23692823 / 25) * c * t ^ 3 + (-506646619 / 500) * c * t ^ 5 + (891688986863 / 1800000) * c * t ^ 7 + (-180875717489 / 1800000) * c * t ^ 9 + (330328717 / 144000) * c * t ^ 11 + (8386735949 / 10800000) * c * t ^ 13 + (-631349639 / 900000) * c * t ^ 15 + (138880621 / 2700000) * c * t ^ 17 + (-4596350587 / 162000000) * c * t ^ 19 + (640675381 / 54000000) * c * t ^ 21 + (35519257 / 13500000) * c * t ^ 25 + (2492223 / 5) * alpha * t + (-52841371 / 50) * alpha * t ^ 3 + (1022205663 / 2000) * alpha * t ^ 5 + (2010813875293 / 7200000) * alpha * t ^ 7 + (-4102578407033 / 14400000) * alpha * t ^ 9 + (45288502529 / 2880000) * alpha * t ^ 11 + (4043172862129 / 86400000) * alpha * t ^ 13 + (-1534461299 / 180000) * alpha * t ^ 15 + (-50182739417 / 86400000) * alpha * t ^ 17 + (270305766877 / 648000000) * alpha * t ^ 19 + (-18113785117 / 432000000) * alpha * t ^ 21 + (-36745616903 / 1296000000) * alpha * t ^ 25 + (1661482 / 5) * alpha * c * t + (-18694951 / 25) * alpha * c * t ^ 3 + (235937211 / 500) * alpha * c * t ^ 5 + (-3051306599 / 200000) * alpha * c * t ^ 7 + (-61397334143 / 1800000) * alpha * c * t ^ 9 + (-21054548629 / 3600000) * alpha * c * t ^ 11 + (-7476953243 / 18000000) * alpha * c * t ^ 13 + (-2490891143 / 13500000) * alpha * c * t ^ 15 + (-49724171 / 4500000) * alpha * c * t ^ 17 + (2812935353 / 54000000) * alpha * c * t ^ 19 + (-1365387461 / 54000000) * alpha * c * t ^ 21 + (-3865163 / 40500000) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_03, v47_04, v47_10, v47_11, v47_12, v47_13, v47_14, v47_20, v47_21, v47_22, v47_23, v47_24, v47_30, v47_31, v47_32, v47_33, v47_34]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24, phase48_30, phase48_31, phase48_32, phase48_33, phase48_34]
  try simp only [star_one, star_neg]
  linear_combination ((5301681 / 200) * t ^ 3 + (-197190341 / 6000) * t ^ 5 + (6045484723 / 4800000) * t ^ 7 + (966158611 / 4800000) * t ^ 9 + (122453796467 / 28800000) * t ^ 11 + (200641914773 / 144000000) * t ^ 13 + (-81103444327 / 108000000) * t ^ 15 + (5457396319 / 54000000) * t ^ 17 + (364907569 / 432000000) * t ^ 19 + (-1356241199 / 144000000) * t ^ 21 + (-4182659 / 2160000) * t ^ 25 + (-16041971 / 600) * c * t ^ 3 + (276141713 / 6000) * c * t ^ 5 + (-917237739467 / 43200000) * c * t ^ 7 + (74689761317 / 43200000) * c * t ^ 9 + (-46353384553 / 86400000) * c * t ^ 11 + (164709075347 / 1296000000) * c * t ^ 13 + (5767697243 / 108000000) * c * t ^ 15 + (62229233 / 40500000) * c * t ^ 17 + (25958952583 / 3888000000) * c * t ^ 19 + (-2863530697 / 1296000000) * c * t ^ 21 + (86359 / 1687500) * c * t ^ 25 + (17116 / 75) * c ^ 2 * t ^ 3 + (-552833 / 1500) * c ^ 2 * t ^ 5 + (14644289 / 67500) * c ^ 2 * t ^ 7 + (-348462929 / 5400000) * c ^ 2 * t ^ 9 + (-90311849 / 2700000) * c ^ 2 * t ^ 11 + (76487063 / 2160000) * c ^ 2 * t ^ 13 + (-355771 / 112500) * c ^ 2 * t ^ 15 + (278 / 253125) * c ^ 2 * t ^ 17 + (1192079 / 8100000) * c ^ 2 * t ^ 19 + (112403 / 2160000) * c ^ 2 * t ^ 21) * alpha_sq + ((-34232 / 25) * t ^ 3 + (23977 / 10) * t ^ 5 + (-8131928 / 5625) * t ^ 7 + (30285821 / 112500) * t ^ 9 + (57135697 / 225000) * t ^ 11 + (-2441262431 / 13500000) * t ^ 13 + (127367281 / 6750000) * t ^ 15 + (113119 / 281250) * t ^ 17 + (-29462953 / 20250000) * t ^ 19 + (-1155473 / 13500000) * t ^ 21 + (-20732 / 1265625) * t ^ 25 + (-34232 / 75) * alpha * t ^ 3 + (267457 / 750) * alpha * t ^ 5 + (3845942 / 16875) * alpha * t ^ 7 + (-55369279 / 337500) * alpha * t ^ 9 + (39158713 / 675000) * alpha * t ^ 11 + (-324576191 / 40500000) * alpha * t ^ 13 + (-213691573 / 6750000) * alpha * t ^ 15 + (-465923 / 2531250) * alpha * t ^ 17 + (-85717033 / 60750000) * alpha * t ^ 19 + (6044527 / 40500000) * alpha * t ^ 21 + (-20732 / 3796875) * alpha * t ^ 25) * c_sq
theorem v48_40 (t : ℂ) : (momentPoly 48 z48 4 0).eval t = ((2615813 / 4800) * t ^ 4 + (-547783 / 800) * t ^ 6 + (183559 / 1920) * t ^ 8 + (-2338253 / 36000) * t ^ 10 + (569897 / 80000) * t ^ 16 + (-92 / 25) * c * t ^ 4 + (8911 / 375) * c * t ^ 6 + (-242 / 125) * c * t ^ 8 + (-9511 / 1125) * c * t ^ 10 + (584 / 5625) * c * t ^ 16 + (-7687847 / 24000) * alpha * t ^ 4 + (349291 / 2400) * alpha * t ^ 6 + (1762917 / 16000) * alpha * t ^ 8 + (-28449 / 800) * alpha * t ^ 10 + (-1313167 / 720000) * alpha * t ^ 16 + (1972 / 225) * alpha * c * t ^ 4 + (-299 / 25) * alpha * c * t ^ 6 + (-322 / 225) * alpha * c * t ^ 8 + (4711 / 3375) * alpha * c * t ^ 10 + (-584 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_10, v47_20, v47_30, v47_40]
  try simp only [phase48_00, phase48_10, phase48_20, phase48_30, phase48_40]
  try simp only [star_one, star_neg]
  linear_combination ((-901 / 1125) * t ^ 4 + (243163 / 9000) * t ^ 6 + (16133 / 3000) * t ^ 8 + (7111 / 13500) * t ^ 10 + (19 / 125) * c * t ^ 4 + (854 / 225) * c * t ^ 6 + (-71 / 4500) * c * t ^ 8 + (-1183 / 1500) * c * t ^ 10 + (146 / 225) * c ^ 2 * t ^ 4 + (-2198 / 3375) * c ^ 2 * t ^ 6 + (-2 / 3375) * c ^ 2 * t ^ 8) * alpha_sq + ((-1429 / 2250) * t ^ 4 + (1223 / 750) * t ^ 6 + (-4 / 1125) * t ^ 8 + (284 / 3375) * t ^ 10 + (4411 / 2250) * alpha * t ^ 4 + (-2171 / 2250) * alpha * t ^ 6 + (-4 / 1125) * alpha * t ^ 8 + (284 / 3375) * alpha * t ^ 10) * c_sq
theorem v48_41 (t : ℂ) : (momentPoly 48 z48 4 1).eval t = ((-62868 / 25) * t ^ 3 + (8327809 / 1875) * t ^ 5 + (-4083838 / 1875) * t ^ 7 + (994877 / 1875) * t ^ 9 + (-176688 / 625) * t ^ 11 + (6316 / 1875) * t ^ 17 + (21514 / 25) * c * t ^ 3 + (-4910609 / 5000) * c * t ^ 5 + (1654267 / 7500) * c * t ^ 7 + (-657391 / 90000) * c * t ^ 9 + (-1962931 / 67500) * c * t ^ 11 + (-35071 / 90000) * c * t ^ 17 + (5983 / 10) * alpha * t ^ 3 + (83009981 / 30000) * alpha * t ^ 5 + (-41122781 / 15000) * alpha * t ^ 7 + (-155776487 / 180000) * alpha * t ^ 9 + (72564193 / 135000) * alpha * t ^ 11 + (989743 / 108000) * alpha * t ^ 17 + (18104 / 25) * alpha * c * t ^ 3 + (-7370194 / 5625) * alpha * c * t ^ 5 + (3261868 / 5625) * alpha * c * t ^ 7 + (25858 / 5625) * alpha * c * t ^ 9 + (7072 / 16875) * alpha * c * t ^ 11 + (20132 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_10, v47_11, v47_20, v47_21, v47_30, v47_31, v47_40, v47_41]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21, phase48_30, phase48_31, phase48_40, phase48_41]
  try simp only [star_one, star_neg]
  linear_combination ((-38409 / 200) * t ^ 3 + (40153961 / 720000) * t ^ 5 + (24829159 / 360000) * t ^ 7 + (7667311 / 1440000) * t ^ 9 + (-998383 / 360000) * t ^ 11 + (-173441 / 1440000) * t ^ 17 + (116219 / 600) * c * t ^ 3 + (-64117823 / 432000) * c * t ^ 5 + (-597563 / 72000) * c * t ^ 7 + (190807 / 864000) * c * t ^ 9 + (1732219 / 648000) * c * t ^ 11 + (-123901 / 4320000) * c * t ^ 17 + (-124 / 75) * c ^ 2 * t ^ 3 + (10969 / 16875) * c ^ 2 * t ^ 5 + (8257 / 16875) * c ^ 2 * t ^ 7 + (484 / 5625) * c ^ 2 * t ^ 9 + (5068 / 50625) * c ^ 2 * t ^ 11 + (146 / 50625) * c ^ 2 * t ^ 17) * alpha_sq + ((368 / 1125) * t ^ 5 + (616 / 1125) * t ^ 7 + (-584 / 1125) * t ^ 9 + (-16 / 45) * t ^ 11 + (-496 / 75) * alpha * t ^ 3 + (21898 / 5625) * alpha * t ^ 5 + (-5671 / 5625) * alpha * t ^ 7 + (1262 / 16875) * alpha * t ^ 9 + (46163 / 50625) * alpha * t ^ 11 + (-584 / 50625) * alpha * t ^ 17) * c_sq
theorem v48_42 (t : ℂ) : (momentPoly 48 z48 4 2).eval t = ((-4739761 / 12) * t ^ 2 + (2341190701 / 3000) * t ^ 4 + (-619374971777 / 1440000) * t ^ 6 + (278189469599 / 7200000) * t ^ 8 + (22153436969 / 14400000) * t ^ 10 + (45115005919 / 14400000) * t ^ 12 + (-5855914681 / 10800000) * t ^ 14 + (-5133608761 / 43200000) * t ^ 18 + (1373200297 / 43200000) * t ^ 20 + (-20984 / 3) * c * t ^ 2 + (4678268 / 375) * c * t ^ 4 + (-95849723 / 15000) * c * t ^ 6 + (41573237 / 75000) * c * t ^ 8 + (373579261 / 450000) * c * t ^ 10 + (-224657359 / 450000) * c * t ^ 12 + (-4535731 / 84375) * c * t ^ 14 + (-9713081 / 1350000) * c * t ^ 18 + (26797 / 90000) * c * t ^ 20 + (558699 / 4) * alpha * t ^ 2 + (-200780927 / 1000) * alpha * t ^ 4 + (14049045179 / 480000) * alpha * t ^ 6 + (233827496977 / 7200000) * alpha * t ^ 8 + (10850565709 / 4800000) * alpha * t ^ 10 + (-27503509069 / 43200000) * alpha * t ^ 12 + (-698774941 / 3600000) * alpha * t ^ 14 + (-56527967 / 4800000) * alpha * t ^ 18 + (-1365153049 / 43200000) * alpha * t ^ 20 + (-20984 / 9) * alpha * c * t ^ 2 + (1657556 / 375) * alpha * c * t ^ 4 + (-377916017 / 135000) * alpha * c * t ^ 6 + (498976703 / 675000) * alpha * c * t ^ 8 + (12059399 / 50000) * alpha * c * t ^ 10 + (-437405327 / 1350000) * alpha * c * t ^ 12 + (6898217 / 253125) * alpha * c * t ^ 14 + (-3422393 / 4050000) * alpha * c * t ^ 18 + (-69203 / 270000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_10, v47_11, v47_12, v47_20, v47_21, v47_22, v47_30, v47_31, v47_32, v47_40, v47_41, v47_42]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22, phase48_30, phase48_31, phase48_32, phase48_40, phase48_41, phase48_42]
  try simp only [star_one, star_neg]
  linear_combination ((2623 / 9) * t ^ 2 + (-354913 / 1125) * t ^ 4 + (134126189 / 540000) * t ^ 6 + (1016828507 / 3600000) * t ^ 8 + (-201362527 / 675000) * t ^ 10 + (-887964349 / 21600000) * t ^ 12 + (163916147 / 5400000) * t ^ 14 + (29230703 / 5400000) * t ^ 18 + (32266091 / 21600000) * t ^ 20 + (598 / 1125) * c * t ^ 4 + (-10180253 / 36000) * c * t ^ 6 + (841589717 / 5400000) * c * t ^ 8 + (630585961 / 5400000) * c * t ^ 10 + (-70697321 / 3600000) * c * t ^ 12 + (-793409 / 112500) * c * t ^ 14 + (-4447427 / 5400000) * c * t ^ 18 + (2797 / 2160000) * c * t ^ 20 + (-2623 / 9) * c ^ 2 * t ^ 2 + (23621 / 75) * c ^ 2 * t ^ 4 + (9288803 / 270000) * c ^ 2 * t ^ 6 + (-141070741 / 2025000) * c ^ 2 * t ^ 8 + (-4199657 / 1350000) * c ^ 2 * t ^ 10 + (-577409 / 1012500) * c ^ 2 * t ^ 12 + (-42571 / 3037500) * c ^ 2 * t ^ 14 + (-74911 / 759375) * c ^ 2 * t ^ 18 + (292 / 759375) * c ^ 2 * t ^ 20) * alpha_sq + ((5246 / 9) * t ^ 2 + (-371404 / 1125) * t ^ 4 + (-275151397 / 540000) * t ^ 6 + (398365241 / 1350000) * t ^ 8 + (57584797 / 5400000) * t ^ 10 + (-171871 / 50000) * t ^ 12 + (203152 / 253125) * t ^ 14 + (4039567 / 16200000) * t ^ 18 + (584 / 253125) * t ^ 20 + (-5246 / 9) * alpha * t ^ 2 + (908684 / 1125) * alpha * t ^ 4 + (-57850121 / 180000) * alpha * t ^ 6 + (71887879 / 1350000) * alpha * t ^ 8 + (-13370719 / 1800000) * alpha * t ^ 10 + (13252111 / 4050000) * alpha * t ^ 12 + (6944 / 9375) * alpha * t ^ 14 + (800891 / 5400000) * alpha * t ^ 18 + (-584 / 253125) * alpha * t ^ 20) * c_sq
theorem v48_43 (t : ℂ) : (momentPoly 48 z48 4 3).eval t = ((7476669 / 5) * t + (-203504961 / 50) * t ^ 3 + (7684284941 / 2000) * t ^ 5 + (-220738717133 / 160000) * t ^ 7 + (183839838811 / 960000) * t ^ 9 + (-231823015881 / 1600000) * t ^ 11 + (9123493741813 / 144000000) * t ^ 13 + (27293109647 / 4500000) * t ^ 15 + (-24263868629 / 16000000) * t ^ 17 + (7560911897 / 43200000) * t ^ 19 + (12295105763 / 144000000) * t ^ 21 + (19604542393 / 432000000) * t ^ 25 + (-1661482 / 5) * c * t + (23692823 / 25) * c * t ^ 3 + (-506646619 / 500) * c * t ^ 5 + (891688986863 / 1800000) * c * t ^ 7 + (-180875717489 / 1800000) * c * t ^ 9 + (330328717 / 144000) * c * t ^ 11 + (8386735949 / 10800000) * c * t ^ 13 + (-631349639 / 900000) * c * t ^ 15 + (138880621 / 2700000) * c * t ^ 17 + (-4596350587 / 162000000) * c * t ^ 19 + (640675381 / 54000000) * c * t ^ 21 + (35519257 / 13500000) * c * t ^ 25 + (-2492223 / 5) * alpha * t + (52841371 / 50) * alpha * t ^ 3 + (-1022205663 / 2000) * alpha * t ^ 5 + (-2010813875293 / 7200000) * alpha * t ^ 7 + (4102578407033 / 14400000) * alpha * t ^ 9 + (-45288502529 / 2880000) * alpha * t ^ 11 + (-4043172862129 / 86400000) * alpha * t ^ 13 + (1534461299 / 180000) * alpha * t ^ 15 + (50182739417 / 86400000) * alpha * t ^ 17 + (-270305766877 / 648000000) * alpha * t ^ 19 + (18113785117 / 432000000) * alpha * t ^ 21 + (36745616903 / 1296000000) * alpha * t ^ 25 + (-1661482 / 5) * alpha * c * t + (18694951 / 25) * alpha * c * t ^ 3 + (-235937211 / 500) * alpha * c * t ^ 5 + (3051306599 / 200000) * alpha * c * t ^ 7 + (61397334143 / 1800000) * alpha * c * t ^ 9 + (21054548629 / 3600000) * alpha * c * t ^ 11 + (7476953243 / 18000000) * alpha * c * t ^ 13 + (2490891143 / 13500000) * alpha * c * t ^ 15 + (49724171 / 4500000) * alpha * c * t ^ 17 + (-2812935353 / 54000000) * alpha * c * t ^ 19 + (1365387461 / 54000000) * alpha * c * t ^ 21 + (3865163 / 40500000) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_03, v47_10, v47_11, v47_12, v47_13, v47_20, v47_21, v47_22, v47_23, v47_30, v47_31, v47_32, v47_33, v47_40, v47_41, v47_42, v47_43]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23, phase48_30, phase48_31, phase48_32, phase48_33, phase48_40, phase48_41, phase48_42, phase48_43]
  try simp only [star_one, star_neg]
  linear_combination ((5301681 / 200) * t ^ 3 + (-197190341 / 6000) * t ^ 5 + (6045484723 / 4800000) * t ^ 7 + (966158611 / 4800000) * t ^ 9 + (122453796467 / 28800000) * t ^ 11 + (200641914773 / 144000000) * t ^ 13 + (-81103444327 / 108000000) * t ^ 15 + (5457396319 / 54000000) * t ^ 17 + (364907569 / 432000000) * t ^ 19 + (-1356241199 / 144000000) * t ^ 21 + (-4182659 / 2160000) * t ^ 25 + (-16041971 / 600) * c * t ^ 3 + (276141713 / 6000) * c * t ^ 5 + (-917237739467 / 43200000) * c * t ^ 7 + (74689761317 / 43200000) * c * t ^ 9 + (-46353384553 / 86400000) * c * t ^ 11 + (164709075347 / 1296000000) * c * t ^ 13 + (5767697243 / 108000000) * c * t ^ 15 + (62229233 / 40500000) * c * t ^ 17 + (25958952583 / 3888000000) * c * t ^ 19 + (-2863530697 / 1296000000) * c * t ^ 21 + (86359 / 1687500) * c * t ^ 25 + (17116 / 75) * c ^ 2 * t ^ 3 + (-552833 / 1500) * c ^ 2 * t ^ 5 + (14644289 / 67500) * c ^ 2 * t ^ 7 + (-348462929 / 5400000) * c ^ 2 * t ^ 9 + (-90311849 / 2700000) * c ^ 2 * t ^ 11 + (76487063 / 2160000) * c ^ 2 * t ^ 13 + (-355771 / 112500) * c ^ 2 * t ^ 15 + (278 / 253125) * c ^ 2 * t ^ 17 + (1192079 / 8100000) * c ^ 2 * t ^ 19 + (112403 / 2160000) * c ^ 2 * t ^ 21) * alpha_sq + ((-34232 / 25) * t ^ 3 + (23977 / 10) * t ^ 5 + (-8131928 / 5625) * t ^ 7 + (30285821 / 112500) * t ^ 9 + (57135697 / 225000) * t ^ 11 + (-2441262431 / 13500000) * t ^ 13 + (127367281 / 6750000) * t ^ 15 + (113119 / 281250) * t ^ 17 + (-29462953 / 20250000) * t ^ 19 + (-1155473 / 13500000) * t ^ 21 + (-20732 / 1265625) * t ^ 25 + (34232 / 75) * alpha * t ^ 3 + (-267457 / 750) * alpha * t ^ 5 + (-3845942 / 16875) * alpha * t ^ 7 + (55369279 / 337500) * alpha * t ^ 9 + (-39158713 / 675000) * alpha * t ^ 11 + (324576191 / 40500000) * alpha * t ^ 13 + (213691573 / 6750000) * alpha * t ^ 15 + (465923 / 2531250) * alpha * t ^ 17 + (85717033 / 60750000) * alpha * t ^ 19 + (-6044527 / 40500000) * alpha * t ^ 21 + (20732 / 3796875) * alpha * t ^ 25) * c_sq
theorem v48_44 (t : ℂ) : (momentPoly 48 z48 4 4).eval t = (119626704 + (-1532144992 / 5) * t ^ 2 + (12510263403 / 50) * t ^ 4 + (-92136293737 / 1500) * t ^ 6 + (472195913944913 / 144000000) * t ^ 8 + (-4054596997317 / 800000) * t ^ 10 + (-1310956080167 / 48000000) * t ^ 12 + (-92712608383439 / 216000000) * t ^ 14 + (198914943297601 / 576000000) * t ^ 16 + (25518804359 / 8000000) * t ^ 18 + (-7030930052747 / 2160000000) * t ^ 20 + (-288668700459 / 40000000) * t ^ 22 + (-666024174817 / 4320000000) * t ^ 24 + (-3356656239037 / 3240000000) * t ^ 26 + (412570977709 / 25920000000) * t ^ 32 + (58689664 / 75) * c * t ^ 4 + (-806693024 / 375) * c * t ^ 6 + (6453266317 / 3125) * c * t ^ 8 + (-892549582 / 1125) * c * t ^ 10 + (1427593649 / 56250) * c * t ^ 12 + (19409146013 / 140625) * c * t ^ 14 + (-18477677447 / 281250) * c * t ^ 16 + (-98598793 / 421875) * c * t ^ 18 + (-2287039621 / 12656250) * c * t ^ 20 + (-320497183 / 2109375) * c * t ^ 22 + (-10508041 / 4218750) * c * t ^ 24 + (-948628487 / 6328125) * c * t ^ 26 + (11757088 / 6328125) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z48, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v47_00, v47_01, v47_02, v47_03, v47_04, v47_10, v47_11, v47_12, v47_13, v47_14, v47_20, v47_21, v47_22, v47_23, v47_24, v47_30, v47_31, v47_32, v47_33, v47_34, v47_40, v47_41, v47_42, v47_43, v47_44]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24, phase48_30, phase48_31, phase48_32, phase48_33, phase48_34, phase48_40, phase48_41, phase48_42, phase48_43, phase48_44]
  try simp only [star_one, star_neg]
  linear_combination ((-1609396 / 15) * t ^ 2 + (5313726 / 25) * t ^ 4 + (-2460804989 / 1500) * t ^ 6 + (10033038499151 / 4500000) * t ^ 8 + (-900856419193 / 1500000) * t ^ 10 + (-48253792093 / 400000) * t ^ 12 + (-6585611002889 / 162000000) * t ^ 14 + (454090633159 / 36000000) * t ^ 16 + (442753190231 / 108000000) * t ^ 18 + (-576758980721 / 405000000) * t ^ 20 + (104480026469 / 135000000) * t ^ 22 + (41693458217 / 180000000) * t ^ 24 + (-30852872257 / 540000000) * t ^ 26 + (-997595963 / 810000000) * t ^ 32 + (-1783804 / 225) * c * t ^ 4 + (1038846 / 125) * c * t ^ 6 + (965318995681 / 27000000) * c * t ^ 8 + (-490616736343 / 10800000) * c * t ^ 10 + (-307089728609 / 54000000) * c * t ^ 12 + (4712249558423 / 324000000) * c * t ^ 14 + (107852916601 / 162000000) * c * t ^ 16 + (-125456144561 / 324000000) * c * t ^ 18 + (453571285897 / 2430000000) * c * t ^ 20 + (-11902076717 / 540000000) * c * t ^ 22 + (-3926323 / 810000000) * c * t ^ 24 + (-13131681533 / 1620000000) * c * t ^ 26 + (-9044773 / 607500000) * c * t ^ 32 + (1609396 / 15) * c ^ 2 * t ^ 2 + (-9207946 / 45) * c ^ 2 * t ^ 4 + (319297567 / 3375) * c ^ 2 * t ^ 6 + (1010269529839 / 81000000) * c ^ 2 * t ^ 8 + (-62399233861 / 9000000) * c ^ 2 * t ^ 10 + (-82217306729 / 54000000) * c ^ 2 * t ^ 12 + (-11364257537 / 32400000) * c ^ 2 * t ^ 14 + (-3270745829 / 40500000) * c ^ 2 * t ^ 16 + (-42762059 / 13500000) * c ^ 2 * t ^ 18 + (16088491741 / 810000000) * c ^ 2 * t ^ 20 + (-6889645597 / 810000000) * c ^ 2 * t ^ 22 + (13550513 / 303750000) * c ^ 2 * t ^ 24 + (-199458821 / 1822500000) * c ^ 2 * t ^ 26 + (42632 / 56953125) * c ^ 2 * t ^ 32) * alpha_sq + ((-6437584 / 15) * t ^ 2 + (66277112 / 75) * t ^ 4 + (-614669116 / 1125) * t ^ 6 + (122398705459 / 1350000) * t ^ 8 + (-833811383 / 90000) * t ^ 10 + (3975127979 / 900000) * t ^ 12 + (103906739881 / 40500000) * t ^ 14 + (-173803687 / 1125000) * t ^ 16 + (34493767 / 1687500) * t ^ 18 + (-9864547193 / 202500000) * t ^ 20 + (1463294947 / 67500000) * t ^ 22 + (2081167 / 25312500) * t ^ 24 + (169384183 / 75937500) * t ^ 26 + (-170528 / 18984375) * t ^ 32) * c_sq
#print axioms v48_00
#print axioms v48_11
#print axioms v48_22
#print axioms v48_33
#print axioms v48_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v49_02 (t : ℂ) : (momentPoly 49 z49 0 2).eval t = ((-6619 / 600) * t ^ 2 + (4151 / 600) * t ^ 4 + (-6 / 25) * c * t ^ 2 + (-1 / 25) * c * t ^ 4 + (-779 / 600) * alpha * t ^ 2 + (-563 / 200) * alpha * t ^ 4 + (2 / 25) * alpha * c * t ^ 2 + (1 / 75) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02]
  try simp only [phase48_00, phase48_01, phase48_02]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 75) * t ^ 2 + (-1 / 225) * c * t ^ 2 + (-2 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((4 / 225) * t ^ 2 + (4 / 225) * alpha * t ^ 2) * c_sq
theorem v49_03 (t : ℂ) : (momentPoly 49 z49 0 3).eval t = ((-411 / 25) * t ^ 3 + (361 / 25) * t ^ 5 + 2 * t ^ 9 + (17 / 12) * c * t ^ 3 + (-111 / 500) * c * t ^ 5 + (71 / 375) * c * t ^ 9 + (118 / 75) * alpha * t ^ 3 + (-54721 / 3000) * alpha * t ^ 5 + (40859 / 9000) * alpha * t ^ 9 + (-73 / 25) * alpha * c * t ^ 3 + (73 / 25) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_03]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03]
  try simp only [star_one, star_neg]
  linear_combination ((-213 / 400) * t ^ 3 + (-3149 / 6000) * t ^ 5 + (1949 / 3600) * c * t ^ 3 + (671 / 18000) * c * t ^ 5 + (-2 / 225) * c ^ 2 * t ^ 3 + (-4 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((8 / 225) * alpha * t ^ 3 + (16 / 1125) * alpha * t ^ 5) * c_sq
theorem v49_04 (t : ℂ) : (momentPoly 49 z49 0 4).eval t = ((1593893 / 4800) * t ^ 4 + (-1453187 / 4000) * t ^ 6 + (12708811 / 240000) * t ^ 8 + (-9113369 / 180000) * t ^ 10 + (4806961 / 720000) * t ^ 16 + (-2521 / 750) * c * t ^ 4 + (7569 / 500) * c * t ^ 6 + (-1523 / 1250) * c * t ^ 8 + (-15073 / 2500) * c * t ^ 10 + (146 / 1875) * c * t ^ 16 + (104073 / 1600) * alpha * t ^ 4 + (683849 / 12000) * alpha * t ^ 6 + (-9949977 / 80000) * alpha * t ^ 8 + (4015129 / 180000) * alpha * t ^ 10 + (545093 / 240000) * alpha * t ^ 16 + (-3749 / 450) * alpha * c * t ^ 4 + (14449 / 1500) * alpha * c * t ^ 6 + (1439 / 1250) * alpha * c * t ^ 8 + (-7073 / 7500) * alpha * c * t ^ 10 + (146 / 5625) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_03, v48_04]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04]
  try simp only [star_one, star_neg]
  linear_combination ((-193 / 450) * t ^ 4 + (23123 / 1800) * t ^ 6 + (101981 / 15000) * t ^ 8 + (10673 / 22500) * t ^ 10 + (-203 / 2250) * c * t ^ 4 + (1397 / 450) * c * t ^ 6 + (229 / 22500) * c * t ^ 8 + (-49699 / 67500) * c * t ^ 10 + (584 / 1125) * c ^ 2 * t ^ 4 + (-352 / 675) * c ^ 2 * t ^ 6 + (-8 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-1058 / 1125) * t ^ 4 + (526 / 375) * t ^ 6 + (-16 / 5625) * t ^ 8 + (1136 / 16875) * t ^ 10 + (-142 / 125) * alpha * t ^ 4 + (758 / 1125) * alpha * t ^ 6 + (16 / 5625) * alpha * t ^ 8 + (-1136 / 16875) * alpha * t ^ 10) * c_sq
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
theorem v49_12 (t : ℂ) : (momentPoly 49 z49 1 2).eval t = ((679 / 10) * t + (-2607 / 40) * t ^ 3 + (2369 / 600) * t ^ 5 + (-97 / 10) * c * t + (6121 / 600) * c * t ^ 3 + (-291 / 200) * c * t ^ 5 + (679 / 30) * alpha * t + (-30929 / 1800) * alpha * t ^ 3 + (-5807 / 1800) * alpha * t ^ 5 + (97 / 10) * alpha * c * t + (-1651 / 200) * alpha * c * t ^ 3 + (-59 / 120) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_10, v48_11, v48_12]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12]
  try simp only [star_one, star_neg]
  linear_combination ((71 / 400) * t ^ 3 + (3149 / 18000) * t ^ 5 + (-1949 / 10800) * c * t ^ 3 + (-671 / 54000) * c * t ^ 5 + (2 / 675) * c ^ 2 * t ^ 3 + (4 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((-4 / 225) * t ^ 3 + (-8 / 1125) * t ^ 5 + (-4 / 675) * alpha * t ^ 3 + (-8 / 3375) * alpha * t ^ 5) * c_sq
theorem v49_13 (t : ℂ) : (momentPoly 49 z49 1 3).eval t = ((-39714 / 25) * t ^ 2 + (1741721 / 750) * t ^ 4 + (-4598429 / 6000) * t ^ 6 + (-23557 / 3600) * t ^ 10 + (-864 / 25) * c * t ^ 2 + (87311 / 3000) * c * t ^ 4 + (581 / 400) * c * t ^ 6 + (2669 / 2000) * c * t ^ 10 + (-4674 / 25) * alpha * t ^ 2 + (-140099 / 750) * alpha * t ^ 4 + (1999331 / 6000) * alpha * t ^ 6 + (4763 / 3600) * alpha * t ^ 10 + (288 / 25) * alpha * c * t ^ 2 + (-92111 / 9000) * alpha * c * t ^ 4 + (379 / 1200) * alpha * c * t ^ 6 + (-1423 / 2000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_03, v48_10, v48_11, v48_12, v48_13]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13]
  try simp only [star_one, star_neg]
  linear_combination ((48 / 25) * t ^ 2 + (-1423 / 1125) * t ^ 4 + (2839 / 6000) * t ^ 6 + (-10673 / 90000) * t ^ 10 + (-16 / 25) * c * t ^ 2 + (1907 / 4500) * c * t ^ 4 + (-4091 / 6000) * c * t ^ 6 + (49699 / 270000) * c * t ^ 10 + (-32 / 25) * c ^ 2 * t ^ 2 + (757 / 900) * c ^ 2 * t ^ 4 + (313 / 1500) * c ^ 2 * t ^ 6) * alpha_sq + ((64 / 25) * t ^ 2 + (-427 / 375) * t ^ 4 + (-947 / 1125) * t ^ 6 + (284 / 16875) * t ^ 10 + (64 / 25) * alpha * t ^ 2 + (-2449 / 1125) * alpha * t ^ 4 + (221 / 1125) * alpha * t ^ 6 + (284 / 16875) * alpha * t ^ 10) * c_sq
theorem v49_14 (t : ℂ) : (momentPoly 49 z49 1 4).eval t = ((-15618 / 5) * t ^ 3 + (6981947 / 1250) * t ^ 5 + (-4734421 / 1875) * t ^ 7 + (1540663 / 3750) * t ^ 9 + (-1980224 / 5625) * t ^ 11 + (23981 / 5625) * t ^ 17 + (1615 / 6) * c * t ^ 3 + (-58503563 / 180000) * c * t ^ 5 + (3120041 / 30000) * c * t ^ 7 + (-136067 / 24000) * c * t ^ 9 + (-525271 / 18000) * c * t ^ 11 + (-4117 / 40000) * c * t ^ 17 + (4484 / 15) * alpha * t ^ 3 + (-213111229 / 60000) * alpha * t ^ 5 + (29944943 / 10000) * alpha * t ^ 7 + (32590119 / 40000) * alpha * t ^ 9 + (-179583989 / 270000) * alpha * t ^ 11 + (-1471543 / 216000) * alpha * t ^ 17 + (-2774 / 5) * alpha * c * t ^ 3 + (1314019 / 1250) * alpha * c * t ^ 5 + (-310999 / 625) * alpha * c * t ^ 7 + (8971 / 3750) * alpha * c * t ^ 9 + (-1768 / 5625) * alpha * c * t ^ 11 + (-5033 / 5625) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_03, v48_04, v48_10, v48_11, v48_12, v48_13, v48_14]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14]
  try simp only [star_one, star_neg]
  linear_combination ((-4047 / 40) * t ^ 3 + (-11452823 / 720000) * t ^ 5 + (9321853 / 120000) * t ^ 7 + (13805807 / 1440000) * t ^ 9 + (-66773 / 43200) * t ^ 11 + (-3245839 / 21600000) * t ^ 17 + (37031 / 360) * c * t ^ 3 + (-170336827 / 2160000) * c * t ^ 5 + (-9907829 / 1080000) * c * t ^ 7 + (-654181 / 480000) * c * t ^ 9 + (4741223 / 3240000) * c * t ^ 11 + (111533 / 64800000) * c * t ^ 17 + (-76 / 45) * c ^ 2 * t ^ 3 + (13507 / 16875) * c ^ 2 * t ^ 5 + (8981 / 16875) * c ^ 2 * t ^ 7 + (232 / 3375) * c ^ 2 * t ^ 9 + (4168 / 50625) * c ^ 2 * t ^ 11 + (584 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((176 / 375) * t ^ 5 + (144 / 625) * t ^ 7 + (-2336 / 5625) * t ^ 9 + (-64 / 225) * t ^ 11 + (304 / 45) * alpha * t ^ 3 + (-25316 / 5625) * alpha * t ^ 5 + (904 / 5625) * alpha * t ^ 7 + (-536 / 16875) * alpha * t ^ 9 + (-35516 / 50625) * alpha * t ^ 11 + (2336 / 253125) * alpha * t ^ 17) * c_sq
theorem v49_20 (t : ℂ) : (momentPoly 49 z49 2 0).eval t = ((-6619 / 600) * t ^ 2 + (4151 / 600) * t ^ 4 + (-6 / 25) * c * t ^ 2 + (-1 / 25) * c * t ^ 4 + (779 / 600) * alpha * t ^ 2 + (563 / 200) * alpha * t ^ 4 + (-2 / 25) * alpha * c * t ^ 2 + (-1 / 75) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_10, v48_20]
  try simp only [phase48_00, phase48_10, phase48_20]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 75) * t ^ 2 + (-1 / 225) * c * t ^ 2 + (-2 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((4 / 225) * t ^ 2 + (-4 / 225) * alpha * t ^ 2) * c_sq
theorem v49_21 (t : ℂ) : (momentPoly 49 z49 2 1).eval t = ((679 / 10) * t + (-2607 / 40) * t ^ 3 + (2369 / 600) * t ^ 5 + (-97 / 10) * c * t + (6121 / 600) * c * t ^ 3 + (-291 / 200) * c * t ^ 5 + (-679 / 30) * alpha * t + (30929 / 1800) * alpha * t ^ 3 + (5807 / 1800) * alpha * t ^ 5 + (-97 / 10) * alpha * c * t + (1651 / 200) * alpha * c * t ^ 3 + (59 / 120) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_10, v48_11, v48_20, v48_21]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21]
  try simp only [star_one, star_neg]
  linear_combination ((71 / 400) * t ^ 3 + (3149 / 18000) * t ^ 5 + (-1949 / 10800) * c * t ^ 3 + (-671 / 54000) * c * t ^ 5 + (2 / 675) * c ^ 2 * t ^ 3 + (4 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((-4 / 225) * t ^ 3 + (-8 / 1125) * t ^ 5 + (4 / 675) * alpha * t ^ 3 + (8 / 3375) * alpha * t ^ 5) * c_sq
theorem v49_22 (t : ℂ) : (momentPoly 49 z49 2 2).eval t = (4753 + (-37888 / 5) * t ^ 2 + (51471677 / 18000) * t ^ 4 + (59107 / 1800) * t ^ 6 + (415973 / 18000) * t ^ 8 + (584 / 125) * c * t ^ 4 + (-292 / 75) * c * t ^ 6 + (-292 / 375) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_10, v48_11, v48_12, v48_20, v48_21, v48_22]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22]
  try simp only [star_one, star_neg]
  linear_combination ((-64 / 25) * t ^ 2 + (12349 / 6750) * t ^ 4 + (-132649 / 27000) * t ^ 6 + (-101981 / 45000) * t ^ 8 + (64 / 75) * c * t ^ 2 + (-3611 / 6750) * c * t ^ 4 + (-1697 / 13500) * c * t ^ 6 + (-229 / 67500) * c * t ^ 8 + (128 / 75) * c ^ 2 * t ^ 2 + (-4369 / 3375) * c ^ 2 * t ^ 4 + (-1057 / 10125) * c ^ 2 * t ^ 6 + (8 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((-512 / 75) * t ^ 2 + (18644 / 3375) * t ^ 4 + (44 / 675) * t ^ 6 + (-32 / 16875) * t ^ 8) * c_sq
theorem v49_23 (t : ℂ) : (momentPoly 49 z49 2 3).eval t = ((97783 / 10) * t + (-148599 / 8) * t ^ 3 + (71928349 / 7500) * t ^ 5 + (-19556021 / 24000) * t ^ 7 + (20303557 / 120000) * t ^ 9 + (-20782997 / 360000) * t ^ 11 + (-1075359 / 40000) * t ^ 13 + (-13969 / 10) * c * t + (116299 / 40) * c * t ^ 3 + (-338323787 / 180000) * c * t ^ 5 + (32913743 / 90000) * c * t ^ 7 + (-524249 / 60000) * c * t ^ 9 + (64391 / 45000) * c * t ^ 11 + (2834 / 1875) * c * t ^ 13 + (97783 / 30) * alpha * t + (-587651 / 120) * alpha * t ^ 3 + (16872059 / 22500) * alpha * t ^ 5 + (42075407 / 40000) * alpha * t ^ 7 + (-48505771 / 360000) * alpha * t ^ 9 + (-47947909 / 1080000) * alpha * t ^ 11 + (39144281 / 1080000) * alpha * t ^ 13 + (13969 / 10) * alpha * c * t + (-94107 / 40) * alpha * c * t ^ 3 + (147358987 / 180000) * alpha * c * t ^ 5 + (4164283 / 30000) * alpha * c * t ^ 7 + (431321 / 60000) * alpha * c * t ^ 9 + (-919 / 45000) * alpha * c * t ^ 11 + (1264 / 5625) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_03, v48_10, v48_11, v48_12, v48_13, v48_20, v48_21, v48_22, v48_23]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23]
  try simp only [star_one, star_neg]
  linear_combination ((4047 / 80) * t ^ 3 + (78437 / 30000) * t ^ 5 + (-569713 / 15000) * t ^ 7 + (-1154057 / 90000) * t ^ 9 + (-116899 / 135000) * t ^ 11 + (2494297 / 1350000) * t ^ 13 + (-37031 / 720) * c * t ^ 3 + (4042321 / 90000) * c * t ^ 5 + (7147 / 135000) * c * t ^ 7 + (84493 / 135000) * c * t ^ 9 + (-19897 / 202500) * c * t ^ 11 + (49699 / 2025000) * c * t ^ 13 + (38 / 45) * c ^ 2 * t ^ 3 + (-18437 / 33750) * c ^ 2 * t ^ 5 + (-227 / 2700) * c ^ 2 * t ^ 7 + (229 / 33750) * c ^ 2 * t ^ 9 + (-4349 / 67500) * c ^ 2 * t ^ 11) * alpha_sq + ((-76 / 15) * t ^ 3 + (20557 / 5625) * t ^ 5 + (4681 / 11250) * t ^ 7 + (-1184 / 5625) * t ^ 9 + (2243 / 6750) * t ^ 11 + (568 / 84375) * t ^ 13 + (-76 / 45) * alpha * t ^ 3 + (7277 / 16875) * alpha * t ^ 5 + (23497 / 33750) * alpha * t ^ 7 + (3488 / 16875) * alpha * t ^ 9 + (1283 / 20250) * alpha * t ^ 11 + (568 / 253125) * alpha * t ^ 13) * c_sq
theorem v49_24 (t : ℂ) : (momentPoly 49 z49 2 4).eval t = ((-45280579 / 150) * t ^ 2 + (2063833259 / 3000) * t ^ 4 + (-1159384350599 / 2400000) * t ^ 6 + (657199748707 / 7200000) * t ^ 8 + (54600089449 / 14400000) * t ^ 10 + (87929161649 / 43200000) * t ^ 12 + (-914078561 / 2160000) * t ^ 14 + (-623601557 / 8640000) * t ^ 18 + (847987709 / 43200000) * t ^ 20 + (-164184 / 25) * c * t ^ 2 + (4505242 / 375) * c * t ^ 4 + (-289164979 / 50000) * c * t ^ 6 + (174054347 / 900000) * c * t ^ 8 + (172161163 / 300000) * c * t ^ 10 + (-83263921 / 200000) * c * t ^ 12 + (-660157 / 18750) * c * t ^ 14 + (-1405897 / 300000) * c * t ^ 18 + (21997 / 120000) * c * t ^ 20 + (-5329139 / 150) * alpha * t ^ 2 + (15405979 / 3000) * alpha * t ^ 4 + (578776493051 / 7200000) * alpha * t ^ 6 + (-352146188621 / 7200000) * alpha * t ^ 8 + (-5491689869 / 4800000) * alpha * t ^ 10 + (-15849352607 / 43200000) * alpha * t ^ 12 + (81909871 / 2160000) * alpha * t ^ 14 + (-188344901 / 8640000) * alpha * t ^ 18 + (58977559 / 1600000) * alpha * t ^ 20 + (54728 / 25) * alpha * c * t ^ 2 + (-4730842 / 1125) * alpha * c * t ^ 4 + (3334340203 / 1350000) * alpha * c * t ^ 6 + (-1398850411 / 2700000) * alpha * c * t ^ 8 + (-156786859 / 900000) * alpha * c * t ^ 10 + (482036179 / 1800000) * alpha * c * t ^ 12 + (-3575447 / 168750) * alpha * c * t ^ 14 + (428123 / 2700000) * alpha * c * t ^ 18 + (74003 / 360000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_03, v48_04, v48_10, v48_11, v48_12, v48_13, v48_14, v48_20, v48_21, v48_22, v48_23, v48_24]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24]
  try simp only [star_one, star_neg]
  linear_combination ((27364 / 75) * t ^ 2 + (-535048 / 1125) * t ^ 4 + (184899869 / 675000) * t ^ 6 + (797785913 / 10800000) * t ^ 8 + (-16695233 / 120000) * t ^ 10 + (-476710267 / 12960000) * t ^ 12 + (337811449 / 16200000) * t ^ 14 + (24245237 / 8100000) * t ^ 18 + (208358807 / 108000000) * t ^ 20 + (-27364 / 225) * c * t ^ 2 + (179258 / 1125) * c * t ^ 4 + (-176434691 / 675000) * c * t ^ 6 + (773150233 / 5400000) * c * t ^ 8 + (270635393 / 2700000) * c * t ^ 10 + (-376028131 / 10800000) * c * t ^ 12 + (-1055819 / 168750) * c * t ^ 14 + (-185177 / 300000) * c * t ^ 18 + (-6803 / 2160000) * c * t ^ 20 + (-54728 / 225) * c ^ 2 * t ^ 2 + (71158 / 225) * c ^ 2 * t ^ 4 + (-1410863 / 112500) * c ^ 2 * t ^ 6 + (-32416819 / 506250) * c ^ 2 * t ^ 8 + (-190807 / 112500) * c ^ 2 * t ^ 10 + (-55454 / 253125) * c ^ 2 * t ^ 12 + (-21547 / 759375) * c ^ 2 * t ^ 14 + (-59812 / 759375) * c ^ 2 * t ^ 18 + (1168 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((109456 / 225) * t ^ 2 + (-160552 / 375) * t ^ 4 + (-23203613 / 75000) * t ^ 6 + (17878241 / 67500) * t ^ 8 + (8331161 / 1350000) * t ^ 10 + (-4479611 / 1012500) * t ^ 12 + (180976 / 253125) * t ^ 14 + (879811 / 4050000) * t ^ 18 + (2336 / 1265625) * t ^ 20 + (109456 / 225) * alpha * t ^ 2 + (-920824 / 1125) * alpha * t ^ 4 + (272736571 / 675000) * alpha * t ^ 6 + (-6365641 / 112500) * alpha * t ^ 8 + (8013593 / 1350000) * alpha * t ^ 10 + (-4307323 / 1012500) * alpha * t ^ 12 + (-131536 / 253125) * alpha * t ^ 14 + (-408637 / 4050000) * alpha * t ^ 18 + (2336 / 1265625) * alpha * t ^ 20) * c_sq
theorem v49_30 (t : ℂ) : (momentPoly 49 z49 3 0).eval t = ((-411 / 25) * t ^ 3 + (361 / 25) * t ^ 5 + 2 * t ^ 9 + (17 / 12) * c * t ^ 3 + (-111 / 500) * c * t ^ 5 + (71 / 375) * c * t ^ 9 + (-118 / 75) * alpha * t ^ 3 + (54721 / 3000) * alpha * t ^ 5 + (-40859 / 9000) * alpha * t ^ 9 + (73 / 25) * alpha * c * t ^ 3 + (-73 / 25) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_10, v48_20, v48_30]
  try simp only [phase48_00, phase48_10, phase48_20, phase48_30]
  try simp only [star_one, star_neg]
  linear_combination ((-213 / 400) * t ^ 3 + (-3149 / 6000) * t ^ 5 + (1949 / 3600) * c * t ^ 3 + (671 / 18000) * c * t ^ 5 + (-2 / 225) * c ^ 2 * t ^ 3 + (-4 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-8 / 225) * alpha * t ^ 3 + (-16 / 1125) * alpha * t ^ 5) * c_sq
theorem v49_31 (t : ℂ) : (momentPoly 49 z49 3 1).eval t = ((-39714 / 25) * t ^ 2 + (1741721 / 750) * t ^ 4 + (-4598429 / 6000) * t ^ 6 + (-23557 / 3600) * t ^ 10 + (-864 / 25) * c * t ^ 2 + (87311 / 3000) * c * t ^ 4 + (581 / 400) * c * t ^ 6 + (2669 / 2000) * c * t ^ 10 + (4674 / 25) * alpha * t ^ 2 + (140099 / 750) * alpha * t ^ 4 + (-1999331 / 6000) * alpha * t ^ 6 + (-4763 / 3600) * alpha * t ^ 10 + (-288 / 25) * alpha * c * t ^ 2 + (92111 / 9000) * alpha * c * t ^ 4 + (-379 / 1200) * alpha * c * t ^ 6 + (1423 / 2000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_10, v48_11, v48_20, v48_21, v48_30, v48_31]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21, phase48_30, phase48_31]
  try simp only [star_one, star_neg]
  linear_combination ((48 / 25) * t ^ 2 + (-1423 / 1125) * t ^ 4 + (2839 / 6000) * t ^ 6 + (-10673 / 90000) * t ^ 10 + (-16 / 25) * c * t ^ 2 + (1907 / 4500) * c * t ^ 4 + (-4091 / 6000) * c * t ^ 6 + (49699 / 270000) * c * t ^ 10 + (-32 / 25) * c ^ 2 * t ^ 2 + (757 / 900) * c ^ 2 * t ^ 4 + (313 / 1500) * c ^ 2 * t ^ 6) * alpha_sq + ((64 / 25) * t ^ 2 + (-427 / 375) * t ^ 4 + (-947 / 1125) * t ^ 6 + (284 / 16875) * t ^ 10 + (-64 / 25) * alpha * t ^ 2 + (2449 / 1125) * alpha * t ^ 4 + (-221 / 1125) * alpha * t ^ 6 + (-284 / 16875) * alpha * t ^ 10) * c_sq
theorem v49_32 (t : ℂ) : (momentPoly 49 z49 3 2).eval t = ((97783 / 10) * t + (-148599 / 8) * t ^ 3 + (71928349 / 7500) * t ^ 5 + (-19556021 / 24000) * t ^ 7 + (20303557 / 120000) * t ^ 9 + (-20782997 / 360000) * t ^ 11 + (-1075359 / 40000) * t ^ 13 + (-13969 / 10) * c * t + (116299 / 40) * c * t ^ 3 + (-338323787 / 180000) * c * t ^ 5 + (32913743 / 90000) * c * t ^ 7 + (-524249 / 60000) * c * t ^ 9 + (64391 / 45000) * c * t ^ 11 + (2834 / 1875) * c * t ^ 13 + (-97783 / 30) * alpha * t + (587651 / 120) * alpha * t ^ 3 + (-16872059 / 22500) * alpha * t ^ 5 + (-42075407 / 40000) * alpha * t ^ 7 + (48505771 / 360000) * alpha * t ^ 9 + (47947909 / 1080000) * alpha * t ^ 11 + (-39144281 / 1080000) * alpha * t ^ 13 + (-13969 / 10) * alpha * c * t + (94107 / 40) * alpha * c * t ^ 3 + (-147358987 / 180000) * alpha * c * t ^ 5 + (-4164283 / 30000) * alpha * c * t ^ 7 + (-431321 / 60000) * alpha * c * t ^ 9 + (919 / 45000) * alpha * c * t ^ 11 + (-1264 / 5625) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_10, v48_11, v48_12, v48_20, v48_21, v48_22, v48_30, v48_31, v48_32]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22, phase48_30, phase48_31, phase48_32]
  try simp only [star_one, star_neg]
  linear_combination ((4047 / 80) * t ^ 3 + (78437 / 30000) * t ^ 5 + (-569713 / 15000) * t ^ 7 + (-1154057 / 90000) * t ^ 9 + (-116899 / 135000) * t ^ 11 + (2494297 / 1350000) * t ^ 13 + (-37031 / 720) * c * t ^ 3 + (4042321 / 90000) * c * t ^ 5 + (7147 / 135000) * c * t ^ 7 + (84493 / 135000) * c * t ^ 9 + (-19897 / 202500) * c * t ^ 11 + (49699 / 2025000) * c * t ^ 13 + (38 / 45) * c ^ 2 * t ^ 3 + (-18437 / 33750) * c ^ 2 * t ^ 5 + (-227 / 2700) * c ^ 2 * t ^ 7 + (229 / 33750) * c ^ 2 * t ^ 9 + (-4349 / 67500) * c ^ 2 * t ^ 11) * alpha_sq + ((-76 / 15) * t ^ 3 + (20557 / 5625) * t ^ 5 + (4681 / 11250) * t ^ 7 + (-1184 / 5625) * t ^ 9 + (2243 / 6750) * t ^ 11 + (568 / 84375) * t ^ 13 + (76 / 45) * alpha * t ^ 3 + (-7277 / 16875) * alpha * t ^ 5 + (-23497 / 33750) * alpha * t ^ 7 + (-3488 / 16875) * alpha * t ^ 9 + (-1283 / 20250) * alpha * t ^ 11 + (-568 / 253125) * alpha * t ^ 13) * c_sq
theorem v49_33 (t : ℂ) : (momentPoly 49 z49 3 3).eval t = (684481 + (-8099744 / 5) * t ^ 2 + (2419168819 / 2000) * t ^ 4 + (-7953043561 / 30000) * t ^ 6 + (-25922129 / 50000) * t ^ 8 + (-4375880503 / 600000) * t ^ 10 + (-523001 / 225000) * t ^ 12 + (-64730591 / 180000) * t ^ 14 + (133865093 / 5400000) * t ^ 18 + (247032 / 125) * c * t ^ 4 + (-4531081 / 1250) * c * t ^ 6 + (11917831 / 7500) * c * t ^ 8 + (19217 / 500) * c * t ^ 10 + (-513131 / 7500) * c * t ^ 12 + (221977 / 2500) * c * t ^ 14 + (284 / 375) * c * t ^ 18) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_03, v48_10, v48_11, v48_12, v48_13, v48_20, v48_21, v48_22, v48_23, v48_30, v48_31, v48_32, v48_33]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23, phase48_30, phase48_31, phase48_32, phase48_33]
  try simp only [star_one, star_neg]
  linear_combination ((-13682 / 25) * t ^ 2 + (580403 / 750) * t ^ 4 + (-420856619 / 180000) * t ^ 6 + (1730345317 / 1800000) * t ^ 8 + (1359051097 / 1800000) * t ^ 10 + (11941081 / 1080000) * t ^ 12 + (-14136949 / 600000) * t ^ 14 + (3140189 / 1687500) * t ^ 18 + (13682 / 75) * c * t ^ 2 + (-169717 / 750) * c * t ^ 4 + (-681953 / 180000) * c * t ^ 6 + (11024509 / 120000) * c * t ^ 8 + (-10921013 / 360000) * c * t ^ 10 + (-3055589 / 216000) * c * t ^ 12 + (34068029 / 5400000) * c * t ^ 14 + (27364 / 75) * c ^ 2 * t ^ 2 + (-205343 / 375) * c ^ 2 * t ^ 4 + (20378579 / 135000) * c ^ 2 * t ^ 6 + (12729103 / 337500) * c ^ 2 * t ^ 8 + (1477711 / 675000) * c ^ 2 * t ^ 10 + (8332 / 28125) * c ^ 2 * t ^ 12 + (421 / 56250) * c ^ 2 * t ^ 14) * alpha_sq + ((-109456 / 75) * t ^ 2 + (876268 / 375) * t ^ 4 + (-9877169 / 11250) * t ^ 6 + (-75621 / 3125) * t ^ 8 + (-508013 / 56250) * t ^ 10 + (-38374 / 28125) * t ^ 12 + (57952 / 84375) * t ^ 14 + (-40328 / 1265625) * t ^ 18) * c_sq
theorem v49_34 (t : ℂ) : (momentPoly 49 z49 3 4).eval t = ((18582823 / 10) * t + (-52392879 / 10) * t ^ 3 + (25205117803 / 5000) * t ^ 5 + (-43199550811 / 24000) * t ^ 7 + (1753264632171 / 8000000) * t ^ 9 + (-1343606190659 / 12000000) * t ^ 11 + (3242220693887 / 144000000) * t ^ 13 + (223588634123 / 18000000) * t ^ 15 + (-79820983511 / 48000000) * t ^ 17 + (-3193933451 / 108000000) * t ^ 19 + (12609853973 / 144000000) * t ^ 21 + (2249223929 / 48000000) * t ^ 25 + (-2654689 / 10) * c * t + (41004579 / 50) * c * t ^ 3 + (-9344014547 / 10000) * c * t ^ 5 + (3356714585509 / 7200000) * c * t ^ 7 + (-635016220063 / 7200000) * c * t ^ 9 + (151099772003 / 72000000) * c * t ^ 11 + (45295331431 / 216000000) * c * t ^ 13 + (-11599849309 / 18000000) * c * t ^ 15 + (575964001 / 18000000) * c * t ^ 17 + (-297780313 / 8000000) * c * t ^ 19 + (1292286881 / 72000000) * c * t ^ 21 + (33719257 / 18000000) * c * t ^ 25 + (18582823 / 30) * alpha * t + (-69064457 / 50) * alpha * t ^ 3 + (10081297523 / 15000) * alpha * t ^ 5 + (239568379523 / 600000) * alpha * t ^ 7 + (-1703911066801 / 4800000) * alpha * t ^ 9 + (625478936869 / 36000000) * alpha * t ^ 11 + (17994286517087 / 432000000) * alpha * t ^ 13 + (-707190653477 / 54000000) * alpha * t ^ 15 + (-182048246341 / 432000000) * alpha * t ^ 17 + (61246859261 / 324000000) * alpha * t ^ 19 + (1625934581 / 432000000) * alpha * t ^ 21 + (-32283030271 / 1296000000) * alpha * t ^ 25 + (2654689 / 10) * alpha * c * t + (-33180147 / 50) * alpha * c * t ^ 3 + (4954711347 / 10000) * alpha * c * t ^ 5 + (-442390383541 / 7200000) * alpha * c * t ^ 7 + (-1110696636661 / 36000000) * alpha * c * t ^ 9 + (-121494759473 / 24000000) * alpha * c * t ^ 11 + (15293842403 / 72000000) * alpha * c * t ^ 13 + (-212973499 / 2000000) * alpha * c * t ^ 15 + (-229760609 / 18000000) * alpha * c * t ^ 17 + (6876305683 / 216000000) * alpha * c * t ^ 19 + (-1253025329 / 72000000) * alpha * c * t ^ 21 + (1534837 / 54000000) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_03, v48_04, v48_10, v48_11, v48_12, v48_13, v48_14, v48_20, v48_21, v48_22, v48_23, v48_24, v48_30, v48_31, v48_32, v48_33, v48_34]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24, phase48_30, phase48_31, phase48_32, phase48_33, phase48_34]
  try simp only [star_one, star_neg]
  linear_combination ((1426887 / 100) * t ^ 3 + (-368892859 / 30000) * t ^ 5 + (-14895419287 / 1600000) * t ^ 7 + (77342304913 / 72000000) * t ^ 9 + (841382937559 / 144000000) * t ^ 11 + (16395899449 / 16000000) * t ^ 13 + (-88511366611 / 108000000) * t ^ 15 + (4907053847 / 54000000) * t ^ 17 + (6640526491 / 1296000000) * t ^ 19 + (-3227403913 / 432000000) * t ^ 21 + (-1426123621 / 810000000) * t ^ 25 + (-4352117 / 300) * c * t ^ 3 + (2343546313 / 90000) * c * t ^ 5 + (-105848157911 / 8640000) * c * t ^ 7 + (40103363657 / 43200000) * c * t ^ 9 + (-184819576373 / 432000000) * c * t ^ 11 + (13634260891 / 259200000) * c * t ^ 13 + (1304277913 / 64800000) * c * t ^ 15 + (8073989 / 4500000) * c * t ^ 17 + (1379077667 / 777600000) * c * t ^ 19 + (-838141109 / 1296000000) * c * t ^ 21 + (3628027 / 75937500) * c * t ^ 25 + (17864 / 75) * c ^ 2 * t ^ 3 + (-2238821 / 5625) * c ^ 2 * t ^ 5 + (267080297 / 1350000) * c ^ 2 * t ^ 7 + (-244890139 / 6750000) * c ^ 2 * t ^ 9 + (-366797597 / 13500000) * c ^ 2 * t ^ 11 + (440473303 / 13500000) * c ^ 2 * t ^ 13 + (-6812377 / 2531250) * c ^ 2 * t ^ 15 + (5612 / 1265625) * c ^ 2 * t ^ 17 + (2058169 / 40500000) * c ^ 2 * t ^ 19 + (117203 / 2700000) * c ^ 2 * t ^ 21) * alpha_sq + ((-35728 / 25) * t ^ 3 + (4871962 / 1875) * t ^ 5 + (-64585349 / 45000) * t ^ 7 + (11275393 / 62500) * t ^ 9 + (481859617 / 2250000) * t ^ 11 + (-566979049 / 3375000) * t ^ 13 + (8875867 / 562500) * t ^ 15 + (4738 / 16875) * t ^ 17 + (-15926347 / 20250000) * t ^ 19 + (-299357 / 3375000) * t ^ 21 + (-82928 / 6328125) * t ^ 25 + (-35728 / 75) * alpha * t ^ 3 + (2401882 / 5625) * alpha * t ^ 5 + (178233191 / 675000) * alpha * t ^ 7 + (-23313641 / 112500) * alpha * t ^ 9 + (131719393 / 6750000) * alpha * t ^ 11 + (-3629873 / 405000) * alpha * t ^ 13 + (-5052823 / 202500) * alpha * t ^ 15 + (-203662 / 1265625) * alpha * t ^ 17 + (-12958991 / 12150000) * alpha * t ^ 19 + (1140643 / 10125000) * alpha * t ^ 21 + (-82928 / 18984375) * alpha * t ^ 25) * c_sq
theorem v49_40 (t : ℂ) : (momentPoly 49 z49 4 0).eval t = ((1593893 / 4800) * t ^ 4 + (-1453187 / 4000) * t ^ 6 + (12708811 / 240000) * t ^ 8 + (-9113369 / 180000) * t ^ 10 + (4806961 / 720000) * t ^ 16 + (-2521 / 750) * c * t ^ 4 + (7569 / 500) * c * t ^ 6 + (-1523 / 1250) * c * t ^ 8 + (-15073 / 2500) * c * t ^ 10 + (146 / 1875) * c * t ^ 16 + (-104073 / 1600) * alpha * t ^ 4 + (-683849 / 12000) * alpha * t ^ 6 + (9949977 / 80000) * alpha * t ^ 8 + (-4015129 / 180000) * alpha * t ^ 10 + (-545093 / 240000) * alpha * t ^ 16 + (3749 / 450) * alpha * c * t ^ 4 + (-14449 / 1500) * alpha * c * t ^ 6 + (-1439 / 1250) * alpha * c * t ^ 8 + (7073 / 7500) * alpha * c * t ^ 10 + (-146 / 5625) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_10, v48_20, v48_30, v48_40]
  try simp only [phase48_00, phase48_10, phase48_20, phase48_30, phase48_40]
  try simp only [star_one, star_neg]
  linear_combination ((-193 / 450) * t ^ 4 + (23123 / 1800) * t ^ 6 + (101981 / 15000) * t ^ 8 + (10673 / 22500) * t ^ 10 + (-203 / 2250) * c * t ^ 4 + (1397 / 450) * c * t ^ 6 + (229 / 22500) * c * t ^ 8 + (-49699 / 67500) * c * t ^ 10 + (584 / 1125) * c ^ 2 * t ^ 4 + (-352 / 675) * c ^ 2 * t ^ 6 + (-8 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-1058 / 1125) * t ^ 4 + (526 / 375) * t ^ 6 + (-16 / 5625) * t ^ 8 + (1136 / 16875) * t ^ 10 + (142 / 125) * alpha * t ^ 4 + (-758 / 1125) * alpha * t ^ 6 + (-16 / 5625) * alpha * t ^ 8 + (1136 / 16875) * alpha * t ^ 10) * c_sq
theorem v49_41 (t : ℂ) : (momentPoly 49 z49 4 1).eval t = ((-15618 / 5) * t ^ 3 + (6981947 / 1250) * t ^ 5 + (-4734421 / 1875) * t ^ 7 + (1540663 / 3750) * t ^ 9 + (-1980224 / 5625) * t ^ 11 + (23981 / 5625) * t ^ 17 + (1615 / 6) * c * t ^ 3 + (-58503563 / 180000) * c * t ^ 5 + (3120041 / 30000) * c * t ^ 7 + (-136067 / 24000) * c * t ^ 9 + (-525271 / 18000) * c * t ^ 11 + (-4117 / 40000) * c * t ^ 17 + (-4484 / 15) * alpha * t ^ 3 + (213111229 / 60000) * alpha * t ^ 5 + (-29944943 / 10000) * alpha * t ^ 7 + (-32590119 / 40000) * alpha * t ^ 9 + (179583989 / 270000) * alpha * t ^ 11 + (1471543 / 216000) * alpha * t ^ 17 + (2774 / 5) * alpha * c * t ^ 3 + (-1314019 / 1250) * alpha * c * t ^ 5 + (310999 / 625) * alpha * c * t ^ 7 + (-8971 / 3750) * alpha * c * t ^ 9 + (1768 / 5625) * alpha * c * t ^ 11 + (5033 / 5625) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_10, v48_11, v48_20, v48_21, v48_30, v48_31, v48_40, v48_41]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21, phase48_30, phase48_31, phase48_40, phase48_41]
  try simp only [star_one, star_neg]
  linear_combination ((-4047 / 40) * t ^ 3 + (-11452823 / 720000) * t ^ 5 + (9321853 / 120000) * t ^ 7 + (13805807 / 1440000) * t ^ 9 + (-66773 / 43200) * t ^ 11 + (-3245839 / 21600000) * t ^ 17 + (37031 / 360) * c * t ^ 3 + (-170336827 / 2160000) * c * t ^ 5 + (-9907829 / 1080000) * c * t ^ 7 + (-654181 / 480000) * c * t ^ 9 + (4741223 / 3240000) * c * t ^ 11 + (111533 / 64800000) * c * t ^ 17 + (-76 / 45) * c ^ 2 * t ^ 3 + (13507 / 16875) * c ^ 2 * t ^ 5 + (8981 / 16875) * c ^ 2 * t ^ 7 + (232 / 3375) * c ^ 2 * t ^ 9 + (4168 / 50625) * c ^ 2 * t ^ 11 + (584 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((176 / 375) * t ^ 5 + (144 / 625) * t ^ 7 + (-2336 / 5625) * t ^ 9 + (-64 / 225) * t ^ 11 + (-304 / 45) * alpha * t ^ 3 + (25316 / 5625) * alpha * t ^ 5 + (-904 / 5625) * alpha * t ^ 7 + (536 / 16875) * alpha * t ^ 9 + (35516 / 50625) * alpha * t ^ 11 + (-2336 / 253125) * alpha * t ^ 17) * c_sq
theorem v49_42 (t : ℂ) : (momentPoly 49 z49 4 2).eval t = ((-45280579 / 150) * t ^ 2 + (2063833259 / 3000) * t ^ 4 + (-1159384350599 / 2400000) * t ^ 6 + (657199748707 / 7200000) * t ^ 8 + (54600089449 / 14400000) * t ^ 10 + (87929161649 / 43200000) * t ^ 12 + (-914078561 / 2160000) * t ^ 14 + (-623601557 / 8640000) * t ^ 18 + (847987709 / 43200000) * t ^ 20 + (-164184 / 25) * c * t ^ 2 + (4505242 / 375) * c * t ^ 4 + (-289164979 / 50000) * c * t ^ 6 + (174054347 / 900000) * c * t ^ 8 + (172161163 / 300000) * c * t ^ 10 + (-83263921 / 200000) * c * t ^ 12 + (-660157 / 18750) * c * t ^ 14 + (-1405897 / 300000) * c * t ^ 18 + (21997 / 120000) * c * t ^ 20 + (5329139 / 150) * alpha * t ^ 2 + (-15405979 / 3000) * alpha * t ^ 4 + (-578776493051 / 7200000) * alpha * t ^ 6 + (352146188621 / 7200000) * alpha * t ^ 8 + (5491689869 / 4800000) * alpha * t ^ 10 + (15849352607 / 43200000) * alpha * t ^ 12 + (-81909871 / 2160000) * alpha * t ^ 14 + (188344901 / 8640000) * alpha * t ^ 18 + (-58977559 / 1600000) * alpha * t ^ 20 + (-54728 / 25) * alpha * c * t ^ 2 + (4730842 / 1125) * alpha * c * t ^ 4 + (-3334340203 / 1350000) * alpha * c * t ^ 6 + (1398850411 / 2700000) * alpha * c * t ^ 8 + (156786859 / 900000) * alpha * c * t ^ 10 + (-482036179 / 1800000) * alpha * c * t ^ 12 + (3575447 / 168750) * alpha * c * t ^ 14 + (-428123 / 2700000) * alpha * c * t ^ 18 + (-74003 / 360000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_10, v48_11, v48_12, v48_20, v48_21, v48_22, v48_30, v48_31, v48_32, v48_40, v48_41, v48_42]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22, phase48_30, phase48_31, phase48_32, phase48_40, phase48_41, phase48_42]
  try simp only [star_one, star_neg]
  linear_combination ((27364 / 75) * t ^ 2 + (-535048 / 1125) * t ^ 4 + (184899869 / 675000) * t ^ 6 + (797785913 / 10800000) * t ^ 8 + (-16695233 / 120000) * t ^ 10 + (-476710267 / 12960000) * t ^ 12 + (337811449 / 16200000) * t ^ 14 + (24245237 / 8100000) * t ^ 18 + (208358807 / 108000000) * t ^ 20 + (-27364 / 225) * c * t ^ 2 + (179258 / 1125) * c * t ^ 4 + (-176434691 / 675000) * c * t ^ 6 + (773150233 / 5400000) * c * t ^ 8 + (270635393 / 2700000) * c * t ^ 10 + (-376028131 / 10800000) * c * t ^ 12 + (-1055819 / 168750) * c * t ^ 14 + (-185177 / 300000) * c * t ^ 18 + (-6803 / 2160000) * c * t ^ 20 + (-54728 / 225) * c ^ 2 * t ^ 2 + (71158 / 225) * c ^ 2 * t ^ 4 + (-1410863 / 112500) * c ^ 2 * t ^ 6 + (-32416819 / 506250) * c ^ 2 * t ^ 8 + (-190807 / 112500) * c ^ 2 * t ^ 10 + (-55454 / 253125) * c ^ 2 * t ^ 12 + (-21547 / 759375) * c ^ 2 * t ^ 14 + (-59812 / 759375) * c ^ 2 * t ^ 18 + (1168 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((109456 / 225) * t ^ 2 + (-160552 / 375) * t ^ 4 + (-23203613 / 75000) * t ^ 6 + (17878241 / 67500) * t ^ 8 + (8331161 / 1350000) * t ^ 10 + (-4479611 / 1012500) * t ^ 12 + (180976 / 253125) * t ^ 14 + (879811 / 4050000) * t ^ 18 + (2336 / 1265625) * t ^ 20 + (-109456 / 225) * alpha * t ^ 2 + (920824 / 1125) * alpha * t ^ 4 + (-272736571 / 675000) * alpha * t ^ 6 + (6365641 / 112500) * alpha * t ^ 8 + (-8013593 / 1350000) * alpha * t ^ 10 + (4307323 / 1012500) * alpha * t ^ 12 + (131536 / 253125) * alpha * t ^ 14 + (408637 / 4050000) * alpha * t ^ 18 + (-2336 / 1265625) * alpha * t ^ 20) * c_sq
theorem v49_43 (t : ℂ) : (momentPoly 49 z49 4 3).eval t = ((18582823 / 10) * t + (-52392879 / 10) * t ^ 3 + (25205117803 / 5000) * t ^ 5 + (-43199550811 / 24000) * t ^ 7 + (1753264632171 / 8000000) * t ^ 9 + (-1343606190659 / 12000000) * t ^ 11 + (3242220693887 / 144000000) * t ^ 13 + (223588634123 / 18000000) * t ^ 15 + (-79820983511 / 48000000) * t ^ 17 + (-3193933451 / 108000000) * t ^ 19 + (12609853973 / 144000000) * t ^ 21 + (2249223929 / 48000000) * t ^ 25 + (-2654689 / 10) * c * t + (41004579 / 50) * c * t ^ 3 + (-9344014547 / 10000) * c * t ^ 5 + (3356714585509 / 7200000) * c * t ^ 7 + (-635016220063 / 7200000) * c * t ^ 9 + (151099772003 / 72000000) * c * t ^ 11 + (45295331431 / 216000000) * c * t ^ 13 + (-11599849309 / 18000000) * c * t ^ 15 + (575964001 / 18000000) * c * t ^ 17 + (-297780313 / 8000000) * c * t ^ 19 + (1292286881 / 72000000) * c * t ^ 21 + (33719257 / 18000000) * c * t ^ 25 + (-18582823 / 30) * alpha * t + (69064457 / 50) * alpha * t ^ 3 + (-10081297523 / 15000) * alpha * t ^ 5 + (-239568379523 / 600000) * alpha * t ^ 7 + (1703911066801 / 4800000) * alpha * t ^ 9 + (-625478936869 / 36000000) * alpha * t ^ 11 + (-17994286517087 / 432000000) * alpha * t ^ 13 + (707190653477 / 54000000) * alpha * t ^ 15 + (182048246341 / 432000000) * alpha * t ^ 17 + (-61246859261 / 324000000) * alpha * t ^ 19 + (-1625934581 / 432000000) * alpha * t ^ 21 + (32283030271 / 1296000000) * alpha * t ^ 25 + (-2654689 / 10) * alpha * c * t + (33180147 / 50) * alpha * c * t ^ 3 + (-4954711347 / 10000) * alpha * c * t ^ 5 + (442390383541 / 7200000) * alpha * c * t ^ 7 + (1110696636661 / 36000000) * alpha * c * t ^ 9 + (121494759473 / 24000000) * alpha * c * t ^ 11 + (-15293842403 / 72000000) * alpha * c * t ^ 13 + (212973499 / 2000000) * alpha * c * t ^ 15 + (229760609 / 18000000) * alpha * c * t ^ 17 + (-6876305683 / 216000000) * alpha * c * t ^ 19 + (1253025329 / 72000000) * alpha * c * t ^ 21 + (-1534837 / 54000000) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_03, v48_10, v48_11, v48_12, v48_13, v48_20, v48_21, v48_22, v48_23, v48_30, v48_31, v48_32, v48_33, v48_40, v48_41, v48_42, v48_43]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23, phase48_30, phase48_31, phase48_32, phase48_33, phase48_40, phase48_41, phase48_42, phase48_43]
  try simp only [star_one, star_neg]
  linear_combination ((1426887 / 100) * t ^ 3 + (-368892859 / 30000) * t ^ 5 + (-14895419287 / 1600000) * t ^ 7 + (77342304913 / 72000000) * t ^ 9 + (841382937559 / 144000000) * t ^ 11 + (16395899449 / 16000000) * t ^ 13 + (-88511366611 / 108000000) * t ^ 15 + (4907053847 / 54000000) * t ^ 17 + (6640526491 / 1296000000) * t ^ 19 + (-3227403913 / 432000000) * t ^ 21 + (-1426123621 / 810000000) * t ^ 25 + (-4352117 / 300) * c * t ^ 3 + (2343546313 / 90000) * c * t ^ 5 + (-105848157911 / 8640000) * c * t ^ 7 + (40103363657 / 43200000) * c * t ^ 9 + (-184819576373 / 432000000) * c * t ^ 11 + (13634260891 / 259200000) * c * t ^ 13 + (1304277913 / 64800000) * c * t ^ 15 + (8073989 / 4500000) * c * t ^ 17 + (1379077667 / 777600000) * c * t ^ 19 + (-838141109 / 1296000000) * c * t ^ 21 + (3628027 / 75937500) * c * t ^ 25 + (17864 / 75) * c ^ 2 * t ^ 3 + (-2238821 / 5625) * c ^ 2 * t ^ 5 + (267080297 / 1350000) * c ^ 2 * t ^ 7 + (-244890139 / 6750000) * c ^ 2 * t ^ 9 + (-366797597 / 13500000) * c ^ 2 * t ^ 11 + (440473303 / 13500000) * c ^ 2 * t ^ 13 + (-6812377 / 2531250) * c ^ 2 * t ^ 15 + (5612 / 1265625) * c ^ 2 * t ^ 17 + (2058169 / 40500000) * c ^ 2 * t ^ 19 + (117203 / 2700000) * c ^ 2 * t ^ 21) * alpha_sq + ((-35728 / 25) * t ^ 3 + (4871962 / 1875) * t ^ 5 + (-64585349 / 45000) * t ^ 7 + (11275393 / 62500) * t ^ 9 + (481859617 / 2250000) * t ^ 11 + (-566979049 / 3375000) * t ^ 13 + (8875867 / 562500) * t ^ 15 + (4738 / 16875) * t ^ 17 + (-15926347 / 20250000) * t ^ 19 + (-299357 / 3375000) * t ^ 21 + (-82928 / 6328125) * t ^ 25 + (35728 / 75) * alpha * t ^ 3 + (-2401882 / 5625) * alpha * t ^ 5 + (-178233191 / 675000) * alpha * t ^ 7 + (23313641 / 112500) * alpha * t ^ 9 + (-131719393 / 6750000) * alpha * t ^ 11 + (3629873 / 405000) * alpha * t ^ 13 + (5052823 / 202500) * alpha * t ^ 15 + (203662 / 1265625) * alpha * t ^ 17 + (12958991 / 12150000) * alpha * t ^ 19 + (-1140643 / 10125000) * alpha * t ^ 21 + (82928 / 18984375) * alpha * t ^ 25) * c_sq
theorem v49_44 (t : ℂ) : (momentPoly 49 z49 4 4).eval t = (130079761 + (-1218653312 / 3) * t ^ 2 + (675153987209 / 1500) * t ^ 4 + (-500420300433 / 2500) * t ^ 6 + (3903724640434577 / 144000000) * t ^ 8 + (-87580387542721 / 36000000) * t ^ 10 + (107462928853119 / 80000000) * t ^ 12 + (-40755905117531 / 1080000000) * t ^ 14 + (228739870286551 / 960000000) * t ^ 16 + (947143102499 / 360000000) * t ^ 18 + (-47971982939329 / 6480000000) * t ^ 20 + (-711565133827 / 360000000) * t ^ 22 + (-219017828713 / 172800000) * t ^ 24 + (-321216604913 / 648000000) * t ^ 26 + (332903260973 / 25920000000) * t ^ 32 + (91923936 / 125) * c * t ^ 4 + (-1292962408 / 625) * c * t ^ 6 + (37141554667 / 18750) * c * t ^ 8 + (-392432060143 / 562500) * c * t ^ 10 + (-2932030427 / 703125) * c * t ^ 12 + (1873279285027 / 16875000) * c * t ^ 14 + (-317800988437 / 5625000) * c * t ^ 16 + (847587451 / 2812500) * c * t ^ 18 + (-3115217381 / 8437500) * c * t ^ 20 + (-259343911 / 5625000) * c * t ^ 22 + (-2654773 / 1125000) * c * t ^ 24 + (-175208027 / 1687500) * c * t ^ 26 + (2939272 / 2109375) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z49, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v48_00, v48_01, v48_02, v48_03, v48_04, v48_10, v48_11, v48_12, v48_13, v48_14, v48_20, v48_21, v48_22, v48_23, v48_24, v48_30, v48_31, v48_32, v48_33, v48_34, v48_40, v48_41, v48_42, v48_43, v48_44]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24, phase48_30, phase48_31, phase48_32, phase48_33, phase48_34, phase48_40, phase48_41, phase48_42, phase48_43, phase48_44]
  try simp only [star_one, star_neg]
  linear_combination ((-2058536 / 15) * t ^ 2 + (323963666 / 1125) * t ^ 4 + (-2411915327 / 2500) * t ^ 6 + (29776481796347 / 27000000) * t ^ 8 + (-490480034701 / 5400000) * t ^ 10 + (-13142264499797 / 67500000) * t ^ 12 + (-12216637373867 / 405000000) * t ^ 14 + (617987517677 / 60000000) * t ^ 16 + (4302655199921 / 1620000000) * t ^ 18 + (-3019474469579 / 2430000000) * t ^ 20 + (170244100217 / 810000000) * t ^ 22 + (152892740143 / 540000000) * t ^ 24 + (-187887530417 / 4860000000) * t ^ 26 + (-6609169511 / 4050000000) * t ^ 32 + (2058536 / 45) * c * t ^ 2 + (-94730974 / 1125) * c * t ^ 4 + (62087309 / 3750) * c * t ^ 6 + (1734190846657 / 27000000) * c * t ^ 8 + (-2827326387251 / 54000000) * c * t ^ 10 + (-416140478357 / 270000000) * c * t ^ 12 + (21338332097683 / 1620000000) * c * t ^ 14 + (-979501301507 / 810000000) * c * t ^ 16 + (-166300291447 / 540000000) * c * t ^ 18 + (267475374617 / 2430000000) * c * t ^ 20 + (-145142657 / 12000000) * c * t ^ 22 + (-3926323 / 810000000) * c * t ^ 24 + (-7334679707 / 972000000) * c * t ^ 26 + (1804487 / 3037500000) * c * t ^ 32 + (4117072 / 45) * c ^ 2 * t ^ 2 + (-229232692 / 1125) * c ^ 2 * t ^ 4 + (715313066 / 5625) * c ^ 2 * t ^ 6 + (-27011205311 / 6750000) * c ^ 2 * t ^ 8 + (-180815377573 / 20250000) * c ^ 2 * t ^ 10 + (-323321933483 / 202500000) * c ^ 2 * t ^ 12 + (-25009648313 / 202500000) * c ^ 2 * t ^ 14 + (-1616080489 / 50625000) * c ^ 2 * t ^ 16 + (-668260483 / 151875000) * c ^ 2 * t ^ 18 + (8346674219 / 607500000) * c ^ 2 * t ^ 20 + (-3943059719 / 607500000) * c ^ 2 * t ^ 22 + (116741 / 3037500) * c ^ 2 * t ^ 24 + (-4520077 / 91125000) * c ^ 2 * t ^ 26 + (170528 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((-16468288 / 45) * t ^ 2 + (978213392 / 1125) * t ^ 4 + (-1230408664 / 1875) * t ^ 6 + (247738990739 / 1687500) * t ^ 8 + (-1773777013 / 1687500) * t ^ 10 + (85293125909 / 16875000) * t ^ 12 + (61308663277 / 50625000) * t ^ 14 + (-1191964793 / 4218750) * t ^ 16 + (46144999 / 2109375) * t ^ 18 + (-206007623 / 6075000) * t ^ 20 + (113911889 / 5625000) * t ^ 22 + (207811 / 6328125) * t ^ 24 + (28211467 / 18984375) * t ^ 26 + (-682112 / 94921875) * t ^ 32) * c_sq
#print axioms v49_00
#print axioms v49_11
#print axioms v49_22
#print axioms v49_33
#print axioms v49_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v50_02 (t : ℂ) : (momentPoly 50 z50 0 2).eval t = ((-4787 / 600) * t ^ 2 + (3859 / 600) * t ^ 4 + (-14 / 75) * c * t ^ 2 + (-2 / 75) * c * t ^ 4 + (351 / 200) * alpha * t ^ 2 + (-1981 / 600) * alpha * t ^ 4 + (14 / 225) * alpha * c * t ^ 2 + (2 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02]
  try simp only [phase48_00, phase48_01, phase48_02]
  try simp only [star_one, star_neg]
  linear_combination ((7 / 450) * t ^ 2 + (-2 / 225) * c * t ^ 2 + (-1 / 150) * c ^ 2 * t ^ 2) * alpha_sq + ((1 / 75) * t ^ 2 + (1 / 75) * alpha * t ^ 2) * c_sq
theorem v50_03 (t : ℂ) : (momentPoly 50 z50 0 3).eval t = ((-484 / 25) * t ^ 3 + (434 / 25) * t ^ 5 + 2 * t ^ 9 + (-43 / 250) * c * t ^ 3 + (173 / 750) * c * t ^ 5 + (142 / 1125) * c * t ^ 9 + (10777 / 1500) * alpha * t ^ 3 + (-52163 / 3000) * alpha * t ^ 5 + (39091 / 9000) * alpha * t ^ 9 + (-146 / 75) * alpha * c * t ^ 3 + (146 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_03]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03]
  try simp only [star_one, star_neg]
  linear_combination ((-779 / 6000) * t ^ 3 + (-3733 / 6000) * t ^ 5 + (827 / 6000) * c * t ^ 3 + (2407 / 18000) * c * t ^ 5 + (-1 / 125) * c ^ 2 * t ^ 3 + (-1 / 375) * c ^ 2 * t ^ 5) * alpha_sq + ((4 / 125) * alpha * t ^ 3 + (4 / 375) * alpha * t ^ 5) * c_sq
theorem v50_04 (t : ℂ) : (momentPoly 50 z50 0 4).eval t = ((2579833 / 24000) * t ^ 4 + (-1590047 / 20000) * t ^ 6 + (1828523 / 240000) * t ^ 8 + (-7179697 / 180000) * t ^ 10 + (4484849 / 720000) * t ^ 16 + (-1196 / 375) * c * t ^ 4 + (11157 / 1250) * c * t ^ 6 + (-1231 / 1875) * c * t ^ 8 + (-42883 / 11250) * c * t ^ 10 + (292 / 5625) * c * t ^ 16 + (-519059 / 8000) * alpha * t ^ 4 + (11007901 / 60000) * alpha * t ^ 6 + (-32611883 / 240000) * alpha * t ^ 8 + (757819 / 60000) * alpha * t ^ 10 + (1957391 / 720000) * alpha * t ^ 16 + (-7772 / 1125) * alpha * c * t ^ 4 + (8839 / 1250) * alpha * c * t ^ 6 + (4609 / 5625) * alpha * c * t ^ 8 + (-18883 / 33750) * alpha * c * t ^ 10 + (292 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_03, v49_04]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04]
  try simp only [star_one, star_neg]
  linear_combination ((236 / 1125) * t ^ 4 + (61159 / 45000) * t ^ 6 + (41099 / 5000) * t ^ 8 + (28483 / 67500) * t ^ 10 + (-674 / 1125) * c * t ^ 4 + (1639 / 625) * c * t ^ 6 + (271 / 7500) * c * t ^ 8 + (-46163 / 67500) * c * t ^ 10 + (146 / 375) * c ^ 2 * t ^ 4 + (-734 / 1875) * c ^ 2 * t ^ 6 + (-2 / 5625) * c ^ 2 * t ^ 8) * alpha_sq + ((-2203 / 2250) * t ^ 4 + (1407 / 1250) * t ^ 6 + (-4 / 1875) * t ^ 8 + (284 / 5625) * t ^ 10 + (-1301 / 2250) * alpha * t ^ 4 + (1619 / 3750) * alpha * t ^ 6 + (4 / 1875) * alpha * t ^ 8 + (-284 / 5625) * alpha * t ^ 10) * c_sq
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
theorem v50_12 (t : ℂ) : (momentPoly 50 z50 1 2).eval t = ((396 / 5) * t + (-5839 / 75) * t ^ 3 + (187 / 75) * t ^ 5 + (-33 / 5) * c * t + (439 / 60) * c * t ^ 3 + (-311 / 300) * c * t ^ 5 + (132 / 5) * alpha * t + (-519 / 25) * alpha * t ^ 3 + (-109 / 25) * alpha * t ^ 5 + (33 / 5) * alpha * c * t + (-5417 / 900) * alpha * c * t ^ 3 + (-47 / 180) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_10, v49_11, v49_12]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12]
  try simp only [star_one, star_neg]
  linear_combination ((779 / 18000) * t ^ 3 + (3733 / 18000) * t ^ 5 + (-827 / 18000) * c * t ^ 3 + (-2407 / 54000) * c * t ^ 5 + (1 / 375) * c ^ 2 * t ^ 3 + (1 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-2 / 125) * t ^ 3 + (-2 / 375) * t ^ 5 + (-2 / 375) * alpha * t ^ 3 + (-2 / 1125) * alpha * t ^ 5) * c_sq
theorem v50_13 (t : ℂ) : (momentPoly 50 z50 1 3).eval t = ((-234563 / 200) * t ^ 2 + (100357 / 50) * t ^ 4 + (-209631 / 250) * t ^ 6 + (-129 / 40) * t ^ 10 + (-686 / 25) * c * t ^ 2 + (11983 / 500) * c * t ^ 4 + (1587 / 1000) * c * t ^ 6 + (863 / 1000) * c * t ^ 10 + (51597 / 200) * alpha * t ^ 2 + (-6991 / 10) * alpha * t ^ 4 + (107329 / 250) * alpha * t ^ 6 + (35 / 8) * alpha * t ^ 10 + (686 / 75) * alpha * c * t ^ 2 + (-37549 / 4500) * alpha * c * t ^ 4 + (13 / 3000) * alpha * c * t ^ 6 + (-4189 / 9000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_03, v49_10, v49_11, v49_12, v49_13]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13]
  try simp only [star_one, star_neg]
  linear_combination ((343 / 150) * t ^ 2 + (-31873 / 18000) * t ^ 4 + (1427 / 5000) * t ^ 6 + (-28483 / 270000) * t ^ 10 + (-98 / 75) * c * t ^ 2 + (9383 / 9000) * c * t ^ 4 + (-4319 / 10000) * c * t ^ 6 + (46163 / 270000) * c * t ^ 10 + (-49 / 50) * c ^ 2 * t ^ 2 + (4369 / 6000) * c ^ 2 * t ^ 4 + (293 / 2000) * c ^ 2 * t ^ 6) * alpha_sq + ((49 / 25) * t ^ 2 + (-5027 / 4500) * t ^ 4 + (-1481 / 2500) * t ^ 6 + (71 / 5625) * t ^ 10 + (49 / 25) * alpha * t ^ 2 + (-8531 / 4500) * alpha * t ^ 4 + (1397 / 7500) * alpha * t ^ 6 + (71 / 5625) * alpha * t ^ 10) * c_sq
theorem v50_14 (t : ℂ) : (momentPoly 50 z50 1 4).eval t = ((-93896 / 25) * t ^ 3 + (4253264 / 625) * t ^ 5 + (-5534864 / 1875) * t ^ 7 + (567686 / 1875) * t ^ 9 + (-2280256 / 5625) * t ^ 11 + (29014 / 5625) * t ^ 17 + (-4171 / 125) * c * t ^ 3 + (4425479 / 90000) * c * t ^ 5 + (57673 / 5000) * c * t ^ 7 + (-566959 / 180000) * c * t ^ 9 + (-1051153 / 45000) * c * t ^ 11 + (10369 / 180000) * c * t ^ 17 + (1045369 / 750) * alpha * t ^ 3 + (-26315054 / 5625) * alpha * t ^ 5 + (403318 / 125) * alpha * t ^ 7 + (17488931 / 22500) * alpha * t ^ 9 + (-928369 / 1250) * alpha * t ^ 11 + (-2427 / 500) * alpha * t ^ 17 + (-28324 / 75) * alpha * c * t ^ 3 + (4155217 / 5625) * alpha * c * t ^ 5 + (-2057254 / 5625) * alpha * c * t ^ 7 + (30871 / 5625) * alpha * c * t ^ 9 + (-3536 / 16875) * alpha * c * t ^ 11 + (-10066 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_03, v49_04, v49_10, v49_11, v49_12, v49_13, v49_14]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14]
  try simp only [star_one, star_neg]
  linear_combination ((-75563 / 3000) * t ^ 3 + (-67810487 / 720000) * t ^ 5 + (2224889 / 24000) * t ^ 7 + (97675691 / 7200000) * t ^ 9 + (-113427 / 200000) * t ^ 11 + (-3890063 / 21600000) * t ^ 17 + (80219 / 3000) * c * t ^ 3 + (-5557531 / 2160000) * c * t ^ 5 + (-19705861 / 1080000) * c * t ^ 7 + (-57510017 / 21600000) * c * t ^ 9 + (906667 / 1800000) * c * t ^ 11 + (2081581 / 64800000) * c * t ^ 17 + (-194 / 125) * c ^ 2 * t ^ 3 + (27803 / 33750) * c ^ 2 * t ^ 5 + (1123 / 2250) * c ^ 2 * t ^ 7 + (1448 / 28125) * c ^ 2 * t ^ 9 + (1784 / 28125) * c ^ 2 * t ^ 11 + (146 / 84375) * c ^ 2 * t ^ 17) * alpha_sq + ((952 / 1875) * t ^ 5 + (32 / 1875) * t ^ 7 + (-584 / 1875) * t ^ 9 + (-16 / 75) * t ^ 11 + (776 / 125) * alpha * t ^ 3 + (-2864 / 625) * alpha * t ^ 5 + (-1453 / 5625) * alpha * t ^ 7 + (-26 / 9375) * alpha * t ^ 9 + (-14209 / 28125) * alpha * t ^ 11 + (584 / 84375) * alpha * t ^ 17) * c_sq
theorem v50_20 (t : ℂ) : (momentPoly 50 z50 2 0).eval t = ((-4787 / 600) * t ^ 2 + (3859 / 600) * t ^ 4 + (-14 / 75) * c * t ^ 2 + (-2 / 75) * c * t ^ 4 + (-351 / 200) * alpha * t ^ 2 + (1981 / 600) * alpha * t ^ 4 + (-14 / 225) * alpha * c * t ^ 2 + (-2 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_10, v49_20]
  try simp only [phase48_00, phase48_10, phase48_20]
  try simp only [star_one, star_neg]
  linear_combination ((7 / 450) * t ^ 2 + (-2 / 225) * c * t ^ 2 + (-1 / 150) * c ^ 2 * t ^ 2) * alpha_sq + ((1 / 75) * t ^ 2 + (-1 / 75) * alpha * t ^ 2) * c_sq
theorem v50_21 (t : ℂ) : (momentPoly 50 z50 2 1).eval t = ((396 / 5) * t + (-5839 / 75) * t ^ 3 + (187 / 75) * t ^ 5 + (-33 / 5) * c * t + (439 / 60) * c * t ^ 3 + (-311 / 300) * c * t ^ 5 + (-132 / 5) * alpha * t + (519 / 25) * alpha * t ^ 3 + (109 / 25) * alpha * t ^ 5 + (-33 / 5) * alpha * c * t + (5417 / 900) * alpha * c * t ^ 3 + (47 / 180) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_10, v49_11, v49_20, v49_21]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21]
  try simp only [star_one, star_neg]
  linear_combination ((779 / 18000) * t ^ 3 + (3733 / 18000) * t ^ 5 + (-827 / 18000) * c * t ^ 3 + (-2407 / 54000) * c * t ^ 5 + (1 / 375) * c ^ 2 * t ^ 3 + (1 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-2 / 125) * t ^ 3 + (-2 / 375) * t ^ 5 + (2 / 375) * alpha * t ^ 3 + (2 / 1125) * alpha * t ^ 5) * c_sq
theorem v50_22 (t : ℂ) : (momentPoly 50 z50 2 2).eval t = (4950 + (-44296 / 5) * t ^ 2 + (23169647 / 6000) * t ^ 4 + (139057 / 3000) * t ^ 6 + (145679 / 6000) * t ^ 8 + (4088 / 1125) * c * t ^ 4 + (-1168 / 375) * c * t ^ 6 + (-584 / 1125) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_10, v49_11, v49_12, v49_20, v49_21, v49_22]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22]
  try simp only [star_one, star_neg]
  linear_combination ((-686 / 225) * t ^ 2 + (30929 / 13500) * t ^ 4 + (-112531 / 135000) * t ^ 6 + (-41099 / 15000) * t ^ 8 + (392 / 225) * c * t ^ 2 + (-1607 / 1350) * c * t ^ 4 + (-2237 / 7500) * c * t ^ 6 + (-271 / 22500) * c * t ^ 8 + (98 / 75) * c ^ 2 * t ^ 2 + (-1651 / 1500) * c ^ 2 * t ^ 4 + (-1459 / 22500) * c ^ 2 * t ^ 6 + (2 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-392 / 75) * t ^ 2 + (1049 / 225) * t ^ 4 + (-11 / 1875) * t ^ 6 + (-8 / 5625) * t ^ 8) * c_sq
theorem v50_23 (t : ℂ) : (momentPoly 50 z50 2 3).eval t = ((58216 / 5) * t + (-566383 / 25) * t ^ 3 + (690859937 / 60000) * t ^ 5 + (-74127133 / 120000) * t ^ 7 + (162199 / 960) * t ^ 9 + (-1190069 / 360000) * t ^ 11 + (-11414059 / 360000) * t ^ 13 + (-14554 / 15) * c * t + (42583 / 20) * c * t ^ 3 + (-128714873 / 90000) * c * t ^ 5 + (12290219 / 45000) * c * t ^ 7 + (-174443 / 30000) * c * t ^ 9 + (5639 / 3750) * c * t ^ 11 + (5293 / 5625) * c * t ^ 13 + (58216 / 15) * alpha * t + (-151029 / 25) * alpha * t ^ 3 + (157201361 / 180000) * alpha * t ^ 5 + (497762803 / 360000) * alpha * t ^ 7 + (-11113703 / 120000) * alpha * t ^ 9 + (-11227319 / 360000) * alpha * t ^ 11 + (1360927 / 40000) * alpha * t ^ 13 + (14554 / 15) * alpha * c * t + (-525449 / 300) * alpha * c * t ^ 3 + (12522917 / 18000) * alpha * c * t ^ 5 + (3730133 / 45000) * alpha * c * t ^ 7 + (411713 / 90000) * alpha * c * t ^ 9 + (-4283 / 6750) * alpha * c * t ^ 11 + (3653 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_03, v49_10, v49_11, v49_12, v49_13, v49_20, v49_21, v49_22, v49_23]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23]
  try simp only [star_one, star_neg]
  linear_combination ((75563 / 6000) * t ^ 3 + (4140587 / 90000) * t ^ 5 + (-1047059 / 22500) * t ^ 7 + (-1528547 / 112500) * t ^ 9 + (-463393 / 1350000) * t ^ 11 + (2236169 / 1350000) * t ^ 13 + (-80219 / 6000) * c * t ^ 3 + (225847 / 90000) * c * t ^ 5 + (764843 / 90000) * c * t ^ 7 + (781853 / 1350000) * c * t ^ 9 + (102163 / 675000) * c * t ^ 11 + (46163 / 2025000) * c * t ^ 13 + (97 / 125) * c ^ 2 * t ^ 3 + (-74351 / 135000) * c ^ 2 * t ^ 5 + (-9179 / 90000) * c ^ 2 * t ^ 7 + (289 / 45000) * c ^ 2 * t ^ 9 + (-1423 / 30000) * c ^ 2 * t ^ 11) * alpha_sq + ((-582 / 125) * t ^ 3 + (82463 / 22500) * t ^ 5 + (19819 / 45000) * t ^ 7 + (-1484 / 9375) * t ^ 9 + (18481 / 75000) * t ^ 11 + (142 / 28125) * t ^ 13 + (-194 / 125) * alpha * t ^ 3 + (7123 / 13500) * alpha * t ^ 5 + (90283 / 135000) * alpha * t ^ 7 + (484 / 3125) * alpha * t ^ 9 + (10481 / 225000) * alpha * t ^ 11 + (142 / 84375) * alpha * t ^ 13) * c_sq
theorem v50_24 (t : ℂ) : (momentPoly 50 z50 2 4).eval t = ((-68267407 / 300) * t ^ 2 + (118232639 / 200) * t ^ 4 + (-1195023378367 / 2400000) * t ^ 6 + (309360110621 / 2400000) * t ^ 8 + (22759167499 / 4800000) * t ^ 10 + (14191314487 / 14400000) * t ^ 12 + (-381092873 / 1200000) * t ^ 14 + (-437290619 / 14400000) * t ^ 18 + (93575707 / 14400000) * t ^ 20 + (-399308 / 75) * c * t ^ 2 + (1243438 / 125) * c * t ^ 4 + (-697182821 / 150000) * c * t ^ 6 + (-516307 / 30000) * c * t ^ 8 + (64061603 / 180000) * c * t ^ 10 + (-266603767 / 900000) * c * t ^ 12 + (-3422153 / 168750) * c * t ^ 14 + (-7301683 / 2700000) * c * t ^ 18 + (17197 / 180000) * c * t ^ 20 + (5005611 / 100) * alpha * t ^ 2 + (-35253713 / 200) * alpha * t ^ 4 + (1415498382163 / 7200000) * alpha * t ^ 6 + (-494257161049 / 7200000) * alpha * t ^ 8 + (-4901265391 / 14400000) * alpha * t ^ 10 + (-59062180523 / 43200000) * alpha * t ^ 12 + (-230925803 / 3600000) * alpha * t ^ 14 + (-616404043 / 14400000) * alpha * t ^ 18 + (1777587137 / 43200000) * alpha * t ^ 20 + (399308 / 225) * alpha * c * t ^ 2 + (-431546 / 125) * alpha * c * t ^ 4 + (872159333 / 450000) * alpha * c * t ^ 6 + (-29268173 / 90000) * alpha * c * t ^ 8 + (-19724833 / 180000) * alpha * c * t ^ 10 + (514504631 / 2700000) * alpha * c * t ^ 12 + (-272873 / 18750) * alpha * c * t ^ 14 + (-173989 / 900000) * alpha * c * t ^ 18 + (78803 / 540000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_03, v49_04, v49_10, v49_11, v49_12, v49_13, v49_14, v49_20, v49_21, v49_22, v49_23, v49_24]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24]
  try simp only [star_one, star_neg]
  linear_combination ((99827 / 225) * t ^ 2 + (-254984 / 375) * t ^ 4 + (912368951 / 2700000) * t ^ 6 + (-33271271 / 1200000) * t ^ 8 + (-8183089 / 300000) * t ^ 10 + (-11537199667 / 324000000) * t ^ 12 + (1065420541 / 81000000) * t ^ 14 + (83837059 / 81000000) * t ^ 18 + (28376351 / 12000000) * t ^ 20 + (-57044 / 225) * c * t ^ 2 + (150128 / 375) * c * t ^ 4 + (-269483971 / 900000) * c * t ^ 6 + (579405773 / 5400000) * c * t ^ 8 + (93191903 / 1080000) * c * t ^ 10 + (-484737707 / 10800000) * c * t ^ 12 + (-208081 / 37500) * c * t ^ 14 + (-158959 / 360000) * c * t ^ 18 + (-16403 / 2160000) * c * t ^ 20 + (-14261 / 75) * c ^ 2 * t ^ 2 + (34952 / 125) * c ^ 2 * t ^ 4 + (-51958519 / 1350000) * c ^ 2 * t ^ 6 + (-104729311 / 2025000) * c ^ 2 * t ^ 8 + (-1020863 / 1350000) * c ^ 2 * t ^ 10 + (-2459 / 187500) * c ^ 2 * t ^ 12 + (-19211 / 562500) * c ^ 2 * t ^ 14 + (-8291 / 140625) * c ^ 2 * t ^ 18 + (292 / 1265625) * c ^ 2 * t ^ 20) * alpha_sq + ((28522 / 75) * t ^ 2 + (-160864 / 375) * t ^ 4 + (-47227927 / 300000) * t ^ 6 + (95030101 / 450000) * t ^ 8 + (5584633 / 1800000) * t ^ 10 + (-29492159 / 6750000) * t ^ 12 + (83096 / 140625) * t ^ 14 + (528727 / 3000000) * t ^ 18 + (584 / 421875) * t ^ 20 + (28522 / 75) * alpha * t ^ 2 + (-272992 / 375) * alpha * t ^ 4 + (1104092401 / 2700000) * alpha * t ^ 6 + (-76603841 / 1350000) * alpha * t ^ 8 + (37529 / 8000) * alpha * t ^ 10 + (-9479573 / 2250000) * alpha * t ^ 12 + (-141352 / 421875) * alpha * t ^ 14 + (-1683697 / 27000000) * alpha * t ^ 18 + (584 / 421875) * alpha * t ^ 20) * c_sq
theorem v50_30 (t : ℂ) : (momentPoly 50 z50 3 0).eval t = ((-484 / 25) * t ^ 3 + (434 / 25) * t ^ 5 + 2 * t ^ 9 + (-43 / 250) * c * t ^ 3 + (173 / 750) * c * t ^ 5 + (142 / 1125) * c * t ^ 9 + (-10777 / 1500) * alpha * t ^ 3 + (52163 / 3000) * alpha * t ^ 5 + (-39091 / 9000) * alpha * t ^ 9 + (146 / 75) * alpha * c * t ^ 3 + (-146 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_10, v49_20, v49_30]
  try simp only [phase48_00, phase48_10, phase48_20, phase48_30]
  try simp only [star_one, star_neg]
  linear_combination ((-779 / 6000) * t ^ 3 + (-3733 / 6000) * t ^ 5 + (827 / 6000) * c * t ^ 3 + (2407 / 18000) * c * t ^ 5 + (-1 / 125) * c ^ 2 * t ^ 3 + (-1 / 375) * c ^ 2 * t ^ 5) * alpha_sq + ((-4 / 125) * alpha * t ^ 3 + (-4 / 375) * alpha * t ^ 5) * c_sq
theorem v50_31 (t : ℂ) : (momentPoly 50 z50 3 1).eval t = ((-234563 / 200) * t ^ 2 + (100357 / 50) * t ^ 4 + (-209631 / 250) * t ^ 6 + (-129 / 40) * t ^ 10 + (-686 / 25) * c * t ^ 2 + (11983 / 500) * c * t ^ 4 + (1587 / 1000) * c * t ^ 6 + (863 / 1000) * c * t ^ 10 + (-51597 / 200) * alpha * t ^ 2 + (6991 / 10) * alpha * t ^ 4 + (-107329 / 250) * alpha * t ^ 6 + (-35 / 8) * alpha * t ^ 10 + (-686 / 75) * alpha * c * t ^ 2 + (37549 / 4500) * alpha * c * t ^ 4 + (-13 / 3000) * alpha * c * t ^ 6 + (4189 / 9000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_10, v49_11, v49_20, v49_21, v49_30, v49_31]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21, phase48_30, phase48_31]
  try simp only [star_one, star_neg]
  linear_combination ((343 / 150) * t ^ 2 + (-31873 / 18000) * t ^ 4 + (1427 / 5000) * t ^ 6 + (-28483 / 270000) * t ^ 10 + (-98 / 75) * c * t ^ 2 + (9383 / 9000) * c * t ^ 4 + (-4319 / 10000) * c * t ^ 6 + (46163 / 270000) * c * t ^ 10 + (-49 / 50) * c ^ 2 * t ^ 2 + (4369 / 6000) * c ^ 2 * t ^ 4 + (293 / 2000) * c ^ 2 * t ^ 6) * alpha_sq + ((49 / 25) * t ^ 2 + (-5027 / 4500) * t ^ 4 + (-1481 / 2500) * t ^ 6 + (71 / 5625) * t ^ 10 + (-49 / 25) * alpha * t ^ 2 + (8531 / 4500) * alpha * t ^ 4 + (-1397 / 7500) * alpha * t ^ 6 + (-71 / 5625) * alpha * t ^ 10) * c_sq
theorem v50_32 (t : ℂ) : (momentPoly 50 z50 3 2).eval t = ((58216 / 5) * t + (-566383 / 25) * t ^ 3 + (690859937 / 60000) * t ^ 5 + (-74127133 / 120000) * t ^ 7 + (162199 / 960) * t ^ 9 + (-1190069 / 360000) * t ^ 11 + (-11414059 / 360000) * t ^ 13 + (-14554 / 15) * c * t + (42583 / 20) * c * t ^ 3 + (-128714873 / 90000) * c * t ^ 5 + (12290219 / 45000) * c * t ^ 7 + (-174443 / 30000) * c * t ^ 9 + (5639 / 3750) * c * t ^ 11 + (5293 / 5625) * c * t ^ 13 + (-58216 / 15) * alpha * t + (151029 / 25) * alpha * t ^ 3 + (-157201361 / 180000) * alpha * t ^ 5 + (-497762803 / 360000) * alpha * t ^ 7 + (11113703 / 120000) * alpha * t ^ 9 + (11227319 / 360000) * alpha * t ^ 11 + (-1360927 / 40000) * alpha * t ^ 13 + (-14554 / 15) * alpha * c * t + (525449 / 300) * alpha * c * t ^ 3 + (-12522917 / 18000) * alpha * c * t ^ 5 + (-3730133 / 45000) * alpha * c * t ^ 7 + (-411713 / 90000) * alpha * c * t ^ 9 + (4283 / 6750) * alpha * c * t ^ 11 + (-3653 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_10, v49_11, v49_12, v49_20, v49_21, v49_22, v49_30, v49_31, v49_32]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22, phase48_30, phase48_31, phase48_32]
  try simp only [star_one, star_neg]
  linear_combination ((75563 / 6000) * t ^ 3 + (4140587 / 90000) * t ^ 5 + (-1047059 / 22500) * t ^ 7 + (-1528547 / 112500) * t ^ 9 + (-463393 / 1350000) * t ^ 11 + (2236169 / 1350000) * t ^ 13 + (-80219 / 6000) * c * t ^ 3 + (225847 / 90000) * c * t ^ 5 + (764843 / 90000) * c * t ^ 7 + (781853 / 1350000) * c * t ^ 9 + (102163 / 675000) * c * t ^ 11 + (46163 / 2025000) * c * t ^ 13 + (97 / 125) * c ^ 2 * t ^ 3 + (-74351 / 135000) * c ^ 2 * t ^ 5 + (-9179 / 90000) * c ^ 2 * t ^ 7 + (289 / 45000) * c ^ 2 * t ^ 9 + (-1423 / 30000) * c ^ 2 * t ^ 11) * alpha_sq + ((-582 / 125) * t ^ 3 + (82463 / 22500) * t ^ 5 + (19819 / 45000) * t ^ 7 + (-1484 / 9375) * t ^ 9 + (18481 / 75000) * t ^ 11 + (142 / 28125) * t ^ 13 + (194 / 125) * alpha * t ^ 3 + (-7123 / 13500) * alpha * t ^ 5 + (-90283 / 135000) * alpha * t ^ 7 + (-484 / 3125) * alpha * t ^ 9 + (-10481 / 225000) * alpha * t ^ 11 + (-142 / 84375) * alpha * t ^ 13) * c_sq
theorem v50_33 (t : ℂ) : (momentPoly 50 z50 3 3).eval t = (727700 + (-9668958 / 5) * t ^ 2 + (208526823 / 125) * t ^ 4 + (-66840109207 / 150000) * t ^ 6 + (-1029417313 / 150000) * t ^ 8 + (-1855774033 / 200000) * t ^ 10 + (-17504611 / 450000) * t ^ 12 + (-24524601 / 100000) * t ^ 14 + (25440199 / 1800000) * t ^ 18 + (196224 / 125) * c * t ^ 4 + (-5505977 / 1875) * c * t ^ 6 + (4863101 / 3750) * c * t ^ 8 + (71511 / 1250) * c * t ^ 10 + (-528331 / 11250) * c * t ^ 12 + (73939 / 1250) * c * t ^ 14 + (568 / 1125) * c * t ^ 18) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_03, v49_10, v49_11, v49_12, v49_13, v49_20, v49_21, v49_22, v49_23, v49_30, v49_31, v49_32, v49_33]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23, phase48_30, phase48_31, phase48_32, phase48_33]
  try simp only [star_one, star_neg]
  linear_combination ((-99827 / 150) * t ^ 2 + (123716 / 125) * t ^ 4 + (-78497159 / 112500) * t ^ 6 + (-91685873 / 120000) * t ^ 8 + (1799919727 / 1800000) * t ^ 10 + (51285893 / 5400000) * t ^ 12 + (-10552043 / 1000000) * t ^ 14 + (9029839 / 5062500) * t ^ 18 + (28522 / 75) * c * t ^ 2 + (-12856 / 25) * c * t ^ 4 + (2421497 / 180000) * c * t ^ 6 + (29542563 / 200000) * c * t ^ 8 + (-11146343 / 600000) * c * t ^ 10 + (-2164837 / 216000) * c * t ^ 12 + (34068253 / 5400000) * c * t ^ 14 + (14261 / 50) * c ^ 2 * t ^ 2 + (-59436 / 125) * c ^ 2 * t ^ 4 + (147371887 / 900000) * c ^ 2 * t ^ 6 + (37110583 / 1350000) * c ^ 2 * t ^ 8 + (1301543 / 900000) * c ^ 2 * t ^ 10 + (-919 / 225000) * c ^ 2 * t ^ 12 + (5843 / 225000) * c ^ 2 * t ^ 14) * alpha_sq + ((-28522 / 25) * t ^ 2 + (50352 / 25) * t ^ 4 + (-195932687 / 225000) * t ^ 6 + (-787637 / 112500) * t ^ 8 + (-447733 / 75000) * t ^ 10 + (10093 / 84375) * t ^ 12 + (5612 / 15625) * t ^ 14 + (-10082 / 421875) * t ^ 18) * c_sq
theorem v50_34 (t : ℂ) : (momentPoly 50 z50 3 4).eval t = ((11296268 / 5) * t + (-163153338 / 25) * t ^ 3 + (12717287523 / 2000) * t ^ 5 + (-26822211331481 / 12000000) * t ^ 7 + (5572597510991 / 24000000) * t ^ 9 + (-2244096544757 / 24000000) * t ^ 11 + (-1648862044711 / 144000000) * t ^ 13 + (18061409221 / 1000000) * t ^ 15 + (-257575395341 / 144000000) * t ^ 17 + (-27751984153 / 216000000) * t ^ 19 + (2276748331 / 28800000) * t ^ 21 + (20967888329 / 432000000) * t ^ 25 + (-2824067 / 15) * c * t + (6133269 / 10) * c * t ^ 3 + (-2190472397 / 3000) * c * t ^ 5 + (268350677563 / 720000) * c * t ^ 7 + (-412537470671 / 6000000) * c * t ^ 9 + (62894509121 / 36000000) * c * t ^ 11 + (-15368490631 / 108000000) * c * t ^ 13 + (-4194552283 / 9000000) * c * t ^ 15 + (148908299 / 9000000) * c * t ^ 17 + (-78569269 / 2400000) * c * t ^ 19 + (211188709 / 12000000) * c * t ^ 21 + (31919257 / 27000000) * c * t ^ 25 + (11296268 / 15) * alpha * t + (-43505694 / 25) * alpha * t ^ 3 + (5132704499 / 6000) * alpha * t ^ 5 + (1295740521001 / 2400000) * alpha * t ^ 7 + (-10608426767419 / 24000000) * alpha * t ^ 9 + (971727700427 / 72000000) * alpha * t ^ 11 + (15867195891481 / 432000000) * alpha * t ^ 13 + (-145423975553 / 9000000) * alpha * t ^ 15 + (-4091802679 / 16000000) * alpha * t ^ 17 + (59618017 / 4800000) * alpha * t ^ 19 + (6474896093 / 144000000) * alpha * t ^ 21 + (-9244681213 / 432000000) * alpha * t ^ 25 + (2824067 / 15) * alpha * c * t + (-25226969 / 50) * alpha * c * t ^ 3 + (250786633 / 600) * alpha * c * t ^ 5 + (-1394131619123 / 18000000) * alpha * c * t ^ 7 + (-75428467879 / 3600000) * alpha * c * t ^ 9 + (-133704550993 / 36000000) * alpha * c * t ^ 11 + (53949991223 / 108000000) * alpha * c * t ^ 13 + (-704676341 / 9000000) * alpha * c * t ^ 15 + (-59909741 / 5400000) * alpha * c * t ^ 17 + (5168708771 / 324000000) * alpha * c * t ^ 19 + (-1097463197 / 108000000) * alpha * c * t ^ 21 + (6934837 / 81000000) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_03, v49_04, v49_10, v49_11, v49_12, v49_13, v49_14, v49_20, v49_21, v49_22, v49_23, v49_24, v49_30, v49_31, v49_32, v49_33, v49_34]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24, phase48_30, phase48_31, phase48_32, phase48_33, phase48_34]
  try simp only [star_one, star_neg]
  linear_combination ((3627803 / 1000) * t ^ 3 + (18423629 / 2000) * t ^ 5 + (-1593518457851 / 72000000) * t ^ 7 + (132514754389 / 72000000) * t ^ 9 + (118554771327 / 16000000) * t ^ 11 + (304977419623 / 432000000) * t ^ 13 + (-89799805663 / 108000000) * t ^ 15 + (21978490379 / 270000000) * t ^ 17 + (44696541143 / 6480000000) * t ^ 19 + (-3940069171 / 720000000) * t ^ 21 + (-1283750117 / 810000000) * t ^ 25 + (-3851339 / 1000) * c * t ^ 3 + (91561159 / 18000) * c * t ^ 5 + (2744599501 / 43200000) * c * t ^ 7 + (-67600117541 / 72000000) * c * t ^ 9 + (-16332939421 / 48000000) * c * t ^ 11 + (-53530251301 / 1296000000) * c * t ^ 13 + (-816287383 / 324000000) * c * t ^ 15 + (374387821 / 202500000) * c * t ^ 17 + (-10498636679 / 6480000000) * c * t ^ 19 + (5211256027 / 6480000000) * c * t ^ 21 + (3369899 / 75937500) * c * t ^ 25 + (27942 / 125) * c ^ 2 * t ^ 3 + (-348157 / 900) * c ^ 2 * t ^ 5 + (2382574303 / 13500000) * c ^ 2 * t ^ 7 + (-143427797 / 9000000) * c ^ 2 * t ^ 9 + (-185745803 / 9000000) * c ^ 2 * t ^ 11 + (162020297 / 6000000) * c ^ 2 * t ^ 13 + (-1791719 / 843750) * c ^ 2 * t ^ 15 + (2528 / 421875) * c ^ 2 * t ^ 17 + (-9407 / 1000000) * c ^ 2 * t ^ 19 + (122003 / 3600000) * c ^ 2 * t ^ 21) * alpha_sq + ((-167652 / 125) * t ^ 3 + (1894913 / 750) * t ^ 5 + (-336947183 / 250000) * t ^ 7 + (43103411 / 375000) * t ^ 9 + (752162807 / 4500000) * t ^ 11 + (-1887400781 / 13500000) * t ^ 13 + (27705701 / 2250000) * t ^ 15 + (252893 / 1406250) * t ^ 17 + (-22449253 / 67500000) * t ^ 19 + (-204233 / 2500000) * t ^ 21 + (-20732 / 2109375) * t ^ 25 + (-55884 / 125) * alpha * t ^ 3 + (1004801 / 2250) * alpha * t ^ 5 + (334450661 / 1350000) * alpha * t ^ 7 + (-248875909 / 1125000) * alpha * t ^ 9 + (-3671893 / 2700000) * alpha * t ^ 11 + (-328204781 / 40500000) * alpha * t ^ 13 + (-124502251 / 6750000) * alpha * t ^ 15 + (-184129 / 1406250) * alpha * t ^ 17 + (-154284133 / 202500000) * alpha * t ^ 19 + (198589 / 2500000) * alpha * t ^ 21 + (-20732 / 6328125) * alpha * t ^ 25) * c_sq
theorem v50_40 (t : ℂ) : (momentPoly 50 z50 4 0).eval t = ((2579833 / 24000) * t ^ 4 + (-1590047 / 20000) * t ^ 6 + (1828523 / 240000) * t ^ 8 + (-7179697 / 180000) * t ^ 10 + (4484849 / 720000) * t ^ 16 + (-1196 / 375) * c * t ^ 4 + (11157 / 1250) * c * t ^ 6 + (-1231 / 1875) * c * t ^ 8 + (-42883 / 11250) * c * t ^ 10 + (292 / 5625) * c * t ^ 16 + (519059 / 8000) * alpha * t ^ 4 + (-11007901 / 60000) * alpha * t ^ 6 + (32611883 / 240000) * alpha * t ^ 8 + (-757819 / 60000) * alpha * t ^ 10 + (-1957391 / 720000) * alpha * t ^ 16 + (7772 / 1125) * alpha * c * t ^ 4 + (-8839 / 1250) * alpha * c * t ^ 6 + (-4609 / 5625) * alpha * c * t ^ 8 + (18883 / 33750) * alpha * c * t ^ 10 + (-292 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_10, v49_20, v49_30, v49_40]
  try simp only [phase48_00, phase48_10, phase48_20, phase48_30, phase48_40]
  try simp only [star_one, star_neg]
  linear_combination ((236 / 1125) * t ^ 4 + (61159 / 45000) * t ^ 6 + (41099 / 5000) * t ^ 8 + (28483 / 67500) * t ^ 10 + (-674 / 1125) * c * t ^ 4 + (1639 / 625) * c * t ^ 6 + (271 / 7500) * c * t ^ 8 + (-46163 / 67500) * c * t ^ 10 + (146 / 375) * c ^ 2 * t ^ 4 + (-734 / 1875) * c ^ 2 * t ^ 6 + (-2 / 5625) * c ^ 2 * t ^ 8) * alpha_sq + ((-2203 / 2250) * t ^ 4 + (1407 / 1250) * t ^ 6 + (-4 / 1875) * t ^ 8 + (284 / 5625) * t ^ 10 + (1301 / 2250) * alpha * t ^ 4 + (-1619 / 3750) * alpha * t ^ 6 + (-4 / 1875) * alpha * t ^ 8 + (284 / 5625) * alpha * t ^ 10) * c_sq
theorem v50_41 (t : ℂ) : (momentPoly 50 z50 4 1).eval t = ((-93896 / 25) * t ^ 3 + (4253264 / 625) * t ^ 5 + (-5534864 / 1875) * t ^ 7 + (567686 / 1875) * t ^ 9 + (-2280256 / 5625) * t ^ 11 + (29014 / 5625) * t ^ 17 + (-4171 / 125) * c * t ^ 3 + (4425479 / 90000) * c * t ^ 5 + (57673 / 5000) * c * t ^ 7 + (-566959 / 180000) * c * t ^ 9 + (-1051153 / 45000) * c * t ^ 11 + (10369 / 180000) * c * t ^ 17 + (-1045369 / 750) * alpha * t ^ 3 + (26315054 / 5625) * alpha * t ^ 5 + (-403318 / 125) * alpha * t ^ 7 + (-17488931 / 22500) * alpha * t ^ 9 + (928369 / 1250) * alpha * t ^ 11 + (2427 / 500) * alpha * t ^ 17 + (28324 / 75) * alpha * c * t ^ 3 + (-4155217 / 5625) * alpha * c * t ^ 5 + (2057254 / 5625) * alpha * c * t ^ 7 + (-30871 / 5625) * alpha * c * t ^ 9 + (3536 / 16875) * alpha * c * t ^ 11 + (10066 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_10, v49_11, v49_20, v49_21, v49_30, v49_31, v49_40, v49_41]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21, phase48_30, phase48_31, phase48_40, phase48_41]
  try simp only [star_one, star_neg]
  linear_combination ((-75563 / 3000) * t ^ 3 + (-67810487 / 720000) * t ^ 5 + (2224889 / 24000) * t ^ 7 + (97675691 / 7200000) * t ^ 9 + (-113427 / 200000) * t ^ 11 + (-3890063 / 21600000) * t ^ 17 + (80219 / 3000) * c * t ^ 3 + (-5557531 / 2160000) * c * t ^ 5 + (-19705861 / 1080000) * c * t ^ 7 + (-57510017 / 21600000) * c * t ^ 9 + (906667 / 1800000) * c * t ^ 11 + (2081581 / 64800000) * c * t ^ 17 + (-194 / 125) * c ^ 2 * t ^ 3 + (27803 / 33750) * c ^ 2 * t ^ 5 + (1123 / 2250) * c ^ 2 * t ^ 7 + (1448 / 28125) * c ^ 2 * t ^ 9 + (1784 / 28125) * c ^ 2 * t ^ 11 + (146 / 84375) * c ^ 2 * t ^ 17) * alpha_sq + ((952 / 1875) * t ^ 5 + (32 / 1875) * t ^ 7 + (-584 / 1875) * t ^ 9 + (-16 / 75) * t ^ 11 + (-776 / 125) * alpha * t ^ 3 + (2864 / 625) * alpha * t ^ 5 + (1453 / 5625) * alpha * t ^ 7 + (26 / 9375) * alpha * t ^ 9 + (14209 / 28125) * alpha * t ^ 11 + (-584 / 84375) * alpha * t ^ 17) * c_sq
theorem v50_42 (t : ℂ) : (momentPoly 50 z50 4 2).eval t = ((-68267407 / 300) * t ^ 2 + (118232639 / 200) * t ^ 4 + (-1195023378367 / 2400000) * t ^ 6 + (309360110621 / 2400000) * t ^ 8 + (22759167499 / 4800000) * t ^ 10 + (14191314487 / 14400000) * t ^ 12 + (-381092873 / 1200000) * t ^ 14 + (-437290619 / 14400000) * t ^ 18 + (93575707 / 14400000) * t ^ 20 + (-399308 / 75) * c * t ^ 2 + (1243438 / 125) * c * t ^ 4 + (-697182821 / 150000) * c * t ^ 6 + (-516307 / 30000) * c * t ^ 8 + (64061603 / 180000) * c * t ^ 10 + (-266603767 / 900000) * c * t ^ 12 + (-3422153 / 168750) * c * t ^ 14 + (-7301683 / 2700000) * c * t ^ 18 + (17197 / 180000) * c * t ^ 20 + (-5005611 / 100) * alpha * t ^ 2 + (35253713 / 200) * alpha * t ^ 4 + (-1415498382163 / 7200000) * alpha * t ^ 6 + (494257161049 / 7200000) * alpha * t ^ 8 + (4901265391 / 14400000) * alpha * t ^ 10 + (59062180523 / 43200000) * alpha * t ^ 12 + (230925803 / 3600000) * alpha * t ^ 14 + (616404043 / 14400000) * alpha * t ^ 18 + (-1777587137 / 43200000) * alpha * t ^ 20 + (-399308 / 225) * alpha * c * t ^ 2 + (431546 / 125) * alpha * c * t ^ 4 + (-872159333 / 450000) * alpha * c * t ^ 6 + (29268173 / 90000) * alpha * c * t ^ 8 + (19724833 / 180000) * alpha * c * t ^ 10 + (-514504631 / 2700000) * alpha * c * t ^ 12 + (272873 / 18750) * alpha * c * t ^ 14 + (173989 / 900000) * alpha * c * t ^ 18 + (-78803 / 540000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_10, v49_11, v49_12, v49_20, v49_21, v49_22, v49_30, v49_31, v49_32, v49_40, v49_41, v49_42]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22, phase48_30, phase48_31, phase48_32, phase48_40, phase48_41, phase48_42]
  try simp only [star_one, star_neg]
  linear_combination ((99827 / 225) * t ^ 2 + (-254984 / 375) * t ^ 4 + (912368951 / 2700000) * t ^ 6 + (-33271271 / 1200000) * t ^ 8 + (-8183089 / 300000) * t ^ 10 + (-11537199667 / 324000000) * t ^ 12 + (1065420541 / 81000000) * t ^ 14 + (83837059 / 81000000) * t ^ 18 + (28376351 / 12000000) * t ^ 20 + (-57044 / 225) * c * t ^ 2 + (150128 / 375) * c * t ^ 4 + (-269483971 / 900000) * c * t ^ 6 + (579405773 / 5400000) * c * t ^ 8 + (93191903 / 1080000) * c * t ^ 10 + (-484737707 / 10800000) * c * t ^ 12 + (-208081 / 37500) * c * t ^ 14 + (-158959 / 360000) * c * t ^ 18 + (-16403 / 2160000) * c * t ^ 20 + (-14261 / 75) * c ^ 2 * t ^ 2 + (34952 / 125) * c ^ 2 * t ^ 4 + (-51958519 / 1350000) * c ^ 2 * t ^ 6 + (-104729311 / 2025000) * c ^ 2 * t ^ 8 + (-1020863 / 1350000) * c ^ 2 * t ^ 10 + (-2459 / 187500) * c ^ 2 * t ^ 12 + (-19211 / 562500) * c ^ 2 * t ^ 14 + (-8291 / 140625) * c ^ 2 * t ^ 18 + (292 / 1265625) * c ^ 2 * t ^ 20) * alpha_sq + ((28522 / 75) * t ^ 2 + (-160864 / 375) * t ^ 4 + (-47227927 / 300000) * t ^ 6 + (95030101 / 450000) * t ^ 8 + (5584633 / 1800000) * t ^ 10 + (-29492159 / 6750000) * t ^ 12 + (83096 / 140625) * t ^ 14 + (528727 / 3000000) * t ^ 18 + (584 / 421875) * t ^ 20 + (-28522 / 75) * alpha * t ^ 2 + (272992 / 375) * alpha * t ^ 4 + (-1104092401 / 2700000) * alpha * t ^ 6 + (76603841 / 1350000) * alpha * t ^ 8 + (-37529 / 8000) * alpha * t ^ 10 + (9479573 / 2250000) * alpha * t ^ 12 + (141352 / 421875) * alpha * t ^ 14 + (1683697 / 27000000) * alpha * t ^ 18 + (-584 / 421875) * alpha * t ^ 20) * c_sq
theorem v50_43 (t : ℂ) : (momentPoly 50 z50 4 3).eval t = ((11296268 / 5) * t + (-163153338 / 25) * t ^ 3 + (12717287523 / 2000) * t ^ 5 + (-26822211331481 / 12000000) * t ^ 7 + (5572597510991 / 24000000) * t ^ 9 + (-2244096544757 / 24000000) * t ^ 11 + (-1648862044711 / 144000000) * t ^ 13 + (18061409221 / 1000000) * t ^ 15 + (-257575395341 / 144000000) * t ^ 17 + (-27751984153 / 216000000) * t ^ 19 + (2276748331 / 28800000) * t ^ 21 + (20967888329 / 432000000) * t ^ 25 + (-2824067 / 15) * c * t + (6133269 / 10) * c * t ^ 3 + (-2190472397 / 3000) * c * t ^ 5 + (268350677563 / 720000) * c * t ^ 7 + (-412537470671 / 6000000) * c * t ^ 9 + (62894509121 / 36000000) * c * t ^ 11 + (-15368490631 / 108000000) * c * t ^ 13 + (-4194552283 / 9000000) * c * t ^ 15 + (148908299 / 9000000) * c * t ^ 17 + (-78569269 / 2400000) * c * t ^ 19 + (211188709 / 12000000) * c * t ^ 21 + (31919257 / 27000000) * c * t ^ 25 + (-11296268 / 15) * alpha * t + (43505694 / 25) * alpha * t ^ 3 + (-5132704499 / 6000) * alpha * t ^ 5 + (-1295740521001 / 2400000) * alpha * t ^ 7 + (10608426767419 / 24000000) * alpha * t ^ 9 + (-971727700427 / 72000000) * alpha * t ^ 11 + (-15867195891481 / 432000000) * alpha * t ^ 13 + (145423975553 / 9000000) * alpha * t ^ 15 + (4091802679 / 16000000) * alpha * t ^ 17 + (-59618017 / 4800000) * alpha * t ^ 19 + (-6474896093 / 144000000) * alpha * t ^ 21 + (9244681213 / 432000000) * alpha * t ^ 25 + (-2824067 / 15) * alpha * c * t + (25226969 / 50) * alpha * c * t ^ 3 + (-250786633 / 600) * alpha * c * t ^ 5 + (1394131619123 / 18000000) * alpha * c * t ^ 7 + (75428467879 / 3600000) * alpha * c * t ^ 9 + (133704550993 / 36000000) * alpha * c * t ^ 11 + (-53949991223 / 108000000) * alpha * c * t ^ 13 + (704676341 / 9000000) * alpha * c * t ^ 15 + (59909741 / 5400000) * alpha * c * t ^ 17 + (-5168708771 / 324000000) * alpha * c * t ^ 19 + (1097463197 / 108000000) * alpha * c * t ^ 21 + (-6934837 / 81000000) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_03, v49_10, v49_11, v49_12, v49_13, v49_20, v49_21, v49_22, v49_23, v49_30, v49_31, v49_32, v49_33, v49_40, v49_41, v49_42, v49_43]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23, phase48_30, phase48_31, phase48_32, phase48_33, phase48_40, phase48_41, phase48_42, phase48_43]
  try simp only [star_one, star_neg]
  linear_combination ((3627803 / 1000) * t ^ 3 + (18423629 / 2000) * t ^ 5 + (-1593518457851 / 72000000) * t ^ 7 + (132514754389 / 72000000) * t ^ 9 + (118554771327 / 16000000) * t ^ 11 + (304977419623 / 432000000) * t ^ 13 + (-89799805663 / 108000000) * t ^ 15 + (21978490379 / 270000000) * t ^ 17 + (44696541143 / 6480000000) * t ^ 19 + (-3940069171 / 720000000) * t ^ 21 + (-1283750117 / 810000000) * t ^ 25 + (-3851339 / 1000) * c * t ^ 3 + (91561159 / 18000) * c * t ^ 5 + (2744599501 / 43200000) * c * t ^ 7 + (-67600117541 / 72000000) * c * t ^ 9 + (-16332939421 / 48000000) * c * t ^ 11 + (-53530251301 / 1296000000) * c * t ^ 13 + (-816287383 / 324000000) * c * t ^ 15 + (374387821 / 202500000) * c * t ^ 17 + (-10498636679 / 6480000000) * c * t ^ 19 + (5211256027 / 6480000000) * c * t ^ 21 + (3369899 / 75937500) * c * t ^ 25 + (27942 / 125) * c ^ 2 * t ^ 3 + (-348157 / 900) * c ^ 2 * t ^ 5 + (2382574303 / 13500000) * c ^ 2 * t ^ 7 + (-143427797 / 9000000) * c ^ 2 * t ^ 9 + (-185745803 / 9000000) * c ^ 2 * t ^ 11 + (162020297 / 6000000) * c ^ 2 * t ^ 13 + (-1791719 / 843750) * c ^ 2 * t ^ 15 + (2528 / 421875) * c ^ 2 * t ^ 17 + (-9407 / 1000000) * c ^ 2 * t ^ 19 + (122003 / 3600000) * c ^ 2 * t ^ 21) * alpha_sq + ((-167652 / 125) * t ^ 3 + (1894913 / 750) * t ^ 5 + (-336947183 / 250000) * t ^ 7 + (43103411 / 375000) * t ^ 9 + (752162807 / 4500000) * t ^ 11 + (-1887400781 / 13500000) * t ^ 13 + (27705701 / 2250000) * t ^ 15 + (252893 / 1406250) * t ^ 17 + (-22449253 / 67500000) * t ^ 19 + (-204233 / 2500000) * t ^ 21 + (-20732 / 2109375) * t ^ 25 + (55884 / 125) * alpha * t ^ 3 + (-1004801 / 2250) * alpha * t ^ 5 + (-334450661 / 1350000) * alpha * t ^ 7 + (248875909 / 1125000) * alpha * t ^ 9 + (3671893 / 2700000) * alpha * t ^ 11 + (328204781 / 40500000) * alpha * t ^ 13 + (124502251 / 6750000) * alpha * t ^ 15 + (184129 / 1406250) * alpha * t ^ 17 + (154284133 / 202500000) * alpha * t ^ 19 + (-198589 / 2500000) * alpha * t ^ 21 + (20732 / 6328125) * alpha * t ^ 25) * c_sq
theorem v50_44 (t : ℂ) : (momentPoly 50 z50 4 4).eval t = (141203350 + (-2476133744 / 5) * t ^ 2 + (79263362387 / 125) * t ^ 4 + (-12845142651941 / 37500) * t ^ 6 + (8772635499033361 / 144000000) * t ^ 8 + (-77664544805767 / 60000000) * t ^ 10 + (1877952712882711 / 720000000) * t ^ 12 + (21913088764183 / 360000000) * t ^ 14 + (93864184244161 / 576000000) * t ^ 16 + (1289492663947 / 360000000) * t ^ 18 + (-18822279537323 / 2160000000) * t ^ 20 + (1106548496909 / 360000000) * t ^ 22 + (-3469183552523 / 1440000000) * t ^ 24 + (-154559702543 / 1080000000) * t ^ 26 + (11299094231 / 960000000) * t ^ 32 + (223760768 / 375) * c * t ^ 4 + (-3202438864 / 1875) * c * t ^ 6 + (461419480211 / 281250) * c * t ^ 8 + (-386087764202 / 703125) * c * t ^ 10 + (-46893517753 / 2812500) * c * t ^ 12 + (164409874639 / 2109375) * c * t ^ 14 + (-70140345197 / 1687500) * c * t ^ 16 + (2134168867 / 4218750) * c * t ^ 18 + (-9957456143 / 25312500) * c * t ^ 20 + (40950812 / 2109375) * c * t ^ 22 + (-5346563 / 2812500) * c * t ^ 24 + (-267817261 / 4218750) * c * t ^ 26 + (5878544 / 6328125) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z50, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v49_00, v49_01, v49_02, v49_03, v49_04, v49_10, v49_11, v49_12, v49_13, v49_14, v49_20, v49_21, v49_22, v49_23, v49_24, v49_30, v49_31, v49_32, v49_33, v49_34, v49_40, v49_41, v49_42, v49_43, v49_44]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24, phase48_30, phase48_31, phase48_32, phase48_33, phase48_34, phase48_40, phase48_41, phase48_42, phase48_43, phase48_44]
  try simp only [star_one, star_neg]
  linear_combination ((-38347204 / 225) * t ^ 2 + (423232436 / 1125) * t ^ 4 + (-14655675521 / 37500) * t ^ 6 + (-182459392513 / 2250000) * t ^ 8 + (2135695223197 / 3750000) * t ^ 10 + (-26074761009779 / 90000000) * t ^ 12 + (-18984074258827 / 810000000) * t ^ 14 + (9810259935139 / 1620000000) * t ^ 16 + (875555856451 / 540000000) * t ^ 18 + (-350494437421 / 303750000) * t ^ 20 + (-18154193099 / 101250000) * t ^ 22 + (32655305533 / 100000000) * t ^ 24 + (-583749113213 / 24300000000) * t ^ 26 + (-2743453069 / 1350000000) * t ^ 32 + (21912688 / 225) * c * t ^ 2 + (-43980376 / 225) * c * t ^ 4 + (326395451 / 5625) * c * t ^ 6 + (2695953181057 / 27000000) * c * t ^ 8 + (-678977743981 / 10000000) * c * t ^ 10 + (-161600956709 / 270000000) * c * t ^ 12 + (18914991835603 / 1620000000) * c * t ^ 14 + (-87529704379 / 32400000) * c * t ^ 16 + (-122540312647 / 540000000) * c * t ^ 18 + (121513491817 / 2430000000) * c * t ^ 20 + (-3604337063 / 1620000000) * c * t ^ 22 + (-7098311 / 450000000) * c * t ^ 24 + (-55294982609 / 8100000000) * c * t ^ 26 + (5425871 / 337500000) * c * t ^ 32 + (5478172 / 75) * c ^ 2 * t ^ 2 + (-22592284 / 125) * c ^ 2 * t ^ 4 + (3756181012 / 28125) * c ^ 2 * t ^ 6 + (-1327465725823 / 81000000) * c ^ 2 * t ^ 8 + (-654812801587 / 81000000) * c ^ 2 * t ^ 10 + (-1115860909033 / 810000000) * c ^ 2 * t ^ 12 + (12855006259 / 270000000) * c ^ 2 * t ^ 14 + (-952689133 / 67500000) * c ^ 2 * t ^ 16 + (-183622087 / 40500000) * c ^ 2 * t ^ 18 + (20278610489 / 2430000000) * c ^ 2 * t ^ 20 + (-3617214563 / 810000000) * c ^ 2 * t ^ 22 + (1737193 / 56250000) * c ^ 2 * t ^ 24 + (-8848343 / 1012500000) * c ^ 2 * t ^ 26 + (42632 / 94921875) * c ^ 2 * t ^ 32) * alpha_sq + ((-21912688 / 75) * t ^ 2 + (57418064 / 75) * t ^ 4 + (-18391169288 / 28125) * t ^ 6 + (1188053599313 / 6750000) * t ^ 8 + (-2311666309 / 11250000) * t ^ 10 + (309761880823 / 67500000) * t ^ 12 + (1290785609 / 7500000) * t ^ 14 + (-839120011 / 3375000) * t ^ 16 + (54191111 / 2812500) * t ^ 18 + (-4060796119 / 202500000) * t ^ 20 + (1123719517 / 67500000) * t ^ 22 + (-1019 / 14062500) * t ^ 24 + (37576829 / 42187500) * t ^ 26 + (-170528 / 31640625) * t ^ 32) * c_sq
#print axioms v50_00
#print axioms v50_11
#print axioms v50_22
#print axioms v50_33
#print axioms v50_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v51_02 (t : ℂ) : (momentPoly 51 z51 0 2).eval t = ((-3539 / 600) * t ^ 2 + (1189 / 200) * t ^ 4 + (-8 / 75) * c * t ^ 2 + (-1 / 75) * c * t ^ 4 + (767 / 200) * alpha * t ^ 2 + (-2273 / 600) * alpha * t ^ 4 + (8 / 225) * alpha * c * t ^ 2 + (1 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02]
  try simp only [phase48_00, phase48_01, phase48_02]
  try simp only [star_one, star_neg]
  linear_combination ((4 / 225) * t ^ 2 + (-1 / 75) * c * t ^ 2 + (-1 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((2 / 225) * t ^ 2 + (2 / 225) * alpha * t ^ 2) * c_sq
theorem v51_03 (t : ℂ) : (momentPoly 51 z51 0 3).eval t = ((-557 / 25) * t ^ 3 + (507 / 25) * t ^ 5 + 2 * t ^ 9 + (-259 / 500) * c * t ^ 3 + (457 / 1500) * c * t ^ 5 + (71 / 1125) * c * t ^ 9 + (9329 / 750) * alpha * t ^ 3 + (-53141 / 3000) * alpha * t ^ 5 + (4147 / 1000) * alpha * t ^ 9 + (-73 / 75) * alpha * c * t ^ 3 + (73 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_03]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03]
  try simp only [star_one, star_neg]
  linear_combination ((351 / 2000) * t ^ 3 + (-1439 / 2000) * t ^ 5 + (-3047 / 18000) * c * t ^ 3 + (1381 / 6000) * c * t ^ 5 + (-7 / 1125) * c ^ 2 * t ^ 3 + (-2 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((28 / 1125) * alpha * t ^ 3 + (8 / 1125) * alpha * t ^ 5) * c_sq
theorem v51_04 (t : ℂ) : (momentPoly 51 z51 0 4).eval t = ((-3243201 / 40000) * t ^ 4 + (3010977 / 20000) * t ^ 6 + (-9695989 / 240000) * t ^ 8 + (-5890249 / 180000) * t ^ 10 + (1387579 / 240000) * t ^ 16 + (-8201 / 3750) * c * t ^ 4 + (31433 / 7500) * c * t ^ 6 + (-313 / 1250) * c * t ^ 8 + (-40547 / 22500) * c * t ^ 10 + (146 / 5625) * c * t ^ 16 + (-4684799 / 40000) * alpha * t ^ 4 + (15000029 / 60000) * alpha * t ^ 6 + (-11576537 / 80000) * alpha * t ^ 8 + (392003 / 60000) * alpha * t ^ 10 + (2279503 / 720000) * alpha * t ^ 16 + (-46921 / 11250) * alpha * c * t ^ 4 + (29731 / 7500) * alpha * c * t ^ 6 + (4901 / 11250) * alpha * c * t ^ 8 + (-16547 / 67500) * alpha * c * t ^ 10 + (146 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_03, v50_04]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04]
  try simp only [star_one, star_neg]
  linear_combination ((10777 / 11250) * t ^ 4 + (-334933 / 45000) * t ^ 6 + (144613 / 15000) * t ^ 8 + (24947 / 67500) * t ^ 10 + (-13697 / 11250) * c * t ^ 4 + (26431 / 11250) * c * t ^ 6 + (1397 / 22500) * c * t ^ 8 + (-14209 / 22500) * c * t ^ 10 + (292 / 1125) * c ^ 2 * t ^ 4 + (-4408 / 16875) * c ^ 2 * t ^ 6 + (-4 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-501 / 625) * t ^ 4 + (1499 / 1875) * t ^ 6 + (-8 / 5625) * t ^ 8 + (568 / 16875) * t ^ 10 + (-1331 / 5625) * alpha * t ^ 4 + (1343 / 5625) * alpha * t ^ 6 + (8 / 5625) * alpha * t ^ 8 + (-568 / 16875) * alpha * t ^ 10) * c_sq
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
theorem v51_12 (t : ℂ) : (momentPoly 51 z51 1 2).eval t = ((909 / 10) * t + (-54167 / 600) * t ^ 3 + (743 / 600) * t ^ 5 + (-101 / 30) * c * t + (6929 / 1800) * c * t ^ 3 + (-331 / 600) * c * t ^ 5 + (303 / 10) * alpha * t + (-8731 / 360) * alpha * t ^ 3 + (-9769 / 1800) * alpha * t ^ 5 + (101 / 30) * alpha * c * t + (-5761 / 1800) * alpha * c * t ^ 3 + (-7 / 72) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_10, v50_11, v50_12]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12]
  try simp only [star_one, star_neg]
  linear_combination ((-117 / 2000) * t ^ 3 + (1439 / 6000) * t ^ 5 + (3047 / 54000) * c * t ^ 3 + (-1381 / 18000) * c * t ^ 5 + (7 / 3375) * c ^ 2 * t ^ 3 + (2 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((-14 / 1125) * t ^ 3 + (-4 / 1125) * t ^ 5 + (-14 / 3375) * alpha * t ^ 3 + (-4 / 3375) * alpha * t ^ 5) * c_sq
theorem v51_13 (t : ℂ) : (momentPoly 51 z51 1 3).eval t = ((-3539 / 4) * t ^ 2 + (869059 / 500) * t ^ 4 + (-5114351 / 6000) * t ^ 6 + (-3167 / 3600) * t ^ 10 + (-16) * c * t ^ 2 + (14311 / 1000) * c * t ^ 4 + (6137 / 6000) * c * t ^ 6 + (2509 / 6000) * c * t ^ 10 + (2301 / 4) * alpha * t ^ 2 + (-1660303 / 1500) * alpha * t ^ 4 + (1050523 / 2000) * alpha * t ^ 6 + (23233 / 3600) * alpha * t ^ 10 + (16 / 3) * alpha * c * t ^ 2 + (-44533 / 9000) * alpha * c * t ^ 4 + (-1337 / 18000) * alpha * c * t ^ 6 + (-4109 / 18000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_03, v50_10, v50_11, v50_12, v50_13]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13]
  try simp only [star_one, star_neg]
  linear_combination ((8 / 3) * t ^ 2 + (-104197 / 45000) * t ^ 4 + (12923 / 90000) * t ^ 6 + (-24947 / 270000) * t ^ 10 + (-2) * c * t ^ 2 + (10004 / 5625) * c * t ^ 4 + (-21113 / 90000) * c * t ^ 6 + (14209 / 90000) * c * t ^ 10 + (-2 / 3) * c ^ 2 * t ^ 2 + (537 / 1000) * c ^ 2 * t ^ 4 + (91 / 1000) * c ^ 2 * t ^ 6) * alpha_sq + ((4 / 3) * t ^ 2 + (-3319 / 3750) * t ^ 4 + (-4151 / 11250) * t ^ 6 + (142 / 16875) * t ^ 10 + (4 / 3) * alpha * t ^ 2 + (-15797 / 11250) * alpha * t ^ 4 + (563 / 3750) * alpha * t ^ 6 + (142 / 16875) * alpha * t ^ 10) * c_sq
theorem v51_14 (t : ℂ) : (momentPoly 51 z51 1 4).eval t = ((-110286 / 25) * t ^ 3 + (30245447 / 3750) * t ^ 5 + (-6419467 / 1875) * t ^ 7 + (773881 / 3750) * t ^ 9 + (-830096 / 1875) * t ^ 11 + (3783 / 625) * t ^ 17 + (-25641 / 250) * c * t ^ 3 + (5236379 / 36000) * c * t ^ 5 + (-878557 / 30000) * c * t ^ 7 + (-317263 / 360000) * c * t ^ 9 + (-3544243 / 270000) * c * t ^ 11 + (33089 / 360000) * c * t ^ 17 + (307857 / 125) * alpha * t ^ 3 + (-1071573353 / 180000) * alpha * t ^ 5 + (105502019 / 30000) * alpha * t ^ 7 + (269815489 / 360000) * alpha * t ^ 9 + (-209232491 / 270000) * alpha * t ^ 11 + (-710249 / 216000) * alpha * t ^ 17 + (-4818 / 25) * alpha * c * t ^ 3 + (4324577 / 11250) * alpha * c * t ^ 5 + (-1102357 / 5625) * alpha * c * t ^ 7 + (52771 / 11250) * alpha * c * t ^ 9 + (-1768 / 16875) * alpha * c * t ^ 11 + (-5033 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_03, v50_04, v50_10, v50_11, v50_12, v50_13, v50_14]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14]
  try simp only [star_one, star_neg]
  linear_combination ((34749 / 1000) * t ^ 3 + (-121908983 / 720000) * t ^ 5 + (201142499 / 1800000) * t ^ 7 + (124276523 / 7200000) * t ^ 9 + (292181 / 1800000) * t ^ 11 + (-1511429 / 7200000) * t ^ 17 + (-33517 / 1000) * c * t ^ 3 + (50918327 / 720000) * c * t ^ 5 + (-59819411 / 1800000) * c * t ^ 7 + (-79445441 / 21600000) * c * t ^ 9 + (-3332861 / 16200000) * c * t ^ 11 + (450181 / 7200000) * c * t ^ 17 + (-154 / 125) * c ^ 2 * t ^ 3 + (23737 / 33750) * c ^ 2 * t ^ 5 + (66763 / 168750) * c ^ 2 * t ^ 7 + (964 / 28125) * c ^ 2 * t ^ 9 + (10988 / 253125) * c ^ 2 * t ^ 11 + (292 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((2488 / 5625) * t ^ 5 + (-104 / 1125) * t ^ 7 + (-1168 / 5625) * t ^ 9 + (-32 / 225) * t ^ 11 + (616 / 125) * alpha * t ^ 3 + (-66298 / 16875) * alpha * t ^ 5 + (-9968 / 28125) * alpha * t ^ 7 + (1028 / 84375) * alpha * t ^ 9 + (-81718 / 253125) * alpha * t ^ 11 + (1168 / 253125) * alpha * t ^ 17) * c_sq
theorem v51_20 (t : ℂ) : (momentPoly 51 z51 2 0).eval t = ((-3539 / 600) * t ^ 2 + (1189 / 200) * t ^ 4 + (-8 / 75) * c * t ^ 2 + (-1 / 75) * c * t ^ 4 + (-767 / 200) * alpha * t ^ 2 + (2273 / 600) * alpha * t ^ 4 + (-8 / 225) * alpha * c * t ^ 2 + (-1 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_10, v50_20]
  try simp only [phase48_00, phase48_10, phase48_20]
  try simp only [star_one, star_neg]
  linear_combination ((4 / 225) * t ^ 2 + (-1 / 75) * c * t ^ 2 + (-1 / 225) * c ^ 2 * t ^ 2) * alpha_sq + ((2 / 225) * t ^ 2 + (-2 / 225) * alpha * t ^ 2) * c_sq
theorem v51_21 (t : ℂ) : (momentPoly 51 z51 2 1).eval t = ((909 / 10) * t + (-54167 / 600) * t ^ 3 + (743 / 600) * t ^ 5 + (-101 / 30) * c * t + (6929 / 1800) * c * t ^ 3 + (-331 / 600) * c * t ^ 5 + (-303 / 10) * alpha * t + (8731 / 360) * alpha * t ^ 3 + (9769 / 1800) * alpha * t ^ 5 + (-101 / 30) * alpha * c * t + (5761 / 1800) * alpha * c * t ^ 3 + (7 / 72) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_10, v50_11, v50_20, v50_21]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21]
  try simp only [star_one, star_neg]
  linear_combination ((-117 / 2000) * t ^ 3 + (1439 / 6000) * t ^ 5 + (3047 / 54000) * c * t ^ 3 + (-1381 / 18000) * c * t ^ 5 + (7 / 3375) * c ^ 2 * t ^ 3 + (2 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((-14 / 1125) * t ^ 3 + (-4 / 1125) * t ^ 5 + (14 / 3375) * alpha * t ^ 3 + (4 / 3375) * alpha * t ^ 5) * c_sq
theorem v51_22 (t : ℂ) : (momentPoly 51 z51 2 2).eval t = (5151 + (-29360 / 3) * t ^ 2 + (27439279 / 6000) * t ^ 4 + (353471 / 9000) * t ^ 6 + (494101 / 18000) * t ^ 8 + (2336 / 1125) * c * t ^ 4 + (-2044 / 1125) * c * t ^ 6 + (-292 / 1125) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_10, v50_11, v50_12, v50_20, v50_21, v50_22]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22]
  try simp only [star_one, star_neg]
  linear_combination ((-32 / 9) * t ^ 2 + (346 / 125) * t ^ 4 + (34343 / 15000) * t ^ 6 + (-144613 / 45000) * t ^ 8 + (8 / 3) * c * t ^ 2 + (-13267 / 6750) * c * t ^ 4 + (-10583 / 22500) * c * t ^ 6 + (-1397 / 67500) * c * t ^ 8 + (8 / 9) * c ^ 2 * t ^ 2 + (-5417 / 6750) * c ^ 2 * t ^ 4 + (-3469 / 101250) * c ^ 2 * t ^ 6 + (4 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((-32 / 9) * t ^ 2 + (3806 / 1125) * t ^ 4 + (-682 / 16875) * t ^ 6 + (-16 / 16875) * t ^ 8) * c_sq
theorem v51_23 (t : ℂ) : (momentPoly 51 z51 2 3).eval t = ((136359 / 10) * t + (-5362533 / 200) * t ^ 3 + (134041611 / 10000) * t ^ 5 + (-48517529 / 120000) * t ^ 7 + (7405787 / 40000) * t ^ 9 + (2299927 / 72000) * t ^ 11 + (-13077887 / 360000) * t ^ 13 + (-15151 / 30) * c * t + (228657 / 200) * c * t ^ 3 + (-141845017 / 180000) * c * t ^ 5 + (13620497 / 90000) * c * t ^ 7 + (-558409 / 180000) * c * t ^ 9 + (129613 / 135000) * c * t ^ 11 + (2459 / 5625) * c * t ^ 13 + (45453 / 10) * alpha * t + (-288123 / 40) * alpha * t ^ 3 + (29738227 / 30000) * alpha * t ^ 5 + (206168189 / 120000) * alpha * t ^ 7 + (-21736927 / 360000) * alpha * t ^ 9 + (-23516029 / 1080000) * alpha * t ^ 11 + (34417777 / 1080000) * alpha * t ^ 13 + (15151 / 30) * alpha * c * t + (-190113 / 200) * alpha * c * t ^ 3 + (24593011 / 60000) * alpha * c * t ^ 5 + (1014949 / 30000) * alpha * c * t ^ 7 + (85621 / 36000) * alpha * c * t ^ 9 + (-25247 / 45000) * alpha * c * t ^ 11 + (2389 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_03, v50_10, v50_11, v50_12, v50_13, v50_20, v50_21, v50_22, v50_23]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23]
  try simp only [star_one, star_neg]
  linear_combination ((-34749 / 2000) * t ^ 3 + (1543327 / 18000) * t ^ 5 + (-12472679 / 225000) * t ^ 7 + (-6672419 / 450000) * t ^ 9 + (1991 / 37500) * t ^ 11 + (659347 / 450000) * t ^ 13 + (33517 / 2000) * c * t ^ 3 + (-9808069 / 270000) * c * t ^ 5 + (3145661 / 168750) * c * t ^ 7 + (36344 / 84375) * c * t ^ 9 + (169553 / 506250) * c * t ^ 11 + (14209 / 675000) * c * t ^ 13 + (77 / 125) * c ^ 2 * t ^ 3 + (-1167 / 2500) * c ^ 2 * t ^ 5 + (-11963 / 135000) * c ^ 2 * t ^ 7 + (349 / 67500) * c ^ 2 * t ^ 9 + (-4189 / 135000) * c ^ 2 * t ^ 11) * alpha_sq + ((-462 / 125) * t ^ 3 + (11599 / 3750) * t ^ 5 + (39437 / 112500) * t ^ 7 + (-992 / 9375) * t ^ 9 + (54811 / 337500) * t ^ 11 + (284 / 84375) * t ^ 13 + (-154 / 125) * alpha * t ^ 3 + (1123 / 2250) * alpha * t ^ 5 + (60079 / 112500) * alpha * t ^ 7 + (8704 / 84375) * alpha * t ^ 9 + (30811 / 1012500) * alpha * t ^ 11 + (284 / 253125) * alpha * t ^ 13) * c_sq
theorem v51_24 (t : ℂ) : (momentPoly 51 z51 2 4).eval t = ((-13140307 / 75) * t ^ 2 + (508396261 / 1000) * t ^ 4 + (-3505329624701 / 7200000) * t ^ 6 + (214345736831 / 1440000) * t ^ 8 + (14058080989 / 2880000) * t ^ 10 + (2417624531 / 14400000) * t ^ 12 + (-2560387837 / 10800000) * t ^ 14 + (158655023 / 43200000) * t ^ 18 + (-328581467 / 43200000) * t ^ 20 + (-237632 / 75) * c * t ^ 2 + (749724 / 125) * c * t ^ 4 + (-207198049 / 75000) * c * t ^ 6 + (-12798599 / 180000) * c * t ^ 8 + (37530041 / 225000) * c * t ^ 10 + (-275669371 / 1800000) * c * t ^ 12 + (-729841 / 84375) * c * t ^ 14 + (-394499 / 337500) * c * t ^ 18 + (12397 / 360000) * c * t ^ 20 + (2847871 / 25) * alpha * t ^ 2 + (-971058337 / 3000) * alpha * t ^ 4 + (723067562161 / 2400000) * alpha * t ^ 6 + (-14311026729 / 160000) * alpha * t ^ 8 + (246509743 / 960000) * alpha * t ^ 10 + (-94437944279 / 43200000) * alpha * t ^ 12 + (-445599823 / 3600000) * alpha * t ^ 14 + (-779951723 / 14400000) * alpha * t ^ 18 + (1920732181 / 43200000) * alpha * t ^ 20 + (237632 / 225) * alpha * c * t ^ 2 + (-2327572 / 1125) * alpha * c * t ^ 4 + (253880017 / 225000) * alpha * c * t ^ 6 + (-9400913 / 60000) * alpha * c * t ^ 8 + (-11300171 / 225000) * alpha * c * t ^ 10 + (535386683 / 5400000) * alpha * c * t ^ 12 + (-1887062 / 253125) * alpha * c * t ^ 14 + (-240253 / 1012500) * alpha * c * t ^ 18 + (83603 / 1080000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_03, v50_04, v50_10, v50_11, v50_12, v50_13, v50_14, v50_20, v50_21, v50_22, v50_23, v50_24]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24]
  try simp only [star_one, star_neg]
  linear_combination ((118816 / 225) * t ^ 2 + (-5105653 / 5625) * t ^ 4 + (115803521 / 270000) * t ^ 6 + (-673082231 / 10800000) * t ^ 8 + (1225499549 / 27000000) * t ^ 10 + (-4005466337 / 108000000) * t ^ 12 + (21771559 / 3000000) * t ^ 14 + (-115387 / 250000) * t ^ 18 + (302415511 / 108000000) * t ^ 20 + (-29704 / 75) * c * t ^ 2 + (3921568 / 5625) * c * t ^ 4 + (-173587769 / 450000) * c * t ^ 6 + (112554683 / 1800000) * c * t ^ 8 + (100520797 / 1350000) * c * t ^ 10 + (-60432059 / 1200000) * c * t ^ 12 + (-1109 / 225) * c * t ^ 14 + (-25016 / 84375) * c * t ^ 18 + (-26003 / 2160000) * c * t ^ 20 + (-29704 / 225) * c ^ 2 * t ^ 2 + (26313 / 125) * c ^ 2 * t ^ 4 + (-29127149 / 675000) * c ^ 2 * t ^ 6 + (-7181707 / 202500) * c ^ 2 * t ^ 8 + (-239219 / 1125000) * c ^ 2 * t ^ 10 + (94004 / 1265625) * c ^ 2 * t ^ 12 + (-238063 / 7593750) * c ^ 2 * t ^ 14 + (-148946 / 3796875) * c ^ 2 * t ^ 18 + (584 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((59408 / 225) * t ^ 2 + (-650524 / 1875) * t ^ 4 + (-78759653 / 1350000) * t ^ 6 + (19416817 / 135000) * t ^ 8 + (16386877 / 13500000) * t ^ 10 + (-11734621 / 3375000) * t ^ 12 + (544712 / 1265625) * t ^ 14 + (5118031 / 40500000) * t ^ 18 + (1168 / 1265625) * t ^ 20 + (59408 / 225) * alpha * t ^ 2 + (-3096212 / 5625) * alpha * t ^ 4 + (151459529 / 450000) * alpha * t ^ 6 + (-11065433 / 225000) * alpha * t ^ 8 + (5174293 / 1500000) * alpha * t ^ 10 + (-33958423 / 10125000) * alpha * t ^ 12 + (-78856 / 421875) * alpha * t ^ 14 + (-441403 / 13500000) * alpha * t ^ 18 + (1168 / 1265625) * alpha * t ^ 20) * c_sq
theorem v51_30 (t : ℂ) : (momentPoly 51 z51 3 0).eval t = ((-557 / 25) * t ^ 3 + (507 / 25) * t ^ 5 + 2 * t ^ 9 + (-259 / 500) * c * t ^ 3 + (457 / 1500) * c * t ^ 5 + (71 / 1125) * c * t ^ 9 + (-9329 / 750) * alpha * t ^ 3 + (53141 / 3000) * alpha * t ^ 5 + (-4147 / 1000) * alpha * t ^ 9 + (73 / 75) * alpha * c * t ^ 3 + (-73 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_10, v50_20, v50_30]
  try simp only [phase48_00, phase48_10, phase48_20, phase48_30]
  try simp only [star_one, star_neg]
  linear_combination ((351 / 2000) * t ^ 3 + (-1439 / 2000) * t ^ 5 + (-3047 / 18000) * c * t ^ 3 + (1381 / 6000) * c * t ^ 5 + (-7 / 1125) * c ^ 2 * t ^ 3 + (-2 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-28 / 1125) * alpha * t ^ 3 + (-8 / 1125) * alpha * t ^ 5) * c_sq
theorem v51_31 (t : ℂ) : (momentPoly 51 z51 3 1).eval t = ((-3539 / 4) * t ^ 2 + (869059 / 500) * t ^ 4 + (-5114351 / 6000) * t ^ 6 + (-3167 / 3600) * t ^ 10 + (-16) * c * t ^ 2 + (14311 / 1000) * c * t ^ 4 + (6137 / 6000) * c * t ^ 6 + (2509 / 6000) * c * t ^ 10 + (-2301 / 4) * alpha * t ^ 2 + (1660303 / 1500) * alpha * t ^ 4 + (-1050523 / 2000) * alpha * t ^ 6 + (-23233 / 3600) * alpha * t ^ 10 + (-16 / 3) * alpha * c * t ^ 2 + (44533 / 9000) * alpha * c * t ^ 4 + (1337 / 18000) * alpha * c * t ^ 6 + (4109 / 18000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_10, v50_11, v50_20, v50_21, v50_30, v50_31]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21, phase48_30, phase48_31]
  try simp only [star_one, star_neg]
  linear_combination ((8 / 3) * t ^ 2 + (-104197 / 45000) * t ^ 4 + (12923 / 90000) * t ^ 6 + (-24947 / 270000) * t ^ 10 + (-2) * c * t ^ 2 + (10004 / 5625) * c * t ^ 4 + (-21113 / 90000) * c * t ^ 6 + (14209 / 90000) * c * t ^ 10 + (-2 / 3) * c ^ 2 * t ^ 2 + (537 / 1000) * c ^ 2 * t ^ 4 + (91 / 1000) * c ^ 2 * t ^ 6) * alpha_sq + ((4 / 3) * t ^ 2 + (-3319 / 3750) * t ^ 4 + (-4151 / 11250) * t ^ 6 + (142 / 16875) * t ^ 10 + (-4 / 3) * alpha * t ^ 2 + (15797 / 11250) * alpha * t ^ 4 + (-563 / 3750) * alpha * t ^ 6 + (-142 / 16875) * alpha * t ^ 10) * c_sq
theorem v51_32 (t : ℂ) : (momentPoly 51 z51 3 2).eval t = ((136359 / 10) * t + (-5362533 / 200) * t ^ 3 + (134041611 / 10000) * t ^ 5 + (-48517529 / 120000) * t ^ 7 + (7405787 / 40000) * t ^ 9 + (2299927 / 72000) * t ^ 11 + (-13077887 / 360000) * t ^ 13 + (-15151 / 30) * c * t + (228657 / 200) * c * t ^ 3 + (-141845017 / 180000) * c * t ^ 5 + (13620497 / 90000) * c * t ^ 7 + (-558409 / 180000) * c * t ^ 9 + (129613 / 135000) * c * t ^ 11 + (2459 / 5625) * c * t ^ 13 + (-45453 / 10) * alpha * t + (288123 / 40) * alpha * t ^ 3 + (-29738227 / 30000) * alpha * t ^ 5 + (-206168189 / 120000) * alpha * t ^ 7 + (21736927 / 360000) * alpha * t ^ 9 + (23516029 / 1080000) * alpha * t ^ 11 + (-34417777 / 1080000) * alpha * t ^ 13 + (-15151 / 30) * alpha * c * t + (190113 / 200) * alpha * c * t ^ 3 + (-24593011 / 60000) * alpha * c * t ^ 5 + (-1014949 / 30000) * alpha * c * t ^ 7 + (-85621 / 36000) * alpha * c * t ^ 9 + (25247 / 45000) * alpha * c * t ^ 11 + (-2389 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_10, v50_11, v50_12, v50_20, v50_21, v50_22, v50_30, v50_31, v50_32]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22, phase48_30, phase48_31, phase48_32]
  try simp only [star_one, star_neg]
  linear_combination ((-34749 / 2000) * t ^ 3 + (1543327 / 18000) * t ^ 5 + (-12472679 / 225000) * t ^ 7 + (-6672419 / 450000) * t ^ 9 + (1991 / 37500) * t ^ 11 + (659347 / 450000) * t ^ 13 + (33517 / 2000) * c * t ^ 3 + (-9808069 / 270000) * c * t ^ 5 + (3145661 / 168750) * c * t ^ 7 + (36344 / 84375) * c * t ^ 9 + (169553 / 506250) * c * t ^ 11 + (14209 / 675000) * c * t ^ 13 + (77 / 125) * c ^ 2 * t ^ 3 + (-1167 / 2500) * c ^ 2 * t ^ 5 + (-11963 / 135000) * c ^ 2 * t ^ 7 + (349 / 67500) * c ^ 2 * t ^ 9 + (-4189 / 135000) * c ^ 2 * t ^ 11) * alpha_sq + ((-462 / 125) * t ^ 3 + (11599 / 3750) * t ^ 5 + (39437 / 112500) * t ^ 7 + (-992 / 9375) * t ^ 9 + (54811 / 337500) * t ^ 11 + (284 / 84375) * t ^ 13 + (154 / 125) * alpha * t ^ 3 + (-1123 / 2250) * alpha * t ^ 5 + (-60079 / 112500) * alpha * t ^ 7 + (-8704 / 84375) * alpha * t ^ 9 + (-30811 / 1012500) * alpha * t ^ 11 + (-284 / 253125) * alpha * t ^ 13) * c_sq
theorem v51_33 (t : ℂ) : (momentPoly 51 z51 3 3).eval t = (772701 + (-10901368 / 5) * t ^ 2 + (4033574013 / 2000) * t ^ 4 + (-29671929281 / 50000) * t ^ 6 + (-127605943 / 30000) * t ^ 8 + (-2276957021 / 200000) * t ^ 10 + (3301507 / 37500) * t ^ 12 + (-199975159 / 900000) * t ^ 14 + (29576101 / 5400000) * t ^ 18 + (114464 / 125) * c * t ^ 4 + (-2168243 / 1250) * c * t ^ 6 + (5797517 / 7500) * c * t ^ 8 + (297941 / 7500) * c * t ^ 10 + (-532171 / 22500) * c * t ^ 12 + (221657 / 7500) * c * t ^ 14 + (284 / 1125) * c * t ^ 18) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_03, v50_10, v50_11, v50_12, v50_13, v50_20, v50_21, v50_22, v50_23, v50_30, v50_31, v50_32, v50_33]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23, phase48_30, phase48_31, phase48_32, phase48_33]
  try simp only [star_one, star_neg]
  linear_combination ((-59408 / 75) * t ^ 2 + (152586 / 125) * t ^ 4 + (527749759 / 900000) * t ^ 6 + (-4189585963 / 1800000) * t ^ 8 + (152655067 / 120000) * t ^ 10 + (244624729 / 27000000) * t ^ 12 + (-23248513 / 27000000) * t ^ 14 + (8639111 / 5062500) * t ^ 18 + (14852 / 25) * c * t ^ 2 + (-650083 / 750) * c * t ^ 4 + (60193511 / 900000) * c * t ^ 6 + (390395947 / 1800000) * c * t ^ 8 + (-14358017 / 1800000) * c * t ^ 10 + (-495023 / 72000) * c * t ^ 12 + (11310719 / 1800000) * c * t ^ 14 + (14852 / 75) * c ^ 2 * t ^ 2 + (-265433 / 750) * c ^ 2 * t ^ 4 + (7518551 / 54000) * c ^ 2 * t ^ 6 + (1226707 / 75000) * c ^ 2 * t ^ 8 + (27451 / 30000) * c ^ 2 * t ^ 10 + (-4283 / 33750) * c ^ 2 * t ^ 12 + (10423 / 337500) * c ^ 2 * t ^ 14) * alpha_sq + ((-59408 / 75) * t ^ 2 + (186494 / 125) * t ^ 4 + (-79488277 / 112500) * t ^ 6 + (420191 / 56250) * t ^ 8 + (-141791 / 37500) * t ^ 10 + (10987 / 15625) * t ^ 12 + (57152 / 421875) * t ^ 14 + (-20164 / 1265625) * t ^ 18) * c_sq
theorem v51_34 (t : ℂ) : (momentPoly 51 z51 3 4).eval t = ((27004509 / 10) * t + (-197113713 / 25) * t ^ 3 + (19238351363 / 2500) * t ^ 5 + (-15836180884079 / 6000000) * t ^ 7 + (1877380873551 / 8000000) * t ^ 9 + (-36523354433 / 400000) * t ^ 11 + (-5189934959933 / 144000000) * t ^ 13 + (409404099401 / 18000000) * t ^ 15 + (-18163530139 / 9600000) * t ^ 17 + (-1719355273 / 10800000) * t ^ 19 + (8875968809 / 144000000) * t ^ 21 + (21779161297 / 432000000) * t ^ 25 + (-1000167 / 10) * c * t + (8404877 / 25) * c * t ^ 3 + (-12343891999 / 30000) * c * t ^ 5 + (7716422648251 / 36000000) * c * t ^ 7 + (-158962846617 / 4000000) * c * t ^ 9 + (1800140733 / 1600000) * c * t ^ 11 + (-45339174011 / 216000000) * c * t ^ 13 + (-280357049 / 1200000) * c * t ^ 15 + (306685793 / 54000000) * c * t ^ 17 + (-12426299179 / 648000000) * c * t ^ 19 + (2465909881 / 216000000) * c * t ^ 21 + (30119257 / 54000000) * c * t ^ 25 + (9001503 / 10) * alpha * t + (-10590703 / 5) * alpha * t ^ 3 + (7807240391 / 7500) * alpha * t ^ 5 + (4142826405491 / 6000000) * alpha * t ^ 7 + (-38509127754611 / 72000000) * alpha * t ^ 9 + (25504952057 / 3600000) * alpha * t ^ 11 + (13940588779363 / 432000000) * alpha * t ^ 13 + (-12827294453 / 720000) * alpha * t ^ 15 + (-35945775061 / 432000000) * alpha * t ^ 17 + (-18573869201 / 162000000) * alpha * t ^ 19 + (35541675977 / 432000000) * alpha * t ^ 21 + (-23098657007 / 1296000000) * alpha * t ^ 25 + (1000167 / 10) * alpha * c * t + (-6988093 / 25) * alpha * c * t ^ 3 + (7405949951 / 30000) * alpha * c * t ^ 5 + (-135644400421 / 2400000) * alpha * c * t ^ 7 + (-65996793923 / 7200000) * alpha * c * t ^ 9 + (-29196926581 / 14400000) * alpha * c * t ^ 11 + (89315019563 / 216000000) * alpha * c * t ^ 13 + (-2888293739 / 54000000) * alpha * c * t ^ 15 + (-119512267 / 18000000) * alpha * c * t ^ 17 + (382846147 / 72000000) * alpha * c * t ^ 19 + (-179740213 / 43200000) * alpha * c * t ^ 21 + (12334837 / 162000000) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_03, v50_04, v50_10, v50_11, v50_12, v50_13, v50_14, v50_20, v50_21, v50_22, v50_23, v50_24, v50_30, v50_31, v50_32, v50_33, v50_34]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24, phase48_30, phase48_31, phase48_32, phase48_33, phase48_34]
  try simp only [star_one, star_neg]
  linear_combination ((-1277289 / 250) * t ^ 3 + (176366621 / 6000) * t ^ 5 + (-2559159404243 / 72000000) * t ^ 7 + (36364454677 / 14400000) * t ^ 9 + (258745056979 / 28800000) * t ^ 11 + (192476866027 / 432000000) * t ^ 13 + (-429623331767 / 540000000) * t ^ 15 + (19616645027 / 270000000) * t ^ 17 + (1005876971 / 144000000) * t ^ 19 + (-2464393943 / 720000000) * t ^ 21 + (-380458871 / 270000000) * t ^ 25 + (3696011 / 750) * c * t ^ 3 + (-1312367171 / 90000) * c * t ^ 5 + (595703572277 / 43200000) * c * t ^ 7 + (-162411345119 / 43200000) * c * t ^ 9 + (-32537353471 / 144000000) * c * t ^ 11 + (-174105254129 / 1296000000) * c * t ^ 13 + (-2962756703 / 180000000) * c * t ^ 15 + (344321113 / 202500000) * c * t ^ 17 + (-2957866981 / 777600000) * c * t ^ 19 + (13888231231 / 6480000000) * c * t ^ 21 + (1037257 / 25312500) * c * t ^ 25 + (67928 / 375) * c ^ 2 * t ^ 3 + (-3626393 / 11250) * c ^ 2 * t ^ 5 + (1913184199 / 13500000) * c ^ 2 * t ^ 7 + (-55318111 / 13500000) * c ^ 2 * t ^ 9 + (-372881423 / 27000000) * c ^ 2 * t ^ 11 + (519774079 / 27000000) * c ^ 2 * t ^ 13 + (-19913 / 13500) * c ^ 2 * t ^ 15 + (7306 / 1265625) * c ^ 2 * t ^ 17 + (-23441 / 648000) * c ^ 2 * t ^ 19 + (126803 / 5400000) * c ^ 2 * t ^ 21) * alpha_sq + ((-135856 / 125) * t ^ 3 + (3945329 / 1875) * t ^ 5 + (-2503241911 / 2250000) * t ^ 7 + (8821347 / 125000) * t ^ 9 + (171400753 / 1500000) * t ^ 11 + (-135088033 / 1350000) * t ^ 13 + (143538781 / 16875000) * t ^ 15 + (69887 / 703125) * t ^ 17 + (-109217 / 1620000) * t ^ 19 + (-2179409 / 33750000) * t ^ 21 + (-41464 / 6328125) * t ^ 25 + (-135856 / 375) * alpha * t ^ 3 + (440797 / 1125) * alpha * t ^ 5 + (28698509 / 150000) * alpha * t ^ 7 + (-654584117 / 3375000) * alpha * t ^ 9 + (-24047497 / 2700000) * alpha * t ^ 11 + (-121603589 / 20250000) * alpha * t ^ 13 + (-204599953 / 16875000) * alpha * t ^ 15 + (-595619 / 6328125) * alpha * t ^ 17 + (-59329721 / 121500000) * alpha * t ^ 19 + (5020591 / 101250000) * alpha * t ^ 21 + (-41464 / 18984375) * alpha * t ^ 25) * c_sq
theorem v51_40 (t : ℂ) : (momentPoly 51 z51 4 0).eval t = ((-3243201 / 40000) * t ^ 4 + (3010977 / 20000) * t ^ 6 + (-9695989 / 240000) * t ^ 8 + (-5890249 / 180000) * t ^ 10 + (1387579 / 240000) * t ^ 16 + (-8201 / 3750) * c * t ^ 4 + (31433 / 7500) * c * t ^ 6 + (-313 / 1250) * c * t ^ 8 + (-40547 / 22500) * c * t ^ 10 + (146 / 5625) * c * t ^ 16 + (4684799 / 40000) * alpha * t ^ 4 + (-15000029 / 60000) * alpha * t ^ 6 + (11576537 / 80000) * alpha * t ^ 8 + (-392003 / 60000) * alpha * t ^ 10 + (-2279503 / 720000) * alpha * t ^ 16 + (46921 / 11250) * alpha * c * t ^ 4 + (-29731 / 7500) * alpha * c * t ^ 6 + (-4901 / 11250) * alpha * c * t ^ 8 + (16547 / 67500) * alpha * c * t ^ 10 + (-146 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_10, v50_20, v50_30, v50_40]
  try simp only [phase48_00, phase48_10, phase48_20, phase48_30, phase48_40]
  try simp only [star_one, star_neg]
  linear_combination ((10777 / 11250) * t ^ 4 + (-334933 / 45000) * t ^ 6 + (144613 / 15000) * t ^ 8 + (24947 / 67500) * t ^ 10 + (-13697 / 11250) * c * t ^ 4 + (26431 / 11250) * c * t ^ 6 + (1397 / 22500) * c * t ^ 8 + (-14209 / 22500) * c * t ^ 10 + (292 / 1125) * c ^ 2 * t ^ 4 + (-4408 / 16875) * c ^ 2 * t ^ 6 + (-4 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-501 / 625) * t ^ 4 + (1499 / 1875) * t ^ 6 + (-8 / 5625) * t ^ 8 + (568 / 16875) * t ^ 10 + (1331 / 5625) * alpha * t ^ 4 + (-1343 / 5625) * alpha * t ^ 6 + (-8 / 5625) * alpha * t ^ 8 + (568 / 16875) * alpha * t ^ 10) * c_sq
theorem v51_41 (t : ℂ) : (momentPoly 51 z51 4 1).eval t = ((-110286 / 25) * t ^ 3 + (30245447 / 3750) * t ^ 5 + (-6419467 / 1875) * t ^ 7 + (773881 / 3750) * t ^ 9 + (-830096 / 1875) * t ^ 11 + (3783 / 625) * t ^ 17 + (-25641 / 250) * c * t ^ 3 + (5236379 / 36000) * c * t ^ 5 + (-878557 / 30000) * c * t ^ 7 + (-317263 / 360000) * c * t ^ 9 + (-3544243 / 270000) * c * t ^ 11 + (33089 / 360000) * c * t ^ 17 + (-307857 / 125) * alpha * t ^ 3 + (1071573353 / 180000) * alpha * t ^ 5 + (-105502019 / 30000) * alpha * t ^ 7 + (-269815489 / 360000) * alpha * t ^ 9 + (209232491 / 270000) * alpha * t ^ 11 + (710249 / 216000) * alpha * t ^ 17 + (4818 / 25) * alpha * c * t ^ 3 + (-4324577 / 11250) * alpha * c * t ^ 5 + (1102357 / 5625) * alpha * c * t ^ 7 + (-52771 / 11250) * alpha * c * t ^ 9 + (1768 / 16875) * alpha * c * t ^ 11 + (5033 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_10, v50_11, v50_20, v50_21, v50_30, v50_31, v50_40, v50_41]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21, phase48_30, phase48_31, phase48_40, phase48_41]
  try simp only [star_one, star_neg]
  linear_combination ((34749 / 1000) * t ^ 3 + (-121908983 / 720000) * t ^ 5 + (201142499 / 1800000) * t ^ 7 + (124276523 / 7200000) * t ^ 9 + (292181 / 1800000) * t ^ 11 + (-1511429 / 7200000) * t ^ 17 + (-33517 / 1000) * c * t ^ 3 + (50918327 / 720000) * c * t ^ 5 + (-59819411 / 1800000) * c * t ^ 7 + (-79445441 / 21600000) * c * t ^ 9 + (-3332861 / 16200000) * c * t ^ 11 + (450181 / 7200000) * c * t ^ 17 + (-154 / 125) * c ^ 2 * t ^ 3 + (23737 / 33750) * c ^ 2 * t ^ 5 + (66763 / 168750) * c ^ 2 * t ^ 7 + (964 / 28125) * c ^ 2 * t ^ 9 + (10988 / 253125) * c ^ 2 * t ^ 11 + (292 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((2488 / 5625) * t ^ 5 + (-104 / 1125) * t ^ 7 + (-1168 / 5625) * t ^ 9 + (-32 / 225) * t ^ 11 + (-616 / 125) * alpha * t ^ 3 + (66298 / 16875) * alpha * t ^ 5 + (9968 / 28125) * alpha * t ^ 7 + (-1028 / 84375) * alpha * t ^ 9 + (81718 / 253125) * alpha * t ^ 11 + (-1168 / 253125) * alpha * t ^ 17) * c_sq
theorem v51_42 (t : ℂ) : (momentPoly 51 z51 4 2).eval t = ((-13140307 / 75) * t ^ 2 + (508396261 / 1000) * t ^ 4 + (-3505329624701 / 7200000) * t ^ 6 + (214345736831 / 1440000) * t ^ 8 + (14058080989 / 2880000) * t ^ 10 + (2417624531 / 14400000) * t ^ 12 + (-2560387837 / 10800000) * t ^ 14 + (158655023 / 43200000) * t ^ 18 + (-328581467 / 43200000) * t ^ 20 + (-237632 / 75) * c * t ^ 2 + (749724 / 125) * c * t ^ 4 + (-207198049 / 75000) * c * t ^ 6 + (-12798599 / 180000) * c * t ^ 8 + (37530041 / 225000) * c * t ^ 10 + (-275669371 / 1800000) * c * t ^ 12 + (-729841 / 84375) * c * t ^ 14 + (-394499 / 337500) * c * t ^ 18 + (12397 / 360000) * c * t ^ 20 + (-2847871 / 25) * alpha * t ^ 2 + (971058337 / 3000) * alpha * t ^ 4 + (-723067562161 / 2400000) * alpha * t ^ 6 + (14311026729 / 160000) * alpha * t ^ 8 + (-246509743 / 960000) * alpha * t ^ 10 + (94437944279 / 43200000) * alpha * t ^ 12 + (445599823 / 3600000) * alpha * t ^ 14 + (779951723 / 14400000) * alpha * t ^ 18 + (-1920732181 / 43200000) * alpha * t ^ 20 + (-237632 / 225) * alpha * c * t ^ 2 + (2327572 / 1125) * alpha * c * t ^ 4 + (-253880017 / 225000) * alpha * c * t ^ 6 + (9400913 / 60000) * alpha * c * t ^ 8 + (11300171 / 225000) * alpha * c * t ^ 10 + (-535386683 / 5400000) * alpha * c * t ^ 12 + (1887062 / 253125) * alpha * c * t ^ 14 + (240253 / 1012500) * alpha * c * t ^ 18 + (-83603 / 1080000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_10, v50_11, v50_12, v50_20, v50_21, v50_22, v50_30, v50_31, v50_32, v50_40, v50_41, v50_42]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22, phase48_30, phase48_31, phase48_32, phase48_40, phase48_41, phase48_42]
  try simp only [star_one, star_neg]
  linear_combination ((118816 / 225) * t ^ 2 + (-5105653 / 5625) * t ^ 4 + (115803521 / 270000) * t ^ 6 + (-673082231 / 10800000) * t ^ 8 + (1225499549 / 27000000) * t ^ 10 + (-4005466337 / 108000000) * t ^ 12 + (21771559 / 3000000) * t ^ 14 + (-115387 / 250000) * t ^ 18 + (302415511 / 108000000) * t ^ 20 + (-29704 / 75) * c * t ^ 2 + (3921568 / 5625) * c * t ^ 4 + (-173587769 / 450000) * c * t ^ 6 + (112554683 / 1800000) * c * t ^ 8 + (100520797 / 1350000) * c * t ^ 10 + (-60432059 / 1200000) * c * t ^ 12 + (-1109 / 225) * c * t ^ 14 + (-25016 / 84375) * c * t ^ 18 + (-26003 / 2160000) * c * t ^ 20 + (-29704 / 225) * c ^ 2 * t ^ 2 + (26313 / 125) * c ^ 2 * t ^ 4 + (-29127149 / 675000) * c ^ 2 * t ^ 6 + (-7181707 / 202500) * c ^ 2 * t ^ 8 + (-239219 / 1125000) * c ^ 2 * t ^ 10 + (94004 / 1265625) * c ^ 2 * t ^ 12 + (-238063 / 7593750) * c ^ 2 * t ^ 14 + (-148946 / 3796875) * c ^ 2 * t ^ 18 + (584 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((59408 / 225) * t ^ 2 + (-650524 / 1875) * t ^ 4 + (-78759653 / 1350000) * t ^ 6 + (19416817 / 135000) * t ^ 8 + (16386877 / 13500000) * t ^ 10 + (-11734621 / 3375000) * t ^ 12 + (544712 / 1265625) * t ^ 14 + (5118031 / 40500000) * t ^ 18 + (1168 / 1265625) * t ^ 20 + (-59408 / 225) * alpha * t ^ 2 + (3096212 / 5625) * alpha * t ^ 4 + (-151459529 / 450000) * alpha * t ^ 6 + (11065433 / 225000) * alpha * t ^ 8 + (-5174293 / 1500000) * alpha * t ^ 10 + (33958423 / 10125000) * alpha * t ^ 12 + (78856 / 421875) * alpha * t ^ 14 + (441403 / 13500000) * alpha * t ^ 18 + (-1168 / 1265625) * alpha * t ^ 20) * c_sq
theorem v51_43 (t : ℂ) : (momentPoly 51 z51 4 3).eval t = ((27004509 / 10) * t + (-197113713 / 25) * t ^ 3 + (19238351363 / 2500) * t ^ 5 + (-15836180884079 / 6000000) * t ^ 7 + (1877380873551 / 8000000) * t ^ 9 + (-36523354433 / 400000) * t ^ 11 + (-5189934959933 / 144000000) * t ^ 13 + (409404099401 / 18000000) * t ^ 15 + (-18163530139 / 9600000) * t ^ 17 + (-1719355273 / 10800000) * t ^ 19 + (8875968809 / 144000000) * t ^ 21 + (21779161297 / 432000000) * t ^ 25 + (-1000167 / 10) * c * t + (8404877 / 25) * c * t ^ 3 + (-12343891999 / 30000) * c * t ^ 5 + (7716422648251 / 36000000) * c * t ^ 7 + (-158962846617 / 4000000) * c * t ^ 9 + (1800140733 / 1600000) * c * t ^ 11 + (-45339174011 / 216000000) * c * t ^ 13 + (-280357049 / 1200000) * c * t ^ 15 + (306685793 / 54000000) * c * t ^ 17 + (-12426299179 / 648000000) * c * t ^ 19 + (2465909881 / 216000000) * c * t ^ 21 + (30119257 / 54000000) * c * t ^ 25 + (-9001503 / 10) * alpha * t + (10590703 / 5) * alpha * t ^ 3 + (-7807240391 / 7500) * alpha * t ^ 5 + (-4142826405491 / 6000000) * alpha * t ^ 7 + (38509127754611 / 72000000) * alpha * t ^ 9 + (-25504952057 / 3600000) * alpha * t ^ 11 + (-13940588779363 / 432000000) * alpha * t ^ 13 + (12827294453 / 720000) * alpha * t ^ 15 + (35945775061 / 432000000) * alpha * t ^ 17 + (18573869201 / 162000000) * alpha * t ^ 19 + (-35541675977 / 432000000) * alpha * t ^ 21 + (23098657007 / 1296000000) * alpha * t ^ 25 + (-1000167 / 10) * alpha * c * t + (6988093 / 25) * alpha * c * t ^ 3 + (-7405949951 / 30000) * alpha * c * t ^ 5 + (135644400421 / 2400000) * alpha * c * t ^ 7 + (65996793923 / 7200000) * alpha * c * t ^ 9 + (29196926581 / 14400000) * alpha * c * t ^ 11 + (-89315019563 / 216000000) * alpha * c * t ^ 13 + (2888293739 / 54000000) * alpha * c * t ^ 15 + (119512267 / 18000000) * alpha * c * t ^ 17 + (-382846147 / 72000000) * alpha * c * t ^ 19 + (179740213 / 43200000) * alpha * c * t ^ 21 + (-12334837 / 162000000) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_03, v50_10, v50_11, v50_12, v50_13, v50_20, v50_21, v50_22, v50_23, v50_30, v50_31, v50_32, v50_33, v50_40, v50_41, v50_42, v50_43]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23, phase48_30, phase48_31, phase48_32, phase48_33, phase48_40, phase48_41, phase48_42, phase48_43]
  try simp only [star_one, star_neg]
  linear_combination ((-1277289 / 250) * t ^ 3 + (176366621 / 6000) * t ^ 5 + (-2559159404243 / 72000000) * t ^ 7 + (36364454677 / 14400000) * t ^ 9 + (258745056979 / 28800000) * t ^ 11 + (192476866027 / 432000000) * t ^ 13 + (-429623331767 / 540000000) * t ^ 15 + (19616645027 / 270000000) * t ^ 17 + (1005876971 / 144000000) * t ^ 19 + (-2464393943 / 720000000) * t ^ 21 + (-380458871 / 270000000) * t ^ 25 + (3696011 / 750) * c * t ^ 3 + (-1312367171 / 90000) * c * t ^ 5 + (595703572277 / 43200000) * c * t ^ 7 + (-162411345119 / 43200000) * c * t ^ 9 + (-32537353471 / 144000000) * c * t ^ 11 + (-174105254129 / 1296000000) * c * t ^ 13 + (-2962756703 / 180000000) * c * t ^ 15 + (344321113 / 202500000) * c * t ^ 17 + (-2957866981 / 777600000) * c * t ^ 19 + (13888231231 / 6480000000) * c * t ^ 21 + (1037257 / 25312500) * c * t ^ 25 + (67928 / 375) * c ^ 2 * t ^ 3 + (-3626393 / 11250) * c ^ 2 * t ^ 5 + (1913184199 / 13500000) * c ^ 2 * t ^ 7 + (-55318111 / 13500000) * c ^ 2 * t ^ 9 + (-372881423 / 27000000) * c ^ 2 * t ^ 11 + (519774079 / 27000000) * c ^ 2 * t ^ 13 + (-19913 / 13500) * c ^ 2 * t ^ 15 + (7306 / 1265625) * c ^ 2 * t ^ 17 + (-23441 / 648000) * c ^ 2 * t ^ 19 + (126803 / 5400000) * c ^ 2 * t ^ 21) * alpha_sq + ((-135856 / 125) * t ^ 3 + (3945329 / 1875) * t ^ 5 + (-2503241911 / 2250000) * t ^ 7 + (8821347 / 125000) * t ^ 9 + (171400753 / 1500000) * t ^ 11 + (-135088033 / 1350000) * t ^ 13 + (143538781 / 16875000) * t ^ 15 + (69887 / 703125) * t ^ 17 + (-109217 / 1620000) * t ^ 19 + (-2179409 / 33750000) * t ^ 21 + (-41464 / 6328125) * t ^ 25 + (135856 / 375) * alpha * t ^ 3 + (-440797 / 1125) * alpha * t ^ 5 + (-28698509 / 150000) * alpha * t ^ 7 + (654584117 / 3375000) * alpha * t ^ 9 + (24047497 / 2700000) * alpha * t ^ 11 + (121603589 / 20250000) * alpha * t ^ 13 + (204599953 / 16875000) * alpha * t ^ 15 + (595619 / 6328125) * alpha * t ^ 17 + (59329721 / 121500000) * alpha * t ^ 19 + (-5020591 / 101250000) * alpha * t ^ 21 + (41464 / 18984375) * alpha * t ^ 25) * c_sq
theorem v51_44 (t : ℂ) : (momentPoly 51 z51 4 4).eval t = (153025551 + (-2849863632 / 5) * t ^ 2 + (391366436377 / 500) * t ^ 4 + (-17337727513531 / 37500) * t ^ 6 + (68691145469763349 / 720000000) * t ^ 8 + (-164628672652487 / 60000000) * t ^ 10 + (542265039770347 / 144000000) * t ^ 12 + (-1017458178131 / 120000000) * t ^ 14 + (43263398118173 / 320000000) * t ^ 16 + (182048624411 / 40000000) * t ^ 18 + (-16442660211659 / 2160000000) * t ^ 20 + (2605286809709 / 360000000) * t ^ 22 + (-15306818994049 / 4320000000) * t ^ 24 + (226075511771 / 3240000000) * t ^ 26 + (329087827501 / 25920000000) * t ^ 32 + (133273472 / 375) * c * t ^ 4 + (-1927192456 / 1875) * c * t ^ 6 + (696103678862 / 703125) * c * t ^ 8 + (-302076804821 / 937500) * c * t ^ 10 + (-1516468717 / 112500) * c * t ^ 12 + (679253621623 / 16875000) * c * t ^ 14 + (-125294884783 / 5625000) * c * t ^ 16 + (3366750283 / 8437500) * c * t ^ 18 + (-3331754677 / 12656250) * c * t ^ 20 + (628447111 / 16875000) * c * t ^ 22 + (-18805513 / 16875000) * c * t ^ 24 + (-730863431 / 25312500) * c * t ^ 26 + (2939272 / 6328125) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z51, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v50_00, v50_01, v50_02, v50_03, v50_04, v50_10, v50_11, v50_12, v50_13, v50_14, v50_20, v50_21, v50_22, v50_23, v50_24, v50_30, v50_31, v50_32, v50_33, v50_34, v50_40, v50_41, v50_42, v50_43, v50_44]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24, phase48_30, phase48_31, phase48_32, phase48_33, phase48_34, phase48_40, phase48_41, phase48_42, phase48_43, phase48_44]
  try simp only [star_one, star_neg]
  linear_combination ((-5176864 / 25) * t ^ 2 + (59219976 / 125) * t ^ 4 + (2506689323 / 37500) * t ^ 6 + (-10678486201121 / 9000000) * t ^ 8 + (57277437207259 / 45000000) * t ^ 10 + (-54303048312079 / 135000000) * t ^ 12 + (-86166141367 / 4500000) * t ^ 14 + (251139576943 / 180000000) * t ^ 16 + (497857081547 / 540000000) * t ^ 18 + (-100120051279 / 90000000) * t ^ 20 + (-575279516707 / 1350000000) * t ^ 22 + (325696839761 / 900000000) * t ^ 24 + (-107104544983 / 8100000000) * t ^ 26 + (-9851548903 / 4050000000) * t ^ 32 + (3882648 / 25) * c * t ^ 2 + (-378454442 / 1125) * c * t ^ 4 + (2440324231 / 18750) * c * t ^ 6 + (6161053706887 / 45000000) * c * t ^ 8 + (-24455149475519 / 270000000) * c * t ^ 10 + (-87285290689 / 54000000) * c * t ^ 12 + (5515927996433 / 540000000) * c * t ^ 14 + (-619295611463 / 162000000) * c * t ^ 16 + (-46988163521 / 324000000) * c * t ^ 18 + (9203356489 / 2430000000) * c * t ^ 20 + (813598957 / 100000000) * c * t ^ 22 + (-152391167 / 4050000000) * c * t ^ 24 + (-48176362817 / 8100000000) * c * t ^ 26 + (95861191 / 3037500000) * c * t ^ 32 + (1294216 / 25) * c ^ 2 * t ^ 2 + (-154525342 / 1125) * c ^ 2 * t ^ 4 + (1901296313 / 16875) * c ^ 2 * t ^ 6 + (-4193063691769 / 202500000) * c ^ 2 * t ^ 8 + (-369670967531 / 67500000) * c ^ 2 * t ^ 10 + (-45394353611 / 45000000) * c ^ 2 * t ^ 12 + (51696476863 / 405000000) * c ^ 2 * t ^ 14 + (-1085019761 / 101250000) * c ^ 2 * t ^ 16 + (-378136129 / 101250000) * c ^ 2 * t ^ 18 + (334897709 / 81000000) * c ^ 2 * t ^ 20 + (-5260419817 / 2025000000) * c ^ 2 * t ^ 22 + (16676849 / 759375000) * c ^ 2 * t ^ 24 + (59911867 / 4556250000) * c ^ 2 * t ^ 26 + (85264 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((-5176864 / 25) * t ^ 2 + (217139912 / 375) * t ^ 4 + (-15071355244 / 28125) * t ^ 6 + (2759862533111 / 16875000) * t ^ 8 + (-4982748937 / 1875000) * t ^ 10 + (23684142169 / 6750000) * t ^ 12 + (-13061559929 / 33750000) * t ^ 14 + (-1226426177 / 8437500) * t ^ 16 + (58632103 / 4218750) * t ^ 18 + (-928897741 / 101250000) * t ^ 20 + (217317503 / 18750000) * t ^ 22 + (-1045169 / 63281250) * t ^ 24 + (84403639 / 189843750) * t ^ 26 + (-341056 / 94921875) * t ^ 32) * c_sq
#print axioms v51_00
#print axioms v51_11
#print axioms v51_22
#print axioms v51_33
#print axioms v51_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v52_02 (t : ℂ) : (momentPoly 52 z52 0 2).eval t = ((-115 / 24) * t ^ 2 + (131 / 24) * t ^ 4 + (593 / 120) * alpha * t ^ 2 + (-171 / 40) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02]
  try simp only [phase48_00, phase48_01, phase48_02]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 50) * t ^ 2 + (-4 / 225) * c * t ^ 2 + (-1 / 450) * c ^ 2 * t ^ 2) * alpha_sq + ((1 / 225) * t ^ 2 + (1 / 225) * alpha * t ^ 2) * c_sq
theorem v52_03 (t : ℂ) : (momentPoly 52 z52 0 3).eval t = ((-126 / 5) * t ^ 3 + (116 / 5) * t ^ 5 + 2 * t ^ 9 + (4847 / 300) * alpha * t ^ 3 + (-11531 / 600) * alpha * t ^ 5 + (7111 / 1800) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_03]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03]
  try simp only [star_one, star_neg]
  linear_combination ((767 / 2000) * t ^ 3 + (-4901 / 6000) * t ^ 5 + (-6839 / 18000) * c * t ^ 3 + (5879 / 18000) * c * t ^ 5 + (-4 / 1125) * c ^ 2 * t ^ 3 + (-1 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((16 / 1125) * alpha * t ^ 3 + (4 / 1125) * alpha * t ^ 5) * c_sq
theorem v52_04 (t : ℂ) : (momentPoly 52 z52 0 4).eval t = ((-188863 / 960) * t ^ 4 + (248601 / 800) * t ^ 6 + (-874589 / 9600) * t ^ 8 + (-209801 / 7200) * t ^ 10 + (6145 / 1152) * t ^ 16 + (-3086233 / 24000) * alpha * t ^ 4 + (3272393 / 12000) * alpha * t ^ 6 + (-2413541 / 16000) * alpha * t ^ 8 + (144557 / 36000) * alpha * t ^ 10 + (173441 / 48000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_03, v51_04]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04]
  try simp only [star_one, star_neg]
  linear_combination ((9329 / 5625) * t ^ 4 + (-610201 / 45000) * t ^ 6 + (165929 / 15000) * t ^ 8 + (793 / 2500) * t ^ 10 + (-3353 / 1875) * c * t ^ 4 + (12856 / 5625) * c * t ^ 6 + (1981 / 22500) * c * t ^ 8 + (-39091 / 67500) * c * t ^ 10 + (146 / 1125) * c ^ 2 * t ^ 4 + (-2206 / 16875) * c ^ 2 * t ^ 6 + (-2 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-573 / 1250) * t ^ 4 + (1591 / 3750) * t ^ 6 + (-4 / 5625) * t ^ 8 + (284 / 16875) * t ^ 10 + (-683 / 11250) * alpha * t ^ 4 + (1067 / 11250) * alpha * t ^ 6 + (4 / 5625) * alpha * t ^ 8 + (-284 / 16875) * alpha * t ^ 10) * c_sq
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
theorem v52_12 (t : ℂ) : (momentPoly 52 z52 1 2).eval t = (103 * t + (-2037 / 20) * t ^ 3 + (11 / 60) * t ^ 5 + (103 / 3) * alpha * t + (-4943 / 180) * alpha * t ^ 3 + (-1157 / 180) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_10, v51_11, v51_12]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12]
  try simp only [star_one, star_neg]
  linear_combination ((-767 / 6000) * t ^ 3 + (4901 / 18000) * t ^ 5 + (6839 / 54000) * c * t ^ 3 + (-5879 / 54000) * c * t ^ 5 + (4 / 3375) * c ^ 2 * t ^ 3 + (1 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((-8 / 1125) * t ^ 3 + (-2 / 1125) * t ^ 5 + (-8 / 3375) * alpha * t ^ 3 + (-2 / 3375) * alpha * t ^ 5) * c_sq
theorem v52_13 (t : ℂ) : (momentPoly 52 z52 1 3).eval t = ((-5865 / 8) * t ^ 2 + (155029 / 100) * t ^ 4 + (-490061 / 600) * t ^ 6 + (443 / 900) * t ^ 10 + (30243 / 40) * alpha * t ^ 2 + (-412513 / 300) * alpha * t ^ 4 + (367379 / 600) * alpha * t ^ 6 + (6803 / 900) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_03, v51_10, v51_11, v51_12, v51_13]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13]
  try simp only [star_one, star_neg]
  linear_combination ((153 / 50) * t ^ 2 + (-28399 / 10000) * t ^ 4 + (179 / 3750) * t ^ 6 + (-793 / 10000) * t ^ 10 + (-68 / 25) * c * t ^ 2 + (114853 / 45000) * c * t ^ 4 + (-899 / 10000) * c * t ^ 6 + (39091 / 270000) * c * t ^ 10 + (-17 / 50) * c ^ 2 * t ^ 2 + (5177 / 18000) * c ^ 2 * t ^ 4 + (253 / 6000) * c ^ 2 * t ^ 6) * alpha_sq + ((17 / 25) * t ^ 2 + (-11141 / 22500) * t ^ 4 + (-3859 / 22500) * t ^ 6 + (71 / 16875) * t ^ 10 + (17 / 25) * alpha * t ^ 2 + (-16981 / 22500) * alpha * t ^ 4 + (1981 / 22500) * alpha * t ^ 6 + (71 / 16875) * alpha * t ^ 10) * c_sq
theorem v52_14 (t : ℂ) : (momentPoly 52 z52 1 4).eval t = ((-25452 / 5) * t ^ 3 + (1166401 / 125) * t ^ 5 + (-1464506 / 375) * t ^ 7 + (45619 / 375) * t ^ 9 + (-522064 / 1125) * t ^ 11 + (7816 / 1125) * t ^ 17 + (489547 / 150) * alpha * t ^ 3 + (-128474101 / 18000) * alpha * t ^ 5 + (11747527 / 3000) * alpha * t ^ 7 + (8733863 / 12000) * alpha * t ^ 9 + (-20697131 / 27000) * alpha * t ^ 11 + (-228449 / 108000) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_03, v51_04, v51_10, v51_11, v51_12, v51_13, v51_14]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14]
  try simp only [star_one, star_neg]
  linear_combination ((77467 / 1000) * t ^ 3 + (-840586163 / 3600000) * t ^ 5 + (79511777 / 600000) * t ^ 7 + (148831531 / 7200000) * t ^ 9 + (3470591 / 5400000) * t ^ 11 + (-5178511 / 21600000) * t ^ 17 + (-690739 / 9000) * c * t ^ 3 + (1438640281 / 10800000) * c * t ^ 5 + (-279996457 / 5400000) * c * t ^ 7 + (-3527571 / 800000) * c * t ^ 9 + (-10772477 / 16200000) * c * t ^ 11 + (6021677 / 64800000) * c * t ^ 17 + (-808 / 1125) * c ^ 2 * t ^ 3 + (36236 / 84375) * c ^ 2 * t ^ 5 + (19186 / 84375) * c ^ 2 * t ^ 7 + (1444 / 84375) * c ^ 2 * t ^ 9 + (5636 / 253125) * c ^ 2 * t ^ 11 + (146 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((512 / 1875) * t ^ 5 + (-184 / 1875) * t ^ 7 + (-584 / 5625) * t ^ 9 + (-16 / 225) * t ^ 11 + (3232 / 1125) * alpha * t ^ 3 + (-203746 / 84375) * alpha * t ^ 5 + (-6557 / 28125) * alpha * t ^ 7 + (1106 / 84375) * alpha * t ^ 9 + (-39091 / 253125) * alpha * t ^ 11 + (584 / 253125) * alpha * t ^ 17) * c_sq
theorem v52_20 (t : ℂ) : (momentPoly 52 z52 2 0).eval t = ((-115 / 24) * t ^ 2 + (131 / 24) * t ^ 4 + (-593 / 120) * alpha * t ^ 2 + (171 / 40) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_10, v51_20]
  try simp only [phase48_00, phase48_10, phase48_20]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 50) * t ^ 2 + (-4 / 225) * c * t ^ 2 + (-1 / 450) * c ^ 2 * t ^ 2) * alpha_sq + ((1 / 225) * t ^ 2 + (-1 / 225) * alpha * t ^ 2) * c_sq
theorem v52_21 (t : ℂ) : (momentPoly 52 z52 2 1).eval t = (103 * t + (-2037 / 20) * t ^ 3 + (11 / 60) * t ^ 5 + (-103 / 3) * alpha * t + (4943 / 180) * alpha * t ^ 3 + (1157 / 180) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_10, v51_11, v51_20, v51_21]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21]
  try simp only [star_one, star_neg]
  linear_combination ((-767 / 6000) * t ^ 3 + (4901 / 18000) * t ^ 5 + (6839 / 54000) * c * t ^ 3 + (-5879 / 54000) * c * t ^ 5 + (4 / 3375) * c ^ 2 * t ^ 3 + (1 / 3375) * c ^ 2 * t ^ 5) * alpha_sq + ((-8 / 1125) * t ^ 3 + (-2 / 1125) * t ^ 5 + (8 / 3375) * alpha * t ^ 3 + (2 / 3375) * alpha * t ^ 5) * c_sq
theorem v52_22 (t : ℂ) : (momentPoly 52 z52 2 2).eval t = (5356 + (-10336) * t ^ 2 + (17731993 / 3600) * t ^ 4 + (42487 / 1800) * t ^ 6 + (117433 / 3600) * t ^ 8) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_10, v51_11, v51_12, v51_20, v51_21, v51_22]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22]
  try simp only [star_one, star_neg]
  linear_combination ((-102 / 25) * t ^ 2 + (8731 / 2700) * t ^ 4 + (601609 / 135000) * t ^ 6 + (-165929 / 45000) * t ^ 8 + (272 / 75) * c * t ^ 2 + (-18947 / 6750) * c * t ^ 4 + (-43333 / 67500) * c * t ^ 6 + (-1981 / 67500) * c * t ^ 8 + (34 / 75) * c ^ 2 * t ^ 2 + (-5761 / 13500) * c ^ 2 * t ^ 4 + (-2561 / 202500) * c ^ 2 * t ^ 6 + (2 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((-136 / 75) * t ^ 2 + (6053 / 3375) * t ^ 4 + (-649 / 16875) * t ^ 6 + (-8 / 16875) * t ^ 8) * c_sq
theorem v52_23 (t : ℂ) : (momentPoly 52 z52 2 3).eval t = (15760 * t + (-617211 / 20) * t ^ 3 + (60240357 / 4000) * t ^ 5 + (-888901 / 4800) * t ^ 7 + (5269403 / 24000) * t ^ 9 + (3500423 / 72000) * t ^ 11 + (-977981 / 24000) * t ^ 13 + (15760 / 3) * alpha * t + (-499243 / 60) * alpha * t ^ 3 + (2544497 / 2400) * alpha * t ^ 5 + (5850383 / 2880) * alpha * t ^ 7 + (-539089 / 14400) * alpha * t ^ 9 + (-137873 / 8640) * alpha * t ^ 11 + (1286501 / 43200) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_03, v51_10, v51_11, v51_12, v51_13, v51_20, v51_21, v51_22, v51_23]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23]
  try simp only [star_one, star_neg]
  linear_combination ((-77467 / 2000) * t ^ 3 + (10683007 / 90000) * t ^ 5 + (-7241963 / 112500) * t ^ 7 + (-3722489 / 225000) * t ^ 9 + (436217 / 1350000) * t ^ 11 + (1719913 / 1350000) * t ^ 13 + (690739 / 18000) * c * t ^ 3 + (-739651 / 10800) * c * t ^ 5 + (13323509 / 450000) * c * t ^ 7 + (243883 / 1350000) * c * t ^ 9 + (916199 / 2025000) * c * t ^ 11 + (39091 / 2025000) * c * t ^ 13 + (404 / 1125) * c ^ 2 * t ^ 3 + (-12791 / 45000) * c ^ 2 * t ^ 5 + (-14027 / 270000) * c ^ 2 * t ^ 7 + (409 / 135000) * c ^ 2 * t ^ 9 + (-4109 / 270000) * c ^ 2 * t ^ 11) * alpha_sq + ((-808 / 375) * t ^ 3 + (8449 / 4500) * t ^ 5 + (14207 / 75000) * t ^ 7 + (-1492 / 28125) * t ^ 9 + (54179 / 675000) * t ^ 11 + (142 / 84375) * t ^ 13 + (-808 / 1125) * alpha * t ^ 3 + (7319 / 22500) * alpha * t ^ 5 + (68927 / 225000) * alpha * t ^ 7 + (4348 / 84375) * alpha * t ^ 9 + (30179 / 2025000) * alpha * t ^ 11 + (142 / 253125) * alpha * t ^ 13) * c_sq
theorem v52_24 (t : ℂ) : (momentPoly 52 z52 2 4).eval t = ((-1777325 / 12) * t ^ 2 + (3638483 / 8) * t ^ 4 + (-664562100241 / 1440000) * t ^ 6 + (216967691203 / 1440000) * t ^ 8 + (529838381 / 115200) * t ^ 10 + (-2415768311 / 8640000) * t ^ 12 + (-417638549 / 2160000) * t ^ 14 + (233485771 / 8640000) * t ^ 18 + (-195987611 / 8640000) * t ^ 20 + (1832963 / 12) * alpha * t ^ 2 + (-10093175 / 24) * alpha * t ^ 4 + (21776586007 / 57600) * alpha * t ^ 6 + (-10373193731 / 96000) * alpha * t ^ 8 + (8298549 / 12800) * alpha * t ^ 10 + (-4651916699 / 1728000) * alpha * t ^ 12 + (-65946433 / 432000) * alpha * t ^ 14 + (-20318381 / 345600) * alpha * t ^ 18 + (26957723 / 576000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_03, v51_04, v51_10, v51_11, v51_12, v51_13, v51_14, v51_20, v51_21, v51_22, v51_23, v51_24]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24]
  try simp only [star_one, star_neg]
  linear_combination ((3091 / 5) * t ^ 2 + (-28399 / 25) * t ^ 4 + (1428947597 / 2700000) * t ^ 6 + (-1122687961 / 18000000) * t ^ 8 + (195804803 / 2250000) * t ^ 10 + (-13193959507 / 324000000) * t ^ 12 + (256291901 / 81000000) * t ^ 14 + (-121214971 / 81000000) * t ^ 18 + (349443863 / 108000000) * t ^ 20 + (-24728 / 45) * c * t ^ 2 + (229706 / 225) * c * t ^ 4 + (-1351038163 / 2700000) * c * t ^ 6 + (110153093 / 5400000) * c * t ^ 8 + (69414569 / 1080000) * c * t ^ 10 + (-559148443 / 10800000) * c * t ^ 12 + (-1483951 / 337500) * c * t ^ 14 + (-327701 / 1800000) * c * t ^ 18 + (-35603 / 2160000) * c * t ^ 20 + (-3091 / 45) * c ^ 2 * t ^ 2 + (5177 / 45) * c ^ 2 * t ^ 4 + (-38954717 / 1350000) * c ^ 2 * t ^ 6 + (-178143229 / 10125000) * c ^ 2 * t ^ 8 + (89239 / 6750000) * c ^ 2 * t ^ 10 + (353147 / 5062500) * c ^ 2 * t ^ 12 + (-303227 / 15187500) * c ^ 2 * t ^ 14 + (-74327 / 3796875) * c ^ 2 * t ^ 18 + (292 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((6182 / 45) * t ^ 2 + (-44564 / 225) * t ^ 4 + (-24265957 / 2700000) * t ^ 6 + (480237529 / 6750000) * t ^ 8 + (7046941 / 27000000) * t ^ 10 + (-39533167 / 20250000) * t ^ 12 + (295424 / 1265625) * t ^ 14 + (5477519 / 81000000) * t ^ 18 + (584 / 1265625) * t ^ 20 + (6182 / 45) * alpha * t ^ 2 + (-67924 / 225) * alpha * t ^ 4 + (527574107 / 2700000) * alpha * t ^ 6 + (-7701413 / 250000) * alpha * t ^ 8 + (53113501 / 27000000) * alpha * t ^ 10 + (-38095727 / 20250000) * alpha * t ^ 12 + (-95216 / 1265625) * alpha * t ^ 14 + (-964721 / 81000000) * alpha * t ^ 18 + (584 / 1265625) * alpha * t ^ 20) * c_sq
theorem v52_30 (t : ℂ) : (momentPoly 52 z52 3 0).eval t = ((-126 / 5) * t ^ 3 + (116 / 5) * t ^ 5 + 2 * t ^ 9 + (-4847 / 300) * alpha * t ^ 3 + (11531 / 600) * alpha * t ^ 5 + (-7111 / 1800) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_10, v51_20, v51_30]
  try simp only [phase48_00, phase48_10, phase48_20, phase48_30]
  try simp only [star_one, star_neg]
  linear_combination ((767 / 2000) * t ^ 3 + (-4901 / 6000) * t ^ 5 + (-6839 / 18000) * c * t ^ 3 + (5879 / 18000) * c * t ^ 5 + (-4 / 1125) * c ^ 2 * t ^ 3 + (-1 / 1125) * c ^ 2 * t ^ 5) * alpha_sq + ((-16 / 1125) * alpha * t ^ 3 + (-4 / 1125) * alpha * t ^ 5) * c_sq
theorem v52_31 (t : ℂ) : (momentPoly 52 z52 3 1).eval t = ((-5865 / 8) * t ^ 2 + (155029 / 100) * t ^ 4 + (-490061 / 600) * t ^ 6 + (443 / 900) * t ^ 10 + (-30243 / 40) * alpha * t ^ 2 + (412513 / 300) * alpha * t ^ 4 + (-367379 / 600) * alpha * t ^ 6 + (-6803 / 900) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_10, v51_11, v51_20, v51_21, v51_30, v51_31]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21, phase48_30, phase48_31]
  try simp only [star_one, star_neg]
  linear_combination ((153 / 50) * t ^ 2 + (-28399 / 10000) * t ^ 4 + (179 / 3750) * t ^ 6 + (-793 / 10000) * t ^ 10 + (-68 / 25) * c * t ^ 2 + (114853 / 45000) * c * t ^ 4 + (-899 / 10000) * c * t ^ 6 + (39091 / 270000) * c * t ^ 10 + (-17 / 50) * c ^ 2 * t ^ 2 + (5177 / 18000) * c ^ 2 * t ^ 4 + (253 / 6000) * c ^ 2 * t ^ 6) * alpha_sq + ((17 / 25) * t ^ 2 + (-11141 / 22500) * t ^ 4 + (-3859 / 22500) * t ^ 6 + (71 / 16875) * t ^ 10 + (-17 / 25) * alpha * t ^ 2 + (16981 / 22500) * alpha * t ^ 4 + (-1981 / 22500) * alpha * t ^ 6 + (-71 / 16875) * alpha * t ^ 10) * c_sq
theorem v52_32 (t : ℂ) : (momentPoly 52 z52 3 2).eval t = (15760 * t + (-617211 / 20) * t ^ 3 + (60240357 / 4000) * t ^ 5 + (-888901 / 4800) * t ^ 7 + (5269403 / 24000) * t ^ 9 + (3500423 / 72000) * t ^ 11 + (-977981 / 24000) * t ^ 13 + (-15760 / 3) * alpha * t + (499243 / 60) * alpha * t ^ 3 + (-2544497 / 2400) * alpha * t ^ 5 + (-5850383 / 2880) * alpha * t ^ 7 + (539089 / 14400) * alpha * t ^ 9 + (137873 / 8640) * alpha * t ^ 11 + (-1286501 / 43200) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_10, v51_11, v51_12, v51_20, v51_21, v51_22, v51_30, v51_31, v51_32]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22, phase48_30, phase48_31, phase48_32]
  try simp only [star_one, star_neg]
  linear_combination ((-77467 / 2000) * t ^ 3 + (10683007 / 90000) * t ^ 5 + (-7241963 / 112500) * t ^ 7 + (-3722489 / 225000) * t ^ 9 + (436217 / 1350000) * t ^ 11 + (1719913 / 1350000) * t ^ 13 + (690739 / 18000) * c * t ^ 3 + (-739651 / 10800) * c * t ^ 5 + (13323509 / 450000) * c * t ^ 7 + (243883 / 1350000) * c * t ^ 9 + (916199 / 2025000) * c * t ^ 11 + (39091 / 2025000) * c * t ^ 13 + (404 / 1125) * c ^ 2 * t ^ 3 + (-12791 / 45000) * c ^ 2 * t ^ 5 + (-14027 / 270000) * c ^ 2 * t ^ 7 + (409 / 135000) * c ^ 2 * t ^ 9 + (-4109 / 270000) * c ^ 2 * t ^ 11) * alpha_sq + ((-808 / 375) * t ^ 3 + (8449 / 4500) * t ^ 5 + (14207 / 75000) * t ^ 7 + (-1492 / 28125) * t ^ 9 + (54179 / 675000) * t ^ 11 + (142 / 84375) * t ^ 13 + (808 / 1125) * alpha * t ^ 3 + (-7319 / 22500) * alpha * t ^ 5 + (-68927 / 225000) * alpha * t ^ 7 + (-4348 / 84375) * alpha * t ^ 9 + (-30179 / 2025000) * alpha * t ^ 11 + (-142 / 253125) * alpha * t ^ 13) * c_sq
theorem v52_33 (t : ℂ) : (momentPoly 52 z52 3 3).eval t = (819520 + (-2349160) * t ^ 2 + (17731993 / 8) * t ^ 4 + (-6769284447 / 10000) * t ^ 6 + (119197843 / 30000) * t ^ 8 + (-1662874439 / 120000) * t ^ 10 + (19021967 / 90000) * t ^ 12 + (-45802841 / 180000) * t ^ 14 + (-1273679 / 1080000) * t ^ 18) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_03, v51_10, v51_11, v51_12, v51_13, v51_20, v51_21, v51_22, v51_23, v51_30, v51_31, v51_32, v51_33]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23, phase48_30, phase48_31, phase48_32, phase48_33]
  try simp only [star_one, star_neg]
  linear_combination ((-9273 / 10) * t ^ 2 + (8731 / 6) * t ^ 4 + (224389453 / 150000) * t ^ 6 + (-2152039253 / 600000) * t ^ 8 + (2782511371 / 1800000) * t ^ 10 + (83176507 / 9000000) * t ^ 12 + (49602413 / 9000000) * t ^ 14 + (916487 / 562500) * t ^ 18 + (12364 / 15) * c * t ^ 2 + (-18947 / 15) * c * t ^ 4 + (129779609 / 900000) * c * t ^ 6 + (58558859 / 200000) * c * t ^ 8 + (2229011 / 1800000) * c * t ^ 10 + (-199801 / 43200) * c * t ^ 12 + (33659741 / 5400000) * c * t ^ 14 + (3091 / 30) * c ^ 2 * t ^ 2 + (-5761 / 30) * c ^ 2 * t ^ 4 + (221566159 / 2700000) * c ^ 2 * t ^ 6 + (2985523 / 450000) * c ^ 2 * t ^ 8 + (1278967 / 2700000) * c ^ 2 * t ^ 10 + (-25247 / 225000) * c ^ 2 * t ^ 12 + (1667 / 75000) * c ^ 2 * t ^ 14) * alpha_sq + ((-6182 / 15) * t ^ 2 + (12106 / 15) * t ^ 4 + (-91217189 / 225000) * t ^ 6 + (1294661 / 112500) * t ^ 8 + (-440933 / 225000) * t ^ 10 + (250606 / 421875) * t ^ 12 + (6644 / 421875) * t ^ 14 + (-10082 / 1265625) * t ^ 18) * c_sq
theorem v52_34 (t : ℂ) : (momentPoly 52 z52 3 4).eval t = (3184135 * t + (-92599983 / 10) * t ^ 3 + (17858734729 / 2000) * t ^ 5 + (-7078386330151 / 2400000) * t ^ 7 + (364758378069 / 1600000) * t ^ 9 + (-512535036647 / 4800000) * t ^ 11 + (-31748016739 / 640000) * t ^ 13 + (11823597491 / 450000) * t ^ 15 + (-6307476017 / 3200000) * t ^ 17 + (-6774828803 / 43200000) * t ^ 19 + (1069147087 / 28800000) * t ^ 21 + (1511788951 / 28800000) * t ^ 25 + (3184135 / 3) * alpha * t + (-24967093 / 10) * alpha * t ^ 3 + (1442580229 / 1200) * alpha * t ^ 5 + (1214078659301 / 1440000) * alpha * t ^ 7 + (-357256309993 / 576000) * alpha * t ^ 9 + (204815269 / 2880000) * alpha * t ^ 11 + (490581073541 / 17280000) * alpha * t ^ 13 + (-4902859201 / 270000) * alpha * t ^ 15 + (1672385819 / 17280000) * alpha * t ^ 17 + (-5011399751 / 25920000) * alpha * t ^ 19 + (2009443907 / 17280000) * alpha * t ^ 21 + (-147014963 / 10368000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_03, v51_04, v51_10, v51_11, v51_12, v51_13, v51_14, v51_20, v51_21, v51_22, v51_23, v51_24, v51_30, v51_31, v51_32, v51_33, v51_34]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24, phase48_30, phase48_31, phase48_32, phase48_33, phase48_34]
  try simp only [star_one, star_neg]
  linear_combination ((-11622351 / 1000) * t ^ 3 + (1387853471 / 30000) * t ^ 5 + (-3448263687443 / 72000000) * t ^ 7 + (221838073549 / 72000000) * t ^ 9 + (1523118250703 / 144000000) * t ^ 11 + (179731651481 / 720000000) * t ^ 13 + (-389209267763 / 540000000) * t ^ 15 + (17449733179 / 270000000) * t ^ 17 + (40215524207 / 6480000000) * t ^ 19 + (-2855942513 / 2160000000) * t ^ 21 + (-999003109 / 810000000) * t ^ 25 + (34543789 / 3000) * c * t ^ 3 + (-557748133 / 18000) * c * t ^ 5 + (5829233162777 / 216000000) * c * t ^ 7 + (-1560135354583 / 216000000) * c * t ^ 9 + (-328577207 / 5760000) * c * t ^ 11 + (-151902484873 / 720000000) * c * t ^ 13 + (-38258287163 / 1620000000) * c * t ^ 15 + (10115903 / 7500000) * c * t ^ 17 + (-98698234093 / 19440000000) * c * t ^ 19 + (21840220067 / 6480000000) * c * t ^ 21 + (2853643 / 75937500) * c * t ^ 25 + (40408 / 375) * c ^ 2 * t ^ 3 + (-4392587 / 22500) * c ^ 2 * t ^ 5 + (21174963 / 250000) * c ^ 2 * t ^ 7 + (3596237 / 9000000) * c ^ 2 * t ^ 9 + (-46064881 / 6750000) * c ^ 2 * t ^ 11 + (542188867 / 54000000) * c ^ 2 * t ^ 13 + (-3856937 / 5062500) * c ^ 2 * t ^ 15 + (4778 / 1265625) * c ^ 2 * t ^ 17 + (-325517 / 10125000) * c ^ 2 * t ^ 19 + (131603 / 10800000) * c ^ 2 * t ^ 21) * alpha_sq + ((-80816 / 125) * t ^ 3 + (955183 / 750) * t ^ 5 + (-758672269 / 1125000) * t ^ 7 + (10492343 / 281250) * t ^ 9 + (576123 / 10000) * t ^ 11 + (-3533114039 / 67500000) * t ^ 13 + (49389611 / 11250000) * t ^ 15 + (166429 / 4218750) * t ^ 17 + (881713 / 25312500) * t ^ 19 + (-2520721 / 67500000) * t ^ 21 + (-20732 / 6328125) * t ^ 25 + (-80816 / 375) * alpha * t ^ 3 + (2767403 / 11250) * alpha * t ^ 5 + (14316379 / 135000) * alpha * t ^ 7 + (-101290823 / 843750) * alpha * t ^ 9 + (-48476053 / 6750000) * alpha * t ^ 11 + (-640384279 / 202500000) * alpha * t ^ 13 + (-605468687 / 101250000) * alpha * t ^ 15 + (-638851 / 12656250) * alpha * t ^ 17 + (-18013487 / 75937500) * alpha * t ^ 19 + (4679279 / 202500000) * alpha * t ^ 21 + (-20732 / 18984375) * alpha * t ^ 25) * c_sq
theorem v52_40 (t : ℂ) : (momentPoly 52 z52 4 0).eval t = ((-188863 / 960) * t ^ 4 + (248601 / 800) * t ^ 6 + (-874589 / 9600) * t ^ 8 + (-209801 / 7200) * t ^ 10 + (6145 / 1152) * t ^ 16 + (3086233 / 24000) * alpha * t ^ 4 + (-3272393 / 12000) * alpha * t ^ 6 + (2413541 / 16000) * alpha * t ^ 8 + (-144557 / 36000) * alpha * t ^ 10 + (-173441 / 48000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_10, v51_20, v51_30, v51_40]
  try simp only [phase48_00, phase48_10, phase48_20, phase48_30, phase48_40]
  try simp only [star_one, star_neg]
  linear_combination ((9329 / 5625) * t ^ 4 + (-610201 / 45000) * t ^ 6 + (165929 / 15000) * t ^ 8 + (793 / 2500) * t ^ 10 + (-3353 / 1875) * c * t ^ 4 + (12856 / 5625) * c * t ^ 6 + (1981 / 22500) * c * t ^ 8 + (-39091 / 67500) * c * t ^ 10 + (146 / 1125) * c ^ 2 * t ^ 4 + (-2206 / 16875) * c ^ 2 * t ^ 6 + (-2 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-573 / 1250) * t ^ 4 + (1591 / 3750) * t ^ 6 + (-4 / 5625) * t ^ 8 + (284 / 16875) * t ^ 10 + (683 / 11250) * alpha * t ^ 4 + (-1067 / 11250) * alpha * t ^ 6 + (-4 / 5625) * alpha * t ^ 8 + (284 / 16875) * alpha * t ^ 10) * c_sq
theorem v52_41 (t : ℂ) : (momentPoly 52 z52 4 1).eval t = ((-25452 / 5) * t ^ 3 + (1166401 / 125) * t ^ 5 + (-1464506 / 375) * t ^ 7 + (45619 / 375) * t ^ 9 + (-522064 / 1125) * t ^ 11 + (7816 / 1125) * t ^ 17 + (-489547 / 150) * alpha * t ^ 3 + (128474101 / 18000) * alpha * t ^ 5 + (-11747527 / 3000) * alpha * t ^ 7 + (-8733863 / 12000) * alpha * t ^ 9 + (20697131 / 27000) * alpha * t ^ 11 + (228449 / 108000) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_10, v51_11, v51_20, v51_21, v51_30, v51_31, v51_40, v51_41]
  try simp only [phase48_00, phase48_01, phase48_10, phase48_11, phase48_20, phase48_21, phase48_30, phase48_31, phase48_40, phase48_41]
  try simp only [star_one, star_neg]
  linear_combination ((77467 / 1000) * t ^ 3 + (-840586163 / 3600000) * t ^ 5 + (79511777 / 600000) * t ^ 7 + (148831531 / 7200000) * t ^ 9 + (3470591 / 5400000) * t ^ 11 + (-5178511 / 21600000) * t ^ 17 + (-690739 / 9000) * c * t ^ 3 + (1438640281 / 10800000) * c * t ^ 5 + (-279996457 / 5400000) * c * t ^ 7 + (-3527571 / 800000) * c * t ^ 9 + (-10772477 / 16200000) * c * t ^ 11 + (6021677 / 64800000) * c * t ^ 17 + (-808 / 1125) * c ^ 2 * t ^ 3 + (36236 / 84375) * c ^ 2 * t ^ 5 + (19186 / 84375) * c ^ 2 * t ^ 7 + (1444 / 84375) * c ^ 2 * t ^ 9 + (5636 / 253125) * c ^ 2 * t ^ 11 + (146 / 253125) * c ^ 2 * t ^ 17) * alpha_sq + ((512 / 1875) * t ^ 5 + (-184 / 1875) * t ^ 7 + (-584 / 5625) * t ^ 9 + (-16 / 225) * t ^ 11 + (-3232 / 1125) * alpha * t ^ 3 + (203746 / 84375) * alpha * t ^ 5 + (6557 / 28125) * alpha * t ^ 7 + (-1106 / 84375) * alpha * t ^ 9 + (39091 / 253125) * alpha * t ^ 11 + (-584 / 253125) * alpha * t ^ 17) * c_sq
theorem v52_42 (t : ℂ) : (momentPoly 52 z52 4 2).eval t = ((-1777325 / 12) * t ^ 2 + (3638483 / 8) * t ^ 4 + (-664562100241 / 1440000) * t ^ 6 + (216967691203 / 1440000) * t ^ 8 + (529838381 / 115200) * t ^ 10 + (-2415768311 / 8640000) * t ^ 12 + (-417638549 / 2160000) * t ^ 14 + (233485771 / 8640000) * t ^ 18 + (-195987611 / 8640000) * t ^ 20 + (-1832963 / 12) * alpha * t ^ 2 + (10093175 / 24) * alpha * t ^ 4 + (-21776586007 / 57600) * alpha * t ^ 6 + (10373193731 / 96000) * alpha * t ^ 8 + (-8298549 / 12800) * alpha * t ^ 10 + (4651916699 / 1728000) * alpha * t ^ 12 + (65946433 / 432000) * alpha * t ^ 14 + (20318381 / 345600) * alpha * t ^ 18 + (-26957723 / 576000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_10, v51_11, v51_12, v51_20, v51_21, v51_22, v51_30, v51_31, v51_32, v51_40, v51_41, v51_42]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_10, phase48_11, phase48_12, phase48_20, phase48_21, phase48_22, phase48_30, phase48_31, phase48_32, phase48_40, phase48_41, phase48_42]
  try simp only [star_one, star_neg]
  linear_combination ((3091 / 5) * t ^ 2 + (-28399 / 25) * t ^ 4 + (1428947597 / 2700000) * t ^ 6 + (-1122687961 / 18000000) * t ^ 8 + (195804803 / 2250000) * t ^ 10 + (-13193959507 / 324000000) * t ^ 12 + (256291901 / 81000000) * t ^ 14 + (-121214971 / 81000000) * t ^ 18 + (349443863 / 108000000) * t ^ 20 + (-24728 / 45) * c * t ^ 2 + (229706 / 225) * c * t ^ 4 + (-1351038163 / 2700000) * c * t ^ 6 + (110153093 / 5400000) * c * t ^ 8 + (69414569 / 1080000) * c * t ^ 10 + (-559148443 / 10800000) * c * t ^ 12 + (-1483951 / 337500) * c * t ^ 14 + (-327701 / 1800000) * c * t ^ 18 + (-35603 / 2160000) * c * t ^ 20 + (-3091 / 45) * c ^ 2 * t ^ 2 + (5177 / 45) * c ^ 2 * t ^ 4 + (-38954717 / 1350000) * c ^ 2 * t ^ 6 + (-178143229 / 10125000) * c ^ 2 * t ^ 8 + (89239 / 6750000) * c ^ 2 * t ^ 10 + (353147 / 5062500) * c ^ 2 * t ^ 12 + (-303227 / 15187500) * c ^ 2 * t ^ 14 + (-74327 / 3796875) * c ^ 2 * t ^ 18 + (292 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((6182 / 45) * t ^ 2 + (-44564 / 225) * t ^ 4 + (-24265957 / 2700000) * t ^ 6 + (480237529 / 6750000) * t ^ 8 + (7046941 / 27000000) * t ^ 10 + (-39533167 / 20250000) * t ^ 12 + (295424 / 1265625) * t ^ 14 + (5477519 / 81000000) * t ^ 18 + (584 / 1265625) * t ^ 20 + (-6182 / 45) * alpha * t ^ 2 + (67924 / 225) * alpha * t ^ 4 + (-527574107 / 2700000) * alpha * t ^ 6 + (7701413 / 250000) * alpha * t ^ 8 + (-53113501 / 27000000) * alpha * t ^ 10 + (38095727 / 20250000) * alpha * t ^ 12 + (95216 / 1265625) * alpha * t ^ 14 + (964721 / 81000000) * alpha * t ^ 18 + (-584 / 1265625) * alpha * t ^ 20) * c_sq
theorem v52_43 (t : ℂ) : (momentPoly 52 z52 4 3).eval t = (3184135 * t + (-92599983 / 10) * t ^ 3 + (17858734729 / 2000) * t ^ 5 + (-7078386330151 / 2400000) * t ^ 7 + (364758378069 / 1600000) * t ^ 9 + (-512535036647 / 4800000) * t ^ 11 + (-31748016739 / 640000) * t ^ 13 + (11823597491 / 450000) * t ^ 15 + (-6307476017 / 3200000) * t ^ 17 + (-6774828803 / 43200000) * t ^ 19 + (1069147087 / 28800000) * t ^ 21 + (1511788951 / 28800000) * t ^ 25 + (-3184135 / 3) * alpha * t + (24967093 / 10) * alpha * t ^ 3 + (-1442580229 / 1200) * alpha * t ^ 5 + (-1214078659301 / 1440000) * alpha * t ^ 7 + (357256309993 / 576000) * alpha * t ^ 9 + (-204815269 / 2880000) * alpha * t ^ 11 + (-490581073541 / 17280000) * alpha * t ^ 13 + (4902859201 / 270000) * alpha * t ^ 15 + (-1672385819 / 17280000) * alpha * t ^ 17 + (5011399751 / 25920000) * alpha * t ^ 19 + (-2009443907 / 17280000) * alpha * t ^ 21 + (147014963 / 10368000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_03, v51_10, v51_11, v51_12, v51_13, v51_20, v51_21, v51_22, v51_23, v51_30, v51_31, v51_32, v51_33, v51_40, v51_41, v51_42, v51_43]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_10, phase48_11, phase48_12, phase48_13, phase48_20, phase48_21, phase48_22, phase48_23, phase48_30, phase48_31, phase48_32, phase48_33, phase48_40, phase48_41, phase48_42, phase48_43]
  try simp only [star_one, star_neg]
  linear_combination ((-11622351 / 1000) * t ^ 3 + (1387853471 / 30000) * t ^ 5 + (-3448263687443 / 72000000) * t ^ 7 + (221838073549 / 72000000) * t ^ 9 + (1523118250703 / 144000000) * t ^ 11 + (179731651481 / 720000000) * t ^ 13 + (-389209267763 / 540000000) * t ^ 15 + (17449733179 / 270000000) * t ^ 17 + (40215524207 / 6480000000) * t ^ 19 + (-2855942513 / 2160000000) * t ^ 21 + (-999003109 / 810000000) * t ^ 25 + (34543789 / 3000) * c * t ^ 3 + (-557748133 / 18000) * c * t ^ 5 + (5829233162777 / 216000000) * c * t ^ 7 + (-1560135354583 / 216000000) * c * t ^ 9 + (-328577207 / 5760000) * c * t ^ 11 + (-151902484873 / 720000000) * c * t ^ 13 + (-38258287163 / 1620000000) * c * t ^ 15 + (10115903 / 7500000) * c * t ^ 17 + (-98698234093 / 19440000000) * c * t ^ 19 + (21840220067 / 6480000000) * c * t ^ 21 + (2853643 / 75937500) * c * t ^ 25 + (40408 / 375) * c ^ 2 * t ^ 3 + (-4392587 / 22500) * c ^ 2 * t ^ 5 + (21174963 / 250000) * c ^ 2 * t ^ 7 + (3596237 / 9000000) * c ^ 2 * t ^ 9 + (-46064881 / 6750000) * c ^ 2 * t ^ 11 + (542188867 / 54000000) * c ^ 2 * t ^ 13 + (-3856937 / 5062500) * c ^ 2 * t ^ 15 + (4778 / 1265625) * c ^ 2 * t ^ 17 + (-325517 / 10125000) * c ^ 2 * t ^ 19 + (131603 / 10800000) * c ^ 2 * t ^ 21) * alpha_sq + ((-80816 / 125) * t ^ 3 + (955183 / 750) * t ^ 5 + (-758672269 / 1125000) * t ^ 7 + (10492343 / 281250) * t ^ 9 + (576123 / 10000) * t ^ 11 + (-3533114039 / 67500000) * t ^ 13 + (49389611 / 11250000) * t ^ 15 + (166429 / 4218750) * t ^ 17 + (881713 / 25312500) * t ^ 19 + (-2520721 / 67500000) * t ^ 21 + (-20732 / 6328125) * t ^ 25 + (80816 / 375) * alpha * t ^ 3 + (-2767403 / 11250) * alpha * t ^ 5 + (-14316379 / 135000) * alpha * t ^ 7 + (101290823 / 843750) * alpha * t ^ 9 + (48476053 / 6750000) * alpha * t ^ 11 + (640384279 / 202500000) * alpha * t ^ 13 + (605468687 / 101250000) * alpha * t ^ 15 + (638851 / 12656250) * alpha * t ^ 17 + (18013487 / 75937500) * alpha * t ^ 19 + (-4679279 / 202500000) * alpha * t ^ 21 + (20732 / 18984375) * alpha * t ^ 25) * c_sq
theorem v52_44 (t : ℂ) : (momentPoly 52 z52 4 4).eval t = (165575020 + (-1879944512 / 3) * t ^ 2 + (131695512011 / 150) * t ^ 4 + (-4011234739061 / 7500) * t ^ 6 + (17214348703941073 / 144000000) * t ^ 8 + (-233223366148033 / 36000000) * t ^ 10 + (46350118957189 / 9600000) * t ^ 12 + (-8254164494501 / 72000000) * t ^ 14 + (86324932989761 / 576000000) * t ^ 16 + (332876141791 / 72000000) * t ^ 18 + (-6421294153517 / 1296000000) * t ^ 20 + (727458805241 / 72000000) * t ^ 22 + (-4003546145453 / 864000000) * t ^ 24 + (123740166727 / 648000000) * t ^ 26 + (80988022153 / 5184000000) * t ^ 32) := by
  rw [momentPoly]
  simp only [z52, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v51_00, v51_01, v51_02, v51_03, v51_04, v51_10, v51_11, v51_12, v51_13, v51_14, v51_20, v51_21, v51_22, v51_23, v51_24, v51_30, v51_31, v51_32, v51_33, v51_34, v51_40, v51_41, v51_42, v51_43, v51_44]
  try simp only [phase48_00, phase48_01, phase48_02, phase48_03, phase48_04, phase48_10, phase48_11, phase48_12, phase48_13, phase48_14, phase48_20, phase48_21, phase48_22, phase48_23, phase48_24, phase48_30, phase48_31, phase48_32, phase48_33, phase48_34, phase48_40, phase48_41, phase48_42, phase48_43, phase48_44]
  try simp only [star_one, star_neg]
  linear_combination ((-6184028 / 25) * t ^ 2 + (129690274 / 225) * t ^ 4 + (44445993449 / 112500) * t ^ 6 + (-47125376590591 / 22500000) * t ^ 8 + (128949804990497 / 67500000) * t ^ 10 + (-1123884352087 / 2160000) * t ^ 12 + (-2663245214597 / 162000000) * t ^ 14 + (-268813985659 / 108000000) * t ^ 16 + (156720501733 / 324000000) * t ^ 18 + (-6576100168841 / 6075000000) * t ^ 20 + (-1137933323227 / 2025000000) * t ^ 22 + (1050655510391 / 2700000000) * t ^ 24 + (-152131217293 / 24300000000) * t ^ 26 + (-11472738599 / 4050000000) * t ^ 32 + (49472224 / 225) * c * t ^ 2 + (-562877476 / 1125) * c * t ^ 4 + (2110222616 / 9375) * c * t ^ 6 + (23262038521061 / 135000000) * c * t ^ 8 + (-31738817329279 / 270000000) * c * t ^ 10 + (-64687781387 / 18000000) * c * t ^ 12 + (14368105581107 / 1620000000) * c * t ^ 14 + (-3711542169443 / 810000000) * c * t ^ 16 + (-34120139111 / 540000000) * c * t ^ 18 + (-369987840083 / 12150000000) * c * t ^ 20 + (17598016757 / 900000000) * c * t ^ 22 + (-285150719 / 4050000000) * c * t ^ 24 + (-119299414547 / 24300000000) * c * t ^ 26 + (142889543 / 3037500000) * c * t ^ 32 + (6184028 / 225) * c ^ 2 * t ^ 2 + (-85573894 / 1125) * c ^ 2 * t ^ 4 + (1871533471 / 28125) * c ^ 2 * t ^ 6 + (-1225409883629 / 81000000) * c ^ 2 * t ^ 8 + (-964042527613 / 405000000) * c ^ 2 * t ^ 10 + (-5939328929 / 10800000) * c ^ 2 * t ^ 12 + (29100854777 / 270000000) * c ^ 2 * t ^ 14 + (-1817520373 / 202500000) * c ^ 2 * t ^ 16 + (-1317154339 / 607500000) * c ^ 2 * t ^ 18 + (16351216967 / 12150000000) * c ^ 2 * t ^ 20 + (-12800858503 / 12150000000) * c ^ 2 * t ^ 22 + (17718961 / 1518750000) * c ^ 2 * t ^ 24 + (146368763 / 9112500000) * c ^ 2 * t ^ 26 + (42632 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((-24736112 / 225) * t ^ 2 + (359645048 / 1125) * t ^ 4 + (-8750509892 / 28125) * t ^ 6 + (3501634397999 / 33750000) * t ^ 8 + (-131726826413 / 33750000) * t ^ 10 + (26892561937 / 13500000) * t ^ 12 + (-28710696109 / 67500000) * t ^ 14 + (-84550301 / 1875000) * t ^ 16 + (2378719 / 337500) * t ^ 18 + (-7320150811 / 3037500000) * t ^ 20 + (1957653331 / 337500000) * t ^ 22 + (-2087281 / 126562500) * t ^ 24 + (56076791 / 379687500) * t ^ 26 + (-170528 / 94921875) * t ^ 32) * c_sq
#print axioms v52_00
#print axioms v52_11
#print axioms v52_22
#print axioms v52_33
#print axioms v52_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v53_02 (t : ℂ) : (momentPoly 53 z53 0 2).eval t = ((-113 / 24) * t ^ 2 + (619 / 96) * t ^ 4 + (-1 / 12) * d * t ^ 2 + (583 / 120) * alpha * t ^ 2 + (-171 / 40) * alpha * t ^ 4 + (-1 / 36) * alpha * d * t ^ 2 + (1 / 288) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02]
  try simp only [phase53_00, phase53_01, phase53_02]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 36) * t ^ 2) * alpha_sq
theorem v53_03 (t : ℂ) : (momentPoly 53 z53 0 3).eval t = ((-7471 / 320) * t ^ 3 + (7861 / 320) * t ^ 5 + 2 * t ^ 9 + (115 / 192) * d * t ^ 3 + (-133 / 192) * d * t ^ 5 + (-47 / 1152) * d * t ^ 9 + (26809 / 1600) * alpha * t ^ 3 + (-90773 / 4800) * alpha * t ^ 5 + (110201 / 28800) * alpha * t ^ 9 + (-593 / 960) * alpha * d * t ^ 3 + (523 / 960) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_03]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03]
  try simp only [star_one, star_neg]
  linear_combination ((-593 / 960) * t ^ 3 + (171 / 320) * t ^ 5 + (1 / 288) * d * t ^ 5) * alpha_sq
theorem v53_04 (t : ℂ) : (momentPoly 53 z53 0 4).eval t = ((-905539 / 4800) * t ^ 4 + (872613 / 3200) * t ^ 6 + (-70433 / 1200) * t ^ 8 + (-48001 / 1800) * t ^ 10 + (28997 / 4608) * t ^ 16 + (21 / 5) * d * t ^ 4 + (-8017 / 1920) * d * t ^ 6 + (171 / 640) * d * t ^ 8 + (-143 / 288) * d * t ^ 10 + (-2985433 / 24000) * alpha * t ^ 4 + (14312347 / 48000) * alpha * t ^ 6 + (-1409833 / 8000) * alpha * t ^ 8 + (57341 / 18000) * alpha * t ^ 10 + (173441 / 48000) * alpha * t ^ 16 + (-4847 / 1800) * alpha * d * t ^ 4 + (29791 / 9600) * alpha * d * t ^ 6 + (131 / 1152) * alpha * d * t ^ 8 + (-15397 / 21600) * alpha * d * t ^ 10 + (95 / 13824) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_03, v52_04]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04]
  try simp only [star_one, star_neg]
  linear_combination ((-4847 / 1800) * t ^ 4 + (11531 / 3600) * t ^ 6 + (-17797 / 21600) * t ^ 10 + (593 / 5760) * d * t ^ 6 + (-57 / 640) * d * t ^ 8) * alpha_sq
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
theorem v53_12 (t : ℂ) : (momentPoly 53 z53 1 2).eval t = (105 * t + (-98369 / 960) * t ^ 3 + (1639 / 960) * t ^ 5 + (-35 / 8) * d * t + (283 / 64) * d * t ^ 3 + (-43 / 192) * d * t ^ 5 + (245 / 8) * alpha * t + (-22501 / 960) * alpha * t ^ 3 + (-6269 / 960) * alpha * t ^ 5 + (-593 / 2880) * alpha * d * t ^ 3 + (523 / 2880) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_10, v52_11, v52_12]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12]
  try simp only [star_one, star_neg]
  linear_combination ((593 / 2880) * t ^ 3 + (-57 / 320) * t ^ 5 + (-1 / 864) * d * t ^ 5) * alpha_sq
theorem v53_13 (t : ℂ) : (momentPoly 53 z53 1 3).eval t = ((-1469 / 2) * t ^ 2 + (4103309 / 2400) * t ^ 4 + (-1547509 / 1600) * t ^ 6 + (-1207 / 9600) * t ^ 10 + (-13) * d * t ^ 2 + (441 / 32) * d * t ^ 4 + (-95 / 96) * d * t ^ 6 + (-143 / 1152) * d * t ^ 10 + (7579 / 10) * alpha * t ^ 2 + (-3302849 / 2400) * alpha * t ^ 4 + (1471781 / 2400) * alpha * t ^ 6 + (216521 / 28800) * alpha * t ^ 10 + (-13 / 3) * alpha * d * t ^ 2 + (7931 / 2400) * alpha * d * t ^ 4 + (5167 / 4800) * alpha * d * t ^ 6 + (-4349 / 28800) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_03, v52_10, v52_11, v52_12, v52_13]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13]
  try simp only [star_one, star_neg]
  linear_combination ((-13 / 3) * t ^ 2 + (4927 / 1200) * t ^ 4 + (13 / 4800) * t ^ 6 + (17797 / 86400) * t ^ 10) * alpha_sq
theorem v53_14 (t : ℂ) : (momentPoly 53 z53 1 4).eval t = ((-769513 / 160) * t ^ 3 + (599352003 / 64000) * t ^ 5 + (-135616703 / 32000) * t ^ 7 + (57444479 / 384000) * t ^ 9 + (-132704461 / 288000) * t ^ 11 + (8587511 / 1152000) * t ^ 17 + (11845 / 96) * d * t ^ 3 + (-29227253 / 115200) * d * t ^ 5 + (799337 / 6400) * d * t ^ 7 + (-997451 / 230400) * d * t ^ 9 + (21659 / 2304) * d * t ^ 11 + (-1985 / 9216) * d * t ^ 17 + (2761327 / 800) * alpha * t ^ 3 + (-4191605687 / 576000) * alpha * t ^ 5 + (374579329 / 96000) * alpha * t ^ 7 + (778429063 / 1152000) * alpha * t ^ 9 + (-213897359 / 288000) * alpha * t ^ 11 + (-2548831 / 1152000) * alpha * t ^ 17 + (-61079 / 480) * alpha * d * t ^ 3 + (136949993 / 576000) * alpha * d * t ^ 5 + (-11091271 / 96000) * alpha * d * t ^ 7 + (7245023 / 1152000) * alpha * d * t ^ 9 + (-1233037 / 864000) * alpha * d * t ^ 11 + (-496573 / 3456000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_03, v52_04, v52_10, v52_11, v52_12, v52_13, v52_14]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14]
  try simp only [star_one, star_neg]
  linear_combination ((-61079 / 480) * t ^ 3 + (129533527 / 576000) * t ^ 5 + (-26117927 / 288000) * t ^ 7 + (-2413541 / 384000) * t ^ 9 + (-314641 / 288000) * t ^ 11 + (173441 / 1152000) * t ^ 17 + (311 / 432) * d * t ^ 5 + (-4943 / 8640) * d * t ^ 7 + (-1157 / 8640) * d * t ^ 9 + (-95 / 41472) * d * t ^ 17) * alpha_sq
theorem v53_20 (t : ℂ) : (momentPoly 53 z53 2 0).eval t = ((-113 / 24) * t ^ 2 + (619 / 96) * t ^ 4 + (-1 / 12) * d * t ^ 2 + (-583 / 120) * alpha * t ^ 2 + (171 / 40) * alpha * t ^ 4 + (1 / 36) * alpha * d * t ^ 2 + (-1 / 288) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_10, v52_20]
  try simp only [phase53_00, phase53_10, phase53_20]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 36) * t ^ 2) * alpha_sq
theorem v53_21 (t : ℂ) : (momentPoly 53 z53 2 1).eval t = (105 * t + (-98369 / 960) * t ^ 3 + (1639 / 960) * t ^ 5 + (-35 / 8) * d * t + (283 / 64) * d * t ^ 3 + (-43 / 192) * d * t ^ 5 + (-245 / 8) * alpha * t + (22501 / 960) * alpha * t ^ 3 + (6269 / 960) * alpha * t ^ 5 + (593 / 2880) * alpha * d * t ^ 3 + (-523 / 2880) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_10, v52_11, v52_20, v52_21]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21]
  try simp only [star_one, star_neg]
  linear_combination ((593 / 2880) * t ^ 3 + (-57 / 320) * t ^ 5 + (-1 / 864) * d * t ^ 5) * alpha_sq
theorem v53_22 (t : ℂ) : (momentPoly 53 z53 2 2).eval t = (5565 + (-10556) * t ^ 2 + (5927141 / 1200) * t ^ 4 + (166409 / 9600) * t ^ 6 + (416863 / 9600) * t ^ 8 + (-52 / 3) * d * t ^ 2 + (679 / 40) * d * t ^ 4 + (139 / 1920) * d * t ^ 6 + (-57 / 640) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_10, v52_11, v52_12, v52_20, v52_21, v52_22]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22]
  try simp only [star_one, star_neg]
  linear_combination ((52 / 9) * t ^ 2 + (-4943 / 1080) * t ^ 4 + (-1157 / 1080) * t ^ 6 + (-593 / 17280) * d * t ^ 6 + (19 / 640) * d * t ^ 8) * alpha_sq
theorem v53_23 (t : ℂ) : (momentPoly 53 z53 2 3).eval t = (16381 * t + (-10132007 / 320) * t ^ 3 + (125714509 / 8000) * t ^ 5 + (-6389443 / 9600) * t ^ 7 + (3888977 / 16000) * t ^ 9 + (5745537 / 128000) * t ^ 11 + (-14276371 / 384000) * t ^ 13 + (-16381 / 24) * d * t + (87447 / 64) * d * t ^ 3 + (-21441239 / 28800) * d * t ^ 5 + (927701 / 14400) * d * t ^ 7 + (-28663 / 6400) * d * t ^ 9 + (35591 / 230400) * d * t ^ 11 + (-41827 / 230400) * d * t ^ 13 + (114667 / 24) * alpha * t + (-2317603 / 320) * alpha * t ^ 3 + (12477097 / 28800) * alpha * t ^ 5 + (29633501 / 14400) * alpha * t ^ 7 + (-795839 / 19200) * alpha * t ^ 9 + (-1176707 / 76800) * alpha * t ^ 11 + (2535319 / 76800) * alpha * t ^ 13 + (-61079 / 960) * alpha * d * t ^ 3 + (1673297 / 14400) * alpha * d * t ^ 5 + (-1497551 / 28800) * alpha * d * t ^ 7 + (-151 / 1920) * alpha * d * t ^ 9 + (-32893 / 76800) * alpha * d * t ^ 11 + (-8357 / 46080) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_03, v52_10, v52_11, v52_12, v52_13, v52_20, v52_21, v52_22, v52_23]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23]
  try simp only [star_one, star_neg]
  linear_combination ((61079 / 960) * t ^ 3 + (-1657747 / 14400) * t ^ 5 + (367379 / 7200) * t ^ 7 + (859387 / 691200) * t ^ 11 + (-2717 / 5120) * t ^ 13 + (-311 / 864) * d * t ^ 5 + (4967 / 21600) * d * t ^ 7 + (23101 / 172800) * d * t ^ 9 + (-7111 / 518400) * d * t ^ 13) * alpha_sq
theorem v53_24 (t : ℂ) : (momentPoly 53 z53 2 4).eval t = ((-907955 / 6) * t ^ 2 + (395547049 / 800) * t ^ 4 + (-253196295707 / 480000) * t ^ 6 + (230092198731 / 1280000) * t ^ 8 + (1841991121 / 384000) * t ^ 10 + (124142101 / 2560000) * t ^ 12 + (-126542021 / 640000) * t ^ 14 + (528988711 / 23040000) * t ^ 18 + (-140233273 / 11520000) * t ^ 20 + (-8035 / 3) * d * t ^ 2 + (22491 / 4) * d * t ^ 4 + (-26332591 / 8000) * d * t ^ 6 + (817852919 / 2304000) * d * t ^ 8 + (-4693553 / 76800) * d * t ^ 10 + (210210577 / 4608000) * d * t ^ 12 + (7837567 / 1152000) * d * t ^ 14 + (-244267 / 512000) * d * t ^ 18 + (-58171 / 1152000) * d * t ^ 20 + (936881 / 6) * alpha * t ^ 2 + (-85361801 / 200) * alpha * t ^ 4 + (109795817303 / 288000) * alpha * t ^ 6 + (-249928556671 / 2304000) * alpha * t ^ 8 + (69207647 / 76800) * alpha * t ^ 10 + (-4358491091 / 1536000) * alpha * t ^ 12 + (-32712107 / 230400) * alpha * t ^ 14 + (-96690409 / 1536000) * alpha * t ^ 18 + (125510677 / 2304000) * alpha * t ^ 20 + (-8035 / 9) * alpha * d * t ^ 2 + (2973323 / 2400) * alpha * d * t ^ 4 + (7479451 / 36000) * alpha * d * t ^ 6 + (-1293892363 / 2304000) * alpha * d * t ^ 8 + (-57632069 / 1152000) * alpha * d * t ^ 10 + (871659041 / 13824000) * alpha * d * t ^ 12 + (-4085789 / 691200) * alpha * d * t ^ 14 + (660527 / 4608000) * alpha * d * t ^ 18 + (175 / 9216) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_03, v52_04, v52_10, v52_11, v52_12, v52_13, v52_14, v52_20, v52_21, v52_22, v52_23, v52_24]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24]
  try simp only [star_one, star_neg]
  linear_combination ((-8035 / 9) * t ^ 2 + (83759 / 50) * t ^ 4 + (-10414951 / 13500) * t ^ 6 + (-5289251 / 432000) * t ^ 8 + (1016159 / 12000) * t ^ 10 + (-24253231 / 324000) * t ^ 12 + (-528439 / 64800) * t ^ 14 + (-228449 / 1296000) * t ^ 18 + (3086233 / 6912000) * d * t ^ 8 + (-3272393 / 3456000) * d * t ^ 10 + (2413541 / 4608000) * d * t ^ 12 + (-144557 / 10368000) * d * t ^ 14 + (-11267 / 331776) * d * t ^ 18 + (58171 / 3456000) * d * t ^ 20) * alpha_sq
theorem v53_30 (t : ℂ) : (momentPoly 53 z53 3 0).eval t = ((-7471 / 320) * t ^ 3 + (7861 / 320) * t ^ 5 + 2 * t ^ 9 + (115 / 192) * d * t ^ 3 + (-133 / 192) * d * t ^ 5 + (-47 / 1152) * d * t ^ 9 + (-26809 / 1600) * alpha * t ^ 3 + (90773 / 4800) * alpha * t ^ 5 + (-110201 / 28800) * alpha * t ^ 9 + (593 / 960) * alpha * d * t ^ 3 + (-523 / 960) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_10, v52_20, v52_30]
  try simp only [phase53_00, phase53_10, phase53_20, phase53_30]
  try simp only [star_one, star_neg]
  linear_combination ((-593 / 960) * t ^ 3 + (171 / 320) * t ^ 5 + (1 / 288) * d * t ^ 5) * alpha_sq
theorem v53_31 (t : ℂ) : (momentPoly 53 z53 3 1).eval t = ((-1469 / 2) * t ^ 2 + (4103309 / 2400) * t ^ 4 + (-1547509 / 1600) * t ^ 6 + (-1207 / 9600) * t ^ 10 + (-13) * d * t ^ 2 + (441 / 32) * d * t ^ 4 + (-95 / 96) * d * t ^ 6 + (-143 / 1152) * d * t ^ 10 + (-7579 / 10) * alpha * t ^ 2 + (3302849 / 2400) * alpha * t ^ 4 + (-1471781 / 2400) * alpha * t ^ 6 + (-216521 / 28800) * alpha * t ^ 10 + (13 / 3) * alpha * d * t ^ 2 + (-7931 / 2400) * alpha * d * t ^ 4 + (-5167 / 4800) * alpha * d * t ^ 6 + (4349 / 28800) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_10, v52_11, v52_20, v52_21, v52_30, v52_31]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21, phase53_30, phase53_31]
  try simp only [star_one, star_neg]
  linear_combination ((-13 / 3) * t ^ 2 + (4927 / 1200) * t ^ 4 + (13 / 4800) * t ^ 6 + (17797 / 86400) * t ^ 10) * alpha_sq
theorem v53_32 (t : ℂ) : (momentPoly 53 z53 3 2).eval t = (16381 * t + (-10132007 / 320) * t ^ 3 + (125714509 / 8000) * t ^ 5 + (-6389443 / 9600) * t ^ 7 + (3888977 / 16000) * t ^ 9 + (5745537 / 128000) * t ^ 11 + (-14276371 / 384000) * t ^ 13 + (-16381 / 24) * d * t + (87447 / 64) * d * t ^ 3 + (-21441239 / 28800) * d * t ^ 5 + (927701 / 14400) * d * t ^ 7 + (-28663 / 6400) * d * t ^ 9 + (35591 / 230400) * d * t ^ 11 + (-41827 / 230400) * d * t ^ 13 + (-114667 / 24) * alpha * t + (2317603 / 320) * alpha * t ^ 3 + (-12477097 / 28800) * alpha * t ^ 5 + (-29633501 / 14400) * alpha * t ^ 7 + (795839 / 19200) * alpha * t ^ 9 + (1176707 / 76800) * alpha * t ^ 11 + (-2535319 / 76800) * alpha * t ^ 13 + (61079 / 960) * alpha * d * t ^ 3 + (-1673297 / 14400) * alpha * d * t ^ 5 + (1497551 / 28800) * alpha * d * t ^ 7 + (151 / 1920) * alpha * d * t ^ 9 + (32893 / 76800) * alpha * d * t ^ 11 + (8357 / 46080) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_10, v52_11, v52_12, v52_20, v52_21, v52_22, v52_30, v52_31, v52_32]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22, phase53_30, phase53_31, phase53_32]
  try simp only [star_one, star_neg]
  linear_combination ((61079 / 960) * t ^ 3 + (-1657747 / 14400) * t ^ 5 + (367379 / 7200) * t ^ 7 + (859387 / 691200) * t ^ 11 + (-2717 / 5120) * t ^ 13 + (-311 / 864) * d * t ^ 5 + (4967 / 21600) * d * t ^ 7 + (23101 / 172800) * d * t ^ 9 + (-7111 / 518400) * d * t ^ 13) * alpha_sq
theorem v53_33 (t : ℂ) : (momentPoly 53 z53 3 3).eval t = (868193 + (-4893315 / 2) * t ^ 2 + (906852573 / 400) * t ^ 4 + (-163650739853 / 240000) * t ^ 6 + (5750669963 / 480000) * t ^ 8 + (-2988603427 / 160000) * t ^ 10 + (76064393 / 360000) * t ^ 12 + (-83058909 / 320000) * t ^ 14 + (-11870419 / 2880000) * t ^ 18 + (-8035 / 2) * d * t ^ 2 + (311661 / 40) * d * t ^ 4 + (-178444621 / 48000) * d * t ^ 6 + (-255427 / 6400) * d * t ^ 8 + (-531871 / 32000) * d * t ^ 10 + (-2908223 / 288000) * d * t ^ 12 + (841601 / 96000) * d * t ^ 14 + (-47 / 288) * d * t ^ 18) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_03, v52_10, v52_11, v52_12, v52_13, v52_20, v52_21, v52_22, v52_23, v52_30, v52_31, v52_32, v52_33]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23, phase53_30, phase53_31, phase53_32, phase53_33]
  try simp only [star_one, star_neg]
  linear_combination ((8035 / 6) * t ^ 2 + (-84031 / 40) * t ^ 4 + (832739 / 3200) * t ^ 6 + (5850383 / 11520) * t ^ 8 + (-539089 / 57600) * t ^ 10 + (313 / 14400) * t ^ 12 + (308023 / 115200) * t ^ 14 + (1016873 / 1036800) * t ^ 18 + (-45661 / 2880) * d * t ^ 6 + (827591 / 28800) * d * t ^ 8 + (-367379 / 28800) * d * t ^ 10 + (-6803 / 43200) * d * t ^ 14) * alpha_sq
theorem v53_34 (t : ℂ) : (momentPoly 53 z53 3 4).eval t = (3375113 * t + (-775246089 / 80) * t ^ 3 + (74917315679 / 8000) * t ^ 5 + (-63242857832083 / 19200000) * t ^ 7 + (7456210365953 / 19200000) * t ^ 9 + (-4618540954601 / 38400000) * t ^ 11 + (-2087983207063 / 46080000) * t ^ 13 + (930404321507 / 38400000) * t ^ 15 + (-110431239247 / 51200000) * t ^ 17 + (-824103817 / 4800000) * t ^ 19 + (2397561041 / 38400000) * t ^ 21 + (24451971641 / 460800000) * t ^ 25 + (-3375113 / 24) * d * t + (6690969 / 16) * d * t ^ 3 + (-1032974057 / 2400) * d * t ^ 5 + (392783514013 / 2304000) * d * t ^ 7 + (-1007568027 / 51200) * d * t ^ 9 + (48475012603 / 23040000) * d * t ^ 11 + (-1246076869 / 5529600) * d * t ^ 13 + (747603821 / 4608000) * d * t ^ 15 + (6854411 / 1228800) * d * t ^ 17 + (-6012841 / 3456000) * d * t ^ 19 + (3037639 / 1280000) * d * t ^ 21 + (-301213 / 2211840) * d * t ^ 25 + (23625791 / 24) * alpha * t + (-177330381 / 80) * alpha * t ^ 3 + (520604239 / 600) * alpha * t ^ 5 + (1256547423199 / 1280000) * alpha * t ^ 7 + (-806428917401 / 1280000) * alpha * t ^ 9 + (2482747349 / 921600) * alpha * t ^ 11 + (4185868171429 / 138240000) * alpha * t ^ 13 + (-457974207001 / 23040000) * alpha * t ^ 15 + (-8418506857 / 92160000) * alpha * t ^ 17 + (-903376679 / 4320000) * alpha * t ^ 19 + (361710233 / 2880000) * alpha * t ^ 21 + (-106317899 / 6144000) * alpha * t ^ 25 + (-1557811 / 80) * alpha * d * t ^ 3 + (85743753 / 1600) * alpha * d * t ^ 5 + (-22191281143 / 460800) * alpha * d * t ^ 7 + (702617593 / 51200) * alpha * d * t ^ 9 + (350183863 / 4608000) * alpha * d * t ^ 11 + (3320886509 / 27648000) * alpha * d * t ^ 13 + (104810279 / 921600) * alpha * d * t ^ 15 + (97788731 / 18432000) * alpha * d * t ^ 17 + (2374709 / 288000) * alpha * d * t ^ 19 + (-26556539 / 4608000) * alpha * d * t ^ 21 + (-821303 / 6144000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_03, v52_04, v52_10, v52_11, v52_12, v52_13, v52_14, v52_20, v52_21, v52_22, v52_23, v52_24, v52_30, v52_31, v52_32, v52_33, v52_34]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24, phase53_30, phase53_31, phase53_32, phase53_33, phase53_34]
  try simp only [star_one, star_neg]
  linear_combination ((1557811 / 80) * t ^ 3 + (-255634609 / 4800) * t ^ 5 + (21917659543 / 460800) * t ^ 7 + (-10373193731 / 768000) * t ^ 9 + (141948659 / 307200) * t ^ 11 + (-28665774997 / 27648000) * t ^ 13 + (4406982227 / 13824000) * t ^ 15 + (-345136363 / 18432000) * t ^ 17 + (-4014107 / 1296000) * t ^ 19 + (26957723 / 4608000) * t ^ 21 + (24802063 / 55296000) * t ^ 25 + (-31933 / 288) * d * t ^ 5 + (302987 / 2160) * d * t ^ 7 + (45615343 / 864000) * d * t ^ 9 + (-287229899 / 3456000) * d * t ^ 11 + (-4442957 / 648000) * d * t ^ 13 + (86235349 / 10368000) * d * t ^ 15 + (-1286501 / 2073600) * d * t ^ 17 + (-92093 / 829440) * d * t ^ 19 + (6391021 / 41472000) * d * t ^ 21 + (-135109 / 4976640) * d * t ^ 25) * alpha_sq
theorem v53_40 (t : ℂ) : (momentPoly 53 z53 4 0).eval t = ((-905539 / 4800) * t ^ 4 + (872613 / 3200) * t ^ 6 + (-70433 / 1200) * t ^ 8 + (-48001 / 1800) * t ^ 10 + (28997 / 4608) * t ^ 16 + (21 / 5) * d * t ^ 4 + (-8017 / 1920) * d * t ^ 6 + (171 / 640) * d * t ^ 8 + (-143 / 288) * d * t ^ 10 + (2985433 / 24000) * alpha * t ^ 4 + (-14312347 / 48000) * alpha * t ^ 6 + (1409833 / 8000) * alpha * t ^ 8 + (-57341 / 18000) * alpha * t ^ 10 + (-173441 / 48000) * alpha * t ^ 16 + (4847 / 1800) * alpha * d * t ^ 4 + (-29791 / 9600) * alpha * d * t ^ 6 + (-131 / 1152) * alpha * d * t ^ 8 + (15397 / 21600) * alpha * d * t ^ 10 + (-95 / 13824) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_10, v52_20, v52_30, v52_40]
  try simp only [phase53_00, phase53_10, phase53_20, phase53_30, phase53_40]
  try simp only [star_one, star_neg]
  linear_combination ((-4847 / 1800) * t ^ 4 + (11531 / 3600) * t ^ 6 + (-17797 / 21600) * t ^ 10 + (593 / 5760) * d * t ^ 6 + (-57 / 640) * d * t ^ 8) * alpha_sq
theorem v53_41 (t : ℂ) : (momentPoly 53 z53 4 1).eval t = ((-769513 / 160) * t ^ 3 + (599352003 / 64000) * t ^ 5 + (-135616703 / 32000) * t ^ 7 + (57444479 / 384000) * t ^ 9 + (-132704461 / 288000) * t ^ 11 + (8587511 / 1152000) * t ^ 17 + (11845 / 96) * d * t ^ 3 + (-29227253 / 115200) * d * t ^ 5 + (799337 / 6400) * d * t ^ 7 + (-997451 / 230400) * d * t ^ 9 + (21659 / 2304) * d * t ^ 11 + (-1985 / 9216) * d * t ^ 17 + (-2761327 / 800) * alpha * t ^ 3 + (4191605687 / 576000) * alpha * t ^ 5 + (-374579329 / 96000) * alpha * t ^ 7 + (-778429063 / 1152000) * alpha * t ^ 9 + (213897359 / 288000) * alpha * t ^ 11 + (2548831 / 1152000) * alpha * t ^ 17 + (61079 / 480) * alpha * d * t ^ 3 + (-136949993 / 576000) * alpha * d * t ^ 5 + (11091271 / 96000) * alpha * d * t ^ 7 + (-7245023 / 1152000) * alpha * d * t ^ 9 + (1233037 / 864000) * alpha * d * t ^ 11 + (496573 / 3456000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_10, v52_11, v52_20, v52_21, v52_30, v52_31, v52_40, v52_41]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21, phase53_30, phase53_31, phase53_40, phase53_41]
  try simp only [star_one, star_neg]
  linear_combination ((-61079 / 480) * t ^ 3 + (129533527 / 576000) * t ^ 5 + (-26117927 / 288000) * t ^ 7 + (-2413541 / 384000) * t ^ 9 + (-314641 / 288000) * t ^ 11 + (173441 / 1152000) * t ^ 17 + (311 / 432) * d * t ^ 5 + (-4943 / 8640) * d * t ^ 7 + (-1157 / 8640) * d * t ^ 9 + (-95 / 41472) * d * t ^ 17) * alpha_sq
theorem v53_42 (t : ℂ) : (momentPoly 53 z53 4 2).eval t = ((-907955 / 6) * t ^ 2 + (395547049 / 800) * t ^ 4 + (-253196295707 / 480000) * t ^ 6 + (230092198731 / 1280000) * t ^ 8 + (1841991121 / 384000) * t ^ 10 + (124142101 / 2560000) * t ^ 12 + (-126542021 / 640000) * t ^ 14 + (528988711 / 23040000) * t ^ 18 + (-140233273 / 11520000) * t ^ 20 + (-8035 / 3) * d * t ^ 2 + (22491 / 4) * d * t ^ 4 + (-26332591 / 8000) * d * t ^ 6 + (817852919 / 2304000) * d * t ^ 8 + (-4693553 / 76800) * d * t ^ 10 + (210210577 / 4608000) * d * t ^ 12 + (7837567 / 1152000) * d * t ^ 14 + (-244267 / 512000) * d * t ^ 18 + (-58171 / 1152000) * d * t ^ 20 + (-936881 / 6) * alpha * t ^ 2 + (85361801 / 200) * alpha * t ^ 4 + (-109795817303 / 288000) * alpha * t ^ 6 + (249928556671 / 2304000) * alpha * t ^ 8 + (-69207647 / 76800) * alpha * t ^ 10 + (4358491091 / 1536000) * alpha * t ^ 12 + (32712107 / 230400) * alpha * t ^ 14 + (96690409 / 1536000) * alpha * t ^ 18 + (-125510677 / 2304000) * alpha * t ^ 20 + (8035 / 9) * alpha * d * t ^ 2 + (-2973323 / 2400) * alpha * d * t ^ 4 + (-7479451 / 36000) * alpha * d * t ^ 6 + (1293892363 / 2304000) * alpha * d * t ^ 8 + (57632069 / 1152000) * alpha * d * t ^ 10 + (-871659041 / 13824000) * alpha * d * t ^ 12 + (4085789 / 691200) * alpha * d * t ^ 14 + (-660527 / 4608000) * alpha * d * t ^ 18 + (-175 / 9216) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_10, v52_11, v52_12, v52_20, v52_21, v52_22, v52_30, v52_31, v52_32, v52_40, v52_41, v52_42]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22, phase53_30, phase53_31, phase53_32, phase53_40, phase53_41, phase53_42]
  try simp only [star_one, star_neg]
  linear_combination ((-8035 / 9) * t ^ 2 + (83759 / 50) * t ^ 4 + (-10414951 / 13500) * t ^ 6 + (-5289251 / 432000) * t ^ 8 + (1016159 / 12000) * t ^ 10 + (-24253231 / 324000) * t ^ 12 + (-528439 / 64800) * t ^ 14 + (-228449 / 1296000) * t ^ 18 + (3086233 / 6912000) * d * t ^ 8 + (-3272393 / 3456000) * d * t ^ 10 + (2413541 / 4608000) * d * t ^ 12 + (-144557 / 10368000) * d * t ^ 14 + (-11267 / 331776) * d * t ^ 18 + (58171 / 3456000) * d * t ^ 20) * alpha_sq
theorem v53_43 (t : ℂ) : (momentPoly 53 z53 4 3).eval t = (3375113 * t + (-775246089 / 80) * t ^ 3 + (74917315679 / 8000) * t ^ 5 + (-63242857832083 / 19200000) * t ^ 7 + (7456210365953 / 19200000) * t ^ 9 + (-4618540954601 / 38400000) * t ^ 11 + (-2087983207063 / 46080000) * t ^ 13 + (930404321507 / 38400000) * t ^ 15 + (-110431239247 / 51200000) * t ^ 17 + (-824103817 / 4800000) * t ^ 19 + (2397561041 / 38400000) * t ^ 21 + (24451971641 / 460800000) * t ^ 25 + (-3375113 / 24) * d * t + (6690969 / 16) * d * t ^ 3 + (-1032974057 / 2400) * d * t ^ 5 + (392783514013 / 2304000) * d * t ^ 7 + (-1007568027 / 51200) * d * t ^ 9 + (48475012603 / 23040000) * d * t ^ 11 + (-1246076869 / 5529600) * d * t ^ 13 + (747603821 / 4608000) * d * t ^ 15 + (6854411 / 1228800) * d * t ^ 17 + (-6012841 / 3456000) * d * t ^ 19 + (3037639 / 1280000) * d * t ^ 21 + (-301213 / 2211840) * d * t ^ 25 + (-23625791 / 24) * alpha * t + (177330381 / 80) * alpha * t ^ 3 + (-520604239 / 600) * alpha * t ^ 5 + (-1256547423199 / 1280000) * alpha * t ^ 7 + (806428917401 / 1280000) * alpha * t ^ 9 + (-2482747349 / 921600) * alpha * t ^ 11 + (-4185868171429 / 138240000) * alpha * t ^ 13 + (457974207001 / 23040000) * alpha * t ^ 15 + (8418506857 / 92160000) * alpha * t ^ 17 + (903376679 / 4320000) * alpha * t ^ 19 + (-361710233 / 2880000) * alpha * t ^ 21 + (106317899 / 6144000) * alpha * t ^ 25 + (1557811 / 80) * alpha * d * t ^ 3 + (-85743753 / 1600) * alpha * d * t ^ 5 + (22191281143 / 460800) * alpha * d * t ^ 7 + (-702617593 / 51200) * alpha * d * t ^ 9 + (-350183863 / 4608000) * alpha * d * t ^ 11 + (-3320886509 / 27648000) * alpha * d * t ^ 13 + (-104810279 / 921600) * alpha * d * t ^ 15 + (-97788731 / 18432000) * alpha * d * t ^ 17 + (-2374709 / 288000) * alpha * d * t ^ 19 + (26556539 / 4608000) * alpha * d * t ^ 21 + (821303 / 6144000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_03, v52_10, v52_11, v52_12, v52_13, v52_20, v52_21, v52_22, v52_23, v52_30, v52_31, v52_32, v52_33, v52_40, v52_41, v52_42, v52_43]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23, phase53_30, phase53_31, phase53_32, phase53_33, phase53_40, phase53_41, phase53_42, phase53_43]
  try simp only [star_one, star_neg]
  linear_combination ((1557811 / 80) * t ^ 3 + (-255634609 / 4800) * t ^ 5 + (21917659543 / 460800) * t ^ 7 + (-10373193731 / 768000) * t ^ 9 + (141948659 / 307200) * t ^ 11 + (-28665774997 / 27648000) * t ^ 13 + (4406982227 / 13824000) * t ^ 15 + (-345136363 / 18432000) * t ^ 17 + (-4014107 / 1296000) * t ^ 19 + (26957723 / 4608000) * t ^ 21 + (24802063 / 55296000) * t ^ 25 + (-31933 / 288) * d * t ^ 5 + (302987 / 2160) * d * t ^ 7 + (45615343 / 864000) * d * t ^ 9 + (-287229899 / 3456000) * d * t ^ 11 + (-4442957 / 648000) * d * t ^ 13 + (86235349 / 10368000) * d * t ^ 15 + (-1286501 / 2073600) * d * t ^ 17 + (-92093 / 829440) * d * t ^ 19 + (6391021 / 41472000) * d * t ^ 21 + (-135109 / 4976640) * d * t ^ 25) * alpha_sq
theorem v53_44 (t : ℂ) : (momentPoly 53 z53 4 4).eval t = (178880989 + (-665700742) * t ^ 2 + (91615818437 / 100) * t ^ 4 + (-526705786087 / 960) * t ^ 6 + (17885313618373373 / 144000000) * t ^ 8 + (-1112244125745913 / 96000000) * t ^ 10 + (380793756369259 / 57600000) * t ^ 12 + (-41085068986033 / 576000000) * t ^ 14 + (44076148630843 / 288000000) * t ^ 16 + (2268822341 / 72000000) * t ^ 18 + (-19732416572699 / 6912000000) * t ^ 20 + (12561357896431 / 1152000000) * t ^ 22 + (-7799435021597 / 1536000000) * t ^ 24 + (179223573223 / 1152000000) * t ^ 26 + (357335064283 / 13824000000) * t ^ 32 + (-3279314 / 3) * d * t ^ 2 + (31485909 / 10) * d * t ^ 4 + (-2867741113 / 960) * d * t ^ 6 + (6699255019151 / 7200000) * d * t ^ 8 + (-556188097451 / 19200000) * d * t ^ 10 + (151413691107 / 6400000) * d * t ^ 12 + (943302006059 / 69120000) * d * t ^ 14 + (-100096869273 / 12800000) * d * t ^ 16 + (537829943 / 900000) * d * t ^ 18 + (274317505457 / 1382400000) * d * t ^ 20 + (-1953612857 / 230400000) * d * t ^ 22 + (-4541537 / 12288000) * d * t ^ 24 + (-13547239183 / 691200000) * d * t ^ 26 + (3295379 / 22118400) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z53, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v52_00, v52_01, v52_02, v52_03, v52_04, v52_10, v52_11, v52_12, v52_13, v52_14, v52_20, v52_21, v52_22, v52_23, v52_24, v52_30, v52_31, v52_32, v52_33, v52_34, v52_40, v52_41, v52_42, v52_43, v52_44]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24, phase53_30, phase53_31, phase53_32, phase53_33, phase53_34, phase53_40, phase53_41, phase53_42, phase53_43, phase53_44]
  try simp only [star_one, star_neg]
  linear_combination ((3279314 / 9) * t ^ 2 + (-76403951 / 90) * t ^ 4 + (18127093 / 45) * t ^ 6 + (1231629808301 / 4320000) * t ^ 8 + (-357385691353 / 1728000) * t ^ 10 + (28069781869 / 8640000) * t ^ 12 + (125243387281 / 51840000) * t ^ 14 + (-14024428193 / 6480000) * t ^ 16 + (13114677563 / 17280000) * t ^ 18 + (-64205194411 / 77760000) * t ^ 20 + (2009443907 / 51840000) * t ^ 22 + (-212351377 / 31104000) * t ^ 26 + (-18572167 / 2880) * d * t ^ 6 + (190899007 / 10800) * d * t ^ 8 + (-2430070559 / 153600) * d * t ^ 10 + (10373193731 / 2304000) * d * t ^ 12 + (-46205419 / 1658880) * d * t ^ 14 + (4651916699 / 41472000) * d * t ^ 16 + (65946433 / 10368000) * d * t ^ 18 + (58638427 / 33177600) * d * t ^ 20 + (-4307741 / 3317760) * d * t ^ 22 + (4541537 / 36864000) * d * t ^ 24 + (-2746583 / 49766400) * d * t ^ 26 + (-3295379 / 66355200) * d * t ^ 32) * alpha_sq
#print axioms v53_00
#print axioms v53_11
#print axioms v53_22
#print axioms v53_33
#print axioms v53_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v54_02 (t : ℂ) : (momentPoly 54 z54 0 2).eval t = ((-127 / 48) * t ^ 2 + (119 / 16) * t ^ 4 + (-1 / 6) * d * t ^ 2 + (191 / 40) * alpha * t ^ 2 + (-171 / 40) * alpha * t ^ 4 + (-7 / 144) * alpha * d * t ^ 2 + (1 / 144) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02]
  try simp only [phase53_00, phase53_01, phase53_02]
  try simp only [star_one, star_neg]
  linear_combination ((-7 / 288) * t ^ 2) * alpha_sq + ((1 / 288) * t ^ 2) * d_sq
theorem v54_03 (t : ℂ) : (momentPoly 54 z54 0 3).eval t = ((-2489 / 160) * t ^ 3 + (4149 / 160) * t ^ 5 + 2 * t ^ 9 + (113 / 96) * d * t ^ 3 + (-313 / 192) * d * t ^ 5 + (-47 / 576) * d * t ^ 9 + (15467 / 800) * alpha * t ^ 3 + (-92873 / 4800) * alpha * t ^ 5 + (17771 / 4800) * alpha * t ^ 9 + (-583 / 480) * alpha * d * t ^ 3 + (523 / 480) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_03]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03]
  try simp only [star_one, star_neg]
  linear_combination ((-583 / 960) * t ^ 3 + (171 / 320) * t ^ 5 + (1 / 288) * d * t ^ 3 + (1 / 384) * d * t ^ 5) * alpha_sq + ((1 / 96) * t ^ 3 + (1 / 288) * alpha * t ^ 3 + (-1 / 1152) * alpha * t ^ 5) * d_sq
theorem v54_04 (t : ℂ) : (momentPoly 54 z54 0 4).eval t = ((-71243 / 300) * t ^ 4 + (241943 / 800) * t ^ 6 + (-394253 / 19200) * t ^ 8 + (-237989 / 14400) * t ^ 10 + (5569 / 768) * t ^ 16 + (7471 / 960) * d * t ^ 4 + (-2111 / 240) * d * t ^ 6 + (171 / 320) * d * t ^ 8 + (-143 / 144) * d * t ^ 10 + (-246043 / 4000) * alpha * t ^ 4 + (3238843 / 12000) * alpha * t ^ 6 + (-3225791 / 16000) * alpha * t ^ 8 + (9423 / 4000) * alpha * t ^ 10 + (173441 / 48000) * alpha * t ^ 16 + (-26809 / 4800) * alpha * d * t ^ 4 + (2443 / 400) * alpha * d * t ^ 6 + (619 / 2304) * alpha * d * t ^ 8 + (-59213 / 43200) * alpha * d * t ^ 10 + (95 / 6912) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_03, v53_04]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04]
  try simp only [star_one, star_neg]
  linear_combination ((-26809 / 9600) * t ^ 4 + (90773 / 28800) * t ^ 6 + (-67613 / 86400) * t ^ 10 + (593 / 5760) * d * t ^ 4 + (1 / 96) * d * t ^ 6 + (-57 / 640) * d * t ^ 8 + (-1 / 1728) * d ^ 2 * t ^ 6 + (1 / 13824) * d ^ 2 * t ^ 8) * alpha_sq + ((-115 / 1152) * t ^ 4 + (15 / 128) * t ^ 6 + (-1 / 4608) * t ^ 8 + (47 / 3456) * t ^ 10 + (593 / 5760) * alpha * t ^ 4 + (-533 / 5760) * alpha * t ^ 6) * d_sq
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
theorem v54_12 (t : ℂ) : (momentPoly 54 z54 1 2).eval t = (107 * t + (-15537 / 160) * t ^ 3 + (517 / 160) * t ^ 5 + (-107 / 12) * d * t + (2549 / 288) * d * t ^ 3 + (-17 / 32) * d * t ^ 5 + (107 / 4) * alpha * t + (-26989 / 1440) * alpha * t ^ 3 + (-9671 / 1440) * alpha * t ^ 5 + (-583 / 1440) * alpha * d * t ^ 3 + (523 / 1440) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_10, v53_11, v53_12]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12]
  try simp only [star_one, star_neg]
  linear_combination ((583 / 2880) * t ^ 3 + (-57 / 320) * t ^ 5 + (-1 / 864) * d * t ^ 3 + (-1 / 1152) * d * t ^ 5) * alpha_sq + ((1 / 96) * t ^ 3 + (1 / 864) * alpha * t ^ 3 + (-1 / 3456) * alpha * t ^ 5) * d_sq
theorem v54_13 (t : ℂ) : (momentPoly 54 z54 1 3).eval t = ((-6731 / 16) * t ^ 2 + (927293 / 600) * t ^ 4 + (-5209741 / 4800) * t ^ 6 + (17791 / 14400) * t ^ 10 + (-53 / 2) * d * t ^ 2 + (441 / 16) * d * t ^ 4 + (-475 / 192) * d * t ^ 6 + (-143 / 576) * d * t ^ 10 + (30369 / 40) * alpha * t ^ 2 + (-1617217 / 1200) * alpha * t ^ 4 + (2820197 / 4800) * alpha * t ^ 6 + (35891 / 4800) * alpha * t ^ 10 + (-371 / 48) * alpha * d * t ^ 2 + (5017 / 900) * alpha * d * t ^ 4 + (30977 / 14400) * alpha * d * t ^ 6 + (-4249 / 14400) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_03, v53_10, v53_11, v53_12, v53_13]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13]
  try simp only [star_one, star_neg]
  linear_combination ((-371 / 96) * t ^ 2 + (23219 / 6400) * t ^ 4 + (1631 / 57600) * t ^ 6 + (67613 / 345600) * t ^ 10) * alpha_sq + ((53 / 96) * t ^ 2 + (-1331 / 2304) * t ^ 4 + (131 / 2304) * t ^ 6 + (47 / 13824) * t ^ 10 + (593 / 11520) * alpha * t ^ 4 + (-533 / 11520) * alpha * t ^ 6) * d_sq
theorem v54_14 (t : ℂ) : (momentPoly 54 z54 1 4).eval t = ((-52269 / 16) * t ^ 3 + (255948747 / 32000) * t ^ 5 + (-210024241 / 48000) * t ^ 7 + (33960601 / 192000) * t ^ 9 + (-61332019 / 144000) * t ^ 11 + (1528573 / 192000) * t ^ 17 + (3955 / 16) * d * t ^ 3 + (-32328533 / 57600) * d * t ^ 5 + (2904991 / 9600) * d * t ^ 7 + (-1344701 / 115200) * d * t ^ 9 + (65071 / 3456) * d * t ^ 11 + (-787 / 1536) * d * t ^ 17 + (324807 / 80) * alpha * t ^ 3 + (-2237335111 / 288000) * alpha * t ^ 5 + (60978519 / 16000) * alpha * t ^ 7 + (355955389 / 576000) * alpha * t ^ 9 + (-296849111 / 432000) * alpha * t ^ 11 + (-4420309 / 1728000) * alpha * t ^ 17 + (-4081 / 16) * alpha * d * t ^ 3 + (136982993 / 288000) * alpha * d * t ^ 5 + (-33628513 / 144000) * alpha * d * t ^ 7 + (8499973 / 576000) * alpha * d * t ^ 9 + (-1197287 / 432000) * alpha * d * t ^ 11 + (-496573 / 1728000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_03, v53_04, v53_10, v53_11, v53_12, v53_13, v53_14]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14]
  try simp only [star_one, star_neg]
  linear_combination ((-4081 / 32) * t ^ 3 + (129744127 / 576000) * t ^ 5 + (-11492237 / 128000) * t ^ 7 + (-1409833 / 192000) * t ^ 9 + (-35849 / 32000) * t ^ 11 + (173441 / 1152000) * t ^ 17 + (35 / 48) * d * t ^ 3 + (-47 / 2160) * d * t ^ 5 + (-827 / 1536) * d * t ^ 7 + (-2269 / 17280) * d * t ^ 9 + (-47 / 10368) * d * t ^ 11 + (-95 / 55296) * d * t ^ 17 + (-593 / 138240) * d ^ 2 * t ^ 7 + (523 / 138240) * d ^ 2 * t ^ 9) * alpha_sq + ((35 / 16) * t ^ 3 + (-791 / 320) * t ^ 5 + (1621 / 4608) * t ^ 7 + (-259 / 11520) * t ^ 9 + (95 / 1728) * t ^ 11 + (35 / 48) * alpha * t ^ 3 + (-11473 / 21600) * alpha * t ^ 5 + (-8317 / 38400) * alpha * t ^ 7 + (-65 / 6912) * alpha * t ^ 9 + (7111 / 129600) * alpha * t ^ 11 + (-95 / 165888) * alpha * t ^ 17) * d_sq
theorem v54_20 (t : ℂ) : (momentPoly 54 z54 2 0).eval t = ((-127 / 48) * t ^ 2 + (119 / 16) * t ^ 4 + (-1 / 6) * d * t ^ 2 + (-191 / 40) * alpha * t ^ 2 + (171 / 40) * alpha * t ^ 4 + (7 / 144) * alpha * d * t ^ 2 + (-1 / 144) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_10, v53_20]
  try simp only [phase53_00, phase53_10, phase53_20]
  try simp only [star_one, star_neg]
  linear_combination ((-7 / 288) * t ^ 2) * alpha_sq + ((1 / 288) * t ^ 2) * d_sq
theorem v54_21 (t : ℂ) : (momentPoly 54 z54 2 1).eval t = (107 * t + (-15537 / 160) * t ^ 3 + (517 / 160) * t ^ 5 + (-107 / 12) * d * t + (2549 / 288) * d * t ^ 3 + (-17 / 32) * d * t ^ 5 + (-107 / 4) * alpha * t + (26989 / 1440) * alpha * t ^ 3 + (9671 / 1440) * alpha * t ^ 5 + (583 / 1440) * alpha * d * t ^ 3 + (-523 / 1440) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_10, v53_11, v53_20, v53_21]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21]
  try simp only [star_one, star_neg]
  linear_combination ((583 / 2880) * t ^ 3 + (-57 / 320) * t ^ 5 + (-1 / 864) * d * t ^ 3 + (-1 / 1152) * d * t ^ 5) * alpha_sq + ((1 / 96) * t ^ 3 + (-1 / 864) * alpha * t ^ 3 + (1 / 3456) * alpha * t ^ 5) * d_sq
theorem v54_22 (t : ℂ) : (momentPoly 54 z54 2 2).eval t = (5778 + (-31058 / 3) * t ^ 2 + (7245943 / 1600) * t ^ 4 + (58207 / 1800) * t ^ 6 + (809657 / 14400) * t ^ 8 + (-106 / 3) * d * t ^ 2 + (98369 / 2880) * d * t ^ 4 + (-11 / 30) * d * t ^ 6 + (-57 / 320) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_10, v53_11, v53_12, v53_20, v53_21, v53_22]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22]
  try simp only [star_one, star_neg]
  linear_combination ((371 / 72) * t ^ 2 + (-22501 / 5760) * t ^ 4 + (-6269 / 5760) * t ^ 6 + (-593 / 17280) * d * t ^ 4 + (-1 / 288) * d * t ^ 6 + (19 / 640) * d * t ^ 8 + (1 / 5184) * d ^ 2 * t ^ 6 + (-1 / 41472) * d ^ 2 * t ^ 8) * alpha_sq + ((53 / 72) * t ^ 2 + (-283 / 384) * t ^ 4 + (127 / 3456) * t ^ 6 + (1 / 13824) * t ^ 8) * d_sq
theorem v54_23 (t : ℂ) : (momentPoly 54 z54 2 3).eval t = (17014 * t + (-978831 / 32) * t ^ 3 + (116080129 / 8000) * t ^ 5 + (-14227057 / 12800) * t ^ 7 + (54781799 / 192000) * t ^ 9 + (28266449 / 576000) * t ^ 11 + (-2150841 / 64000) * t ^ 13 + (-8507 / 6) * d * t + (89215 / 32) * d * t ^ 3 + (-21880207 / 14400) * d * t ^ 5 + (1993593 / 12800) * d * t ^ 7 + (-1342993 / 115200) * d * t ^ 9 + (140017 / 345600) * d * t ^ 11 + (-51427 / 115200) * d * t ^ 13 + (8507 / 2) * alpha * t + (-188923 / 32) * alpha * t ^ 3 + (-204995 / 576) * alpha * t ^ 5 + (234441281 / 115200) * alpha * t ^ 7 + (-5318081 / 115200) * alpha * t ^ 9 + (-2829263 / 345600) * alpha * t ^ 11 + (12497063 / 345600) * alpha * t ^ 13 + (-4081 / 32) * alpha * d * t ^ 3 + (3349939 / 14400) * alpha * d * t ^ 5 + (-12001493 / 115200) * alpha * d * t ^ 7 + (-1037 / 7680) * alpha * d * t ^ 9 + (-32893 / 38400) * alpha * d * t ^ 11 + (-8357 / 23040) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_03, v53_10, v53_11, v53_12, v53_13, v53_20, v53_21, v53_22, v53_23]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23]
  try simp only [star_one, star_neg]
  linear_combination ((4081 / 64) * t ^ 3 + (-3318239 / 28800) * t ^ 5 + (1471781 / 28800) * t ^ 7 + (849887 / 691200) * t ^ 11 + (-2717 / 5120) * t ^ 13 + (-35 / 96) * d * t ^ 3 + (-3907 / 86400) * d * t ^ 5 + (5293 / 19200) * d * t ^ 7 + (23101 / 172800) * d * t ^ 9 + (-8311 / 518400) * d * t ^ 11 + (-17771 / 1382400) * d * t ^ 13 + (593 / 138240) * d ^ 2 * t ^ 7 + (-523 / 138240) * d ^ 2 * t ^ 9) * alpha_sq + ((105 / 32) * t ^ 3 + (-2093 / 640) * t ^ 5 + (31 / 512) * t ^ 7 + (259 / 11520) * t ^ 9 + (95 / 6912) * t ^ 11 + (35 / 96) * alpha * t ^ 3 + (-27793 / 86400) * alpha * t ^ 5 + (-7901 / 172800) * alpha * t ^ 7 + (1 / 13824) * alpha * t ^ 9 + (371 / 32400) * alpha * t ^ 11 + (47 / 165888) * alpha * t ^ 13) * d_sq
theorem v54_24 (t : ℂ) : (momentPoly 54 z54 2 4).eval t = ((-2120519 / 24) * t ^ 2 + (479258651 / 1200) * t ^ 4 + (-328274453281 / 640000) * t ^ 6 + (377896277339 / 1920000) * t ^ 8 + (6910981681 / 1152000) * t ^ 10 + (-1196008517 / 2880000) * t ^ 12 + (-44240353 / 270000) * t ^ 14 + (125090303 / 4320000) * t ^ 18 + (5475403 / 17280000) * t ^ 20 + (-16697 / 3) * d * t ^ 2 + 11466 * d * t ^ 4 + (-871528049 / 128000) * d * t ^ 6 + (23695389 / 25600) * d * t ^ 8 + (-77668757 / 576000) * d * t ^ 10 + (105531389 / 1152000) * d * t ^ 12 + (3427721 / 288000) * d * t ^ 14 + (-1200481 / 1152000) * d * t ^ 18 + (-58171 / 576000) * d * t ^ 20 + (3189127 / 20) * alpha * t ^ 2 + (-252390211 / 600) * alpha * t ^ 4 + (416498040229 / 1152000) * alpha * t ^ 6 + (-113085390749 / 1152000) * alpha * t ^ 8 + (205663879 / 230400) * alpha * t ^ 10 + (-5043609587 / 1728000) * alpha * t ^ 12 + (-21208981 / 216000) * alpha * t ^ 14 + (-26115461 / 432000) * alpha * t ^ 18 + (23865077 / 384000) * alpha * t ^ 20 + (-116879 / 72) * alpha * d * t ^ 2 + (7529663 / 3600) * alpha * d * t ^ 4 + (2207067727 / 3456000) * alpha * d * t ^ 6 + (-3902371439 / 3456000) * alpha * d * t ^ 8 + (-17511733 / 192000) * alpha * d * t ^ 10 + (142222751 / 1152000) * alpha * d * t ^ 12 + (-6713377 / 518400) * alpha * d * t ^ 14 + (3152309 / 10368000) * alpha * d * t ^ 18 + (23 / 512) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_03, v53_04, v53_10, v53_11, v53_12, v53_13, v53_14, v53_20, v53_21, v53_22, v53_23, v53_24]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24]
  try simp only [star_one, star_neg]
  linear_combination ((-116879 / 144) * t ^ 2 + (301847 / 200) * t ^ 4 + (-521100743 / 768000) * t ^ 6 + (-61602053 / 3456000) * t ^ 8 + (1093956823 / 13824000) * t ^ 10 + (-40882099 / 576000) * t ^ 12 + (-3022073 / 345600) * t ^ 14 + (-2548831 / 13824000) * t ^ 18 + (3086233 / 6912000) * d * t ^ 6 + (-1220051 / 2304000) * d * t ^ 8 + (-1721531 / 3456000) * d * t ^ 10 + (1064737 / 2304000) * d * t ^ 12 + (41 / 375) * d * t ^ 14 + (-34837 / 768000) * d * t ^ 18 + (58171 / 3456000) * d * t ^ 20 + (4847 / 518400) * d ^ 2 * t ^ 8 + (-29791 / 2764800) * d ^ 2 * t ^ 10 + (-131 / 331776) * d ^ 2 * t ^ 12 + (15397 / 6220800) * d ^ 2 * t ^ 14 + (95 / 497664) * d ^ 2 * t ^ 18 + (-95 / 1990656) * d ^ 2 * t ^ 20) * alpha_sq + ((16697 / 144) * t ^ 2 + (-17303 / 72) * t ^ 4 + (1489419 / 10240) * t ^ 6 + (-4878343 / 230400) * t ^ 8 + (128819 / 69120) * t ^ 10 + (-4228957 / 2764800) * t ^ 12 + (123131 / 2073600) * t ^ 14 + (5765 / 331776) * t ^ 18 + (95 / 663552) * t ^ 20 + (7709 / 360) * alpha * t ^ 4 + (-274580953 / 6912000) * alpha * t ^ 6 + (64396633 / 3456000) * alpha * t ^ 8 + (-1710637 / 3456000) * alpha * t ^ 10 + (6383543 / 41472000) * alpha * t ^ 12 + (25541 / 414720) * alpha * t ^ 14 + (472823 / 41472000) * alpha * t ^ 18) * d_sq
theorem v54_30 (t : ℂ) : (momentPoly 54 z54 3 0).eval t = ((-2489 / 160) * t ^ 3 + (4149 / 160) * t ^ 5 + 2 * t ^ 9 + (113 / 96) * d * t ^ 3 + (-313 / 192) * d * t ^ 5 + (-47 / 576) * d * t ^ 9 + (-15467 / 800) * alpha * t ^ 3 + (92873 / 4800) * alpha * t ^ 5 + (-17771 / 4800) * alpha * t ^ 9 + (583 / 480) * alpha * d * t ^ 3 + (-523 / 480) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_10, v53_20, v53_30]
  try simp only [phase53_00, phase53_10, phase53_20, phase53_30]
  try simp only [star_one, star_neg]
  linear_combination ((-583 / 960) * t ^ 3 + (171 / 320) * t ^ 5 + (1 / 288) * d * t ^ 3 + (1 / 384) * d * t ^ 5) * alpha_sq + ((1 / 96) * t ^ 3 + (-1 / 288) * alpha * t ^ 3 + (1 / 1152) * alpha * t ^ 5) * d_sq
theorem v54_31 (t : ℂ) : (momentPoly 54 z54 3 1).eval t = ((-6731 / 16) * t ^ 2 + (927293 / 600) * t ^ 4 + (-5209741 / 4800) * t ^ 6 + (17791 / 14400) * t ^ 10 + (-53 / 2) * d * t ^ 2 + (441 / 16) * d * t ^ 4 + (-475 / 192) * d * t ^ 6 + (-143 / 576) * d * t ^ 10 + (-30369 / 40) * alpha * t ^ 2 + (1617217 / 1200) * alpha * t ^ 4 + (-2820197 / 4800) * alpha * t ^ 6 + (-35891 / 4800) * alpha * t ^ 10 + (371 / 48) * alpha * d * t ^ 2 + (-5017 / 900) * alpha * d * t ^ 4 + (-30977 / 14400) * alpha * d * t ^ 6 + (4249 / 14400) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_10, v53_11, v53_20, v53_21, v53_30, v53_31]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21, phase53_30, phase53_31]
  try simp only [star_one, star_neg]
  linear_combination ((-371 / 96) * t ^ 2 + (23219 / 6400) * t ^ 4 + (1631 / 57600) * t ^ 6 + (67613 / 345600) * t ^ 10) * alpha_sq + ((53 / 96) * t ^ 2 + (-1331 / 2304) * t ^ 4 + (131 / 2304) * t ^ 6 + (47 / 13824) * t ^ 10 + (-593 / 11520) * alpha * t ^ 4 + (533 / 11520) * alpha * t ^ 6) * d_sq
theorem v54_32 (t : ℂ) : (momentPoly 54 z54 3 2).eval t = (17014 * t + (-978831 / 32) * t ^ 3 + (116080129 / 8000) * t ^ 5 + (-14227057 / 12800) * t ^ 7 + (54781799 / 192000) * t ^ 9 + (28266449 / 576000) * t ^ 11 + (-2150841 / 64000) * t ^ 13 + (-8507 / 6) * d * t + (89215 / 32) * d * t ^ 3 + (-21880207 / 14400) * d * t ^ 5 + (1993593 / 12800) * d * t ^ 7 + (-1342993 / 115200) * d * t ^ 9 + (140017 / 345600) * d * t ^ 11 + (-51427 / 115200) * d * t ^ 13 + (-8507 / 2) * alpha * t + (188923 / 32) * alpha * t ^ 3 + (204995 / 576) * alpha * t ^ 5 + (-234441281 / 115200) * alpha * t ^ 7 + (5318081 / 115200) * alpha * t ^ 9 + (2829263 / 345600) * alpha * t ^ 11 + (-12497063 / 345600) * alpha * t ^ 13 + (4081 / 32) * alpha * d * t ^ 3 + (-3349939 / 14400) * alpha * d * t ^ 5 + (12001493 / 115200) * alpha * d * t ^ 7 + (1037 / 7680) * alpha * d * t ^ 9 + (32893 / 38400) * alpha * d * t ^ 11 + (8357 / 23040) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_10, v53_11, v53_12, v53_20, v53_21, v53_22, v53_30, v53_31, v53_32]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22, phase53_30, phase53_31, phase53_32]
  try simp only [star_one, star_neg]
  linear_combination ((4081 / 64) * t ^ 3 + (-3318239 / 28800) * t ^ 5 + (1471781 / 28800) * t ^ 7 + (849887 / 691200) * t ^ 11 + (-2717 / 5120) * t ^ 13 + (-35 / 96) * d * t ^ 3 + (-3907 / 86400) * d * t ^ 5 + (5293 / 19200) * d * t ^ 7 + (23101 / 172800) * d * t ^ 9 + (-8311 / 518400) * d * t ^ 11 + (-17771 / 1382400) * d * t ^ 13 + (593 / 138240) * d ^ 2 * t ^ 7 + (-523 / 138240) * d ^ 2 * t ^ 9) * alpha_sq + ((105 / 32) * t ^ 3 + (-2093 / 640) * t ^ 5 + (31 / 512) * t ^ 7 + (259 / 11520) * t ^ 9 + (95 / 6912) * t ^ 11 + (-35 / 96) * alpha * t ^ 3 + (27793 / 86400) * alpha * t ^ 5 + (7901 / 172800) * alpha * t ^ 7 + (-1 / 13824) * alpha * t ^ 9 + (-371 / 32400) * alpha * t ^ 11 + (-47 / 165888) * alpha * t ^ 13) * d_sq
theorem v54_33 (t : ℂ) : (momentPoly 54 z54 3 3).eval t = (918756 + (-4892221 / 2) * t ^ 2 + (847775331 / 400) * t ^ 4 + (-69580015439 / 120000) * t ^ 6 + (476297499 / 40000) * t ^ 8 + (-3793645427 / 160000) * t ^ 10 + (57660793 / 360000) * t ^ 12 + (-156955889 / 720000) * t ^ 14 + (-21876541 / 4320000) * t ^ 18 + (-16697 / 2) * d * t ^ 2 + (1278797 / 80) * d * t ^ 4 + (-186344951 / 24000) * d * t ^ 6 + (1538167 / 9600) * d * t ^ 8 + (-2154013 / 48000) * d * t ^ 10 + (-2683213 / 144000) * d * t ^ 12 + (248317 / 16000) * d * t ^ 14 + (-47 / 144) * d * t ^ 18) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_03, v53_10, v53_11, v53_12, v53_13, v53_20, v53_21, v53_22, v53_23, v53_30, v53_31, v53_32, v53_33]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23, phase53_30, phase53_31, phase53_32, phase53_33]
  try simp only [star_one, star_neg]
  linear_combination ((116879 / 96) * t ^ 2 + (-292513 / 160) * t ^ 4 + (11912887 / 115200) * t ^ 6 + (29633501 / 57600) * t ^ 8 + (-795839 / 76800) * t ^ 10 + (151783 / 460800) * t ^ 12 + (2459333 / 691200) * t ^ 14 + (15758743 / 16588800) * t ^ 18 + (-7709 / 480) * d * t ^ 4 + (95729 / 7200) * d * t ^ 6 + (302593 / 19200) * d * t ^ 8 + (-737023 / 57600) * d * t ^ 10 + (-22501 / 86400) * d * t ^ 12 + (-15371 / 230400) * d * t ^ 14 + (157 / 1728) * d ^ 2 * t ^ 6 + (-11909 / 172800) * d ^ 2 * t ^ 8 + (-5167 / 230400) * d ^ 2 * t ^ 10 + (4349 / 1382400) * d ^ 2 * t ^ 14) * alpha_sq + ((16697 / 96) * t ^ 2 + (-11037 / 32) * t ^ 4 + (2381021 / 12800) * t ^ 6 + (-19079 / 1200) * t ^ 8 + (22789 / 19200) * t ^ 10 + (-120949 / 1382400) * t ^ 12 + (127831 / 1382400) * t ^ 14 + (2209 / 663552) * t ^ 18) * d_sq
theorem v54_34 (t : ℂ) : (momentPoly 54 z54 3 4).eval t = (3573579 * t + (-763628013 / 80) * t ^ 3 + (8655836409 / 1000) * t ^ 5 + (-29403811844279 / 9600000) * t ^ 7 + (20737248852131 / 38400000) * t ^ 9 + (-107569773037 / 800000) * t ^ 11 + (-2040334589303 / 46080000) * t ^ 13 + (604262259149 / 28800000) * t ^ 15 + (-178538413333 / 76800000) * t ^ 17 + (-2530918139 / 21600000) * t ^ 19 + (21926171071 / 230400000) * t ^ 21 + (1373073337 / 25600000) * t ^ 25 + (-1191193 / 4) * d * t + (13920089 / 16) * d * t ^ 3 + (-1065403073 / 1200) * d * t ^ 5 + (414043670369 / 1152000) * d * t ^ 7 + (-227646309643 / 4608000) * d * t ^ 9 + (4153793113 / 720000) * d * t ^ 11 + (-16295701489 / 27648000) * d * t ^ 13 + (438965543 / 1152000) * d * t ^ 15 + (49300679 / 5529600) * d * t ^ 17 + (-47243 / 32400) * d * t ^ 19 + (293790649 / 138240000) * d * t ^ 21 + (-393373 / 1105920) * d * t ^ 25 + (3573579 / 4) * alpha * t + (-147386929 / 80) * alpha * t ^ 3 + (25631303 / 60) * alpha * t ^ 5 + (6380153331487 / 5760000) * alpha * t ^ 7 + (-4618768614347 / 7680000) * alpha * t ^ 9 + (1103657269 / 120000) * alpha * t ^ 11 + (256830846347 / 9216000) * alpha * t ^ 13 + (-4852546823 / 230400) * alpha * t ^ 15 + (-41398255823 / 138240000) * alpha * t ^ 17 + (-745951909 / 3240000) * alpha * t ^ 19 + (18362250487 / 138240000) * alpha * t ^ 21 + (-1701375569 / 82944000) * alpha * t ^ 25 + (-3183763 / 80) * alpha * d * t ^ 3 + (65263133 / 600) * alpha * d * t ^ 5 + (-12435081787 / 128000) * alpha * d * t ^ 7 + (127079909747 / 4608000) * alpha * d * t ^ 9 + (43958123 / 576000) * alpha * d * t ^ 11 + (7638498797 / 27648000) * alpha * d * t ^ 13 + (769962277 / 3456000) * alpha * d * t ^ 15 + (13138659 / 1024000) * alpha * d * t ^ 17 + (30430721 / 1728000) * alpha * d * t ^ 19 + (-41276761 / 3072000) * alpha * d * t ^ 21 + (-821303 / 3072000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_03, v53_04, v53_10, v53_11, v53_12, v53_13, v53_14, v53_20, v53_21, v53_22, v53_23, v53_24, v53_30, v53_31, v53_32, v53_33, v53_34]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24, phase53_30, phase53_31, phase53_32, phase53_33, phase53_34]
  try simp only [star_one, star_neg]
  linear_combination ((3183763 / 160) * t ^ 3 + (-129696691 / 2400) * t ^ 5 + (110502272183 / 2304000) * t ^ 7 + (-249928556671 / 18432000) * t ^ 9 + (911516453 / 1843200) * t ^ 11 + (-7778622281 / 7372800) * t ^ 13 + (17902477051 / 55296000) * t ^ 15 + (-201606119 / 9216000) * t ^ 17 + (-248188943 / 66355200) * t ^ 19 + (125510677 / 18432000) * t ^ 21 + (24802063 / 55296000) * t ^ 25 + (-5461 / 48) * d * t ^ 3 + (1604083 / 28800) * d * t ^ 5 + (40948781 / 288000) * d * t ^ 7 + (-8865889 / 3072000) * d * t ^ 9 + (-1271917877 / 13824000) * d * t ^ 11 + (163745549 / 55296000) * d * t ^ 13 + (227721619 / 27648000) * d * t ^ 15 + (-11174773 / 16588800) * d * t ^ 17 + (-129736963 / 497664000) * d * t ^ 19 + (805487 / 5184000) * d * t ^ 21 + (-337649 / 13271040) * d * t ^ 25 + (184423 / 69120) * d ^ 2 * t ^ 7 + (-271650553 / 55296000) * d ^ 2 * t ^ 9 + (63224833 / 27648000) * d ^ 2 * t ^ 11 + (-7063823 / 110592000) * d ^ 2 * t ^ 13 + (3946259 / 165888000) * d ^ 2 * t ^ 15 + (8357 / 2211840) * d ^ 2 * t ^ 17 + (11267 / 2654208) * d ^ 2 * t ^ 19 + (-46597 / 20736000) * d ^ 2 * t ^ 21) * alpha_sq + ((16383 / 16) * t ^ 3 + (-646737 / 320) * t ^ 5 + (589525711 / 576000) * t ^ 7 + (-211183103 / 9216000) * t ^ 9 + (1764209 / 307200) * t ^ 11 + (-69098839 / 11059200) * t ^ 13 + (-56707691 / 27648000) * t ^ 15 + (-8197 / 368640) * t ^ 17 + (19013251 / 165888000) * t ^ 19 + (360901 / 27648000) * t ^ 21 + (5461 / 48) * alpha * t ^ 3 + (-4922383 / 28800) * alpha * t ^ 5 + (732617 / 864000) * alpha * t ^ 7 + (528363299 / 9216000) * alpha * t ^ 9 + (8693089 / 1536000) * alpha * t ^ 11 + (-402544933 / 55296000) * alpha * t ^ 13 + (3833417 / 5529600) * alpha * t ^ 15 + (-139703 / 16588800) * alpha * t ^ 17 + (-4659677 / 497664000) * alpha * t ^ 19 + (-3245 / 663552) * alpha * t ^ 21 + (-4465 / 7962624) * alpha * t ^ 25) * d_sq
theorem v54_40 (t : ℂ) : (momentPoly 54 z54 4 0).eval t = ((-71243 / 300) * t ^ 4 + (241943 / 800) * t ^ 6 + (-394253 / 19200) * t ^ 8 + (-237989 / 14400) * t ^ 10 + (5569 / 768) * t ^ 16 + (7471 / 960) * d * t ^ 4 + (-2111 / 240) * d * t ^ 6 + (171 / 320) * d * t ^ 8 + (-143 / 144) * d * t ^ 10 + (246043 / 4000) * alpha * t ^ 4 + (-3238843 / 12000) * alpha * t ^ 6 + (3225791 / 16000) * alpha * t ^ 8 + (-9423 / 4000) * alpha * t ^ 10 + (-173441 / 48000) * alpha * t ^ 16 + (26809 / 4800) * alpha * d * t ^ 4 + (-2443 / 400) * alpha * d * t ^ 6 + (-619 / 2304) * alpha * d * t ^ 8 + (59213 / 43200) * alpha * d * t ^ 10 + (-95 / 6912) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_10, v53_20, v53_30, v53_40]
  try simp only [phase53_00, phase53_10, phase53_20, phase53_30, phase53_40]
  try simp only [star_one, star_neg]
  linear_combination ((-26809 / 9600) * t ^ 4 + (90773 / 28800) * t ^ 6 + (-67613 / 86400) * t ^ 10 + (593 / 5760) * d * t ^ 4 + (1 / 96) * d * t ^ 6 + (-57 / 640) * d * t ^ 8 + (-1 / 1728) * d ^ 2 * t ^ 6 + (1 / 13824) * d ^ 2 * t ^ 8) * alpha_sq + ((-115 / 1152) * t ^ 4 + (15 / 128) * t ^ 6 + (-1 / 4608) * t ^ 8 + (47 / 3456) * t ^ 10 + (-593 / 5760) * alpha * t ^ 4 + (533 / 5760) * alpha * t ^ 6) * d_sq
theorem v54_41 (t : ℂ) : (momentPoly 54 z54 4 1).eval t = ((-52269 / 16) * t ^ 3 + (255948747 / 32000) * t ^ 5 + (-210024241 / 48000) * t ^ 7 + (33960601 / 192000) * t ^ 9 + (-61332019 / 144000) * t ^ 11 + (1528573 / 192000) * t ^ 17 + (3955 / 16) * d * t ^ 3 + (-32328533 / 57600) * d * t ^ 5 + (2904991 / 9600) * d * t ^ 7 + (-1344701 / 115200) * d * t ^ 9 + (65071 / 3456) * d * t ^ 11 + (-787 / 1536) * d * t ^ 17 + (-324807 / 80) * alpha * t ^ 3 + (2237335111 / 288000) * alpha * t ^ 5 + (-60978519 / 16000) * alpha * t ^ 7 + (-355955389 / 576000) * alpha * t ^ 9 + (296849111 / 432000) * alpha * t ^ 11 + (4420309 / 1728000) * alpha * t ^ 17 + (4081 / 16) * alpha * d * t ^ 3 + (-136982993 / 288000) * alpha * d * t ^ 5 + (33628513 / 144000) * alpha * d * t ^ 7 + (-8499973 / 576000) * alpha * d * t ^ 9 + (1197287 / 432000) * alpha * d * t ^ 11 + (496573 / 1728000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_10, v53_11, v53_20, v53_21, v53_30, v53_31, v53_40, v53_41]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21, phase53_30, phase53_31, phase53_40, phase53_41]
  try simp only [star_one, star_neg]
  linear_combination ((-4081 / 32) * t ^ 3 + (129744127 / 576000) * t ^ 5 + (-11492237 / 128000) * t ^ 7 + (-1409833 / 192000) * t ^ 9 + (-35849 / 32000) * t ^ 11 + (173441 / 1152000) * t ^ 17 + (35 / 48) * d * t ^ 3 + (-47 / 2160) * d * t ^ 5 + (-827 / 1536) * d * t ^ 7 + (-2269 / 17280) * d * t ^ 9 + (-47 / 10368) * d * t ^ 11 + (-95 / 55296) * d * t ^ 17 + (-593 / 138240) * d ^ 2 * t ^ 7 + (523 / 138240) * d ^ 2 * t ^ 9) * alpha_sq + ((35 / 16) * t ^ 3 + (-791 / 320) * t ^ 5 + (1621 / 4608) * t ^ 7 + (-259 / 11520) * t ^ 9 + (95 / 1728) * t ^ 11 + (-35 / 48) * alpha * t ^ 3 + (11473 / 21600) * alpha * t ^ 5 + (8317 / 38400) * alpha * t ^ 7 + (65 / 6912) * alpha * t ^ 9 + (-7111 / 129600) * alpha * t ^ 11 + (95 / 165888) * alpha * t ^ 17) * d_sq
theorem v54_42 (t : ℂ) : (momentPoly 54 z54 4 2).eval t = ((-2120519 / 24) * t ^ 2 + (479258651 / 1200) * t ^ 4 + (-328274453281 / 640000) * t ^ 6 + (377896277339 / 1920000) * t ^ 8 + (6910981681 / 1152000) * t ^ 10 + (-1196008517 / 2880000) * t ^ 12 + (-44240353 / 270000) * t ^ 14 + (125090303 / 4320000) * t ^ 18 + (5475403 / 17280000) * t ^ 20 + (-16697 / 3) * d * t ^ 2 + 11466 * d * t ^ 4 + (-871528049 / 128000) * d * t ^ 6 + (23695389 / 25600) * d * t ^ 8 + (-77668757 / 576000) * d * t ^ 10 + (105531389 / 1152000) * d * t ^ 12 + (3427721 / 288000) * d * t ^ 14 + (-1200481 / 1152000) * d * t ^ 18 + (-58171 / 576000) * d * t ^ 20 + (-3189127 / 20) * alpha * t ^ 2 + (252390211 / 600) * alpha * t ^ 4 + (-416498040229 / 1152000) * alpha * t ^ 6 + (113085390749 / 1152000) * alpha * t ^ 8 + (-205663879 / 230400) * alpha * t ^ 10 + (5043609587 / 1728000) * alpha * t ^ 12 + (21208981 / 216000) * alpha * t ^ 14 + (26115461 / 432000) * alpha * t ^ 18 + (-23865077 / 384000) * alpha * t ^ 20 + (116879 / 72) * alpha * d * t ^ 2 + (-7529663 / 3600) * alpha * d * t ^ 4 + (-2207067727 / 3456000) * alpha * d * t ^ 6 + (3902371439 / 3456000) * alpha * d * t ^ 8 + (17511733 / 192000) * alpha * d * t ^ 10 + (-142222751 / 1152000) * alpha * d * t ^ 12 + (6713377 / 518400) * alpha * d * t ^ 14 + (-3152309 / 10368000) * alpha * d * t ^ 18 + (-23 / 512) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_10, v53_11, v53_12, v53_20, v53_21, v53_22, v53_30, v53_31, v53_32, v53_40, v53_41, v53_42]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22, phase53_30, phase53_31, phase53_32, phase53_40, phase53_41, phase53_42]
  try simp only [star_one, star_neg]
  linear_combination ((-116879 / 144) * t ^ 2 + (301847 / 200) * t ^ 4 + (-521100743 / 768000) * t ^ 6 + (-61602053 / 3456000) * t ^ 8 + (1093956823 / 13824000) * t ^ 10 + (-40882099 / 576000) * t ^ 12 + (-3022073 / 345600) * t ^ 14 + (-2548831 / 13824000) * t ^ 18 + (3086233 / 6912000) * d * t ^ 6 + (-1220051 / 2304000) * d * t ^ 8 + (-1721531 / 3456000) * d * t ^ 10 + (1064737 / 2304000) * d * t ^ 12 + (41 / 375) * d * t ^ 14 + (-34837 / 768000) * d * t ^ 18 + (58171 / 3456000) * d * t ^ 20 + (4847 / 518400) * d ^ 2 * t ^ 8 + (-29791 / 2764800) * d ^ 2 * t ^ 10 + (-131 / 331776) * d ^ 2 * t ^ 12 + (15397 / 6220800) * d ^ 2 * t ^ 14 + (95 / 497664) * d ^ 2 * t ^ 18 + (-95 / 1990656) * d ^ 2 * t ^ 20) * alpha_sq + ((16697 / 144) * t ^ 2 + (-17303 / 72) * t ^ 4 + (1489419 / 10240) * t ^ 6 + (-4878343 / 230400) * t ^ 8 + (128819 / 69120) * t ^ 10 + (-4228957 / 2764800) * t ^ 12 + (123131 / 2073600) * t ^ 14 + (5765 / 331776) * t ^ 18 + (95 / 663552) * t ^ 20 + (-7709 / 360) * alpha * t ^ 4 + (274580953 / 6912000) * alpha * t ^ 6 + (-64396633 / 3456000) * alpha * t ^ 8 + (1710637 / 3456000) * alpha * t ^ 10 + (-6383543 / 41472000) * alpha * t ^ 12 + (-25541 / 414720) * alpha * t ^ 14 + (-472823 / 41472000) * alpha * t ^ 18) * d_sq
theorem v54_43 (t : ℂ) : (momentPoly 54 z54 4 3).eval t = (3573579 * t + (-763628013 / 80) * t ^ 3 + (8655836409 / 1000) * t ^ 5 + (-29403811844279 / 9600000) * t ^ 7 + (20737248852131 / 38400000) * t ^ 9 + (-107569773037 / 800000) * t ^ 11 + (-2040334589303 / 46080000) * t ^ 13 + (604262259149 / 28800000) * t ^ 15 + (-178538413333 / 76800000) * t ^ 17 + (-2530918139 / 21600000) * t ^ 19 + (21926171071 / 230400000) * t ^ 21 + (1373073337 / 25600000) * t ^ 25 + (-1191193 / 4) * d * t + (13920089 / 16) * d * t ^ 3 + (-1065403073 / 1200) * d * t ^ 5 + (414043670369 / 1152000) * d * t ^ 7 + (-227646309643 / 4608000) * d * t ^ 9 + (4153793113 / 720000) * d * t ^ 11 + (-16295701489 / 27648000) * d * t ^ 13 + (438965543 / 1152000) * d * t ^ 15 + (49300679 / 5529600) * d * t ^ 17 + (-47243 / 32400) * d * t ^ 19 + (293790649 / 138240000) * d * t ^ 21 + (-393373 / 1105920) * d * t ^ 25 + (-3573579 / 4) * alpha * t + (147386929 / 80) * alpha * t ^ 3 + (-25631303 / 60) * alpha * t ^ 5 + (-6380153331487 / 5760000) * alpha * t ^ 7 + (4618768614347 / 7680000) * alpha * t ^ 9 + (-1103657269 / 120000) * alpha * t ^ 11 + (-256830846347 / 9216000) * alpha * t ^ 13 + (4852546823 / 230400) * alpha * t ^ 15 + (41398255823 / 138240000) * alpha * t ^ 17 + (745951909 / 3240000) * alpha * t ^ 19 + (-18362250487 / 138240000) * alpha * t ^ 21 + (1701375569 / 82944000) * alpha * t ^ 25 + (3183763 / 80) * alpha * d * t ^ 3 + (-65263133 / 600) * alpha * d * t ^ 5 + (12435081787 / 128000) * alpha * d * t ^ 7 + (-127079909747 / 4608000) * alpha * d * t ^ 9 + (-43958123 / 576000) * alpha * d * t ^ 11 + (-7638498797 / 27648000) * alpha * d * t ^ 13 + (-769962277 / 3456000) * alpha * d * t ^ 15 + (-13138659 / 1024000) * alpha * d * t ^ 17 + (-30430721 / 1728000) * alpha * d * t ^ 19 + (41276761 / 3072000) * alpha * d * t ^ 21 + (821303 / 3072000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_03, v53_10, v53_11, v53_12, v53_13, v53_20, v53_21, v53_22, v53_23, v53_30, v53_31, v53_32, v53_33, v53_40, v53_41, v53_42, v53_43]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23, phase53_30, phase53_31, phase53_32, phase53_33, phase53_40, phase53_41, phase53_42, phase53_43]
  try simp only [star_one, star_neg]
  linear_combination ((3183763 / 160) * t ^ 3 + (-129696691 / 2400) * t ^ 5 + (110502272183 / 2304000) * t ^ 7 + (-249928556671 / 18432000) * t ^ 9 + (911516453 / 1843200) * t ^ 11 + (-7778622281 / 7372800) * t ^ 13 + (17902477051 / 55296000) * t ^ 15 + (-201606119 / 9216000) * t ^ 17 + (-248188943 / 66355200) * t ^ 19 + (125510677 / 18432000) * t ^ 21 + (24802063 / 55296000) * t ^ 25 + (-5461 / 48) * d * t ^ 3 + (1604083 / 28800) * d * t ^ 5 + (40948781 / 288000) * d * t ^ 7 + (-8865889 / 3072000) * d * t ^ 9 + (-1271917877 / 13824000) * d * t ^ 11 + (163745549 / 55296000) * d * t ^ 13 + (227721619 / 27648000) * d * t ^ 15 + (-11174773 / 16588800) * d * t ^ 17 + (-129736963 / 497664000) * d * t ^ 19 + (805487 / 5184000) * d * t ^ 21 + (-337649 / 13271040) * d * t ^ 25 + (184423 / 69120) * d ^ 2 * t ^ 7 + (-271650553 / 55296000) * d ^ 2 * t ^ 9 + (63224833 / 27648000) * d ^ 2 * t ^ 11 + (-7063823 / 110592000) * d ^ 2 * t ^ 13 + (3946259 / 165888000) * d ^ 2 * t ^ 15 + (8357 / 2211840) * d ^ 2 * t ^ 17 + (11267 / 2654208) * d ^ 2 * t ^ 19 + (-46597 / 20736000) * d ^ 2 * t ^ 21) * alpha_sq + ((16383 / 16) * t ^ 3 + (-646737 / 320) * t ^ 5 + (589525711 / 576000) * t ^ 7 + (-211183103 / 9216000) * t ^ 9 + (1764209 / 307200) * t ^ 11 + (-69098839 / 11059200) * t ^ 13 + (-56707691 / 27648000) * t ^ 15 + (-8197 / 368640) * t ^ 17 + (19013251 / 165888000) * t ^ 19 + (360901 / 27648000) * t ^ 21 + (-5461 / 48) * alpha * t ^ 3 + (4922383 / 28800) * alpha * t ^ 5 + (-732617 / 864000) * alpha * t ^ 7 + (-528363299 / 9216000) * alpha * t ^ 9 + (-8693089 / 1536000) * alpha * t ^ 11 + (402544933 / 55296000) * alpha * t ^ 13 + (-3833417 / 5529600) * alpha * t ^ 15 + (139703 / 16588800) * alpha * t ^ 17 + (4659677 / 497664000) * alpha * t ^ 19 + (3245 / 663552) * alpha * t ^ 21 + (4465 / 7962624) * alpha * t ^ 25) * d_sq
theorem v54_44 (t : ℂ) : (momentPoly 54 z54 4 4).eval t = (192973266 + (-678593860) * t ^ 2 + (43671298461 / 50) * t ^ 4 + (-1797208672357 / 3750) * t ^ 6 + (6968337801997849 / 72000000) * t ^ 8 + (-110161151196149 / 8000000) * t ^ 10 + (1905557771377901 / 230400000) * t ^ 12 + (103595706944251 / 1728000000) * t ^ 14 + (258142859456719 / 2304000000) * t ^ 16 + (-1436268639061 / 288000000) * t ^ 18 + (-7894048910087 / 3456000000) * t ^ 20 + (6453559861753 / 576000000) * t ^ 22 + (-9211601253781 / 1728000000) * t ^ 24 + (57606942551 / 324000000) * t ^ 26 + (789525104237 / 20736000000) * t ^ 32 + (-2316020) * d * t ^ 2 + (197623321 / 30) * d * t ^ 4 + (-3133215267 / 500) * d * t ^ 6 + (20073350913361 / 9600000) * d * t ^ 8 + (-2363770659889 / 14400000) * d * t ^ 10 + (12911435625229 / 230400000) * d * t ^ 12 + (563509595081 / 23040000) * d * t ^ 14 + (-6495324395681 / 460800000) * d * t ^ 16 + (225236852537 / 172800000) * d * t ^ 18 + (839781655871 / 2073600000) * d * t ^ 20 + (-11326245721 / 345600000) * d * t ^ 22 + (-4211729 / 4608000) * d * t ^ 24 + (-575704867 / 14400000) * d * t ^ 26 + (3295379 / 11059200) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z54, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v53_00, v53_01, v53_02, v53_03, v53_04, v53_10, v53_11, v53_12, v53_13, v53_14, v53_20, v53_21, v53_22, v53_23, v53_24, v53_30, v53_31, v53_32, v53_33, v53_34, v53_40, v53_41, v53_42, v53_43, v53_44]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24, phase53_30, phase53_31, phase53_32, phase53_33, phase53_34, phase53_40, phase53_41, phase53_42, phase53_43, phase53_44]
  try simp only [star_one, star_neg]
  linear_combination ((4053035 / 12) * t ^ 2 + (-45204509 / 60) * t ^ 4 + (464124771 / 1600) * t ^ 6 + (3817055871197 / 11520000) * t ^ 8 + (-806747253001 / 3840000) * t ^ 10 + (11920902953 / 2764800) * t ^ 12 + (75528951689 / 25920000) * t ^ 14 + (-31691664461 / 11520000) * t ^ 16 + (29692944893 / 46080000) * t ^ 18 + (-167390638549 / 207360000) * t ^ 20 + (361710233 / 8640000) * t ^ 22 + (-330335981 / 41472000) * t ^ 26 + (-1191337 / 180) * d * t ^ 4 + (13806619 / 1200) * d * t ^ 6 + (98431249 / 55296) * d * t ^ 8 + (-4369449041 / 384000) * d * t ^ 10 + (244260569003 / 55296000) * d * t ^ 12 + (19735892873 / 82944000) * d * t ^ 14 + (4579470409 / 110592000) * d * t ^ 16 + (577691923 / 41472000) * d * t ^ 18 + (12107069 / 3981312) * d * t ^ 20 + (-56340811 / 16588800) * d * t ^ 22 + (4211729 / 27648000) * d * t ^ 24 + (-383249 / 1658880) * d * t ^ 26 + (-3295379 / 66355200) * d * t ^ 32 + (32557 / 864) * d ^ 2 * t ^ 6 + (-4491721 / 86400) * d ^ 2 * t ^ 8 + (-2527597 / 288000) * d ^ 2 * t ^ 10 + (1293892363 / 55296000) * d ^ 2 * t ^ 12 + (174287887 / 82944000) * d ^ 2 * t ^ 14 + (-871659041 / 331776000) * d ^ 2 * t ^ 16 + (4085789 / 16588800) * d ^ 2 * t ^ 18 + (92093 / 2488320) * d ^ 2 * t ^ 20 + (-8066153 / 165888000) * d ^ 2 * t ^ 22 + (-18745 / 7962624) * d ^ 2 * t ^ 24 + (292543 / 29859840) * d ^ 2 * t ^ 26 + (-9025 / 95551488) * d ^ 2 * t ^ 32) * alpha_sq + ((579005 / 12) * t ^ 2 + (-568547 / 4) * t ^ 4 + (2085767953 / 14400) * t ^ 6 + (-392596093933 / 6912000) * t ^ 8 + (5064940031 / 768000) * t ^ 10 + (-224582204257 / 276480000) * t ^ 12 + (12624793579 / 82944000) * t ^ 14 + (-9617432207 / 110592000) * t ^ 16 + (-3240203 / 2764800) * t ^ 18 + (-107799911 / 41472000) * t ^ 20 + (-178379243 / 276480000) * t ^ 22 + (18745 / 2654208) * t ^ 24 + (858989 / 9953280) * t ^ 26 + (9025 / 31850496) * t ^ 32) * d_sq
#print axioms v54_00
#print axioms v54_11
#print axioms v54_22
#print axioms v54_33
#print axioms v54_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v55_02 (t : ℂ) : (momentPoly 55 z55 0 2).eval t = ((67 / 48) * t ^ 2 + (809 / 96) * t ^ 4 + (-1 / 4) * d * t ^ 2 + (563 / 120) * alpha * t ^ 2 + (-171 / 40) * alpha * t ^ 4 + (-1 / 16) * alpha * d * t ^ 2 + (1 / 96) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02]
  try simp only [phase53_00, phase53_01, phase53_02]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 48) * t ^ 2) * alpha_sq + ((1 / 144) * t ^ 2) * d_sq
theorem v55_03 (t : ℂ) : (momentPoly 55 z55 0 3).eval t = ((-117 / 64) * t ^ 3 + (1747 / 64) * t ^ 5 + 2 * t ^ 9 + (143 / 96) * d * t ^ 3 + (-45 / 16) * d * t ^ 5 + (-47 / 384) * d * t ^ 9 + (18517 / 800) * alpha * t ^ 3 + (-24637 / 1200) * alpha * t ^ 5 + (103051 / 28800) * alpha * t ^ 9 + (-573 / 320) * alpha * d * t ^ 3 + (523 / 320) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_03]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03]
  try simp only [star_one, star_neg]
  linear_combination ((-191 / 320) * t ^ 3 + (171 / 320) * t ^ 5 + (7 / 1152) * d * t ^ 3 + (1 / 576) * d * t ^ 5) * alpha_sq + ((1 / 48) * t ^ 3 + (7 / 1152) * alpha * t ^ 3 + (-1 / 576) * alpha * t ^ 5) * d_sq
theorem v55_04 (t : ℂ) : (momentPoly 55 z55 0 4).eval t = ((-272177 / 800) * t ^ 4 + (695153 / 1600) * t ^ 6 + (448847 / 19200) * t ^ 8 + (3691 / 2880) * t ^ 10 + (37831 / 4608) * t ^ 16 + (9377 / 960) * d * t ^ 4 + (-8871 / 640) * d * t ^ 6 + (513 / 640) * d * t ^ 8 + (-143 / 96) * d * t ^ 10 + (21403 / 375) * alpha * t ^ 4 + (9018647 / 48000) * alpha * t ^ 6 + (-907979 / 4000) * alpha * t ^ 8 + (13733 / 9000) * alpha * t ^ 10 + (173441 / 48000) * alpha * t ^ 16 + (-129653 / 14400) * alpha * d * t ^ 4 + (44449 / 4800) * alpha * d * t ^ 6 + (119 / 256) * alpha * d * t ^ 8 + (-9473 / 4800) * alpha * d * t ^ 10 + (95 / 4608) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_03, v54_04]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04]
  try simp only [star_one, star_neg]
  linear_combination ((-15467 / 4800) * t ^ 4 + (92873 / 28800) * t ^ 6 + (-10673 / 14400) * t ^ 10 + (583 / 2880) * d * t ^ 4 + (-473 / 5760) * d * t ^ 6 + (-57 / 640) * d * t ^ 8 + (-7 / 6912) * d ^ 2 * t ^ 6 + (1 / 6912) * d ^ 2 * t ^ 8) * alpha_sq + ((-113 / 576) * t ^ 4 + (211 / 768) * t ^ 6 + (-1 / 2304) * t ^ 8 + (47 / 1728) * t ^ 10 + (583 / 2880) * alpha * t ^ 4 + (-533 / 2880) * alpha * t ^ 6) * d_sq
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
theorem v55_12 (t : ℂ) : (momentPoly 55 z55 1 2).eval t = (109 * t + (-5489 / 64) * t ^ 3 + (913 / 192) * t ^ 5 + (-109 / 8) * d * t + (2503 / 192) * d * t ^ 3 + (-59 / 64) * d * t ^ 5 + (545 / 24) * alpha * t + (-39233 / 2880) * alpha * t ^ 3 + (-20117 / 2880) * alpha * t ^ 5 + (-191 / 320) * alpha * d * t ^ 3 + (523 / 960) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_10, v54_11, v54_12]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12]
  try simp only [star_one, star_neg]
  linear_combination ((191 / 960) * t ^ 3 + (-57 / 320) * t ^ 5 + (-7 / 3456) * d * t ^ 3 + (-1 / 1728) * d * t ^ 5) * alpha_sq + ((1 / 48) * t ^ 3 + (7 / 3456) * alpha * t ^ 3 + (-1 / 1728) * alpha * t ^ 5) * d_sq
theorem v55_13 (t : ℂ) : (momentPoly 55 z55 1 3).eval t = ((1809 / 8) * t ^ 2 + (1015319 / 960) * t ^ 4 + (-553663 / 480) * t ^ 6 + (26357 / 5760) * t ^ 10 + (-81 / 2) * d * t ^ 2 + (7747 / 192) * d * t ^ 4 + (-285 / 64) * d * t ^ 6 + (-143 / 384) * d * t ^ 10 + (15201 / 20) * alpha * t ^ 2 + (-2065631 / 1600) * alpha * t ^ 4 + (2568937 / 4800) * alpha * t ^ 6 + (214171 / 28800) * alpha * t ^ 10 + (-81 / 8) * alpha * d * t ^ 2 + (95633 / 14400) * alpha * d * t ^ 4 + (493 / 150) * alpha * d * t ^ 6 + (-1383 / 3200) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_03, v54_10, v54_11, v54_12, v54_13]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13]
  try simp only [star_one, star_neg]
  linear_combination ((-27 / 8) * t ^ 2 + (90673 / 28800) * t ^ 4 + (1279 / 38400) * t ^ 6 + (10673 / 57600) * t ^ 10) * alpha_sq + ((9 / 8) * t ^ 2 + (-1331 / 1152) * t ^ 4 + (619 / 4608) * t ^ 6 + (47 / 6912) * t ^ 10 + (583 / 5760) * alpha * t ^ 4 + (-533 / 5760) * alpha * t ^ 6) * d_sq
theorem v55_14 (t : ℂ) : (momentPoly 55 z55 1 4).eval t = ((-12519 / 32) * t ^ 3 + (67251397 / 12800) * t ^ 5 + (-81240541 / 19200) * t ^ 7 + (3125761 / 15360) * t ^ 9 + (-20705423 / 57600) * t ^ 11 + (1951073 / 230400) * t ^ 17 + (15301 / 48) * d * t ^ 3 + (-100084639 / 115200) * d * t ^ 5 + (10078663 / 19200) * d * t ^ 7 + (-1748351 / 76800) * d * t ^ 9 + (62909 / 2304) * d * t ^ 11 + (-2737 / 3072) * d * t ^ 17 + (1981319 / 400) * alpha * t ^ 3 + (-4874428837 / 576000) * alpha * t ^ 5 + (350185969 / 96000) * alpha * t ^ 7 + (212107331 / 384000) * alpha * t ^ 9 + (-520900627 / 864000) * alpha * t ^ 11 + (-10892743 / 3456000) * alpha * t ^ 17 + (-61311 / 160) * alpha * d * t ^ 3 + (135592793 / 192000) * alpha * d * t ^ 5 + (-11106621 / 32000) * alpha * d * t ^ 7 + (3251641 / 128000) * alpha * d * t ^ 9 + (-387179 / 96000) * alpha * d * t ^ 11 + (-496573 / 1152000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_03, v54_04, v54_10, v54_11, v54_12, v54_13, v54_14]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14]
  try simp only [star_one, star_neg]
  linear_combination ((-20437 / 160) * t ^ 3 + (64258351 / 288000) * t ^ 5 + (-24963127 / 288000) * t ^ 7 + (-3225791 / 384000) * t ^ 9 + (-330641 / 288000) * t ^ 11 + (173441 / 1152000) * t ^ 17 + (749 / 576) * d * t ^ 3 + (-41663 / 69120) * d * t ^ 5 + (-34181 / 69120) * d * t ^ 7 + (-11863 / 92160) * d * t ^ 9 + (-329 / 41472) * d * t ^ 11 + (-95 / 82944) * d * t ^ 17 + (-583 / 69120) * d ^ 2 * t ^ 7 + (523 / 69120) * d ^ 2 * t ^ 9) * alpha_sq + ((107 / 24) * t ^ 3 + (-113311 / 23040) * t ^ 5 + (18527 / 23040) * t ^ 7 + (-259 / 5760) * t ^ 9 + (95 / 864) * t ^ 11 + (749 / 576) * alpha * t ^ 3 + (-305861 / 345600) * alpha * t ^ 5 + (-16459 / 38400) * alpha * t ^ 7 + (-1231 / 55296) * alpha * t ^ 9 + (110201 / 1036800) * alpha * t ^ 11 + (-95 / 82944) * alpha * t ^ 17) * d_sq
theorem v55_20 (t : ℂ) : (momentPoly 55 z55 2 0).eval t = ((67 / 48) * t ^ 2 + (809 / 96) * t ^ 4 + (-1 / 4) * d * t ^ 2 + (-563 / 120) * alpha * t ^ 2 + (171 / 40) * alpha * t ^ 4 + (1 / 16) * alpha * d * t ^ 2 + (-1 / 96) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_10, v54_20]
  try simp only [phase53_00, phase53_10, phase53_20]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 48) * t ^ 2) * alpha_sq + ((1 / 144) * t ^ 2) * d_sq
theorem v55_21 (t : ℂ) : (momentPoly 55 z55 2 1).eval t = (109 * t + (-5489 / 64) * t ^ 3 + (913 / 192) * t ^ 5 + (-109 / 8) * d * t + (2503 / 192) * d * t ^ 3 + (-59 / 64) * d * t ^ 5 + (-545 / 24) * alpha * t + (39233 / 2880) * alpha * t ^ 3 + (20117 / 2880) * alpha * t ^ 5 + (191 / 320) * alpha * d * t ^ 3 + (-523 / 960) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_10, v54_11, v54_20, v54_21]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21]
  try simp only [star_one, star_neg]
  linear_combination ((191 / 960) * t ^ 3 + (-57 / 320) * t ^ 5 + (-7 / 3456) * d * t ^ 3 + (-1 / 1728) * d * t ^ 5) * alpha_sq + ((1 / 48) * t ^ 3 + (-7 / 3456) * alpha * t ^ 3 + (1 / 1728) * alpha * t ^ 5) * d_sq
theorem v55_22 (t : ℂ) : (momentPoly 55 z55 2 2).eval t = (5995 + (-9702) * t ^ 2 + (53176957 / 14400) * t ^ 4 + (2321647 / 28800) * t ^ 6 + (2045639 / 28800) * t ^ 8 + (-54) * d * t ^ 2 + (48521 / 960) * d * t ^ 4 + (-843 / 640) * d * t ^ 6 + (-171 / 640) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_10, v54_11, v54_12, v54_20, v54_21, v54_22]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22]
  try simp only [star_one, star_neg]
  linear_combination ((9 / 2) * t ^ 2 + (-26989 / 8640) * t ^ 4 + (-9671 / 8640) * t ^ 6 + (-583 / 8640) * d * t ^ 4 + (473 / 17280) * d * t ^ 6 + (19 / 640) * d * t ^ 8 + (7 / 20736) * d ^ 2 * t ^ 6 + (-1 / 20736) * d ^ 2 * t ^ 8) * alpha_sq + ((3 / 2) * t ^ 2 + (-2549 / 1728) * t ^ 4 + (605 / 6912) * t ^ 6 + (1 / 6912) * t ^ 8) * d_sq
theorem v55_23 (t : ℂ) : (momentPoly 55 z55 2 3).eval t = (17659 * t + (-1761969 / 64) * t ^ 3 + (2193607001 / 192000) * t ^ 5 + (-1099897 / 768) * t ^ 7 + (66497449 / 192000) * t ^ 9 + (70475963 / 1152000) * t ^ 11 + (-11533721 / 384000) * t ^ 13 + (-17659 / 8) * d * t + (267821 / 64) * d * t ^ 3 + (-10347943 / 4608) * d * t ^ 5 + (15475531 / 57600) * d * t ^ 7 + (-855859 / 38400) * d * t ^ 9 + (115661 / 230400) * d * t ^ 11 + (-61027 / 76800) * d * t ^ 13 + (88295 / 24) * alpha * t + (-4197931 / 960) * alpha * t ^ 3 + (-142006783 / 115200) * alpha * t ^ 5 + (113076407 / 57600) * alpha * t ^ 7 + (-6028253 / 115200) * alpha * t ^ 9 + (3592871 / 691200) * alpha * t ^ 11 + (27112781 / 691200) * alpha * t ^ 13 + (-61311 / 320) * alpha * d * t ^ 3 + (39951803 / 115200) * alpha * d * t ^ 5 + (-987259 / 6400) * alpha * d * t ^ 7 + (-433 / 2560) * alpha * d * t ^ 9 + (-32893 / 25600) * alpha * d * t ^ 11 + (-8357 / 15360) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_03, v54_10, v54_11, v54_12, v54_13, v54_20, v54_21, v54_22, v54_23]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23]
  try simp only [star_one, star_neg]
  linear_combination ((20437 / 320) * t ^ 3 + (-101557 / 900) * t ^ 5 + (2820197 / 57600) * t ^ 7 + (280129 / 230400) * t ^ 11 + (-2717 / 5120) * t ^ 13 + (-749 / 1152) * d * t ^ 3 + (7993 / 43200) * d * t ^ 5 + (53113 / 172800) * d * t ^ 7 + (189583 / 1382400) * d * t ^ 9 + (-127001 / 4147200) * d * t ^ 11 + (-24869 / 2073600) * d * t ^ 13 + (583 / 69120) * d ^ 2 * t ^ 7 + (-523 / 69120) * d ^ 2 * t ^ 9) * alpha_sq + ((107 / 16) * t ^ 3 + (-151289 / 23040) * t ^ 5 + (1741 / 7680) * t ^ 7 + (259 / 5760) * t ^ 9 + (95 / 3456) * t ^ 11 + (749 / 1152) * alpha * t ^ 3 + (-24143 / 43200) * alpha * t ^ 5 + (-1969 / 21600) * alpha * t ^ 7 + (7 / 55296) * alpha * t ^ 9 + (93751 / 4147200) * alpha * t ^ 11 + (47 / 82944) * alpha * t ^ 13) * d_sq
theorem v55_24 (t : ℂ) : (momentPoly 55 z55 2 4).eval t = ((145189 / 3) * t ^ 2 + (77673133 / 480) * t ^ 4 + (-2358646107299 / 5760000) * t ^ 6 + (745663694113 / 3840000) * t ^ 8 + (10176157889 / 1152000) * t ^ 10 + (-115424977093 / 69120000) * t ^ 12 + (-1174952467 / 17280000) * t ^ 14 + (3521722313 / 69120000) * t ^ 18 + (511001431 / 34560000) * t ^ 20 + (-8668) * d * t ^ 2 + (410591 / 24) * d * t ^ 4 + (-1297038579 / 128000) * d * t ^ 6 + (3897512923 / 2304000) * d * t ^ 8 + (-43934297 / 192000) * d * t ^ 10 + (204298979 / 1536000) * d * t ^ 12 + (5873317 / 384000) * d * t ^ 14 + (-2603521 / 1536000) * d * t ^ 18 + (-58171 / 384000) * d * t ^ 20 + (2440042 / 15) * alpha * t ^ 2 + (-40199519 / 100) * alpha * t ^ 4 + (367411870391 / 1152000) * alpha * t ^ 6 + (-7088221031 / 92160) * alpha * t ^ 8 + (34949197 / 76800) * alpha * t ^ 10 + (-40651248223 / 13824000) * alpha * t ^ 12 + (-73557737 / 3456000) * alpha * t ^ 14 + (-709178453 / 13824000) * alpha * t ^ 18 + (160870247 / 2304000) * alpha * t ^ 20 + (-2167) * alpha * d * t ^ 2 + (17723371 / 7200) * alpha * d * t ^ 4 + (4695088253 / 3456000) * alpha * d * t ^ 6 + (-11729874797 / 6912000) * alpha * d * t ^ 8 + (-70577681 / 576000) * alpha * d * t ^ 10 + (818569811 / 4608000) * alpha * d * t ^ 12 + (-14538541 / 691200) * alpha * d * t ^ 14 + (6952493 / 13824000) * alpha * d * t ^ 18 + (239 / 3072) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_03, v54_04, v54_10, v54_11, v54_12, v54_13, v54_14, v54_20, v54_21, v54_22, v54_23, v54_24]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24]
  try simp only [star_one, star_neg]
  linear_combination ((-2167 / 3) * t ^ 2 + (4805669 / 3600) * t ^ 4 + (-2031879671 / 3456000) * t ^ 6 + (-74593063 / 3456000) * t ^ 8 + (168545413 / 2304000) * t ^ 10 + (-338018791 / 5184000) * t ^ 12 + (-4852957 / 518400) * t ^ 14 + (-4420309 / 20736000) * t ^ 18 + (2985433 / 3456000) * d * t ^ 6 + (-813929 / 432000) * d * t ^ 8 + (2177837 / 6912000) * d * t ^ 10 + (5679221 / 13824000) * d * t ^ 12 + (2411693 / 10368000) * d * t ^ 14 + (-2354021 / 41472000) * d * t ^ 18 + (58171 / 3456000) * d * t ^ 20 + (26809 / 1382400) * d ^ 2 * t ^ 8 + (-2443 / 115200) * d ^ 2 * t ^ 10 + (-619 / 663552) * d ^ 2 * t ^ 12 + (59213 / 12441600) * d ^ 2 * t ^ 14 + (665 / 1990656) * d ^ 2 * t ^ 18 + (-95 / 995328) * d ^ 2 * t ^ 20) * alpha_sq + ((2167 / 9) * t ^ 2 + (-70543 / 144) * t ^ 4 + (207741589 / 691200) * t ^ 6 + (-23608331 / 460800) * t ^ 8 + (1231687 / 276480) * t ^ 10 + (-51062711 / 16588800) * t ^ 12 + (608899 / 4147200) * t ^ 14 + (27667 / 663552) * t ^ 18 + (95 / 331776) * t ^ 20 + (30899 / 720) * alpha * t ^ 4 + (-274795753 / 3456000) * alpha * t ^ 6 + (86420219 / 2304000) * alpha * t ^ 8 + (-8186123 / 6912000) * alpha * t ^ 10 + (6264043 / 20736000) * alpha * t ^ 12 + (25541 / 207360) * alpha * t ^ 14 + (472823 / 20736000) * alpha * t ^ 18) * d_sq
theorem v55_30 (t : ℂ) : (momentPoly 55 z55 3 0).eval t = ((-117 / 64) * t ^ 3 + (1747 / 64) * t ^ 5 + 2 * t ^ 9 + (143 / 96) * d * t ^ 3 + (-45 / 16) * d * t ^ 5 + (-47 / 384) * d * t ^ 9 + (-18517 / 800) * alpha * t ^ 3 + (24637 / 1200) * alpha * t ^ 5 + (-103051 / 28800) * alpha * t ^ 9 + (573 / 320) * alpha * d * t ^ 3 + (-523 / 320) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_10, v54_20, v54_30]
  try simp only [phase53_00, phase53_10, phase53_20, phase53_30]
  try simp only [star_one, star_neg]
  linear_combination ((-191 / 320) * t ^ 3 + (171 / 320) * t ^ 5 + (7 / 1152) * d * t ^ 3 + (1 / 576) * d * t ^ 5) * alpha_sq + ((1 / 48) * t ^ 3 + (-7 / 1152) * alpha * t ^ 3 + (1 / 576) * alpha * t ^ 5) * d_sq
theorem v55_31 (t : ℂ) : (momentPoly 55 z55 3 1).eval t = ((1809 / 8) * t ^ 2 + (1015319 / 960) * t ^ 4 + (-553663 / 480) * t ^ 6 + (26357 / 5760) * t ^ 10 + (-81 / 2) * d * t ^ 2 + (7747 / 192) * d * t ^ 4 + (-285 / 64) * d * t ^ 6 + (-143 / 384) * d * t ^ 10 + (-15201 / 20) * alpha * t ^ 2 + (2065631 / 1600) * alpha * t ^ 4 + (-2568937 / 4800) * alpha * t ^ 6 + (-214171 / 28800) * alpha * t ^ 10 + (81 / 8) * alpha * d * t ^ 2 + (-95633 / 14400) * alpha * d * t ^ 4 + (-493 / 150) * alpha * d * t ^ 6 + (1383 / 3200) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_10, v54_11, v54_20, v54_21, v54_30, v54_31]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21, phase53_30, phase53_31]
  try simp only [star_one, star_neg]
  linear_combination ((-27 / 8) * t ^ 2 + (90673 / 28800) * t ^ 4 + (1279 / 38400) * t ^ 6 + (10673 / 57600) * t ^ 10) * alpha_sq + ((9 / 8) * t ^ 2 + (-1331 / 1152) * t ^ 4 + (619 / 4608) * t ^ 6 + (47 / 6912) * t ^ 10 + (-583 / 5760) * alpha * t ^ 4 + (533 / 5760) * alpha * t ^ 6) * d_sq
theorem v55_32 (t : ℂ) : (momentPoly 55 z55 3 2).eval t = (17659 * t + (-1761969 / 64) * t ^ 3 + (2193607001 / 192000) * t ^ 5 + (-1099897 / 768) * t ^ 7 + (66497449 / 192000) * t ^ 9 + (70475963 / 1152000) * t ^ 11 + (-11533721 / 384000) * t ^ 13 + (-17659 / 8) * d * t + (267821 / 64) * d * t ^ 3 + (-10347943 / 4608) * d * t ^ 5 + (15475531 / 57600) * d * t ^ 7 + (-855859 / 38400) * d * t ^ 9 + (115661 / 230400) * d * t ^ 11 + (-61027 / 76800) * d * t ^ 13 + (-88295 / 24) * alpha * t + (4197931 / 960) * alpha * t ^ 3 + (142006783 / 115200) * alpha * t ^ 5 + (-113076407 / 57600) * alpha * t ^ 7 + (6028253 / 115200) * alpha * t ^ 9 + (-3592871 / 691200) * alpha * t ^ 11 + (-27112781 / 691200) * alpha * t ^ 13 + (61311 / 320) * alpha * d * t ^ 3 + (-39951803 / 115200) * alpha * d * t ^ 5 + (987259 / 6400) * alpha * d * t ^ 7 + (433 / 2560) * alpha * d * t ^ 9 + (32893 / 25600) * alpha * d * t ^ 11 + (8357 / 15360) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_10, v54_11, v54_12, v54_20, v54_21, v54_22, v54_30, v54_31, v54_32]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22, phase53_30, phase53_31, phase53_32]
  try simp only [star_one, star_neg]
  linear_combination ((20437 / 320) * t ^ 3 + (-101557 / 900) * t ^ 5 + (2820197 / 57600) * t ^ 7 + (280129 / 230400) * t ^ 11 + (-2717 / 5120) * t ^ 13 + (-749 / 1152) * d * t ^ 3 + (7993 / 43200) * d * t ^ 5 + (53113 / 172800) * d * t ^ 7 + (189583 / 1382400) * d * t ^ 9 + (-127001 / 4147200) * d * t ^ 11 + (-24869 / 2073600) * d * t ^ 13 + (583 / 69120) * d ^ 2 * t ^ 7 + (-523 / 69120) * d ^ 2 * t ^ 9) * alpha_sq + ((107 / 16) * t ^ 3 + (-151289 / 23040) * t ^ 5 + (1741 / 7680) * t ^ 7 + (259 / 5760) * t ^ 9 + (95 / 3456) * t ^ 11 + (-749 / 1152) * alpha * t ^ 3 + (24143 / 43200) * alpha * t ^ 5 + (1969 / 21600) * alpha * t ^ 7 + (-7 / 55296) * alpha * t ^ 9 + (-93751 / 4147200) * alpha * t ^ 11 + (-47 / 82944) * alpha * t ^ 13) * d_sq
theorem v55_33 (t : ℂ) : (momentPoly 55 z55 3 3).eval t = (971245 + (-2336026) * t ^ 2 + (2818378721 / 1600) * t ^ 4 + (-43699403789 / 120000) * t ^ 6 + (-240427903 / 120000) * t ^ 8 + (-1702377907 / 60000) * t ^ 10 + (18642149 / 480000) * t ^ 12 + (-270045581 / 2880000) * t ^ 14 + (-34614907 / 8640000) * t ^ 18 + (-13002) * d * t ^ 2 + (7714839 / 320) * d * t ^ 4 + (-186935631 / 16000) * d * t ^ 6 + (2280133 / 3840) * d * t ^ 8 + (-3010313 / 32000) * d * t ^ 10 + (-2696203 / 96000) * d * t ^ 12 + (648301 / 32000) * d * t ^ 14 + (-47 / 96) * d * t ^ 18) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_03, v54_10, v54_11, v54_12, v54_13, v54_20, v54_21, v54_22, v54_23, v54_30, v54_31, v54_32, v54_33]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23, phase53_30, phase53_31, phase53_32, phase53_33]
  try simp only [star_one, star_neg]
  linear_combination ((2167 / 2) * t ^ 2 + (-1430417 / 960) * t ^ 4 + (-1083001 / 11520) * t ^ 6 + (234441281 / 460800) * t ^ 8 + (-5318081 / 460800) * t ^ 10 + (5947 / 2160) * t ^ 12 + (3904429 / 921600) * t ^ 14 + (2541253 / 2764800) * t ^ 18 + (-30899 / 960) * d * t ^ 4 + (2448829 / 57600) * d * t ^ 6 + (108587 / 51200) * d * t ^ 8 + (-5655949 / 460800) * d * t ^ 10 + (-356441 / 691200) * d * t ^ 12 + (8311 / 345600) * d * t ^ 14 + (35 / 216) * d ^ 2 * t ^ 6 + (-20093 / 172800) * d ^ 2 * t ^ 8 + (-30977 / 691200) * d ^ 2 * t ^ 10 + (4249 / 691200) * d ^ 2 * t ^ 14) * alpha_sq + ((2167 / 6) * t ^ 2 + (-135097 / 192) * t ^ 4 + (2430573 / 6400) * t ^ 6 + (-17781593 / 460800) * t ^ 8 + (1404947 / 460800) * t ^ 10 + (-34099 / 172800) * t ^ 12 + (625349 / 2764800) * t ^ 14 + (2209 / 331776) * t ^ 18) * d_sq
theorem v55_34 (t : ℂ) : (momentPoly 55 z55 3 4).eval t = (3779677 * t + (-35025309 / 4) * t ^ 3 + (43018792121 / 6400) * t ^ 5 + (-83879974960291 / 38400000) * t ^ 7 + (8008786304127 / 12800000) * t ^ 9 + (-11239905776177 / 76800000) * t ^ 11 + (-536904928537 / 11520000) * t ^ 13 + (1968933353921 / 115200000) * t ^ 15 + (-126702725197 / 51200000) * t ^ 17 + (11378982577 / 691200000) * t ^ 19 + (31175591171 / 230400000) * t ^ 21 + (24978668491 / 460800000) * t ^ 25 + (-3779677 / 8) * d * t + (5323881 / 4) * d * t ^ 3 + (-338549921 / 256) * d * t ^ 5 + (497172003499 / 921600) * d * t ^ 7 + (-399585846689 / 4608000) * d * t ^ 9 + (514244639953 / 46080000) * d * t ^ 11 + (-6587964203 / 6912000) * d * t ^ 13 + (2941479073 / 4608000) * d * t ^ 15 + (34146859 / 3686400) * d * t ^ 17 + (-12885257 / 9216000) * d * t ^ 19 + (-68834363 / 46080000) * d * t ^ 21 + (-485533 / 737280) * d * t ^ 25 + (18898385 / 24) * alpha * t + (-27816197 / 20) * alpha * t ^ 3 + (-296683879 / 3840) * alpha * t ^ 5 + (27581170410589 / 23040000) * alpha * t ^ 7 + (-12308867377139 / 23040000) * alpha * t ^ 9 + (294700675189 / 15360000) * alpha * t ^ 11 + (735708248239 / 34560000) * alpha * t ^ 13 + (-1491753183247 / 69120000) * alpha * t ^ 15 + (-146072160121 / 276480000) * alpha * t ^ 17 + (-21536987479 / 82944000) * alpha * t ^ 19 + (3794469833 / 27648000) * alpha * t ^ 21 + (-3948743003 / 165888000) * alpha * t ^ 25 + (-1218771 / 20) * alpha * d * t ^ 3 + (41969261 / 256) * alpha * d * t ^ 5 + (-132757396207 / 921600) * alpha * d * t ^ 7 + (185175654509 / 4608000) * alpha * d * t ^ 9 + (81767069 / 3072000) * alpha * d * t ^ 11 + (1081366259 / 2304000) * alpha * d * t ^ 13 + (1480505323 / 4608000) * alpha * d * t ^ 15 + (138707131 / 6144000) * alpha * d * t ^ 17 + (50268749 / 1843200) * alpha * d * t ^ 19 + (-14143441 / 614400) * alpha * d * t ^ 21 + (-821303 / 2048000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_03, v54_04, v54_10, v54_11, v54_12, v54_13, v54_14, v54_20, v54_21, v54_22, v54_23, v54_24, v54_30, v54_31, v54_32, v54_33, v54_34]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24, phase53_30, phase53_31, phase53_32, phase53_33, phase53_34]
  try simp only [star_one, star_neg]
  linear_combination ((406257 / 20) * t ^ 3 + (-3408397 / 64) * t ^ 5 + (419205429349 / 9216000) * t ^ 7 + (-113085390749 / 9216000) * t ^ 9 + (910675231 / 1843200) * t ^ 11 + (-7210825487 / 6912000) * t ^ 13 + (4326364411 / 13824000) * t ^ 15 + (-461288113 / 18432000) * t ^ 17 + (-49095247 / 13824000) * t ^ 19 + (23865077 / 3072000) * t ^ 21 + (24802063 / 55296000) * t ^ 25 + (-4963 / 24) * d * t ^ 3 + (502571 / 2880) * d * t ^ 5 + (1494093829 / 9216000) * d * t ^ 7 + (-2508463 / 48000) * d * t ^ 9 + (-2695716481 / 27648000) * d * t ^ 11 + (1987729931 / 165888000) * d * t ^ 13 + (625054037 / 82944000) * d * t ^ 15 + (-15925109 / 22118400) * d * t ^ 17 + (-204795001 / 497664000) * d * t ^ 19 + (54818293 / 331776000) * d * t ^ 21 + (-472511 / 19906560) * d * t ^ 25 + (184811 / 34560) * d ^ 2 * t ^ 7 + (-271817353 / 27648000) * d ^ 2 * t ^ 9 + (14140499 / 3072000) * d ^ 2 * t ^ 11 + (-8344423 / 55296000) * d ^ 2 * t ^ 13 + (3874759 / 82944000) * d ^ 2 * t ^ 15 + (8357 / 1105920) * d ^ 2 * t ^ 17 + (11077 / 1327104) * d ^ 2 * t ^ 19 + (-46597 / 10368000) * d ^ 2 * t ^ 21) * alpha_sq + (2127 * t ^ 3 + (-1059023 / 256) * t ^ 5 + (3927182981 / 1843200) * t ^ 7 + (-7217713 / 64000) * t ^ 9 + (138189439 / 9216000) * t ^ 11 + (-234236761 / 18432000) * t ^ 13 + (-95438507 / 27648000) * t ^ 15 + (-8197 / 184320) * t ^ 17 + (39920783 / 165888000) * t ^ 19 + (360901 / 13824000) * t ^ 21 + (4963 / 24) * alpha * t ^ 3 + (-847141 / 2880) * alpha * t ^ 5 + (-692381647 / 27648000) * alpha * t ^ 7 + (199301239 / 1728000) * alpha * t ^ 9 + (95604563 / 9216000) * alpha * t ^ 11 + (-2391087743 / 165888000) * alpha * t ^ 13 + (5086019 / 3317760) * alpha * t ^ 15 + (-1344449 / 66355200) * alpha * t ^ 17 + (-11022479 / 497664000) * alpha * t ^ 19 + (-30473 / 2654208) * alpha * t ^ 21 + (-4465 / 3981312) * alpha * t ^ 25) * d_sq
theorem v55_40 (t : ℂ) : (momentPoly 55 z55 4 0).eval t = ((-272177 / 800) * t ^ 4 + (695153 / 1600) * t ^ 6 + (448847 / 19200) * t ^ 8 + (3691 / 2880) * t ^ 10 + (37831 / 4608) * t ^ 16 + (9377 / 960) * d * t ^ 4 + (-8871 / 640) * d * t ^ 6 + (513 / 640) * d * t ^ 8 + (-143 / 96) * d * t ^ 10 + (-21403 / 375) * alpha * t ^ 4 + (-9018647 / 48000) * alpha * t ^ 6 + (907979 / 4000) * alpha * t ^ 8 + (-13733 / 9000) * alpha * t ^ 10 + (-173441 / 48000) * alpha * t ^ 16 + (129653 / 14400) * alpha * d * t ^ 4 + (-44449 / 4800) * alpha * d * t ^ 6 + (-119 / 256) * alpha * d * t ^ 8 + (9473 / 4800) * alpha * d * t ^ 10 + (-95 / 4608) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_10, v54_20, v54_30, v54_40]
  try simp only [phase53_00, phase53_10, phase53_20, phase53_30, phase53_40]
  try simp only [star_one, star_neg]
  linear_combination ((-15467 / 4800) * t ^ 4 + (92873 / 28800) * t ^ 6 + (-10673 / 14400) * t ^ 10 + (583 / 2880) * d * t ^ 4 + (-473 / 5760) * d * t ^ 6 + (-57 / 640) * d * t ^ 8 + (-7 / 6912) * d ^ 2 * t ^ 6 + (1 / 6912) * d ^ 2 * t ^ 8) * alpha_sq + ((-113 / 576) * t ^ 4 + (211 / 768) * t ^ 6 + (-1 / 2304) * t ^ 8 + (47 / 1728) * t ^ 10 + (-583 / 2880) * alpha * t ^ 4 + (533 / 2880) * alpha * t ^ 6) * d_sq
theorem v55_41 (t : ℂ) : (momentPoly 55 z55 4 1).eval t = ((-12519 / 32) * t ^ 3 + (67251397 / 12800) * t ^ 5 + (-81240541 / 19200) * t ^ 7 + (3125761 / 15360) * t ^ 9 + (-20705423 / 57600) * t ^ 11 + (1951073 / 230400) * t ^ 17 + (15301 / 48) * d * t ^ 3 + (-100084639 / 115200) * d * t ^ 5 + (10078663 / 19200) * d * t ^ 7 + (-1748351 / 76800) * d * t ^ 9 + (62909 / 2304) * d * t ^ 11 + (-2737 / 3072) * d * t ^ 17 + (-1981319 / 400) * alpha * t ^ 3 + (4874428837 / 576000) * alpha * t ^ 5 + (-350185969 / 96000) * alpha * t ^ 7 + (-212107331 / 384000) * alpha * t ^ 9 + (520900627 / 864000) * alpha * t ^ 11 + (10892743 / 3456000) * alpha * t ^ 17 + (61311 / 160) * alpha * d * t ^ 3 + (-135592793 / 192000) * alpha * d * t ^ 5 + (11106621 / 32000) * alpha * d * t ^ 7 + (-3251641 / 128000) * alpha * d * t ^ 9 + (387179 / 96000) * alpha * d * t ^ 11 + (496573 / 1152000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_10, v54_11, v54_20, v54_21, v54_30, v54_31, v54_40, v54_41]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21, phase53_30, phase53_31, phase53_40, phase53_41]
  try simp only [star_one, star_neg]
  linear_combination ((-20437 / 160) * t ^ 3 + (64258351 / 288000) * t ^ 5 + (-24963127 / 288000) * t ^ 7 + (-3225791 / 384000) * t ^ 9 + (-330641 / 288000) * t ^ 11 + (173441 / 1152000) * t ^ 17 + (749 / 576) * d * t ^ 3 + (-41663 / 69120) * d * t ^ 5 + (-34181 / 69120) * d * t ^ 7 + (-11863 / 92160) * d * t ^ 9 + (-329 / 41472) * d * t ^ 11 + (-95 / 82944) * d * t ^ 17 + (-583 / 69120) * d ^ 2 * t ^ 7 + (523 / 69120) * d ^ 2 * t ^ 9) * alpha_sq + ((107 / 24) * t ^ 3 + (-113311 / 23040) * t ^ 5 + (18527 / 23040) * t ^ 7 + (-259 / 5760) * t ^ 9 + (95 / 864) * t ^ 11 + (-749 / 576) * alpha * t ^ 3 + (305861 / 345600) * alpha * t ^ 5 + (16459 / 38400) * alpha * t ^ 7 + (1231 / 55296) * alpha * t ^ 9 + (-110201 / 1036800) * alpha * t ^ 11 + (95 / 82944) * alpha * t ^ 17) * d_sq
theorem v55_42 (t : ℂ) : (momentPoly 55 z55 4 2).eval t = ((145189 / 3) * t ^ 2 + (77673133 / 480) * t ^ 4 + (-2358646107299 / 5760000) * t ^ 6 + (745663694113 / 3840000) * t ^ 8 + (10176157889 / 1152000) * t ^ 10 + (-115424977093 / 69120000) * t ^ 12 + (-1174952467 / 17280000) * t ^ 14 + (3521722313 / 69120000) * t ^ 18 + (511001431 / 34560000) * t ^ 20 + (-8668) * d * t ^ 2 + (410591 / 24) * d * t ^ 4 + (-1297038579 / 128000) * d * t ^ 6 + (3897512923 / 2304000) * d * t ^ 8 + (-43934297 / 192000) * d * t ^ 10 + (204298979 / 1536000) * d * t ^ 12 + (5873317 / 384000) * d * t ^ 14 + (-2603521 / 1536000) * d * t ^ 18 + (-58171 / 384000) * d * t ^ 20 + (-2440042 / 15) * alpha * t ^ 2 + (40199519 / 100) * alpha * t ^ 4 + (-367411870391 / 1152000) * alpha * t ^ 6 + (7088221031 / 92160) * alpha * t ^ 8 + (-34949197 / 76800) * alpha * t ^ 10 + (40651248223 / 13824000) * alpha * t ^ 12 + (73557737 / 3456000) * alpha * t ^ 14 + (709178453 / 13824000) * alpha * t ^ 18 + (-160870247 / 2304000) * alpha * t ^ 20 + 2167 * alpha * d * t ^ 2 + (-17723371 / 7200) * alpha * d * t ^ 4 + (-4695088253 / 3456000) * alpha * d * t ^ 6 + (11729874797 / 6912000) * alpha * d * t ^ 8 + (70577681 / 576000) * alpha * d * t ^ 10 + (-818569811 / 4608000) * alpha * d * t ^ 12 + (14538541 / 691200) * alpha * d * t ^ 14 + (-6952493 / 13824000) * alpha * d * t ^ 18 + (-239 / 3072) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_10, v54_11, v54_12, v54_20, v54_21, v54_22, v54_30, v54_31, v54_32, v54_40, v54_41, v54_42]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22, phase53_30, phase53_31, phase53_32, phase53_40, phase53_41, phase53_42]
  try simp only [star_one, star_neg]
  linear_combination ((-2167 / 3) * t ^ 2 + (4805669 / 3600) * t ^ 4 + (-2031879671 / 3456000) * t ^ 6 + (-74593063 / 3456000) * t ^ 8 + (168545413 / 2304000) * t ^ 10 + (-338018791 / 5184000) * t ^ 12 + (-4852957 / 518400) * t ^ 14 + (-4420309 / 20736000) * t ^ 18 + (2985433 / 3456000) * d * t ^ 6 + (-813929 / 432000) * d * t ^ 8 + (2177837 / 6912000) * d * t ^ 10 + (5679221 / 13824000) * d * t ^ 12 + (2411693 / 10368000) * d * t ^ 14 + (-2354021 / 41472000) * d * t ^ 18 + (58171 / 3456000) * d * t ^ 20 + (26809 / 1382400) * d ^ 2 * t ^ 8 + (-2443 / 115200) * d ^ 2 * t ^ 10 + (-619 / 663552) * d ^ 2 * t ^ 12 + (59213 / 12441600) * d ^ 2 * t ^ 14 + (665 / 1990656) * d ^ 2 * t ^ 18 + (-95 / 995328) * d ^ 2 * t ^ 20) * alpha_sq + ((2167 / 9) * t ^ 2 + (-70543 / 144) * t ^ 4 + (207741589 / 691200) * t ^ 6 + (-23608331 / 460800) * t ^ 8 + (1231687 / 276480) * t ^ 10 + (-51062711 / 16588800) * t ^ 12 + (608899 / 4147200) * t ^ 14 + (27667 / 663552) * t ^ 18 + (95 / 331776) * t ^ 20 + (-30899 / 720) * alpha * t ^ 4 + (274795753 / 3456000) * alpha * t ^ 6 + (-86420219 / 2304000) * alpha * t ^ 8 + (8186123 / 6912000) * alpha * t ^ 10 + (-6264043 / 20736000) * alpha * t ^ 12 + (-25541 / 207360) * alpha * t ^ 14 + (-472823 / 20736000) * alpha * t ^ 18) * d_sq
theorem v55_43 (t : ℂ) : (momentPoly 55 z55 4 3).eval t = (3779677 * t + (-35025309 / 4) * t ^ 3 + (43018792121 / 6400) * t ^ 5 + (-83879974960291 / 38400000) * t ^ 7 + (8008786304127 / 12800000) * t ^ 9 + (-11239905776177 / 76800000) * t ^ 11 + (-536904928537 / 11520000) * t ^ 13 + (1968933353921 / 115200000) * t ^ 15 + (-126702725197 / 51200000) * t ^ 17 + (11378982577 / 691200000) * t ^ 19 + (31175591171 / 230400000) * t ^ 21 + (24978668491 / 460800000) * t ^ 25 + (-3779677 / 8) * d * t + (5323881 / 4) * d * t ^ 3 + (-338549921 / 256) * d * t ^ 5 + (497172003499 / 921600) * d * t ^ 7 + (-399585846689 / 4608000) * d * t ^ 9 + (514244639953 / 46080000) * d * t ^ 11 + (-6587964203 / 6912000) * d * t ^ 13 + (2941479073 / 4608000) * d * t ^ 15 + (34146859 / 3686400) * d * t ^ 17 + (-12885257 / 9216000) * d * t ^ 19 + (-68834363 / 46080000) * d * t ^ 21 + (-485533 / 737280) * d * t ^ 25 + (-18898385 / 24) * alpha * t + (27816197 / 20) * alpha * t ^ 3 + (296683879 / 3840) * alpha * t ^ 5 + (-27581170410589 / 23040000) * alpha * t ^ 7 + (12308867377139 / 23040000) * alpha * t ^ 9 + (-294700675189 / 15360000) * alpha * t ^ 11 + (-735708248239 / 34560000) * alpha * t ^ 13 + (1491753183247 / 69120000) * alpha * t ^ 15 + (146072160121 / 276480000) * alpha * t ^ 17 + (21536987479 / 82944000) * alpha * t ^ 19 + (-3794469833 / 27648000) * alpha * t ^ 21 + (3948743003 / 165888000) * alpha * t ^ 25 + (1218771 / 20) * alpha * d * t ^ 3 + (-41969261 / 256) * alpha * d * t ^ 5 + (132757396207 / 921600) * alpha * d * t ^ 7 + (-185175654509 / 4608000) * alpha * d * t ^ 9 + (-81767069 / 3072000) * alpha * d * t ^ 11 + (-1081366259 / 2304000) * alpha * d * t ^ 13 + (-1480505323 / 4608000) * alpha * d * t ^ 15 + (-138707131 / 6144000) * alpha * d * t ^ 17 + (-50268749 / 1843200) * alpha * d * t ^ 19 + (14143441 / 614400) * alpha * d * t ^ 21 + (821303 / 2048000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_03, v54_10, v54_11, v54_12, v54_13, v54_20, v54_21, v54_22, v54_23, v54_30, v54_31, v54_32, v54_33, v54_40, v54_41, v54_42, v54_43]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23, phase53_30, phase53_31, phase53_32, phase53_33, phase53_40, phase53_41, phase53_42, phase53_43]
  try simp only [star_one, star_neg]
  linear_combination ((406257 / 20) * t ^ 3 + (-3408397 / 64) * t ^ 5 + (419205429349 / 9216000) * t ^ 7 + (-113085390749 / 9216000) * t ^ 9 + (910675231 / 1843200) * t ^ 11 + (-7210825487 / 6912000) * t ^ 13 + (4326364411 / 13824000) * t ^ 15 + (-461288113 / 18432000) * t ^ 17 + (-49095247 / 13824000) * t ^ 19 + (23865077 / 3072000) * t ^ 21 + (24802063 / 55296000) * t ^ 25 + (-4963 / 24) * d * t ^ 3 + (502571 / 2880) * d * t ^ 5 + (1494093829 / 9216000) * d * t ^ 7 + (-2508463 / 48000) * d * t ^ 9 + (-2695716481 / 27648000) * d * t ^ 11 + (1987729931 / 165888000) * d * t ^ 13 + (625054037 / 82944000) * d * t ^ 15 + (-15925109 / 22118400) * d * t ^ 17 + (-204795001 / 497664000) * d * t ^ 19 + (54818293 / 331776000) * d * t ^ 21 + (-472511 / 19906560) * d * t ^ 25 + (184811 / 34560) * d ^ 2 * t ^ 7 + (-271817353 / 27648000) * d ^ 2 * t ^ 9 + (14140499 / 3072000) * d ^ 2 * t ^ 11 + (-8344423 / 55296000) * d ^ 2 * t ^ 13 + (3874759 / 82944000) * d ^ 2 * t ^ 15 + (8357 / 1105920) * d ^ 2 * t ^ 17 + (11077 / 1327104) * d ^ 2 * t ^ 19 + (-46597 / 10368000) * d ^ 2 * t ^ 21) * alpha_sq + (2127 * t ^ 3 + (-1059023 / 256) * t ^ 5 + (3927182981 / 1843200) * t ^ 7 + (-7217713 / 64000) * t ^ 9 + (138189439 / 9216000) * t ^ 11 + (-234236761 / 18432000) * t ^ 13 + (-95438507 / 27648000) * t ^ 15 + (-8197 / 184320) * t ^ 17 + (39920783 / 165888000) * t ^ 19 + (360901 / 13824000) * t ^ 21 + (-4963 / 24) * alpha * t ^ 3 + (847141 / 2880) * alpha * t ^ 5 + (692381647 / 27648000) * alpha * t ^ 7 + (-199301239 / 1728000) * alpha * t ^ 9 + (-95604563 / 9216000) * alpha * t ^ 11 + (2391087743 / 165888000) * alpha * t ^ 13 + (-5086019 / 3317760) * alpha * t ^ 15 + (1344449 / 66355200) * alpha * t ^ 17 + (11022479 / 497664000) * alpha * t ^ 19 + (30473 / 2654208) * alpha * t ^ 21 + (4465 / 3981312) * alpha * t ^ 25) * d_sq
theorem v55_44 (t : ℂ) : (momentPoly 55 z55 4 4).eval t = (207882235 + (-1981528934 / 3) * t ^ 2 + (888002004943 / 1200) * t ^ 4 + (-38258230063123 / 120000) * t ^ 6 + (63942697833209 / 2000000) * t ^ 8 + (-5862445381564903 / 576000000) * t ^ 10 + (718806677076677 / 76800000) * t ^ 12 + (1156475070922927 / 3456000000) * t ^ 14 + (-8555487256031 / 2304000000) * t ^ 16 + (-2591599598111 / 288000000) * t ^ 18 + (-79560277195547 / 20736000000) * t ^ 20 + (752324187817 / 64000000) * t ^ 22 + (-74052758834873 / 13824000000) * t ^ 24 + (3168736675507 / 10368000000) * t ^ 26 + (2169039224099 / 41472000000) * t ^ 32 + (-3676306) * d * t ^ 2 + (810252179 / 80) * d * t ^ 4 + (-75695172771 / 8000) * d * t ^ 6 + (10555182658493 / 3200000) * d * t ^ 8 + (-47067464747743 / 115200000) * d * t ^ 10 + (23258483974231 / 230400000) * d * t ^ 12 + (4662053914819 / 138240000) * d * t ^ 14 + (-8508896524159 / 460800000) * d * t ^ 16 + (120212383481 / 57600000) * d * t ^ 18 + (270069697657 / 460800000) * d * t ^ 20 + (-8838502873 / 115200000) * d * t ^ 22 + (-20069221 / 12288000) * d * t ^ 24 + (-14086594433 / 230400000) * d * t ^ 26 + (3295379 / 7372800) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z55, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v54_00, v54_01, v54_02, v54_03, v54_04, v54_10, v54_11, v54_12, v54_13, v54_14, v54_20, v54_21, v54_22, v54_23, v54_24, v54_30, v54_31, v54_32, v54_33, v54_34, v54_40, v54_41, v54_42, v54_43, v54_44]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24, phase53_30, phase53_31, phase53_32, phase53_33, phase53_34, phase53_40, phase53_41, phase53_42, phase53_43, phase53_44]
  try simp only [star_one, star_neg]
  linear_combination ((1838153 / 6) * t ^ 2 + (-450689311 / 720) * t ^ 4 + (204006107 / 1440) * t ^ 6 + (6450485715787 / 17280000) * t ^ 8 + (-4620895846747 / 23040000) * t ^ 10 + (61347745631 / 8640000) * t ^ 12 + (27003917371 / 16588800) * t ^ 14 + (-22365683579 / 6912000) * t ^ 16 + (26829324889 / 51840000) * t ^ 18 + (-236117575453 / 311040000) * t ^ 20 + (18362250487 / 414720000) * t ^ 22 + (-583369939 / 62208000) * t ^ 26 + (-9735517 / 720) * d * t ^ 4 + (431923967 / 14400) * d * t ^ 6 + (-51544049983 / 3456000) * d * t ^ 8 + (-32830122643 / 5529600) * d * t ^ 10 + (106705011197 / 27648000) * d * t ^ 12 + (4369134229 / 8294400) * d * t ^ 14 + (-1494296023 / 41472000) * d * t ^ 16 + (159131969 / 6912000) * d * t ^ 18 + (986193209 / 248832000) * d * t ^ 20 + (-235128623 / 41472000) * d * t ^ 22 + (20069221 / 110592000) * d * t ^ 24 + (-20248357 / 49766400) * d * t ^ 26 + (-3295379 / 66355200) * d * t ^ 32 + (78911 / 1152) * d ^ 2 * t ^ 6 + (-2843701 / 32400) * d ^ 2 * t ^ 8 + (-742297669 / 27648000) * d ^ 2 * t ^ 10 + (3902371439 / 82944000) * d ^ 2 * t ^ 12 + (158965277 / 41472000) * d ^ 2 * t ^ 14 + (-142222751 / 27648000) * d ^ 2 * t ^ 16 + (6713377 / 12441600) * d ^ 2 * t ^ 18 + (509371 / 6635520) * d ^ 2 * t ^ 20 + (-24039959 / 248832000) * d ^ 2 * t ^ 22 + (-88613 / 15925248) * d ^ 2 * t ^ 24 + (1125047 / 59719680) * d ^ 2 * t ^ 26 + (-9025 / 47775744) * d ^ 2 * t ^ 32) * alpha_sq + ((1838153 / 18) * t ^ 2 + (-42565751 / 144) * t ^ 4 + (8604857687 / 28800) * t ^ 6 + (-138070075423 / 1152000) * t ^ 8 + (458164148933 / 27648000) * t ^ 10 + (-296672840027 / 138240000) * t ^ 12 + (30654508217 / 82944000) * t ^ 14 + (-5815747631 / 27648000) * t ^ 16 + (-17377 / 23040) * t ^ 18 + (-586212263 / 99532800) * t ^ 20 + (-28931809 / 69120000) * t ^ 22 + (88613 / 5308416) * t ^ 24 + (4564201 / 19906560) * t ^ 26 + (9025 / 15925248) * t ^ 32) * d_sq
#print axioms v55_00
#print axioms v55_11
#print axioms v55_22
#print axioms v55_33
#print axioms v55_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v56_02 (t : ℂ) : (momentPoly 56 z56 0 2).eval t = ((89 / 12) * t ^ 2 + (113 / 12) * t ^ 4 + (-1 / 3) * d * t ^ 2 + (553 / 120) * alpha * t ^ 2 + (-171 / 40) * alpha * t ^ 4 + (-5 / 72) * alpha * d * t ^ 2 + (1 / 72) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02]
  try simp only [phase53_00, phase53_01, phase53_02]
  try simp only [star_one, star_neg]
  linear_combination ((-5 / 288) * t ^ 2) * alpha_sq + ((1 / 96) * t ^ 2) * d_sq
theorem v56_03 (t : ℂ) : (momentPoly 56 z56 0 3).eval t = ((1427 / 80) * t ^ 3 + (2293 / 80) * t ^ 5 + 2 * t ^ 9 + (31 / 24) * d * t ^ 3 + (-407 / 96) * d * t ^ 5 + (-47 / 288) * d * t ^ 9 + (16469 / 600) * alpha * t ^ 3 + (-53899 / 2400) * alpha * t ^ 5 + (24869 / 7200) * alpha * t ^ 9 + (-563 / 240) * alpha * d * t ^ 3 + (523 / 240) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_03]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03]
  try simp only [star_one, star_neg]
  linear_combination ((-563 / 960) * t ^ 3 + (171 / 320) * t ^ 5 + (1 / 128) * d * t ^ 3 + (1 / 1152) * d * t ^ 5) * alpha_sq + ((1 / 32) * t ^ 3 + (1 / 128) * alpha * t ^ 3 + (-1 / 384) * alpha * t ^ 5) * d_sq
theorem v56_04 (t : ℂ) : (momentPoly 56 z56 0 4).eval t = ((-141271 / 300) * t ^ 4 + (28133 / 40) * t ^ 6 + (350593 / 4800) * t ^ 8 + (96331 / 3600) * t ^ 10 + (5281 / 576) * t ^ 16 + (881 / 96) * d * t ^ 4 + (-4649 / 240) * d * t ^ 6 + (171 / 160) * d * t ^ 8 + (-143 / 72) * d * t ^ 10 + (5481217 / 24000) * alpha * t ^ 4 + (625543 / 12000) * alpha * t ^ 6 + (-4038041 / 16000) * alpha * t ^ 8 + (25057 / 36000) * alpha * t ^ 10 + (173441 / 48000) * alpha * t ^ 16 + (-188779 / 14400) * alpha * d * t ^ 4 + (10247 / 800) * alpha * d * t ^ 6 + (809 / 1152) * alpha * d * t ^ 8 + (-54463 / 21600) * alpha * d * t ^ 10 + (95 / 3456) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_03, v55_04]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04]
  try simp only [star_one, star_neg]
  linear_combination ((-18517 / 4800) * t ^ 4 + (24637 / 7200) * t ^ 6 + (-60463 / 86400) * t ^ 10 + (191 / 640) * d * t ^ 4 + (-503 / 2880) * d * t ^ 6 + (-57 / 640) * d * t ^ 8 + (-1 / 768) * d ^ 2 * t ^ 6 + (1 / 4608) * d ^ 2 * t ^ 8) * alpha_sq + ((-143 / 576) * t ^ 4 + (121 / 256) * t ^ 6 + (-1 / 1536) * t ^ 8 + (47 / 1152) * t ^ 10 + (191 / 640) * alpha * t ^ 4 + (-533 / 1920) * alpha * t ^ 6) * d_sq
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
theorem v56_12 (t : ℂ) : (momentPoly 56 z56 1 2).eval t = (111 * t + (-16427 / 240) * t ^ 3 + (1507 / 240) * t ^ 5 + (-37 / 2) * d * t + (803 / 48) * d * t ^ 3 + (-67 / 48) * d * t ^ 5 + (37 / 2) * alpha * t + (-1999 / 240) * alpha * t ^ 3 + (-587 / 80) * alpha * t ^ 5 + (-563 / 720) * alpha * d * t ^ 3 + (523 / 720) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_10, v55_11, v55_12]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12]
  try simp only [star_one, star_neg]
  linear_combination ((563 / 2880) * t ^ 3 + (-57 / 320) * t ^ 5 + (-1 / 384) * d * t ^ 3 + (-1 / 3456) * d * t ^ 5) * alpha_sq + ((1 / 32) * t ^ 3 + (1 / 384) * alpha * t ^ 3 + (-1 / 1152) * alpha * t ^ 5) * d_sq
theorem v56_13 (t : ℂ) : (momentPoly 56 z56 1 3).eval t = ((4895 / 4) * t ^ 2 + (323849 / 1200) * t ^ 4 + (-922949 / 800) * t ^ 6 + (23749 / 2400) * t ^ 10 + (-55) * d * t ^ 2 + (2455 / 48) * d * t ^ 4 + (-665 / 96) * d * t ^ 6 + (-143 / 288) * d * t ^ 10 + (6083 / 8) * alpha * t ^ 2 + (-483079 / 400) * alpha * t ^ 4 + (1094891 / 2400) * alpha * t ^ 6 + (53249 / 7200) * alpha * t ^ 10 + (-275 / 24) * alpha * d * t ^ 2 + (23111 / 3600) * alpha * d * t ^ 4 + (10909 / 2400) * alpha * d * t ^ 6 + (-4049 / 7200) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_03, v55_10, v55_11, v55_12, v55_13]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13]
  try simp only [star_one, star_neg]
  linear_combination ((-275 / 96) * t ^ 2 + (307267 / 115200) * t ^ 4 + (679 / 38400) * t ^ 6 + (60463 / 345600) * t ^ 10) * alpha_sq + ((55 / 32) * t ^ 2 + (-7795 / 4608) * t ^ 4 + (119 / 512) * t ^ 6 + (47 / 4608) * t ^ 10 + (191 / 1280) * alpha * t ^ 4 + (-533 / 3840) * alpha * t ^ 6) * d_sq
theorem v56_14 (t : ℂ) : (momentPoly 56 z56 1 4).eval t = ((155543 / 40) * t ^ 3 + (61054507 / 48000) * t ^ 5 + (-29750569 / 8000) * t ^ 7 + (22028237 / 96000) * t ^ 9 + (-18823423 / 72000) * t ^ 11 + (2584823 / 288000) * t ^ 17 + (3379 / 12) * d * t ^ 3 + (-32331143 / 28800) * d * t ^ 5 + (3733501 / 4800) * d * t ^ 7 + (-2208401 / 57600) * d * t ^ 9 + (6499 / 192) * d * t ^ 11 + (-3113 / 2304) * d * t ^ 17 + (1795121 / 300) * alpha * t ^ 3 + (-1322780633 / 144000) * alpha * t ^ 5 + (27183137 / 8000) * alpha * t ^ 7 + (137272177 / 288000) * alpha * t ^ 9 + (-35489441 / 72000) * alpha * t ^ 11 + (-383413 / 96000) * alpha * t ^ 17 + (-61367 / 120) * alpha * d * t ^ 3 + (132851143 / 144000) * alpha * d * t ^ 5 + (-3594207 / 8000) * alpha * d * t ^ 7 + (11009873 / 288000) * alpha * d * t ^ 9 + (-1125787 / 216000) * alpha * d * t ^ 11 + (-496573 / 864000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_03, v55_04, v55_10, v55_11, v55_12, v55_13, v55_14]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14]
  try simp only [star_one, star_neg]
  linear_combination ((-61367 / 480) * t ^ 3 + (31480813 / 144000) * t ^ 5 + (-93738833 / 1152000) * t ^ 7 + (-907979 / 96000) * t ^ 9 + (-338641 / 288000) * t ^ 11 + (173441 / 1152000) * t ^ 17 + (109 / 64) * d * t ^ 3 + (-23239 / 23040) * d * t ^ 5 + (-61619 / 138240) * d * t ^ 7 + (-34879 / 276480) * d * t ^ 9 + (-47 / 4608) * d * t ^ 11 + (-95 / 165888) * d * t ^ 17 + (-191 / 15360) * d ^ 2 * t ^ 7 + (523 / 46080) * d ^ 2 * t ^ 9) * alpha_sq + ((109 / 16) * t ^ 3 + (-164317 / 23040) * t ^ 5 + (1737 / 1280) * t ^ 7 + (-259 / 3840) * t ^ 9 + (95 / 576) * t ^ 11 + (109 / 64) * alpha * t ^ 3 + (-117493 / 115200) * alpha * t ^ 5 + (-152531 / 230400) * alpha * t ^ 7 + (-79 / 2048) * alpha * t ^ 9 + (17771 / 115200) * alpha * t ^ 11 + (-95 / 55296) * alpha * t ^ 17) * d_sq
theorem v56_20 (t : ℂ) : (momentPoly 56 z56 2 0).eval t = ((89 / 12) * t ^ 2 + (113 / 12) * t ^ 4 + (-1 / 3) * d * t ^ 2 + (-553 / 120) * alpha * t ^ 2 + (171 / 40) * alpha * t ^ 4 + (5 / 72) * alpha * d * t ^ 2 + (-1 / 72) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_10, v55_20]
  try simp only [phase53_00, phase53_10, phase53_20]
  try simp only [star_one, star_neg]
  linear_combination ((-5 / 288) * t ^ 2) * alpha_sq + ((1 / 96) * t ^ 2) * d_sq
theorem v56_21 (t : ℂ) : (momentPoly 56 z56 2 1).eval t = (111 * t + (-16427 / 240) * t ^ 3 + (1507 / 240) * t ^ 5 + (-37 / 2) * d * t + (803 / 48) * d * t ^ 3 + (-67 / 48) * d * t ^ 5 + (-37 / 2) * alpha * t + (1999 / 240) * alpha * t ^ 3 + (587 / 80) * alpha * t ^ 5 + (563 / 720) * alpha * d * t ^ 3 + (-523 / 720) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_10, v55_11, v55_20, v55_21]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21]
  try simp only [star_one, star_neg]
  linear_combination ((563 / 2880) * t ^ 3 + (-57 / 320) * t ^ 5 + (-1 / 384) * d * t ^ 3 + (-1 / 3456) * d * t ^ 5) * alpha_sq + ((1 / 32) * t ^ 3 + (-1 / 384) * alpha * t ^ 3 + (1 / 1152) * alpha * t ^ 5) * d_sq
theorem v56_22 (t : ℂ) : (momentPoly 56 z56 2 2).eval t = (6216 + (-8580) * t ^ 2 + (1963739 / 800) * t ^ 4 + (208993 / 1200) * t ^ 6 + (210797 / 2400) * t ^ 8 + (-220 / 3) * d * t ^ 2 + (6253 / 96) * d * t ^ 4 + (-667 / 240) * d * t ^ 6 + (-57 / 160) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_10, v55_11, v55_12, v55_20, v55_21, v55_22]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22]
  try simp only [star_one, star_neg]
  linear_combination ((275 / 72) * t ^ 2 + (-39233 / 17280) * t ^ 4 + (-20117 / 17280) * t ^ 6 + (-191 / 1920) * d * t ^ 4 + (503 / 8640) * d * t ^ 6 + (19 / 640) * d * t ^ 8 + (1 / 2304) * d ^ 2 * t ^ 6 + (-1 / 13824) * d ^ 2 * t ^ 8) * alpha_sq + ((55 / 24) * t ^ 2 + (-2503 / 1152) * t ^ 4 + (39 / 256) * t ^ 6 + (1 / 4608) * t ^ 8) * d_sq
theorem v56_23 (t : ℂ) : (momentPoly 56 z56 2 3).eval t = (18316 * t + (-1790543 / 80) * t ^ 3 + (314722289 / 48000) * t ^ 5 + (-29506127 / 19200) * t ^ 7 + (13635779 / 32000) * t ^ 9 + (7794919 / 96000) * t ^ 11 + (-2540599 / 96000) * t ^ 13 + (-9158 / 3) * d * t + (87527 / 16) * d * t ^ 3 + (-9099583 / 3200) * d * t ^ 5 + (2520881 / 6400) * d * t ^ 7 + (-712681 / 19200) * d * t ^ 9 + (749 / 3840) * d * t ^ 11 + (-70627 / 57600) * d * t ^ 13 + (9158 / 3) * alpha * t + (-217891 / 80) * alpha * t ^ 3 + (-20299553 / 9600) * alpha * t ^ 5 + (35293247 / 19200) * alpha * t ^ 7 + (-46613 / 768) * alpha * t ^ 9 + (471973 / 19200) * alpha * t ^ 11 + (2431153 / 57600) * alpha * t ^ 13 + (-61367 / 240) * alpha * d * t ^ 3 + (4381237 / 9600) * alpha * d * t ^ 5 + (-11517253 / 57600) * alpha * d * t ^ 7 + (-139 / 768) * alpha * d * t ^ 9 + (-32893 / 19200) * alpha * d * t ^ 11 + (-8357 / 11520) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_03, v55_10, v55_11, v55_12, v55_13, v55_20, v55_21, v55_22, v55_23]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23]
  try simp only [star_one, star_neg]
  linear_combination ((61367 / 960) * t ^ 3 + (-2075891 / 19200) * t ^ 5 + (2568937 / 57600) * t ^ 7 + (830887 / 691200) * t ^ 11 + (-2717 / 5120) * t ^ 13 + (-109 / 128) * d * t ^ 3 + (54733 / 172800) * d * t ^ 5 + (463687 / 1382400) * d * t ^ 7 + (199133 / 1382400) * d * t ^ 9 + (-20171 / 460800) * d * t ^ 11 + (-46163 / 4147200) * d * t ^ 13 + (191 / 15360) * d ^ 2 * t ^ 7 + (-523 / 46080) * d ^ 2 * t ^ 9) * alpha_sq + ((327 / 32) * t ^ 3 + (-223033 / 23040) * t ^ 5 + (319 / 640) * t ^ 7 + (259 / 3840) * t ^ 9 + (95 / 2304) * t ^ 11 + (109 / 128) * alpha * t ^ 3 + (-120533 / 172800) * alpha * t ^ 5 + (-198049 / 1382400) * alpha * t ^ 7 + (1 / 6144) * alpha * t ^ 9 + (15421 / 460800) * alpha * t ^ 11 + (47 / 55296) * alpha * t ^ 13) * d_sq
theorem v56_24 (t : ℂ) : (momentPoly 56 z56 2 4).eval t = ((1600843 / 6) * t ^ 2 + (-21583211 / 100) * t ^ 4 + (-17496020677 / 80000) * t ^ 6 + (4951952441 / 30000) * t ^ 8 + (226256821 / 16000) * t ^ 10 + (-5211974761 / 1440000) * t ^ 12 + (3408083 / 30000) * t ^ 14 + (8539321 / 90000) * t ^ 18 + (44977169 / 1440000) * t ^ 20 + (-35974 / 3) * d * t ^ 2 + 22095 * d * t ^ 4 + (-1849453733 / 144000) * d * t ^ 6 + (2602927 / 1000) * d * t ^ 8 + (-5611267 / 16000) * d * t ^ 10 + (9495959 / 57600) * d * t ^ 12 + (611399 / 36000) * d * t ^ 14 + (-2923 / 1200) * d * t ^ 18 + (-58171 / 288000) * d * t ^ 20 + (9946811 / 60) * alpha * t ^ 2 + (-74162709 / 200) * alpha * t ^ 4 + (18284337253 / 72000) * alpha * t ^ 6 + (-721291483 / 16000) * alpha * t ^ 8 + (-11122919 / 19200) * alpha * t ^ 10 + (-2791811 / 960) * alpha * t ^ 12 + (6389089 / 72000) * alpha * t ^ 14 + (-10222183 / 288000) * alpha * t ^ 18 + (11159377 / 144000) * alpha * t ^ 20 + (-89935 / 36) * alpha * d * t ^ 2 + (1369817 / 600) * alpha * d * t ^ 4 + (345729191 / 144000) * alpha * d * t ^ 6 + (-162722081 / 72000) * alpha * d * t ^ 8 + (-6827639 / 48000) * alpha * d * t ^ 10 + (192127739 / 864000) * alpha * d * t ^ 12 + (-649697 / 21600) * alpha * d * t ^ 14 + (164341 / 216000) * alpha * d * t ^ 18 + (271 / 2304) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_03, v55_04, v55_10, v55_11, v55_12, v55_13, v55_14, v55_20, v55_21, v55_22, v55_23, v55_24]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24]
  try simp only [star_one, star_neg]
  linear_combination ((-89935 / 144) * t ^ 2 + (921801 / 800) * t ^ 4 + (-1151290709 / 2304000) * t ^ 6 + (-80206163 / 3456000) * t ^ 8 + (307238711 / 4608000) * t ^ 10 + (-37500737 / 648000) * t ^ 12 + (-10374109 / 1036800) * t ^ 14 + (-10892743 / 41472000) * t ^ 18 + (7260349 / 6912000) * d * t ^ 6 + (-471647 / 138240) * d * t ^ 8 + (10317911 / 6912000) * d * t ^ 10 + (85217 / 230400) * d * t ^ 12 + (1844909 / 5184000) * d * t ^ 14 + (-706711 / 10368000) * d * t ^ 18 + (58171 / 3456000) * d * t ^ 20 + (129653 / 4147200) * d ^ 2 * t ^ 8 + (-44449 / 1382400) * d ^ 2 * t ^ 10 + (-119 / 73728) * d ^ 2 * t ^ 12 + (9473 / 1382400) * d ^ 2 * t ^ 14 + (95 / 221184) * d ^ 2 * t ^ 18 + (-95 / 663552) * d ^ 2 * t ^ 20) * alpha_sq + ((17987 / 48) * t ^ 2 + (-23385 / 32) * t ^ 4 + (206255663 / 460800) * t ^ 6 + (-8166917 / 92160) * t ^ 8 + (1467617 / 184320) * t ^ 10 + (-24781769 / 5529600) * t ^ 12 + (13431 / 51200) * t ^ 14 + (1793 / 24576) * t ^ 18 + (95 / 221184) * t ^ 20 + (5157 / 80) * alpha * t ^ 4 + (-817886009 / 6912000) * alpha * t ^ 6 + (384669523 / 6912000) * alpha * t ^ 8 + (-1588283 / 768000) * alpha * t ^ 10 + (682727 / 1536000) * alpha * t ^ 12 + (25541 / 138240) * alpha * t ^ 14 + (472823 / 13824000) * alpha * t ^ 18) * d_sq
theorem v56_30 (t : ℂ) : (momentPoly 56 z56 3 0).eval t = ((1427 / 80) * t ^ 3 + (2293 / 80) * t ^ 5 + 2 * t ^ 9 + (31 / 24) * d * t ^ 3 + (-407 / 96) * d * t ^ 5 + (-47 / 288) * d * t ^ 9 + (-16469 / 600) * alpha * t ^ 3 + (53899 / 2400) * alpha * t ^ 5 + (-24869 / 7200) * alpha * t ^ 9 + (563 / 240) * alpha * d * t ^ 3 + (-523 / 240) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_10, v55_20, v55_30]
  try simp only [phase53_00, phase53_10, phase53_20, phase53_30]
  try simp only [star_one, star_neg]
  linear_combination ((-563 / 960) * t ^ 3 + (171 / 320) * t ^ 5 + (1 / 128) * d * t ^ 3 + (1 / 1152) * d * t ^ 5) * alpha_sq + ((1 / 32) * t ^ 3 + (-1 / 128) * alpha * t ^ 3 + (1 / 384) * alpha * t ^ 5) * d_sq
theorem v56_31 (t : ℂ) : (momentPoly 56 z56 3 1).eval t = ((4895 / 4) * t ^ 2 + (323849 / 1200) * t ^ 4 + (-922949 / 800) * t ^ 6 + (23749 / 2400) * t ^ 10 + (-55) * d * t ^ 2 + (2455 / 48) * d * t ^ 4 + (-665 / 96) * d * t ^ 6 + (-143 / 288) * d * t ^ 10 + (-6083 / 8) * alpha * t ^ 2 + (483079 / 400) * alpha * t ^ 4 + (-1094891 / 2400) * alpha * t ^ 6 + (-53249 / 7200) * alpha * t ^ 10 + (275 / 24) * alpha * d * t ^ 2 + (-23111 / 3600) * alpha * d * t ^ 4 + (-10909 / 2400) * alpha * d * t ^ 6 + (4049 / 7200) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_10, v55_11, v55_20, v55_21, v55_30, v55_31]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21, phase53_30, phase53_31]
  try simp only [star_one, star_neg]
  linear_combination ((-275 / 96) * t ^ 2 + (307267 / 115200) * t ^ 4 + (679 / 38400) * t ^ 6 + (60463 / 345600) * t ^ 10) * alpha_sq + ((55 / 32) * t ^ 2 + (-7795 / 4608) * t ^ 4 + (119 / 512) * t ^ 6 + (47 / 4608) * t ^ 10 + (-191 / 1280) * alpha * t ^ 4 + (533 / 3840) * alpha * t ^ 6) * d_sq
theorem v56_32 (t : ℂ) : (momentPoly 56 z56 3 2).eval t = (18316 * t + (-1790543 / 80) * t ^ 3 + (314722289 / 48000) * t ^ 5 + (-29506127 / 19200) * t ^ 7 + (13635779 / 32000) * t ^ 9 + (7794919 / 96000) * t ^ 11 + (-2540599 / 96000) * t ^ 13 + (-9158 / 3) * d * t + (87527 / 16) * d * t ^ 3 + (-9099583 / 3200) * d * t ^ 5 + (2520881 / 6400) * d * t ^ 7 + (-712681 / 19200) * d * t ^ 9 + (749 / 3840) * d * t ^ 11 + (-70627 / 57600) * d * t ^ 13 + (-9158 / 3) * alpha * t + (217891 / 80) * alpha * t ^ 3 + (20299553 / 9600) * alpha * t ^ 5 + (-35293247 / 19200) * alpha * t ^ 7 + (46613 / 768) * alpha * t ^ 9 + (-471973 / 19200) * alpha * t ^ 11 + (-2431153 / 57600) * alpha * t ^ 13 + (61367 / 240) * alpha * d * t ^ 3 + (-4381237 / 9600) * alpha * d * t ^ 5 + (11517253 / 57600) * alpha * d * t ^ 7 + (139 / 768) * alpha * d * t ^ 9 + (32893 / 19200) * alpha * d * t ^ 11 + (8357 / 11520) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_10, v55_11, v55_12, v55_20, v55_21, v55_22, v55_30, v55_31, v55_32]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22, phase53_30, phase53_31, phase53_32]
  try simp only [star_one, star_neg]
  linear_combination ((61367 / 960) * t ^ 3 + (-2075891 / 19200) * t ^ 5 + (2568937 / 57600) * t ^ 7 + (830887 / 691200) * t ^ 11 + (-2717 / 5120) * t ^ 13 + (-109 / 128) * d * t ^ 3 + (54733 / 172800) * d * t ^ 5 + (463687 / 1382400) * d * t ^ 7 + (199133 / 1382400) * d * t ^ 9 + (-20171 / 460800) * d * t ^ 11 + (-46163 / 4147200) * d * t ^ 13 + (191 / 15360) * d ^ 2 * t ^ 7 + (-523 / 46080) * d ^ 2 * t ^ 9) * alpha_sq + ((327 / 32) * t ^ 3 + (-223033 / 23040) * t ^ 5 + (319 / 640) * t ^ 7 + (259 / 3840) * t ^ 9 + (95 / 2304) * t ^ 11 + (-109 / 128) * alpha * t ^ 3 + (120533 / 172800) * alpha * t ^ 5 + (198049 / 1382400) * alpha * t ^ 7 + (-1 / 6144) * alpha * t ^ 9 + (-15421 / 460800) * alpha * t ^ 11 + (-47 / 55296) * alpha * t ^ 13) * d_sq
theorem v56_33 (t : ℂ) : (momentPoly 56 z56 3 3).eval t = (1025696 + (-2104479) * t ^ 2 + (477188577 / 400) * t ^ 4 + (-394247197 / 10000) * t ^ 6 + (-1390243501 / 40000) * t ^ 8 + (-2549756451 / 80000) * t ^ 10 + (-14862869 / 120000) * t ^ 12 + (1491263 / 10000) * t ^ 14 + (-227687 / 240000) * t ^ 18 + (-17987) * d * t ^ 2 + (506493 / 16) * d * t ^ 4 + (-180127711 / 12000) * d * t ^ 6 + (5873903 / 4800) * d * t ^ 8 + (-1388171 / 8000) * d * t ^ 10 + (-2947193 / 72000) * d * t ^ 12 + (551651 / 24000) * d * t ^ 14 + (-47 / 72) * d * t ^ 18) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_03, v55_10, v55_11, v55_12, v55_13, v55_20, v55_21, v55_22, v55_23, v55_30, v55_31, v55_32, v55_33]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23, phase53_30, phase53_31, phase53_32, phase53_33]
  try simp only [star_one, star_neg]
  linear_combination ((89935 / 96) * t ^ 2 + (-353097 / 320) * t ^ 4 + (-144420823 / 460800) * t ^ 6 + (113076407 / 230400) * t ^ 8 + (-6028253 / 460800) * t ^ 10 + (19480457 / 2764800) * t ^ 12 + (1446713 / 307200) * t ^ 14 + (14736293 / 16588800) * t ^ 18 + (-15471 / 320) * d * t ^ 4 + (32798563 / 460800) * d * t ^ 6 + (-444653 / 38400) * d * t ^ 8 + (-5157359 / 460800) * d * t ^ 10 + (-58811 / 76800) * d * t ^ 12 + (79357 / 691200) * d * t ^ 14 + (163 / 768) * d ^ 2 * t ^ 6 + (-95783 / 691200) * d ^ 2 * t ^ 8 + (-493 / 7200) * d ^ 2 * t ^ 10 + (461 / 51200) * d ^ 2 * t ^ 14) * alpha_sq + ((17987 / 32) * t ^ 2 + (-67581 / 64) * t ^ 4 + (10348951 / 18432) * t ^ 6 + (-3844937 / 57600) * t ^ 8 + (887411 / 153600) * t ^ 10 + (-683033 / 2764800) * t ^ 12 + (123229 / 307200) * t ^ 14 + (2209 / 221184) * t ^ 18) * d_sq
theorem v56_34 (t : ℂ) : (momentPoly 56 z56 3 4).eval t = (3993551 * t + (-290117247 / 40) * t ^ 3 + (28453379223 / 8000) * t ^ 5 + (-6317037318179 / 9600000) * t ^ 7 + (3773901698451 / 6400000) * t ^ 9 + (-2888785041463 / 19200000) * t ^ 11 + (-1190845711909 / 23040000) * t ^ 13 + (31488543677 / 2400000) * t ^ 15 + (-33365647043 / 12800000) * t ^ 17 + (13763806271 / 57600000) * t ^ 19 + (7022271091 / 38400000) * t ^ 21 + (6310504229 / 115200000) * t ^ 25 + (-3993551 / 6) * d * t + (14181783 / 8) * d * t ^ 3 + (-2688804443 / 1600) * d * t ^ 5 + (261275943829 / 384000) * d * t ^ 7 + (-97241900683 / 768000) * d * t ^ 9 + (69900275437 / 3840000) * d * t ^ 11 + (-1811815063 / 1536000) * d * t ^ 13 + (28737601 / 32000) * d * t ^ 15 + (5409413 / 921600) * d * t ^ 17 + (-33199459 / 6912000) * d * t ^ 19 + (-212749367 / 23040000) * d * t ^ 21 + (-577693 / 552960) * d * t ^ 25 + (3993551 / 6) * alpha * t + (-35304339 / 40) * alpha * t ^ 3 + (-951643951 / 1600) * alpha * t ^ 5 + (468693074543 / 384000) * alpha * t ^ 7 + (-1644239729677 / 3840000) * alpha * t ^ 9 + (123522614999 / 3840000) * alpha * t ^ 11 + (251528073197 / 23040000) * alpha * t ^ 13 + (-10237716251 / 480000) * alpha * t ^ 15 + (-17940818833 / 23040000) * alpha * t ^ 17 + (-10414804349 / 34560000) * alpha * t ^ 19 + (3181451203 / 23040000) * alpha * t ^ 21 + (-375713239 / 13824000) * alpha * t ^ 25 + (-3314381 / 40) * alpha * d * t ^ 3 + (1043927617 / 4800) * alpha * d * t ^ 5 + (-71397159989 / 384000) * alpha * d * t ^ 7 + (38500528039 / 768000) * alpha * d * t ^ 9 + (-41350819 / 2304000) * alpha * d * t ^ 11 + (9688234843 / 13824000) * alpha * d * t ^ 13 + (12906449 / 32000) * alpha * d * t ^ 15 + (159166331 / 4608000) * alpha * d * t ^ 17 + (16777733 / 460800) * alpha * d * t ^ 19 + (-159038537 / 4608000) * alpha * d * t ^ 21 + (-821303 / 1536000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_03, v55_04, v55_10, v55_11, v55_12, v55_13, v55_14, v55_20, v55_21, v55_22, v55_23, v55_24, v55_30, v55_31, v55_32, v55_33, v55_34]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24, phase53_30, phase53_31, phase53_32, phase53_33, phase53_34]
  try simp only [star_one, star_neg]
  linear_combination ((3314381 / 160) * t ^ 3 + (-162867127 / 3200) * t ^ 5 + (369878049911 / 9216000) * t ^ 7 + (-7088221031 / 737280) * t ^ 9 + (90057687 / 204800) * t ^ 11 + (-110936244719 / 110592000) * t ^ 13 + (15836870687 / 55296000) * t ^ 15 + (-129840997 / 4608000) * t ^ 17 + (-839635031 / 331776000) * t ^ 19 + (160870247 / 18432000) * t ^ 21 + (24802063 / 55296000) * t ^ 25 + (-17661 / 64) * d * t ^ 3 + (1120451 / 4800) * d * t ^ 5 + (5839537093 / 27648000) * d * t ^ 7 + (-108070337 / 1105920) * d * t ^ 9 + (-2750402123 / 27648000) * d * t ^ 11 + (163197257 / 8294400) * d * t ^ 13 + (1049083039 / 165888000) * d * t ^ 15 + (-50396737 / 66355200) * d * t ^ 17 + (-61463717 / 110592000) * d * t ^ 19 + (60929543 / 331776000) * d * t ^ 21 + (-877097 / 39813120) * d * t ^ 25 + (61693 / 7680) * d ^ 2 * t ^ 7 + (-808806809 / 55296000) * d ^ 2 * t ^ 9 + (20979211 / 3072000) * d ^ 2 * t ^ 11 + (-1069447 / 4096000) * d ^ 2 * t ^ 13 + (1267753 / 18432000) * d ^ 2 * t ^ 15 + (8357 / 737280) * d ^ 2 * t ^ 17 + (3629 / 294912) * d ^ 2 * t ^ 19 + (-46597 / 6912000) * d ^ 2 * t ^ 21) * alpha_sq + ((52983 / 16) * t ^ 3 + (-23864531 / 3840) * t ^ 5 + (3269633043 / 1024000) * t ^ 7 + (-2454559457 / 9216000) * t ^ 9 + (31355323 / 1024000) * t ^ 11 + (-125417783 / 6912000) * t ^ 13 + (-67241 / 16000) * t ^ 15 + (-8197 / 122880) * t ^ 17 + (5226883 / 13824000) * t ^ 19 + (360901 / 9216000) * t ^ 21 + (17661 / 64) * alpha * t ^ 3 + (-5149103 / 14400) * alpha * t ^ 5 + (-2407494133 / 27648000) * alpha * t ^ 7 + (178580523 / 1024000) * alpha * t ^ 9 + (387120511 / 27648000) * alpha * t ^ 11 + (-435004139 / 20736000) * alpha * t ^ 13 + (27800863 / 11059200) * alpha * t ^ 15 + (-87293 / 2457600) * alpha * t ^ 17 + (-14147729 / 331776000) * alpha * t ^ 19 + (-5831 / 294912) * alpha * t ^ 21 + (-4465 / 2654208) * alpha * t ^ 25) * d_sq
theorem v56_40 (t : ℂ) : (momentPoly 56 z56 4 0).eval t = ((-141271 / 300) * t ^ 4 + (28133 / 40) * t ^ 6 + (350593 / 4800) * t ^ 8 + (96331 / 3600) * t ^ 10 + (5281 / 576) * t ^ 16 + (881 / 96) * d * t ^ 4 + (-4649 / 240) * d * t ^ 6 + (171 / 160) * d * t ^ 8 + (-143 / 72) * d * t ^ 10 + (-5481217 / 24000) * alpha * t ^ 4 + (-625543 / 12000) * alpha * t ^ 6 + (4038041 / 16000) * alpha * t ^ 8 + (-25057 / 36000) * alpha * t ^ 10 + (-173441 / 48000) * alpha * t ^ 16 + (188779 / 14400) * alpha * d * t ^ 4 + (-10247 / 800) * alpha * d * t ^ 6 + (-809 / 1152) * alpha * d * t ^ 8 + (54463 / 21600) * alpha * d * t ^ 10 + (-95 / 3456) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_10, v55_20, v55_30, v55_40]
  try simp only [phase53_00, phase53_10, phase53_20, phase53_30, phase53_40]
  try simp only [star_one, star_neg]
  linear_combination ((-18517 / 4800) * t ^ 4 + (24637 / 7200) * t ^ 6 + (-60463 / 86400) * t ^ 10 + (191 / 640) * d * t ^ 4 + (-503 / 2880) * d * t ^ 6 + (-57 / 640) * d * t ^ 8 + (-1 / 768) * d ^ 2 * t ^ 6 + (1 / 4608) * d ^ 2 * t ^ 8) * alpha_sq + ((-143 / 576) * t ^ 4 + (121 / 256) * t ^ 6 + (-1 / 1536) * t ^ 8 + (47 / 1152) * t ^ 10 + (-191 / 640) * alpha * t ^ 4 + (533 / 1920) * alpha * t ^ 6) * d_sq
theorem v56_41 (t : ℂ) : (momentPoly 56 z56 4 1).eval t = ((155543 / 40) * t ^ 3 + (61054507 / 48000) * t ^ 5 + (-29750569 / 8000) * t ^ 7 + (22028237 / 96000) * t ^ 9 + (-18823423 / 72000) * t ^ 11 + (2584823 / 288000) * t ^ 17 + (3379 / 12) * d * t ^ 3 + (-32331143 / 28800) * d * t ^ 5 + (3733501 / 4800) * d * t ^ 7 + (-2208401 / 57600) * d * t ^ 9 + (6499 / 192) * d * t ^ 11 + (-3113 / 2304) * d * t ^ 17 + (-1795121 / 300) * alpha * t ^ 3 + (1322780633 / 144000) * alpha * t ^ 5 + (-27183137 / 8000) * alpha * t ^ 7 + (-137272177 / 288000) * alpha * t ^ 9 + (35489441 / 72000) * alpha * t ^ 11 + (383413 / 96000) * alpha * t ^ 17 + (61367 / 120) * alpha * d * t ^ 3 + (-132851143 / 144000) * alpha * d * t ^ 5 + (3594207 / 8000) * alpha * d * t ^ 7 + (-11009873 / 288000) * alpha * d * t ^ 9 + (1125787 / 216000) * alpha * d * t ^ 11 + (496573 / 864000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_10, v55_11, v55_20, v55_21, v55_30, v55_31, v55_40, v55_41]
  try simp only [phase53_00, phase53_01, phase53_10, phase53_11, phase53_20, phase53_21, phase53_30, phase53_31, phase53_40, phase53_41]
  try simp only [star_one, star_neg]
  linear_combination ((-61367 / 480) * t ^ 3 + (31480813 / 144000) * t ^ 5 + (-93738833 / 1152000) * t ^ 7 + (-907979 / 96000) * t ^ 9 + (-338641 / 288000) * t ^ 11 + (173441 / 1152000) * t ^ 17 + (109 / 64) * d * t ^ 3 + (-23239 / 23040) * d * t ^ 5 + (-61619 / 138240) * d * t ^ 7 + (-34879 / 276480) * d * t ^ 9 + (-47 / 4608) * d * t ^ 11 + (-95 / 165888) * d * t ^ 17 + (-191 / 15360) * d ^ 2 * t ^ 7 + (523 / 46080) * d ^ 2 * t ^ 9) * alpha_sq + ((109 / 16) * t ^ 3 + (-164317 / 23040) * t ^ 5 + (1737 / 1280) * t ^ 7 + (-259 / 3840) * t ^ 9 + (95 / 576) * t ^ 11 + (-109 / 64) * alpha * t ^ 3 + (117493 / 115200) * alpha * t ^ 5 + (152531 / 230400) * alpha * t ^ 7 + (79 / 2048) * alpha * t ^ 9 + (-17771 / 115200) * alpha * t ^ 11 + (95 / 55296) * alpha * t ^ 17) * d_sq
theorem v56_42 (t : ℂ) : (momentPoly 56 z56 4 2).eval t = ((1600843 / 6) * t ^ 2 + (-21583211 / 100) * t ^ 4 + (-17496020677 / 80000) * t ^ 6 + (4951952441 / 30000) * t ^ 8 + (226256821 / 16000) * t ^ 10 + (-5211974761 / 1440000) * t ^ 12 + (3408083 / 30000) * t ^ 14 + (8539321 / 90000) * t ^ 18 + (44977169 / 1440000) * t ^ 20 + (-35974 / 3) * d * t ^ 2 + 22095 * d * t ^ 4 + (-1849453733 / 144000) * d * t ^ 6 + (2602927 / 1000) * d * t ^ 8 + (-5611267 / 16000) * d * t ^ 10 + (9495959 / 57600) * d * t ^ 12 + (611399 / 36000) * d * t ^ 14 + (-2923 / 1200) * d * t ^ 18 + (-58171 / 288000) * d * t ^ 20 + (-9946811 / 60) * alpha * t ^ 2 + (74162709 / 200) * alpha * t ^ 4 + (-18284337253 / 72000) * alpha * t ^ 6 + (721291483 / 16000) * alpha * t ^ 8 + (11122919 / 19200) * alpha * t ^ 10 + (2791811 / 960) * alpha * t ^ 12 + (-6389089 / 72000) * alpha * t ^ 14 + (10222183 / 288000) * alpha * t ^ 18 + (-11159377 / 144000) * alpha * t ^ 20 + (89935 / 36) * alpha * d * t ^ 2 + (-1369817 / 600) * alpha * d * t ^ 4 + (-345729191 / 144000) * alpha * d * t ^ 6 + (162722081 / 72000) * alpha * d * t ^ 8 + (6827639 / 48000) * alpha * d * t ^ 10 + (-192127739 / 864000) * alpha * d * t ^ 12 + (649697 / 21600) * alpha * d * t ^ 14 + (-164341 / 216000) * alpha * d * t ^ 18 + (-271 / 2304) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_10, v55_11, v55_12, v55_20, v55_21, v55_22, v55_30, v55_31, v55_32, v55_40, v55_41, v55_42]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_10, phase53_11, phase53_12, phase53_20, phase53_21, phase53_22, phase53_30, phase53_31, phase53_32, phase53_40, phase53_41, phase53_42]
  try simp only [star_one, star_neg]
  linear_combination ((-89935 / 144) * t ^ 2 + (921801 / 800) * t ^ 4 + (-1151290709 / 2304000) * t ^ 6 + (-80206163 / 3456000) * t ^ 8 + (307238711 / 4608000) * t ^ 10 + (-37500737 / 648000) * t ^ 12 + (-10374109 / 1036800) * t ^ 14 + (-10892743 / 41472000) * t ^ 18 + (7260349 / 6912000) * d * t ^ 6 + (-471647 / 138240) * d * t ^ 8 + (10317911 / 6912000) * d * t ^ 10 + (85217 / 230400) * d * t ^ 12 + (1844909 / 5184000) * d * t ^ 14 + (-706711 / 10368000) * d * t ^ 18 + (58171 / 3456000) * d * t ^ 20 + (129653 / 4147200) * d ^ 2 * t ^ 8 + (-44449 / 1382400) * d ^ 2 * t ^ 10 + (-119 / 73728) * d ^ 2 * t ^ 12 + (9473 / 1382400) * d ^ 2 * t ^ 14 + (95 / 221184) * d ^ 2 * t ^ 18 + (-95 / 663552) * d ^ 2 * t ^ 20) * alpha_sq + ((17987 / 48) * t ^ 2 + (-23385 / 32) * t ^ 4 + (206255663 / 460800) * t ^ 6 + (-8166917 / 92160) * t ^ 8 + (1467617 / 184320) * t ^ 10 + (-24781769 / 5529600) * t ^ 12 + (13431 / 51200) * t ^ 14 + (1793 / 24576) * t ^ 18 + (95 / 221184) * t ^ 20 + (-5157 / 80) * alpha * t ^ 4 + (817886009 / 6912000) * alpha * t ^ 6 + (-384669523 / 6912000) * alpha * t ^ 8 + (1588283 / 768000) * alpha * t ^ 10 + (-682727 / 1536000) * alpha * t ^ 12 + (-25541 / 138240) * alpha * t ^ 14 + (-472823 / 13824000) * alpha * t ^ 18) * d_sq
theorem v56_43 (t : ℂ) : (momentPoly 56 z56 4 3).eval t = (3993551 * t + (-290117247 / 40) * t ^ 3 + (28453379223 / 8000) * t ^ 5 + (-6317037318179 / 9600000) * t ^ 7 + (3773901698451 / 6400000) * t ^ 9 + (-2888785041463 / 19200000) * t ^ 11 + (-1190845711909 / 23040000) * t ^ 13 + (31488543677 / 2400000) * t ^ 15 + (-33365647043 / 12800000) * t ^ 17 + (13763806271 / 57600000) * t ^ 19 + (7022271091 / 38400000) * t ^ 21 + (6310504229 / 115200000) * t ^ 25 + (-3993551 / 6) * d * t + (14181783 / 8) * d * t ^ 3 + (-2688804443 / 1600) * d * t ^ 5 + (261275943829 / 384000) * d * t ^ 7 + (-97241900683 / 768000) * d * t ^ 9 + (69900275437 / 3840000) * d * t ^ 11 + (-1811815063 / 1536000) * d * t ^ 13 + (28737601 / 32000) * d * t ^ 15 + (5409413 / 921600) * d * t ^ 17 + (-33199459 / 6912000) * d * t ^ 19 + (-212749367 / 23040000) * d * t ^ 21 + (-577693 / 552960) * d * t ^ 25 + (-3993551 / 6) * alpha * t + (35304339 / 40) * alpha * t ^ 3 + (951643951 / 1600) * alpha * t ^ 5 + (-468693074543 / 384000) * alpha * t ^ 7 + (1644239729677 / 3840000) * alpha * t ^ 9 + (-123522614999 / 3840000) * alpha * t ^ 11 + (-251528073197 / 23040000) * alpha * t ^ 13 + (10237716251 / 480000) * alpha * t ^ 15 + (17940818833 / 23040000) * alpha * t ^ 17 + (10414804349 / 34560000) * alpha * t ^ 19 + (-3181451203 / 23040000) * alpha * t ^ 21 + (375713239 / 13824000) * alpha * t ^ 25 + (3314381 / 40) * alpha * d * t ^ 3 + (-1043927617 / 4800) * alpha * d * t ^ 5 + (71397159989 / 384000) * alpha * d * t ^ 7 + (-38500528039 / 768000) * alpha * d * t ^ 9 + (41350819 / 2304000) * alpha * d * t ^ 11 + (-9688234843 / 13824000) * alpha * d * t ^ 13 + (-12906449 / 32000) * alpha * d * t ^ 15 + (-159166331 / 4608000) * alpha * d * t ^ 17 + (-16777733 / 460800) * alpha * d * t ^ 19 + (159038537 / 4608000) * alpha * d * t ^ 21 + (821303 / 1536000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_03, v55_10, v55_11, v55_12, v55_13, v55_20, v55_21, v55_22, v55_23, v55_30, v55_31, v55_32, v55_33, v55_40, v55_41, v55_42, v55_43]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_10, phase53_11, phase53_12, phase53_13, phase53_20, phase53_21, phase53_22, phase53_23, phase53_30, phase53_31, phase53_32, phase53_33, phase53_40, phase53_41, phase53_42, phase53_43]
  try simp only [star_one, star_neg]
  linear_combination ((3314381 / 160) * t ^ 3 + (-162867127 / 3200) * t ^ 5 + (369878049911 / 9216000) * t ^ 7 + (-7088221031 / 737280) * t ^ 9 + (90057687 / 204800) * t ^ 11 + (-110936244719 / 110592000) * t ^ 13 + (15836870687 / 55296000) * t ^ 15 + (-129840997 / 4608000) * t ^ 17 + (-839635031 / 331776000) * t ^ 19 + (160870247 / 18432000) * t ^ 21 + (24802063 / 55296000) * t ^ 25 + (-17661 / 64) * d * t ^ 3 + (1120451 / 4800) * d * t ^ 5 + (5839537093 / 27648000) * d * t ^ 7 + (-108070337 / 1105920) * d * t ^ 9 + (-2750402123 / 27648000) * d * t ^ 11 + (163197257 / 8294400) * d * t ^ 13 + (1049083039 / 165888000) * d * t ^ 15 + (-50396737 / 66355200) * d * t ^ 17 + (-61463717 / 110592000) * d * t ^ 19 + (60929543 / 331776000) * d * t ^ 21 + (-877097 / 39813120) * d * t ^ 25 + (61693 / 7680) * d ^ 2 * t ^ 7 + (-808806809 / 55296000) * d ^ 2 * t ^ 9 + (20979211 / 3072000) * d ^ 2 * t ^ 11 + (-1069447 / 4096000) * d ^ 2 * t ^ 13 + (1267753 / 18432000) * d ^ 2 * t ^ 15 + (8357 / 737280) * d ^ 2 * t ^ 17 + (3629 / 294912) * d ^ 2 * t ^ 19 + (-46597 / 6912000) * d ^ 2 * t ^ 21) * alpha_sq + ((52983 / 16) * t ^ 3 + (-23864531 / 3840) * t ^ 5 + (3269633043 / 1024000) * t ^ 7 + (-2454559457 / 9216000) * t ^ 9 + (31355323 / 1024000) * t ^ 11 + (-125417783 / 6912000) * t ^ 13 + (-67241 / 16000) * t ^ 15 + (-8197 / 122880) * t ^ 17 + (5226883 / 13824000) * t ^ 19 + (360901 / 9216000) * t ^ 21 + (-17661 / 64) * alpha * t ^ 3 + (5149103 / 14400) * alpha * t ^ 5 + (2407494133 / 27648000) * alpha * t ^ 7 + (-178580523 / 1024000) * alpha * t ^ 9 + (-387120511 / 27648000) * alpha * t ^ 11 + (435004139 / 20736000) * alpha * t ^ 13 + (-27800863 / 11059200) * alpha * t ^ 15 + (87293 / 2457600) * alpha * t ^ 17 + (14147729 / 331776000) * alpha * t ^ 19 + (5831 / 294912) * alpha * t ^ 21 + (4465 / 2654208) * alpha * t ^ 25) * d_sq
theorem v56_44 (t : ℂ) : (momentPoly 56 z56 4 4).eval t = (223638856 + (-606260616) * t ^ 2 + (51070960173 / 100) * t ^ 4 + (-344841435303 / 5000) * t ^ 6 + (-6766098257557343 / 96000000) * t ^ 8 + (40553081890453 / 24000000) * t ^ 10 + (178913659178423 / 19200000) * t ^ 12 + (12464403317347 / 16000000) * t ^ 14 + (-253672172928253 / 1152000000) * t ^ 16 + (-1439050983893 / 144000000) * t ^ 18 + (-6467403843653 / 864000000) * t ^ 20 + (1957811235457 / 144000000) * t ^ 22 + (-983015244559 / 192000000) * t ^ 24 + (84536384731 / 144000000) * t ^ 26 + (236831019977 / 3456000000) * t ^ 32 + (-15545144 / 3) * d * t ^ 2 + (54207257 / 4) * d * t ^ 4 + (-36485874557 / 3000) * d * t ^ 6 + (249851843291957 / 57600000) * d * t ^ 8 + (-3551726417401 / 4800000) * d * t ^ 10 + (9267336696427 / 57600000) * d * t ^ 12 + (245811796993 / 5760000) * d * t ^ 14 + (-4805449168931 / 230400000) * d * t ^ 16 + (28010049043 / 9600000) * d * t ^ 18 + (40535984947 / 57600000) * d * t ^ 20 + (-461354049 / 3200000) * d * t ^ 22 + (-3881921 / 1536000) * d * t ^ 24 + (-7178136029 / 86400000) * d * t ^ 26 + (3295379 / 5529600) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z56, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v55_00, v55_01, v55_02, v55_03, v55_04, v55_10, v55_11, v55_12, v55_13, v55_14, v55_20, v55_21, v55_22, v55_23, v55_24, v55_30, v55_31, v55_32, v55_33, v55_34, v55_40, v55_41, v55_42, v55_43, v55_44]
  try simp only [phase53_00, phase53_01, phase53_02, phase53_03, phase53_04, phase53_10, phase53_11, phase53_12, phase53_13, phase53_14, phase53_20, phase53_21, phase53_22, phase53_23, phase53_24, phase53_30, phase53_31, phase53_32, phase53_33, phase53_34, phase53_40, phase53_41, phase53_42, phase53_43, phase53_44]
  try simp only [star_one, star_neg]
  linear_combination ((9715715 / 36) * t ^ 2 + (-340110877 / 720) * t ^ 4 + (-813115429 / 28800) * t ^ 6 + (27852553787389 / 69120000) * t ^ 8 + (-12316101280739 / 69120000) * t ^ 10 + (1568705371967 / 138240000) * t ^ 12 + (-172767902233 / 138240000) * t ^ 14 + (-370302139871 / 103680000) * t ^ 16 + (17324740193 / 46080000) * t ^ 18 + (-170514566801 / 248832000) * t ^ 20 + (3794469833 / 82944000) * t ^ 22 + (-1376601313 / 124416000) * t ^ 26 + (-1655779 / 80) * d * t ^ 4 + (465404473 / 9600) * d * t ^ 6 + (-86903448463 / 2764800) * d * t ^ 8 + (1285966147 / 27648000) * d * t ^ 10 + (156413768429 / 55296000) * d * t ^ 12 + (1738720483 / 2073600) * d * t ^ 14 + (-38170393841 / 331776000) * d * t ^ 16 + (279017081 / 8294400) * d * t ^ 18 + (356766533 / 82944000) * d * t ^ 20 + (-336676549 / 41472000) * d * t ^ 22 + (3881921 / 18432000) * d * t ^ 24 + (-7249811 / 12441600) * d * t ^ 26 + (-3295379 / 66355200) * d * t ^ 32 + (35105 / 384) * d ^ 2 * t ^ 6 + (-5355287 / 51840) * d ^ 2 * t ^ 8 + (-4725378173 / 82944000) * d ^ 2 * t ^ 10 + (11729874797 / 165888000) * d ^ 2 * t ^ 12 + (71241521 / 13824000) * d ^ 2 * t ^ 14 + (-818569811 / 110592000) * d ^ 2 * t ^ 16 + (14538541 / 16588800) * d ^ 2 * t ^ 18 + (2463407 / 19906560) * d ^ 2 * t ^ 20 + (-49179043 / 331776000) * d ^ 2 * t ^ 22 + (-17041 / 1769472) * d ^ 2 * t ^ 24 + (179987 / 6635520) * d ^ 2 * t ^ 26 + (-9025 / 31850496) * d ^ 2 * t ^ 32) * alpha_sq + ((1943143 / 12) * t ^ 2 + (-21698507 / 48) * t ^ 4 + (64085629 / 144) * t ^ 6 + (-99560161711 / 552960) * t ^ 8 + (89458834279 / 3072000) * t ^ 10 + (-1116316540291 / 276480000) * t ^ 12 + (16265785973 / 27648000) * t ^ 14 + (-40024009591 / 110592000) * t ^ 16 + (538621 / 307200) * t ^ 18 + (-1462635133 / 165888000) * t ^ 20 + (521232667 / 552960000) * t ^ 22 + (17041 / 589824) * t ^ 24 + (316247 / 737280) * t ^ 26 + (9025 / 10616832) * t ^ 32) * d_sq
#print axioms v56_00
#print axioms v56_11
#print axioms v56_22
#print axioms v56_33
#print axioms v56_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v57_02 (t : ℂ) : (momentPoly 57 z57 0 2).eval t = ((-1 / 2) * t ^ 2 + (333 / 32) * t ^ 4 + (-1 / 4) * d * t ^ 2 + (181 / 40) * alpha * t ^ 2 + (-171 / 40) * alpha * t ^ 4 + (-1 / 24) * alpha * d * t ^ 2 + (1 / 96) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02]
  try simp only [phase57_00, phase57_01, phase57_02]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 72) * t ^ 2) * alpha_sq + ((-1 / 72) * t ^ 2) * d_sq
theorem v57_03 (t : ℂ) : (momentPoly 57 z57 0 3).eval t = ((-1379 / 320) * t ^ 3 + (9609 / 320) * t ^ 5 + 2 * t ^ 9 + (421 / 192) * d * t ^ 3 + (-227 / 64) * d * t ^ 5 + (-47 / 384) * d * t ^ 9 + (103427 / 4800) * alpha * t ^ 3 + (-33841 / 1600) * alpha * t ^ 5 + (31967 / 9600) * alpha * t ^ 9 + (-553 / 320) * alpha * d * t ^ 3 + (523 / 320) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_03]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03]
  try simp only [star_one, star_neg]
  linear_combination ((-553 / 960) * t ^ 3 + (171 / 320) * t ^ 5 + (5 / 576) * d * t ^ 3 + (-1 / 288) * d * t ^ 5) * alpha_sq + ((-1 / 24) * t ^ 3 + (-5 / 576) * alpha * t ^ 3 + (1 / 288) * alpha * t ^ 5) * d_sq
theorem v57_04 (t : ℂ) : (momentPoly 57 z57 0 4).eval t = ((-13353 / 40) * t ^ 4 + (1052049 / 3200) * t ^ 6 + (414237 / 3200) * t ^ 8 + (-1949 / 800) * t ^ 10 + (5185 / 512) * t ^ 16 + (5269 / 480) * d * t ^ 4 + (-1945 / 128) * d * t ^ 6 + (513 / 640) * d * t ^ 8 + (-143 / 96) * d * t ^ 10 + (33217 / 24000) * alpha * t ^ 4 + (4588849 / 16000) * alpha * t ^ 6 + (-2222083 / 8000) * alpha * t ^ 8 + (-803 / 6000) * alpha * t ^ 10 + (173441 / 48000) * alpha * t ^ 16 + (-42001 / 4800) * alpha * d * t ^ 4 + (88373 / 9600) * alpha * d * t ^ 6 + (113 / 192) * alpha * d * t ^ 8 + (-6511 / 3600) * alpha * d * t ^ 10 + (95 / 4608) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_03, v56_04]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04]
  try simp only [star_one, star_neg]
  linear_combination ((-16469 / 3600) * t ^ 4 + (53899 / 14400) * t ^ 6 + (-7111 / 10800) * t ^ 10 + (563 / 1440) * d * t ^ 4 + (-529 / 1152) * d * t ^ 6 + (57 / 640) * d * t ^ 8 + (5 / 3456) * d ^ 2 * t ^ 6 + (-1 / 3456) * d ^ 2 * t ^ 8) * alpha_sq + ((31 / 144) * t ^ 4 + (-91 / 128) * t ^ 6 + (1 / 1152) * t ^ 8 + (-47 / 864) * t ^ 10 + (-563 / 1440) * alpha * t ^ 4 + (533 / 1440) * alpha * t ^ 6) * d_sq
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
theorem v57_12 (t : ℂ) : (momentPoly 57 z57 1 2).eval t = (113 * t + (-29727 / 320) * t ^ 3 + (2497 / 320) * t ^ 5 + (-113 / 8) * d * t + (883 / 64) * d * t ^ 3 + (-75 / 64) * d * t ^ 5 + (113 / 8) * alpha * t + (-2057 / 320) * alpha * t ^ 3 + (-2063 / 320) * alpha * t ^ 5 + (-553 / 960) * alpha * d * t ^ 3 + (523 / 960) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_10, v56_11, v56_12]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12]
  try simp only [star_one, star_neg]
  linear_combination ((553 / 2880) * t ^ 3 + (-57 / 320) * t ^ 5 + (-5 / 1728) * d * t ^ 3 + (1 / 864) * d * t ^ 5) * alpha_sq + ((-1 / 24) * t ^ 3 + (-5 / 1728) * alpha * t ^ 3 + (1 / 864) * alpha * t ^ 5) * d_sq
theorem v57_13 (t : ℂ) : (momentPoly 57 z57 1 3).eval t = ((-84) * t ^ 2 + (2700599 / 1600) * t ^ 4 + (-4705947 / 3200) * t ^ 6 + (5149 / 3200) * t ^ 10 + (-42) * d * t ^ 2 + (130 / 3) * d * t ^ 4 + (-95 / 16) * d * t ^ 6 + (-143 / 384) * d * t ^ 10 + (3801 / 5) * alpha * t ^ 2 + (-3175769 / 2400) * alpha * t ^ 4 + (450127 / 800) * alpha * t ^ 6 + (70607 / 9600) * alpha * t ^ 10 + (-7) * alpha * d * t ^ 2 + (18911 / 4800) * alpha * d * t ^ 4 + (9909 / 3200) * alpha * d * t ^ 6 + (-3949 / 9600) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_03, v56_10, v56_11, v56_12, v56_13]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13]
  try simp only [star_one, star_neg]
  linear_combination ((-7 / 3) * t ^ 2 + (62923 / 28800) * t ^ 4 + (-1069 / 57600) * t ^ 6 + (7111 / 43200) * t ^ 10) * alpha_sq + ((-7 / 3) * t ^ 2 + (2471 / 1152) * t ^ 4 + (-809 / 2304) * t ^ 6 + (-47 / 3456) * t ^ 10 + (-563 / 2880) * alpha * t ^ 4 + (533 / 2880) * alpha * t ^ 6) * d_sq
theorem v57_14 (t : ℂ) : (momentPoly 57 z57 1 4).eval t = ((-153069 / 160) * t ^ 3 + (417124267 / 64000) * t ^ 5 + (-161780817 / 32000) * t ^ 7 + (45801057 / 128000) * t ^ 9 + (-12282641 / 32000) * t ^ 11 + (1213691 / 128000) * t ^ 17 + (15577 / 32) * d * t ^ 3 + (-46707323 / 38400) * d * t ^ 5 + (4571631 / 6400) * d * t ^ 7 + (-911467 / 25600) * d * t ^ 9 + (23257 / 768) * d * t ^ 11 + (-1163 / 1024) * d * t ^ 17 + (3826799 / 800) * alpha * t ^ 3 + (-1671937679 / 192000) * alpha * t ^ 5 + (131526903 / 32000) * alpha * t ^ 7 + (58295297 / 128000) * alpha * t ^ 9 + (-56446403 / 96000) * alpha * t ^ 11 + (-314759 / 128000) * alpha * t ^ 17 + (-61383 / 160) * alpha * d * t ^ 3 + (139774093 / 192000) * alpha * d * t ^ 5 + (-35898163 / 96000) * alpha * d * t ^ 7 + (12264823 / 384000) * alpha * d * t ^ 9 + (-1090037 / 288000) * alpha * d * t ^ 11 + (-496573 / 1152000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_03, v56_04, v56_10, v56_11, v56_12, v56_13, v56_14]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14]
  try simp only [star_one, star_neg]
  linear_combination ((-20461 / 160) * t ^ 3 + (122035777 / 576000) * t ^ 5 + (-7090759 / 96000) * t ^ 7 + (-4038041 / 384000) * t ^ 9 + (-115547 / 96000) * t ^ 11 + (173441 / 1152000) * t ^ 17 + (185 / 96) * d * t ^ 3 + (-138751 / 69120) * d * t ^ 5 + (-29 / 576) * d * t ^ 7 + (25177 / 138240) * d * t ^ 9 + (-235 / 20736) * d * t ^ 11 + (95 / 41472) * d * t ^ 17 + (563 / 34560) * d ^ 2 * t ^ 7 + (-523 / 34560) * d ^ 2 * t ^ 9) * alpha_sq + ((-37 / 4) * t ^ 3 + (20521 / 2304) * t ^ 5 + (-23161 / 11520) * t ^ 7 + (259 / 2880) * t ^ 9 + (-95 / 432) * t ^ 11 + (-185 / 96) * alpha * t ^ 3 + (11711 / 12800) * alpha * t ^ 5 + (27151 / 28800) * alpha * t ^ 7 + (1613 / 27648) * alpha * t ^ 9 + (-103051 / 518400) * alpha * t ^ 11 + (95 / 41472) * alpha * t ^ 17) * d_sq
theorem v57_20 (t : ℂ) : (momentPoly 57 z57 2 0).eval t = ((-1 / 2) * t ^ 2 + (333 / 32) * t ^ 4 + (-1 / 4) * d * t ^ 2 + (-181 / 40) * alpha * t ^ 2 + (171 / 40) * alpha * t ^ 4 + (1 / 24) * alpha * d * t ^ 2 + (-1 / 96) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_10, v56_20]
  try simp only [phase57_00, phase57_10, phase57_20]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 72) * t ^ 2) * alpha_sq + ((-1 / 72) * t ^ 2) * d_sq
theorem v57_21 (t : ℂ) : (momentPoly 57 z57 2 1).eval t = (113 * t + (-29727 / 320) * t ^ 3 + (2497 / 320) * t ^ 5 + (-113 / 8) * d * t + (883 / 64) * d * t ^ 3 + (-75 / 64) * d * t ^ 5 + (-113 / 8) * alpha * t + (2057 / 320) * alpha * t ^ 3 + (2063 / 320) * alpha * t ^ 5 + (553 / 960) * alpha * d * t ^ 3 + (-523 / 960) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_10, v56_11, v56_20, v56_21]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21]
  try simp only [star_one, star_neg]
  linear_combination ((553 / 2880) * t ^ 3 + (-57 / 320) * t ^ 5 + (-5 / 1728) * d * t ^ 3 + (1 / 864) * d * t ^ 5) * alpha_sq + ((-1 / 24) * t ^ 3 + (5 / 1728) * alpha * t ^ 3 + (-1 / 864) * alpha * t ^ 5) * d_sq
theorem v57_22 (t : ℂ) : (momentPoly 57 z57 2 2).eval t = (6441 + (-10528) * t ^ 2 + (3245179 / 800) * t ^ 4 + (192113 / 3200) * t ^ 6 + (340171 / 3200) * t ^ 8 + (-56) * d * t ^ 2 + (8659 / 160) * d * t ^ 4 + (-365 / 128) * d * t ^ 6 + (-171 / 640) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_10, v56_11, v56_12, v56_20, v56_21, v56_22]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22]
  try simp only [star_one, star_neg]
  linear_combination ((28 / 9) * t ^ 2 + (-1999 / 1440) * t ^ 4 + (-587 / 480) * t ^ 6 + (-563 / 4320) * d * t ^ 4 + (529 / 3456) * d * t ^ 6 + (-19 / 640) * d * t ^ 8 + (-5 / 10368) * d ^ 2 * t ^ 6 + (1 / 10368) * d ^ 2 * t ^ 8) * alpha_sq + ((-28 / 9) * t ^ 2 + (803 / 288) * t ^ 4 + (-799 / 3456) * t ^ 6 + (-1 / 3456) * t ^ 8) * d_sq
theorem v57_23 (t : ℂ) : (momentPoly 57 z57 2 3).eval t = (18985 * t + (-9899091 / 320) * t ^ 3 + (458782881 / 32000) * t ^ 5 + (-3741117 / 1600) * t ^ 7 + (13490979 / 32000) * t ^ 9 + (5904677 / 128000) * t ^ 11 + (-2930357 / 128000) * t ^ 13 + (-18985 / 8) * d * t + (294039 / 64) * d * t ^ 3 + (-16505199 / 6400) * d * t ^ 5 + (283621 / 768) * d * t ^ 7 + (-435403 / 12800) * d * t ^ 9 + (38111 / 25600) * d * t ^ 11 + (-80227 / 76800) * d * t ^ 13 + (18985 / 8) * alpha * t + (-684981 / 320) * alpha * t ^ 3 + (-13301501 / 6400) * alpha * t ^ 5 + (36325061 / 19200) * alpha * t ^ 7 + (-924383 / 12800) * alpha * t ^ 9 + (-19031 / 25600) * alpha * t ^ 11 + (3364399 / 76800) * alpha * t ^ 13 + (-61383 / 320) * alpha * d * t ^ 3 + (6806753 / 19200) * alpha * d * t ^ 5 + (-774673 / 4800) * alpha * d * t ^ 7 + (-131 / 1280) * alpha * d * t ^ 9 + (-32893 / 25600) * alpha * d * t ^ 11 + (-8357 / 15360) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_03, v56_10, v56_11, v56_12, v56_13, v56_20, v56_21, v56_22, v56_23]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23]
  try simp only [star_one, star_neg]
  linear_combination ((20461 / 320) * t ^ 3 + (-121411 / 1200) * t ^ 5 + (1094891 / 28800) * t ^ 7 + (821387 / 691200) * t ^ 11 + (-2717 / 5120) * t ^ 13 + (-185 / 192) * d * t ^ 3 + (31561 / 43200) * d * t ^ 5 + (133861 / 345600) * d * t ^ 7 + (-106729 / 691200) * d * t ^ 9 + (-115051 / 2073600) * d * t ^ 11 + (7111 / 518400) * d * t ^ 13 + (-563 / 34560) * d ^ 2 * t ^ 7 + (523 / 34560) * d ^ 2 * t ^ 9) * alpha_sq + ((-111 / 8) * t ^ 3 + (28579 / 2304) * t ^ 5 + (-1121 / 1280) * t ^ 7 + (-259 / 2880) * t ^ 9 + (-95 / 1728) * t ^ 11 + (-185 / 192) * alpha * t ^ 3 + (31561 / 43200) * alpha * t ^ 5 + (72233 / 345600) * alpha * t ^ 7 + (-5 / 27648) * alpha * t ^ 9 + (-91301 / 2073600) * alpha * t ^ 11 + (-47 / 41472) * alpha * t ^ 13) * d_sq
theorem v57_24 (t : ℂ) : (momentPoly 57 z57 2 4).eval t = ((-18650) * t ^ 2 + (57862381 / 160) * t ^ 4 + (-12078357053 / 20000) * t ^ 6 + (325220360761 / 1280000) * t ^ 8 + (8771595 / 1024) * t ^ 10 + (2437291093 / 7680000) * t ^ 12 + (-116078413 / 1920000) * t ^ 14 + (301770527 / 7680000) * t ^ 18 + (188180159 / 3840000) * t ^ 20 + (-9325) * d * t ^ 2 + (57200 / 3) * d * t ^ 4 + (-58236749 / 4800) * d * t ^ 6 + (625326721 / 256000) * d * t ^ 8 + (-112076743 / 384000) * d * t ^ 10 + (76093127 / 512000) * d * t ^ 12 + (3909067 / 384000) * d * t ^ 14 + (-3008639 / 1536000) * d * t ^ 18 + (-58171 / 384000) * d * t ^ 20 + (337565 / 2) * alpha * t ^ 2 + (-51083423 / 120) * alpha * t ^ 4 + (16586294783 / 48000) * alpha * t ^ 6 + (-22071334103 / 256000) * alpha * t ^ 8 + (471274957 / 384000) * alpha * t ^ 10 + (-1788006553 / 512000) * alpha * t ^ 12 + (-6455847 / 128000) * alpha * t ^ 14 + (-100291921 / 1536000) * alpha * t ^ 18 + (21803313 / 256000) * alpha * t ^ 20 + (-9325 / 6) * alpha * d * t ^ 2 + (649009 / 480) * alpha * d * t ^ 4 + (22465661 / 12000) * alpha * d * t ^ 6 + (-1334080253 / 768000) * alpha * d * t ^ 8 + (-36830839 / 384000) * alpha * d * t ^ 10 + (831057631 / 4608000) * alpha * d * t ^ 12 + (-119559 / 5120) * alpha * d * t ^ 14 + (1525331 / 4608000) * alpha * d * t ^ 18 + (101 / 1024) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_03, v56_04, v56_10, v56_11, v56_12, v56_13, v56_14, v56_20, v56_21, v56_22, v56_23, v56_24]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24]
  try simp only [star_one, star_neg]
  linear_combination ((-9325 / 18) * t ^ 2 + (692153 / 720) * t ^ 4 + (-713922323 / 1728000) * t ^ 6 + (-13367413 / 576000) * t ^ 8 + (206110447 / 3456000) * t ^ 10 + (-14200817 / 288000) * t ^ 12 + (-922567 / 86400) * t ^ 14 + (-383413 / 1152000) * t ^ 18 + (1414033 / 1728000) * d * t ^ 6 + (-7652209 / 2304000) * d * t ^ 8 + (1956611 / 576000) * d * t ^ 10 + (-6512809 / 4608000) * d * t ^ 12 + (5018057 / 10368000) * d * t ^ 14 + (-672917 / 41472000) * d * t ^ 18 + (-58171 / 3456000) * d * t ^ 20 + (-188779 / 4147200) * d ^ 2 * t ^ 8 + (10247 / 230400) * d ^ 2 * t ^ 10 + (809 / 331776) * d ^ 2 * t ^ 12 + (-54463 / 6220800) * d ^ 2 * t ^ 14 + (-475 / 995328) * d ^ 2 * t ^ 18 + (95 / 497664) * d ^ 2 * t ^ 20) * alpha_sq + ((-9325 / 18) * t ^ 2 + (135905 / 144) * t ^ 4 + (-196609037 / 345600) * t ^ 6 + (180544519 / 1382400) * t ^ 8 + (-869171 / 69120) * t ^ 10 + (1027777 / 184320) * t ^ 12 + (-841649 / 2073600) * t ^ 14 + (-36881 / 331776) * t ^ 18 + (-95 / 165888) * t ^ 20 + (-6193 / 72) * alpha * t ^ 4 + (268199453 / 1728000) * alpha * t ^ 6 + (-9227541 / 128000) * alpha * t ^ 8 + (10873273 / 3456000) * alpha * t ^ 10 + (-6025043 / 10368000) * alpha * t ^ 12 + (-25541 / 103680) * alpha * t ^ 14 + (-472823 / 10368000) * alpha * t ^ 18) * d_sq
theorem v57_30 (t : ℂ) : (momentPoly 57 z57 3 0).eval t = ((-1379 / 320) * t ^ 3 + (9609 / 320) * t ^ 5 + 2 * t ^ 9 + (421 / 192) * d * t ^ 3 + (-227 / 64) * d * t ^ 5 + (-47 / 384) * d * t ^ 9 + (-103427 / 4800) * alpha * t ^ 3 + (33841 / 1600) * alpha * t ^ 5 + (-31967 / 9600) * alpha * t ^ 9 + (553 / 320) * alpha * d * t ^ 3 + (-523 / 320) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_10, v56_20, v56_30]
  try simp only [phase57_00, phase57_10, phase57_20, phase57_30]
  try simp only [star_one, star_neg]
  linear_combination ((-553 / 960) * t ^ 3 + (171 / 320) * t ^ 5 + (5 / 576) * d * t ^ 3 + (-1 / 288) * d * t ^ 5) * alpha_sq + ((-1 / 24) * t ^ 3 + (5 / 576) * alpha * t ^ 3 + (-1 / 288) * alpha * t ^ 5) * d_sq
theorem v57_31 (t : ℂ) : (momentPoly 57 z57 3 1).eval t = ((-84) * t ^ 2 + (2700599 / 1600) * t ^ 4 + (-4705947 / 3200) * t ^ 6 + (5149 / 3200) * t ^ 10 + (-42) * d * t ^ 2 + (130 / 3) * d * t ^ 4 + (-95 / 16) * d * t ^ 6 + (-143 / 384) * d * t ^ 10 + (-3801 / 5) * alpha * t ^ 2 + (3175769 / 2400) * alpha * t ^ 4 + (-450127 / 800) * alpha * t ^ 6 + (-70607 / 9600) * alpha * t ^ 10 + 7 * alpha * d * t ^ 2 + (-18911 / 4800) * alpha * d * t ^ 4 + (-9909 / 3200) * alpha * d * t ^ 6 + (3949 / 9600) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_10, v56_11, v56_20, v56_21, v56_30, v56_31]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21, phase57_30, phase57_31]
  try simp only [star_one, star_neg]
  linear_combination ((-7 / 3) * t ^ 2 + (62923 / 28800) * t ^ 4 + (-1069 / 57600) * t ^ 6 + (7111 / 43200) * t ^ 10) * alpha_sq + ((-7 / 3) * t ^ 2 + (2471 / 1152) * t ^ 4 + (-809 / 2304) * t ^ 6 + (-47 / 3456) * t ^ 10 + (563 / 2880) * alpha * t ^ 4 + (-533 / 2880) * alpha * t ^ 6) * d_sq
theorem v57_32 (t : ℂ) : (momentPoly 57 z57 3 2).eval t = (18985 * t + (-9899091 / 320) * t ^ 3 + (458782881 / 32000) * t ^ 5 + (-3741117 / 1600) * t ^ 7 + (13490979 / 32000) * t ^ 9 + (5904677 / 128000) * t ^ 11 + (-2930357 / 128000) * t ^ 13 + (-18985 / 8) * d * t + (294039 / 64) * d * t ^ 3 + (-16505199 / 6400) * d * t ^ 5 + (283621 / 768) * d * t ^ 7 + (-435403 / 12800) * d * t ^ 9 + (38111 / 25600) * d * t ^ 11 + (-80227 / 76800) * d * t ^ 13 + (-18985 / 8) * alpha * t + (684981 / 320) * alpha * t ^ 3 + (13301501 / 6400) * alpha * t ^ 5 + (-36325061 / 19200) * alpha * t ^ 7 + (924383 / 12800) * alpha * t ^ 9 + (19031 / 25600) * alpha * t ^ 11 + (-3364399 / 76800) * alpha * t ^ 13 + (61383 / 320) * alpha * d * t ^ 3 + (-6806753 / 19200) * alpha * d * t ^ 5 + (774673 / 4800) * alpha * d * t ^ 7 + (131 / 1280) * alpha * d * t ^ 9 + (32893 / 25600) * alpha * d * t ^ 11 + (8357 / 15360) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_10, v56_11, v56_12, v56_20, v56_21, v56_22, v56_30, v56_31, v56_32]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22, phase57_30, phase57_31, phase57_32]
  try simp only [star_one, star_neg]
  linear_combination ((20461 / 320) * t ^ 3 + (-121411 / 1200) * t ^ 5 + (1094891 / 28800) * t ^ 7 + (821387 / 691200) * t ^ 11 + (-2717 / 5120) * t ^ 13 + (-185 / 192) * d * t ^ 3 + (31561 / 43200) * d * t ^ 5 + (133861 / 345600) * d * t ^ 7 + (-106729 / 691200) * d * t ^ 9 + (-115051 / 2073600) * d * t ^ 11 + (7111 / 518400) * d * t ^ 13 + (-563 / 34560) * d ^ 2 * t ^ 7 + (523 / 34560) * d ^ 2 * t ^ 9) * alpha_sq + ((-111 / 8) * t ^ 3 + (28579 / 2304) * t ^ 5 + (-1121 / 1280) * t ^ 7 + (-259 / 2880) * t ^ 9 + (-95 / 1728) * t ^ 11 + (185 / 192) * alpha * t ^ 3 + (-31561 / 43200) * alpha * t ^ 5 + (-72233 / 345600) * alpha * t ^ 7 + (5 / 27648) * alpha * t ^ 9 + (91301 / 2073600) * alpha * t ^ 11 + (47 / 41472) * alpha * t ^ 13) * d_sq
theorem v57_33 (t : ℂ) : (momentPoly 57 z57 3 3).eval t = (1082145 + (-2629650) * t ^ 2 + (321272721 / 160) * t ^ 4 + (-69836855877 / 160000) * t ^ 6 + (7202576367 / 320000) * t ^ 8 + (-14130079479 / 320000) * t ^ 10 + (-23809159 / 320000) * t ^ 12 + (-102899043 / 640000) * t ^ 14 + (-7136907 / 640000) * t ^ 18 + (-27975 / 2) * d * t ^ 2 + (857241 / 32) * d * t ^ 4 + (-1354755721 / 96000) * d * t ^ 6 + (17481217 / 12800) * d * t ^ 8 + (-8735901 / 64000) * d * t ^ 10 + (-258343 / 16000) * d * t ^ 12 + (455001 / 32000) * d * t ^ 14 + (-47 / 96) * d * t ^ 18) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_03, v56_10, v56_11, v56_12, v56_13, v56_20, v56_21, v56_22, v56_23, v56_30, v56_31, v56_32, v56_33]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23, phase57_30, phase57_31, phase57_32, phase57_33]
  try simp only [star_one, star_neg]
  linear_combination ((9325 / 12) * t ^ 2 + (-21989 / 32) * t ^ 4 + (-20510873 / 38400) * t ^ 6 + (35293247 / 76800) * t ^ 8 + (-46613 / 3072) * t ^ 10 + (8957891 / 691200) * t ^ 12 + (6879361 / 1382400) * t ^ 14 + (3556267 / 4147200) * t ^ 18 + (-6193 / 96) * d * t ^ 4 + (15042431 / 115200) * d * t ^ 6 + (-17334721 / 230400) * d * t ^ 8 + (2179357 / 230400) * d * t ^ 10 + (-349291 / 345600) * d * t ^ 12 + (22193 / 43200) * d * t ^ 14 + (-415 / 1728) * d ^ 2 * t ^ 6 + (23161 / 172800) * d ^ 2 * t ^ 8 + (10909 / 115200) * d ^ 2 * t ^ 10 + (-4049 / 345600) * d ^ 2 * t ^ 14) * alpha_sq + ((-9325 / 12) * t ^ 2 + (44165 / 32) * t ^ 4 + (-81933847 / 115200) * t ^ 6 + (4519057 / 46080) * t ^ 8 + (-244833 / 25600) * t ^ 10 + (21311 / 138240) * t ^ 12 + (-853399 / 1382400) * t ^ 14 + (-2209 / 165888) * t ^ 18) * d_sq
theorem v57_34 (t : ℂ) : (momentPoly 57 z57 3 4).eval t = (4215345 * t + (-816808779 / 80) * t ^ 3 + (136555805937 / 16000) * t ^ 5 + (-1293060319971 / 400000) * t ^ 7 + (5918497379101 / 6400000) * t ^ 9 + (-1295188744171 / 6400000) * t ^ 11 + (-518507229581 / 15360000) * t ^ 13 + (186362541519 / 12800000) * t ^ 15 + (-134086441147 / 51200000) * t ^ 17 + (-842278093 / 19200000) * t ^ 19 + (1139273861 / 6400000) * t ^ 21 + (8501788447 / 153600000) * t ^ 25 + (-4215345 / 8) * d * t + (24262191 / 16) * d * t ^ 3 + (-4992728823 / 3200) * d * t ^ 5 + (262415860811 / 384000) * d * t ^ 7 + (-100713728023 / 768000) * d * t ^ 9 + (37180491787 / 1920000) * d * t ^ 11 + (-19128380663 / 9216000) * d * t ^ 13 + (1371305881 / 1536000) * d * t ^ 15 + (-1634677 / 1228800) * d * t ^ 17 + (54231857 / 4608000) * d * t ^ 19 + (-197544371 / 15360000) * d * t ^ 21 + (-669853 / 737280) * d * t ^ 25 + (4215345 / 8) * alpha * t + (-56520189 / 80) * alpha * t ^ 3 + (-2124459657 / 3200) * alpha * t ^ 5 + (2619911175193 / 1920000) * alpha * t ^ 7 + (-84772336493 / 153600) * alpha * t ^ 9 + (55252607371 / 1920000) * alpha * t ^ 11 + (1281820700321 / 46080000) * alpha * t ^ 13 + (-187151164999 / 7680000) * alpha * t ^ 15 + (-30387224869 / 30720000) * alpha * t ^ 17 + (-6317292887 / 23040000) * alpha * t ^ 19 + (2591426419 / 15360000) * alpha * t ^ 21 + (-517310137 / 18432000) * alpha * t ^ 25 + (-5064927 / 80) * alpha * d * t ^ 3 + (553901887 / 3200) * alpha * d * t ^ 5 + (-29750962483 / 192000) * alpha * d * t ^ 7 + (34192321897 / 768000) * alpha * d * t ^ 9 + (-286387873 / 768000) * alpha * d * t ^ 11 + (5961053597 / 9216000) * alpha * d * t ^ 13 + (169833679 / 512000) * alpha * d * t ^ 15 + (59875177 / 2048000) * alpha * d * t ^ 17 + (3769931 / 115200) * alpha * d * t ^ 19 + (-7360111 / 256000) * alpha * d * t ^ 21 + (-821303 / 2048000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_03, v56_04, v56_10, v56_11, v56_12, v56_13, v56_14, v56_20, v56_21, v56_22, v56_23, v56_24, v56_30, v56_31, v56_32, v56_33, v56_34]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24, phase57_30, phase57_31, phase57_32, phase57_33, phase57_34]
  try simp only [star_one, star_neg]
  linear_combination ((1688309 / 80) * t ^ 3 + (-75130577 / 1600) * t ^ 5 + (18415724173 / 576000) * t ^ 7 + (-721291483 / 128000) * t ^ 9 + (143099801 / 460800) * t ^ 11 + (-25889992249 / 27648000) * t ^ 13 + (674835809 / 2764800) * t ^ 15 + (-577439863 / 18432000) * t ^ 17 + (-28124003 / 41472000) * t ^ 19 + (11159377 / 1152000) * t ^ 21 + (24802063 / 55296000) * t ^ 25 + (-15265 / 48) * d * t ^ 3 + (211777 / 600) * d * t ^ 5 + (1064472793 / 3456000) * d * t ^ 7 + (-5845635487 / 13824000) * d * t ^ 9 + (690005627 / 13824000) * d * t ^ 11 + (228857587 / 6912000) * d * t ^ 13 + (-15673873 / 3456000) * d * t ^ 15 + (32066011 / 33177600) * d * t ^ 17 + (-9595147 / 31104000) * d * t ^ 19 + (-30064459 / 165888000) * d * t ^ 21 + (135109 / 4976640) * d * t ^ 25 + (-185227 / 17280) * d ^ 2 * t ^ 7 + (265125053 / 13824000) * d ^ 2 * t ^ 9 + (-122281991 / 13824000) * d ^ 2 * t ^ 11 + (10905623 / 27648000) * d ^ 2 * t ^ 13 + (-3731759 / 41472000) * d ^ 2 * t ^ 15 + (-8357 / 552960) * d ^ 2 * t ^ 17 + (-10697 / 663552) * d ^ 2 * t ^ 19 + (46597 / 5184000) * d ^ 2 * t ^ 21) * alpha_sq + ((-9159 / 2) * t ^ 3 + (3115111 / 384) * t ^ 5 + (-4700842909 / 1152000) * t ^ 7 + (241417131 / 512000) * t ^ 9 + (-28408893 / 512000) * t ^ 11 + (196514023 / 9216000) * t ^ 13 + (59484757 / 13824000) * t ^ 15 + (8197 / 92160) * t ^ 17 + (-8741869 / 16588800) * t ^ 19 + (-360901 / 6912000) * t ^ 21 + (-15265 / 48) * alpha * t ^ 3 + (211777 / 600) * alpha * t ^ 5 + (658960553 / 3456000) * alpha * t ^ 7 + (-3248033189 / 13824000) * alpha * t ^ 9 + (-225149159 / 13824000) * alpha * t ^ 11 + (1102479359 / 41472000) * alpha * t ^ 13 + (-5018801 / 1382400) * alpha * t ^ 15 + (1798099 / 33177600) * alpha * t ^ 17 + (292111 / 3888000) * alpha * t ^ 19 + (39499 / 1327104) * alpha * t ^ 21 + (4465 / 1990656) * alpha * t ^ 25) * d_sq
theorem v57_40 (t : ℂ) : (momentPoly 57 z57 4 0).eval t = ((-13353 / 40) * t ^ 4 + (1052049 / 3200) * t ^ 6 + (414237 / 3200) * t ^ 8 + (-1949 / 800) * t ^ 10 + (5185 / 512) * t ^ 16 + (5269 / 480) * d * t ^ 4 + (-1945 / 128) * d * t ^ 6 + (513 / 640) * d * t ^ 8 + (-143 / 96) * d * t ^ 10 + (-33217 / 24000) * alpha * t ^ 4 + (-4588849 / 16000) * alpha * t ^ 6 + (2222083 / 8000) * alpha * t ^ 8 + (803 / 6000) * alpha * t ^ 10 + (-173441 / 48000) * alpha * t ^ 16 + (42001 / 4800) * alpha * d * t ^ 4 + (-88373 / 9600) * alpha * d * t ^ 6 + (-113 / 192) * alpha * d * t ^ 8 + (6511 / 3600) * alpha * d * t ^ 10 + (-95 / 4608) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_10, v56_20, v56_30, v56_40]
  try simp only [phase57_00, phase57_10, phase57_20, phase57_30, phase57_40]
  try simp only [star_one, star_neg]
  linear_combination ((-16469 / 3600) * t ^ 4 + (53899 / 14400) * t ^ 6 + (-7111 / 10800) * t ^ 10 + (563 / 1440) * d * t ^ 4 + (-529 / 1152) * d * t ^ 6 + (57 / 640) * d * t ^ 8 + (5 / 3456) * d ^ 2 * t ^ 6 + (-1 / 3456) * d ^ 2 * t ^ 8) * alpha_sq + ((31 / 144) * t ^ 4 + (-91 / 128) * t ^ 6 + (1 / 1152) * t ^ 8 + (-47 / 864) * t ^ 10 + (563 / 1440) * alpha * t ^ 4 + (-533 / 1440) * alpha * t ^ 6) * d_sq
theorem v57_41 (t : ℂ) : (momentPoly 57 z57 4 1).eval t = ((-153069 / 160) * t ^ 3 + (417124267 / 64000) * t ^ 5 + (-161780817 / 32000) * t ^ 7 + (45801057 / 128000) * t ^ 9 + (-12282641 / 32000) * t ^ 11 + (1213691 / 128000) * t ^ 17 + (15577 / 32) * d * t ^ 3 + (-46707323 / 38400) * d * t ^ 5 + (4571631 / 6400) * d * t ^ 7 + (-911467 / 25600) * d * t ^ 9 + (23257 / 768) * d * t ^ 11 + (-1163 / 1024) * d * t ^ 17 + (-3826799 / 800) * alpha * t ^ 3 + (1671937679 / 192000) * alpha * t ^ 5 + (-131526903 / 32000) * alpha * t ^ 7 + (-58295297 / 128000) * alpha * t ^ 9 + (56446403 / 96000) * alpha * t ^ 11 + (314759 / 128000) * alpha * t ^ 17 + (61383 / 160) * alpha * d * t ^ 3 + (-139774093 / 192000) * alpha * d * t ^ 5 + (35898163 / 96000) * alpha * d * t ^ 7 + (-12264823 / 384000) * alpha * d * t ^ 9 + (1090037 / 288000) * alpha * d * t ^ 11 + (496573 / 1152000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_10, v56_11, v56_20, v56_21, v56_30, v56_31, v56_40, v56_41]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21, phase57_30, phase57_31, phase57_40, phase57_41]
  try simp only [star_one, star_neg]
  linear_combination ((-20461 / 160) * t ^ 3 + (122035777 / 576000) * t ^ 5 + (-7090759 / 96000) * t ^ 7 + (-4038041 / 384000) * t ^ 9 + (-115547 / 96000) * t ^ 11 + (173441 / 1152000) * t ^ 17 + (185 / 96) * d * t ^ 3 + (-138751 / 69120) * d * t ^ 5 + (-29 / 576) * d * t ^ 7 + (25177 / 138240) * d * t ^ 9 + (-235 / 20736) * d * t ^ 11 + (95 / 41472) * d * t ^ 17 + (563 / 34560) * d ^ 2 * t ^ 7 + (-523 / 34560) * d ^ 2 * t ^ 9) * alpha_sq + ((-37 / 4) * t ^ 3 + (20521 / 2304) * t ^ 5 + (-23161 / 11520) * t ^ 7 + (259 / 2880) * t ^ 9 + (-95 / 432) * t ^ 11 + (185 / 96) * alpha * t ^ 3 + (-11711 / 12800) * alpha * t ^ 5 + (-27151 / 28800) * alpha * t ^ 7 + (-1613 / 27648) * alpha * t ^ 9 + (103051 / 518400) * alpha * t ^ 11 + (-95 / 41472) * alpha * t ^ 17) * d_sq
theorem v57_42 (t : ℂ) : (momentPoly 57 z57 4 2).eval t = ((-18650) * t ^ 2 + (57862381 / 160) * t ^ 4 + (-12078357053 / 20000) * t ^ 6 + (325220360761 / 1280000) * t ^ 8 + (8771595 / 1024) * t ^ 10 + (2437291093 / 7680000) * t ^ 12 + (-116078413 / 1920000) * t ^ 14 + (301770527 / 7680000) * t ^ 18 + (188180159 / 3840000) * t ^ 20 + (-9325) * d * t ^ 2 + (57200 / 3) * d * t ^ 4 + (-58236749 / 4800) * d * t ^ 6 + (625326721 / 256000) * d * t ^ 8 + (-112076743 / 384000) * d * t ^ 10 + (76093127 / 512000) * d * t ^ 12 + (3909067 / 384000) * d * t ^ 14 + (-3008639 / 1536000) * d * t ^ 18 + (-58171 / 384000) * d * t ^ 20 + (-337565 / 2) * alpha * t ^ 2 + (51083423 / 120) * alpha * t ^ 4 + (-16586294783 / 48000) * alpha * t ^ 6 + (22071334103 / 256000) * alpha * t ^ 8 + (-471274957 / 384000) * alpha * t ^ 10 + (1788006553 / 512000) * alpha * t ^ 12 + (6455847 / 128000) * alpha * t ^ 14 + (100291921 / 1536000) * alpha * t ^ 18 + (-21803313 / 256000) * alpha * t ^ 20 + (9325 / 6) * alpha * d * t ^ 2 + (-649009 / 480) * alpha * d * t ^ 4 + (-22465661 / 12000) * alpha * d * t ^ 6 + (1334080253 / 768000) * alpha * d * t ^ 8 + (36830839 / 384000) * alpha * d * t ^ 10 + (-831057631 / 4608000) * alpha * d * t ^ 12 + (119559 / 5120) * alpha * d * t ^ 14 + (-1525331 / 4608000) * alpha * d * t ^ 18 + (-101 / 1024) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_10, v56_11, v56_12, v56_20, v56_21, v56_22, v56_30, v56_31, v56_32, v56_40, v56_41, v56_42]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22, phase57_30, phase57_31, phase57_32, phase57_40, phase57_41, phase57_42]
  try simp only [star_one, star_neg]
  linear_combination ((-9325 / 18) * t ^ 2 + (692153 / 720) * t ^ 4 + (-713922323 / 1728000) * t ^ 6 + (-13367413 / 576000) * t ^ 8 + (206110447 / 3456000) * t ^ 10 + (-14200817 / 288000) * t ^ 12 + (-922567 / 86400) * t ^ 14 + (-383413 / 1152000) * t ^ 18 + (1414033 / 1728000) * d * t ^ 6 + (-7652209 / 2304000) * d * t ^ 8 + (1956611 / 576000) * d * t ^ 10 + (-6512809 / 4608000) * d * t ^ 12 + (5018057 / 10368000) * d * t ^ 14 + (-672917 / 41472000) * d * t ^ 18 + (-58171 / 3456000) * d * t ^ 20 + (-188779 / 4147200) * d ^ 2 * t ^ 8 + (10247 / 230400) * d ^ 2 * t ^ 10 + (809 / 331776) * d ^ 2 * t ^ 12 + (-54463 / 6220800) * d ^ 2 * t ^ 14 + (-475 / 995328) * d ^ 2 * t ^ 18 + (95 / 497664) * d ^ 2 * t ^ 20) * alpha_sq + ((-9325 / 18) * t ^ 2 + (135905 / 144) * t ^ 4 + (-196609037 / 345600) * t ^ 6 + (180544519 / 1382400) * t ^ 8 + (-869171 / 69120) * t ^ 10 + (1027777 / 184320) * t ^ 12 + (-841649 / 2073600) * t ^ 14 + (-36881 / 331776) * t ^ 18 + (-95 / 165888) * t ^ 20 + (6193 / 72) * alpha * t ^ 4 + (-268199453 / 1728000) * alpha * t ^ 6 + (9227541 / 128000) * alpha * t ^ 8 + (-10873273 / 3456000) * alpha * t ^ 10 + (6025043 / 10368000) * alpha * t ^ 12 + (25541 / 103680) * alpha * t ^ 14 + (472823 / 10368000) * alpha * t ^ 18) * d_sq
theorem v57_43 (t : ℂ) : (momentPoly 57 z57 4 3).eval t = (4215345 * t + (-816808779 / 80) * t ^ 3 + (136555805937 / 16000) * t ^ 5 + (-1293060319971 / 400000) * t ^ 7 + (5918497379101 / 6400000) * t ^ 9 + (-1295188744171 / 6400000) * t ^ 11 + (-518507229581 / 15360000) * t ^ 13 + (186362541519 / 12800000) * t ^ 15 + (-134086441147 / 51200000) * t ^ 17 + (-842278093 / 19200000) * t ^ 19 + (1139273861 / 6400000) * t ^ 21 + (8501788447 / 153600000) * t ^ 25 + (-4215345 / 8) * d * t + (24262191 / 16) * d * t ^ 3 + (-4992728823 / 3200) * d * t ^ 5 + (262415860811 / 384000) * d * t ^ 7 + (-100713728023 / 768000) * d * t ^ 9 + (37180491787 / 1920000) * d * t ^ 11 + (-19128380663 / 9216000) * d * t ^ 13 + (1371305881 / 1536000) * d * t ^ 15 + (-1634677 / 1228800) * d * t ^ 17 + (54231857 / 4608000) * d * t ^ 19 + (-197544371 / 15360000) * d * t ^ 21 + (-669853 / 737280) * d * t ^ 25 + (-4215345 / 8) * alpha * t + (56520189 / 80) * alpha * t ^ 3 + (2124459657 / 3200) * alpha * t ^ 5 + (-2619911175193 / 1920000) * alpha * t ^ 7 + (84772336493 / 153600) * alpha * t ^ 9 + (-55252607371 / 1920000) * alpha * t ^ 11 + (-1281820700321 / 46080000) * alpha * t ^ 13 + (187151164999 / 7680000) * alpha * t ^ 15 + (30387224869 / 30720000) * alpha * t ^ 17 + (6317292887 / 23040000) * alpha * t ^ 19 + (-2591426419 / 15360000) * alpha * t ^ 21 + (517310137 / 18432000) * alpha * t ^ 25 + (5064927 / 80) * alpha * d * t ^ 3 + (-553901887 / 3200) * alpha * d * t ^ 5 + (29750962483 / 192000) * alpha * d * t ^ 7 + (-34192321897 / 768000) * alpha * d * t ^ 9 + (286387873 / 768000) * alpha * d * t ^ 11 + (-5961053597 / 9216000) * alpha * d * t ^ 13 + (-169833679 / 512000) * alpha * d * t ^ 15 + (-59875177 / 2048000) * alpha * d * t ^ 17 + (-3769931 / 115200) * alpha * d * t ^ 19 + (7360111 / 256000) * alpha * d * t ^ 21 + (821303 / 2048000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_03, v56_10, v56_11, v56_12, v56_13, v56_20, v56_21, v56_22, v56_23, v56_30, v56_31, v56_32, v56_33, v56_40, v56_41, v56_42, v56_43]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23, phase57_30, phase57_31, phase57_32, phase57_33, phase57_40, phase57_41, phase57_42, phase57_43]
  try simp only [star_one, star_neg]
  linear_combination ((1688309 / 80) * t ^ 3 + (-75130577 / 1600) * t ^ 5 + (18415724173 / 576000) * t ^ 7 + (-721291483 / 128000) * t ^ 9 + (143099801 / 460800) * t ^ 11 + (-25889992249 / 27648000) * t ^ 13 + (674835809 / 2764800) * t ^ 15 + (-577439863 / 18432000) * t ^ 17 + (-28124003 / 41472000) * t ^ 19 + (11159377 / 1152000) * t ^ 21 + (24802063 / 55296000) * t ^ 25 + (-15265 / 48) * d * t ^ 3 + (211777 / 600) * d * t ^ 5 + (1064472793 / 3456000) * d * t ^ 7 + (-5845635487 / 13824000) * d * t ^ 9 + (690005627 / 13824000) * d * t ^ 11 + (228857587 / 6912000) * d * t ^ 13 + (-15673873 / 3456000) * d * t ^ 15 + (32066011 / 33177600) * d * t ^ 17 + (-9595147 / 31104000) * d * t ^ 19 + (-30064459 / 165888000) * d * t ^ 21 + (135109 / 4976640) * d * t ^ 25 + (-185227 / 17280) * d ^ 2 * t ^ 7 + (265125053 / 13824000) * d ^ 2 * t ^ 9 + (-122281991 / 13824000) * d ^ 2 * t ^ 11 + (10905623 / 27648000) * d ^ 2 * t ^ 13 + (-3731759 / 41472000) * d ^ 2 * t ^ 15 + (-8357 / 552960) * d ^ 2 * t ^ 17 + (-10697 / 663552) * d ^ 2 * t ^ 19 + (46597 / 5184000) * d ^ 2 * t ^ 21) * alpha_sq + ((-9159 / 2) * t ^ 3 + (3115111 / 384) * t ^ 5 + (-4700842909 / 1152000) * t ^ 7 + (241417131 / 512000) * t ^ 9 + (-28408893 / 512000) * t ^ 11 + (196514023 / 9216000) * t ^ 13 + (59484757 / 13824000) * t ^ 15 + (8197 / 92160) * t ^ 17 + (-8741869 / 16588800) * t ^ 19 + (-360901 / 6912000) * t ^ 21 + (15265 / 48) * alpha * t ^ 3 + (-211777 / 600) * alpha * t ^ 5 + (-658960553 / 3456000) * alpha * t ^ 7 + (3248033189 / 13824000) * alpha * t ^ 9 + (225149159 / 13824000) * alpha * t ^ 11 + (-1102479359 / 41472000) * alpha * t ^ 13 + (5018801 / 1382400) * alpha * t ^ 15 + (-1798099 / 33177600) * alpha * t ^ 17 + (-292111 / 3888000) * alpha * t ^ 19 + (-39499 / 1327104) * alpha * t ^ 21 + (-4465 / 1990656) * alpha * t ^ 25) * d_sq
theorem v57_44 (t : ℂ) : (momentPoly 57 z57 4 4).eval t = (240274665 + (-771573432) * t ^ 2 + (175132575093 / 200) * t ^ 4 + (-15593336811507 / 40000) * t ^ 6 + (1773604924194419 / 32000000) * t ^ 8 + (-203396124893299 / 8000000) * t ^ 10 + (95476319399941 / 6400000) * t ^ 12 + (6465139324229 / 12000000) * t ^ 14 + (18850919286049 / 384000000) * t ^ 16 + (-635358682181 / 48000000) * t ^ 18 + (-2063437465183 / 2304000000) * t ^ 20 + (5303843502677 / 384000000) * t ^ 22 + (-7117757236847 / 1536000000) * t ^ 24 + (328059483973 / 1152000000) * t ^ 26 + (393775698511 / 4608000000) * t ^ 32 + (-4104114) * d * t ^ 2 + (467300253 / 40) * d * t ^ 4 + (-92711135037 / 8000) * d * t ^ 6 + (88948602053983 / 19200000) * d * t ^ 8 + (-7488675091039 / 9600000) * d * t ^ 10 + (2872796159063 / 19200000) * d * t ^ 12 + (214553940127 / 11520000) * d * t ^ 14 + (-1109067403189 / 76800000) * d * t ^ 16 + (6899429467 / 3200000) * d * t ^ 18 + (35090703473 / 51200000) * d * t ^ 20 + (-2879395869 / 25600000) * d * t ^ 22 + (-26513831 / 12288000) * d * t ^ 24 + (-4875316561 / 76800000) * d * t ^ 26 + (3295379 / 7372800) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z57, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v56_00, v56_01, v56_02, v56_03, v56_04, v56_10, v56_11, v56_12, v56_13, v56_14, v56_20, v56_21, v56_22, v56_23, v56_24, v56_30, v56_31, v56_32, v56_33, v56_34, v56_40, v56_41, v56_42, v56_43, v56_44]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24, phase57_30, phase57_31, phase57_32, phase57_33, phase57_34, phase57_40, phase57_41, phase57_42, phase57_43, phase57_44]
  try simp only [star_one, star_neg]
  linear_combination ((684019 / 3) * t ^ 2 + (-35960011 / 120) * t ^ 4 + (-40500581 / 200) * t ^ 6 + (472928264183 / 1152000) * t ^ 8 + (-1645638119677 / 11520000) * t ^ 10 + (64285646333 / 3840000) * t ^ 12 + (-1124112318199 / 207360000) * t ^ 14 + (-7171640683 / 1920000) * t ^ 16 + (117287509 / 540000) * t ^ 18 + (-6796078331 / 11520000) * t ^ 20 + (3181451203 / 69120000) * t ^ 22 + (-67524677 / 5184000) * t ^ 26 + (-10127807 / 360) * d * t ^ 4 + (1157779723 / 14400) * d * t ^ 6 + (-89811690749 / 1152000) * d * t ^ 8 + (188986796249 / 6912000) * d * t ^ 10 + (-16574574673 / 6912000) * d * t ^ 12 + (46746254791 / 41472000) * d * t ^ 14 + (-498684763 / 1152000) * d * t ^ 16 + (275656121 / 5184000) * d * t ^ 18 + (5026330069 / 497664000) * d * t ^ 20 + (-1017470833 / 82944000) * d * t ^ 22 + (-26513831 / 110592000) * d * t ^ 24 + (-7359593 / 9953280) * d * t ^ 26 + (3295379 / 66355200) * d * t ^ 32 + (-182075 / 1728) * d ^ 2 * t ^ 6 + (1552609 / 16200) * d ^ 2 * t ^ 8 + (115824877 / 1152000) * d ^ 2 * t ^ 10 + (-162722081 / 1728000) * d ^ 2 * t ^ 12 + (-62096591 / 10368000) * d ^ 2 * t ^ 14 + (192127739 / 20736000) * d ^ 2 * t ^ 16 + (-649697 / 518400) * d ^ 2 * t ^ 18 + (-3586801 / 19906560) * d ^ 2 * t ^ 20 + (17231431 / 82944000) * d ^ 2 * t ^ 22 + (115879 / 7962624) * d ^ 2 * t ^ 24 + (-1034797 / 29859840) * d ^ 2 * t ^ 26 + (9025 / 23887872) * d ^ 2 * t ^ 32) * alpha_sq + ((-684019 / 3) * t ^ 2 + (14445167 / 24) * t ^ 4 + (-8143797901 / 14400) * t ^ 6 + (785556713207 / 3456000) * t ^ 8 + (-19621578677 / 460800) * t ^ 10 + (74222821057 / 11520000) * t ^ 12 + (-6183180713 / 8294400) * t ^ 14 + (1210575001 / 2304000) * t ^ 16 + (-2367623 / 345600) * t ^ 18 + (1656792353 / 165888000) * t ^ 20 + (-170551963 / 46080000) * t ^ 22 + (-115879 / 2654208) * t ^ 24 + (-6820691 / 9953280) * t ^ 26 + (-9025 / 7962624) * t ^ 32) * d_sq
#print axioms v57_00
#print axioms v57_11
#print axioms v57_22
#print axioms v57_33
#print axioms v57_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v58_02 (t : ℂ) : (momentPoly 58 z58 0 2).eval t = ((-103 / 16) * t ^ 2 + (547 / 48) * t ^ 4 + (-1 / 6) * d * t ^ 2 + (533 / 120) * alpha * t ^ 2 + (-171 / 40) * alpha * t ^ 4 + (-1 / 48) * alpha * d * t ^ 2 + (1 / 144) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02]
  try simp only [phase57_00, phase57_01, phase57_02]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 96) * t ^ 2) * alpha_sq + ((-1 / 96) * t ^ 2) * d_sq
theorem v58_03 (t : ℂ) : (momentPoly 58 z58 0 3).eval t = ((-3283 / 160) * t ^ 3 + (5023 / 160) * t ^ 5 + 2 * t ^ 9 + (203 / 96) * d * t ^ 3 + (-167 / 64) * d * t ^ 5 + (-47 / 576) * d * t ^ 9 + (44701 / 2400) * alpha * t ^ 3 + (-32941 / 1600) * alpha * t ^ 5 + (46163 / 14400) * alpha * t ^ 9 + (-181 / 160) * alpha * d * t ^ 3 + (523 / 480) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_03]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03]
  try simp only [star_one, star_neg]
  linear_combination ((-181 / 320) * t ^ 3 + (171 / 320) * t ^ 5 + (1 / 192) * d * t ^ 3 + (-1 / 384) * d * t ^ 5) * alpha_sq + ((-1 / 32) * t ^ 3 + (-1 / 192) * alpha * t ^ 3 + (1 / 384) * alpha * t ^ 5) * d_sq
theorem v58_04 (t : ℂ) : (momentPoly 58 z58 0 4).eval t = ((-545509 / 4800) * t ^ 4 + (-9999 / 400) * t ^ 6 + (1226299 / 6400) * t ^ 8 + (-115021 / 4800) * t ^ 10 + (25541 / 2304) * t ^ 16 + (9019 / 960) * d * t ^ 4 + (-423 / 40) * d * t ^ 6 + (171 / 320) * d * t ^ 8 + (-143 / 144) * d * t ^ 10 + (-488801 / 3000) * alpha * t ^ 4 + (1870931 / 4000) * alpha * t ^ 6 + (-4850291 / 16000) * alpha * t ^ 8 + (-34693 / 36000) * alpha * t ^ 10 + (173441 / 48000) * alpha * t ^ 16 + (-1243 / 225) * alpha * d * t ^ 4 + (14483 / 2400) * alpha * d * t ^ 6 + (111 / 256) * alpha * d * t ^ 8 + (-16571 / 14400) * alpha * d * t ^ 10 + (95 / 6912) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_03, v57_04]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04]
  try simp only [star_one, star_neg]
  linear_combination ((-103427 / 28800) * t ^ 4 + (33841 / 9600) * t ^ 6 + (-17771 / 28800) * t ^ 10 + (553 / 1920) * d * t ^ 4 + (-11 / 30) * d * t ^ 6 + (57 / 640) * d * t ^ 8 + (1 / 1152) * d ^ 2 * t ^ 6 + (-1 / 4608) * d ^ 2 * t ^ 8) * alpha_sq + ((421 / 1152) * t ^ 4 + (-19 / 32) * t ^ 6 + (1 / 1536) * t ^ 8 + (-47 / 1152) * t ^ 10 + (-553 / 1920) * alpha * t ^ 4 + (533 / 1920) * alpha * t ^ 6) * d_sq
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
theorem v58_12 (t : ℂ) : (momentPoly 58 z58 1 2).eval t = (115 * t + (-17819 / 160) * t ^ 3 + (4477 / 480) * t ^ 5 + (-115 / 12) * d * t + (947 / 96) * d * t ^ 3 + (-83 / 96) * d * t ^ 5 + (115 / 12) * alpha * t + (-1693 / 480) * alpha * t ^ 3 + (-2707 / 480) * alpha * t ^ 5 + (-181 / 480) * alpha * d * t ^ 3 + (523 / 1440) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_10, v57_11, v57_12]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12]
  try simp only [star_one, star_neg]
  linear_combination ((181 / 960) * t ^ 3 + (-57 / 320) * t ^ 5 + (-1 / 576) * d * t ^ 3 + (1 / 1152) * d * t ^ 5) * alpha_sq + ((-1 / 32) * t ^ 3 + (-1 / 576) * alpha * t ^ 3 + (1 / 1152) * alpha * t ^ 5) * d_sq
theorem v58_13 (t : ℂ) : (momentPoly 58 z58 1 3).eval t = ((-17613 / 16) * t ^ 2 + (7019399 / 2400) * t ^ 4 + (-2845649 / 1600) * t ^ 6 + (-7517 / 1600) * t ^ 10 + (-57 / 2) * d * t ^ 2 + (757 / 24) * d * t ^ 4 + (-285 / 64) * d * t ^ 6 + (-143 / 576) * d * t ^ 10 + (30381 / 40) * alpha * t ^ 2 + (-562859 / 400) * alpha * t ^ 4 + (1027949 / 1600) * alpha * t ^ 6 + (105323 / 14400) * alpha * t ^ 10 + (-57 / 16) * alpha * d * t ^ 2 + (13211 / 7200) * alpha * d * t ^ 4 + (9109 / 4800) * alpha * d * t ^ 6 + (-1283 / 4800) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_03, v57_10, v57_11, v57_12, v57_13]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13]
  try simp only [star_one, star_neg]
  linear_combination ((-57 / 32) * t ^ 2 + (24499 / 14400) * t ^ 4 + (-181 / 2400) * t ^ 6 + (17771 / 115200) * t ^ 10) * alpha_sq + ((-57 / 32) * t ^ 2 + (523 / 288) * t ^ 4 + (-113 / 384) * t ^ 6 + (-47 / 4608) * t ^ 10 + (-553 / 3840) * alpha * t ^ 4 + (533 / 3840) * alpha * t ^ 6) * d_sq
theorem v58_14 (t : ℂ) : (momentPoly 58 z58 1 4).eval t = ((-370979 / 80) * t ^ 3 + (353535629 / 32000) * t ^ 5 + (-100995129 / 16000) * t ^ 7 + (31073249 / 64000) * t ^ 9 + (-7594297 / 16000) * t ^ 11 + (5753573 / 576000) * t ^ 17 + (22939 / 48) * d * t ^ 3 + (-19985701 / 19200) * d * t ^ 5 + (5422361 / 9600) * d * t ^ 7 + (-3316801 / 115200) * d * t ^ 9 + (8755 / 384) * d * t ^ 11 + (-3865 / 4608) * d * t ^ 17 + (5051213 / 1200) * alpha * t ^ 3 + (-832092437 / 96000) * alpha * t ^ 5 + (224719297 / 48000) * alpha * t ^ 7 + (250837319 / 576000) * alpha * t ^ 9 + (-93237287 / 144000) * alpha * t ^ 11 + (-675353 / 576000) * alpha * t ^ 17 + (-20453 / 80) * alpha * d * t ^ 3 + (48369031 / 96000) * alpha * d * t ^ 5 + (-4309457 / 16000) * alpha * d * t ^ 7 + (1502197 / 64000) * alpha * d * t ^ 9 + (-117143 / 48000) * alpha * d * t ^ 11 + (-496573 / 1728000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_03, v57_04, v57_10, v57_11, v57_12, v57_13, v57_14]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14]
  try simp only [star_one, star_neg]
  linear_combination ((-20453 / 160) * t ^ 3 + (42559859 / 192000) * t ^ 5 + (-31421311 / 384000) * t ^ 7 + (-2222083 / 192000) * t ^ 9 + (-354641 / 288000) * t ^ 11 + (173441 / 1152000) * t ^ 17 + (113 / 96) * d * t ^ 3 + (-30409 / 23040) * d * t ^ 5 + (1 / 720) * d * t ^ 7 + (7319 / 46080) * d * t ^ 9 + (-47 / 6912) * d * t ^ 11 + (95 / 55296) * d * t ^ 17 + (553 / 46080) * d ^ 2 * t ^ 7 + (-523 / 46080) * d ^ 2 * t ^ 9) * alpha_sq + ((-113 / 16) * t ^ 3 + (88469 / 11520) * t ^ 5 + (-12739 / 7680) * t ^ 7 + (259 / 3840) * t ^ 9 + (-95 / 576) * t ^ 11 + (-113 / 96) * alpha * t ^ 3 + (22681 / 38400) * alpha * t ^ 5 + (551 / 900) * alpha * t ^ 7 + (451 / 9216) * alpha * t ^ 9 + (-24869 / 172800) * alpha * t ^ 11 + (95 / 55296) * alpha * t ^ 17) * d_sq
theorem v58_20 (t : ℂ) : (momentPoly 58 z58 2 0).eval t = ((-103 / 16) * t ^ 2 + (547 / 48) * t ^ 4 + (-1 / 6) * d * t ^ 2 + (-533 / 120) * alpha * t ^ 2 + (171 / 40) * alpha * t ^ 4 + (1 / 48) * alpha * d * t ^ 2 + (-1 / 144) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_10, v57_20]
  try simp only [phase57_00, phase57_10, phase57_20]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 96) * t ^ 2) * alpha_sq + ((-1 / 96) * t ^ 2) * d_sq
theorem v58_21 (t : ℂ) : (momentPoly 58 z58 2 1).eval t = (115 * t + (-17819 / 160) * t ^ 3 + (4477 / 480) * t ^ 5 + (-115 / 12) * d * t + (947 / 96) * d * t ^ 3 + (-83 / 96) * d * t ^ 5 + (-115 / 12) * alpha * t + (1693 / 480) * alpha * t ^ 3 + (2707 / 480) * alpha * t ^ 5 + (181 / 480) * alpha * d * t ^ 3 + (-523 / 1440) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_10, v57_11, v57_20, v57_21]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21]
  try simp only [star_one, star_neg]
  linear_combination ((181 / 960) * t ^ 3 + (-57 / 320) * t ^ 5 + (-1 / 576) * d * t ^ 3 + (1 / 1152) * d * t ^ 5) * alpha_sq + ((-1 / 32) * t ^ 3 + (1 / 576) * alpha * t ^ 3 + (-1 / 1152) * alpha * t ^ 5) * d_sq
theorem v58_22 (t : ℂ) : (momentPoly 58 z58 2 2).eval t = (6670 + (-12084) * t ^ 2 + (8603663 / 1600) * t ^ 4 + (-19659 / 400) * t ^ 6 + (608519 / 4800) * t ^ 8 + (-38) * d * t ^ 2 + (37367 / 960) * d * t ^ 4 + (-193 / 80) * d * t ^ 6 + (-57 / 320) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_10, v57_11, v57_12, v57_20, v57_21, v57_22]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22]
  try simp only [star_one, star_neg]
  linear_combination ((19 / 8) * t ^ 2 + (-2057 / 1920) * t ^ 4 + (-2063 / 1920) * t ^ 6 + (-553 / 5760) * d * t ^ 4 + (11 / 90) * d * t ^ 6 + (-19 / 640) * d * t ^ 8 + (-1 / 3456) * d ^ 2 * t ^ 6 + (1 / 13824) * d ^ 2 * t ^ 8) * alpha_sq + ((-19 / 8) * t ^ 2 + (883 / 384) * t ^ 4 + (-7 / 36) * t ^ 6 + (-1 / 4608) * t ^ 8) * d_sq
theorem v58_23 (t : ℂ) : (momentPoly 58 z58 2 3).eval t = (19666 * t + (-6040641 / 160) * t ^ 3 + (1007955179 / 48000) * t ^ 5 + (-123880097 / 38400) * t ^ 7 + (27892883 / 64000) * t ^ 9 + (1214731 / 64000) * t ^ 11 + (-3709873 / 192000) * t ^ 13 + (-9833 / 6) * d * t + (107011 / 32) * d * t ^ 3 + (-1584453 / 800) * d * t ^ 5 + (3796269 / 12800) * d * t ^ 7 + (-349377 / 12800) * d * t ^ 9 + (66077 / 38400) * d * t ^ 11 + (-89827 / 115200) * d * t ^ 13 + (9833 / 6) * alpha * t + (-191309 / 160) * alpha * t ^ 3 + (-720207 / 320) * alpha * t ^ 5 + (14378149 / 7680) * alpha * t ^ 7 + (-1118191 / 12800) * alpha * t ^ 9 + (-737869 / 38400) * alpha * t ^ 11 + (5221291 / 115200) * alpha * t ^ 13 + (-20453 / 160) * alpha * d * t ^ 3 + (6988183 / 28800) * alpha * d * t ^ 5 + (-13096813 / 115200) * alpha * d * t ^ 7 + (-353 / 7680) * alpha * d * t ^ 9 + (-32893 / 38400) * alpha * d * t ^ 11 + (-8357 / 23040) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_03, v57_10, v57_11, v57_12, v57_13, v57_20, v57_21, v57_22, v57_23]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23]
  try simp only [star_one, star_neg]
  linear_combination ((20453 / 320) * t ^ 3 + (-3191159 / 28800) * t ^ 5 + (450127 / 9600) * t ^ 7 + (270629 / 230400) * t ^ 11 + (-2717 / 5120) * t ^ 13 + (-113 / 192) * d * t ^ 3 + (27511 / 57600) * d * t ^ 5 + (183793 / 691200) * d * t ^ 7 + (-32393 / 230400) * d * t ^ 9 + (-27269 / 691200) * d * t ^ 11 + (17771 / 1382400) * d * t ^ 13 + (-553 / 46080) * d ^ 2 * t ^ 7 + (523 / 46080) * d ^ 2 * t ^ 9) * alpha_sq + ((-339 / 32) * t ^ 3 + (119531 / 11520) * t ^ 5 + (-2087 / 2560) * t ^ 7 + (-259 / 3840) * t ^ 9 + (-95 / 2304) * t ^ 11 + (-113 / 192) * alpha * t ^ 3 + (27511 / 57600) * alpha * t ^ 5 + (84287 / 691200) * alpha * t ^ 7 + (-1 / 9216) * alpha * t ^ 9 + (-22519 / 691200) * alpha * t ^ 11 + (-47 / 55296) * alpha * t ^ 13) * d_sq
theorem v58_24 (t : ℂ) : (momentPoly 58 z58 2 4).eval t = ((-1990475 / 8) * t ^ 2 + (1053338101 / 1200) * t ^ 4 + (-1886340731053 / 1920000) * t ^ 6 + (222195609703 / 640000) * t ^ 8 + (1054460551 / 384000) * t ^ 10 + (985832329 / 240000) * t ^ 12 + (-165535483 / 720000) * t ^ 14 + (-13738511 / 960000) * t ^ 18 + (396031801 / 5760000) * t ^ 20 + (-19325 / 3) * d * t ^ 2 + (42392 / 3) * d * t ^ 4 + (-1225963847 / 128000) * d * t ^ 6 + (759032333 / 384000) * d * t ^ 8 + (-25217011 / 115200) * d * t ^ 10 + (14390199 / 128000) * d * t ^ 12 + (1463471 / 288000) * d * t ^ 14 + (-1605599 / 1152000) * d * t ^ 18 + (-58171 / 576000) * d * t ^ 20 + (2060045 / 12) * alpha * t ^ 2 + (-93630601 / 200) * alpha * t ^ 4 + (53479231209 / 128000) * alpha * t ^ 6 + (-46133356067 / 384000) * alpha * t ^ 8 + (3447493477 / 1152000) * alpha * t ^ 10 + (-576777397 / 144000) * alpha * t ^ 12 + (-4507033 / 28800) * alpha * t ^ 14 + (-50941351 / 576000) * alpha * t ^ 18 + (106954801 / 1152000) * alpha * t ^ 20 + (-19325 / 24) * alpha * d * t ^ 2 + (2010439 / 3600) * alpha * d * t ^ 4 + (1575010849 / 1152000) * alpha * d * t ^ 6 + (-1354285753 / 1152000) * alpha * d * t ^ 8 + (-32441219 / 576000) * alpha * d * t ^ 10 + (145750691 / 1152000) * alpha * d * t ^ 12 + (-2771767 / 172800) * alpha * d * t ^ 14 + (86201 / 1152000) * alpha * d * t ^ 18 + (335 / 4608) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_03, v57_04, v57_10, v57_11, v57_12, v57_13, v57_14, v57_20, v57_21, v57_22, v57_23, v57_24]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24]
  try simp only [star_one, star_neg]
  linear_combination ((-19325 / 48) * t ^ 2 + (171493 / 225) * t ^ 4 + (-874542659 / 2304000) * t ^ 6 + (31330099 / 1152000) * t ^ 8 + (265367231 / 4608000) * t ^ 10 + (-29990279 / 576000) * t ^ 12 + (-134429 / 12800) * t ^ 14 + (-314759 / 1536000) * t ^ 18 + (404337 / 256000) * d * t ^ 6 + (-29434241 / 6912000) * d * t ^ 8 + (1058267 / 288000) * d * t ^ 10 + (-3114371 / 2304000) * d * t ^ 12 + (11543 / 32000) * d * t ^ 14 + (-33349 / 6912000) * d * t ^ 18 + (-58171 / 3456000) * d * t ^ 20 + (-42001 / 1382400) * d ^ 2 * t ^ 8 + (88373 / 2764800) * d ^ 2 * t ^ 10 + (113 / 55296) * d ^ 2 * t ^ 12 + (-6511 / 1036800) * d ^ 2 * t ^ 14 + (-95 / 331776) * d ^ 2 * t ^ 18 + (95 / 663552) * d ^ 2 * t ^ 20) * alpha_sq + ((-19325 / 48) * t ^ 2 + (7322 / 9) * t ^ 4 + (-245312111 / 460800) * t ^ 6 + (55833887 / 460800) * t ^ 8 + (-340007 / 30720) * t ^ 10 + (2311883 / 460800) * t ^ 12 + (-119753 / 345600) * t ^ 14 + (-2593 / 27648) * t ^ 18 + (-95 / 221184) * t ^ 20 + (-3871 / 60) * alpha * t ^ 4 + (93289451 / 768000) * alpha * t ^ 6 + (-102210037 / 1728000) * alpha * t ^ 8 + (763553 / 288000) * alpha * t ^ 10 + (-5905543 / 13824000) * alpha * t ^ 12 + (-25541 / 138240) * alpha * t ^ 14 + (-472823 / 13824000) * alpha * t ^ 18) * d_sq
theorem v58_30 (t : ℂ) : (momentPoly 58 z58 3 0).eval t = ((-3283 / 160) * t ^ 3 + (5023 / 160) * t ^ 5 + 2 * t ^ 9 + (203 / 96) * d * t ^ 3 + (-167 / 64) * d * t ^ 5 + (-47 / 576) * d * t ^ 9 + (-44701 / 2400) * alpha * t ^ 3 + (32941 / 1600) * alpha * t ^ 5 + (-46163 / 14400) * alpha * t ^ 9 + (181 / 160) * alpha * d * t ^ 3 + (-523 / 480) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_10, v57_20, v57_30]
  try simp only [phase57_00, phase57_10, phase57_20, phase57_30]
  try simp only [star_one, star_neg]
  linear_combination ((-181 / 320) * t ^ 3 + (171 / 320) * t ^ 5 + (1 / 192) * d * t ^ 3 + (-1 / 384) * d * t ^ 5) * alpha_sq + ((-1 / 32) * t ^ 3 + (1 / 192) * alpha * t ^ 3 + (-1 / 384) * alpha * t ^ 5) * d_sq
theorem v58_31 (t : ℂ) : (momentPoly 58 z58 3 1).eval t = ((-17613 / 16) * t ^ 2 + (7019399 / 2400) * t ^ 4 + (-2845649 / 1600) * t ^ 6 + (-7517 / 1600) * t ^ 10 + (-57 / 2) * d * t ^ 2 + (757 / 24) * d * t ^ 4 + (-285 / 64) * d * t ^ 6 + (-143 / 576) * d * t ^ 10 + (-30381 / 40) * alpha * t ^ 2 + (562859 / 400) * alpha * t ^ 4 + (-1027949 / 1600) * alpha * t ^ 6 + (-105323 / 14400) * alpha * t ^ 10 + (57 / 16) * alpha * d * t ^ 2 + (-13211 / 7200) * alpha * d * t ^ 4 + (-9109 / 4800) * alpha * d * t ^ 6 + (1283 / 4800) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_10, v57_11, v57_20, v57_21, v57_30, v57_31]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21, phase57_30, phase57_31]
  try simp only [star_one, star_neg]
  linear_combination ((-57 / 32) * t ^ 2 + (24499 / 14400) * t ^ 4 + (-181 / 2400) * t ^ 6 + (17771 / 115200) * t ^ 10) * alpha_sq + ((-57 / 32) * t ^ 2 + (523 / 288) * t ^ 4 + (-113 / 384) * t ^ 6 + (-47 / 4608) * t ^ 10 + (553 / 3840) * alpha * t ^ 4 + (-533 / 3840) * alpha * t ^ 6) * d_sq
theorem v58_32 (t : ℂ) : (momentPoly 58 z58 3 2).eval t = (19666 * t + (-6040641 / 160) * t ^ 3 + (1007955179 / 48000) * t ^ 5 + (-123880097 / 38400) * t ^ 7 + (27892883 / 64000) * t ^ 9 + (1214731 / 64000) * t ^ 11 + (-3709873 / 192000) * t ^ 13 + (-9833 / 6) * d * t + (107011 / 32) * d * t ^ 3 + (-1584453 / 800) * d * t ^ 5 + (3796269 / 12800) * d * t ^ 7 + (-349377 / 12800) * d * t ^ 9 + (66077 / 38400) * d * t ^ 11 + (-89827 / 115200) * d * t ^ 13 + (-9833 / 6) * alpha * t + (191309 / 160) * alpha * t ^ 3 + (720207 / 320) * alpha * t ^ 5 + (-14378149 / 7680) * alpha * t ^ 7 + (1118191 / 12800) * alpha * t ^ 9 + (737869 / 38400) * alpha * t ^ 11 + (-5221291 / 115200) * alpha * t ^ 13 + (20453 / 160) * alpha * d * t ^ 3 + (-6988183 / 28800) * alpha * d * t ^ 5 + (13096813 / 115200) * alpha * d * t ^ 7 + (353 / 7680) * alpha * d * t ^ 9 + (32893 / 38400) * alpha * d * t ^ 11 + (8357 / 23040) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_10, v57_11, v57_12, v57_20, v57_21, v57_22, v57_30, v57_31, v57_32]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22, phase57_30, phase57_31, phase57_32]
  try simp only [star_one, star_neg]
  linear_combination ((20453 / 320) * t ^ 3 + (-3191159 / 28800) * t ^ 5 + (450127 / 9600) * t ^ 7 + (270629 / 230400) * t ^ 11 + (-2717 / 5120) * t ^ 13 + (-113 / 192) * d * t ^ 3 + (27511 / 57600) * d * t ^ 5 + (183793 / 691200) * d * t ^ 7 + (-32393 / 230400) * d * t ^ 9 + (-27269 / 691200) * d * t ^ 11 + (17771 / 1382400) * d * t ^ 13 + (-553 / 46080) * d ^ 2 * t ^ 7 + (523 / 46080) * d ^ 2 * t ^ 9) * alpha_sq + ((-339 / 32) * t ^ 3 + (119531 / 11520) * t ^ 5 + (-2087 / 2560) * t ^ 7 + (-259 / 3840) * t ^ 9 + (-95 / 2304) * t ^ 11 + (113 / 192) * alpha * t ^ 3 + (-27511 / 57600) * alpha * t ^ 5 + (-84287 / 691200) * alpha * t ^ 7 + (1 / 9216) * alpha * t ^ 9 + (22519 / 691200) * alpha * t ^ 11 + (47 / 55296) * alpha * t ^ 13) * d_sq
theorem v58_33 (t : ℂ) : (momentPoly 58 z58 3 3).eval t = (1140628 + (-3072675) * t ^ 2 + (542030769 / 200) * t ^ 4 + (-64364214651 / 80000) * t ^ 6 + (13582379621 / 160000) * t ^ 8 + (-18501676929 / 320000) * t ^ 10 + (108424349 / 480000) * t ^ 12 + (-37525921 / 80000) * t ^ 14 + (-18579973 / 960000) * t ^ 18 + (-19325 / 2) * d * t ^ 2 + (784707 / 40) * d * t ^ 4 + (-533442167 / 48000) * d * t ^ 6 + (3968223 / 3200) * d * t ^ 8 + (-202887 / 2000) * d * t ^ 10 + (-390923 / 144000) * d * t ^ 12 + (358351 / 48000) * d * t ^ 14 + (-47 / 144) * d * t ^ 18) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_03, v57_10, v57_11, v57_12, v57_13, v57_20, v57_21, v57_22, v57_23, v57_30, v57_31, v57_32, v57_33]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23, phase57_30, phase57_31, phase57_32, phase57_33]
  try simp only [star_one, star_neg]
  linear_combination ((19325 / 32) * t ^ 2 + (-43197 / 80) * t ^ 4 + (-13425281 / 25600) * t ^ 6 + (36325061 / 76800) * t ^ 8 + (-924383 / 51200) * t ^ 10 + (111533 / 21600) * t ^ 12 + (2626967 / 460800) * t ^ 14 + (4571281 / 5529600) * t ^ 18 + (-3871 / 80) * d * t ^ 4 + (2687231 / 25600) * d * t ^ 6 + (-7834067 / 115200) * d * t ^ 8 + (898289 / 76800) * d * t ^ 10 + (-86429 / 115200) * d * t ^ 12 + (97451 / 230400) * d * t ^ 14 + (-169 / 1152) * d ^ 2 * t ^ 6 + (18961 / 230400) * d ^ 2 * t ^ 8 + (3303 / 51200) * d ^ 2 * t ^ 10 + (-3949 / 460800) * d ^ 2 * t ^ 14) * alpha_sq + ((-19325 / 32) * t ^ 2 + (18543 / 16) * t ^ 4 + (-49549297 / 76800) * t ^ 6 + (589297 / 6400) * t ^ 8 + (-3479 / 400) * t ^ 10 + (190459 / 345600) * t ^ 12 + (-3779 / 7200) * t ^ 14 + (-2209 / 221184) * t ^ 18) * d_sq
theorem v58_34 (t : ℂ) : (momentPoly 58 z58 3 4).eval t = (4445203 * t + (-1014988059 / 80) * t ^ 3 + (103538120719 / 8000) * t ^ 5 + (-18510638313443 / 3200000) * t ^ 7 + (17232645664427 / 12800000) * t ^ 9 + (-1650156532221 / 6400000) * t ^ 11 + (-73369741297 / 5120000) * t ^ 13 + (134959843633 / 9600000) * t ^ 15 + (-200689561183 / 76800000) * t ^ 17 + (-1732491331 / 6400000) * t ^ 19 + (4622522969 / 25600000) * t ^ 21 + (12884356883 / 230400000) * t ^ 25 + (-4445203 / 12) * d * t + (17980689 / 16) * d * t ^ 3 + (-977891773 / 800) * d * t ^ 5 + (72582867127 / 128000) * d * t ^ 7 + (-34975108843 / 307200) * d * t ^ 9 + (8253494347 / 480000) * d * t ^ 11 + (-4029211799 / 1843200) * d * t ^ 13 + (431838179 / 576000) * d * t ^ 15 + (-9600367 / 1843200) * d * t ^ 17 + (61534253 / 3456000) * d * t ^ 19 + (-200156039 / 15360000) * d * t ^ 21 + (-762013 / 1105920) * d * t ^ 25 + (4445203 / 12) * alpha * t + (-32144991 / 80) * alpha * t ^ 3 + (-69457339 / 80) * alpha * t ^ 5 + (955850612157 / 640000) * alpha * t ^ 7 + (-4909460936071 / 7680000) * alpha * t ^ 9 + (12186287921 / 384000) * alpha * t ^ 11 + (1928089174273 / 46080000) * alpha * t ^ 13 + (-38741007331 / 1440000) * alpha * t ^ 15 + (-55617433591 / 46080000) * alpha * t ^ 17 + (-150073333 / 540000) * alpha * t ^ 19 + (1034568387 / 5120000) * alpha * t ^ 21 + (-802807933 / 27648000) * alpha * t ^ 25 + (-3436647 / 80) * alpha * d * t ^ 3 + (580719143 / 4800) * alpha * d * t ^ 5 + (-128957062877 / 1152000) * alpha * d * t ^ 7 + (17227000579 / 512000) * alpha * d * t ^ 9 + (-387569023 / 768000) * alpha * d * t ^ 11 + (4716764347 / 9216000) * alpha * d * t ^ 13 + (54530671 / 230400) * alpha * d * t ^ 15 + (200084731 / 9216000) * alpha * d * t ^ 17 + (171973619 / 6912000) * alpha * d * t ^ 19 + (-194246791 / 9216000) * alpha * d * t ^ 21 + (-821303 / 3072000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_03, v57_04, v57_10, v57_11, v57_12, v57_13, v57_14, v57_20, v57_21, v57_22, v57_23, v57_24, v57_30, v57_31, v57_32, v57_33, v57_34]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24, phase57_30, phase57_31, phase57_32, phase57_33, phase57_34]
  try simp only [star_one, star_neg]
  linear_combination ((3436647 / 160) * t ^ 3 + (-43099669 / 800) * t ^ 5 + (16694325263 / 384000) * t ^ 7 + (-22071334103 / 2048000) * t ^ 9 + (549102359 / 1024000) * t ^ 11 + (-121094833127 / 110592000) * t ^ 13 + (632161449 / 2048000) * t ^ 15 + (-317757869 / 9216000) * t ^ 17 + (-166864171 / 36864000) * t ^ 19 + (21803313 / 2048000) * t ^ 21 + (24802063 / 55296000) * t ^ 25 + (-6329 / 32) * d * t ^ 3 + (1060873 / 4800) * d * t ^ 5 + (416154253 / 1728000) * d * t ^ 7 + (-1080439043 / 3072000) * d * t ^ 9 + (306634141 / 4608000) * d * t ^ 11 + (54688969 / 2048000) * d * t ^ 13 + (-88183387 / 13824000) * d * t ^ 15 + (10901147 / 11059200) * d * t ^ 17 + (-19848719 / 82944000) * d * t ^ 19 + (-8771903 / 55296000) * d * t ^ 21 + (337649 / 13271040) * d * t ^ 25 + (-37051 / 4608) * d ^ 2 * t ^ 7 + (92248651 / 6144000) * d ^ 2 * t ^ 9 + (-66885083 / 9216000) * d ^ 2 * t ^ 11 + (12186223 / 36864000) * d ^ 2 * t ^ 13 + (-3660259 / 55296000) * d ^ 2 * t ^ 15 + (-8357 / 737280) * d ^ 2 * t ^ 17 + (-10507 / 884736) * d ^ 2 * t ^ 19 + (46597 / 6912000) * d ^ 2 * t ^ 21) * alpha_sq + ((-56961 / 16) * t ^ 3 + (4422647 / 640) * t ^ 5 + (-1108677353 / 288000) * t ^ 7 + (299650037 / 614400) * t ^ 9 + (-34200217 / 768000) * t ^ 11 + (1239417943 / 55296000) * t ^ 13 + (20753941 / 9216000) * t ^ 15 + (8197 / 122880) * t ^ 17 + (-22801813 / 55296000) * t ^ 19 + (-360901 / 9216000) * t ^ 21 + (-6329 / 32) * alpha * t ^ 3 + (1060873 / 4800) * alpha * t ^ 5 + (249481703 / 1728000) * alpha * t ^ 7 + (-540912239 / 3072000) * alpha * t ^ 9 + (-52071911 / 4608000) * alpha * t ^ 11 + (1209807059 / 55296000) * alpha * t ^ 13 + (-7642631 / 2764800) * alpha * t ^ 15 + (506231 / 11059200) * alpha * t ^ 17 + (1629901 / 82944000) * alpha * t ^ 19 + (11003 / 442368) * alpha * t ^ 21 + (4465 / 2654208) * alpha * t ^ 25) * d_sq
theorem v58_40 (t : ℂ) : (momentPoly 58 z58 4 0).eval t = ((-545509 / 4800) * t ^ 4 + (-9999 / 400) * t ^ 6 + (1226299 / 6400) * t ^ 8 + (-115021 / 4800) * t ^ 10 + (25541 / 2304) * t ^ 16 + (9019 / 960) * d * t ^ 4 + (-423 / 40) * d * t ^ 6 + (171 / 320) * d * t ^ 8 + (-143 / 144) * d * t ^ 10 + (488801 / 3000) * alpha * t ^ 4 + (-1870931 / 4000) * alpha * t ^ 6 + (4850291 / 16000) * alpha * t ^ 8 + (34693 / 36000) * alpha * t ^ 10 + (-173441 / 48000) * alpha * t ^ 16 + (1243 / 225) * alpha * d * t ^ 4 + (-14483 / 2400) * alpha * d * t ^ 6 + (-111 / 256) * alpha * d * t ^ 8 + (16571 / 14400) * alpha * d * t ^ 10 + (-95 / 6912) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_10, v57_20, v57_30, v57_40]
  try simp only [phase57_00, phase57_10, phase57_20, phase57_30, phase57_40]
  try simp only [star_one, star_neg]
  linear_combination ((-103427 / 28800) * t ^ 4 + (33841 / 9600) * t ^ 6 + (-17771 / 28800) * t ^ 10 + (553 / 1920) * d * t ^ 4 + (-11 / 30) * d * t ^ 6 + (57 / 640) * d * t ^ 8 + (1 / 1152) * d ^ 2 * t ^ 6 + (-1 / 4608) * d ^ 2 * t ^ 8) * alpha_sq + ((421 / 1152) * t ^ 4 + (-19 / 32) * t ^ 6 + (1 / 1536) * t ^ 8 + (-47 / 1152) * t ^ 10 + (553 / 1920) * alpha * t ^ 4 + (-533 / 1920) * alpha * t ^ 6) * d_sq
theorem v58_41 (t : ℂ) : (momentPoly 58 z58 4 1).eval t = ((-370979 / 80) * t ^ 3 + (353535629 / 32000) * t ^ 5 + (-100995129 / 16000) * t ^ 7 + (31073249 / 64000) * t ^ 9 + (-7594297 / 16000) * t ^ 11 + (5753573 / 576000) * t ^ 17 + (22939 / 48) * d * t ^ 3 + (-19985701 / 19200) * d * t ^ 5 + (5422361 / 9600) * d * t ^ 7 + (-3316801 / 115200) * d * t ^ 9 + (8755 / 384) * d * t ^ 11 + (-3865 / 4608) * d * t ^ 17 + (-5051213 / 1200) * alpha * t ^ 3 + (832092437 / 96000) * alpha * t ^ 5 + (-224719297 / 48000) * alpha * t ^ 7 + (-250837319 / 576000) * alpha * t ^ 9 + (93237287 / 144000) * alpha * t ^ 11 + (675353 / 576000) * alpha * t ^ 17 + (20453 / 80) * alpha * d * t ^ 3 + (-48369031 / 96000) * alpha * d * t ^ 5 + (4309457 / 16000) * alpha * d * t ^ 7 + (-1502197 / 64000) * alpha * d * t ^ 9 + (117143 / 48000) * alpha * d * t ^ 11 + (496573 / 1728000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_10, v57_11, v57_20, v57_21, v57_30, v57_31, v57_40, v57_41]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21, phase57_30, phase57_31, phase57_40, phase57_41]
  try simp only [star_one, star_neg]
  linear_combination ((-20453 / 160) * t ^ 3 + (42559859 / 192000) * t ^ 5 + (-31421311 / 384000) * t ^ 7 + (-2222083 / 192000) * t ^ 9 + (-354641 / 288000) * t ^ 11 + (173441 / 1152000) * t ^ 17 + (113 / 96) * d * t ^ 3 + (-30409 / 23040) * d * t ^ 5 + (1 / 720) * d * t ^ 7 + (7319 / 46080) * d * t ^ 9 + (-47 / 6912) * d * t ^ 11 + (95 / 55296) * d * t ^ 17 + (553 / 46080) * d ^ 2 * t ^ 7 + (-523 / 46080) * d ^ 2 * t ^ 9) * alpha_sq + ((-113 / 16) * t ^ 3 + (88469 / 11520) * t ^ 5 + (-12739 / 7680) * t ^ 7 + (259 / 3840) * t ^ 9 + (-95 / 576) * t ^ 11 + (113 / 96) * alpha * t ^ 3 + (-22681 / 38400) * alpha * t ^ 5 + (-551 / 900) * alpha * t ^ 7 + (-451 / 9216) * alpha * t ^ 9 + (24869 / 172800) * alpha * t ^ 11 + (-95 / 55296) * alpha * t ^ 17) * d_sq
theorem v58_42 (t : ℂ) : (momentPoly 58 z58 4 2).eval t = ((-1990475 / 8) * t ^ 2 + (1053338101 / 1200) * t ^ 4 + (-1886340731053 / 1920000) * t ^ 6 + (222195609703 / 640000) * t ^ 8 + (1054460551 / 384000) * t ^ 10 + (985832329 / 240000) * t ^ 12 + (-165535483 / 720000) * t ^ 14 + (-13738511 / 960000) * t ^ 18 + (396031801 / 5760000) * t ^ 20 + (-19325 / 3) * d * t ^ 2 + (42392 / 3) * d * t ^ 4 + (-1225963847 / 128000) * d * t ^ 6 + (759032333 / 384000) * d * t ^ 8 + (-25217011 / 115200) * d * t ^ 10 + (14390199 / 128000) * d * t ^ 12 + (1463471 / 288000) * d * t ^ 14 + (-1605599 / 1152000) * d * t ^ 18 + (-58171 / 576000) * d * t ^ 20 + (-2060045 / 12) * alpha * t ^ 2 + (93630601 / 200) * alpha * t ^ 4 + (-53479231209 / 128000) * alpha * t ^ 6 + (46133356067 / 384000) * alpha * t ^ 8 + (-3447493477 / 1152000) * alpha * t ^ 10 + (576777397 / 144000) * alpha * t ^ 12 + (4507033 / 28800) * alpha * t ^ 14 + (50941351 / 576000) * alpha * t ^ 18 + (-106954801 / 1152000) * alpha * t ^ 20 + (19325 / 24) * alpha * d * t ^ 2 + (-2010439 / 3600) * alpha * d * t ^ 4 + (-1575010849 / 1152000) * alpha * d * t ^ 6 + (1354285753 / 1152000) * alpha * d * t ^ 8 + (32441219 / 576000) * alpha * d * t ^ 10 + (-145750691 / 1152000) * alpha * d * t ^ 12 + (2771767 / 172800) * alpha * d * t ^ 14 + (-86201 / 1152000) * alpha * d * t ^ 18 + (-335 / 4608) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_10, v57_11, v57_12, v57_20, v57_21, v57_22, v57_30, v57_31, v57_32, v57_40, v57_41, v57_42]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22, phase57_30, phase57_31, phase57_32, phase57_40, phase57_41, phase57_42]
  try simp only [star_one, star_neg]
  linear_combination ((-19325 / 48) * t ^ 2 + (171493 / 225) * t ^ 4 + (-874542659 / 2304000) * t ^ 6 + (31330099 / 1152000) * t ^ 8 + (265367231 / 4608000) * t ^ 10 + (-29990279 / 576000) * t ^ 12 + (-134429 / 12800) * t ^ 14 + (-314759 / 1536000) * t ^ 18 + (404337 / 256000) * d * t ^ 6 + (-29434241 / 6912000) * d * t ^ 8 + (1058267 / 288000) * d * t ^ 10 + (-3114371 / 2304000) * d * t ^ 12 + (11543 / 32000) * d * t ^ 14 + (-33349 / 6912000) * d * t ^ 18 + (-58171 / 3456000) * d * t ^ 20 + (-42001 / 1382400) * d ^ 2 * t ^ 8 + (88373 / 2764800) * d ^ 2 * t ^ 10 + (113 / 55296) * d ^ 2 * t ^ 12 + (-6511 / 1036800) * d ^ 2 * t ^ 14 + (-95 / 331776) * d ^ 2 * t ^ 18 + (95 / 663552) * d ^ 2 * t ^ 20) * alpha_sq + ((-19325 / 48) * t ^ 2 + (7322 / 9) * t ^ 4 + (-245312111 / 460800) * t ^ 6 + (55833887 / 460800) * t ^ 8 + (-340007 / 30720) * t ^ 10 + (2311883 / 460800) * t ^ 12 + (-119753 / 345600) * t ^ 14 + (-2593 / 27648) * t ^ 18 + (-95 / 221184) * t ^ 20 + (3871 / 60) * alpha * t ^ 4 + (-93289451 / 768000) * alpha * t ^ 6 + (102210037 / 1728000) * alpha * t ^ 8 + (-763553 / 288000) * alpha * t ^ 10 + (5905543 / 13824000) * alpha * t ^ 12 + (25541 / 138240) * alpha * t ^ 14 + (472823 / 13824000) * alpha * t ^ 18) * d_sq
theorem v58_43 (t : ℂ) : (momentPoly 58 z58 4 3).eval t = (4445203 * t + (-1014988059 / 80) * t ^ 3 + (103538120719 / 8000) * t ^ 5 + (-18510638313443 / 3200000) * t ^ 7 + (17232645664427 / 12800000) * t ^ 9 + (-1650156532221 / 6400000) * t ^ 11 + (-73369741297 / 5120000) * t ^ 13 + (134959843633 / 9600000) * t ^ 15 + (-200689561183 / 76800000) * t ^ 17 + (-1732491331 / 6400000) * t ^ 19 + (4622522969 / 25600000) * t ^ 21 + (12884356883 / 230400000) * t ^ 25 + (-4445203 / 12) * d * t + (17980689 / 16) * d * t ^ 3 + (-977891773 / 800) * d * t ^ 5 + (72582867127 / 128000) * d * t ^ 7 + (-34975108843 / 307200) * d * t ^ 9 + (8253494347 / 480000) * d * t ^ 11 + (-4029211799 / 1843200) * d * t ^ 13 + (431838179 / 576000) * d * t ^ 15 + (-9600367 / 1843200) * d * t ^ 17 + (61534253 / 3456000) * d * t ^ 19 + (-200156039 / 15360000) * d * t ^ 21 + (-762013 / 1105920) * d * t ^ 25 + (-4445203 / 12) * alpha * t + (32144991 / 80) * alpha * t ^ 3 + (69457339 / 80) * alpha * t ^ 5 + (-955850612157 / 640000) * alpha * t ^ 7 + (4909460936071 / 7680000) * alpha * t ^ 9 + (-12186287921 / 384000) * alpha * t ^ 11 + (-1928089174273 / 46080000) * alpha * t ^ 13 + (38741007331 / 1440000) * alpha * t ^ 15 + (55617433591 / 46080000) * alpha * t ^ 17 + (150073333 / 540000) * alpha * t ^ 19 + (-1034568387 / 5120000) * alpha * t ^ 21 + (802807933 / 27648000) * alpha * t ^ 25 + (3436647 / 80) * alpha * d * t ^ 3 + (-580719143 / 4800) * alpha * d * t ^ 5 + (128957062877 / 1152000) * alpha * d * t ^ 7 + (-17227000579 / 512000) * alpha * d * t ^ 9 + (387569023 / 768000) * alpha * d * t ^ 11 + (-4716764347 / 9216000) * alpha * d * t ^ 13 + (-54530671 / 230400) * alpha * d * t ^ 15 + (-200084731 / 9216000) * alpha * d * t ^ 17 + (-171973619 / 6912000) * alpha * d * t ^ 19 + (194246791 / 9216000) * alpha * d * t ^ 21 + (821303 / 3072000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_03, v57_10, v57_11, v57_12, v57_13, v57_20, v57_21, v57_22, v57_23, v57_30, v57_31, v57_32, v57_33, v57_40, v57_41, v57_42, v57_43]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23, phase57_30, phase57_31, phase57_32, phase57_33, phase57_40, phase57_41, phase57_42, phase57_43]
  try simp only [star_one, star_neg]
  linear_combination ((3436647 / 160) * t ^ 3 + (-43099669 / 800) * t ^ 5 + (16694325263 / 384000) * t ^ 7 + (-22071334103 / 2048000) * t ^ 9 + (549102359 / 1024000) * t ^ 11 + (-121094833127 / 110592000) * t ^ 13 + (632161449 / 2048000) * t ^ 15 + (-317757869 / 9216000) * t ^ 17 + (-166864171 / 36864000) * t ^ 19 + (21803313 / 2048000) * t ^ 21 + (24802063 / 55296000) * t ^ 25 + (-6329 / 32) * d * t ^ 3 + (1060873 / 4800) * d * t ^ 5 + (416154253 / 1728000) * d * t ^ 7 + (-1080439043 / 3072000) * d * t ^ 9 + (306634141 / 4608000) * d * t ^ 11 + (54688969 / 2048000) * d * t ^ 13 + (-88183387 / 13824000) * d * t ^ 15 + (10901147 / 11059200) * d * t ^ 17 + (-19848719 / 82944000) * d * t ^ 19 + (-8771903 / 55296000) * d * t ^ 21 + (337649 / 13271040) * d * t ^ 25 + (-37051 / 4608) * d ^ 2 * t ^ 7 + (92248651 / 6144000) * d ^ 2 * t ^ 9 + (-66885083 / 9216000) * d ^ 2 * t ^ 11 + (12186223 / 36864000) * d ^ 2 * t ^ 13 + (-3660259 / 55296000) * d ^ 2 * t ^ 15 + (-8357 / 737280) * d ^ 2 * t ^ 17 + (-10507 / 884736) * d ^ 2 * t ^ 19 + (46597 / 6912000) * d ^ 2 * t ^ 21) * alpha_sq + ((-56961 / 16) * t ^ 3 + (4422647 / 640) * t ^ 5 + (-1108677353 / 288000) * t ^ 7 + (299650037 / 614400) * t ^ 9 + (-34200217 / 768000) * t ^ 11 + (1239417943 / 55296000) * t ^ 13 + (20753941 / 9216000) * t ^ 15 + (8197 / 122880) * t ^ 17 + (-22801813 / 55296000) * t ^ 19 + (-360901 / 9216000) * t ^ 21 + (6329 / 32) * alpha * t ^ 3 + (-1060873 / 4800) * alpha * t ^ 5 + (-249481703 / 1728000) * alpha * t ^ 7 + (540912239 / 3072000) * alpha * t ^ 9 + (52071911 / 4608000) * alpha * t ^ 11 + (-1209807059 / 55296000) * alpha * t ^ 13 + (7642631 / 2764800) * alpha * t ^ 15 + (-506231 / 11059200) * alpha * t ^ 17 + (-1629901 / 82944000) * alpha * t ^ 19 + (-11003 / 442368) * alpha * t ^ 21 + (-4465 / 2654208) * alpha * t ^ 25) * d_sq
theorem v58_44 (t : ℂ) : (momentPoly 58 z58 4 4).eval t = (257821774 + (-917946008) * t ^ 2 + (120356641707 / 100) * t ^ 4 + (-348605163213 / 500) * t ^ 6 + (18202698375490457 / 96000000) * t ^ 8 + (-1392425680500947 / 24000000) * t ^ 10 + (558267773280299 / 25600000) * t ^ 12 + (9827837849467 / 576000000) * t ^ 14 + (91181618187791 / 256000000) * t ^ 16 + (-632758902529 / 32000000) * t ^ 18 + (9916897554821 / 1152000000) * t ^ 20 + (6936546567203 / 576000000) * t ^ 22 + (-550774360013 / 144000000) * t ^ 24 + (-11972392307 / 432000000) * t ^ 26 + (721489055579 / 6912000000) * t ^ 32 + (-8659868 / 3) * d * t ^ 2 + (174242321 / 20) * d * t ^ 4 + (-2774948651 / 300) * d * t ^ 6 + (76986597158747 / 19200000) * d * t ^ 8 + (-3385540885763 / 4800000) * d * t ^ 10 + (28339173349879 / 230400000) * d * t ^ 12 + (74652591431 / 23040000) * d * t ^ 14 + (-3803534308981 / 460800000) * d * t ^ 16 + (8931342231 / 6400000) * d * t ^ 18 + (376705007207 / 691200000) * d * t ^ 20 + (-9267119957 / 115200000) * d * t ^ 22 + (-3717017 / 2304000) * d * t ^ 24 + (-3723906827 / 86400000) * d * t ^ 26 + (3295379 / 11059200) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z58, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v57_00, v57_01, v57_02, v57_03, v57_04, v57_10, v57_11, v57_12, v57_13, v57_14, v57_20, v57_21, v57_22, v57_23, v57_24, v57_30, v57_31, v57_32, v57_33, v57_34, v57_40, v57_41, v57_42, v57_43, v57_44]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24, phase57_30, phase57_31, phase57_32, phase57_33, phase57_34, phase57_40, phase57_41, phase57_42, phase57_43, phase57_44]
  try simp only [star_one, star_neg]
  linear_combination ((2164967 / 12) * t ^ 2 + (-9591791 / 40) * t ^ 4 + (-36074799 / 160) * t ^ 6 + (2641706211793 / 5760000) * t ^ 8 + (-84838892069 / 460800) * t ^ 10 + (124093360169 / 8640000) * t ^ 12 + (7966128203 / 11520000) * t ^ 14 + (-46554714677 / 11520000) * t ^ 16 + (17397996829 / 138240000) * t ^ 18 + (-5834558879 / 8640000) * t ^ 20 + (2591426419 / 46080000) * t ^ 22 + (-163085437 / 13824000) * t ^ 26 + (-2578639 / 120) * d * t ^ 4 + (62904479 / 960) * d * t ^ 6 + (-120715075129 / 1728000) * d * t ^ 8 + (67508480503 / 2304000) * d * t ^ 10 + (-75606318013 / 18432000) * d * t ^ 12 + (27399956207 / 27648000) * d * t ^ 14 + (-44931532561 / 110592000) * d * t ^ 16 + (544135259 / 13824000) * d * t ^ 18 + (1189221331 / 165888000) * d * t ^ 20 + (-231197773 / 27648000) * d * t ^ 22 + (-3717017 / 13824000) * d * t ^ 24 + (-1558171 / 2764800) * d * t ^ 26 + (3295379 / 66355200) * d * t ^ 32 + (-12583 / 192) * d ^ 2 * t ^ 6 + (4905427 / 86400) * d ^ 2 * t ^ 8 + (22564751 / 288000) * d ^ 2 * t ^ 10 + (-1334080253 / 18432000) * d ^ 2 * t ^ 12 + (-111756197 / 27648000) * d ^ 2 * t ^ 14 + (831057631 / 110592000) * d ^ 2 * t ^ 16 + (-39853 / 40960) * d ^ 2 * t ^ 18 + (-798019 / 6635520) * d ^ 2 * t ^ 20 + (2909573 / 20736000) * d ^ 2 * t ^ 22 + (16189 / 1327104) * d ^ 2 * t ^ 24 + (-123709 / 4976640) * d ^ 2 * t ^ 26 + (9025 / 31850496) * d ^ 2 * t ^ 32) * alpha_sq + ((-2164967 / 12) * t ^ 2 + (4117429 / 8) * t ^ 4 + (-168012649 / 320) * t ^ 6 + (263070506731 / 1152000) * t ^ 8 + (-101412027127 / 2304000) * t ^ 10 + (1889645424761 / 276480000) * t ^ 12 + (-29859103417 / 27648000) * t ^ 14 + (18734055697 / 36864000) * t ^ 16 + (-25395437 / 2764800) * t ^ 18 + (783417403 / 55296000) * t ^ 20 + (-650824573 / 138240000) * t ^ 22 + (-16189 / 442368) * t ^ 24 + (-993617 / 1658880) * t ^ 26 + (-9025 / 10616832) * t ^ 32) * d_sq
#print axioms v58_00
#print axioms v58_11
#print axioms v58_22
#print axioms v58_33
#print axioms v58_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v59_02 (t : ℂ) : (momentPoly 59 z59 0 2).eval t = ((-499 / 48) * t ^ 2 + (1189 / 96) * t ^ 4 + (-1 / 12) * d * t ^ 2 + (523 / 120) * alpha * t ^ 2 + (-171 / 40) * alpha * t ^ 4 + (-1 / 144) * alpha * d * t ^ 2 + (1 / 288) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02]
  try simp only [phase57_00, phase57_01, phase57_02]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 144) * t ^ 2) * alpha_sq + ((-1 / 144) * t ^ 2) * d_sq
theorem v59_03 (t : ℂ) : (momentPoly 59 z59 0 3).eval t = ((-9853 / 320) * t ^ 3 + (10483 / 320) * t ^ 5 + 2 * t ^ 9 + (125 / 96) * d * t ^ 3 + (-137 / 96) * d * t ^ 5 + (-47 / 1152) * d * t ^ 9 + (43051 / 2400) * alpha * t ^ 3 + (-49849 / 2400) * alpha * t ^ 5 + (88751 / 28800) * alpha * t ^ 9 + (-533 / 960) * alpha * d * t ^ 3 + (523 / 960) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_03]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03]
  try simp only [star_one, star_neg]
  linear_combination ((-533 / 960) * t ^ 3 + (171 / 320) * t ^ 5 + (1 / 384) * d * t ^ 3 + (-1 / 576) * d * t ^ 5) * alpha_sq + ((-1 / 48) * t ^ 3 + (-1 / 384) * alpha * t ^ 3 + (1 / 576) * alpha * t ^ 5) * d_sq
theorem v59_04 (t : ℂ) : (momentPoly 59 z59 0 4).eval t = ((468517 / 4800) * t ^ 4 + (-517529 / 1600) * t ^ 6 + (4982797 / 19200) * t ^ 8 + (-544619 / 14400) * t ^ 10 + (55499 / 4608) * t ^ 16 + (1731 / 320) * d * t ^ 4 + (-10579 / 1920) * d * t ^ 6 + (171 / 640) * d * t ^ 8 + (-143 / 288) * d * t ^ 10 + (-1070193 / 4000) * alpha * t ^ 4 + (28556047 / 48000) * alpha * t ^ 6 + (-164263 / 500) * alpha * t ^ 8 + (-8071 / 4500) * alpha * t ^ 10 + (173441 / 48000) * alpha * t ^ 16 + (-19963 / 7200) * alpha * d * t ^ 4 + (14633 / 4800) * alpha * d * t ^ 6 + (547 / 2304) * alpha * d * t ^ 8 + (-23669 / 43200) * alpha * d * t ^ 10 + (95 / 13824) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_03, v58_04]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04]
  try simp only [star_one, star_neg]
  linear_combination ((-44701 / 14400) * t ^ 4 + (32941 / 9600) * t ^ 6 + (-24869 / 43200) * t ^ 10 + (181 / 960) * d * t ^ 4 + (-1579 / 5760) * d * t ^ 6 + (57 / 640) * d * t ^ 8 + (1 / 2304) * d ^ 2 * t ^ 6 + (-1 / 6912) * d ^ 2 * t ^ 8) * alpha_sq + ((203 / 576) * t ^ 4 + (-335 / 768) * t ^ 6 + (1 / 2304) * t ^ 8 + (-47 / 1728) * t ^ 10 + (-181 / 960) * alpha * t ^ 4 + (533 / 2880) * alpha * t ^ 6) * d_sq
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
theorem v59_12 (t : ℂ) : (momentPoly 59 z59 1 2).eval t = (117 * t + (-118907 / 960) * t ^ 3 + (10417 / 960) * t ^ 5 + (-39 / 8) * d * t + (995 / 192) * d * t ^ 3 + (-91 / 192) * d * t ^ 5 + (39 / 8) * alpha * t + (119 / 960) * alpha * t ^ 3 + (-1573 / 320) * alpha * t ^ 5 + (-533 / 2880) * alpha * d * t ^ 3 + (523 / 2880) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_10, v58_11, v58_12]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12]
  try simp only [star_one, star_neg]
  linear_combination ((533 / 2880) * t ^ 3 + (-57 / 320) * t ^ 5 + (-1 / 1152) * d * t ^ 3 + (1 / 1728) * d * t ^ 5) * alpha_sq + ((-1 / 48) * t ^ 3 + (-1 / 1152) * alpha * t ^ 3 + (1 / 1728) * alpha * t ^ 5) * d_sq
theorem v59_13 (t : ℂ) : (momentPoly 59 z59 1 3).eval t = ((-14471 / 8) * t ^ 2 + (18650399 / 4800) * t ^ 4 + (-6590849 / 3200) * t ^ 6 + (-86651 / 9600) * t ^ 10 + (-29 / 2) * d * t ^ 2 + (1073 / 64) * d * t ^ 4 + (-475 / 192) * d * t ^ 6 + (-143 / 1152) * d * t ^ 10 + (15167 / 20) * alpha * t ^ 2 + (-7012433 / 4800) * alpha * t ^ 4 + (3339037 / 4800) * alpha * t ^ 6 + (209471 / 28800) * alpha * t ^ 10 + (-29 / 24) * alpha * d * t ^ 2 + (6311 / 14400) * alpha * d * t ^ 4 + (8509 / 9600) * alpha * d * t ^ 6 + (-3749 / 28800) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_03, v58_10, v58_11, v58_12, v58_13]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13]
  try simp only [star_one, star_neg]
  linear_combination ((-29 / 24) * t ^ 2 + (4381 / 3600) * t ^ 4 + (-1957 / 12800) * t ^ 6 + (24869 / 172800) * t ^ 10) * alpha_sq + ((-29 / 24) * t ^ 2 + (761 / 576) * t ^ 4 + (-111 / 512) * t ^ 6 + (-47 / 6912) * t ^ 10 + (-181 / 1920) * alpha * t ^ 4 + (533 / 5760) * alpha * t ^ 6) * d_sq
theorem v59_14 (t : ℂ) : (momentPoly 59 z59 1 4).eval t = ((-226619 / 32) * t ^ 3 + (922268849 / 64000) * t ^ 5 + (-236861949 / 32000) * t ^ 7 + (235221917 / 384000) * t ^ 9 + (-153754423 / 288000) * t ^ 11 + (12091073 / 1152000) * t ^ 17 + (14375 / 48) * d * t ^ 3 + (-71516483 / 115200) * d * t ^ 5 + (6257491 / 19200) * d * t ^ 7 + (-3955601 / 230400) * d * t ^ 9 + (3169 / 256) * d * t ^ 11 + (-4241 / 9216) * d * t ^ 17 + (990173 / 240) * alpha * t ^ 3 + (-5200359287 / 576000) * alpha * t ^ 5 + (165236433 / 32000) * alpha * t ^ 7 + (477565603 / 1152000) * alpha * t ^ 9 + (-194221859 / 288000) * alpha * t ^ 11 + (-51527 / 384000) * alpha * t ^ 17 + (-12259 / 96) * alpha * d * t ^ 3 + (16546877 / 64000) * alpha * d * t ^ 5 + (-13669571 / 96000) * alpha * d * t ^ 7 + (14774723 / 1152000) * alpha * d * t ^ 9 + (-1018537 / 864000) * alpha * d * t ^ 11 + (-496573 / 3456000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_03, v58_04, v58_10, v58_11, v58_12, v58_13, v58_14]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14]
  try simp only [star_one, star_neg]
  linear_combination ((-12259 / 96) * t ^ 3 + (16473919 / 72000) * t ^ 5 + (-2802853 / 32000) * t ^ 7 + (-4850291 / 384000) * t ^ 9 + (-362641 / 288000) * t ^ 11 + (173441 / 1152000) * t ^ 17 + (115 / 192) * d * t ^ 3 + (-709 / 960) * d * t ^ 5 + (199 / 23040) * d * t ^ 7 + (12493 / 92160) * d * t ^ 9 + (-47 / 13824) * d * t ^ 11 + (95 / 82944) * d * t ^ 17 + (181 / 23040) * d ^ 2 * t ^ 7 + (-523 / 69120) * d ^ 2 * t ^ 9) * alpha_sq + ((-115 / 24) * t ^ 3 + (130139 / 23040) * t ^ 5 + (-1853 / 1536) * t ^ 7 + (259 / 5760) * t ^ 9 + (-95 / 864) * t ^ 11 + (-115 / 192) * alpha * t ^ 3 + (12017 / 43200) * alpha * t ^ 5 + (13909 / 38400) * alpha * t ^ 7 + (665 / 18432) * alpha * t ^ 9 + (-31967 / 345600) * alpha * t ^ 11 + (95 / 82944) * alpha * t ^ 17) * d_sq
theorem v59_20 (t : ℂ) : (momentPoly 59 z59 2 0).eval t = ((-499 / 48) * t ^ 2 + (1189 / 96) * t ^ 4 + (-1 / 12) * d * t ^ 2 + (-523 / 120) * alpha * t ^ 2 + (171 / 40) * alpha * t ^ 4 + (1 / 144) * alpha * d * t ^ 2 + (-1 / 288) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_10, v58_20]
  try simp only [phase57_00, phase57_10, phase57_20]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 144) * t ^ 2) * alpha_sq + ((-1 / 144) * t ^ 2) * d_sq
theorem v59_21 (t : ℂ) : (momentPoly 59 z59 2 1).eval t = (117 * t + (-118907 / 960) * t ^ 3 + (10417 / 960) * t ^ 5 + (-39 / 8) * d * t + (995 / 192) * d * t ^ 3 + (-91 / 192) * d * t ^ 5 + (-39 / 8) * alpha * t + (-119 / 960) * alpha * t ^ 3 + (1573 / 320) * alpha * t ^ 5 + (533 / 2880) * alpha * d * t ^ 3 + (-523 / 2880) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_10, v58_11, v58_20, v58_21]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21]
  try simp only [star_one, star_neg]
  linear_combination ((533 / 2880) * t ^ 3 + (-57 / 320) * t ^ 5 + (-1 / 1152) * d * t ^ 3 + (1 / 1728) * d * t ^ 5) * alpha_sq + ((-1 / 48) * t ^ 3 + (1 / 1152) * alpha * t ^ 3 + (-1 / 1728) * alpha * t ^ 5) * d_sq
theorem v59_22 (t : ℂ) : (momentPoly 59 z59 2 2).eval t = (6903 + (-13224) * t ^ 2 + (10113793 / 1600) * t ^ 4 + (-1357321 / 9600) * t ^ 6 + (1432763 / 9600) * t ^ 8 + (-58 / 3) * d * t ^ 2 + (19729 / 960) * d * t ^ 4 + (-2807 / 1920) * d * t ^ 6 + (-57 / 640) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_10, v58_11, v58_12, v58_20, v58_21, v58_22]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22]
  try simp only [star_one, star_neg]
  linear_combination ((29 / 18) * t ^ 2 + (-1693 / 2880) * t ^ 4 + (-2707 / 2880) * t ^ 6 + (-181 / 2880) * d * t ^ 4 + (1579 / 17280) * d * t ^ 6 + (-19 / 640) * d * t ^ 8 + (-1 / 6912) * d ^ 2 * t ^ 6 + (1 / 20736) * d ^ 2 * t ^ 8) * alpha_sq + ((-29 / 18) * t ^ 2 + (947 / 576) * t ^ 4 + (-331 / 2304) * t ^ 6 + (-1 / 6912) * t ^ 8) * d_sq
theorem v59_23 (t : ℂ) : (momentPoly 59 z59 2 3).eval t = (20359 * t + (-2734861 / 64) * t ^ 3 + (5000802671 / 192000) * t ^ 5 + (-78902783 / 19200) * t ^ 7 + (30004333 / 64000) * t ^ 9 + (-97259 / 384000) * t ^ 11 + (-6048421 / 384000) * t ^ 13 + (-20359 / 24) * d * t + (114425 / 64) * d * t ^ 3 + (-14052057 / 12800) * d * t ^ 5 + (3322541 / 19200) * d * t ^ 7 + (-77791 / 4800) * d * t ^ 9 + (87643 / 76800) * d * t ^ 11 + (-99427 / 230400) * d * t ^ 13 + (20359 / 24) * alpha * t + (2737 / 64) * alpha * t ^ 3 + (-99627389 / 38400) * alpha * t ^ 5 + (11487573 / 6400) * alpha * t ^ 7 + (-2051861 / 19200) * alpha * t ^ 9 + (-2387243 / 76800) * alpha * t ^ 11 + (10772767 / 230400) * alpha * t ^ 13 + (-12259 / 192) * alpha * d * t ^ 3 + (1581899 / 12800) * alpha * d * t ^ 5 + (-3405847 / 57600) * alpha * d * t ^ 7 + (-91 / 7680) * alpha * d * t ^ 9 + (-32893 / 76800) * alpha * d * t ^ 11 + (-8357 / 46080) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_03, v58_10, v58_11, v58_12, v58_13, v58_20, v58_21, v58_22, v58_23]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23]
  try simp only [star_one, star_neg]
  linear_combination ((12259 / 192) * t ^ 3 + (-35339 / 300) * t ^ 5 + (1027949 / 19200) * t ^ 7 + (802387 / 691200) * t ^ 11 + (-2717 / 5120) * t ^ 13 + (-115 / 384) * d * t ^ 3 + (21961 / 86400) * d * t ^ 5 + (64307 / 345600) * d * t ^ 7 + (-60011 / 460800) * d * t ^ 9 + (-34367 / 1382400) * d * t ^ 11 + (24869 / 2073600) * d * t ^ 13 + (-181 / 23040) * d ^ 2 * t ^ 7 + (523 / 69120) * d ^ 2 * t ^ 9) * alpha_sq + ((-115 / 16) * t ^ 3 + (172661 / 23040) * t ^ 5 + (-997 / 1536) * t ^ 7 + (-259 / 5760) * t ^ 9 + (-95 / 3456) * t ^ 11 + (-115 / 384) * alpha * t ^ 3 + (21961 / 86400) * alpha * t ^ 5 + (21679 / 345600) * alpha * t ^ 7 + (-1 / 18432) * alpha * t ^ 9 + (-29617 / 1382400) * alpha * t ^ 11 + (-47 / 82944) * alpha * t ^ 13) * d_sq
theorem v59_24 (t : ℂ) : (momentPoly 59 z59 2 4).eval t = ((-2496497 / 6) * t ^ 2 + (1027884199 / 800) * t ^ 4 + (-836587064181 / 640000) * t ^ 6 + (1666900968203 / 3840000) * t ^ 8 + (-345851631 / 128000) * t ^ 10 + (170043272339 / 23040000) * t ^ 12 + (-237443771 / 640000) * t ^ 14 + (-1382241359 / 23040000) * t ^ 18 + (1042386727 / 11520000) * t ^ 20 + (-10006 / 3) * d * t ^ 2 + (61161 / 8) * d * t ^ 4 + (-6237670453 / 1152000) * d * t ^ 6 + (59676313 / 51200) * d * t ^ 8 + (-23837957 / 192000) * d * t ^ 10 + (282151783 / 4608000) * d * t ^ 12 + (1944817 / 1152000) * d * t ^ 14 + (-1137919 / 1536000) * d * t ^ 18 + (-58171 / 1152000) * d * t ^ 20 + (2616569 / 15) * alpha * t ^ 2 + (-49810951 / 100) * alpha * t ^ 4 + (107887839503 / 230400) * alpha * t ^ 6 + (-36979889303 / 256000) * alpha * t ^ 8 + (582265017 / 128000) * alpha * t ^ 10 + (-2279777109 / 512000) * alpha * t ^ 12 + (-264310667 / 1152000) * alpha * t ^ 14 + (-483520063 / 4608000) * alpha * t ^ 18 + (231589387 / 2304000) * alpha * t ^ 20 + (-5003 / 18) * alpha * d * t ^ 2 + (152011 / 2400) * alpha * d * t ^ 4 + (893131387 / 1152000) * alpha * d * t ^ 6 + (-1367842523 / 2304000) * alpha * d * t ^ 8 + (-4596829 / 192000) * alpha * d * t ^ 10 + (900002501 / 13824000) * alpha * d * t ^ 12 + (-5687713 / 691200) * alpha * d * t ^ 14 + (-394919 / 13824000) * alpha * d * t ^ 18 + (367 / 9216) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_03, v58_04, v58_10, v58_11, v58_12, v58_13, v58_14, v58_20, v58_21, v58_22, v58_23, v58_24]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24]
  try simp only [star_one, star_neg]
  linear_combination ((-5003 / 18) * t ^ 2 + (83239 / 150) * t ^ 4 + (-400672757 / 1152000) * t ^ 6 + (89984869 / 1152000) * t ^ 8 + (129400183 / 2304000) * t ^ 10 + (-30243169 / 576000) * t ^ 12 + (-1789199 / 172800) * t ^ 14 + (-675353 / 6912000) * t ^ 18 + (5343433 / 3456000) * d * t ^ 6 + (-936091 / 230400) * d * t ^ 8 + (8266103 / 2304000) * d * t ^ 10 + (-719081 / 552960) * d * t ^ 12 + (2461807 / 10368000) * d * t ^ 14 + (272729 / 41472000) * d * t ^ 18 + (-58171 / 3456000) * d * t ^ 20 + (-1243 / 64800) * d ^ 2 * t ^ 8 + (14483 / 691200) * d ^ 2 * t ^ 10 + (37 / 24576) * d ^ 2 * t ^ 12 + (-16571 / 4147200) * d ^ 2 * t ^ 14 + (-95 / 663552) * d ^ 2 * t ^ 18 + (95 / 995328) * d ^ 2 * t ^ 20) * alpha_sq + ((-5003 / 18) * t ^ 2 + (14459 / 24) * t ^ 4 + (-19247849 / 46080) * t ^ 6 + (66740363 / 691200) * t ^ 8 + (-792179 / 92160) * t ^ 10 + (20968673 / 5529600) * t ^ 12 + (-358133 / 1382400) * t ^ 14 + (-15365 / 221184) * t ^ 18 + (-95 / 331776) * t ^ 20 + (-3439 / 80) * alpha * t ^ 4 + (96292651 / 1152000) * alpha * t ^ 6 + (-32387573 / 768000) * alpha * t ^ 8 + (4520141 / 2304000) * alpha * t ^ 10 + (-1928681 / 6912000) * alpha * t ^ 12 + (-25541 / 207360) * alpha * t ^ 14 + (-472823 / 20736000) * alpha * t ^ 18) * d_sq
theorem v59_30 (t : ℂ) : (momentPoly 59 z59 3 0).eval t = ((-9853 / 320) * t ^ 3 + (10483 / 320) * t ^ 5 + 2 * t ^ 9 + (125 / 96) * d * t ^ 3 + (-137 / 96) * d * t ^ 5 + (-47 / 1152) * d * t ^ 9 + (-43051 / 2400) * alpha * t ^ 3 + (49849 / 2400) * alpha * t ^ 5 + (-88751 / 28800) * alpha * t ^ 9 + (533 / 960) * alpha * d * t ^ 3 + (-523 / 960) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_10, v58_20, v58_30]
  try simp only [phase57_00, phase57_10, phase57_20, phase57_30]
  try simp only [star_one, star_neg]
  linear_combination ((-533 / 960) * t ^ 3 + (171 / 320) * t ^ 5 + (1 / 384) * d * t ^ 3 + (-1 / 576) * d * t ^ 5) * alpha_sq + ((-1 / 48) * t ^ 3 + (1 / 384) * alpha * t ^ 3 + (-1 / 576) * alpha * t ^ 5) * d_sq
theorem v59_31 (t : ℂ) : (momentPoly 59 z59 3 1).eval t = ((-14471 / 8) * t ^ 2 + (18650399 / 4800) * t ^ 4 + (-6590849 / 3200) * t ^ 6 + (-86651 / 9600) * t ^ 10 + (-29 / 2) * d * t ^ 2 + (1073 / 64) * d * t ^ 4 + (-475 / 192) * d * t ^ 6 + (-143 / 1152) * d * t ^ 10 + (-15167 / 20) * alpha * t ^ 2 + (7012433 / 4800) * alpha * t ^ 4 + (-3339037 / 4800) * alpha * t ^ 6 + (-209471 / 28800) * alpha * t ^ 10 + (29 / 24) * alpha * d * t ^ 2 + (-6311 / 14400) * alpha * d * t ^ 4 + (-8509 / 9600) * alpha * d * t ^ 6 + (3749 / 28800) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_10, v58_11, v58_20, v58_21, v58_30, v58_31]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21, phase57_30, phase57_31]
  try simp only [star_one, star_neg]
  linear_combination ((-29 / 24) * t ^ 2 + (4381 / 3600) * t ^ 4 + (-1957 / 12800) * t ^ 6 + (24869 / 172800) * t ^ 10) * alpha_sq + ((-29 / 24) * t ^ 2 + (761 / 576) * t ^ 4 + (-111 / 512) * t ^ 6 + (-47 / 6912) * t ^ 10 + (181 / 1920) * alpha * t ^ 4 + (-533 / 5760) * alpha * t ^ 6) * d_sq
theorem v59_32 (t : ℂ) : (momentPoly 59 z59 3 2).eval t = (20359 * t + (-2734861 / 64) * t ^ 3 + (5000802671 / 192000) * t ^ 5 + (-78902783 / 19200) * t ^ 7 + (30004333 / 64000) * t ^ 9 + (-97259 / 384000) * t ^ 11 + (-6048421 / 384000) * t ^ 13 + (-20359 / 24) * d * t + (114425 / 64) * d * t ^ 3 + (-14052057 / 12800) * d * t ^ 5 + (3322541 / 19200) * d * t ^ 7 + (-77791 / 4800) * d * t ^ 9 + (87643 / 76800) * d * t ^ 11 + (-99427 / 230400) * d * t ^ 13 + (-20359 / 24) * alpha * t + (-2737 / 64) * alpha * t ^ 3 + (99627389 / 38400) * alpha * t ^ 5 + (-11487573 / 6400) * alpha * t ^ 7 + (2051861 / 19200) * alpha * t ^ 9 + (2387243 / 76800) * alpha * t ^ 11 + (-10772767 / 230400) * alpha * t ^ 13 + (12259 / 192) * alpha * d * t ^ 3 + (-1581899 / 12800) * alpha * d * t ^ 5 + (3405847 / 57600) * alpha * d * t ^ 7 + (91 / 7680) * alpha * d * t ^ 9 + (32893 / 76800) * alpha * d * t ^ 11 + (8357 / 46080) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_10, v58_11, v58_12, v58_20, v58_21, v58_22, v58_30, v58_31, v58_32]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22, phase57_30, phase57_31, phase57_32]
  try simp only [star_one, star_neg]
  linear_combination ((12259 / 192) * t ^ 3 + (-35339 / 300) * t ^ 5 + (1027949 / 19200) * t ^ 7 + (802387 / 691200) * t ^ 11 + (-2717 / 5120) * t ^ 13 + (-115 / 384) * d * t ^ 3 + (21961 / 86400) * d * t ^ 5 + (64307 / 345600) * d * t ^ 7 + (-60011 / 460800) * d * t ^ 9 + (-34367 / 1382400) * d * t ^ 11 + (24869 / 2073600) * d * t ^ 13 + (-181 / 23040) * d ^ 2 * t ^ 7 + (523 / 69120) * d ^ 2 * t ^ 9) * alpha_sq + ((-115 / 16) * t ^ 3 + (172661 / 23040) * t ^ 5 + (-997 / 1536) * t ^ 7 + (-259 / 5760) * t ^ 9 + (-95 / 3456) * t ^ 11 + (115 / 384) * alpha * t ^ 3 + (-21961 / 86400) * alpha * t ^ 5 + (-21679 / 345600) * alpha * t ^ 7 + (1 / 18432) * alpha * t ^ 9 + (29617 / 1382400) * alpha * t ^ 11 + (47 / 82944) * alpha * t ^ 13) * d_sq
theorem v59_33 (t : ℂ) : (momentPoly 59 z59 3 3).eval t = (1201181 + (-3422052) * t ^ 2 + (5188375809 / 1600) * t ^ 4 + (-175012476027 / 160000) * t ^ 6 + (23116755521 / 160000) * t ^ 8 + (-11566436577 / 160000) * t ^ 10 + (274458949 / 480000) * t ^ 12 + (-473444143 / 640000) * t ^ 14 + (-49069171 / 1920000) * t ^ 18 + (-5003) * d * t ^ 2 + (3373659 / 320) * d * t ^ 4 + (-301396151 / 48000) * d * t ^ 6 + (30440209 / 38400) * d * t ^ 8 + (-3779017 / 64000) * d * t ^ 10 + (132553 / 72000) * d * t ^ 12 + (261701 / 96000) * d * t ^ 14 + (-47 / 288) * d * t ^ 18) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_03, v58_10, v58_11, v58_12, v58_13, v58_20, v58_21, v58_22, v58_23, v58_30, v58_31, v58_32, v58_33]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23, phase57_30, phase57_31, phase57_32, phase57_33]
  try simp only [star_one, star_neg]
  linear_combination ((5003 / 12) * t ^ 2 + (-96501 / 320) * t ^ 4 + (-725621 / 1280) * t ^ 6 + (14378149 / 30720) * t ^ 8 + (-1118191 / 51200) * t ^ 10 + (-124289 / 691200) * t ^ 12 + (636891 / 102400) * t ^ 14 + (6601309 / 8294400) * t ^ 18 + (-10317 / 320) * d * t ^ 4 + (8853083 / 115200) * d * t ^ 6 + (-26646469 / 460800) * d * t ^ 8 + (684711 / 51200) * d * t ^ 10 + (-114047 / 230400) * d * t ^ 12 + (114809 / 345600) * d * t ^ 14 + (-43 / 576) * d ^ 2 * t ^ 6 + (13261 / 345600) * d ^ 2 * t ^ 8 + (9109 / 230400) * d ^ 2 * t ^ 10 + (-1283 / 230400) * d ^ 2 * t ^ 14) * alpha_sq + ((-5003 / 12) * t ^ 2 + (53979 / 64) * t ^ 4 + (-2378717 / 4800) * t ^ 6 + (34113377 / 460800) * t ^ 8 + (-1066349 / 153600) * t ^ 10 + (416609 / 691200) * t ^ 12 + (-120161 / 307200) * t ^ 14 + (-2209 / 331776) * t ^ 18) * d_sq
theorem v59_34 (t : ℂ) : (momentPoly 59 z59 3 4).eval t = (4683269 * t + (-584665719 / 40) * t ^ 3 + (524850872523 / 32000) * t ^ 5 + (-101897041343847 / 12800000) * t ^ 7 + (22994711917427 / 12800000) * t ^ 9 + (-24345034818427 / 76800000) * t ^ 11 + (42418856293 / 11520000) * t ^ 13 + (467600008757 / 38400000) * t ^ 15 + (-132582387097 / 51200000) * t ^ 17 + (-99487982041 / 230400000) * t ^ 19 + (14633389907 / 76800000) * t ^ 21 + (26032062191 / 460800000) * t ^ 25 + (-4683269 / 24) * d * t + (4892415 / 8) * d * t ^ 3 + (-4412123423 / 6400) * d * t ^ 5 + (512429414431 / 1536000) * d * t ^ 7 + (-36123821261 / 512000) * d * t ^ 9 + (168052929797 / 15360000) * d * t ^ 11 + (-6794290397 / 4608000) * d * t ^ 13 + (693986047 / 1536000) * d * t ^ 15 + (-18487657 / 3686400) * d * t ^ 17 + (74581687 / 5529600) * d * t ^ 19 + (-207221873 / 23040000) * d * t ^ 21 + (-854173 / 2211840) * d * t ^ 25 + (4683269 / 24) * alpha * t + (585123 / 40) * alpha * t ^ 3 + (-7612089937 / 6400) * alpha * t ^ 5 + (12344123678771 / 7680000) * alpha * t ^ 7 + (-5301521711167 / 7680000) * alpha * t ^ 9 + (209245630479 / 5120000) * alpha * t ^ 11 + (48042681583 / 921600) * alpha * t ^ 13 + (-14772170331 / 512000) * alpha * t ^ 15 + (-132051973057 / 92160000) * alpha * t ^ 17 + (-41450797049 / 138240000) * alpha * t ^ 19 + (2734712771 / 11520000) * alpha * t ^ 21 + (-1663909321 / 55296000) * alpha * t ^ 25 + (-873587 / 40) * alpha * d * t ^ 3 + (1204731943 / 19200) * alpha * d * t ^ 5 + (-273539752987 / 4608000) * alpha * d * t ^ 7 + (28265214881 / 1536000) * alpha * d * t ^ 9 + (-3512963557 / 9216000) * alpha * d * t ^ 11 + (255968131 / 864000) * alpha * d * t ^ 13 + (190683061 / 1536000) * alpha * d * t ^ 15 + (220543931 / 18432000) * alpha * d * t ^ 17 + (126241423 / 9216000) * alpha * d * t ^ 19 + (-105925459 / 9216000) * alpha * d * t ^ 21 + (-821303 / 6144000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_03, v58_04, v58_10, v58_11, v58_12, v58_13, v58_14, v58_20, v58_21, v58_22, v58_23, v58_24, v58_30, v58_31, v58_32, v58_33, v58_34]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24, phase57_30, phase57_31, phase57_32, phase57_33, phase57_34]
  try simp only [star_one, star_neg]
  linear_combination ((873587 / 40) * t ^ 3 + (-94758029 / 1600) * t ^ 5 + (53808174889 / 1024000) * t ^ 7 + (-46133356067 / 3072000) * t ^ 9 + (6972027037 / 9216000) * t ^ 11 + (-4220397769 / 3456000) * t ^ 13 + (549123181 / 1536000) * t ^ 15 + (-693591613 / 18432000) * t ^ 17 + (-39102671 / 5184000) * t ^ 19 + (106954801 / 9216000) * t ^ 21 + (24802063 / 55296000) * t ^ 25 + (-1639 / 16) * d * t ^ 3 + (378967 / 3600) * d * t ^ 5 + (5277934147 / 27648000) * d * t ^ 7 + (-262330327 / 921600) * d * t ^ 9 + (726404701 / 9216000) * d * t ^ 11 + (623860477 / 33177600) * d * t ^ 13 + (-206215519 / 27648000) * d * t ^ 15 + (22075639 / 22118400) * d * t ^ 17 + (-7642739 / 55296000) * d * t ^ 19 + (-15992681 / 110592000) * d * t ^ 21 + (472511 / 19906560) * d * t ^ 25 + (-61721 / 11520) * d ^ 2 * t ^ 7 + (95235851 / 9216000) * d ^ 2 * t ^ 9 + (-143054291 / 27648000) * d ^ 2 * t ^ 11 + (4488941 / 18432000) * d ^ 2 * t ^ 13 + (-132917 / 3072000) * d ^ 2 * t ^ 15 + (-8357 / 1105920) * d ^ 2 * t ^ 17 + (-3439 / 442368) * d ^ 2 * t ^ 19 + (46597 / 10368000) * d ^ 2 * t ^ 21) * alpha_sq + ((-4917 / 2) * t ^ 3 + (19510693 / 3840) * t ^ 5 + (-27992888767 / 9216000) * t ^ 7 + (216383627 / 512000) * t ^ 9 + (-61825807 / 1843200) * t ^ 11 + (7536873 / 409600) * t ^ 13 + (7843669 / 9216000) * t ^ 15 + (8197 / 184320) * t ^ 17 + (-47497907 / 165888000) * t ^ 19 + (-360901 / 13824000) * t ^ 21 + (-1639 / 16) * alpha * t ^ 3 + (378967 / 3600) * alpha * t ^ 5 + (2952150467 / 27648000) * alpha * t ^ 7 + (-536973769 / 4608000) * alpha * t ^ 9 + (-63453043 / 9216000) * alpha * t ^ 11 + (860233471 / 55296000) * alpha * t ^ 13 + (-10323139 / 5529600) * alpha * t ^ 15 + (750583 / 22118400) * alpha * t ^ 17 + (-470419 / 55296000) * alpha * t ^ 19 + (16175 / 884736) * alpha * t ^ 21 + (4465 / 3981312) * alpha * t ^ 25) * d_sq
theorem v59_40 (t : ℂ) : (momentPoly 59 z59 4 0).eval t = ((468517 / 4800) * t ^ 4 + (-517529 / 1600) * t ^ 6 + (4982797 / 19200) * t ^ 8 + (-544619 / 14400) * t ^ 10 + (55499 / 4608) * t ^ 16 + (1731 / 320) * d * t ^ 4 + (-10579 / 1920) * d * t ^ 6 + (171 / 640) * d * t ^ 8 + (-143 / 288) * d * t ^ 10 + (1070193 / 4000) * alpha * t ^ 4 + (-28556047 / 48000) * alpha * t ^ 6 + (164263 / 500) * alpha * t ^ 8 + (8071 / 4500) * alpha * t ^ 10 + (-173441 / 48000) * alpha * t ^ 16 + (19963 / 7200) * alpha * d * t ^ 4 + (-14633 / 4800) * alpha * d * t ^ 6 + (-547 / 2304) * alpha * d * t ^ 8 + (23669 / 43200) * alpha * d * t ^ 10 + (-95 / 13824) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_10, v58_20, v58_30, v58_40]
  try simp only [phase57_00, phase57_10, phase57_20, phase57_30, phase57_40]
  try simp only [star_one, star_neg]
  linear_combination ((-44701 / 14400) * t ^ 4 + (32941 / 9600) * t ^ 6 + (-24869 / 43200) * t ^ 10 + (181 / 960) * d * t ^ 4 + (-1579 / 5760) * d * t ^ 6 + (57 / 640) * d * t ^ 8 + (1 / 2304) * d ^ 2 * t ^ 6 + (-1 / 6912) * d ^ 2 * t ^ 8) * alpha_sq + ((203 / 576) * t ^ 4 + (-335 / 768) * t ^ 6 + (1 / 2304) * t ^ 8 + (-47 / 1728) * t ^ 10 + (181 / 960) * alpha * t ^ 4 + (-533 / 2880) * alpha * t ^ 6) * d_sq
theorem v59_41 (t : ℂ) : (momentPoly 59 z59 4 1).eval t = ((-226619 / 32) * t ^ 3 + (922268849 / 64000) * t ^ 5 + (-236861949 / 32000) * t ^ 7 + (235221917 / 384000) * t ^ 9 + (-153754423 / 288000) * t ^ 11 + (12091073 / 1152000) * t ^ 17 + (14375 / 48) * d * t ^ 3 + (-71516483 / 115200) * d * t ^ 5 + (6257491 / 19200) * d * t ^ 7 + (-3955601 / 230400) * d * t ^ 9 + (3169 / 256) * d * t ^ 11 + (-4241 / 9216) * d * t ^ 17 + (-990173 / 240) * alpha * t ^ 3 + (5200359287 / 576000) * alpha * t ^ 5 + (-165236433 / 32000) * alpha * t ^ 7 + (-477565603 / 1152000) * alpha * t ^ 9 + (194221859 / 288000) * alpha * t ^ 11 + (51527 / 384000) * alpha * t ^ 17 + (12259 / 96) * alpha * d * t ^ 3 + (-16546877 / 64000) * alpha * d * t ^ 5 + (13669571 / 96000) * alpha * d * t ^ 7 + (-14774723 / 1152000) * alpha * d * t ^ 9 + (1018537 / 864000) * alpha * d * t ^ 11 + (496573 / 3456000) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_10, v58_11, v58_20, v58_21, v58_30, v58_31, v58_40, v58_41]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21, phase57_30, phase57_31, phase57_40, phase57_41]
  try simp only [star_one, star_neg]
  linear_combination ((-12259 / 96) * t ^ 3 + (16473919 / 72000) * t ^ 5 + (-2802853 / 32000) * t ^ 7 + (-4850291 / 384000) * t ^ 9 + (-362641 / 288000) * t ^ 11 + (173441 / 1152000) * t ^ 17 + (115 / 192) * d * t ^ 3 + (-709 / 960) * d * t ^ 5 + (199 / 23040) * d * t ^ 7 + (12493 / 92160) * d * t ^ 9 + (-47 / 13824) * d * t ^ 11 + (95 / 82944) * d * t ^ 17 + (181 / 23040) * d ^ 2 * t ^ 7 + (-523 / 69120) * d ^ 2 * t ^ 9) * alpha_sq + ((-115 / 24) * t ^ 3 + (130139 / 23040) * t ^ 5 + (-1853 / 1536) * t ^ 7 + (259 / 5760) * t ^ 9 + (-95 / 864) * t ^ 11 + (115 / 192) * alpha * t ^ 3 + (-12017 / 43200) * alpha * t ^ 5 + (-13909 / 38400) * alpha * t ^ 7 + (-665 / 18432) * alpha * t ^ 9 + (31967 / 345600) * alpha * t ^ 11 + (-95 / 82944) * alpha * t ^ 17) * d_sq
theorem v59_42 (t : ℂ) : (momentPoly 59 z59 4 2).eval t = ((-2496497 / 6) * t ^ 2 + (1027884199 / 800) * t ^ 4 + (-836587064181 / 640000) * t ^ 6 + (1666900968203 / 3840000) * t ^ 8 + (-345851631 / 128000) * t ^ 10 + (170043272339 / 23040000) * t ^ 12 + (-237443771 / 640000) * t ^ 14 + (-1382241359 / 23040000) * t ^ 18 + (1042386727 / 11520000) * t ^ 20 + (-10006 / 3) * d * t ^ 2 + (61161 / 8) * d * t ^ 4 + (-6237670453 / 1152000) * d * t ^ 6 + (59676313 / 51200) * d * t ^ 8 + (-23837957 / 192000) * d * t ^ 10 + (282151783 / 4608000) * d * t ^ 12 + (1944817 / 1152000) * d * t ^ 14 + (-1137919 / 1536000) * d * t ^ 18 + (-58171 / 1152000) * d * t ^ 20 + (-2616569 / 15) * alpha * t ^ 2 + (49810951 / 100) * alpha * t ^ 4 + (-107887839503 / 230400) * alpha * t ^ 6 + (36979889303 / 256000) * alpha * t ^ 8 + (-582265017 / 128000) * alpha * t ^ 10 + (2279777109 / 512000) * alpha * t ^ 12 + (264310667 / 1152000) * alpha * t ^ 14 + (483520063 / 4608000) * alpha * t ^ 18 + (-231589387 / 2304000) * alpha * t ^ 20 + (5003 / 18) * alpha * d * t ^ 2 + (-152011 / 2400) * alpha * d * t ^ 4 + (-893131387 / 1152000) * alpha * d * t ^ 6 + (1367842523 / 2304000) * alpha * d * t ^ 8 + (4596829 / 192000) * alpha * d * t ^ 10 + (-900002501 / 13824000) * alpha * d * t ^ 12 + (5687713 / 691200) * alpha * d * t ^ 14 + (394919 / 13824000) * alpha * d * t ^ 18 + (-367 / 9216) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_10, v58_11, v58_12, v58_20, v58_21, v58_22, v58_30, v58_31, v58_32, v58_40, v58_41, v58_42]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22, phase57_30, phase57_31, phase57_32, phase57_40, phase57_41, phase57_42]
  try simp only [star_one, star_neg]
  linear_combination ((-5003 / 18) * t ^ 2 + (83239 / 150) * t ^ 4 + (-400672757 / 1152000) * t ^ 6 + (89984869 / 1152000) * t ^ 8 + (129400183 / 2304000) * t ^ 10 + (-30243169 / 576000) * t ^ 12 + (-1789199 / 172800) * t ^ 14 + (-675353 / 6912000) * t ^ 18 + (5343433 / 3456000) * d * t ^ 6 + (-936091 / 230400) * d * t ^ 8 + (8266103 / 2304000) * d * t ^ 10 + (-719081 / 552960) * d * t ^ 12 + (2461807 / 10368000) * d * t ^ 14 + (272729 / 41472000) * d * t ^ 18 + (-58171 / 3456000) * d * t ^ 20 + (-1243 / 64800) * d ^ 2 * t ^ 8 + (14483 / 691200) * d ^ 2 * t ^ 10 + (37 / 24576) * d ^ 2 * t ^ 12 + (-16571 / 4147200) * d ^ 2 * t ^ 14 + (-95 / 663552) * d ^ 2 * t ^ 18 + (95 / 995328) * d ^ 2 * t ^ 20) * alpha_sq + ((-5003 / 18) * t ^ 2 + (14459 / 24) * t ^ 4 + (-19247849 / 46080) * t ^ 6 + (66740363 / 691200) * t ^ 8 + (-792179 / 92160) * t ^ 10 + (20968673 / 5529600) * t ^ 12 + (-358133 / 1382400) * t ^ 14 + (-15365 / 221184) * t ^ 18 + (-95 / 331776) * t ^ 20 + (3439 / 80) * alpha * t ^ 4 + (-96292651 / 1152000) * alpha * t ^ 6 + (32387573 / 768000) * alpha * t ^ 8 + (-4520141 / 2304000) * alpha * t ^ 10 + (1928681 / 6912000) * alpha * t ^ 12 + (25541 / 207360) * alpha * t ^ 14 + (472823 / 20736000) * alpha * t ^ 18) * d_sq
theorem v59_43 (t : ℂ) : (momentPoly 59 z59 4 3).eval t = (4683269 * t + (-584665719 / 40) * t ^ 3 + (524850872523 / 32000) * t ^ 5 + (-101897041343847 / 12800000) * t ^ 7 + (22994711917427 / 12800000) * t ^ 9 + (-24345034818427 / 76800000) * t ^ 11 + (42418856293 / 11520000) * t ^ 13 + (467600008757 / 38400000) * t ^ 15 + (-132582387097 / 51200000) * t ^ 17 + (-99487982041 / 230400000) * t ^ 19 + (14633389907 / 76800000) * t ^ 21 + (26032062191 / 460800000) * t ^ 25 + (-4683269 / 24) * d * t + (4892415 / 8) * d * t ^ 3 + (-4412123423 / 6400) * d * t ^ 5 + (512429414431 / 1536000) * d * t ^ 7 + (-36123821261 / 512000) * d * t ^ 9 + (168052929797 / 15360000) * d * t ^ 11 + (-6794290397 / 4608000) * d * t ^ 13 + (693986047 / 1536000) * d * t ^ 15 + (-18487657 / 3686400) * d * t ^ 17 + (74581687 / 5529600) * d * t ^ 19 + (-207221873 / 23040000) * d * t ^ 21 + (-854173 / 2211840) * d * t ^ 25 + (-4683269 / 24) * alpha * t + (-585123 / 40) * alpha * t ^ 3 + (7612089937 / 6400) * alpha * t ^ 5 + (-12344123678771 / 7680000) * alpha * t ^ 7 + (5301521711167 / 7680000) * alpha * t ^ 9 + (-209245630479 / 5120000) * alpha * t ^ 11 + (-48042681583 / 921600) * alpha * t ^ 13 + (14772170331 / 512000) * alpha * t ^ 15 + (132051973057 / 92160000) * alpha * t ^ 17 + (41450797049 / 138240000) * alpha * t ^ 19 + (-2734712771 / 11520000) * alpha * t ^ 21 + (1663909321 / 55296000) * alpha * t ^ 25 + (873587 / 40) * alpha * d * t ^ 3 + (-1204731943 / 19200) * alpha * d * t ^ 5 + (273539752987 / 4608000) * alpha * d * t ^ 7 + (-28265214881 / 1536000) * alpha * d * t ^ 9 + (3512963557 / 9216000) * alpha * d * t ^ 11 + (-255968131 / 864000) * alpha * d * t ^ 13 + (-190683061 / 1536000) * alpha * d * t ^ 15 + (-220543931 / 18432000) * alpha * d * t ^ 17 + (-126241423 / 9216000) * alpha * d * t ^ 19 + (105925459 / 9216000) * alpha * d * t ^ 21 + (821303 / 6144000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_03, v58_10, v58_11, v58_12, v58_13, v58_20, v58_21, v58_22, v58_23, v58_30, v58_31, v58_32, v58_33, v58_40, v58_41, v58_42, v58_43]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23, phase57_30, phase57_31, phase57_32, phase57_33, phase57_40, phase57_41, phase57_42, phase57_43]
  try simp only [star_one, star_neg]
  linear_combination ((873587 / 40) * t ^ 3 + (-94758029 / 1600) * t ^ 5 + (53808174889 / 1024000) * t ^ 7 + (-46133356067 / 3072000) * t ^ 9 + (6972027037 / 9216000) * t ^ 11 + (-4220397769 / 3456000) * t ^ 13 + (549123181 / 1536000) * t ^ 15 + (-693591613 / 18432000) * t ^ 17 + (-39102671 / 5184000) * t ^ 19 + (106954801 / 9216000) * t ^ 21 + (24802063 / 55296000) * t ^ 25 + (-1639 / 16) * d * t ^ 3 + (378967 / 3600) * d * t ^ 5 + (5277934147 / 27648000) * d * t ^ 7 + (-262330327 / 921600) * d * t ^ 9 + (726404701 / 9216000) * d * t ^ 11 + (623860477 / 33177600) * d * t ^ 13 + (-206215519 / 27648000) * d * t ^ 15 + (22075639 / 22118400) * d * t ^ 17 + (-7642739 / 55296000) * d * t ^ 19 + (-15992681 / 110592000) * d * t ^ 21 + (472511 / 19906560) * d * t ^ 25 + (-61721 / 11520) * d ^ 2 * t ^ 7 + (95235851 / 9216000) * d ^ 2 * t ^ 9 + (-143054291 / 27648000) * d ^ 2 * t ^ 11 + (4488941 / 18432000) * d ^ 2 * t ^ 13 + (-132917 / 3072000) * d ^ 2 * t ^ 15 + (-8357 / 1105920) * d ^ 2 * t ^ 17 + (-3439 / 442368) * d ^ 2 * t ^ 19 + (46597 / 10368000) * d ^ 2 * t ^ 21) * alpha_sq + ((-4917 / 2) * t ^ 3 + (19510693 / 3840) * t ^ 5 + (-27992888767 / 9216000) * t ^ 7 + (216383627 / 512000) * t ^ 9 + (-61825807 / 1843200) * t ^ 11 + (7536873 / 409600) * t ^ 13 + (7843669 / 9216000) * t ^ 15 + (8197 / 184320) * t ^ 17 + (-47497907 / 165888000) * t ^ 19 + (-360901 / 13824000) * t ^ 21 + (1639 / 16) * alpha * t ^ 3 + (-378967 / 3600) * alpha * t ^ 5 + (-2952150467 / 27648000) * alpha * t ^ 7 + (536973769 / 4608000) * alpha * t ^ 9 + (63453043 / 9216000) * alpha * t ^ 11 + (-860233471 / 55296000) * alpha * t ^ 13 + (10323139 / 5529600) * alpha * t ^ 15 + (-750583 / 22118400) * alpha * t ^ 17 + (470419 / 55296000) * alpha * t ^ 19 + (-16175 / 884736) * alpha * t ^ 21 + (-4465 / 3981312) * alpha * t ^ 25) * d_sq
theorem v59_44 (t : ℂ) : (momentPoly 59 z59 4 4).eval t = (276312871 + (-1040566920) * t ^ 2 + (586407831933 / 400) * t ^ 4 + (-37915070264323 / 40000) * t ^ 6 + (9874965948070419 / 32000000) * t ^ 8 + (-17645058159792701 / 192000000) * t ^ 10 + (751351101073269 / 25600000) * t ^ 12 + (-672431361274291 / 1152000000) * t ^ 14 + (1515298457209969 / 2304000000) * t ^ 16 + (-8109895686811 / 288000000) * t ^ 18 + (127130177420201 / 6912000000) * t ^ 20 + (1293959851207 / 144000000) * t ^ 22 + (-1360111255449 / 512000000) * t ^ 24 + (-348370512527 / 1152000000) * t ^ 26 + (1732277126783 / 13824000000) * t ^ 32 + (-4563890 / 3) * d * t ^ 2 + (381302383 / 80) * d * t ^ 4 + (-127036262423 / 24000) * d * t ^ 6 + (140274601399433 / 57600000) * d * t ^ 8 + (-5853052423059 / 12800000) * d * t ^ 10 + (17347595290177 / 230400000) * d * t ^ 12 + (-14526701331 / 5120000) * d * t ^ 14 + (-1486948988803 / 460800000) * d * t ^ 16 + (12799487759 / 19200000) * d * t ^ 18 + (141450968219 / 460800000) * d * t ^ 20 + (-849264161 / 19200000) * d * t ^ 22 + (-3662049 / 4096000) * d * t ^ 24 + (-15165304933 / 691200000) * d * t ^ 26 + (3295379 / 22118400) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z59, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v58_00, v58_01, v58_02, v58_03, v58_04, v58_10, v58_11, v58_12, v58_13, v58_14, v58_20, v58_21, v58_22, v58_23, v58_24, v58_30, v58_31, v58_32, v58_33, v58_34, v58_40, v58_41, v58_42, v58_43, v58_44]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24, phase57_30, phase57_31, phase57_32, phase57_33, phase57_34, phase57_40, phase57_41, phase57_42, phase57_43, phase57_44]
  try simp only [star_one, star_neg]
  linear_combination ((2281945 / 18) * t ^ 2 + (-32720611 / 240) * t ^ 4 + (-141080713 / 480) * t ^ 6 + (963039686657 / 1920000) * t ^ 8 + (-4913486423671 / 23040000) * t ^ 10 + (50936438953 / 3456000) * t ^ 12 + (249300583321 / 46080000) * t ^ 14 + (-149253761293 / 34560000) * t ^ 16 + (863540257 / 25920000) * t ^ 18 + (-941596957 / 1280000) * t ^ 20 + (344856129 / 5120000) * t ^ 22 + (-224845853 / 20736000) * t ^ 26 + (-3498187 / 240) * d * t ^ 4 + (691937941 / 14400) * d * t ^ 6 + (-197697864617 / 3456000) * d * t ^ 8 + (264456737261 / 9216000) * d * t ^ 10 + (-50049597199 / 9216000) * d * t ^ 12 + (6609038519 / 8294400) * d * t ^ 14 + (-2457005137 / 6912000) * d * t ^ 16 + (55353827 / 2304000) * d * t ^ 18 + (75283177 / 20736000) * d * t ^ 20 + (-14798881 / 3456000) * d * t ^ 22 + (-1220683 / 4096000) * d * t ^ 24 + (-19296191 / 49766400) * d * t ^ 26 + (3295379 / 66355200) * d * t ^ 32 + (-39107 / 1152) * d ^ 2 * t ^ 6 + (1521059 / 64800) * d ^ 2 * t ^ 8 + (1580840609 / 27648000) * d ^ 2 * t ^ 10 + (-1354285753 / 27648000) * d ^ 2 * t ^ 12 + (-10950593 / 4608000) * d ^ 2 * t ^ 14 + (145750691 / 27648000) * d ^ 2 * t ^ 16 + (-2771767 / 4147200) * d ^ 2 * t ^ 18 + (-23617 / 311040) * d ^ 2 * t ^ 20 + (1784507 / 20736000) * d ^ 2 * t ^ 22 + (15905 / 1769472) * d ^ 2 * t ^ 24 + (-314849 / 19906560) * d ^ 2 * t ^ 26 + (9025 / 47775744) * d ^ 2 * t ^ 32) * alpha_sq + ((-2281945 / 18) * t ^ 2 + (18302669 / 48) * t ^ 4 + (-1316210963 / 3200) * t ^ 6 + (655052419963 / 3456000) * t ^ 8 + (-117278343973 / 3072000) * t ^ 10 + (834783568007 / 138240000) * t ^ 12 + (-1089218213 / 1024000) * t ^ 14 + (11569178131 / 27648000) * t ^ 16 + (-9491959 / 1036800) * t ^ 18 + (3482701 / 256000) * t ^ 20 + (-636158257 / 138240000) * t ^ 22 + (-15905 / 589824) * t ^ 24 + (-3025727 / 6635520) * t ^ 26 + (-9025 / 15925248) * t ^ 32) * d_sq
#print axioms v59_00
#print axioms v59_11
#print axioms v59_22
#print axioms v59_33
#print axioms v59_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v60_02 (t : ℂ) : (momentPoly 60 z60 0 2).eval t = ((-99 / 8) * t ^ 2 + (107 / 8) * t ^ 4 + (171 / 40) * alpha * t ^ 2 + (-171 / 40) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02]
  try simp only [phase57_00, phase57_01, phase57_02]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 288) * t ^ 2) * alpha_sq + ((-1 / 288) * t ^ 2) * d_sq
theorem v60_03 (t : ℂ) : (momentPoly 60 z60 0 3).eval t = ((-281 / 8) * t ^ 3 + (273 / 8) * t ^ 5 + 2 * t ^ 9 + (937 / 50) * alpha * t ^ 3 + (-8679 / 400) * alpha * t ^ 5 + (1183 / 400) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_03]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03]
  try simp only [star_one, star_neg]
  linear_combination ((-523 / 960) * t ^ 3 + (171 / 320) * t ^ 5 + (1 / 1152) * d * t ^ 3 + (-1 / 1152) * d * t ^ 5) * alpha_sq + ((-1 / 96) * t ^ 3 + (-1 / 1152) * alpha * t ^ 3 + (1 / 1152) * alpha * t ^ 5) * d_sq
theorem v60_04 (t : ℂ) : (momentPoly 60 z60 0 4).eval t = ((369481 / 1600) * t ^ 4 + (-425681 / 800) * t ^ 6 + (1066187 / 3200) * t ^ 8 + (-4225 / 96) * t ^ 10 + (4993 / 384) * t ^ 16 + (-2523511 / 8000) * alpha * t ^ 4 + (2673431 / 4000) * alpha * t ^ 6 + (-5662541 / 16000) * alpha * t ^ 8 + (-31481 / 12000) * alpha * t ^ 10 + (173441 / 48000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_03, v59_04]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04]
  try simp only [star_one, star_neg]
  linear_combination ((-43051 / 14400) * t ^ 4 + (49849 / 14400) * t ^ 6 + (-46163 / 86400) * t ^ 10 + (533 / 5760) * d * t ^ 4 + (-523 / 2880) * d * t ^ 6 + (57 / 640) * d * t ^ 8 + (1 / 6912) * d ^ 2 * t ^ 6 + (-1 / 13824) * d ^ 2 * t ^ 8) * alpha_sq + ((125 / 576) * t ^ 4 + (-61 / 256) * t ^ 6 + (1 / 4608) * t ^ 8 + (-47 / 3456) * t ^ 10 + (-533 / 5760) * alpha * t ^ 4 + (533 / 5760) * alpha * t ^ 6) * d_sq
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
theorem v60_12 (t : ℂ) : (momentPoly 60 z60 1 2).eval t = (119 * t + (-1043 / 8) * t ^ 3 + (99 / 8) * t ^ 5 + (171 / 40) * alpha * t ^ 3 + (-171 / 40) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_10, v59_11, v59_12]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12]
  try simp only [star_one, star_neg]
  linear_combination ((523 / 2880) * t ^ 3 + (-57 / 320) * t ^ 5 + (-1 / 3456) * d * t ^ 3 + (1 / 3456) * d * t ^ 5) * alpha_sq + ((-1 / 96) * t ^ 3 + (-1 / 3456) * alpha * t ^ 3 + (1 / 3456) * alpha * t ^ 5) * d_sq
theorem v60_13 (t : ℂ) : (momentPoly 60 z60 1 3).eval t = ((-17523 / 8) * t ^ 2 + (35991 / 8) * t ^ 4 + (-18369 / 8) * t ^ 6 + (-91 / 8) * t ^ 10 + (30267 / 40) * alpha * t ^ 2 + (-74303 / 50) * alpha * t ^ 4 + (288861 / 400) * alpha * t ^ 6 + (2893 / 400) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_03, v59_10, v59_11, v59_12, v59_13]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13]
  try simp only [star_one, star_neg]
  linear_combination ((-59 / 96) * t ^ 2 + (84317 / 115200) * t ^ 4 + (-28913 / 115200) * t ^ 6 + (46163 / 345600) * t ^ 10) * alpha_sq + ((-59 / 96) * t ^ 2 + (3235 / 4608) * t ^ 4 + (-547 / 4608) * t ^ 6 + (-47 / 13824) * t ^ 10 + (-533 / 11520) * alpha * t ^ 4 + (533 / 11520) * alpha * t ^ 6) * d_sq
theorem v60_14 (t : ℂ) : (momentPoly 60 z60 1 4).eval t = ((-32877 / 4) * t ^ 3 + (26032281 / 1600) * t ^ 5 + (-6590681 / 800) * t ^ 7 + (2364587 / 3200) * t ^ 9 + (-53905 / 96) * t ^ 11 + (4225 / 384) * t ^ 17 + (109629 / 25) * alpha * t ^ 3 + (-77554431 / 8000) * alpha * t ^ 5 + (22358951 / 4000) * alpha * t ^ 7 + (6246619 / 16000) * alpha * t ^ 9 + (-8059961 / 12000) * alpha * t ^ 11 + (31481 / 48000) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_03, v59_04, v59_10, v59_11, v59_12, v59_13, v59_14]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14]
  try simp only [star_one, star_neg]
  linear_combination ((-20397 / 160) * t ^ 3 + (67221551 / 288000) * t ^ 5 + (-35001811 / 384000) * t ^ 7 + (-164263 / 12000) * t ^ 9 + (-123547 / 96000) * t ^ 11 + (173441 / 1152000) * t ^ 17 + (13 / 64) * d * t ^ 3 + (-3359 / 11520) * d * t ^ 5 + (-1073 / 46080) * d * t ^ 7 + (31049 / 276480) * d * t ^ 9 + (-47 / 41472) * d * t ^ 11 + (95 / 165888) * d * t ^ 17 + (533 / 138240) * d ^ 2 * t ^ 7 + (-523 / 138240) * d ^ 2 * t ^ 9) * alpha_sq + ((-39 / 16) * t ^ 3 + (23191 / 7680) * t ^ 5 + (-941 / 1440) * t ^ 7 + (259 / 11520) * t ^ 9 + (-95 / 1728) * t ^ 11 + (-13 / 64) * alpha * t ^ 3 + (10459 / 172800) * alpha * t ^ 5 + (12809 / 76800) * alpha * t ^ 7 + (1093 / 55296) * alpha * t ^ 9 + (-46163 / 1036800) * alpha * t ^ 11 + (95 / 165888) * alpha * t ^ 17) * d_sq
theorem v60_20 (t : ℂ) : (momentPoly 60 z60 2 0).eval t = ((-99 / 8) * t ^ 2 + (107 / 8) * t ^ 4 + (-171 / 40) * alpha * t ^ 2 + (171 / 40) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_10, v59_20]
  try simp only [phase57_00, phase57_10, phase57_20]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 288) * t ^ 2) * alpha_sq + ((-1 / 288) * t ^ 2) * d_sq
theorem v60_21 (t : ℂ) : (momentPoly 60 z60 2 1).eval t = (119 * t + (-1043 / 8) * t ^ 3 + (99 / 8) * t ^ 5 + (-171 / 40) * alpha * t ^ 3 + (171 / 40) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_10, v59_11, v59_20, v59_21]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21]
  try simp only [star_one, star_neg]
  linear_combination ((523 / 2880) * t ^ 3 + (-57 / 320) * t ^ 5 + (-1 / 3456) * d * t ^ 3 + (1 / 3456) * d * t ^ 5) * alpha_sq + ((-1 / 96) * t ^ 3 + (1 / 3456) * alpha * t ^ 3 + (-1 / 3456) * alpha * t ^ 5) * d_sq
theorem v60_22 (t : ℂ) : (momentPoly 60 z60 2 2).eval t = (7140 + (-13924) * t ^ 2 + (2726387 / 400) * t ^ 4 + (-40937 / 200) * t ^ 6 + (69487 / 400) * t ^ 8) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_10, v59_11, v59_12, v59_20, v59_21, v59_22]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22]
  try simp only [star_one, star_neg]
  linear_combination ((59 / 72) * t ^ 2 + (119 / 5760) * t ^ 4 + (-1573 / 1920) * t ^ 6 + (-533 / 17280) * d * t ^ 4 + (523 / 8640) * d * t ^ 6 + (-19 / 640) * d * t ^ 8 + (-1 / 20736) * d ^ 2 * t ^ 6 + (1 / 41472) * d ^ 2 * t ^ 8) * alpha_sq + ((-59 / 72) * t ^ 2 + (995 / 1152) * t ^ 4 + (-545 / 6912) * t ^ 6 + (-1 / 13824) * t ^ 8) * d_sq
theorem v60_23 (t : ℂ) : (momentPoly 60 z60 2 3).eval t = (21064 * t + (-366093 / 8) * t ^ 3 + (232797099 / 8000) * t ^ 5 + (-3134611 / 640) * t ^ 7 + (8329077 / 16000) * t ^ 9 + (-185121 / 16000) * t ^ 11 + (-194879 / 16000) * t ^ 13 + (60021 / 40) * alpha * t ^ 3 + (-4884597 / 1600) * alpha * t ^ 5 + (5351473 / 3200) * alpha * t ^ 7 + (-420783 / 3200) * alpha * t ^ 9 + (-117117 / 3200) * alpha * t ^ 11 + (153941 / 3200) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_03, v59_10, v59_11, v59_12, v59_13, v59_20, v59_21, v59_22, v59_23]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23]
  try simp only [star_one, star_neg]
  linear_combination ((20397 / 320) * t ^ 3 + (-7043213 / 57600) * t ^ 5 + (3339037 / 57600) * t ^ 7 + (792887 / 691200) * t ^ 11 + (-2717 / 5120) * t ^ 13 + (-13 / 128) * d * t ^ 3 + (15211 / 172800) * d * t ^ 5 + (37999 / 276480) * d * t ^ 7 + (-170483 / 1382400) * d * t ^ 9 + (-48563 / 4147200) * d * t ^ 11 + (46163 / 4147200) * d * t ^ 13 + (-533 / 138240) * d ^ 2 * t ^ 7 + (523 / 138240) * d ^ 2 * t ^ 9) * alpha_sq + ((-117 / 32) * t ^ 3 + (10153 / 2560) * t ^ 5 + (-483 / 1280) * t ^ 7 + (-259 / 11520) * t ^ 9 + (-95 / 6912) * t ^ 11 + (-13 / 128) * alpha * t ^ 3 + (15211 / 172800) * alpha * t ^ 5 + (33733 / 1382400) * alpha * t ^ 7 + (-1 / 55296) * alpha * t ^ 9 + (-43813 / 4147200) * alpha * t ^ 11 + (-47 / 165888) * alpha * t ^ 13) * d_sq
theorem v60_24 (t : ℂ) : (momentPoly 60 z60 2 4).eval t = ((-2050389 / 4) * t ^ 2 + (12344817 / 8) * t ^ 4 + (-245825153309 / 160000) * t ^ 6 + (80548571987 / 160000) * t ^ 8 + (-444612347 / 64000) * t ^ 10 + (3155021627 / 320000) * t ^ 12 + (-110398561 / 240000) * t ^ 14 + (-29381107 / 320000) * t ^ 18 + (109625821 / 960000) * t ^ 20 + (3541581 / 20) * alpha * t ^ 2 + (-103107013 / 200) * alpha * t ^ 4 + (15845514529 / 32000) * alpha * t ^ 6 + (-5034558791 / 32000) * alpha * t ^ 8 + (366625243 / 64000) * alpha * t ^ 10 + (-309698039 / 64000) * alpha * t ^ 12 + (-12924611 / 48000) * alpha * t ^ 14 + (-7345049 / 64000) * alpha * t ^ 18 + (20772431 / 192000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_03, v59_04, v59_10, v59_11, v59_12, v59_13, v59_14, v59_20, v59_21, v59_22, v59_23, v59_24]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24]
  try simp only [star_one, star_neg]
  linear_combination ((-20711 / 144) * t ^ 2 + (2445193 / 7200) * t ^ 4 + (-2218476737 / 6912000) * t ^ 6 + (16786901 / 128000) * t ^ 8 + (764494003 / 13824000) * t ^ 10 + (-7337701 / 144000) * t ^ 12 + (-3536713 / 345600) * t ^ 14 + (-51527 / 4608000) * t ^ 18 + (242629 / 256000) * d * t ^ 6 + (-5080411 / 1728000) * d * t ^ 8 + (1445269 / 460800) * d * t ^ 10 + (-241817 / 192000) * d * t ^ 12 + (591841 / 5184000) * d * t ^ 14 + (46597 / 2592000) * d * t ^ 18 + (-58171 / 3456000) * d * t ^ 20 + (-19963 / 2073600) * d ^ 2 * t ^ 8 + (14633 / 1382400) * d ^ 2 * t ^ 10 + (547 / 663552) * d ^ 2 * t ^ 12 + (-23669 / 12441600) * d ^ 2 * t ^ 14 + (-95 / 1990656) * d ^ 2 * t ^ 18 + (95 / 1990656) * d ^ 2 * t ^ 20) * alpha_sq + ((-20711 / 144) * t ^ 2 + (93815 / 288) * t ^ 4 + (-325109909 / 1382400) * t ^ 6 + (19363841 / 345600) * t ^ 8 + (-2747827 / 552960) * t ^ 10 + (1268749 / 614400) * t ^ 12 + (-595387 / 4147200) * t ^ 14 + (-25351 / 663552) * t ^ 18 + (-95 / 663552) * t ^ 20 + (-15457 / 720) * alpha * t ^ 4 + (295348003 / 6912000) * alpha * t ^ 6 + (-152963891 / 6912000) * alpha * t ^ 8 + (7451999 / 6912000) * alpha * t ^ 10 + (-5666543 / 41472000) * alpha * t ^ 12 + (-25541 / 414720) * alpha * t ^ 14 + (-472823 / 41472000) * alpha * t ^ 18) * d_sq
theorem v60_30 (t : ℂ) : (momentPoly 60 z60 3 0).eval t = ((-281 / 8) * t ^ 3 + (273 / 8) * t ^ 5 + 2 * t ^ 9 + (-937 / 50) * alpha * t ^ 3 + (8679 / 400) * alpha * t ^ 5 + (-1183 / 400) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_10, v59_20, v59_30]
  try simp only [phase57_00, phase57_10, phase57_20, phase57_30]
  try simp only [star_one, star_neg]
  linear_combination ((-523 / 960) * t ^ 3 + (171 / 320) * t ^ 5 + (1 / 1152) * d * t ^ 3 + (-1 / 1152) * d * t ^ 5) * alpha_sq + ((-1 / 96) * t ^ 3 + (1 / 1152) * alpha * t ^ 3 + (-1 / 1152) * alpha * t ^ 5) * d_sq
theorem v60_31 (t : ℂ) : (momentPoly 60 z60 3 1).eval t = ((-17523 / 8) * t ^ 2 + (35991 / 8) * t ^ 4 + (-18369 / 8) * t ^ 6 + (-91 / 8) * t ^ 10 + (-30267 / 40) * alpha * t ^ 2 + (74303 / 50) * alpha * t ^ 4 + (-288861 / 400) * alpha * t ^ 6 + (-2893 / 400) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_10, v59_11, v59_20, v59_21, v59_30, v59_31]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21, phase57_30, phase57_31]
  try simp only [star_one, star_neg]
  linear_combination ((-59 / 96) * t ^ 2 + (84317 / 115200) * t ^ 4 + (-28913 / 115200) * t ^ 6 + (46163 / 345600) * t ^ 10) * alpha_sq + ((-59 / 96) * t ^ 2 + (3235 / 4608) * t ^ 4 + (-547 / 4608) * t ^ 6 + (-47 / 13824) * t ^ 10 + (533 / 11520) * alpha * t ^ 4 + (-533 / 11520) * alpha * t ^ 6) * d_sq
theorem v60_32 (t : ℂ) : (momentPoly 60 z60 3 2).eval t = (21064 * t + (-366093 / 8) * t ^ 3 + (232797099 / 8000) * t ^ 5 + (-3134611 / 640) * t ^ 7 + (8329077 / 16000) * t ^ 9 + (-185121 / 16000) * t ^ 11 + (-194879 / 16000) * t ^ 13 + (-60021 / 40) * alpha * t ^ 3 + (4884597 / 1600) * alpha * t ^ 5 + (-5351473 / 3200) * alpha * t ^ 7 + (420783 / 3200) * alpha * t ^ 9 + (117117 / 3200) * alpha * t ^ 11 + (-153941 / 3200) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_10, v59_11, v59_12, v59_20, v59_21, v59_22, v59_30, v59_31, v59_32]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22, phase57_30, phase57_31, phase57_32]
  try simp only [star_one, star_neg]
  linear_combination ((20397 / 320) * t ^ 3 + (-7043213 / 57600) * t ^ 5 + (3339037 / 57600) * t ^ 7 + (792887 / 691200) * t ^ 11 + (-2717 / 5120) * t ^ 13 + (-13 / 128) * d * t ^ 3 + (15211 / 172800) * d * t ^ 5 + (37999 / 276480) * d * t ^ 7 + (-170483 / 1382400) * d * t ^ 9 + (-48563 / 4147200) * d * t ^ 11 + (46163 / 4147200) * d * t ^ 13 + (-533 / 138240) * d ^ 2 * t ^ 7 + (523 / 138240) * d ^ 2 * t ^ 9) * alpha_sq + ((-117 / 32) * t ^ 3 + (10153 / 2560) * t ^ 5 + (-483 / 1280) * t ^ 7 + (-259 / 11520) * t ^ 9 + (-95 / 6912) * t ^ 11 + (13 / 128) * alpha * t ^ 3 + (-15211 / 172800) * alpha * t ^ 5 + (-33733 / 1382400) * alpha * t ^ 7 + (1 / 55296) * alpha * t ^ 9 + (43813 / 4147200) * alpha * t ^ 11 + (47 / 165888) * alpha * t ^ 13) * d_sq
theorem v60_33 (t : ℂ) : (momentPoly 60 z60 3 3).eval t = (1263840 + (-3665847) * t ^ 2 + (711587007 / 200) * t ^ 4 + (-50454716663 / 40000) * t ^ 6 + (3847877637 / 20000) * t ^ 8 + (-13886801577 / 160000) * t ^ 10 + (8060963 / 10000) * t ^ 12 + (-74946171 / 80000) * t ^ 14 + (-4761533 / 160000) * t ^ 18) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_03, v59_10, v59_11, v59_12, v59_13, v59_20, v59_21, v59_22, v59_23, v59_30, v59_31, v59_32, v59_33]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23, phase57_30, phase57_31, phase57_32, phase57_33]
  try simp only [star_one, star_neg]
  linear_combination ((20711 / 96) * t ^ 2 + (3451 / 320) * t ^ 4 + (-100193669 / 153600) * t ^ 6 + (11487573 / 25600) * t ^ 8 + (-2051861 / 76800) * t ^ 10 + (-9172601 / 2764800) * t ^ 12 + (18061487 / 2764800) * t ^ 14 + (12691393 / 16588800) * t ^ 18 + (-15457 / 960) * d * t ^ 4 + (21621851 / 460800) * d * t ^ 6 + (-8699 / 192) * d * t ^ 8 + (6676709 / 460800) * d * t ^ 10 + (-169283 / 691200) * d * t ^ 12 + (166883 / 691200) * d * t ^ 14 + (-175 / 6912) * d ^ 2 * t ^ 6 + (6361 / 691200) * d ^ 2 * t ^ 8 + (8509 / 460800) * d ^ 2 * t ^ 10 + (-3749 / 1382400) * d ^ 2 * t ^ 14) * alpha_sq + ((-20711 / 96) * t ^ 2 + (28855 / 64) * t ^ 4 + (-126597313 / 460800) * t ^ 6 + (4980631 / 115200) * t ^ 8 + (-210279 / 51200) * t ^ 10 + (1082537 / 2764800) * t ^ 12 + (-597737 / 2764800) * t ^ 14 + (-2209 / 663552) * t ^ 18) * d_sq
theorem v60_34 (t : ℂ) : (momentPoly 60 z60 3 4).eval t = (4929687 * t + (-63709569 / 4) * t ^ 3 + (14874910731 / 800) * t ^ 5 + (-15115545930809 / 1600000) * t ^ 7 + (7052836268513 / 3200000) * t ^ 9 + (-1207946991173 / 3200000) * t ^ 11 + (69427326631 / 3840000) * t ^ 13 + (3790599867 / 400000) * t ^ 15 + (-16306810009 / 6400000) * t ^ 17 + (-1655810753 / 3200000) * t ^ 19 + (1330729111 / 6400000) * t ^ 21 + (1095642109 / 19200000) * t ^ 25 + (10445193 / 20) * alpha * t ^ 3 + (-254951037 / 160) * alpha * t ^ 5 + (542403492367 / 320000) * alpha * t ^ 7 + (-451878726099 / 640000) * alpha * t ^ 9 + (35850506691 / 640000) * alpha * t ^ 11 + (74395354757 / 1280000) * alpha * t ^ 13 + (-2412056513 / 80000) * alpha * t ^ 15 + (-2134473781 / 1280000) * alpha * t ^ 17 + (-25213667 / 76800) * alpha * t ^ 19 + (70127367 / 256000) * alpha * t ^ 21 + (-23983483 / 768000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_03, v59_04, v59_10, v59_11, v59_12, v59_13, v59_14, v59_20, v59_21, v59_22, v59_23, v59_24, v59_30, v59_31, v59_32, v59_33, v59_34]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24, phase57_30, phase57_31, phase57_32, phase57_33, phase57_34]
  try simp only [star_one, star_neg]
  linear_combination ((3549601 / 160) * t ^ 3 + (-120950821 / 1920) * t ^ 5 + (108528934607 / 1843200) * t ^ 7 + (-36979889303 / 2048000) * t ^ 9 + (8759067913 / 9216000) * t ^ 11 + (-145625179439 / 110592000) * t ^ 13 + (21596942359 / 55296000) * t ^ 15 + (-23489609 / 576000) * t ^ 17 + (-3227372239 / 331776000) * t ^ 19 + (231589387 / 18432000) * t ^ 21 + (24802063 / 55296000) * t ^ 25 + (-6787 / 192) * d * t ^ 3 + (24973 / 960) * d * t ^ 5 + (3911518681 / 27648000) * d * t ^ 7 + (-6159992903 / 27648000) * d * t ^ 9 + (96792301 / 1105920) * d * t ^ 11 + (105208531 / 10368000) * d * t ^ 13 + (-145289521 / 18432000) * d * t ^ 15 + (66592127 / 66355200) * d * t ^ 17 + (-12885101 / 995328000) * d * t ^ 19 + (-46168793 / 331776000) * d * t ^ 21 + (877097 / 39813120) * d * t ^ 25 + (-184951 / 69120) * d ^ 2 * t ^ 7 + (292129603 / 55296000) * d ^ 2 * t ^ 9 + (-75067183 / 27648000) * d ^ 2 * t ^ 11 + (14747423 / 110592000) * d ^ 2 * t ^ 13 + (-3517259 / 165888000) * d ^ 2 * t ^ 15 + (-8357 / 2211840) * d ^ 2 * t ^ 17 + (-10127 / 2654208) * d ^ 2 * t ^ 19 + (46597 / 20736000) * d ^ 2 * t ^ 21) * alpha_sq + ((-20361 / 16) * t ^ 3 + (700557 / 256) * t ^ 5 + (-3165974417 / 1843200) * t ^ 7 + (2413645001 / 9216000) * t ^ 9 + (-20125663 / 1024000) * t ^ 11 + (290784937 / 27648000) * t ^ 13 + (1388533 / 13824000) * t ^ 15 + (8197 / 368640) * t ^ 17 + (-12348047 / 82944000) * t ^ 19 + (-360901 / 27648000) * t ^ 21 + (-6787 / 192) * alpha * t ^ 3 + (24973 / 960) * alpha * t ^ 5 + (1742602121 / 27648000) * alpha * t ^ 7 + (-1598214427 / 27648000) * alpha * t ^ 9 + (-84880807 / 27648000) * alpha * t ^ 11 + (56064661 / 6912000) * alpha * t ^ 13 + (-2087299 / 2211840) * alpha * t ^ 15 + (1239287 / 66355200) * alpha * t ^ 17 + (-13565021 / 995328000) * alpha * t ^ 19 + (26519 / 2654208) * alpha * t ^ 21 + (4465 / 7962624) * alpha * t ^ 25) * d_sq
theorem v60_40 (t : ℂ) : (momentPoly 60 z60 4 0).eval t = ((369481 / 1600) * t ^ 4 + (-425681 / 800) * t ^ 6 + (1066187 / 3200) * t ^ 8 + (-4225 / 96) * t ^ 10 + (4993 / 384) * t ^ 16 + (2523511 / 8000) * alpha * t ^ 4 + (-2673431 / 4000) * alpha * t ^ 6 + (5662541 / 16000) * alpha * t ^ 8 + (31481 / 12000) * alpha * t ^ 10 + (-173441 / 48000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_10, v59_20, v59_30, v59_40]
  try simp only [phase57_00, phase57_10, phase57_20, phase57_30, phase57_40]
  try simp only [star_one, star_neg]
  linear_combination ((-43051 / 14400) * t ^ 4 + (49849 / 14400) * t ^ 6 + (-46163 / 86400) * t ^ 10 + (533 / 5760) * d * t ^ 4 + (-523 / 2880) * d * t ^ 6 + (57 / 640) * d * t ^ 8 + (1 / 6912) * d ^ 2 * t ^ 6 + (-1 / 13824) * d ^ 2 * t ^ 8) * alpha_sq + ((125 / 576) * t ^ 4 + (-61 / 256) * t ^ 6 + (1 / 4608) * t ^ 8 + (-47 / 3456) * t ^ 10 + (533 / 5760) * alpha * t ^ 4 + (-533 / 5760) * alpha * t ^ 6) * d_sq
theorem v60_41 (t : ℂ) : (momentPoly 60 z60 4 1).eval t = ((-32877 / 4) * t ^ 3 + (26032281 / 1600) * t ^ 5 + (-6590681 / 800) * t ^ 7 + (2364587 / 3200) * t ^ 9 + (-53905 / 96) * t ^ 11 + (4225 / 384) * t ^ 17 + (-109629 / 25) * alpha * t ^ 3 + (77554431 / 8000) * alpha * t ^ 5 + (-22358951 / 4000) * alpha * t ^ 7 + (-6246619 / 16000) * alpha * t ^ 9 + (8059961 / 12000) * alpha * t ^ 11 + (-31481 / 48000) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_10, v59_11, v59_20, v59_21, v59_30, v59_31, v59_40, v59_41]
  try simp only [phase57_00, phase57_01, phase57_10, phase57_11, phase57_20, phase57_21, phase57_30, phase57_31, phase57_40, phase57_41]
  try simp only [star_one, star_neg]
  linear_combination ((-20397 / 160) * t ^ 3 + (67221551 / 288000) * t ^ 5 + (-35001811 / 384000) * t ^ 7 + (-164263 / 12000) * t ^ 9 + (-123547 / 96000) * t ^ 11 + (173441 / 1152000) * t ^ 17 + (13 / 64) * d * t ^ 3 + (-3359 / 11520) * d * t ^ 5 + (-1073 / 46080) * d * t ^ 7 + (31049 / 276480) * d * t ^ 9 + (-47 / 41472) * d * t ^ 11 + (95 / 165888) * d * t ^ 17 + (533 / 138240) * d ^ 2 * t ^ 7 + (-523 / 138240) * d ^ 2 * t ^ 9) * alpha_sq + ((-39 / 16) * t ^ 3 + (23191 / 7680) * t ^ 5 + (-941 / 1440) * t ^ 7 + (259 / 11520) * t ^ 9 + (-95 / 1728) * t ^ 11 + (13 / 64) * alpha * t ^ 3 + (-10459 / 172800) * alpha * t ^ 5 + (-12809 / 76800) * alpha * t ^ 7 + (-1093 / 55296) * alpha * t ^ 9 + (46163 / 1036800) * alpha * t ^ 11 + (-95 / 165888) * alpha * t ^ 17) * d_sq
theorem v60_42 (t : ℂ) : (momentPoly 60 z60 4 2).eval t = ((-2050389 / 4) * t ^ 2 + (12344817 / 8) * t ^ 4 + (-245825153309 / 160000) * t ^ 6 + (80548571987 / 160000) * t ^ 8 + (-444612347 / 64000) * t ^ 10 + (3155021627 / 320000) * t ^ 12 + (-110398561 / 240000) * t ^ 14 + (-29381107 / 320000) * t ^ 18 + (109625821 / 960000) * t ^ 20 + (-3541581 / 20) * alpha * t ^ 2 + (103107013 / 200) * alpha * t ^ 4 + (-15845514529 / 32000) * alpha * t ^ 6 + (5034558791 / 32000) * alpha * t ^ 8 + (-366625243 / 64000) * alpha * t ^ 10 + (309698039 / 64000) * alpha * t ^ 12 + (12924611 / 48000) * alpha * t ^ 14 + (7345049 / 64000) * alpha * t ^ 18 + (-20772431 / 192000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_10, v59_11, v59_12, v59_20, v59_21, v59_22, v59_30, v59_31, v59_32, v59_40, v59_41, v59_42]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_10, phase57_11, phase57_12, phase57_20, phase57_21, phase57_22, phase57_30, phase57_31, phase57_32, phase57_40, phase57_41, phase57_42]
  try simp only [star_one, star_neg]
  linear_combination ((-20711 / 144) * t ^ 2 + (2445193 / 7200) * t ^ 4 + (-2218476737 / 6912000) * t ^ 6 + (16786901 / 128000) * t ^ 8 + (764494003 / 13824000) * t ^ 10 + (-7337701 / 144000) * t ^ 12 + (-3536713 / 345600) * t ^ 14 + (-51527 / 4608000) * t ^ 18 + (242629 / 256000) * d * t ^ 6 + (-5080411 / 1728000) * d * t ^ 8 + (1445269 / 460800) * d * t ^ 10 + (-241817 / 192000) * d * t ^ 12 + (591841 / 5184000) * d * t ^ 14 + (46597 / 2592000) * d * t ^ 18 + (-58171 / 3456000) * d * t ^ 20 + (-19963 / 2073600) * d ^ 2 * t ^ 8 + (14633 / 1382400) * d ^ 2 * t ^ 10 + (547 / 663552) * d ^ 2 * t ^ 12 + (-23669 / 12441600) * d ^ 2 * t ^ 14 + (-95 / 1990656) * d ^ 2 * t ^ 18 + (95 / 1990656) * d ^ 2 * t ^ 20) * alpha_sq + ((-20711 / 144) * t ^ 2 + (93815 / 288) * t ^ 4 + (-325109909 / 1382400) * t ^ 6 + (19363841 / 345600) * t ^ 8 + (-2747827 / 552960) * t ^ 10 + (1268749 / 614400) * t ^ 12 + (-595387 / 4147200) * t ^ 14 + (-25351 / 663552) * t ^ 18 + (-95 / 663552) * t ^ 20 + (15457 / 720) * alpha * t ^ 4 + (-295348003 / 6912000) * alpha * t ^ 6 + (152963891 / 6912000) * alpha * t ^ 8 + (-7451999 / 6912000) * alpha * t ^ 10 + (5666543 / 41472000) * alpha * t ^ 12 + (25541 / 414720) * alpha * t ^ 14 + (472823 / 41472000) * alpha * t ^ 18) * d_sq
theorem v60_43 (t : ℂ) : (momentPoly 60 z60 4 3).eval t = (4929687 * t + (-63709569 / 4) * t ^ 3 + (14874910731 / 800) * t ^ 5 + (-15115545930809 / 1600000) * t ^ 7 + (7052836268513 / 3200000) * t ^ 9 + (-1207946991173 / 3200000) * t ^ 11 + (69427326631 / 3840000) * t ^ 13 + (3790599867 / 400000) * t ^ 15 + (-16306810009 / 6400000) * t ^ 17 + (-1655810753 / 3200000) * t ^ 19 + (1330729111 / 6400000) * t ^ 21 + (1095642109 / 19200000) * t ^ 25 + (-10445193 / 20) * alpha * t ^ 3 + (254951037 / 160) * alpha * t ^ 5 + (-542403492367 / 320000) * alpha * t ^ 7 + (451878726099 / 640000) * alpha * t ^ 9 + (-35850506691 / 640000) * alpha * t ^ 11 + (-74395354757 / 1280000) * alpha * t ^ 13 + (2412056513 / 80000) * alpha * t ^ 15 + (2134473781 / 1280000) * alpha * t ^ 17 + (25213667 / 76800) * alpha * t ^ 19 + (-70127367 / 256000) * alpha * t ^ 21 + (23983483 / 768000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_03, v59_10, v59_11, v59_12, v59_13, v59_20, v59_21, v59_22, v59_23, v59_30, v59_31, v59_32, v59_33, v59_40, v59_41, v59_42, v59_43]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_10, phase57_11, phase57_12, phase57_13, phase57_20, phase57_21, phase57_22, phase57_23, phase57_30, phase57_31, phase57_32, phase57_33, phase57_40, phase57_41, phase57_42, phase57_43]
  try simp only [star_one, star_neg]
  linear_combination ((3549601 / 160) * t ^ 3 + (-120950821 / 1920) * t ^ 5 + (108528934607 / 1843200) * t ^ 7 + (-36979889303 / 2048000) * t ^ 9 + (8759067913 / 9216000) * t ^ 11 + (-145625179439 / 110592000) * t ^ 13 + (21596942359 / 55296000) * t ^ 15 + (-23489609 / 576000) * t ^ 17 + (-3227372239 / 331776000) * t ^ 19 + (231589387 / 18432000) * t ^ 21 + (24802063 / 55296000) * t ^ 25 + (-6787 / 192) * d * t ^ 3 + (24973 / 960) * d * t ^ 5 + (3911518681 / 27648000) * d * t ^ 7 + (-6159992903 / 27648000) * d * t ^ 9 + (96792301 / 1105920) * d * t ^ 11 + (105208531 / 10368000) * d * t ^ 13 + (-145289521 / 18432000) * d * t ^ 15 + (66592127 / 66355200) * d * t ^ 17 + (-12885101 / 995328000) * d * t ^ 19 + (-46168793 / 331776000) * d * t ^ 21 + (877097 / 39813120) * d * t ^ 25 + (-184951 / 69120) * d ^ 2 * t ^ 7 + (292129603 / 55296000) * d ^ 2 * t ^ 9 + (-75067183 / 27648000) * d ^ 2 * t ^ 11 + (14747423 / 110592000) * d ^ 2 * t ^ 13 + (-3517259 / 165888000) * d ^ 2 * t ^ 15 + (-8357 / 2211840) * d ^ 2 * t ^ 17 + (-10127 / 2654208) * d ^ 2 * t ^ 19 + (46597 / 20736000) * d ^ 2 * t ^ 21) * alpha_sq + ((-20361 / 16) * t ^ 3 + (700557 / 256) * t ^ 5 + (-3165974417 / 1843200) * t ^ 7 + (2413645001 / 9216000) * t ^ 9 + (-20125663 / 1024000) * t ^ 11 + (290784937 / 27648000) * t ^ 13 + (1388533 / 13824000) * t ^ 15 + (8197 / 368640) * t ^ 17 + (-12348047 / 82944000) * t ^ 19 + (-360901 / 27648000) * t ^ 21 + (6787 / 192) * alpha * t ^ 3 + (-24973 / 960) * alpha * t ^ 5 + (-1742602121 / 27648000) * alpha * t ^ 7 + (1598214427 / 27648000) * alpha * t ^ 9 + (84880807 / 27648000) * alpha * t ^ 11 + (-56064661 / 6912000) * alpha * t ^ 13 + (2087299 / 2211840) * alpha * t ^ 15 + (-1239287 / 66355200) * alpha * t ^ 17 + (13565021 / 995328000) * alpha * t ^ 19 + (-26519 / 2654208) * alpha * t ^ 21 + (-4465 / 7962624) * alpha * t ^ 25) * d_sq
theorem v60_44 (t : ℂ) : (momentPoly 60 z60 4 4).eval t = (295781220 + (-1134245736) * t ^ 2 + (81848864127 / 50) * t ^ 4 + (-1377611634633 / 1250) * t ^ 6 + (6217380134993047 / 16000000) * t ^ 8 + (-486020114884337 / 4000000) * t ^ 10 + (117281223336003 / 3200000) * t ^ 12 + (-25202700720017 / 24000000) * t ^ 14 + (173064446591737 / 192000000) * t ^ 16 + (-872935034603 / 24000000) * t ^ 18 + (3721754313787 / 144000000) * t ^ 20 + (135074262097 / 24000000) * t ^ 22 + (-104917688467 / 96000000) * t ^ 24 + (-35373557197 / 72000000) * t ^ 26 + (85384339267 / 576000000) * t ^ 32) := by
  rw [momentPoly]
  simp only [z60, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v59_00, v59_01, v59_02, v59_03, v59_04, v59_10, v59_11, v59_12, v59_13, v59_14, v59_20, v59_21, v59_22, v59_23, v59_24, v59_30, v59_31, v59_32, v59_33, v59_34, v59_40, v59_41, v59_42, v59_43, v59_44]
  try simp only [phase57_00, phase57_01, phase57_02, phase57_03, phase57_04, phase57_10, phase57_11, phase57_12, phase57_13, phase57_14, phase57_20, phase57_21, phase57_22, phase57_23, phase57_24, phase57_30, phase57_31, phase57_32, phase57_33, phase57_34, phase57_40, phase57_41, phase57_42, phase57_43, phase57_44]
  try simp only [star_one, star_neg]
  linear_combination ((267007 / 4) * t ^ 2 + (1190833 / 240) * t ^ 4 + (-1285317681 / 3200) * t ^ 6 + (12426834204371 / 23040000) * t ^ 8 + (-5306446177567 / 23040000) * t ^ 10 + (814486024237 / 46080000) * t ^ 12 + (703674644009 / 82944000) * t ^ 14 + (-3447950179 / 768000) * t ^ 16 + (-8693039071 / 138240000) * t ^ 18 + (-35465339491 / 46080000) * t ^ 20 + (2734712771 / 34560000) * t ^ 22 + (-421503601 / 41472000) * t ^ 26 + (-5333731 / 720) * d * t ^ 4 + (821252447 / 28800) * d * t ^ 6 + (-564332078267 / 13824000) * d * t ^ 8 + (711166815281 / 27648000) * d * t ^ 10 + (-346934932361 / 55296000) * d * t ^ 12 + (1509659509 / 2764800) * d * t ^ 14 + (-31579589741 / 110592000) * d * t ^ 16 + (59427659 / 8294400) * d * t ^ 18 + (-7014379 / 24883200) * d * t ^ 20 + (-552577 / 20736000) * d * t ^ 22 + (-18090373 / 55296000) * d * t ^ 24 + (-1318163 / 6220800) * d * t ^ 26 + (3295379 / 66355200) * d * t ^ 32 + (-40489 / 3456) * d ^ 2 * t ^ 6 + (696709 / 259200) * d ^ 2 * t ^ 8 + (99539363 / 3072000) * d ^ 2 * t ^ 10 + (-1367842523 / 55296000) * d ^ 2 * t ^ 12 + (-41971301 / 41472000) * d ^ 2 * t ^ 14 + (900002501 / 331776000) * d ^ 2 * t ^ 16 + (-5687713 / 16588800) * d ^ 2 * t ^ 18 + (-379297 / 9953280) * d ^ 2 * t ^ 20 + (13506431 / 331776000) * d ^ 2 * t ^ 22 + (78389 / 15925248) * d ^ 2 * t ^ 24 + (-449711 / 59719680) * d ^ 2 * t ^ 26 + (9025 / 95551488) * d ^ 2 * t ^ 32) * alpha_sq + ((-267007 / 4) * t ^ 2 + (9956965 / 48) * t ^ 4 + (-3340217233 / 14400) * t ^ 6 + (1541961228893 / 13824000) * t ^ 8 + (-24215277697 / 1024000) * t ^ 10 + (117400971803 / 30720000) * t ^ 12 + (-57430509521 / 82944000) * t ^ 14 + (1019249841 / 4096000) * t ^ 16 + (-1153843 / 184320) * t ^ 18 + (23917087 / 2764800) * t ^ 20 + (-1725307139 / 552960000) * t ^ 22 + (-78389 / 5308416) * t ^ 24 + (-5102713 / 19906560) * t ^ 26 + (-9025 / 31850496) * t ^ 32) * d_sq
#print axioms v60_00
#print axioms v60_11
#print axioms v60_22
#print axioms v60_33
#print axioms v60_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v61_02 (t : ℂ) : (momentPoly 61 z61 0 2).eval t = ((-115 / 8) * t ^ 2 + (115 / 8) * t ^ 4 + (171 / 40) * alpha * t ^ 2 + (-171 / 40) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02]
  try simp only [phase61_00, phase61_01, phase61_02]
  try simp only [star_one, star_neg]
  ring
theorem v61_03 (t : ℂ) : (momentPoly 61 z61 0 3).eval t = (2 * t ^ 3 + (-3) * t ^ 5 + 1 * t ^ 9 + (1183 / 200) * alpha * t ^ 3 + (-3549 / 400) * alpha * t ^ 5 + (1183 / 400) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_03]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03]
  try simp only [star_one, star_neg]
  ring
theorem v61_04 (t : ℂ) : (momentPoly 61 z61 0 4).eval t = ((594281 / 1600) * t ^ 4 + (-594281 / 800) * t ^ 6 + (1322987 / 3200) * t ^ 8 + (-5377 / 96) * t ^ 10 + (5377 / 384) * t ^ 16 + (-3123191 / 8000) * alpha * t ^ 4 + (3123191 / 4000) * alpha * t ^ 6 + (-6072941 / 16000) * alpha * t ^ 8 + (-173441 / 12000) * alpha * t ^ 10 + (173441 / 48000) * alpha * t ^ 16) := by
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
theorem v61_13 (t : ℂ) : (momentPoly 61 z61 1 3).eval t = ((-5175 / 2) * t ^ 2 + (20585 / 4) * t ^ 4 + (-20355 / 8) * t ^ 6 + (-115 / 8) * t ^ 10 + (1539 / 2) * alpha * t ^ 2 + (-30609 / 20) * alpha * t ^ 4 + (30267 / 40) * alpha * t ^ 6 + (171 / 40) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_03, v60_10, v60_11, v60_12, v60_13]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_10, phase61_11, phase61_12, phase61_13]
  try simp only [star_one, star_neg]
  ring
theorem v61_14 (t : ℂ) : (momentPoly 61 z61 1 4).eval t = (476 * t ^ 3 + (-1182) * t ^ 5 + 696 * t ^ 7 + 247 * t ^ 9 + (-236) * t ^ 11 + (-1) * t ^ 17 + (140777 / 100) * alpha * t ^ 3 + (-699153 / 200) * alpha * t ^ 5 + (102921 / 50) * alpha * t ^ 7 + (292201 / 400) * alpha * t ^ 9 + (-69797 / 100) * alpha * t ^ 11 + (-1183 / 400) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_03, v60_04, v60_10, v60_11, v60_12, v60_13, v60_14]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_04, phase61_10, phase61_11, phase61_12, phase61_13, phase61_14]
  try simp only [star_one, star_neg]
  ring
theorem v61_20 (t : ℂ) : (momentPoly 61 z61 2 0).eval t = ((-115 / 8) * t ^ 2 + (115 / 8) * t ^ 4 + (-171 / 40) * alpha * t ^ 2 + (171 / 40) * alpha * t ^ 4) := by
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
theorem v61_22 (t : ℂ) : (momentPoly 61 z61 2 2).eval t = (7381 + (-14640) * t ^ 2 + (2934987 / 400) * t ^ 4 + (-55787 / 200) * t ^ 6 + (80187 / 400) * t ^ 8) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_10, v60_11, v60_12, v60_20, v60_21, v60_22]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_10, phase61_11, phase61_12, phase61_20, phase61_21, phase61_22]
  try simp only [star_one, star_neg]
  ring
theorem v61_23 (t : ℂ) : (momentPoly 61 z61 2 3).eval t = ((376879 / 8000) * t ^ 5 + (-376879 / 3200) * t ^ 7 + (1130637 / 16000) * t ^ 9 + (376879 / 16000) * t ^ 11 + (-376879 / 16000) * t ^ 13 + (-5989 / 64) * alpha * t ^ 5 + (29945 / 128) * alpha * t ^ 7 + (-17967 / 128) * alpha * t ^ 9 + (-5989 / 128) * alpha * t ^ 11 + (5989 / 128) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_03, v60_10, v60_11, v60_12, v60_13, v60_20, v60_21, v60_22, v60_23]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_10, phase61_11, phase61_12, phase61_13, phase61_20, phase61_21, phase61_22, phase61_23]
  try simp only [star_one, star_neg]
  ring
theorem v61_24 (t : ℂ) : (momentPoly 61 z61 2 4).eval t = ((-1231765 / 2) * t ^ 2 + (14589475 / 8) * t ^ 4 + (-286082577429 / 160000) * t ^ 6 + (92899732287 / 160000) * t ^ 8 + (-822042579 / 64000) * t ^ 10 + (12408702821 / 960000) * t ^ 12 + (-121148321 / 240000) * t ^ 14 + (-121148321 / 960000) * t ^ 18 + (134948321 / 960000) * t ^ 20 + (1831581 / 10) * alpha * t ^ 2 + (-4338783 / 8) * alpha * t ^ 4 + (17046007657 / 32000) * alpha * t ^ 6 + (-5616454971 / 32000) * alpha * t ^ 8 + (396035747 / 64000) * alpha * t ^ 10 + (-707734577 / 192000) * alpha * t ^ 12 + (-4621559 / 9600) * alpha * t ^ 14 + (-4621559 / 38400) * alpha * t ^ 18 + (4457399 / 38400) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_03, v60_04, v60_10, v60_11, v60_12, v60_13, v60_14, v60_20, v60_21, v60_22, v60_23, v60_24]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_04, phase61_10, phase61_11, phase61_12, phase61_13, phase61_14, phase61_20, phase61_21, phase61_22, phase61_23, phase61_24]
  try simp only [star_one, star_neg]
  ring
theorem v61_30 (t : ℂ) : (momentPoly 61 z61 3 0).eval t = (2 * t ^ 3 + (-3) * t ^ 5 + 1 * t ^ 9 + (-1183 / 200) * alpha * t ^ 3 + (3549 / 400) * alpha * t ^ 5 + (-1183 / 400) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_10, v60_20, v60_30]
  try simp only [phase61_00, phase61_10, phase61_20, phase61_30]
  try simp only [star_one, star_neg]
  ring
theorem v61_31 (t : ℂ) : (momentPoly 61 z61 3 1).eval t = ((-5175 / 2) * t ^ 2 + (20585 / 4) * t ^ 4 + (-20355 / 8) * t ^ 6 + (-115 / 8) * t ^ 10 + (-1539 / 2) * alpha * t ^ 2 + (30609 / 20) * alpha * t ^ 4 + (-30267 / 40) * alpha * t ^ 6 + (-171 / 40) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_10, v60_11, v60_20, v60_21, v60_30, v60_31]
  try simp only [phase61_00, phase61_01, phase61_10, phase61_11, phase61_20, phase61_21, phase61_30, phase61_31]
  try simp only [star_one, star_neg]
  ring
theorem v61_32 (t : ℂ) : (momentPoly 61 z61 3 2).eval t = ((376879 / 8000) * t ^ 5 + (-376879 / 3200) * t ^ 7 + (1130637 / 16000) * t ^ 9 + (376879 / 16000) * t ^ 11 + (-376879 / 16000) * t ^ 13 + (5989 / 64) * alpha * t ^ 5 + (-29945 / 128) * alpha * t ^ 7 + (17967 / 128) * alpha * t ^ 9 + (5989 / 128) * alpha * t ^ 11 + (-5989 / 128) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_10, v60_11, v60_12, v60_20, v60_21, v60_22, v60_30, v60_31, v60_32]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_10, phase61_11, phase61_12, phase61_20, phase61_21, phase61_22, phase61_30, phase61_31, phase61_32]
  try simp only [star_one, star_neg]
  ring
theorem v61_33 (t : ℂ) : (momentPoly 61 z61 3 3).eval t = (1328641 + (-3920226) * t ^ 2 + (1558478097 / 400) * t ^ 4 + (-58049886233 / 40000) * t ^ 6 + (10016712699 / 40000) * t ^ 8 + (-16590826197 / 160000) * t ^ 10 + (37830667 / 40000) * t ^ 12 + (-80019801 / 80000) * t ^ 14 + (-5401533 / 160000) * t ^ 18) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_03, v60_10, v60_11, v60_12, v60_13, v60_20, v60_21, v60_22, v60_23, v60_30, v60_31, v60_32, v60_33]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_10, phase61_11, phase61_12, phase61_13, phase61_20, phase61_21, phase61_22, phase61_23, phase61_30, phase61_31, phase61_32, phase61_33]
  try simp only [star_one, star_neg]
  ring
theorem v61_34 (t : ℂ) : (momentPoly 61 z61 3 4).eval t = ((132284529 / 4000) * t ^ 5 + (-193586467459 / 1600000) * t ^ 7 + (483082642013 / 3200000) * t ^ 9 + (-175289405363 / 3200000) * t ^ 11 + (-106702792949 / 3840000) * t ^ 13 + (4513287971 / 200000) * t ^ 15 + (-18906893609 / 6400000) * t ^ 17 + (-658264709 / 9600000) * t ^ 19 + (-432137309 / 6400000) * t ^ 21 + (884392109 / 19200000) * t ^ 25 + (-2102139 / 32) * alpha * t ^ 5 + (72023075297 / 320000) * alpha * t ^ 7 + (-157727822079 / 640000) * alpha * t ^ 9 + (30770947881 / 640000) * alpha * t ^ 11 + (89019082617 / 1280000) * alpha * t ^ 13 + (-578361237 / 20000) * alpha * t ^ 15 + (-2050928901 / 1280000) * alpha * t ^ 17 + (3687633 / 128000) * alpha * t ^ 19 + (-6904101 / 256000) * alpha * t ^ 21 + (-9676633 / 256000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_03, v60_04, v60_10, v60_11, v60_12, v60_13, v60_14, v60_20, v60_21, v60_22, v60_23, v60_24, v60_30, v60_31, v60_32, v60_33, v60_34]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_04, phase61_10, phase61_11, phase61_12, phase61_13, phase61_14, phase61_20, phase61_21, phase61_22, phase61_23, phase61_24, phase61_30, phase61_31, phase61_32, phase61_33, phase61_34]
  try simp only [star_one, star_neg]
  ring
theorem v61_40 (t : ℂ) : (momentPoly 61 z61 4 0).eval t = ((594281 / 1600) * t ^ 4 + (-594281 / 800) * t ^ 6 + (1322987 / 3200) * t ^ 8 + (-5377 / 96) * t ^ 10 + (5377 / 384) * t ^ 16 + (3123191 / 8000) * alpha * t ^ 4 + (-3123191 / 4000) * alpha * t ^ 6 + (6072941 / 16000) * alpha * t ^ 8 + (173441 / 12000) * alpha * t ^ 10 + (-173441 / 48000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_10, v60_20, v60_30, v60_40]
  try simp only [phase61_00, phase61_10, phase61_20, phase61_30, phase61_40]
  try simp only [star_one, star_neg]
  ring
theorem v61_41 (t : ℂ) : (momentPoly 61 z61 4 1).eval t = (476 * t ^ 3 + (-1182) * t ^ 5 + 696 * t ^ 7 + 247 * t ^ 9 + (-236) * t ^ 11 + (-1) * t ^ 17 + (-140777 / 100) * alpha * t ^ 3 + (699153 / 200) * alpha * t ^ 5 + (-102921 / 50) * alpha * t ^ 7 + (-292201 / 400) * alpha * t ^ 9 + (69797 / 100) * alpha * t ^ 11 + (1183 / 400) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_10, v60_11, v60_20, v60_21, v60_30, v60_31, v60_40, v60_41]
  try simp only [phase61_00, phase61_01, phase61_10, phase61_11, phase61_20, phase61_21, phase61_30, phase61_31, phase61_40, phase61_41]
  try simp only [star_one, star_neg]
  ring
theorem v61_42 (t : ℂ) : (momentPoly 61 z61 4 2).eval t = ((-1231765 / 2) * t ^ 2 + (14589475 / 8) * t ^ 4 + (-286082577429 / 160000) * t ^ 6 + (92899732287 / 160000) * t ^ 8 + (-822042579 / 64000) * t ^ 10 + (12408702821 / 960000) * t ^ 12 + (-121148321 / 240000) * t ^ 14 + (-121148321 / 960000) * t ^ 18 + (134948321 / 960000) * t ^ 20 + (-1831581 / 10) * alpha * t ^ 2 + (4338783 / 8) * alpha * t ^ 4 + (-17046007657 / 32000) * alpha * t ^ 6 + (5616454971 / 32000) * alpha * t ^ 8 + (-396035747 / 64000) * alpha * t ^ 10 + (707734577 / 192000) * alpha * t ^ 12 + (4621559 / 9600) * alpha * t ^ 14 + (4621559 / 38400) * alpha * t ^ 18 + (-4457399 / 38400) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_10, v60_11, v60_12, v60_20, v60_21, v60_22, v60_30, v60_31, v60_32, v60_40, v60_41, v60_42]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_10, phase61_11, phase61_12, phase61_20, phase61_21, phase61_22, phase61_30, phase61_31, phase61_32, phase61_40, phase61_41, phase61_42]
  try simp only [star_one, star_neg]
  ring
theorem v61_43 (t : ℂ) : (momentPoly 61 z61 4 3).eval t = ((132284529 / 4000) * t ^ 5 + (-193586467459 / 1600000) * t ^ 7 + (483082642013 / 3200000) * t ^ 9 + (-175289405363 / 3200000) * t ^ 11 + (-106702792949 / 3840000) * t ^ 13 + (4513287971 / 200000) * t ^ 15 + (-18906893609 / 6400000) * t ^ 17 + (-658264709 / 9600000) * t ^ 19 + (-432137309 / 6400000) * t ^ 21 + (884392109 / 19200000) * t ^ 25 + (2102139 / 32) * alpha * t ^ 5 + (-72023075297 / 320000) * alpha * t ^ 7 + (157727822079 / 640000) * alpha * t ^ 9 + (-30770947881 / 640000) * alpha * t ^ 11 + (-89019082617 / 1280000) * alpha * t ^ 13 + (578361237 / 20000) * alpha * t ^ 15 + (2050928901 / 1280000) * alpha * t ^ 17 + (-3687633 / 128000) * alpha * t ^ 19 + (6904101 / 256000) * alpha * t ^ 21 + (9676633 / 256000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z61, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v60_00, v60_01, v60_02, v60_03, v60_10, v60_11, v60_12, v60_13, v60_20, v60_21, v60_22, v60_23, v60_30, v60_31, v60_32, v60_33, v60_40, v60_41, v60_42, v60_43]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_10, phase61_11, phase61_12, phase61_13, phase61_20, phase61_21, phase61_22, phase61_23, phase61_30, phase61_31, phase61_32, phase61_33, phase61_40, phase61_41, phase61_42, phase61_43]
  try simp only [star_one, star_neg]
  ring
theorem v61_44 (t : ℂ) : (momentPoly 61 z61 4 4).eval t = (316260661 + (-1233855784) * t ^ 2 + (182377157193 / 100) * t ^ 4 + (-3196616136089 / 2500) * t ^ 6 + (7778319837691367 / 16000000) * t ^ 8 + (-636244597116967 / 4000000) * t ^ 10 + (146530817834427 / 3200000) * t ^ 12 + (-34159694665867 / 24000000) * t ^ 14 + (193878806336857 / 192000000) * t ^ 16 + (-669895906733 / 24000000) * t ^ 18 + (5031212764867 / 144000000) * t ^ 20 + (43168532467 / 24000000) * t ^ 22 + (90604516733 / 96000000) * t ^ 24 + (-80917820467 / 72000000) * t ^ 26 + (100363339267 / 576000000) * t ^ 32) := by
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
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v62_02 (t : ℂ) : (momentPoly 62 z62 0 2).eval t = ((-115 / 8) * t ^ 2 + (123 / 8) * t ^ 4 + (171 / 40) * alpha * t ^ 2 + (-171 / 40) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02]
  try simp only [phase61_00, phase61_01, phase61_02]
  try simp only [star_one, star_neg]
  ring
theorem v62_03 (t : ℂ) : (momentPoly 62 z62 0 3).eval t = ((361 / 8) * t ^ 3 + (-369 / 8) * t ^ 5 + (-691 / 100) * alpha * t ^ 3 + (1581 / 400) * alpha * t ^ 5 + (1183 / 400) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_03]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03]
  try simp only [star_one, star_neg]
  ring
theorem v62_04 (t : ℂ) : (momentPoly 62 z62 0 4).eval t = ((581481 / 1600) * t ^ 4 + (-653681 / 800) * t ^ 6 + (1598987 / 3200) * t ^ 8 + (-5761 / 96) * t ^ 10 + (5761 / 384) * t ^ 16 + (-3312471 / 8000) * alpha * t ^ 4 + (3367751 / 4000) * alpha * t ^ 6 + (-6483341 / 16000) * alpha * t ^ 8 + (-315401 / 12000) * alpha * t ^ 10 + (173441 / 48000) * alpha * t ^ 16) := by
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
theorem v62_12 (t : ℂ) : (momentPoly 62 z62 1 2).eval t = ((-123) * t + (1091 / 8) * t ^ 3 + (-115 / 8) * t ^ 5 + (-171 / 40) * alpha * t ^ 3 + (171 / 40) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_10, v61_11, v61_12]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_10, phase61_11, phase61_12]
  try simp only [star_one, star_neg]
  ring
theorem v62_13 (t : ℂ) : (momentPoly 62 z62 1 3).eval t = ((-21045 / 8) * t ^ 2 + (42971 / 8) * t ^ 4 + (-21795 / 8) * t ^ 6 + (-123 / 8) * t ^ 10 + (31293 / 40) * alpha * t ^ 2 + (-154919 / 100) * alpha * t ^ 4 + (306219 / 400) * alpha * t ^ 6 + (527 / 400) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_03, v61_10, v61_11, v61_12, v61_13]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_10, phase61_11, phase61_12, phase61_13]
  try simp only [star_one, star_neg]
  ring
theorem v62_14 (t : ℂ) : (momentPoly 62 z62 1 4).eval t = ((43681 / 4) * t ^ 3 + (-35578681 / 1600) * t ^ 5 + (9293081 / 800) * t ^ 7 + (-1303787 / 3200) * t ^ 9 + (11665 / 96) * t ^ 11 + (-5761 / 384) * t ^ 17 + (-83611 / 50) * alpha * t ^ 3 + (24052751 / 8000) * alpha * t ^ 5 + (-6996311 / 4000) * alpha * t ^ 7 + (17950261 / 16000) * alpha * t ^ 9 + (-8407399 / 12000) * alpha * t ^ 11 + (-315401 / 48000) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_03, v61_04, v61_10, v61_11, v61_12, v61_13, v61_14]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_04, phase61_10, phase61_11, phase61_12, phase61_13, phase61_14]
  try simp only [star_one, star_neg]
  ring
theorem v62_20 (t : ℂ) : (momentPoly 62 z62 2 0).eval t = ((-115 / 8) * t ^ 2 + (123 / 8) * t ^ 4 + (-171 / 40) * alpha * t ^ 2 + (171 / 40) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_10, v61_20]
  try simp only [phase61_00, phase61_10, phase61_20]
  try simp only [star_one, star_neg]
  ring
theorem v62_21 (t : ℂ) : (momentPoly 62 z62 2 1).eval t = ((-123) * t + (1091 / 8) * t ^ 3 + (-115 / 8) * t ^ 5 + (171 / 40) * alpha * t ^ 3 + (-171 / 40) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_10, v61_11, v61_20, v61_21]
  try simp only [phase61_00, phase61_01, phase61_10, phase61_11, phase61_20, phase61_21]
  try simp only [star_one, star_neg]
  ring
theorem v62_22 (t : ℂ) : (momentPoly 62 z62 2 2).eval t = (7626 + (-14884) * t ^ 2 + (2934987 / 400) * t ^ 4 + (-61537 / 200) * t ^ 6 + (91687 / 400) * t ^ 8) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_10, v61_11, v61_12, v61_20, v61_21, v61_22]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_10, phase61_11, phase61_12, phase61_20, phase61_21, phase61_22]
  try simp only [star_one, star_neg]
  ring
theorem v62_23 (t : ℂ) : (momentPoly 62 z62 2 3).eval t = ((-22510) * t + (396033 / 8) * t ^ 3 + (-258407341 / 8000) * t ^ 5 + (18591297 / 3200) * t ^ 7 + (-8539803 / 16000) * t ^ 9 + (1066879 / 16000) * t ^ 11 + (-590879 / 16000) * t ^ 13 + (-62073 / 40) * alpha * t ^ 3 + (953647 / 320) * alpha * t ^ 5 + (-4075167 / 3200) * alpha * t ^ 7 + (-477567 / 3200) * alpha * t ^ 9 + (-32681 / 640) * alpha * t ^ 11 + (145509 / 3200) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_03, v61_10, v61_11, v61_12, v61_13, v61_20, v61_21, v61_22, v61_23]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_10, phase61_11, phase61_12, phase61_13, phase61_20, phase61_21, phase61_22, phase61_23]
  try simp only [star_one, star_neg]
  ring
theorem v62_24 (t : ℂ) : (momentPoly 62 z62 2 4).eval t = ((-2546675 / 4) * t ^ 2 + (15270045 / 8) * t ^ 4 + (-303121847749 / 160000) * t ^ 6 + (99855784987 / 160000) * t ^ 8 + (-1034018291 / 64000) * t ^ 10 + (14322960761 / 960000) * t ^ 12 + (-37326027 / 80000) * t ^ 14 + (-133028321 / 960000) * t ^ 18 + (54063607 / 320000) * t ^ 20 + (757359 / 4) * alpha * t ^ 2 + (-22298253 / 40) * alpha * t ^ 4 + (17476559097 / 32000) * alpha * t ^ 6 + (-1158126323 / 6400) * alpha * t ^ 8 + (389868163 / 64000) * alpha * t ^ 10 + (-476655389 / 192000) * alpha * t ^ 12 + (-10928353 / 16000) * alpha * t ^ 14 + (-4558583 / 38400) * alpha * t ^ 18 + (7933853 / 64000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_03, v61_04, v61_10, v61_11, v61_12, v61_13, v61_14, v61_20, v61_21, v61_22, v61_23, v61_24]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_04, phase61_10, phase61_11, phase61_12, phase61_13, phase61_14, phase61_20, phase61_21, phase61_22, phase61_23, phase61_24]
  try simp only [star_one, star_neg]
  ring
theorem v62_30 (t : ℂ) : (momentPoly 62 z62 3 0).eval t = ((361 / 8) * t ^ 3 + (-369 / 8) * t ^ 5 + (691 / 100) * alpha * t ^ 3 + (-1581 / 400) * alpha * t ^ 5 + (-1183 / 400) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_10, v61_20, v61_30]
  try simp only [phase61_00, phase61_10, phase61_20, phase61_30]
  try simp only [star_one, star_neg]
  ring
theorem v62_31 (t : ℂ) : (momentPoly 62 z62 3 1).eval t = ((-21045 / 8) * t ^ 2 + (42971 / 8) * t ^ 4 + (-21795 / 8) * t ^ 6 + (-123 / 8) * t ^ 10 + (-31293 / 40) * alpha * t ^ 2 + (154919 / 100) * alpha * t ^ 4 + (-306219 / 400) * alpha * t ^ 6 + (-527 / 400) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_10, v61_11, v61_20, v61_21, v61_30, v61_31]
  try simp only [phase61_00, phase61_01, phase61_10, phase61_11, phase61_20, phase61_21, phase61_30, phase61_31]
  try simp only [star_one, star_neg]
  ring
theorem v62_32 (t : ℂ) : (momentPoly 62 z62 3 2).eval t = ((-22510) * t + (396033 / 8) * t ^ 3 + (-258407341 / 8000) * t ^ 5 + (18591297 / 3200) * t ^ 7 + (-8539803 / 16000) * t ^ 9 + (1066879 / 16000) * t ^ 11 + (-590879 / 16000) * t ^ 13 + (62073 / 40) * alpha * t ^ 3 + (-953647 / 320) * alpha * t ^ 5 + (4075167 / 3200) * alpha * t ^ 7 + (477567 / 3200) * alpha * t ^ 9 + (32681 / 640) * alpha * t ^ 11 + (-145509 / 3200) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_10, v61_11, v61_12, v61_20, v61_21, v61_22, v61_30, v61_31, v61_32]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_10, phase61_11, phase61_12, phase61_20, phase61_21, phase61_22, phase61_30, phase61_31, phase61_32]
  try simp only [star_one, star_neg]
  ring
theorem v62_33 (t : ℂ) : (momentPoly 62 z62 3 3).eval t = (1395620 + (-4052535) * t ^ 2 + (79244649 / 20) * t ^ 4 + (-58786059203 / 40000) * t ^ 6 + (2838924231 / 10000) * t ^ 8 + (-19101264417 / 160000) * t ^ 10 + (16008741 / 20000) * t ^ 12 + (-75133431 / 80000) * t ^ 14 + (-5721533 / 160000) * t ^ 18) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_03, v61_10, v61_11, v61_12, v61_13, v61_20, v61_21, v61_22, v61_23, v61_30, v61_31, v61_32, v61_33]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_10, phase61_11, phase61_12, phase61_13, phase61_20, phase61_21, phase61_22, phase61_23, phase61_30, phase61_31, phase61_32, phase61_33]
  try simp only [star_one, star_neg]
  ring
theorem v62_34 (t : ℂ) : (momentPoly 62 z62 3 4).eval t = ((-5448155) * t + (71295759 / 4) * t ^ 3 + (-84864453237 / 4000) * t ^ 5 + (17733794306691 / 1600000) * t ^ 7 + (-8315563848487 / 3200000) * t ^ 9 + (1314417912847 / 3200000) * t ^ 11 + (-347368971569 / 3840000) * t ^ 13 + (15374185917 / 400000) * t ^ 15 + (-22457377209 / 6400000) * t ^ 17 + (5381452841 / 9600000) * t ^ 19 + (-3169503729 / 6400000) * t ^ 21 + (211580703 / 6400000) * t ^ 25 + (-11174679 / 20) * alpha * t ^ 3 + (252579183 / 160) * alpha * t ^ 5 + (-440005406013 / 320000) * alpha * t ^ 7 + (171806213781 / 640000) * alpha * t ^ 9 + (23529647871 / 640000) * alpha * t ^ 11 + (100438136717 / 1280000) * alpha * t ^ 13 + (-2163287843 / 80000) * alpha * t ^ 15 + (-1924433621 / 1280000) * alpha * t ^ 17 + (159554821 / 384000) * alpha * t ^ 19 + (-96052081 / 256000) * alpha * t ^ 21 + (-6815263 / 153600) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_03, v61_04, v61_10, v61_11, v61_12, v61_13, v61_14, v61_20, v61_21, v61_22, v61_23, v61_24, v61_30, v61_31, v61_32, v61_33, v61_34]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_04, phase61_10, phase61_11, phase61_12, phase61_13, phase61_14, phase61_20, phase61_21, phase61_22, phase61_23, phase61_24, phase61_30, phase61_31, phase61_32, phase61_33, phase61_34]
  try simp only [star_one, star_neg]
  ring
theorem v62_40 (t : ℂ) : (momentPoly 62 z62 4 0).eval t = ((581481 / 1600) * t ^ 4 + (-653681 / 800) * t ^ 6 + (1598987 / 3200) * t ^ 8 + (-5761 / 96) * t ^ 10 + (5761 / 384) * t ^ 16 + (3312471 / 8000) * alpha * t ^ 4 + (-3367751 / 4000) * alpha * t ^ 6 + (6483341 / 16000) * alpha * t ^ 8 + (315401 / 12000) * alpha * t ^ 10 + (-173441 / 48000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_10, v61_20, v61_30, v61_40]
  try simp only [phase61_00, phase61_10, phase61_20, phase61_30, phase61_40]
  try simp only [star_one, star_neg]
  ring
theorem v62_41 (t : ℂ) : (momentPoly 62 z62 4 1).eval t = ((43681 / 4) * t ^ 3 + (-35578681 / 1600) * t ^ 5 + (9293081 / 800) * t ^ 7 + (-1303787 / 3200) * t ^ 9 + (11665 / 96) * t ^ 11 + (-5761 / 384) * t ^ 17 + (83611 / 50) * alpha * t ^ 3 + (-24052751 / 8000) * alpha * t ^ 5 + (6996311 / 4000) * alpha * t ^ 7 + (-17950261 / 16000) * alpha * t ^ 9 + (8407399 / 12000) * alpha * t ^ 11 + (315401 / 48000) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_10, v61_11, v61_20, v61_21, v61_30, v61_31, v61_40, v61_41]
  try simp only [phase61_00, phase61_01, phase61_10, phase61_11, phase61_20, phase61_21, phase61_30, phase61_31, phase61_40, phase61_41]
  try simp only [star_one, star_neg]
  ring
theorem v62_42 (t : ℂ) : (momentPoly 62 z62 4 2).eval t = ((-2546675 / 4) * t ^ 2 + (15270045 / 8) * t ^ 4 + (-303121847749 / 160000) * t ^ 6 + (99855784987 / 160000) * t ^ 8 + (-1034018291 / 64000) * t ^ 10 + (14322960761 / 960000) * t ^ 12 + (-37326027 / 80000) * t ^ 14 + (-133028321 / 960000) * t ^ 18 + (54063607 / 320000) * t ^ 20 + (-757359 / 4) * alpha * t ^ 2 + (22298253 / 40) * alpha * t ^ 4 + (-17476559097 / 32000) * alpha * t ^ 6 + (1158126323 / 6400) * alpha * t ^ 8 + (-389868163 / 64000) * alpha * t ^ 10 + (476655389 / 192000) * alpha * t ^ 12 + (10928353 / 16000) * alpha * t ^ 14 + (4558583 / 38400) * alpha * t ^ 18 + (-7933853 / 64000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_10, v61_11, v61_12, v61_20, v61_21, v61_22, v61_30, v61_31, v61_32, v61_40, v61_41, v61_42]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_10, phase61_11, phase61_12, phase61_20, phase61_21, phase61_22, phase61_30, phase61_31, phase61_32, phase61_40, phase61_41, phase61_42]
  try simp only [star_one, star_neg]
  ring
theorem v62_43 (t : ℂ) : (momentPoly 62 z62 4 3).eval t = ((-5448155) * t + (71295759 / 4) * t ^ 3 + (-84864453237 / 4000) * t ^ 5 + (17733794306691 / 1600000) * t ^ 7 + (-8315563848487 / 3200000) * t ^ 9 + (1314417912847 / 3200000) * t ^ 11 + (-347368971569 / 3840000) * t ^ 13 + (15374185917 / 400000) * t ^ 15 + (-22457377209 / 6400000) * t ^ 17 + (5381452841 / 9600000) * t ^ 19 + (-3169503729 / 6400000) * t ^ 21 + (211580703 / 6400000) * t ^ 25 + (11174679 / 20) * alpha * t ^ 3 + (-252579183 / 160) * alpha * t ^ 5 + (440005406013 / 320000) * alpha * t ^ 7 + (-171806213781 / 640000) * alpha * t ^ 9 + (-23529647871 / 640000) * alpha * t ^ 11 + (-100438136717 / 1280000) * alpha * t ^ 13 + (2163287843 / 80000) * alpha * t ^ 15 + (1924433621 / 1280000) * alpha * t ^ 17 + (-159554821 / 384000) * alpha * t ^ 19 + (96052081 / 256000) * alpha * t ^ 21 + (6815263 / 153600) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z62, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v61_00, v61_01, v61_02, v61_03, v61_10, v61_11, v61_12, v61_13, v61_20, v61_21, v61_22, v61_23, v61_30, v61_31, v61_32, v61_33, v61_40, v61_41, v61_42, v61_43]
  try simp only [phase61_00, phase61_01, phase61_02, phase61_03, phase61_10, phase61_11, phase61_12, phase61_13, phase61_20, phase61_21, phase61_22, phase61_23, phase61_30, phase61_31, phase61_32, phase61_33, phase61_40, phase61_41, phase61_42, phase61_43]
  try simp only [star_one, star_neg]
  ring
theorem v62_44 (t : ℂ) : (momentPoly 62 z62 4 4).eval t = (337785610 + (-1297107416) * t ^ 2 + (47159371116 / 25) * t ^ 4 + (-818510527138 / 625) * t ^ 6 + (8210904676601687 / 16000000) * t ^ 8 + (-733875774888597 / 4000000) * t ^ 10 + (170261637241571 / 3200000) * t ^ 12 + (-10888075460239 / 8000000) * t ^ 14 + (187928585489977 / 192000000) * t ^ 16 + (-308646762863 / 24000000) * t ^ 18 + (5489047109947 / 144000000) * t ^ 20 + (-15868704563 / 24000000) * t ^ 22 + (331921721933 / 96000000) * t ^ 24 + (-114939083737 / 72000000) * t ^ 26 + (116494339267 / 576000000) * t ^ 32) := by
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
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
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
theorem v63_02 (t : ℂ) : (momentPoly 63 z63 0 2).eval t = ((-131 / 8) * t ^ 2 + (131 / 8) * t ^ 4 + (171 / 40) * alpha * t ^ 2 + (-171 / 40) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02]
  try simp only [phase63_00, phase63_01, phase63_02]
  try simp only [star_one, star_neg]
  ring
theorem v63_03 (t : ℂ) : (momentPoly 63 z63 0 3).eval t = (2 * t ^ 3 + (-3) * t ^ 5 + 1 * t ^ 9 + (1183 / 200) * alpha * t ^ 3 + (-3549 / 400) * alpha * t ^ 5 + (1183 / 400) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_03]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_03]
  try simp only [star_one, star_neg]
  ring
theorem v63_04 (t : ℂ) : (momentPoly 63 z63 0 4).eval t = ((870281 / 1600) * t ^ 4 + (-870281 / 800) * t ^ 6 + (1894187 / 3200) * t ^ 8 + (-6145 / 96) * t ^ 10 + (6145 / 384) * t ^ 16 + (-3533591 / 8000) * alpha * t ^ 4 + (3533591 / 4000) * alpha * t ^ 6 + (-6893741 / 16000) * alpha * t ^ 8 + (-173441 / 12000) * alpha * t ^ 10 + (173441 / 48000) * alpha * t ^ 16) := by
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
theorem v63_13 (t : ℂ) : (momentPoly 63 z63 1 3).eval t = ((-12183 / 4) * t ^ 2 + (24235 / 4) * t ^ 4 + (-23973 / 8) * t ^ 6 + (-131 / 8) * t ^ 10 + (15903 / 20) * alpha * t ^ 2 + (-6327 / 4) * alpha * t ^ 4 + (31293 / 40) * alpha * t ^ 6 + (171 / 40) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_03, v62_10, v62_11, v62_12, v62_13]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_03, phase63_10, phase63_11, phase63_12, phase63_13]
  try simp only [star_one, star_neg]
  ring
theorem v63_14 (t : ℂ) : (momentPoly 63 z63 1 4).eval t = (492 * t ^ 3 + (-1222) * t ^ 5 + 720 * t ^ 7 + 255 * t ^ 9 + (-244) * t ^ 11 + (-1) * t ^ 17 + (145509 / 100) * alpha * t ^ 3 + (-722813 / 200) * alpha * t ^ 5 + (10647 / 5) * alpha * t ^ 7 + (60333 / 80) * alpha * t ^ 9 + (-72163 / 100) * alpha * t ^ 11 + (-1183 / 400) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_03, v62_04, v62_10, v62_11, v62_12, v62_13, v62_14]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_03, phase63_04, phase63_10, phase63_11, phase63_12, phase63_13, phase63_14]
  try simp only [star_one, star_neg]
  ring
theorem v63_20 (t : ℂ) : (momentPoly 63 z63 2 0).eval t = ((-131 / 8) * t ^ 2 + (131 / 8) * t ^ 4 + (-171 / 40) * alpha * t ^ 2 + (171 / 40) * alpha * t ^ 4) := by
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
theorem v63_23 (t : ℂ) : (momentPoly 63 z63 2 3).eval t = ((344879 / 8000) * t ^ 5 + (-344879 / 3200) * t ^ 7 + (1034637 / 16000) * t ^ 9 + (344879 / 16000) * t ^ 11 + (-344879 / 16000) * t ^ 13 + (-168653 / 1600) * alpha * t ^ 5 + (168653 / 640) * alpha * t ^ 7 + (-505959 / 3200) * alpha * t ^ 9 + (-168653 / 3200) * alpha * t ^ 11 + (168653 / 3200) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_03, v62_10, v62_11, v62_12, v62_13, v62_20, v62_21, v62_22, v62_23]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_03, phase63_10, phase63_11, phase63_12, phase63_13, phase63_20, phase63_21, phase63_22, phase63_23]
  try simp only [star_one, star_neg]
  ring
theorem v63_24 (t : ℂ) : (momentPoly 63 z63 2 4).eval t = ((-749320) * t ^ 2 + (17757967 / 8) * t ^ 4 + (-348821211229 / 160000) * t ^ 6 + (114393393687 / 160000) * t ^ 8 + (-1432740139 / 64000) * t ^ 10 + (17135980621 / 960000) * t ^ 12 + (-175633321 / 240000) * t ^ 14 + (-175633321 / 960000) * t ^ 18 + (191353321 / 960000) * t ^ 20 + 195624 * alpha * t ^ 2 + (-23180247 / 40) * alpha * t ^ 4 + (3649713517 / 6400) * alpha * t ^ 6 + (-1215765831 / 6400) * alpha * t ^ 8 + (550580587 / 64000) * alpha * t ^ 10 + (-859426249 / 192000) * alpha * t ^ 12 + (-26136923 / 48000) * alpha * t ^ 14 + (-26136923 / 192000) * alpha * t ^ 18 + (25316123 / 192000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_03, v62_04, v62_10, v62_11, v62_12, v62_13, v62_14, v62_20, v62_21, v62_22, v62_23, v62_24]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_03, phase63_04, phase63_10, phase63_11, phase63_12, phase63_13, phase63_14, phase63_20, phase63_21, phase63_22, phase63_23, phase63_24]
  try simp only [star_one, star_neg]
  ring
theorem v63_30 (t : ℂ) : (momentPoly 63 z63 3 0).eval t = (2 * t ^ 3 + (-3) * t ^ 5 + 1 * t ^ 9 + (-1183 / 200) * alpha * t ^ 3 + (3549 / 400) * alpha * t ^ 5 + (-1183 / 400) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_10, v62_20, v62_30]
  try simp only [phase63_00, phase63_10, phase63_20, phase63_30]
  try simp only [star_one, star_neg]
  ring
theorem v63_31 (t : ℂ) : (momentPoly 63 z63 3 1).eval t = ((-12183 / 4) * t ^ 2 + (24235 / 4) * t ^ 4 + (-23973 / 8) * t ^ 6 + (-131 / 8) * t ^ 10 + (-15903 / 20) * alpha * t ^ 2 + (6327 / 4) * alpha * t ^ 4 + (-31293 / 40) * alpha * t ^ 6 + (-171 / 40) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_10, v62_11, v62_20, v62_21, v62_30, v62_31]
  try simp only [phase63_00, phase63_01, phase63_10, phase63_11, phase63_20, phase63_21, phase63_30, phase63_31]
  try simp only [star_one, star_neg]
  ring
theorem v63_32 (t : ℂ) : (momentPoly 63 z63 3 2).eval t = ((344879 / 8000) * t ^ 5 + (-344879 / 3200) * t ^ 7 + (1034637 / 16000) * t ^ 9 + (344879 / 16000) * t ^ 11 + (-344879 / 16000) * t ^ 13 + (168653 / 1600) * alpha * t ^ 5 + (-168653 / 640) * alpha * t ^ 7 + (505959 / 3200) * alpha * t ^ 9 + (168653 / 3200) * alpha * t ^ 11 + (-168653 / 3200) * alpha * t ^ 13) := by
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
theorem v63_34 (t : ℂ) : (momentPoly 63 z63 3 4).eval t = ((125191077 / 4000) * t ^ 5 + (-184688144259 / 1600000) * t ^ 7 + (467521562813 / 3200000) * t ^ 9 + (-177561120563 / 3200000) * t ^ 11 + (-97814415989 / 3840000) * t ^ 13 + (4465815371 / 200000) * t ^ 15 + (-20677512809 / 6400000) * t ^ 17 + (-715864709 / 9600000) * t ^ 19 + (-508937309 / 6400000) * t ^ 21 + (922792109 / 19200000) * t ^ 25 + (-61221039 / 800) * alpha * t ^ 5 + (83722612897 / 320000) * alpha * t ^ 7 + (-182471661279 / 640000) * alpha * t ^ 9 + (34364650281 / 640000) * alpha * t ^ 11 + (104491111417 / 1280000) * alpha * t ^ 13 + (-662117637 / 20000) * alpha * t ^ 15 + (-2792322501 / 1280000) * alpha * t ^ 17 + (4444753 / 128000) * alpha * t ^ 19 + (-6904101 / 256000) * alpha * t ^ 21 + (-11190873 / 256000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_03, v62_04, v62_10, v62_11, v62_12, v62_13, v62_14, v62_20, v62_21, v62_22, v62_23, v62_24, v62_30, v62_31, v62_32, v62_33, v62_34]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_03, phase63_04, phase63_10, phase63_11, phase63_12, phase63_13, phase63_14, phase63_20, phase63_21, phase63_22, phase63_23, phase63_24, phase63_30, phase63_31, phase63_32, phase63_33, phase63_34]
  try simp only [star_one, star_neg]
  ring
theorem v63_40 (t : ℂ) : (momentPoly 63 z63 4 0).eval t = ((870281 / 1600) * t ^ 4 + (-870281 / 800) * t ^ 6 + (1894187 / 3200) * t ^ 8 + (-6145 / 96) * t ^ 10 + (6145 / 384) * t ^ 16 + (3533591 / 8000) * alpha * t ^ 4 + (-3533591 / 4000) * alpha * t ^ 6 + (6893741 / 16000) * alpha * t ^ 8 + (173441 / 12000) * alpha * t ^ 10 + (-173441 / 48000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_10, v62_20, v62_30, v62_40]
  try simp only [phase63_00, phase63_10, phase63_20, phase63_30, phase63_40]
  try simp only [star_one, star_neg]
  ring
theorem v63_41 (t : ℂ) : (momentPoly 63 z63 4 1).eval t = (492 * t ^ 3 + (-1222) * t ^ 5 + 720 * t ^ 7 + 255 * t ^ 9 + (-244) * t ^ 11 + (-1) * t ^ 17 + (-145509 / 100) * alpha * t ^ 3 + (722813 / 200) * alpha * t ^ 5 + (-10647 / 5) * alpha * t ^ 7 + (-60333 / 80) * alpha * t ^ 9 + (72163 / 100) * alpha * t ^ 11 + (1183 / 400) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_10, v62_11, v62_20, v62_21, v62_30, v62_31, v62_40, v62_41]
  try simp only [phase63_00, phase63_01, phase63_10, phase63_11, phase63_20, phase63_21, phase63_30, phase63_31, phase63_40, phase63_41]
  try simp only [star_one, star_neg]
  ring
theorem v63_42 (t : ℂ) : (momentPoly 63 z63 4 2).eval t = ((-749320) * t ^ 2 + (17757967 / 8) * t ^ 4 + (-348821211229 / 160000) * t ^ 6 + (114393393687 / 160000) * t ^ 8 + (-1432740139 / 64000) * t ^ 10 + (17135980621 / 960000) * t ^ 12 + (-175633321 / 240000) * t ^ 14 + (-175633321 / 960000) * t ^ 18 + (191353321 / 960000) * t ^ 20 + (-195624) * alpha * t ^ 2 + (23180247 / 40) * alpha * t ^ 4 + (-3649713517 / 6400) * alpha * t ^ 6 + (1215765831 / 6400) * alpha * t ^ 8 + (-550580587 / 64000) * alpha * t ^ 10 + (859426249 / 192000) * alpha * t ^ 12 + (26136923 / 48000) * alpha * t ^ 14 + (26136923 / 192000) * alpha * t ^ 18 + (-25316123 / 192000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_10, v62_11, v62_12, v62_20, v62_21, v62_22, v62_30, v62_31, v62_32, v62_40, v62_41, v62_42]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_10, phase63_11, phase63_12, phase63_20, phase63_21, phase63_22, phase63_30, phase63_31, phase63_32, phase63_40, phase63_41, phase63_42]
  try simp only [star_one, star_neg]
  ring
theorem v63_43 (t : ℂ) : (momentPoly 63 z63 4 3).eval t = ((125191077 / 4000) * t ^ 5 + (-184688144259 / 1600000) * t ^ 7 + (467521562813 / 3200000) * t ^ 9 + (-177561120563 / 3200000) * t ^ 11 + (-97814415989 / 3840000) * t ^ 13 + (4465815371 / 200000) * t ^ 15 + (-20677512809 / 6400000) * t ^ 17 + (-715864709 / 9600000) * t ^ 19 + (-508937309 / 6400000) * t ^ 21 + (922792109 / 19200000) * t ^ 25 + (61221039 / 800) * alpha * t ^ 5 + (-83722612897 / 320000) * alpha * t ^ 7 + (182471661279 / 640000) * alpha * t ^ 9 + (-34364650281 / 640000) * alpha * t ^ 11 + (-104491111417 / 1280000) * alpha * t ^ 13 + (662117637 / 20000) * alpha * t ^ 15 + (2792322501 / 1280000) * alpha * t ^ 17 + (-4444753 / 128000) * alpha * t ^ 19 + (6904101 / 256000) * alpha * t ^ 21 + (11190873 / 256000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z63, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v62_00, v62_01, v62_02, v62_03, v62_10, v62_11, v62_12, v62_13, v62_20, v62_21, v62_22, v62_23, v62_30, v62_31, v62_32, v62_33, v62_40, v62_41, v62_42, v62_43]
  try simp only [phase63_00, phase63_01, phase63_02, phase63_03, phase63_10, phase63_11, phase63_12, phase63_13, phase63_20, phase63_21, phase63_22, phase63_23, phase63_30, phase63_31, phase63_32, phase63_33, phase63_40, phase63_41, phase63_42, phase63_43]
  try simp only [star_one, star_neg]
  ring
theorem v63_44 (t : ℂ) : (momentPoly 63 z63 4 4).eval t = (360391059 + (-1407156408) * t ^ 2 + (209500897467 / 100) * t ^ 4 + (-756073380891 / 500) * t ^ 6 + (10076112798010567 / 16000000) * t ^ 8 + (-916059671100967 / 4000000) * t ^ 10 + (205074306956587 / 3200000) * t ^ 12 + (-59379046745467 / 24000000) * t ^ 14 + (299183280757657 / 192000000) * t ^ 16 + (-1208700675533 / 24000000) * t ^ 18 + (6379468030867 / 144000000) * t ^ 20 + (-190083172733 / 24000000) * t ^ 22 + (622489927133 / 96000000) * t ^ 24 + (-113179820467 / 72000000) * t ^ 26 + (133777339267 / 576000000) * t ^ 32) := by
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
end PhotonCertB
