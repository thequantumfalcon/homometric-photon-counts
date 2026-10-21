import PhotonCertA0
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
theorem phase1_00 : (thetaPlus : ℂ) ^ 0 * star (thetaPlus : ℂ) ^ 0 = (1) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase1_01 : (thetaPlus : ℂ) ^ 0 * star (thetaPlus : ℂ) ^ 1 = ((-1 / 10) + (1 / 30) * c + (-1 / 30) * alpha + (-1 / 30) * alpha * c) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 30)) * alpha_sq
theorem phase1_02 : (thetaPlus : ℂ) ^ 0 * star (thetaPlus : ℂ) ^ 2 = ((-73 / 150) + (-1 / 75) * c + (-73 / 150) * alpha + (1 / 225) * alpha * c) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 450) + (1 / 225) * c + (1 / 900) * c ^ 2 + (-1 / 450) * alpha + (-1 / 450) * alpha * c + (1 / 900) * alpha ^ 2) * alpha_sq + ((-1 / 450) + (-1 / 450) * alpha) * c_sq
theorem phase1_03 : (thetaPlus : ℂ) ^ 0 * star (thetaPlus : ℂ) ^ 3 = ((-71 / 1125) * c + (221 / 1125) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 1125) * c + (1 / 9000) * c ^ 3 + (1 / 3375) * alpha + (-1 / 3000) * alpha * c ^ 2 + (-1 / 27000) * alpha * c ^ 3 + (1 / 3000) * alpha ^ 2 * c + (1 / 9000) * alpha ^ 2 * c ^ 2 + (-1 / 9000) * alpha ^ 3 + (-1 / 9000) * alpha ^ 3 * c + (1 / 27000) * alpha ^ 4) * alpha_sq + ((-1 / 3375) * c + (1 / 1125) * alpha) * c_sq
theorem phase1_04 : (thetaPlus : ℂ) ^ 0 * star (thetaPlus : ℂ) ^ 4 = ((-5033 / 11250) + (146 / 5625) * c + (5033 / 11250) * alpha + (146 / 16875) * alpha * c) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 33750) + (2 / 16875) * c + (-1 / 16875) * c ^ 2 + (-2 / 50625) * c ^ 3 + (1 / 270000) * c ^ 4 + (-1 / 33750) * alpha + (2 / 50625) * alpha * c + (1 / 16875) * alpha * c ^ 2 + (-1 / 67500) * alpha * c ^ 3 + (-1 / 202500) * alpha * c ^ 4 + (-1 / 101250) * alpha ^ 2 + (-2 / 50625) * alpha ^ 2 * c + (1 / 45000) * alpha ^ 2 * c ^ 2 + (1 / 50625) * alpha ^ 2 * c ^ 3 + (1 / 810000) * alpha ^ 2 * c ^ 4 + (1 / 101250) * alpha ^ 3 + (-1 / 67500) * alpha ^ 3 * c + (-1 / 33750) * alpha ^ 3 * c ^ 2 + (-1 / 202500) * alpha ^ 3 * c ^ 3 + (1 / 270000) * alpha ^ 4 + (1 / 50625) * alpha ^ 4 * c + (1 / 135000) * alpha ^ 4 * c ^ 2 + (-1 / 202500) * alpha ^ 5 + (-1 / 202500) * alpha ^ 5 * c + (1 / 810000) * alpha ^ 6) * alpha_sq + ((-34 / 16875) + (2 / 16875) * c + (-1 / 101250) * c ^ 2 + (34 / 16875) * alpha + (2 / 50625) * alpha * c + (1 / 101250) * alpha * c ^ 2) * c_sq
theorem phase1_10 : (thetaPlus : ℂ) ^ 1 * star (thetaPlus : ℂ) ^ 0 = ((-1 / 10) + (1 / 30) * c + (1 / 30) * alpha + (1 / 30) * alpha * c) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 30)) * alpha_sq
theorem phase1_11 : (thetaPlus : ℂ) ^ 1 * star (thetaPlus : ℂ) ^ 1 = (1) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 225) + (-1 / 900) * c ^ 2 + (1 / 900) * alpha ^ 2) * alpha_sq + ((1 / 225)) * c_sq
theorem phase1_12 : (thetaPlus : ℂ) ^ 1 * star (thetaPlus : ℂ) ^ 2 = ((-1 / 10) + (1 / 30) * c + (-1 / 30) * alpha + (-1 / 30) * alpha * c) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 2250) + (-1 / 6750) * c + (1 / 6750) * c ^ 2 + (-1 / 27000) * c ^ 3 + (1 / 6750) * alpha + (1 / 6750) * alpha * c + (1 / 27000) * alpha * c ^ 2 + (1 / 27000) * alpha * c ^ 3 + (-1 / 6750) * alpha ^ 2 + (1 / 27000) * alpha ^ 2 * c + (-1 / 27000) * alpha ^ 2 * c ^ 2 + (-1 / 27000) * alpha ^ 3 + (-1 / 27000) * alpha ^ 3 * c + (1 / 27000) * alpha ^ 4) * alpha_sq + ((-1 / 2250) + (1 / 6750) * c + (-1 / 6750) * alpha + (-1 / 6750) * alpha * c) * c_sq
theorem phase1_13 : (thetaPlus : ℂ) ^ 1 * star (thetaPlus : ℂ) ^ 3 = ((-73 / 150) + (-1 / 75) * c + (-73 / 150) * alpha + (1 / 225) * alpha * c) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 33750) + (1 / 16875) * c + (1 / 50625) * c ^ 3 + (1 / 270000) * c ^ 4 + (-1 / 33750) * alpha + (-1 / 50625) * alpha * c + (-1 / 135000) * alpha * c ^ 3 + (1 / 405000) * alpha * c ^ 4 + (1 / 101250) * alpha ^ 2 + (-1 / 50625) * alpha ^ 2 * c + (-1 / 202500) * alpha ^ 2 * c ^ 3 + (-1 / 810000) * alpha ^ 2 * c ^ 4 + (1 / 101250) * alpha ^ 3 + (1 / 135000) * alpha ^ 3 * c + (1 / 405000) * alpha ^ 3 * c ^ 3 + (-1 / 270000) * alpha ^ 4 + (1 / 202500) * alpha ^ 4 * c + (-1 / 405000) * alpha ^ 5 + (-1 / 405000) * alpha ^ 5 * c + (1 / 810000) * alpha ^ 6) * alpha_sq + ((-37 / 16875) + (-1 / 16875) * c + (-1 / 101250) * c ^ 2 + (-37 / 16875) * alpha + (1 / 50625) * alpha * c + (-1 / 101250) * alpha * c ^ 2) * c_sq
theorem phase1_14 : (thetaPlus : ℂ) ^ 1 * star (thetaPlus : ℂ) ^ 4 = ((-71 / 1125) * c + (221 / 1125) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 84375) * c + (-2 / 759375) * c ^ 3 + (11 / 24300000) * c ^ 5 + (1 / 253125) * alpha + (-2 / 759375) * alpha * c ^ 2 + (-11 / 8100000) * alpha * c ^ 4 + (-1 / 24300000) * alpha * c ^ 5 + (1 / 253125) * alpha ^ 2 * c + (11 / 12150000) * alpha ^ 2 * c ^ 3 + (1 / 8100000) * alpha ^ 2 * c ^ 4 + (-1 / 8100000) * alpha ^ 2 * c ^ 5 + (-1 / 759375) * alpha ^ 3 + (11 / 12150000) * alpha ^ 3 * c ^ 2 + (-1 / 12150000) * alpha ^ 3 * c ^ 3 + (1 / 2700000) * alpha ^ 3 * c ^ 4 + (1 / 24300000) * alpha ^ 3 * c ^ 5 + (-11 / 8100000) * alpha ^ 4 * c + (-1 / 12150000) * alpha ^ 4 * c ^ 2 + (-1 / 4050000) * alpha ^ 4 * c ^ 3 + (-1 / 8100000) * alpha ^ 4 * c ^ 4 + (11 / 24300000) * alpha ^ 5 + (1 / 8100000) * alpha ^ 5 * c + (-1 / 4050000) * alpha ^ 5 * c ^ 2 + (1 / 12150000) * alpha ^ 5 * c ^ 3 + (-1 / 24300000) * alpha ^ 6 + (1 / 2700000) * alpha ^ 6 * c + (1 / 12150000) * alpha ^ 6 * c ^ 2 + (-1 / 8100000) * alpha ^ 7 + (-1 / 8100000) * alpha ^ 7 * c + (1 / 24300000) * alpha ^ 8) * alpha_sq + ((-8 / 28125) * c + (-1 / 759375) * c ^ 3 + (224 / 253125) * alpha + (1 / 253125) * alpha * c ^ 2) * c_sq
theorem phase1_20 : (thetaPlus : ℂ) ^ 2 * star (thetaPlus : ℂ) ^ 0 = ((-73 / 150) + (-1 / 75) * c + (73 / 150) * alpha + (-1 / 225) * alpha * c) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 450) + (1 / 225) * c + (1 / 900) * c ^ 2 + (1 / 450) * alpha + (1 / 450) * alpha * c + (1 / 900) * alpha ^ 2) * alpha_sq + ((-1 / 450) + (1 / 450) * alpha) * c_sq
theorem phase1_21 : (thetaPlus : ℂ) ^ 2 * star (thetaPlus : ℂ) ^ 1 = ((-1 / 10) + (1 / 30) * c + (1 / 30) * alpha + (1 / 30) * alpha * c) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 2250) + (-1 / 6750) * c + (1 / 6750) * c ^ 2 + (-1 / 27000) * c ^ 3 + (-1 / 6750) * alpha + (-1 / 6750) * alpha * c + (-1 / 27000) * alpha * c ^ 2 + (-1 / 27000) * alpha * c ^ 3 + (-1 / 6750) * alpha ^ 2 + (1 / 27000) * alpha ^ 2 * c + (-1 / 27000) * alpha ^ 2 * c ^ 2 + (1 / 27000) * alpha ^ 3 + (1 / 27000) * alpha ^ 3 * c + (1 / 27000) * alpha ^ 4) * alpha_sq + ((-1 / 2250) + (1 / 6750) * c + (1 / 6750) * alpha + (1 / 6750) * alpha * c) * c_sq
theorem phase1_22 : (thetaPlus : ℂ) ^ 2 * star (thetaPlus : ℂ) ^ 2 = (1) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 16875) + (-2 / 50625) * c ^ 2 + (-1 / 162000) * c ^ 4 + (1 / 50625) * alpha ^ 2 + (1 / 81000) * alpha ^ 2 * c ^ 2 + (1 / 810000) * alpha ^ 2 * c ^ 4 + (-1 / 162000) * alpha ^ 4 + (-1 / 405000) * alpha ^ 4 * c ^ 2 + (1 / 810000) * alpha ^ 6) * alpha_sq + ((76 / 16875) + (1 / 50625) * c ^ 2) * c_sq
theorem phase1_23 : (thetaPlus : ℂ) ^ 2 * star (thetaPlus : ℂ) ^ 3 = ((-1 / 10) + (1 / 30) * c + (-1 / 30) * alpha + (-1 / 30) * alpha * c) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 168750) + (-1 / 506250) * c + (1 / 253125) * c ^ 2 + (-1 / 759375) * c ^ 3 + (1 / 1518750) * c ^ 4 + (-1 / 4860000) * c ^ 5 + (1 / 506250) * alpha + (1 / 506250) * alpha * c + (1 / 759375) * alpha * c ^ 2 + (1 / 759375) * alpha * c ^ 3 + (1 / 4860000) * alpha * c ^ 4 + (1 / 4860000) * alpha * c ^ 5 + (-1 / 506250) * alpha ^ 2 + (1 / 1518750) * alpha ^ 2 * c + (-1 / 759375) * alpha ^ 2 * c ^ 2 + (1 / 2430000) * alpha ^ 2 * c ^ 3 + (-1 / 4860000) * alpha ^ 2 * c ^ 4 + (1 / 24300000) * alpha ^ 2 * c ^ 5 + (-1 / 1518750) * alpha ^ 3 + (-1 / 1518750) * alpha ^ 3 * c + (-1 / 2430000) * alpha ^ 3 * c ^ 2 + (-1 / 2430000) * alpha ^ 3 * c ^ 3 + (-1 / 24300000) * alpha ^ 3 * c ^ 4 + (-1 / 24300000) * alpha ^ 3 * c ^ 5 + (1 / 1518750) * alpha ^ 4 + (-1 / 4860000) * alpha ^ 4 * c + (1 / 2430000) * alpha ^ 4 * c ^ 2 + (-1 / 12150000) * alpha ^ 4 * c ^ 3 + (1 / 24300000) * alpha ^ 4 * c ^ 4 + (1 / 4860000) * alpha ^ 5 + (1 / 4860000) * alpha ^ 5 * c + (1 / 12150000) * alpha ^ 5 * c ^ 2 + (1 / 12150000) * alpha ^ 5 * c ^ 3 + (-1 / 4860000) * alpha ^ 6 + (1 / 24300000) * alpha ^ 6 * c + (-1 / 12150000) * alpha ^ 6 * c ^ 2 + (-1 / 24300000) * alpha ^ 7 + (-1 / 24300000) * alpha ^ 7 * c + (1 / 24300000) * alpha ^ 8) * alpha_sq + ((-38 / 84375) + (38 / 253125) * c + (-1 / 506250) * c ^ 2 + (1 / 1518750) * c ^ 3 + (-38 / 253125) * alpha + (-38 / 253125) * alpha * c + (-1 / 1518750) * alpha * c ^ 2 + (-1 / 1518750) * alpha * c ^ 3) * c_sq
theorem phase1_24 : (thetaPlus : ℂ) ^ 2 * star (thetaPlus : ℂ) ^ 4 = ((-73 / 150) + (-1 / 75) * c + (-73 / 150) * alpha + (1 / 225) * alpha * c) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 2531250) + (1 / 1265625) * c + (-1 / 7593750) * c ^ 2 + (2 / 3796875) * c ^ 3 + (1 / 22781250) * c ^ 4 + (1 / 11390625) * c ^ 5 + (11 / 729000000) * c ^ 6 + (-1 / 2531250) * alpha + (-1 / 3796875) * alpha * c + (-1 / 7593750) * alpha * c ^ 2 + (-2 / 11390625) * alpha * c ^ 3 + (1 / 22781250) * alpha * c ^ 4 + (-11 / 364500000) * alpha * c ^ 5 + (1 / 72900000) * alpha * c ^ 6 + (1 / 7593750) * alpha ^ 2 + (-1 / 3796875) * alpha ^ 2 * c + (1 / 22781250) * alpha ^ 2 * c ^ 2 + (-2 / 11390625) * alpha ^ 2 * c ^ 3 + (-11 / 729000000) * alpha ^ 2 * c ^ 4 + (-1 / 36450000) * alpha ^ 2 * c ^ 5 + (-1 / 182250000) * alpha ^ 2 * c ^ 6 + (1 / 7593750) * alpha ^ 3 + (1 / 11390625) * alpha ^ 3 * c + (1 / 22781250) * alpha ^ 3 * c ^ 2 + (11 / 182250000) * alpha ^ 3 * c ^ 3 + (-1 / 72900000) * alpha ^ 3 * c ^ 4 + (1 / 91125000) * alpha ^ 3 * c ^ 5 + (-1 / 364500000) * alpha ^ 3 * c ^ 6 + (-1 / 22781250) * alpha ^ 4 + (1 / 11390625) * alpha ^ 4 * c + (-11 / 729000000) * alpha ^ 4 * c ^ 2 + (1 / 18225000) * alpha ^ 4 * c ^ 3 + (1 / 182250000) * alpha ^ 4 * c ^ 4 + (1 / 182250000) * alpha ^ 4 * c ^ 5 + (1 / 729000000) * alpha ^ 4 * c ^ 6 + (-1 / 22781250) * alpha ^ 5 + (-11 / 364500000) * alpha ^ 5 * c + (-1 / 72900000) * alpha ^ 5 * c ^ 2 + (-1 / 45562500) * alpha ^ 5 * c ^ 3 + (1 / 364500000) * alpha ^ 5 * c ^ 4 + (-1 / 364500000) * alpha ^ 5 * c ^ 5 + (11 / 729000000) * alpha ^ 6 + (-1 / 36450000) * alpha ^ 6 * c + (1 / 182250000) * alpha ^ 6 * c ^ 2 + (-1 / 91125000) * alpha ^ 6 * c ^ 3 + (-1 / 729000000) * alpha ^ 6 * c ^ 4 + (1 / 72900000) * alpha ^ 7 + (1 / 91125000) * alpha ^ 7 * c + (1 / 364500000) * alpha ^ 7 * c ^ 2 + (1 / 182250000) * alpha ^ 7 * c ^ 3 + (-1 / 182250000) * alpha ^ 8 + (1 / 182250000) * alpha ^ 8 * c + (-1 / 729000000) * alpha ^ 8 * c ^ 2 + (-1 / 364500000) * alpha ^ 9 + (-1 / 364500000) * alpha ^ 9 * c + (1 / 729000000) * alpha ^ 10) * alpha_sq + ((-5549 / 2531250) + (-76 / 1265625) * c + (-1 / 101250) * c ^ 2 + (-1 / 3796875) * c ^ 3 + (-1 / 22781250) * c ^ 4 + (-5549 / 2531250) * alpha + (76 / 3796875) * alpha * c + (-1 / 101250) * alpha * c ^ 2 + (1 / 11390625) * alpha * c ^ 3 + (-1 / 22781250) * alpha * c ^ 4) * c_sq
theorem phase1_30 : (thetaPlus : ℂ) ^ 3 * star (thetaPlus : ℂ) ^ 0 = ((-71 / 1125) * c + (-221 / 1125) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 1125) * c + (1 / 9000) * c ^ 3 + (-1 / 3375) * alpha + (1 / 3000) * alpha * c ^ 2 + (1 / 27000) * alpha * c ^ 3 + (1 / 3000) * alpha ^ 2 * c + (1 / 9000) * alpha ^ 2 * c ^ 2 + (1 / 9000) * alpha ^ 3 + (1 / 9000) * alpha ^ 3 * c + (1 / 27000) * alpha ^ 4) * alpha_sq + ((-1 / 3375) * c + (-1 / 1125) * alpha) * c_sq
theorem phase1_31 : (thetaPlus : ℂ) ^ 3 * star (thetaPlus : ℂ) ^ 1 = ((-73 / 150) + (-1 / 75) * c + (73 / 150) * alpha + (-1 / 225) * alpha * c) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 33750) + (1 / 16875) * c + (1 / 50625) * c ^ 3 + (1 / 270000) * c ^ 4 + (1 / 33750) * alpha + (1 / 50625) * alpha * c + (1 / 135000) * alpha * c ^ 3 + (-1 / 405000) * alpha * c ^ 4 + (1 / 101250) * alpha ^ 2 + (-1 / 50625) * alpha ^ 2 * c + (-1 / 202500) * alpha ^ 2 * c ^ 3 + (-1 / 810000) * alpha ^ 2 * c ^ 4 + (-1 / 101250) * alpha ^ 3 + (-1 / 135000) * alpha ^ 3 * c + (-1 / 405000) * alpha ^ 3 * c ^ 3 + (-1 / 270000) * alpha ^ 4 + (1 / 202500) * alpha ^ 4 * c + (1 / 405000) * alpha ^ 5 + (1 / 405000) * alpha ^ 5 * c + (1 / 810000) * alpha ^ 6) * alpha_sq + ((-37 / 16875) + (-1 / 16875) * c + (-1 / 101250) * c ^ 2 + (37 / 16875) * alpha + (-1 / 50625) * alpha * c + (1 / 101250) * alpha * c ^ 2) * c_sq
theorem phase1_32 : (thetaPlus : ℂ) ^ 3 * star (thetaPlus : ℂ) ^ 2 = ((-1 / 10) + (1 / 30) * c + (1 / 30) * alpha + (1 / 30) * alpha * c) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 168750) + (-1 / 506250) * c + (1 / 253125) * c ^ 2 + (-1 / 759375) * c ^ 3 + (1 / 1518750) * c ^ 4 + (-1 / 4860000) * c ^ 5 + (-1 / 506250) * alpha + (-1 / 506250) * alpha * c + (-1 / 759375) * alpha * c ^ 2 + (-1 / 759375) * alpha * c ^ 3 + (-1 / 4860000) * alpha * c ^ 4 + (-1 / 4860000) * alpha * c ^ 5 + (-1 / 506250) * alpha ^ 2 + (1 / 1518750) * alpha ^ 2 * c + (-1 / 759375) * alpha ^ 2 * c ^ 2 + (1 / 2430000) * alpha ^ 2 * c ^ 3 + (-1 / 4860000) * alpha ^ 2 * c ^ 4 + (1 / 24300000) * alpha ^ 2 * c ^ 5 + (1 / 1518750) * alpha ^ 3 + (1 / 1518750) * alpha ^ 3 * c + (1 / 2430000) * alpha ^ 3 * c ^ 2 + (1 / 2430000) * alpha ^ 3 * c ^ 3 + (1 / 24300000) * alpha ^ 3 * c ^ 4 + (1 / 24300000) * alpha ^ 3 * c ^ 5 + (1 / 1518750) * alpha ^ 4 + (-1 / 4860000) * alpha ^ 4 * c + (1 / 2430000) * alpha ^ 4 * c ^ 2 + (-1 / 12150000) * alpha ^ 4 * c ^ 3 + (1 / 24300000) * alpha ^ 4 * c ^ 4 + (-1 / 4860000) * alpha ^ 5 + (-1 / 4860000) * alpha ^ 5 * c + (-1 / 12150000) * alpha ^ 5 * c ^ 2 + (-1 / 12150000) * alpha ^ 5 * c ^ 3 + (-1 / 4860000) * alpha ^ 6 + (1 / 24300000) * alpha ^ 6 * c + (-1 / 12150000) * alpha ^ 6 * c ^ 2 + (1 / 24300000) * alpha ^ 7 + (1 / 24300000) * alpha ^ 7 * c + (1 / 24300000) * alpha ^ 8) * alpha_sq + ((-38 / 84375) + (38 / 253125) * c + (-1 / 506250) * c ^ 2 + (1 / 1518750) * c ^ 3 + (38 / 253125) * alpha + (38 / 253125) * alpha * c + (1 / 1518750) * alpha * c ^ 2 + (1 / 1518750) * alpha * c ^ 3) * c_sq
theorem phase1_33 : (thetaPlus : ℂ) ^ 3 * star (thetaPlus : ℂ) ^ 3 = (1) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 1265625) + (-1 / 1265625) * c ^ 2 + (-1 / 3796875) * c ^ 4 + (-7 / 243000000) * c ^ 6 + (1 / 3796875) * alpha ^ 2 + (1 / 3796875) * alpha ^ 2 * c ^ 2 + (7 / 81000000) * alpha ^ 2 * c ^ 4 + (1 / 121500000) * alpha ^ 2 * c ^ 6 + (-1 / 11390625) * alpha ^ 4 + (-7 / 81000000) * alpha ^ 4 * c ^ 2 + (-1 / 40500000) * alpha ^ 4 * c ^ 4 + (-1 / 729000000) * alpha ^ 4 * c ^ 6 + (7 / 243000000) * alpha ^ 6 + (1 / 40500000) * alpha ^ 6 * c ^ 2 + (1 / 243000000) * alpha ^ 6 * c ^ 4 + (-1 / 121500000) * alpha ^ 8 + (-1 / 243000000) * alpha ^ 8 * c ^ 2 + (1 / 729000000) * alpha ^ 10) * alpha_sq + ((5701 / 1265625) + (77 / 3796875) * c ^ 2 + (1 / 11390625) * c ^ 4) * c_sq
theorem phase1_34 : (thetaPlus : ℂ) ^ 3 * star (thetaPlus : ℂ) ^ 4 = ((-1 / 10) + (1 / 30) * c + (-1 / 30) * alpha + (-1 / 30) * alpha * c) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 12656250) + (-1 / 37968750) * c + (1 / 12656250) * c ^ 2 + (-1 / 37968750) * c ^ 3 + (1 / 37968750) * c ^ 4 + (-1 / 113906250) * c ^ 5 + (1 / 341718750) * c ^ 6 + (-7 / 7290000000) * c ^ 7 + (1 / 37968750) * alpha + (1 / 37968750) * alpha * c + (1 / 37968750) * alpha * c ^ 2 + (1 / 37968750) * alpha * c ^ 3 + (1 / 113906250) * alpha * c ^ 4 + (1 / 113906250) * alpha * c ^ 5 + (7 / 7290000000) * alpha * c ^ 6 + (7 / 7290000000) * alpha * c ^ 7 + (-1 / 37968750) * alpha ^ 2 + (1 / 113906250) * alpha ^ 2 * c + (-1 / 37968750) * alpha ^ 2 * c ^ 2 + (1 / 113906250) * alpha ^ 2 * c ^ 3 + (-1 / 113906250) * alpha ^ 2 * c ^ 4 + (7 / 2430000000) * alpha ^ 2 * c ^ 5 + (-7 / 7290000000) * alpha ^ 2 * c ^ 6 + (1 / 3645000000) * alpha ^ 2 * c ^ 7 + (-1 / 113906250) * alpha ^ 3 + (-1 / 113906250) * alpha ^ 3 * c + (-1 / 113906250) * alpha ^ 3 * c ^ 2 + (-1 / 113906250) * alpha ^ 3 * c ^ 3 + (-7 / 2430000000) * alpha ^ 3 * c ^ 4 + (-7 / 2430000000) * alpha ^ 3 * c ^ 5 + (-1 / 3645000000) * alpha ^ 3 * c ^ 6 + (-1 / 3645000000) * alpha ^ 3 * c ^ 7 + (1 / 113906250) * alpha ^ 4 + (-1 / 341718750) * alpha ^ 4 * c + (1 / 113906250) * alpha ^ 4 * c ^ 2 + (-7 / 2430000000) * alpha ^ 4 * c ^ 3 + (7 / 2430000000) * alpha ^ 4 * c ^ 4 + (-1 / 1215000000) * alpha ^ 4 * c ^ 5 + (1 / 3645000000) * alpha ^ 4 * c ^ 6 + (-1 / 21870000000) * alpha ^ 4 * c ^ 7 + (1 / 341718750) * alpha ^ 5 + (1 / 341718750) * alpha ^ 5 * c + (7 / 2430000000) * alpha ^ 5 * c ^ 2 + (7 / 2430000000) * alpha ^ 5 * c ^ 3 + (1 / 1215000000) * alpha ^ 5 * c ^ 4 + (1 / 1215000000) * alpha ^ 5 * c ^ 5 + (1 / 21870000000) * alpha ^ 5 * c ^ 6 + (1 / 21870000000) * alpha ^ 5 * c ^ 7 + (-1 / 341718750) * alpha ^ 6 + (7 / 7290000000) * alpha ^ 6 * c + (-7 / 2430000000) * alpha ^ 6 * c ^ 2 + (1 / 1215000000) * alpha ^ 6 * c ^ 3 + (-1 / 1215000000) * alpha ^ 6 * c ^ 4 + (1 / 7290000000) * alpha ^ 6 * c ^ 5 + (-1 / 21870000000) * alpha ^ 6 * c ^ 6 + (-7 / 7290000000) * alpha ^ 7 + (-7 / 7290000000) * alpha ^ 7 * c + (-1 / 1215000000) * alpha ^ 7 * c ^ 2 + (-1 / 1215000000) * alpha ^ 7 * c ^ 3 + (-1 / 7290000000) * alpha ^ 7 * c ^ 4 + (-1 / 7290000000) * alpha ^ 7 * c ^ 5 + (7 / 7290000000) * alpha ^ 8 + (-1 / 3645000000) * alpha ^ 8 * c + (1 / 1215000000) * alpha ^ 8 * c ^ 2 + (-1 / 7290000000) * alpha ^ 8 * c ^ 3 + (1 / 7290000000) * alpha ^ 8 * c ^ 4 + (1 / 3645000000) * alpha ^ 9 + (1 / 3645000000) * alpha ^ 9 * c + (1 / 7290000000) * alpha ^ 9 * c ^ 2 + (1 / 7290000000) * alpha ^ 9 * c ^ 3 + (-1 / 3645000000) * alpha ^ 10 + (1 / 21870000000) * alpha ^ 10 * c + (-1 / 7290000000) * alpha ^ 10 * c ^ 2 + (-1 / 21870000000) * alpha ^ 11 + (-1 / 21870000000) * alpha ^ 11 * c + (1 / 21870000000) * alpha ^ 12) * alpha_sq + ((-5701 / 12656250) + (5701 / 37968750) * c + (-77 / 37968750) * c ^ 2 + (77 / 113906250) * c ^ 3 + (-1 / 113906250) * c ^ 4 + (1 / 341718750) * c ^ 5 + (-5701 / 37968750) * alpha + (-5701 / 37968750) * alpha * c + (-77 / 113906250) * alpha * c ^ 2 + (-77 / 113906250) * alpha * c ^ 3 + (-1 / 341718750) * alpha * c ^ 4 + (-1 / 341718750) * alpha * c ^ 5) * c_sq
theorem phase1_40 : (thetaPlus : ℂ) ^ 4 * star (thetaPlus : ℂ) ^ 0 = ((-5033 / 11250) + (146 / 5625) * c + (-5033 / 11250) * alpha + (-146 / 16875) * alpha * c) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 33750) + (2 / 16875) * c + (-1 / 16875) * c ^ 2 + (-2 / 50625) * c ^ 3 + (1 / 270000) * c ^ 4 + (1 / 33750) * alpha + (-2 / 50625) * alpha * c + (-1 / 16875) * alpha * c ^ 2 + (1 / 67500) * alpha * c ^ 3 + (1 / 202500) * alpha * c ^ 4 + (-1 / 101250) * alpha ^ 2 + (-2 / 50625) * alpha ^ 2 * c + (1 / 45000) * alpha ^ 2 * c ^ 2 + (1 / 50625) * alpha ^ 2 * c ^ 3 + (1 / 810000) * alpha ^ 2 * c ^ 4 + (-1 / 101250) * alpha ^ 3 + (1 / 67500) * alpha ^ 3 * c + (1 / 33750) * alpha ^ 3 * c ^ 2 + (1 / 202500) * alpha ^ 3 * c ^ 3 + (1 / 270000) * alpha ^ 4 + (1 / 50625) * alpha ^ 4 * c + (1 / 135000) * alpha ^ 4 * c ^ 2 + (1 / 202500) * alpha ^ 5 + (1 / 202500) * alpha ^ 5 * c + (1 / 810000) * alpha ^ 6) * alpha_sq + ((-34 / 16875) + (2 / 16875) * c + (-1 / 101250) * c ^ 2 + (-34 / 16875) * alpha + (-2 / 50625) * alpha * c + (-1 / 101250) * alpha * c ^ 2) * c_sq
theorem phase1_41 : (thetaPlus : ℂ) ^ 4 * star (thetaPlus : ℂ) ^ 1 = ((-71 / 1125) * c + (-221 / 1125) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 84375) * c + (-2 / 759375) * c ^ 3 + (11 / 24300000) * c ^ 5 + (-1 / 253125) * alpha + (2 / 759375) * alpha * c ^ 2 + (11 / 8100000) * alpha * c ^ 4 + (1 / 24300000) * alpha * c ^ 5 + (1 / 253125) * alpha ^ 2 * c + (11 / 12150000) * alpha ^ 2 * c ^ 3 + (1 / 8100000) * alpha ^ 2 * c ^ 4 + (-1 / 8100000) * alpha ^ 2 * c ^ 5 + (1 / 759375) * alpha ^ 3 + (-11 / 12150000) * alpha ^ 3 * c ^ 2 + (1 / 12150000) * alpha ^ 3 * c ^ 3 + (-1 / 2700000) * alpha ^ 3 * c ^ 4 + (-1 / 24300000) * alpha ^ 3 * c ^ 5 + (-11 / 8100000) * alpha ^ 4 * c + (-1 / 12150000) * alpha ^ 4 * c ^ 2 + (-1 / 4050000) * alpha ^ 4 * c ^ 3 + (-1 / 8100000) * alpha ^ 4 * c ^ 4 + (-11 / 24300000) * alpha ^ 5 + (-1 / 8100000) * alpha ^ 5 * c + (1 / 4050000) * alpha ^ 5 * c ^ 2 + (-1 / 12150000) * alpha ^ 5 * c ^ 3 + (-1 / 24300000) * alpha ^ 6 + (1 / 2700000) * alpha ^ 6 * c + (1 / 12150000) * alpha ^ 6 * c ^ 2 + (1 / 8100000) * alpha ^ 7 + (1 / 8100000) * alpha ^ 7 * c + (1 / 24300000) * alpha ^ 8) * alpha_sq + ((-8 / 28125) * c + (-1 / 759375) * c ^ 3 + (-224 / 253125) * alpha + (-1 / 253125) * alpha * c ^ 2) * c_sq
theorem phase1_42 : (thetaPlus : ℂ) ^ 4 * star (thetaPlus : ℂ) ^ 2 = ((-73 / 150) + (-1 / 75) * c + (73 / 150) * alpha + (-1 / 225) * alpha * c) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 2531250) + (1 / 1265625) * c + (-1 / 7593750) * c ^ 2 + (2 / 3796875) * c ^ 3 + (1 / 22781250) * c ^ 4 + (1 / 11390625) * c ^ 5 + (11 / 729000000) * c ^ 6 + (1 / 2531250) * alpha + (1 / 3796875) * alpha * c + (1 / 7593750) * alpha * c ^ 2 + (2 / 11390625) * alpha * c ^ 3 + (-1 / 22781250) * alpha * c ^ 4 + (11 / 364500000) * alpha * c ^ 5 + (-1 / 72900000) * alpha * c ^ 6 + (1 / 7593750) * alpha ^ 2 + (-1 / 3796875) * alpha ^ 2 * c + (1 / 22781250) * alpha ^ 2 * c ^ 2 + (-2 / 11390625) * alpha ^ 2 * c ^ 3 + (-11 / 729000000) * alpha ^ 2 * c ^ 4 + (-1 / 36450000) * alpha ^ 2 * c ^ 5 + (-1 / 182250000) * alpha ^ 2 * c ^ 6 + (-1 / 7593750) * alpha ^ 3 + (-1 / 11390625) * alpha ^ 3 * c + (-1 / 22781250) * alpha ^ 3 * c ^ 2 + (-11 / 182250000) * alpha ^ 3 * c ^ 3 + (1 / 72900000) * alpha ^ 3 * c ^ 4 + (-1 / 91125000) * alpha ^ 3 * c ^ 5 + (1 / 364500000) * alpha ^ 3 * c ^ 6 + (-1 / 22781250) * alpha ^ 4 + (1 / 11390625) * alpha ^ 4 * c + (-11 / 729000000) * alpha ^ 4 * c ^ 2 + (1 / 18225000) * alpha ^ 4 * c ^ 3 + (1 / 182250000) * alpha ^ 4 * c ^ 4 + (1 / 182250000) * alpha ^ 4 * c ^ 5 + (1 / 729000000) * alpha ^ 4 * c ^ 6 + (1 / 22781250) * alpha ^ 5 + (11 / 364500000) * alpha ^ 5 * c + (1 / 72900000) * alpha ^ 5 * c ^ 2 + (1 / 45562500) * alpha ^ 5 * c ^ 3 + (-1 / 364500000) * alpha ^ 5 * c ^ 4 + (1 / 364500000) * alpha ^ 5 * c ^ 5 + (11 / 729000000) * alpha ^ 6 + (-1 / 36450000) * alpha ^ 6 * c + (1 / 182250000) * alpha ^ 6 * c ^ 2 + (-1 / 91125000) * alpha ^ 6 * c ^ 3 + (-1 / 729000000) * alpha ^ 6 * c ^ 4 + (-1 / 72900000) * alpha ^ 7 + (-1 / 91125000) * alpha ^ 7 * c + (-1 / 364500000) * alpha ^ 7 * c ^ 2 + (-1 / 182250000) * alpha ^ 7 * c ^ 3 + (-1 / 182250000) * alpha ^ 8 + (1 / 182250000) * alpha ^ 8 * c + (-1 / 729000000) * alpha ^ 8 * c ^ 2 + (1 / 364500000) * alpha ^ 9 + (1 / 364500000) * alpha ^ 9 * c + (1 / 729000000) * alpha ^ 10) * alpha_sq + ((-5549 / 2531250) + (-76 / 1265625) * c + (-1 / 101250) * c ^ 2 + (-1 / 3796875) * c ^ 3 + (-1 / 22781250) * c ^ 4 + (5549 / 2531250) * alpha + (-76 / 3796875) * alpha * c + (1 / 101250) * alpha * c ^ 2 + (-1 / 11390625) * alpha * c ^ 3 + (1 / 22781250) * alpha * c ^ 4) * c_sq
theorem phase1_43 : (thetaPlus : ℂ) ^ 4 * star (thetaPlus : ℂ) ^ 3 = ((-1 / 10) + (1 / 30) * c + (1 / 30) * alpha + (1 / 30) * alpha * c) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 12656250) + (-1 / 37968750) * c + (1 / 12656250) * c ^ 2 + (-1 / 37968750) * c ^ 3 + (1 / 37968750) * c ^ 4 + (-1 / 113906250) * c ^ 5 + (1 / 341718750) * c ^ 6 + (-7 / 7290000000) * c ^ 7 + (-1 / 37968750) * alpha + (-1 / 37968750) * alpha * c + (-1 / 37968750) * alpha * c ^ 2 + (-1 / 37968750) * alpha * c ^ 3 + (-1 / 113906250) * alpha * c ^ 4 + (-1 / 113906250) * alpha * c ^ 5 + (-7 / 7290000000) * alpha * c ^ 6 + (-7 / 7290000000) * alpha * c ^ 7 + (-1 / 37968750) * alpha ^ 2 + (1 / 113906250) * alpha ^ 2 * c + (-1 / 37968750) * alpha ^ 2 * c ^ 2 + (1 / 113906250) * alpha ^ 2 * c ^ 3 + (-1 / 113906250) * alpha ^ 2 * c ^ 4 + (7 / 2430000000) * alpha ^ 2 * c ^ 5 + (-7 / 7290000000) * alpha ^ 2 * c ^ 6 + (1 / 3645000000) * alpha ^ 2 * c ^ 7 + (1 / 113906250) * alpha ^ 3 + (1 / 113906250) * alpha ^ 3 * c + (1 / 113906250) * alpha ^ 3 * c ^ 2 + (1 / 113906250) * alpha ^ 3 * c ^ 3 + (7 / 2430000000) * alpha ^ 3 * c ^ 4 + (7 / 2430000000) * alpha ^ 3 * c ^ 5 + (1 / 3645000000) * alpha ^ 3 * c ^ 6 + (1 / 3645000000) * alpha ^ 3 * c ^ 7 + (1 / 113906250) * alpha ^ 4 + (-1 / 341718750) * alpha ^ 4 * c + (1 / 113906250) * alpha ^ 4 * c ^ 2 + (-7 / 2430000000) * alpha ^ 4 * c ^ 3 + (7 / 2430000000) * alpha ^ 4 * c ^ 4 + (-1 / 1215000000) * alpha ^ 4 * c ^ 5 + (1 / 3645000000) * alpha ^ 4 * c ^ 6 + (-1 / 21870000000) * alpha ^ 4 * c ^ 7 + (-1 / 341718750) * alpha ^ 5 + (-1 / 341718750) * alpha ^ 5 * c + (-7 / 2430000000) * alpha ^ 5 * c ^ 2 + (-7 / 2430000000) * alpha ^ 5 * c ^ 3 + (-1 / 1215000000) * alpha ^ 5 * c ^ 4 + (-1 / 1215000000) * alpha ^ 5 * c ^ 5 + (-1 / 21870000000) * alpha ^ 5 * c ^ 6 + (-1 / 21870000000) * alpha ^ 5 * c ^ 7 + (-1 / 341718750) * alpha ^ 6 + (7 / 7290000000) * alpha ^ 6 * c + (-7 / 2430000000) * alpha ^ 6 * c ^ 2 + (1 / 1215000000) * alpha ^ 6 * c ^ 3 + (-1 / 1215000000) * alpha ^ 6 * c ^ 4 + (1 / 7290000000) * alpha ^ 6 * c ^ 5 + (-1 / 21870000000) * alpha ^ 6 * c ^ 6 + (7 / 7290000000) * alpha ^ 7 + (7 / 7290000000) * alpha ^ 7 * c + (1 / 1215000000) * alpha ^ 7 * c ^ 2 + (1 / 1215000000) * alpha ^ 7 * c ^ 3 + (1 / 7290000000) * alpha ^ 7 * c ^ 4 + (1 / 7290000000) * alpha ^ 7 * c ^ 5 + (7 / 7290000000) * alpha ^ 8 + (-1 / 3645000000) * alpha ^ 8 * c + (1 / 1215000000) * alpha ^ 8 * c ^ 2 + (-1 / 7290000000) * alpha ^ 8 * c ^ 3 + (1 / 7290000000) * alpha ^ 8 * c ^ 4 + (-1 / 3645000000) * alpha ^ 9 + (-1 / 3645000000) * alpha ^ 9 * c + (-1 / 7290000000) * alpha ^ 9 * c ^ 2 + (-1 / 7290000000) * alpha ^ 9 * c ^ 3 + (-1 / 3645000000) * alpha ^ 10 + (1 / 21870000000) * alpha ^ 10 * c + (-1 / 7290000000) * alpha ^ 10 * c ^ 2 + (1 / 21870000000) * alpha ^ 11 + (1 / 21870000000) * alpha ^ 11 * c + (1 / 21870000000) * alpha ^ 12) * alpha_sq + ((-5701 / 12656250) + (5701 / 37968750) * c + (-77 / 37968750) * c ^ 2 + (77 / 113906250) * c ^ 3 + (-1 / 113906250) * c ^ 4 + (1 / 341718750) * c ^ 5 + (5701 / 37968750) * alpha + (5701 / 37968750) * alpha * c + (77 / 113906250) * alpha * c ^ 2 + (77 / 113906250) * alpha * c ^ 3 + (1 / 341718750) * alpha * c ^ 4 + (1 / 341718750) * alpha * c ^ 5) * c_sq
theorem phase1_44 : (thetaPlus : ℂ) ^ 4 * star (thetaPlus : ℂ) ^ 4 = (1) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 94921875) + (-4 / 284765625) * c ^ 2 + (-2 / 284765625) * c ^ 4 + (-4 / 2562890625) * c ^ 6 + (-17 / 131220000000) * c ^ 8 + (1 / 284765625) * alpha ^ 2 + (4 / 854296875) * alpha ^ 2 * c ^ 2 + (2 / 854296875) * alpha ^ 2 * c ^ 4 + (17 / 32805000000) * alpha ^ 2 * c ^ 6 + (1 / 24300000000) * alpha ^ 2 * c ^ 8 + (-1 / 854296875) * alpha ^ 4 + (-4 / 2562890625) * alpha ^ 4 * c ^ 2 + (-17 / 21870000000) * alpha ^ 4 * c ^ 4 + (-1 / 6075000000) * alpha ^ 4 * c ^ 6 + (-7 / 656100000000) * alpha ^ 4 * c ^ 8 + (1 / 2562890625) * alpha ^ 6 + (17 / 32805000000) * alpha ^ 6 * c ^ 2 + (1 / 4050000000) * alpha ^ 6 * c ^ 4 + (7 / 164025000000) * alpha ^ 6 * c ^ 6 + (1 / 656100000000) * alpha ^ 6 * c ^ 8 + (-17 / 131220000000) * alpha ^ 8 + (-1 / 6075000000) * alpha ^ 8 * c ^ 2 + (-7 / 109350000000) * alpha ^ 8 * c ^ 4 + (-1 / 164025000000) * alpha ^ 8 * c ^ 6 + (1 / 24300000000) * alpha ^ 10 + (7 / 164025000000) * alpha ^ 10 * c ^ 2 + (1 / 109350000000) * alpha ^ 10 * c ^ 4 + (-7 / 656100000000) * alpha ^ 12 + (-1 / 164025000000) * alpha ^ 12 * c ^ 2 + (1 / 656100000000) * alpha ^ 14) * alpha_sq + ((427576 / 94921875) + (214 / 10546875) * c ^ 2 + (26 / 284765625) * c ^ 4 + (1 / 2562890625) * c ^ 6) * c_sq
noncomputable def z1 : Fin 1 → ℂ := Fin.snoc z0 thetaPlus
theorem v1_00 (t : ℂ) : (momentPoly 1 z1 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00]
  simp only [phase1_00]
  ring
theorem v1_01 (t : ℂ) : (momentPoly 1 z1 0 1).eval t = ((-1 / 10) * t + (1 / 30) * c * t + (-1 / 30) * alpha * t + (-1 / 30) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_01]
  simp only [phase1_00, phase1_01]
  ring
theorem v1_02 (t : ℂ) : (momentPoly 1 z1 0 2).eval t = ((-73 / 150) * t ^ 4 + (-1 / 75) * c * t ^ 4 + (-73 / 150) * alpha * t ^ 4 + (1 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_01, v0_02]
  simp only [phase1_00, phase1_01, phase1_02]
  ring
theorem v1_03 (t : ℂ) : (momentPoly 1 z1 0 3).eval t = ((-71 / 1125) * c * t ^ 9 + (221 / 1125) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_01, v0_02, v0_03]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03]
  ring
theorem v1_04 (t : ℂ) : (momentPoly 1 z1 0 4).eval t = ((-5033 / 11250) * t ^ 16 + (146 / 5625) * c * t ^ 16 + (5033 / 11250) * alpha * t ^ 16 + (146 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_01, v0_02, v0_03, v0_04]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_04]
  ring
theorem v1_10 (t : ℂ) : (momentPoly 1 z1 1 0).eval t = ((-1 / 10) * t + (1 / 30) * c * t + (1 / 30) * alpha * t + (1 / 30) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_10]
  simp only [phase1_00, phase1_10]
  ring
theorem v1_11 (t : ℂ) : (momentPoly 1 z1 1 1).eval t = (1) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_01, v0_10, v0_11]
  simp only [phase1_00, phase1_01, phase1_10, phase1_11]
  ring
theorem v1_12 (t : ℂ) : (momentPoly 1 z1 1 2).eval t = ((-1 / 10) * t + (1 / 30) * c * t + (-1 / 30) * alpha * t + (-1 / 30) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_01, v0_02, v0_10, v0_11, v0_12]
  simp only [phase1_00, phase1_01, phase1_02, phase1_10, phase1_11, phase1_12]
  ring
theorem v1_13 (t : ℂ) : (momentPoly 1 z1 1 3).eval t = ((-73 / 150) * t ^ 4 + (-1 / 75) * c * t ^ 4 + (-73 / 150) * alpha * t ^ 4 + (1 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_01, v0_02, v0_03, v0_10, v0_11, v0_12, v0_13]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_10, phase1_11, phase1_12, phase1_13]
  ring
theorem v1_14 (t : ℂ) : (momentPoly 1 z1 1 4).eval t = ((-71 / 1125) * c * t ^ 9 + (221 / 1125) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_01, v0_02, v0_03, v0_04, v0_10, v0_11, v0_12, v0_13, v0_14]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_04, phase1_10, phase1_11, phase1_12, phase1_13, phase1_14]
  ring
theorem v1_20 (t : ℂ) : (momentPoly 1 z1 2 0).eval t = ((-73 / 150) * t ^ 4 + (-1 / 75) * c * t ^ 4 + (73 / 150) * alpha * t ^ 4 + (-1 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_10, v0_20]
  simp only [phase1_00, phase1_10, phase1_20]
  ring
theorem v1_21 (t : ℂ) : (momentPoly 1 z1 2 1).eval t = ((-1 / 10) * t + (1 / 30) * c * t + (1 / 30) * alpha * t + (1 / 30) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_01, v0_10, v0_11, v0_20, v0_21]
  simp only [phase1_00, phase1_01, phase1_10, phase1_11, phase1_20, phase1_21]
  ring
theorem v1_22 (t : ℂ) : (momentPoly 1 z1 2 2).eval t = (1) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_01, v0_02, v0_10, v0_11, v0_12, v0_20, v0_21, v0_22]
  simp only [phase1_00, phase1_01, phase1_02, phase1_10, phase1_11, phase1_12, phase1_20, phase1_21, phase1_22]
  ring
theorem v1_23 (t : ℂ) : (momentPoly 1 z1 2 3).eval t = ((-1 / 10) * t + (1 / 30) * c * t + (-1 / 30) * alpha * t + (-1 / 30) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_01, v0_02, v0_03, v0_10, v0_11, v0_12, v0_13, v0_20, v0_21, v0_22, v0_23]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_10, phase1_11, phase1_12, phase1_13, phase1_20, phase1_21, phase1_22, phase1_23]
  ring
theorem v1_24 (t : ℂ) : (momentPoly 1 z1 2 4).eval t = ((-73 / 150) * t ^ 4 + (-1 / 75) * c * t ^ 4 + (-73 / 150) * alpha * t ^ 4 + (1 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_01, v0_02, v0_03, v0_04, v0_10, v0_11, v0_12, v0_13, v0_14, v0_20, v0_21, v0_22, v0_23, v0_24]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_04, phase1_10, phase1_11, phase1_12, phase1_13, phase1_14, phase1_20, phase1_21, phase1_22, phase1_23, phase1_24]
  ring
theorem v1_30 (t : ℂ) : (momentPoly 1 z1 3 0).eval t = ((-71 / 1125) * c * t ^ 9 + (-221 / 1125) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_10, v0_20, v0_30]
  simp only [phase1_00, phase1_10, phase1_20, phase1_30]
  ring
theorem v1_31 (t : ℂ) : (momentPoly 1 z1 3 1).eval t = ((-73 / 150) * t ^ 4 + (-1 / 75) * c * t ^ 4 + (73 / 150) * alpha * t ^ 4 + (-1 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_01, v0_10, v0_11, v0_20, v0_21, v0_30, v0_31]
  simp only [phase1_00, phase1_01, phase1_10, phase1_11, phase1_20, phase1_21, phase1_30, phase1_31]
  ring
theorem v1_32 (t : ℂ) : (momentPoly 1 z1 3 2).eval t = ((-1 / 10) * t + (1 / 30) * c * t + (1 / 30) * alpha * t + (1 / 30) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_01, v0_02, v0_10, v0_11, v0_12, v0_20, v0_21, v0_22, v0_30, v0_31, v0_32]
  simp only [phase1_00, phase1_01, phase1_02, phase1_10, phase1_11, phase1_12, phase1_20, phase1_21, phase1_22, phase1_30, phase1_31, phase1_32]
  ring
theorem v1_33 (t : ℂ) : (momentPoly 1 z1 3 3).eval t = (1) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_01, v0_02, v0_03, v0_10, v0_11, v0_12, v0_13, v0_20, v0_21, v0_22, v0_23, v0_30, v0_31, v0_32, v0_33]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_10, phase1_11, phase1_12, phase1_13, phase1_20, phase1_21, phase1_22, phase1_23, phase1_30, phase1_31, phase1_32, phase1_33]
  ring
theorem v1_34 (t : ℂ) : (momentPoly 1 z1 3 4).eval t = ((-1 / 10) * t + (1 / 30) * c * t + (-1 / 30) * alpha * t + (-1 / 30) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_01, v0_02, v0_03, v0_04, v0_10, v0_11, v0_12, v0_13, v0_14, v0_20, v0_21, v0_22, v0_23, v0_24, v0_30, v0_31, v0_32, v0_33, v0_34]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_04, phase1_10, phase1_11, phase1_12, phase1_13, phase1_14, phase1_20, phase1_21, phase1_22, phase1_23, phase1_24, phase1_30, phase1_31, phase1_32, phase1_33, phase1_34]
  ring
theorem v1_40 (t : ℂ) : (momentPoly 1 z1 4 0).eval t = ((-5033 / 11250) * t ^ 16 + (146 / 5625) * c * t ^ 16 + (-5033 / 11250) * alpha * t ^ 16 + (-146 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_10, v0_20, v0_30, v0_40]
  simp only [phase1_00, phase1_10, phase1_20, phase1_30, phase1_40]
  ring
theorem v1_41 (t : ℂ) : (momentPoly 1 z1 4 1).eval t = ((-71 / 1125) * c * t ^ 9 + (-221 / 1125) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_01, v0_10, v0_11, v0_20, v0_21, v0_30, v0_31, v0_40, v0_41]
  simp only [phase1_00, phase1_01, phase1_10, phase1_11, phase1_20, phase1_21, phase1_30, phase1_31, phase1_40, phase1_41]
  ring
theorem v1_42 (t : ℂ) : (momentPoly 1 z1 4 2).eval t = ((-73 / 150) * t ^ 4 + (-1 / 75) * c * t ^ 4 + (73 / 150) * alpha * t ^ 4 + (-1 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_01, v0_02, v0_10, v0_11, v0_12, v0_20, v0_21, v0_22, v0_30, v0_31, v0_32, v0_40, v0_41, v0_42]
  simp only [phase1_00, phase1_01, phase1_02, phase1_10, phase1_11, phase1_12, phase1_20, phase1_21, phase1_22, phase1_30, phase1_31, phase1_32, phase1_40, phase1_41, phase1_42]
  ring
theorem v1_43 (t : ℂ) : (momentPoly 1 z1 4 3).eval t = ((-1 / 10) * t + (1 / 30) * c * t + (1 / 30) * alpha * t + (1 / 30) * alpha * c * t) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_01, v0_02, v0_03, v0_10, v0_11, v0_12, v0_13, v0_20, v0_21, v0_22, v0_23, v0_30, v0_31, v0_32, v0_33, v0_40, v0_41, v0_42, v0_43]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_10, phase1_11, phase1_12, phase1_13, phase1_20, phase1_21, phase1_22, phase1_23, phase1_30, phase1_31, phase1_32, phase1_33, phase1_40, phase1_41, phase1_42, phase1_43]
  ring
theorem v1_44 (t : ℂ) : (momentPoly 1 z1 4 4).eval t = (1) := by
  rw [momentPoly]
  simp only [z1, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v0_00, v0_01, v0_02, v0_03, v0_04, v0_10, v0_11, v0_12, v0_13, v0_14, v0_20, v0_21, v0_22, v0_23, v0_24, v0_30, v0_31, v0_32, v0_33, v0_34, v0_40, v0_41, v0_42, v0_43, v0_44]
  simp only [phase1_00, phase1_01, phase1_02, phase1_03, phase1_04, phase1_10, phase1_11, phase1_12, phase1_13, phase1_14, phase1_20, phase1_21, phase1_22, phase1_23, phase1_24, phase1_30, phase1_31, phase1_32, phase1_33, phase1_34, phase1_40, phase1_41, phase1_42, phase1_43, phase1_44]
  ring
#print axioms v1_00
#print axioms v1_11
#print axioms v1_22
#print axioms v1_33
#print axioms v1_44
end PhotonCertA
