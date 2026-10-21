import PhotonCertA21
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
noncomputable abbrev z21 : Fin 21 → ℂ := PhotonCertA.z21
theorem v21_00 (t : ℂ) : (momentPoly 21 z21 0 0).eval t = (1) :=
  PhotonCertA.v21_00 t
theorem v21_01 (t : ℂ) : (momentPoly 21 z21 0 1).eval t = 0 :=
  PhotonCertA.v21_01 t
theorem v21_02 (t : ℂ) : (momentPoly 21 z21 0 2).eval t = ((-121 / 20) * t ^ 2 + (121 / 20) * t ^ 4 + (73 / 15) * alpha * t ^ 2 + (-73 / 15) * alpha * t ^ 4) :=
  PhotonCertA.v21_02 t
theorem v21_03 (t : ℂ) : (momentPoly 21 z21 0 3).eval t = (2 * t ^ 3 + (-3) * t ^ 5 + 1 * t ^ 9 + (1183 / 200) * alpha * t ^ 3 + (-3549 / 400) * alpha * t ^ 5 + (1183 / 400) * alpha * t ^ 9) :=
  PhotonCertA.v21_03 t
theorem v21_04 (t : ℂ) : (momentPoly 21 z21 0 4).eval t = ((-562081 / 4000) * t ^ 4 + (562081 / 2000) * t ^ 6 + (-975491 / 8000) * t ^ 8 + (-49557 / 2000) * t ^ 10 + (49557 / 8000) * t ^ 16 + (-152627 / 750) * alpha * t ^ 4 + (152627 / 375) * alpha * t ^ 6 + (-142561 / 750) * alpha * t ^ 8 + (-20132 / 1125) * alpha * t ^ 10 + (5033 / 1125) * alpha * t ^ 16) :=
  PhotonCertA.v21_04 t
theorem v21_10 (t : ℂ) : (momentPoly 21 z21 1 0).eval t = 0 :=
  PhotonCertA.v21_10 t
theorem v21_11 (t : ℂ) : (momentPoly 21 z21 1 1).eval t = (21 + (-21) * t ^ 2) :=
  PhotonCertA.v21_11 t
theorem v21_12 (t : ℂ) : (momentPoly 21 z21 1 2).eval t = 0 :=
  PhotonCertA.v21_12 t
theorem v21_13 (t : ℂ) : (momentPoly 21 z21 1 3).eval t = ((-363) * t ^ 2 + (7139 / 10) * t ^ 4 + (-6897 / 20) * t ^ 6 + (-121 / 20) * t ^ 10 + 292 * alpha * t ^ 2 + (-8614 / 15) * alpha * t ^ 4 + (1387 / 5) * alpha * t ^ 6 + (73 / 15) * alpha * t ^ 10) :=
  PhotonCertA.v21_13 t
theorem v21_14 (t : ℂ) : (momentPoly 21 z21 1 4).eval t = (156 * t ^ 3 + (-382) * t ^ 5 + 216 * t ^ 7 + 87 * t ^ 9 + (-76) * t ^ 11 + (-1) * t ^ 17 + (46137 / 100) * alpha * t ^ 3 + (-225953 / 200) * alpha * t ^ 5 + (31941 / 50) * alpha * t ^ 7 + (102921 / 400) * alpha * t ^ 9 + (-22477 / 100) * alpha * t ^ 11 + (-1183 / 400) * alpha * t ^ 17) :=
  PhotonCertA.v21_14 t
theorem v21_20 (t : ℂ) : (momentPoly 21 z21 2 0).eval t = ((-121 / 20) * t ^ 2 + (121 / 20) * t ^ 4 + (-73 / 15) * alpha * t ^ 2 + (73 / 15) * alpha * t ^ 4) :=
  PhotonCertA.v21_20 t
theorem v21_21 (t : ℂ) : (momentPoly 21 z21 2 1).eval t = 0 :=
  PhotonCertA.v21_21 t
theorem v21_22 (t : ℂ) : (momentPoly 21 z21 2 2).eval t = (861 + (-1680) * t ^ 2 + (1036387 / 1200) * t ^ 4 + (-78787 / 600) * t ^ 6 + (103987 / 1200) * t ^ 8) :=
  PhotonCertA.v21_22 t
theorem v21_23 (t : ℂ) : (momentPoly 21 z21 2 3).eval t = ((74259 / 1000) * t ^ 5 + (-74259 / 400) * t ^ 7 + (222777 / 2000) * t ^ 9 + (74259 / 2000) * t ^ 11 + (-74259 / 2000) * t ^ 13 + (-546229 / 12000) * alpha * t ^ 5 + (546229 / 4800) * alpha * t ^ 7 + (-546229 / 8000) * alpha * t ^ 9 + (-546229 / 24000) * alpha * t ^ 11 + (546229 / 24000) * alpha * t ^ 13) :=
  PhotonCertA.v21_23 t
theorem v21_24 (t : ℂ) : (momentPoly 21 z21 2 4).eval t = ((-141691 / 5) * t ^ 2 + (326821 / 4) * t ^ 4 + (-18606765941 / 240000) * t ^ 6 + (2053965941 / 80000) * t ^ 8 + (-360053303 / 96000) * t ^ 10 + (2982691729 / 1440000) * t ^ 12 + (57513131 / 360000) * t ^ 14 + (57513131 / 1440000) * t ^ 18 + (-48801131 / 1440000) * t ^ 20 + (341932 / 15) * alpha * t ^ 2 + (-197173 / 3) * alpha * t ^ 4 + (3754391381 / 60000) * alpha * t ^ 6 + (-425591381 / 20000) * alpha * t ^ 8 + (84942283 / 24000) * alpha * t ^ 10 + (-587290189 / 360000) * alpha * t ^ 12 + (-24100871 / 90000) * alpha * t ^ 14 + (-24100871 / 360000) * alpha * t ^ 18 + (22348871 / 360000) * alpha * t ^ 20) :=
  PhotonCertA.v21_24 t
theorem v21_30 (t : ℂ) : (momentPoly 21 z21 3 0).eval t = (2 * t ^ 3 + (-3) * t ^ 5 + 1 * t ^ 9 + (-1183 / 200) * alpha * t ^ 3 + (3549 / 400) * alpha * t ^ 5 + (-1183 / 400) * alpha * t ^ 9) :=
  PhotonCertA.v21_30 t
theorem v21_31 (t : ℂ) : (momentPoly 21 z21 3 1).eval t = ((-363) * t ^ 2 + (7139 / 10) * t ^ 4 + (-6897 / 20) * t ^ 6 + (-121 / 20) * t ^ 10 + (-292) * alpha * t ^ 2 + (8614 / 15) * alpha * t ^ 4 + (-1387 / 5) * alpha * t ^ 6 + (-73 / 15) * alpha * t ^ 10) :=
  PhotonCertA.v21_31 t
theorem v21_32 (t : ℂ) : (momentPoly 21 z21 3 2).eval t = ((74259 / 1000) * t ^ 5 + (-74259 / 400) * t ^ 7 + (222777 / 2000) * t ^ 9 + (74259 / 2000) * t ^ 11 + (-74259 / 2000) * t ^ 13 + (546229 / 12000) * alpha * t ^ 5 + (-546229 / 4800) * alpha * t ^ 7 + (546229 / 8000) * alpha * t ^ 9 + (546229 / 24000) * alpha * t ^ 11 + (-546229 / 24000) * alpha * t ^ 13) :=
  PhotonCertA.v21_32 t
theorem v21_33 (t : ℂ) : (momentPoly 21 z21 3 3).eval t = (51681 + (-147546) * t ^ 2 + (59074059 / 400) * t ^ 4 + (-2939304433 / 40000) * t ^ 6 + (1404075299 / 40000) * t ^ 8 + (-2142588597 / 160000) * t ^ 10 + (20115867 / 40000) * t ^ 12 + (-44590201 / 80000) * t ^ 14 + (998467 / 160000) * t ^ 18) :=
  PhotonCertA.v21_33 t
theorem v21_34 (t : ℂ) : (momentPoly 21 z21 3 4).eval t = ((8242749 / 500) * t ^ 5 + (-751328229 / 12500) * t ^ 7 + (3744317931 / 50000) * t ^ 9 + (-2743479847 / 100000) * t ^ 11 + (-1627085987 / 120000) * t ^ 13 + (578585897 / 50000) * t ^ 15 + (-361686601 / 200000) * t ^ 17 + (-16394081 / 300000) * t ^ 19 + (-5255231 / 200000) * t ^ 21 + (27532931 / 600000) * t ^ 25 + (-20210473 / 2000) * alpha * t ^ 5 + (27905694423 / 800000) * alpha * t ^ 7 + (-187381658683 / 4800000) * alpha * t ^ 9 + (43468689373 / 4800000) * alpha * t ^ 11 + (57774287803 / 5760000) * alpha * t ^ 13 + (-372012439 / 75000) * alpha * t ^ 15 + (1637236759 / 9600000) * alpha * t ^ 17 + (71051179 / 14400000) * alpha * t ^ 19 + (-256686221 / 9600000) * alpha * t ^ 21 + (-398788579 / 28800000) * alpha * t ^ 25) :=
  PhotonCertA.v21_34 t
theorem v21_40 (t : ℂ) : (momentPoly 21 z21 4 0).eval t = ((-562081 / 4000) * t ^ 4 + (562081 / 2000) * t ^ 6 + (-975491 / 8000) * t ^ 8 + (-49557 / 2000) * t ^ 10 + (49557 / 8000) * t ^ 16 + (152627 / 750) * alpha * t ^ 4 + (-152627 / 375) * alpha * t ^ 6 + (142561 / 750) * alpha * t ^ 8 + (20132 / 1125) * alpha * t ^ 10 + (-5033 / 1125) * alpha * t ^ 16) :=
  PhotonCertA.v21_40 t
theorem v21_41 (t : ℂ) : (momentPoly 21 z21 4 1).eval t = (156 * t ^ 3 + (-382) * t ^ 5 + 216 * t ^ 7 + 87 * t ^ 9 + (-76) * t ^ 11 + (-1) * t ^ 17 + (-46137 / 100) * alpha * t ^ 3 + (225953 / 200) * alpha * t ^ 5 + (-31941 / 50) * alpha * t ^ 7 + (-102921 / 400) * alpha * t ^ 9 + (22477 / 100) * alpha * t ^ 11 + (1183 / 400) * alpha * t ^ 17) :=
  PhotonCertA.v21_41 t
theorem v21_42 (t : ℂ) : (momentPoly 21 z21 4 2).eval t = ((-141691 / 5) * t ^ 2 + (326821 / 4) * t ^ 4 + (-18606765941 / 240000) * t ^ 6 + (2053965941 / 80000) * t ^ 8 + (-360053303 / 96000) * t ^ 10 + (2982691729 / 1440000) * t ^ 12 + (57513131 / 360000) * t ^ 14 + (57513131 / 1440000) * t ^ 18 + (-48801131 / 1440000) * t ^ 20 + (-341932 / 15) * alpha * t ^ 2 + (197173 / 3) * alpha * t ^ 4 + (-3754391381 / 60000) * alpha * t ^ 6 + (425591381 / 20000) * alpha * t ^ 8 + (-84942283 / 24000) * alpha * t ^ 10 + (587290189 / 360000) * alpha * t ^ 12 + (24100871 / 90000) * alpha * t ^ 14 + (24100871 / 360000) * alpha * t ^ 18 + (-22348871 / 360000) * alpha * t ^ 20) :=
  PhotonCertA.v21_42 t
theorem v21_43 (t : ℂ) : (momentPoly 21 z21 4 3).eval t = ((8242749 / 500) * t ^ 5 + (-751328229 / 12500) * t ^ 7 + (3744317931 / 50000) * t ^ 9 + (-2743479847 / 100000) * t ^ 11 + (-1627085987 / 120000) * t ^ 13 + (578585897 / 50000) * t ^ 15 + (-361686601 / 200000) * t ^ 17 + (-16394081 / 300000) * t ^ 19 + (-5255231 / 200000) * t ^ 21 + (27532931 / 600000) * t ^ 25 + (20210473 / 2000) * alpha * t ^ 5 + (-27905694423 / 800000) * alpha * t ^ 7 + (187381658683 / 4800000) * alpha * t ^ 9 + (-43468689373 / 4800000) * alpha * t ^ 11 + (-57774287803 / 5760000) * alpha * t ^ 13 + (372012439 / 75000) * alpha * t ^ 15 + (-1637236759 / 9600000) * alpha * t ^ 17 + (-71051179 / 14400000) * alpha * t ^ 19 + (256686221 / 9600000) * alpha * t ^ 21 + (398788579 / 28800000) * alpha * t ^ 25) :=
  PhotonCertA.v21_43 t
theorem v21_44 (t : ℂ) : (momentPoly 21 z21 4 4).eval t = (4036221 + (-14984424) * t ^ 2 + (2189885731 / 100) * t ^ 4 + (-45074082319 / 2500) * t ^ 6 + (566736924672707 / 48000000) * t ^ 8 + (-77658112021507 / 12000000) * t ^ 10 + (19312097126641 / 9600000) * t ^ 12 + (-31773908311057 / 72000000) * t ^ 14 + (77867340225457 / 576000000) * t ^ 16 + (2665257924007 / 72000000) * t ^ 18 + (-3580114876043 / 432000000) * t ^ 20 + (1254554608237 / 72000000) * t ^ 22 + (-2204023710007 / 288000000) * t ^ 24 + (-144560782867 / 216000000) * t ^ 26 + (133777339267 / 1728000000) * t ^ 32) :=
  PhotonCertA.v21_44 t
#print axioms v21_00
#print axioms v21_11
#print axioms v21_22
#print axioms v21_33
#print axioms v21_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
theorem site22 : ((r ^ 2 * thetaPlus) : ℂ) = ((-1 / 15) * c + (-1 / 15) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 40) * c + (1 / 40) * alpha + (1 / 120) * alpha * c + (1 / 120) * alpha ^ 2) * alpha_sq
theorem phase22_00 : ((r ^ 2 * thetaPlus) : ℂ) ^ 0 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 0 = (1) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase22_01 : ((r ^ 2 * thetaPlus) : ℂ) ^ 0 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 1 = ((-1 / 15) * c + (1 / 15) * alpha) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase22_02 : ((r ^ 2 * thetaPlus) : ℂ) ^ 0 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 2 = ((73 / 75) + (-2 / 225) * alpha * c) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 225)) * alpha_sq + ((1 / 225)) * c_sq
theorem phase22_03 : ((r ^ 2 * thetaPlus) : ℂ) ^ 0 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 3 = ((-71 / 1125) * c + (221 / 1125) * alpha) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 1125) * c + (1 / 3375) * alpha) * alpha_sq + ((-1 / 3375) * c + (1 / 1125) * alpha) * c_sq
theorem phase22_04 : ((r ^ 2 * thetaPlus) : ℂ) ^ 0 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 4 = ((5033 / 5625) + (-292 / 16875) * alpha * c) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 16875) + (2 / 16875) * c ^ 2 + (-4 / 50625) * alpha * c + (1 / 50625) * alpha ^ 2) * alpha_sq + ((68 / 16875) + (1 / 50625) * c ^ 2 + (-4 / 50625) * alpha * c) * c_sq
theorem phase22_10 : ((r ^ 2 * thetaPlus) : ℂ) ^ 1 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 0 = ((-1 / 15) * c + (-1 / 15) * alpha) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase22_11 : ((r ^ 2 * thetaPlus) : ℂ) ^ 1 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 1 = (1) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 225)) * alpha_sq + ((1 / 225)) * c_sq
theorem phase22_12 : ((r ^ 2 * thetaPlus) : ℂ) ^ 1 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 2 = ((-1 / 15) * c + (1 / 15) * alpha) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 3375) * c + (-1 / 3375) * alpha) * alpha_sq + ((-1 / 3375) * c + (1 / 3375) * alpha) * c_sq
theorem phase22_13 : ((r ^ 2 * thetaPlus) : ℂ) ^ 1 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 3 = ((73 / 75) + (-2 / 225) * alpha * c) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 16875) + (2 / 50625) * alpha * c + (-1 / 50625) * alpha ^ 2) * alpha_sq + ((74 / 16875) + (1 / 50625) * c ^ 2 + (-2 / 50625) * alpha * c) * c_sq
theorem phase22_14 : ((r ^ 2 * thetaPlus) : ℂ) ^ 1 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 4 = ((-71 / 1125) * c + (221 / 1125) * alpha) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 84375) * c + (-2 / 759375) * c ^ 3 + (1 / 253125) * alpha + (-2 / 759375) * alpha * c ^ 2 + (1 / 253125) * alpha ^ 2 * c + (-1 / 759375) * alpha ^ 3) * alpha_sq + ((-8 / 28125) * c + (-1 / 759375) * c ^ 3 + (224 / 253125) * alpha + (1 / 253125) * alpha * c ^ 2) * c_sq
theorem phase22_20 : ((r ^ 2 * thetaPlus) : ℂ) ^ 2 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 0 = ((73 / 75) + (2 / 225) * alpha * c) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 225)) * alpha_sq + ((1 / 225)) * c_sq
theorem phase22_21 : ((r ^ 2 * thetaPlus) : ℂ) ^ 2 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 1 = ((-1 / 15) * c + (-1 / 15) * alpha) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 3375) * c + (1 / 3375) * alpha) * alpha_sq + ((-1 / 3375) * c + (-1 / 3375) * alpha) * c_sq
theorem phase22_22 : ((r ^ 2 * thetaPlus) : ℂ) ^ 2 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 2 = (1) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 16875) + (-2 / 50625) * c ^ 2 + (1 / 50625) * alpha ^ 2) * alpha_sq + ((76 / 16875) + (1 / 50625) * c ^ 2) * c_sq
theorem phase22_23 : ((r ^ 2 * thetaPlus) : ℂ) ^ 2 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 3 = ((-1 / 15) * c + (1 / 15) * alpha) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 253125) * c + (2 / 759375) * c ^ 3 + (-1 / 253125) * alpha + (-2 / 759375) * alpha * c ^ 2 + (-1 / 759375) * alpha ^ 2 * c + (1 / 759375) * alpha ^ 3) * alpha_sq + ((-76 / 253125) * c + (-1 / 759375) * c ^ 3 + (76 / 253125) * alpha + (1 / 759375) * alpha * c ^ 2) * c_sq
theorem phase22_24 : ((r ^ 2 * thetaPlus) : ℂ) ^ 2 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 4 = ((73 / 75) + (-2 / 225) * alpha * c) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 1265625) + (1 / 3796875) * c ^ 2 + (-1 / 11390625) * c ^ 4 + (2 / 3796875) * alpha * c + (4 / 11390625) * alpha * c ^ 3 + (-1 / 3796875) * alpha ^ 2 + (-1 / 11390625) * alpha ^ 2 * c ^ 2 + (-2 / 11390625) * alpha ^ 3 * c + (1 / 11390625) * alpha ^ 4) * alpha_sq + ((5549 / 1265625) + (1 / 50625) * c ^ 2 + (1 / 11390625) * c ^ 4 + (-152 / 3796875) * alpha * c + (-2 / 11390625) * alpha * c ^ 3) * c_sq
theorem phase22_30 : ((r ^ 2 * thetaPlus) : ℂ) ^ 3 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 0 = ((-71 / 1125) * c + (-221 / 1125) * alpha) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 1125) * c + (-1 / 3375) * alpha) * alpha_sq + ((-1 / 3375) * c + (-1 / 1125) * alpha) * c_sq
theorem phase22_31 : ((r ^ 2 * thetaPlus) : ℂ) ^ 3 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 1 = ((73 / 75) + (2 / 225) * alpha * c) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 16875) + (-2 / 50625) * alpha * c + (-1 / 50625) * alpha ^ 2) * alpha_sq + ((74 / 16875) + (1 / 50625) * c ^ 2 + (2 / 50625) * alpha * c) * c_sq
theorem phase22_32 : ((r ^ 2 * thetaPlus) : ℂ) ^ 3 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 2 = ((-1 / 15) * c + (-1 / 15) * alpha) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 253125) * c + (2 / 759375) * c ^ 3 + (1 / 253125) * alpha + (2 / 759375) * alpha * c ^ 2 + (-1 / 759375) * alpha ^ 2 * c + (-1 / 759375) * alpha ^ 3) * alpha_sq + ((-76 / 253125) * c + (-1 / 759375) * c ^ 3 + (-76 / 253125) * alpha + (-1 / 759375) * alpha * c ^ 2) * c_sq
theorem phase22_33 : ((r ^ 2 * thetaPlus) : ℂ) ^ 3 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 3 = (1) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 1265625) + (-1 / 1265625) * c ^ 2 + (-1 / 3796875) * c ^ 4 + (1 / 3796875) * alpha ^ 2 + (1 / 3796875) * alpha ^ 2 * c ^ 2 + (-1 / 11390625) * alpha ^ 4) * alpha_sq + ((5701 / 1265625) + (77 / 3796875) * c ^ 2 + (1 / 11390625) * c ^ 4) * c_sq
theorem phase22_34 : ((r ^ 2 * thetaPlus) : ℂ) ^ 3 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 4 = ((-1 / 15) * c + (1 / 15) * alpha) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 18984375) * c + (1 / 18984375) * c ^ 3 + (1 / 56953125) * c ^ 5 + (-1 / 18984375) * alpha + (-1 / 18984375) * alpha * c ^ 2 + (-1 / 56953125) * alpha * c ^ 4 + (-1 / 56953125) * alpha ^ 2 * c + (-1 / 56953125) * alpha ^ 2 * c ^ 3 + (1 / 56953125) * alpha ^ 3 + (1 / 56953125) * alpha ^ 3 * c ^ 2 + (1 / 170859375) * alpha ^ 4 * c + (-1 / 170859375) * alpha ^ 5) * alpha_sq + ((-5701 / 18984375) * c + (-77 / 56953125) * c ^ 3 + (-1 / 170859375) * c ^ 5 + (5701 / 18984375) * alpha + (77 / 56953125) * alpha * c ^ 2 + (1 / 170859375) * alpha * c ^ 4) * c_sq
theorem phase22_40 : ((r ^ 2 * thetaPlus) : ℂ) ^ 4 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 0 = ((5033 / 5625) + (292 / 16875) * alpha * c) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 16875) + (2 / 16875) * c ^ 2 + (4 / 50625) * alpha * c + (1 / 50625) * alpha ^ 2) * alpha_sq + ((68 / 16875) + (1 / 50625) * c ^ 2 + (4 / 50625) * alpha * c) * c_sq
theorem phase22_41 : ((r ^ 2 * thetaPlus) : ℂ) ^ 4 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 1 = ((-71 / 1125) * c + (-221 / 1125) * alpha) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 84375) * c + (-2 / 759375) * c ^ 3 + (-1 / 253125) * alpha + (2 / 759375) * alpha * c ^ 2 + (1 / 253125) * alpha ^ 2 * c + (1 / 759375) * alpha ^ 3) * alpha_sq + ((-8 / 28125) * c + (-1 / 759375) * c ^ 3 + (-224 / 253125) * alpha + (-1 / 253125) * alpha * c ^ 2) * c_sq
theorem phase22_42 : ((r ^ 2 * thetaPlus) : ℂ) ^ 4 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 2 = ((73 / 75) + (2 / 225) * alpha * c) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 1265625) + (1 / 3796875) * c ^ 2 + (-1 / 11390625) * c ^ 4 + (-2 / 3796875) * alpha * c + (-4 / 11390625) * alpha * c ^ 3 + (-1 / 3796875) * alpha ^ 2 + (-1 / 11390625) * alpha ^ 2 * c ^ 2 + (2 / 11390625) * alpha ^ 3 * c + (1 / 11390625) * alpha ^ 4) * alpha_sq + ((5549 / 1265625) + (1 / 50625) * c ^ 2 + (1 / 11390625) * c ^ 4 + (152 / 3796875) * alpha * c + (2 / 11390625) * alpha * c ^ 3) * c_sq
theorem phase22_43 : ((r ^ 2 * thetaPlus) : ℂ) ^ 4 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 3 = ((-1 / 15) * c + (-1 / 15) * alpha) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 18984375) * c + (1 / 18984375) * c ^ 3 + (1 / 56953125) * c ^ 5 + (1 / 18984375) * alpha + (1 / 18984375) * alpha * c ^ 2 + (1 / 56953125) * alpha * c ^ 4 + (-1 / 56953125) * alpha ^ 2 * c + (-1 / 56953125) * alpha ^ 2 * c ^ 3 + (-1 / 56953125) * alpha ^ 3 + (-1 / 56953125) * alpha ^ 3 * c ^ 2 + (1 / 170859375) * alpha ^ 4 * c + (1 / 170859375) * alpha ^ 5) * alpha_sq + ((-5701 / 18984375) * c + (-77 / 56953125) * c ^ 3 + (-1 / 170859375) * c ^ 5 + (-5701 / 18984375) * alpha + (-77 / 56953125) * alpha * c ^ 2 + (-1 / 170859375) * alpha * c ^ 4) * c_sq
theorem phase22_44 : ((r ^ 2 * thetaPlus) : ℂ) ^ 4 * star ((r ^ 2 * thetaPlus) : ℂ) ^ 4 = (1) := by
  rw [site22]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 94921875) + (-4 / 284765625) * c ^ 2 + (-2 / 284765625) * c ^ 4 + (-4 / 2562890625) * c ^ 6 + (1 / 284765625) * alpha ^ 2 + (4 / 854296875) * alpha ^ 2 * c ^ 2 + (2 / 854296875) * alpha ^ 2 * c ^ 4 + (-1 / 854296875) * alpha ^ 4 + (-4 / 2562890625) * alpha ^ 4 * c ^ 2 + (1 / 2562890625) * alpha ^ 6) * alpha_sq + ((427576 / 94921875) + (214 / 10546875) * c ^ 2 + (26 / 284765625) * c ^ 4 + (1 / 2562890625) * c ^ 6) * c_sq
noncomputable def z22 : Fin 22 → ℂ := Fin.snoc z21 (r ^ 2 * thetaPlus)
theorem v22_00 (t : ℂ) : (momentPoly 22 z22 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00]
  try simp only [phase22_00]
  try simp only [star_one, star_neg]
  ring
theorem v22_01 (t : ℂ) : (momentPoly 22 z22 0 1).eval t = ((-1 / 15) * c * t + (1 / 15) * alpha * t) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_01]
  try simp only [phase22_00, phase22_01]
  try simp only [star_one, star_neg]
  ring
theorem v22_02 (t : ℂ) : (momentPoly 22 z22 0 2).eval t = ((-121 / 20) * t ^ 2 + (2107 / 300) * t ^ 4 + (73 / 15) * alpha * t ^ 2 + (-73 / 15) * alpha * t ^ 4 + (-2 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_01, v21_02]
  try simp only [phase22_00, phase22_01, phase22_02]
  try simp only [star_one, star_neg]
  ring
theorem v22_03 (t : ℂ) : (momentPoly 22 z22 0 3).eval t = ((-23 / 25) * t ^ 3 + (-2 / 25) * t ^ 5 + 1 * t ^ 9 + (121 / 100) * c * t ^ 3 + (-121 / 100) * c * t ^ 5 + (-71 / 1125) * c * t ^ 9 + (941 / 200) * alpha * t ^ 3 + (-613 / 80) * alpha * t ^ 5 + (56771 / 18000) * alpha * t ^ 9 + (-73 / 75) * alpha * c * t ^ 3 + (73 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_01, v21_02, v21_03]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5) * alpha_sq
theorem v22_04 (t : ℂ) : (momentPoly 22 z22 0 4).eval t = ((-581009 / 4000) * t ^ 4 + (505613 / 2000) * t ^ 6 + (-138567 / 1600) * t ^ 8 + (-54289 / 2000) * t ^ 10 + (2552177 / 360000) * t ^ 16 + (-8 / 15) * c * t ^ 4 + (592 / 375) * c * t ^ 6 + (-292 / 375) * c * t ^ 8 + (-4 / 15) * c * t ^ 10 + (-152227 / 750) * alpha * t ^ 4 + (32597 / 75) * alpha * t ^ 6 + (-163877 / 750) * alpha * t ^ 8 + (-19832 / 1125) * alpha * t ^ 10 + (5033 / 1125) * alpha * t ^ 16 + (-1183 / 750) * alpha * c * t ^ 4 + (4033 / 1500) * alpha * c * t ^ 6 + (-121 / 375) * alpha * c * t ^ 8 + (-1183 / 1500) * alpha * c * t ^ 10 + (-292 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_01, v21_02, v21_03, v21_04]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04]
  try simp only [star_one, star_neg]
  linear_combination ((1183 / 750) * t ^ 4 + (-1183 / 500) * t ^ 6 + (1183 / 1500) * t ^ 10 + (-292 / 1125) * c * t ^ 6 + (292 / 1125) * c * t ^ 8) * alpha_sq
theorem v22_10 (t : ℂ) : (momentPoly 22 z22 1 0).eval t = ((-1 / 15) * c * t + (-1 / 15) * alpha * t) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_10]
  try simp only [phase22_00, phase22_10]
  try simp only [star_one, star_neg]
  ring
theorem v22_11 (t : ℂ) : (momentPoly 22 z22 1 1).eval t = (22 + (-21) * t ^ 2) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_01, v21_10, v21_11]
  try simp only [phase22_00, phase22_01, phase22_10, phase22_11]
  try simp only [star_one, star_neg]
  ring
theorem v22_12 (t : ℂ) : (momentPoly 22 z22 1 2).eval t = ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-43 / 15) * c * t + (961 / 300) * c * t ^ 3 + (-121 / 300) * c * t ^ 5 + (43 / 15) * alpha * t + (-719 / 300) * alpha * t ^ 3 + (-121 / 300) * alpha * t ^ 5 + (-73 / 225) * alpha * c * t ^ 3 + (73 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_01, v21_02, v21_10, v21_11, v21_12]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_10, phase22_11, phase22_12]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 225) * t ^ 3 + (73 / 225) * t ^ 5) * alpha_sq
theorem v22_13 (t : ℂ) : (momentPoly 22 z22 1 3).eval t = ((-7623 / 20) * t ^ 2 + (2386579 / 3000) * t ^ 4 + (-815889 / 2000) * t ^ 6 + (-10917 / 2000) * t ^ 10 + (-2 / 15) * c * t ^ 4 + (1 / 5) * c * t ^ 6 + (-1 / 15) * c * t ^ 10 + (1533 / 5) * alpha * t ^ 2 + (-589) * alpha * t ^ 4 + (1388 / 5) * alpha * t ^ 6 + (24 / 5) * alpha * t ^ 10 + (-8669 / 9000) * alpha * c * t ^ 4 + (2303 / 2000) * alpha * c * t ^ 6 + (-1183 / 6000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_01, v21_02, v21_03, v21_10, v21_11, v21_12, v21_13]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_10, phase22_11, phase22_12, phase22_13]
  try simp only [star_one, star_neg]
  linear_combination ((-1183 / 3000) * t ^ 4 + (1183 / 2000) * t ^ 6 + (-1183 / 6000) * t ^ 10) * alpha_sq
theorem v22_14 (t : ℂ) : (momentPoly 22 z22 1 4).eval t = ((-1886 / 25) * t ^ 3 + (38191 / 1250) * t ^ 5 + (141527 / 1875) * t ^ 7 + (198689 / 3750) * t ^ 9 + (-469532 / 5625) * t ^ 11 + (-592 / 5625) * t ^ 17 + (4961 / 50) * c * t ^ 3 + (-11005519 / 60000) * c * t ^ 5 + (2196719 / 30000) * c * t ^ 7 + (995273 / 360000) * c * t ^ 9 + (256997 / 30000) * c * t ^ 11 + (-16519 / 40000) * c * t ^ 17 + (38581 / 100) * alpha * t ^ 3 + (-19261873 / 20000) * alpha * t ^ 5 + (15843719 / 30000) * alpha * t ^ 7 + (105825373 / 360000) * alpha * t ^ 9 + (-7236983 / 30000) * alpha * t ^ 11 + (-134819 / 40000) * alpha * t ^ 17 + (-5986 / 75) * alpha * c * t ^ 3 + (1897327 / 11250) * alpha * c * t ^ 5 + (-568727 / 5625) * alpha * c * t ^ 7 + (142561 / 11250) * alpha * c * t ^ 9 + (-1768 / 16875) * alpha * c * t ^ 11 + (-5033 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_01, v21_02, v21_03, v21_04, v21_10, v21_11, v21_12, v21_13, v21_14]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04, phase22_10, phase22_11, phase22_12, phase22_13, phase22_14]
  try simp only [star_one, star_neg]
  linear_combination ((5986 / 75) * t ^ 3 + (-176897 / 1250) * t ^ 5 + (263473 / 5625) * t ^ 7 + (142561 / 11250) * t ^ 9 + (42032 / 16875) * t ^ 11 + (-5033 / 16875) * t ^ 17) * alpha_sq
theorem v22_20 (t : ℂ) : (momentPoly 22 z22 2 0).eval t = ((-121 / 20) * t ^ 2 + (2107 / 300) * t ^ 4 + (-73 / 15) * alpha * t ^ 2 + (73 / 15) * alpha * t ^ 4 + (2 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_10, v21_20]
  try simp only [phase22_00, phase22_10, phase22_20]
  try simp only [star_one, star_neg]
  ring
theorem v22_21 (t : ℂ) : (momentPoly 22 z22 2 1).eval t = ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-43 / 15) * c * t + (961 / 300) * c * t ^ 3 + (-121 / 300) * c * t ^ 5 + (-43 / 15) * alpha * t + (719 / 300) * alpha * t ^ 3 + (121 / 300) * alpha * t ^ 5 + (73 / 225) * alpha * c * t ^ 3 + (-73 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_01, v21_10, v21_11, v21_20, v21_21]
  try simp only [phase22_00, phase22_01, phase22_10, phase22_11, phase22_20, phase22_21]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 225) * t ^ 3 + (73 / 225) * t ^ 5) * alpha_sq
theorem v22_22 (t : ℂ) : (momentPoly 22 z22 2 2).eval t = (946 + (-1764) * t ^ 2 + (1036387 / 1200) * t ^ 4 + (-143089 / 1000) * t ^ 6 + (590599 / 6000) * t ^ 8 + (-292 / 1125) * c * t ^ 6 + (292 / 1125) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_01, v21_02, v21_10, v21_11, v21_12, v21_20, v21_21, v21_22]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_10, phase22_11, phase22_12, phase22_20, phase22_21, phase22_22]
  try simp only [star_one, star_neg]
  linear_combination ((292 / 3375) * c * t ^ 6 + (-292 / 3375) * c * t ^ 8) * alpha_sq
theorem v22_23 (t : ℂ) : (momentPoly 22 z22 2 3).eval t = ((2993 / 25) * t ^ 3 + (-475103 / 3000) * t ^ 5 + (-87289 / 1200) * t ^ 7 + (216937 / 2000) * t ^ 9 + (3774983 / 90000) * t ^ 11 + (-3512183 / 90000) * t ^ 13 + (-542 / 3) * c * t + (39401 / 100) * c * t ^ 3 + (-1614767 / 6000) * c * t ^ 5 + (360423 / 5000) * c * t ^ 7 + (-512837 / 30000) * c * t ^ 9 + (26741 / 22500) * c * t ^ 11 + (-20731 / 45000) * c * t ^ 13 + (542 / 3) * alpha * t + (-29479 / 100) * alpha * t ^ 3 + (73957 / 2400) * alpha * t ^ 5 + (16712717 / 120000) * alpha * t ^ 7 + (-7150003 / 120000) * alpha * t ^ 9 + (-8330891 / 360000) * alpha * t ^ 11 + (9657599 / 360000) * alpha * t ^ 13 + (-2993 / 75) * alpha * c * t ^ 3 + (17447 / 225) * alpha * c * t ^ 5 + (-8318 / 225) * alpha * c * t ^ 7 + (-2 / 75) * alpha * c * t ^ 9 + (-5767 / 16875) * alpha * c * t ^ 11 + (-5033 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_01, v21_02, v21_03, v21_10, v21_11, v21_12, v21_13, v21_20, v21_21, v21_22, v21_23]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_10, phase22_11, phase22_12, phase22_13, phase22_20, phase22_21, phase22_22, phase22_23]
  try simp only [star_one, star_neg]
  linear_combination ((-2993 / 75) * t ^ 3 + (17447 / 225) * t ^ 5 + (-2774 / 75) * t ^ 7 + (-27083 / 16875) * t ^ 11 + (16133 / 16875) * t ^ 13 + (1183 / 22500) * c * t ^ 7 + (-1183 / 15000) * c * t ^ 9 + (1183 / 45000) * c * t ^ 13) * alpha_sq
theorem v22_24 (t : ℂ) : (momentPoly 22 z22 2 4).eval t = ((-62557 / 2) * t ^ 2 + (27850429 / 300) * t ^ 4 + (-21764232037 / 240000) * t ^ 6 + (36895249343 / 1200000) * t ^ 8 + (-3305887509 / 800000) * t ^ 10 + (17186390369 / 7200000) * t ^ 12 + (211379983 / 1800000) * t ^ 14 + (240072503 / 7200000) * t ^ 18 + (-161618171 / 7200000) * t ^ 20 + (-64 / 3) * c * t ^ 4 + (119741 / 3750) * c * t ^ 6 + (2939933 / 112500) * c * t ^ 8 + (-5897671 / 112500) * c * t ^ 10 + (596359 / 112500) * c * t ^ 12 + (3502711 / 337500) * c * t ^ 14 + (-10066 / 84375) * c * t ^ 18 + (2 / 15) * c * t ^ 20 + (75482 / 3) * alpha * t ^ 2 + (-70369) * alpha * t ^ 4 + (155673421 / 2400) * alpha * t ^ 6 + (-19400355881 / 900000) * alpha * t ^ 8 + (7185931049 / 1800000) * alpha * t ^ 10 + (-3233411281 / 1800000) * alpha * t ^ 12 + (-398393861 / 1350000) * alpha * t ^ 14 + (-384307241 / 5400000) * alpha * t ^ 18 + (382261417 / 5400000) * alpha * t ^ 20 + (-24866 / 225) * alpha * c * t ^ 4 + (11530489 / 45000) * alpha * c * t ^ 6 + (-36637373 / 225000) * alpha * c * t ^ 8 + (-1107991 / 150000) * alpha * c * t ^ 10 + (27299719 / 900000) * alpha * c * t ^ 12 + (-2830259 / 450000) * alpha * c * t ^ 14 + (336839 / 675000) * alpha * c * t ^ 18 + (-26797 / 540000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_01, v21_02, v21_03, v21_04, v21_10, v21_11, v21_12, v21_13, v21_14, v21_20, v21_21, v21_22, v21_23, v21_24]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04, phase22_10, phase22_11, phase22_12, phase22_13, phase22_14, phase22_20, phase22_21, phase22_22, phase22_23, phase22_24]
  try simp only [star_one, star_neg]
  linear_combination ((-4732 / 75) * t ^ 4 + (6338831 / 45000) * t ^ 6 + (-986939 / 18000) * t ^ 8 + (-533033 / 10000) * t ^ 10 + (2151011 / 90000) * t ^ 12 + (546229 / 90000) * t ^ 14 + (1183 / 3000) * t ^ 18 + (-152627 / 84375) * c * t ^ 8 + (305254 / 84375) * c * t ^ 10 + (-142561 / 84375) * c * t ^ 12 + (-40264 / 253125) * c * t ^ 14 + (21316 / 253125) * c * t ^ 18 + (-2 / 45) * c * t ^ 20) * alpha_sq
theorem v22_30 (t : ℂ) : (momentPoly 22 z22 3 0).eval t = ((-23 / 25) * t ^ 3 + (-2 / 25) * t ^ 5 + 1 * t ^ 9 + (121 / 100) * c * t ^ 3 + (-121 / 100) * c * t ^ 5 + (-71 / 1125) * c * t ^ 9 + (-941 / 200) * alpha * t ^ 3 + (613 / 80) * alpha * t ^ 5 + (-56771 / 18000) * alpha * t ^ 9 + (73 / 75) * alpha * c * t ^ 3 + (-73 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_10, v21_20, v21_30]
  try simp only [phase22_00, phase22_10, phase22_20, phase22_30]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5) * alpha_sq
theorem v22_31 (t : ℂ) : (momentPoly 22 z22 3 1).eval t = ((-7623 / 20) * t ^ 2 + (2386579 / 3000) * t ^ 4 + (-815889 / 2000) * t ^ 6 + (-10917 / 2000) * t ^ 10 + (-2 / 15) * c * t ^ 4 + (1 / 5) * c * t ^ 6 + (-1 / 15) * c * t ^ 10 + (-1533 / 5) * alpha * t ^ 2 + 589 * alpha * t ^ 4 + (-1388 / 5) * alpha * t ^ 6 + (-24 / 5) * alpha * t ^ 10 + (8669 / 9000) * alpha * c * t ^ 4 + (-2303 / 2000) * alpha * c * t ^ 6 + (1183 / 6000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_01, v21_10, v21_11, v21_20, v21_21, v21_30, v21_31]
  try simp only [phase22_00, phase22_01, phase22_10, phase22_11, phase22_20, phase22_21, phase22_30, phase22_31]
  try simp only [star_one, star_neg]
  linear_combination ((-1183 / 3000) * t ^ 4 + (1183 / 2000) * t ^ 6 + (-1183 / 6000) * t ^ 10) * alpha_sq
theorem v22_32 (t : ℂ) : (momentPoly 22 z22 3 2).eval t = ((2993 / 25) * t ^ 3 + (-475103 / 3000) * t ^ 5 + (-87289 / 1200) * t ^ 7 + (216937 / 2000) * t ^ 9 + (3774983 / 90000) * t ^ 11 + (-3512183 / 90000) * t ^ 13 + (-542 / 3) * c * t + (39401 / 100) * c * t ^ 3 + (-1614767 / 6000) * c * t ^ 5 + (360423 / 5000) * c * t ^ 7 + (-512837 / 30000) * c * t ^ 9 + (26741 / 22500) * c * t ^ 11 + (-20731 / 45000) * c * t ^ 13 + (-542 / 3) * alpha * t + (29479 / 100) * alpha * t ^ 3 + (-73957 / 2400) * alpha * t ^ 5 + (-16712717 / 120000) * alpha * t ^ 7 + (7150003 / 120000) * alpha * t ^ 9 + (8330891 / 360000) * alpha * t ^ 11 + (-9657599 / 360000) * alpha * t ^ 13 + (2993 / 75) * alpha * c * t ^ 3 + (-17447 / 225) * alpha * c * t ^ 5 + (8318 / 225) * alpha * c * t ^ 7 + (2 / 75) * alpha * c * t ^ 9 + (5767 / 16875) * alpha * c * t ^ 11 + (5033 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_01, v21_02, v21_10, v21_11, v21_12, v21_20, v21_21, v21_22, v21_30, v21_31, v21_32]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_10, phase22_11, phase22_12, phase22_20, phase22_21, phase22_22, phase22_30, phase22_31, phase22_32]
  try simp only [star_one, star_neg]
  linear_combination ((-2993 / 75) * t ^ 3 + (17447 / 225) * t ^ 5 + (-2774 / 75) * t ^ 7 + (-27083 / 16875) * t ^ 11 + (16133 / 16875) * t ^ 13 + (1183 / 22500) * c * t ^ 7 + (-1183 / 15000) * c * t ^ 9 + (1183 / 45000) * c * t ^ 13) * alpha_sq
theorem v22_33 (t : ℂ) : (momentPoly 22 z22 3 3).eval t = (59620 + (-162855) * t ^ 2 + (3109161 / 20) * t ^ 4 + (-3074971629 / 40000) * t ^ 6 + (1608914009 / 40000) * t ^ 8 + (-2477925933 / 160000) * t ^ 10 + (289534223 / 600000) * t ^ 12 + (-230342313 / 400000) * t ^ 14 + (23343181 / 2400000) * t ^ 18 + (-579017 / 7500) * c * t ^ 6 + (500761 / 3000) * c * t ^ 8 + (-444697 / 5000) * c * t ^ 10 + (-679691 / 45000) * c * t ^ 12 + (72259 / 5000) * c * t ^ 14 + (-142 / 1125) * c * t ^ 18) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_01, v21_02, v21_03, v21_10, v21_11, v21_12, v21_13, v21_20, v21_21, v21_22, v21_23, v21_30, v21_31, v21_32, v21_33]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_10, phase22_11, phase22_12, phase22_13, phase22_20, phase22_21, phase22_22, phase22_23, phase22_30, phase22_31, phase22_32, phase22_33]
  try simp only [star_one, star_neg]
  linear_combination ((546229 / 30000) * t ^ 6 + (-546229 / 12000) * t ^ 8 + (546229 / 20000) * t ^ 10 + (6101891 / 900000) * t ^ 12 + (-561791 / 100000) * t ^ 14 + (-261443 / 225000) * t ^ 18 + (17812 / 1125) * c * t ^ 6 + (-34748 / 1125) * c * t ^ 8 + (5548 / 375) * c * t ^ 10 + (292 / 1125) * c * t ^ 14) * alpha_sq
theorem v22_34 (t : ℂ) : (momentPoly 22 z22 3 4).eval t = ((359598 / 25) * t ^ 3 + (-11721037 / 500) * t ^ 5 + (-7098314353 / 300000) * t ^ 7 + (251047327 / 4000) * t ^ 9 + (-4922104639 / 200000) * t ^ 11 + (-35003816611 / 2250000) * t ^ 13 + (13837216301 / 1125000) * t ^ 15 + (-19235614957 / 9000000) * t ^ 17 + (-2486683093 / 27000000) * t ^ 19 + (1610309 / 300000) * t ^ 21 + (1334327047 / 27000000) * t ^ 25 + (-44495 / 3) * c * t + (2366943 / 50) * c * t ^ 3 + (-57333683 / 1000) * c * t ^ 5 + (2839753171 / 80000) * c * t ^ 7 + (-5800317277 / 400000) * c * t ^ 9 + (10438563863 / 2400000) * c * t ^ 11 + (-2923363093 / 4000000) * c * t ^ 13 + (207624079 / 1000000) * c * t ^ 15 + (36486121 / 9000000) * c * t ^ 17 + (-9889939 / 1440000) * c * t ^ 19 + (269104183 / 36000000) * c * t ^ 21 + (-4900291 / 9000000) * c * t ^ 25 + (44495 / 3) * alpha * t + (-1770897 / 50) * alpha * t ^ 3 + (1028243 / 80) * alpha * t ^ 5 + (80751603343 / 2400000) * alpha * t ^ 7 + (-185257156183 / 4800000) * alpha * t ^ 9 + (33018266347 / 4800000) * alpha * t ^ 11 + (1695878998127 / 144000000) * alpha * t ^ 13 + (-17971045753 / 3000000) * alpha * t ^ 15 + (8868023401 / 144000000) * alpha * t ^ 17 + (-157645189 / 24000000) * alpha * t ^ 19 + (-2974664807 / 144000000) * alpha * t ^ 21 + (-2550234943 / 144000000) * alpha * t ^ 25 + (-119866 / 25) * alpha * c * t ^ 3 + (1020467 / 75) * alpha * c * t ^ 5 + (-11459094143 / 900000) * alpha * c * t ^ 7 + (1272497999 / 300000) * alpha * c * t ^ 9 + (-14914783 / 24000) * alpha * c * t ^ 11 + (568915771 / 3000000) * alpha * c * t ^ 13 + (633771773 / 6750000) * alpha * c * t ^ 15 + (23585317 / 1687500) * alpha * c * t ^ 17 + (1272729403 / 81000000) * alpha * c * t ^ 19 + (-2478159 / 200000) * alpha * c * t ^ 21 + (-379243 / 1265625) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_01, v21_02, v21_03, v21_04, v21_10, v21_11, v21_12, v21_13, v21_14, v21_20, v21_21, v21_22, v21_23, v21_24, v21_30, v21_31, v21_32, v21_33, v21_34]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04, phase22_10, phase22_11, phase22_12, phase22_13, phase22_14, phase22_20, phase22_21, phase22_22, phase22_23, phase22_24, phase22_30, phase22_31, phase22_32, phase22_33, phase22_34]
  try simp only [star_one, star_neg]
  linear_combination ((-119866 / 25) * t ^ 3 + (1020467 / 75) * t ^ 5 + (-3820967381 / 300000) * t ^ 7 + (425591381 / 100000) * t ^ 9 + (-113287307 / 120000) * t ^ 11 + (22149810979 / 27000000) * t ^ 13 + (-1649505607 / 6750000) * t ^ 15 + (31505981 / 843750) * t ^ 17 + (1059532603 / 81000000) * t ^ 19 + (-22348871 / 1800000) * t ^ 21 + (-1112293 / 1265625) * t ^ 25 + (140777 / 11250) * c * t ^ 7 + (-7395799 / 225000) * c * t ^ 9 + (2079397 / 90000) * c * t ^ 11 + (1496263 / 450000) * c * t ^ 13 + (-3243469 / 450000) * c * t ^ 15 + (546229 / 450000) * c * t ^ 17 + (86359 / 843750) * c * t ^ 19 + (-261443 / 1125000) * c * t ^ 21 + (86359 / 1687500) * c * t ^ 25) * alpha_sq
theorem v22_40 (t : ℂ) : (momentPoly 22 z22 4 0).eval t = ((-581009 / 4000) * t ^ 4 + (505613 / 2000) * t ^ 6 + (-138567 / 1600) * t ^ 8 + (-54289 / 2000) * t ^ 10 + (2552177 / 360000) * t ^ 16 + (-8 / 15) * c * t ^ 4 + (592 / 375) * c * t ^ 6 + (-292 / 375) * c * t ^ 8 + (-4 / 15) * c * t ^ 10 + (152227 / 750) * alpha * t ^ 4 + (-32597 / 75) * alpha * t ^ 6 + (163877 / 750) * alpha * t ^ 8 + (19832 / 1125) * alpha * t ^ 10 + (-5033 / 1125) * alpha * t ^ 16 + (1183 / 750) * alpha * c * t ^ 4 + (-4033 / 1500) * alpha * c * t ^ 6 + (121 / 375) * alpha * c * t ^ 8 + (1183 / 1500) * alpha * c * t ^ 10 + (292 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_10, v21_20, v21_30, v21_40]
  try simp only [phase22_00, phase22_10, phase22_20, phase22_30, phase22_40]
  try simp only [star_one, star_neg]
  linear_combination ((1183 / 750) * t ^ 4 + (-1183 / 500) * t ^ 6 + (1183 / 1500) * t ^ 10 + (-292 / 1125) * c * t ^ 6 + (292 / 1125) * c * t ^ 8) * alpha_sq
theorem v22_41 (t : ℂ) : (momentPoly 22 z22 4 1).eval t = ((-1886 / 25) * t ^ 3 + (38191 / 1250) * t ^ 5 + (141527 / 1875) * t ^ 7 + (198689 / 3750) * t ^ 9 + (-469532 / 5625) * t ^ 11 + (-592 / 5625) * t ^ 17 + (4961 / 50) * c * t ^ 3 + (-11005519 / 60000) * c * t ^ 5 + (2196719 / 30000) * c * t ^ 7 + (995273 / 360000) * c * t ^ 9 + (256997 / 30000) * c * t ^ 11 + (-16519 / 40000) * c * t ^ 17 + (-38581 / 100) * alpha * t ^ 3 + (19261873 / 20000) * alpha * t ^ 5 + (-15843719 / 30000) * alpha * t ^ 7 + (-105825373 / 360000) * alpha * t ^ 9 + (7236983 / 30000) * alpha * t ^ 11 + (134819 / 40000) * alpha * t ^ 17 + (5986 / 75) * alpha * c * t ^ 3 + (-1897327 / 11250) * alpha * c * t ^ 5 + (568727 / 5625) * alpha * c * t ^ 7 + (-142561 / 11250) * alpha * c * t ^ 9 + (1768 / 16875) * alpha * c * t ^ 11 + (5033 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_01, v21_10, v21_11, v21_20, v21_21, v21_30, v21_31, v21_40, v21_41]
  try simp only [phase22_00, phase22_01, phase22_10, phase22_11, phase22_20, phase22_21, phase22_30, phase22_31, phase22_40, phase22_41]
  try simp only [star_one, star_neg]
  linear_combination ((5986 / 75) * t ^ 3 + (-176897 / 1250) * t ^ 5 + (263473 / 5625) * t ^ 7 + (142561 / 11250) * t ^ 9 + (42032 / 16875) * t ^ 11 + (-5033 / 16875) * t ^ 17) * alpha_sq
theorem v22_42 (t : ℂ) : (momentPoly 22 z22 4 2).eval t = ((-62557 / 2) * t ^ 2 + (27850429 / 300) * t ^ 4 + (-21764232037 / 240000) * t ^ 6 + (36895249343 / 1200000) * t ^ 8 + (-3305887509 / 800000) * t ^ 10 + (17186390369 / 7200000) * t ^ 12 + (211379983 / 1800000) * t ^ 14 + (240072503 / 7200000) * t ^ 18 + (-161618171 / 7200000) * t ^ 20 + (-64 / 3) * c * t ^ 4 + (119741 / 3750) * c * t ^ 6 + (2939933 / 112500) * c * t ^ 8 + (-5897671 / 112500) * c * t ^ 10 + (596359 / 112500) * c * t ^ 12 + (3502711 / 337500) * c * t ^ 14 + (-10066 / 84375) * c * t ^ 18 + (2 / 15) * c * t ^ 20 + (-75482 / 3) * alpha * t ^ 2 + 70369 * alpha * t ^ 4 + (-155673421 / 2400) * alpha * t ^ 6 + (19400355881 / 900000) * alpha * t ^ 8 + (-7185931049 / 1800000) * alpha * t ^ 10 + (3233411281 / 1800000) * alpha * t ^ 12 + (398393861 / 1350000) * alpha * t ^ 14 + (384307241 / 5400000) * alpha * t ^ 18 + (-382261417 / 5400000) * alpha * t ^ 20 + (24866 / 225) * alpha * c * t ^ 4 + (-11530489 / 45000) * alpha * c * t ^ 6 + (36637373 / 225000) * alpha * c * t ^ 8 + (1107991 / 150000) * alpha * c * t ^ 10 + (-27299719 / 900000) * alpha * c * t ^ 12 + (2830259 / 450000) * alpha * c * t ^ 14 + (-336839 / 675000) * alpha * c * t ^ 18 + (26797 / 540000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_01, v21_02, v21_10, v21_11, v21_12, v21_20, v21_21, v21_22, v21_30, v21_31, v21_32, v21_40, v21_41, v21_42]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_10, phase22_11, phase22_12, phase22_20, phase22_21, phase22_22, phase22_30, phase22_31, phase22_32, phase22_40, phase22_41, phase22_42]
  try simp only [star_one, star_neg]
  linear_combination ((-4732 / 75) * t ^ 4 + (6338831 / 45000) * t ^ 6 + (-986939 / 18000) * t ^ 8 + (-533033 / 10000) * t ^ 10 + (2151011 / 90000) * t ^ 12 + (546229 / 90000) * t ^ 14 + (1183 / 3000) * t ^ 18 + (-152627 / 84375) * c * t ^ 8 + (305254 / 84375) * c * t ^ 10 + (-142561 / 84375) * c * t ^ 12 + (-40264 / 253125) * c * t ^ 14 + (21316 / 253125) * c * t ^ 18 + (-2 / 45) * c * t ^ 20) * alpha_sq
theorem v22_43 (t : ℂ) : (momentPoly 22 z22 4 3).eval t = ((359598 / 25) * t ^ 3 + (-11721037 / 500) * t ^ 5 + (-7098314353 / 300000) * t ^ 7 + (251047327 / 4000) * t ^ 9 + (-4922104639 / 200000) * t ^ 11 + (-35003816611 / 2250000) * t ^ 13 + (13837216301 / 1125000) * t ^ 15 + (-19235614957 / 9000000) * t ^ 17 + (-2486683093 / 27000000) * t ^ 19 + (1610309 / 300000) * t ^ 21 + (1334327047 / 27000000) * t ^ 25 + (-44495 / 3) * c * t + (2366943 / 50) * c * t ^ 3 + (-57333683 / 1000) * c * t ^ 5 + (2839753171 / 80000) * c * t ^ 7 + (-5800317277 / 400000) * c * t ^ 9 + (10438563863 / 2400000) * c * t ^ 11 + (-2923363093 / 4000000) * c * t ^ 13 + (207624079 / 1000000) * c * t ^ 15 + (36486121 / 9000000) * c * t ^ 17 + (-9889939 / 1440000) * c * t ^ 19 + (269104183 / 36000000) * c * t ^ 21 + (-4900291 / 9000000) * c * t ^ 25 + (-44495 / 3) * alpha * t + (1770897 / 50) * alpha * t ^ 3 + (-1028243 / 80) * alpha * t ^ 5 + (-80751603343 / 2400000) * alpha * t ^ 7 + (185257156183 / 4800000) * alpha * t ^ 9 + (-33018266347 / 4800000) * alpha * t ^ 11 + (-1695878998127 / 144000000) * alpha * t ^ 13 + (17971045753 / 3000000) * alpha * t ^ 15 + (-8868023401 / 144000000) * alpha * t ^ 17 + (157645189 / 24000000) * alpha * t ^ 19 + (2974664807 / 144000000) * alpha * t ^ 21 + (2550234943 / 144000000) * alpha * t ^ 25 + (119866 / 25) * alpha * c * t ^ 3 + (-1020467 / 75) * alpha * c * t ^ 5 + (11459094143 / 900000) * alpha * c * t ^ 7 + (-1272497999 / 300000) * alpha * c * t ^ 9 + (14914783 / 24000) * alpha * c * t ^ 11 + (-568915771 / 3000000) * alpha * c * t ^ 13 + (-633771773 / 6750000) * alpha * c * t ^ 15 + (-23585317 / 1687500) * alpha * c * t ^ 17 + (-1272729403 / 81000000) * alpha * c * t ^ 19 + (2478159 / 200000) * alpha * c * t ^ 21 + (379243 / 1265625) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_01, v21_02, v21_03, v21_10, v21_11, v21_12, v21_13, v21_20, v21_21, v21_22, v21_23, v21_30, v21_31, v21_32, v21_33, v21_40, v21_41, v21_42, v21_43]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_10, phase22_11, phase22_12, phase22_13, phase22_20, phase22_21, phase22_22, phase22_23, phase22_30, phase22_31, phase22_32, phase22_33, phase22_40, phase22_41, phase22_42, phase22_43]
  try simp only [star_one, star_neg]
  linear_combination ((-119866 / 25) * t ^ 3 + (1020467 / 75) * t ^ 5 + (-3820967381 / 300000) * t ^ 7 + (425591381 / 100000) * t ^ 9 + (-113287307 / 120000) * t ^ 11 + (22149810979 / 27000000) * t ^ 13 + (-1649505607 / 6750000) * t ^ 15 + (31505981 / 843750) * t ^ 17 + (1059532603 / 81000000) * t ^ 19 + (-22348871 / 1800000) * t ^ 21 + (-1112293 / 1265625) * t ^ 25 + (140777 / 11250) * c * t ^ 7 + (-7395799 / 225000) * c * t ^ 9 + (2079397 / 90000) * c * t ^ 11 + (1496263 / 450000) * c * t ^ 13 + (-3243469 / 450000) * c * t ^ 15 + (546229 / 450000) * c * t ^ 17 + (86359 / 843750) * c * t ^ 19 + (-261443 / 1125000) * c * t ^ 21 + (86359 / 1687500) * c * t ^ 25) * alpha_sq
theorem v22_44 (t : ℂ) : (momentPoly 22 z22 4 4).eval t = (4894450 + (-17405976) * t ^ 2 + (607322782 / 25) * t ^ 4 + (-24461317953 / 1250) * t ^ 6 + (42896948575341 / 3200000) * t ^ 8 + (-30660617705261 / 4000000) * t ^ 10 + (112131663491941 / 48000000) * t ^ 12 + (-34798941807677 / 72000000) * t ^ 14 + (88965997388273 / 576000000) * t ^ 16 + (2914791220091 / 72000000) * t ^ 18 + (-20715666956071 / 2160000000) * t ^ 20 + (734040360613 / 40000000) * t ^ 22 + (-11904333117107 / 1440000000) * t ^ 24 + (-809679059027 / 1080000000) * t ^ 26 + (764664122639 / 8640000000) * t ^ 32 + (-10359484 / 625) * c * t ^ 6 + (7618236749 / 140625) * c * t ^ 8 + (-11354244343 / 187500) * c * t ^ 10 + (1194905687 / 56250) * c * t ^ 12 + (720896989 / 112500) * c * t ^ 14 + (-259137143 / 45000) * c * t ^ 16 + (1131479287 / 1125000) * c * t ^ 18 + (747939551 / 8437500) * c * t ^ 20 + (-28768721 / 4218750) * c * t ^ 22 + (-2210569 / 16875000) * c * t ^ 24 + (-1119365191 / 50625000) * c * t ^ 26 + (-2939272 / 6328125) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z22, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v21_00, v21_01, v21_02, v21_03, v21_04, v21_10, v21_11, v21_12, v21_13, v21_14, v21_20, v21_21, v21_22, v21_23, v21_24, v21_30, v21_31, v21_32, v21_33, v21_34, v21_40, v21_41, v21_42, v21_43, v21_44]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04, phase22_10, phase22_11, phase22_12, phase22_13, phase22_14, phase22_20, phase22_21, phase22_22, phase22_23, phase22_24, phase22_30, phase22_31, phase22_32, phase22_33, phase22_34, phase22_40, phase22_41, phase22_42, phase22_43, phase22_44]
  try simp only [star_one, star_neg]
  linear_combination ((10378351 / 1875) * t ^ 6 + (-28451923423 / 1500000) * t ^ 8 + (189348083083 / 9000000) * t ^ 10 + (-49422493613 / 9000000) * t ^ 12 + (-39234991003 / 10800000) * t ^ 14 + (230833219 / 140625) * t ^ 16 + (-8999471639 / 18000000) * t ^ 18 + (9466389461 / 27000000) * t ^ 20 + (256686221 / 18000000) * t ^ 22 + (649773859 / 54000000) * t ^ 26 + (188632 / 75) * c * t ^ 6 + (-24213808 / 3375) * c * t ^ 8 + (3798775381 / 562500) * c * t ^ 10 + (-425591381 / 187500) * c * t ^ 12 + (255761249 / 675000) * c * t ^ 14 + (-587290189 / 3375000) * c * t ^ 16 + (-24100871 / 843750) * c * t ^ 18 + (-44567084 / 6328125) * c * t ^ 20 + (351560279 / 50625000) * c * t ^ 22 + (2210569 / 50625000) * c * t ^ 24 + (-11757088 / 18984375) * c * t ^ 26 + (2939272 / 18984375) * c * t ^ 32) * alpha_sq
#print axioms v22_00
#print axioms v22_11
#print axioms v22_22
#print axioms v22_33
#print axioms v22_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
noncomputable def z23 : Fin 23 → ℂ := Fin.snoc z22 (r ^ 2 * thetaPlus)
theorem v23_00 (t : ℂ) : (momentPoly 23 z23 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00]
  try simp only [phase22_00]
  try simp only [star_one, star_neg]
  ring
theorem v23_01 (t : ℂ) : (momentPoly 23 z23 0 1).eval t = ((-2 / 15) * c * t + (2 / 15) * alpha * t) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_01]
  try simp only [phase22_00, phase22_01]
  try simp only [star_one, star_neg]
  ring
theorem v23_02 (t : ℂ) : (momentPoly 23 z23 0 2).eval t = ((-1231 / 300) * t ^ 2 + (2399 / 300) * t ^ 4 + (73 / 15) * alpha * t ^ 2 + (-73 / 15) * alpha * t ^ 4 + (-4 / 225) * alpha * c * t ^ 2 + (-4 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_01, v22_02]
  try simp only [phase22_00, phase22_01, phase22_02]
  try simp only [star_one, star_neg]
  linear_combination ((2 / 225) * t ^ 2) * alpha_sq + ((2 / 225) * t ^ 2) * c_sq
theorem v23_03 (t : ℂ) : (momentPoly 23 z23 0 3).eval t = ((-96 / 25) * t ^ 3 + (71 / 25) * t ^ 5 + 1 * t ^ 9 + (121 / 50) * c * t ^ 3 + (-2099 / 750) * c * t ^ 5 + (-142 / 1125) * c * t ^ 9 + (699 / 200) * alpha * t ^ 3 + (-31643 / 6000) * alpha * t ^ 5 + (60307 / 18000) * alpha * t ^ 9 + (-146 / 75) * alpha * c * t ^ 3 + (146 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_01, v22_02, v22_03]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-4 / 1125) * c * t ^ 5) * alpha_sq + ((4 / 1125) * alpha * t ^ 5) * c_sq
theorem v23_04 (t : ℂ) : (momentPoly 23 z23 0 4).eval t = ((-882593 / 4000) * t ^ 4 + (590473 / 2000) * t ^ 6 + (-5508461 / 120000) * t ^ 8 + (-2011721 / 90000) * t ^ 10 + (2874289 / 360000) * t ^ 16 + (184 / 375) * c * t ^ 4 + (8 / 5) * c * t ^ 6 + (-584 / 375) * c * t ^ 8 + (-8 / 15) * c * t ^ 10 + (-21839 / 150) * alpha * t ^ 4 + (152027 / 375) * alpha * t ^ 6 + (-61731 / 250) * alpha * t ^ 8 + (-19532 / 1125) * alpha * t ^ 10 + (5033 / 1125) * alpha * t ^ 16 + (-941 / 375) * alpha * c * t ^ 4 + (1183 / 250) * alpha * c * t ^ 6 + (-4214 / 5625) * alpha * c * t ^ 8 + (-57907 / 33750) * alpha * c * t ^ 10 + (-584 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_01, v22_02, v22_03, v22_04]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04]
  try simp only [star_one, star_neg]
  linear_combination ((941 / 750) * t ^ 4 + (-613 / 300) * t ^ 6 + (60307 / 67500) * t ^ 10 + (-292 / 1125) * c * t ^ 4 + (292 / 1125) * c * t ^ 8 + (8 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-121 / 375) * t ^ 4 + (121 / 375) * t ^ 6 + (-8 / 5625) * t ^ 8 + (568 / 16875) * t ^ 10 + (292 / 1125) * alpha * t ^ 4 + (-292 / 1125) * alpha * t ^ 6) * c_sq
theorem v23_10 (t : ℂ) : (momentPoly 23 z23 1 0).eval t = ((-2 / 15) * c * t + (-2 / 15) * alpha * t) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_10]
  try simp only [phase22_00, phase22_10]
  try simp only [star_one, star_neg]
  ring
theorem v23_11 (t : ℂ) : (momentPoly 23 z23 1 1).eval t = (23 + (-19) * t ^ 2) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_01, v22_10, v22_11]
  try simp only [phase22_00, phase22_01, phase22_10, phase22_11]
  try simp only [star_one, star_neg]
  linear_combination ((-2 / 225) * t ^ 2) * alpha_sq + ((2 / 225) * t ^ 2) * c_sq
theorem v23_12 (t : ℂ) : (momentPoly 23 z23 1 2).eval t = ((146 / 75) * t ^ 3 + (-146 / 75) * t ^ 5 + (-6) * c * t + (961 / 150) * c * t ^ 3 + (-47 / 50) * c * t ^ 5 + 6 * alpha * t + (-719 / 150) * alpha * t ^ 3 + (-101 / 150) * alpha * t ^ 5 + (-146 / 225) * alpha * c * t ^ 3 + (146 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_01, v22_02, v22_10, v22_11, v22_12]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_10, phase22_11, phase22_12]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 225) * t ^ 3 + (73 / 225) * t ^ 5 + (4 / 3375) * c * t ^ 5) * alpha_sq + ((4 / 3375) * alpha * t ^ 5) * c_sq
theorem v23_13 (t : ℂ) : (momentPoly 23 z23 1 3).eval t = ((-13541 / 50) * t ^ 2 + (1086079 / 1500) * t ^ 4 + (-434739 / 1000) * t ^ 6 + (-8761 / 3000) * t ^ 10 + (-4 / 15) * c * t ^ 4 + (2 / 5) * c * t ^ 6 + (-2 / 15) * c * t ^ 10 + (1606 / 5) * alpha * t ^ 2 + (-8618 / 15) * alpha * t ^ 4 + (1243 / 5) * alpha * t ^ 6 + (71 / 15) * alpha * t ^ 10 + (-88 / 75) * alpha * c * t ^ 2 + (-3869 / 4500) * alpha * c * t ^ 4 + (2303 / 1000) * alpha * c * t ^ 6 + (-3709 / 9000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_01, v22_02, v22_03, v22_10, v22_11, v22_12, v22_13]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_10, phase22_11, phase22_12, phase22_13]
  try simp only [star_one, star_neg]
  linear_combination ((44 / 75) * t ^ 2 + (-793 / 1000) * t ^ 4 + (2581 / 6000) * t ^ 6 + (-60307 / 270000) * t ^ 10) * alpha_sq + ((44 / 75) * t ^ 2 + (-541 / 750) * t ^ 4 + (121 / 750) * t ^ 6 + (142 / 16875) * t ^ 10 + (146 / 1125) * alpha * t ^ 4 + (-146 / 1125) * alpha * t ^ 6) * c_sq
theorem v23_14 (t : ℂ) : (momentPoly 23 z23 1 4).eval t = ((-8256 / 25) * t ^ 3 + (301541 / 625) * t ^ 5 + (-188846 / 1875) * t ^ 7 + (57464 / 1875) * t ^ 9 + (-466564 / 5625) * t ^ 11 + (4441 / 5625) * t ^ 17 + (5203 / 25) * c * t ^ 3 + (-36864077 / 90000) * c * t ^ 5 + (2746439 / 15000) * c * t ^ 7 + (33193 / 180000) * c * t ^ 9 + (256997 / 15000) * c * t ^ 11 + (-171391 / 180000) * c * t ^ 17 + (30057 / 100) * alpha * t ^ 3 + (-57283687 / 90000) * alpha * t ^ 5 + (3638999 / 15000) * alpha * t ^ 7 + (60665003 / 180000) * alpha * t ^ 9 + (-3510533 / 15000) * alpha * t ^ 11 + (-610301 / 180000) * alpha * t ^ 17 + (-12556 / 75) * alpha * c * t ^ 3 + (1941127 / 5625) * alpha * c * t ^ 5 + (-1159354 / 5625) * alpha * c * t ^ 7 + (164461 / 5625) * alpha * c * t ^ 9 + (-3536 / 16875) * alpha * c * t ^ 11 + (-10066 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_01, v22_02, v22_03, v22_04, v22_10, v22_11, v22_12, v22_13, v22_14]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04, phase22_10, phase22_11, phase22_12, phase22_13, phase22_14]
  try simp only [star_one, star_neg]
  linear_combination ((6278 / 75) * t ^ 3 + (-1636673 / 11250) * t ^ 5 + (50683 / 1125) * t ^ 7 + (163877 / 11250) * t ^ 9 + (41432 / 16875) * t ^ 11 + (-5033 / 16875) * t ^ 17 + (-1048 / 3375) * c * t ^ 5 + (1438 / 5625) * c * t ^ 7 + (242 / 5625) * c * t ^ 9 + (584 / 253125) * c * t ^ 17 + (292 / 16875) * c ^ 2 * t ^ 7 + (-292 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((16 / 225) * t ^ 5 + (-1184 / 5625) * t ^ 7 + (584 / 5625) * t ^ 9 + (8 / 225) * t ^ 11 + (8789 / 16875) * alpha * t ^ 5 + (-7393 / 11250) * alpha * t ^ 7 + (242 / 5625) * alpha * t ^ 9 + (1183 / 11250) * alpha * t ^ 11 + (584 / 253125) * alpha * t ^ 17) * c_sq
theorem v23_20 (t : ℂ) : (momentPoly 23 z23 2 0).eval t = ((-1231 / 300) * t ^ 2 + (2399 / 300) * t ^ 4 + (-73 / 15) * alpha * t ^ 2 + (73 / 15) * alpha * t ^ 4 + (4 / 225) * alpha * c * t ^ 2 + (4 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_10, v22_20]
  try simp only [phase22_00, phase22_10, phase22_20]
  try simp only [star_one, star_neg]
  linear_combination ((2 / 225) * t ^ 2) * alpha_sq + ((2 / 225) * t ^ 2) * c_sq
theorem v23_21 (t : ℂ) : (momentPoly 23 z23 2 1).eval t = ((146 / 75) * t ^ 3 + (-146 / 75) * t ^ 5 + (-6) * c * t + (961 / 150) * c * t ^ 3 + (-47 / 50) * c * t ^ 5 + (-6) * alpha * t + (719 / 150) * alpha * t ^ 3 + (101 / 150) * alpha * t ^ 5 + (146 / 225) * alpha * c * t ^ 3 + (-146 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_01, v22_10, v22_11, v22_20, v22_21]
  try simp only [phase22_00, phase22_01, phase22_10, phase22_11, phase22_20, phase22_21]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 225) * t ^ 3 + (73 / 225) * t ^ 5 + (4 / 3375) * c * t ^ 5) * alpha_sq + ((-4 / 3375) * alpha * t ^ 5) * c_sq
theorem v23_22 (t : ℂ) : (momentPoly 23 z23 2 2).eval t = (1035 + (-1672) * t ^ 2 + (4032607 / 6000) * t ^ 4 + (-78787 / 600) * t ^ 6 + (224421 / 2000) * t ^ 8 + (-584 / 1125) * c * t ^ 4 + (584 / 1125) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_01, v22_02, v22_10, v22_11, v22_12, v22_20, v22_21, v22_22]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_10, phase22_11, phase22_12, phase22_20, phase22_21, phase22_22]
  try simp only [star_one, star_neg]
  linear_combination ((-176 / 225) * t ^ 2 + (719 / 1125) * t ^ 4 + (121 / 1125) * t ^ 6 + (292 / 3375) * c * t ^ 4 + (-292 / 3375) * c * t ^ 8 + (-8 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((176 / 225) * t ^ 2 + (-961 / 1125) * t ^ 4 + (121 / 1125) * t ^ 6 + (8 / 16875) * t ^ 8) * c_sq
theorem v23_23 (t : ℂ) : (momentPoly 23 z23 2 3).eval t = ((6278 / 25) * t ^ 3 + (-398781 / 1000) * t ^ 5 + (1721231 / 30000) * t ^ 7 + (2474999 / 30000) * t ^ 9 + (4383511 / 90000) * t ^ 11 + (-3682711 / 90000) * t ^ 13 + (-5942 / 15) * c * t + (41323 / 50) * c * t ^ 3 + (-2804389 / 5000) * c * t ^ 5 + (24923 / 150) * c * t ^ 7 + (-583501 / 15000) * c * t ^ 9 + (49933 / 22500) * c * t ^ 11 + (-23731 / 22500) * c * t ^ 13 + (5942 / 15) * alpha * t + (-30917 / 50) * alpha * t ^ 3 + (7877467 / 60000) * alpha * t ^ 5 + (15115781 / 120000) * alpha * t ^ 7 + (-5541259 / 120000) * alpha * t ^ 9 + (-6395731 / 360000) * alpha * t ^ 11 + (11169763 / 360000) * alpha * t ^ 13 + (-6278 / 75) * alpha * c * t ^ 3 + (11926 / 75) * alpha * c * t ^ 5 + (-138928 / 1875) * alpha * c * t ^ 7 + (284 / 5625) * alpha * c * t ^ 9 + (-11234 / 16875) * alpha * c * t ^ 11 + (-10066 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_01, v22_02, v22_03, v22_10, v22_11, v22_12, v22_13, v22_20, v22_21, v22_22, v22_23]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_10, phase22_11, phase22_12, phase22_13, phase22_20, phase22_21, phase22_22, phase22_23]
  try simp only [star_one, star_neg]
  linear_combination ((-3139 / 75) * t ^ 3 + (5963 / 75) * t ^ 5 + (-2776 / 75) * t ^ 7 + (-26933 / 16875) * t ^ 11 + (16133 / 16875) * t ^ 13 + (14029 / 67500) * c * t ^ 5 + (-7903 / 45000) * c * t ^ 7 + (-1183 / 15000) * c * t ^ 9 + (1183 / 45000) * c * t ^ 11 + (60307 / 2025000) * c * t ^ 13 + (-292 / 16875) * c ^ 2 * t ^ 7 + (292 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((4 / 225) * t ^ 5 + (434 / 5625) * t ^ 7 + (-584 / 5625) * t ^ 9 + (2 / 225) * t ^ 11 + (14029 / 67500) * alpha * t ^ 5 + (-1141 / 5000) * alpha * t ^ 7 + (1183 / 45000) * alpha * t ^ 11 + (-284 / 253125) * alpha * t ^ 13) * c_sq
theorem v23_24 (t : ℂ) : (momentPoly 23 z23 2 4).eval t = ((-349604 / 15) * t ^ 2 + (39217429 / 500) * t ^ 4 + (-99987800209 / 1200000) * t ^ 6 + (11729097553 / 400000) * t ^ 8 + (-8425162807 / 2400000) * t ^ 10 + (16505147533 / 7200000) * t ^ 12 + (44332603 / 360000) * t ^ 14 + (18626881 / 480000) * t ^ 18 + (-21738229 / 2400000) * t ^ 20 + (-224 / 5) * c * t ^ 4 + (2191369 / 28125) * c * t ^ 6 + (1658917 / 56250) * c * t ^ 8 + (-5382691 / 56250) * c * t ^ 10 + (621623 / 56250) * c * t ^ 12 + (3753767 / 168750) * c * t ^ 14 + (-40264 / 84375) * c * t ^ 18 + (4 / 15) * c * t ^ 20 + (82928 / 3) * alpha * t ^ 2 + (-70227) * alpha * t ^ 4 + (51605858363 / 900000) * alpha * t ^ 6 + (-14942426273 / 900000) * alpha * t ^ 8 + (7394197529 / 1800000) * alpha * t ^ 10 + (-10721136611 / 5400000) * alpha * t ^ 12 + (-25931087 / 90000) * alpha * t ^ 14 + (-24004871 / 360000) * alpha * t ^ 18 + (429289769 / 5400000) * alpha * t ^ 20 + (-4544 / 45) * alpha * c * t ^ 2 + (-18146 / 375) * alpha * c * t ^ 4 + (98160469 / 225000) * alpha * c * t ^ 6 + (-8713613 / 28125) * alpha * c * t ^ 8 + (-12182461 / 450000) * alpha * c * t ^ 10 + (85619129 / 1350000) * alpha * c * t ^ 12 + (-10120789 / 675000) * alpha * c * t ^ 14 + (1496027 / 1350000) * alpha * c * t ^ 18 + (-31597 / 270000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_01, v22_02, v22_03, v22_04, v22_10, v22_11, v22_12, v22_13, v22_14, v22_20, v22_21, v22_22, v22_23, v22_24]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04, phase22_10, phase22_11, phase22_12, phase22_13, phase22_14, phase22_20, phase22_21, phase22_22, phase22_23, phase22_24]
  try simp only [star_one, star_neg]
  linear_combination ((2272 / 45) * t ^ 2 + (-16653 / 125) * t ^ 4 + (62257769 / 450000) * t ^ 6 + (-14974721 / 450000) * t ^ 8 + (-52382957 / 900000) * t ^ 10 + (37633391 / 1350000) * t ^ 12 + (2017091 / 270000) * t ^ 14 + (134819 / 300000) * t ^ 18 + (-152627 / 84375) * c * t ^ 6 + (153427 / 84375) * c * t ^ 8 + (182809 / 84375) * c * t ^ 10 + (-148877 / 84375) * c * t ^ 12 + (-124328 / 253125) * c * t ^ 14 + (31382 / 253125) * c * t ^ 18 + (-2 / 45) * c * t ^ 20 + (-1183 / 84375) * c ^ 2 * t ^ 8 + (4033 / 168750) * c ^ 2 * t ^ 10 + (-242 / 84375) * c ^ 2 * t ^ 12 + (-1183 / 168750) * c ^ 2 * t ^ 14 + (-1168 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((2272 / 45) * t ^ 2 + (-15148 / 125) * t ^ 4 + (43591259 / 450000) * t ^ 6 + (-2170777 / 75000) * t ^ 8 + (4380437 / 900000) * t ^ 10 + (-1524959 / 675000) * t ^ 12 + (20731 / 84375) * t ^ 14 + (16519 / 300000) * t ^ 18 + (1168 / 1265625) * t ^ 20 + (8176 / 375) * alpha * t ^ 4 + (-1228609 / 28125) * alpha * t ^ 6 + (1968854 / 84375) * alpha * t ^ 8 + (-139609 / 84375) * alpha * t ^ 10 + (616 / 253125) * alpha * t ^ 12 + (40264 / 253125) * alpha * t ^ 14 + (10066 / 253125) * alpha * t ^ 18) * c_sq
theorem v23_30 (t : ℂ) : (momentPoly 23 z23 3 0).eval t = ((-96 / 25) * t ^ 3 + (71 / 25) * t ^ 5 + 1 * t ^ 9 + (121 / 50) * c * t ^ 3 + (-2099 / 750) * c * t ^ 5 + (-142 / 1125) * c * t ^ 9 + (-699 / 200) * alpha * t ^ 3 + (31643 / 6000) * alpha * t ^ 5 + (-60307 / 18000) * alpha * t ^ 9 + (146 / 75) * alpha * c * t ^ 3 + (-146 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_10, v22_20, v22_30]
  try simp only [phase22_00, phase22_10, phase22_20, phase22_30]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-4 / 1125) * c * t ^ 5) * alpha_sq + ((-4 / 1125) * alpha * t ^ 5) * c_sq
theorem v23_31 (t : ℂ) : (momentPoly 23 z23 3 1).eval t = ((-13541 / 50) * t ^ 2 + (1086079 / 1500) * t ^ 4 + (-434739 / 1000) * t ^ 6 + (-8761 / 3000) * t ^ 10 + (-4 / 15) * c * t ^ 4 + (2 / 5) * c * t ^ 6 + (-2 / 15) * c * t ^ 10 + (-1606 / 5) * alpha * t ^ 2 + (8618 / 15) * alpha * t ^ 4 + (-1243 / 5) * alpha * t ^ 6 + (-71 / 15) * alpha * t ^ 10 + (88 / 75) * alpha * c * t ^ 2 + (3869 / 4500) * alpha * c * t ^ 4 + (-2303 / 1000) * alpha * c * t ^ 6 + (3709 / 9000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_01, v22_10, v22_11, v22_20, v22_21, v22_30, v22_31]
  try simp only [phase22_00, phase22_01, phase22_10, phase22_11, phase22_20, phase22_21, phase22_30, phase22_31]
  try simp only [star_one, star_neg]
  linear_combination ((44 / 75) * t ^ 2 + (-793 / 1000) * t ^ 4 + (2581 / 6000) * t ^ 6 + (-60307 / 270000) * t ^ 10) * alpha_sq + ((44 / 75) * t ^ 2 + (-541 / 750) * t ^ 4 + (121 / 750) * t ^ 6 + (142 / 16875) * t ^ 10 + (-146 / 1125) * alpha * t ^ 4 + (146 / 1125) * alpha * t ^ 6) * c_sq
theorem v23_32 (t : ℂ) : (momentPoly 23 z23 3 2).eval t = ((6278 / 25) * t ^ 3 + (-398781 / 1000) * t ^ 5 + (1721231 / 30000) * t ^ 7 + (2474999 / 30000) * t ^ 9 + (4383511 / 90000) * t ^ 11 + (-3682711 / 90000) * t ^ 13 + (-5942 / 15) * c * t + (41323 / 50) * c * t ^ 3 + (-2804389 / 5000) * c * t ^ 5 + (24923 / 150) * c * t ^ 7 + (-583501 / 15000) * c * t ^ 9 + (49933 / 22500) * c * t ^ 11 + (-23731 / 22500) * c * t ^ 13 + (-5942 / 15) * alpha * t + (30917 / 50) * alpha * t ^ 3 + (-7877467 / 60000) * alpha * t ^ 5 + (-15115781 / 120000) * alpha * t ^ 7 + (5541259 / 120000) * alpha * t ^ 9 + (6395731 / 360000) * alpha * t ^ 11 + (-11169763 / 360000) * alpha * t ^ 13 + (6278 / 75) * alpha * c * t ^ 3 + (-11926 / 75) * alpha * c * t ^ 5 + (138928 / 1875) * alpha * c * t ^ 7 + (-284 / 5625) * alpha * c * t ^ 9 + (11234 / 16875) * alpha * c * t ^ 11 + (10066 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_01, v22_02, v22_10, v22_11, v22_12, v22_20, v22_21, v22_22, v22_30, v22_31, v22_32]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_10, phase22_11, phase22_12, phase22_20, phase22_21, phase22_22, phase22_30, phase22_31, phase22_32]
  try simp only [star_one, star_neg]
  linear_combination ((-3139 / 75) * t ^ 3 + (5963 / 75) * t ^ 5 + (-2776 / 75) * t ^ 7 + (-26933 / 16875) * t ^ 11 + (16133 / 16875) * t ^ 13 + (14029 / 67500) * c * t ^ 5 + (-7903 / 45000) * c * t ^ 7 + (-1183 / 15000) * c * t ^ 9 + (1183 / 45000) * c * t ^ 11 + (60307 / 2025000) * c * t ^ 13 + (-292 / 16875) * c ^ 2 * t ^ 7 + (292 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((4 / 225) * t ^ 5 + (434 / 5625) * t ^ 7 + (-584 / 5625) * t ^ 9 + (2 / 225) * t ^ 11 + (-14029 / 67500) * alpha * t ^ 5 + (1141 / 5000) * alpha * t ^ 7 + (-1183 / 45000) * alpha * t ^ 11 + (284 / 253125) * alpha * t ^ 13) * c_sq
theorem v23_33 (t : ℂ) : (momentPoly 23 z23 3 3).eval t = (68333 + (-161880) * t ^ 2 + (254054241 / 2000) * t ^ 4 + (-451054509 / 8000) * t ^ 6 + (7919236571 / 200000) * t ^ 8 + (-13171069401 / 800000) * t ^ 10 + (192533641 / 600000) * t ^ 12 + (-40220369 / 80000) * t ^ 14 + (36509357 / 2400000) * t ^ 18 + (-12264 / 125) * c * t ^ 4 + (36701 / 1250) * c * t ^ 6 + (24823 / 100) * c * t ^ 8 + (-439017 / 2500) * c * t ^ 10 + (-749771 / 22500) * c * t ^ 12 + (74259 / 2500) * c * t ^ 14 + (-284 / 1125) * c * t ^ 18) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_01, v22_02, v22_03, v22_10, v22_11, v22_12, v22_13, v22_20, v22_21, v22_22, v22_23, v22_30, v22_31, v22_32, v22_33]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_10, phase22_11, phase22_12, phase22_13, phase22_20, phase22_21, phase22_22, phase22_23, phase22_30, phase22_31, phase22_32, phase22_33]
  try simp only [star_one, star_neg]
  linear_combination ((-1136 / 15) * t ^ 2 + (15099 / 125) * t ^ 4 + (-71053 / 6000) * t ^ 6 + (-16712717 / 300000) * t ^ 8 + (7150003 / 300000) * t ^ 10 + (2222401 / 300000) * t ^ 12 + (-6948139 / 900000) * t ^ 14 + (-12546391 / 10125000) * t ^ 18 + (2044 / 125) * c * t ^ 4 + (-5548 / 375) * c * t ^ 6 + (-6332 / 375) * c * t ^ 8 + (1852 / 125) * c * t ^ 10 + (584 / 1125) * c * t ^ 12 + (-8 / 1125) * c * t ^ 14 + (-8749 / 168750) * c ^ 2 * t ^ 8 + (2303 / 37500) * c ^ 2 * t ^ 10 + (-1183 / 112500) * c ^ 2 * t ^ 14) * alpha_sq + ((1136 / 15) * t ^ 2 + (-20181 / 125) * t ^ 4 + (1622027 / 15000) * t ^ 6 + (-3226309 / 112500) * t ^ 8 + (499019 / 75000) * t ^ 10 + (-17666 / 28125) * t ^ 12 + (20731 / 56250) * t ^ 14 + (10082 / 1265625) * t ^ 18) * c_sq
theorem v23_34 (t : ℂ) : (momentPoly 23 z23 3 4).eval t = ((791904 / 25) * t ^ 3 + (-34014983 / 500) * t ^ 5 + (3240698563 / 150000) * t ^ 7 + (1042993237 / 31250) * t ^ 9 + (-490309621 / 46875) * t ^ 11 + (-2085399733 / 120000) * t ^ 13 + (350962801 / 30000) * t ^ 15 + (-22252136069 / 9000000) * t ^ 17 + (-174215081 / 1687500) * t ^ 19 + (320600639 / 9000000) * t ^ 21 + (1429672199 / 27000000) * t ^ 25 + (-511546 / 15) * c * t + (2606232 / 25) * c * t ^ 3 + (-308639397 / 2500) * c * t ^ 5 + (15660519983 / 200000) * c * t ^ 7 + (-101522147951 / 3000000) * c * t ^ 9 + (59922556307 / 6000000) * c * t ^ 11 + (-29282053169 / 18000000) * c * t ^ 13 + (720313621 / 1500000) * c * t ^ 15 + (10560889 / 4500000) * c * t ^ 17 + (-230958779 / 18000000) * c * t ^ 19 + (185644819 / 18000000) * c * t ^ 21 + (-5500291 / 4500000) * c * t ^ 25 + (511546 / 15) * alpha * t + (-1949928 / 25) * alpha * t ^ 3 + (426985947 / 10000) * alpha * t ^ 5 + (48668797241 / 2400000) * alpha * t ^ 7 + (-679252387583 / 24000000) * alpha * t ^ 9 + (29366101503 / 8000000) * alpha * t ^ 11 + (1795068509947 / 144000000) * alpha * t ^ 13 + (-3382054677 / 500000) * alpha * t ^ 15 + (-9805815559 / 144000000) * alpha * t ^ 17 + (-2924265013 / 72000000) * alpha * t ^ 19 + (-2123583211 / 144000000) * alpha * t ^ 21 + (-1029108997 / 48000000) * alpha * t ^ 25 + (-263968 / 25) * alpha * c * t ^ 3 + (2182042 / 75) * alpha * c * t ^ 5 + (-158440781 / 6000) * alpha * c * t ^ 7 + (19442484857 / 2250000) * alpha * c * t ^ 9 + (-6462571993 / 4500000) * alpha * c * t ^ 11 + (1177900967 / 2700000) * alpha * c * t ^ 13 + (43743223 / 225000) * alpha * c * t ^ 15 + (26782717 / 843750) * alpha * c * t ^ 17 + (1342478203 / 40500000) * alpha * c * t ^ 19 + (-382299817 / 13500000) * alpha * c * t ^ 21 + (-758486 / 1265625) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_01, v22_02, v22_03, v22_04, v22_10, v22_11, v22_12, v22_13, v22_14, v22_20, v22_21, v22_22, v22_23, v22_24, v22_30, v22_31, v22_32, v22_33, v22_34]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04, phase22_10, phase22_11, phase22_12, phase22_13, phase22_14, phase22_20, phase22_21, phase22_22, phase22_23, phase22_24, phase22_30, phase22_31, phase22_32, phase22_33, phase22_34]
  try simp only [star_one, star_neg]
  linear_combination ((-131984 / 25) * t ^ 3 + (1091021 / 75) * t ^ 5 + (-158338381 / 12000) * t ^ 7 + (19400355881 / 4500000) * t ^ 9 + (-9414579049 / 9000000) * t ^ 11 + (23350445587 / 27000000) * t ^ 13 + (-550103833 / 2250000) * t ^ 15 + (36216817 / 843750) * t ^ 17 + (1127915131 / 81000000) * t ^ 19 + (-382261417 / 27000000) * t ^ 21 + (-1112293 / 1265625) * t ^ 25 + (369229 / 11250) * c * t ^ 5 + (-1442251 / 25000) * c * t ^ 7 + (6159059 / 750000) * c * t ^ 9 + (4339919 / 187500) * c * t ^ 11 + (-4482359 / 20250000) * c * t ^ 13 + (-2646737 / 337500) * c * t ^ 15 + (2017091 / 1350000) * c * t ^ 17 + (196741 / 675000) * c * t ^ 19 + (-1434673 / 6750000) * c * t ^ 21 + (4402411 / 75937500) * c * t ^ 25 + (-584 / 135) * c ^ 2 * t ^ 7 + (3671227 / 421875) * c ^ 2 * t ^ 9 + (-218806 / 46875) * c ^ 2 * t ^ 11 + (141961 / 421875) * c ^ 2 * t ^ 13 + (-2956 / 140625) * c ^ 2 * t ^ 15 + (-20132 / 1265625) * c ^ 2 * t ^ 17 + (-21316 / 1265625) * c ^ 2 * t ^ 19 + (2 / 225) * c ^ 2 * t ^ 21) * alpha_sq + ((328 / 75) * t ^ 5 + (1537331 / 56250) * t ^ 7 + (-42838091 / 562500) * t ^ 9 + (27145597 / 562500) * t ^ 11 + (3417901 / 1687500) * t ^ 13 + (-3384311 / 562500) * t ^ 15 + (40864 / 421875) * t ^ 17 + (59782 / 421875) * t ^ 19 + (-4 / 75) * t ^ 21 + (369229 / 11250) * alpha * t ^ 5 + (-15937759 / 225000) * alpha * t ^ 7 + (94564567 / 2250000) * alpha * t ^ 9 + (-577841 / 2250000) * alpha * t ^ 11 + (-52940687 / 10125000) * alpha * t ^ 13 + (10421687 / 6750000) * alpha * t ^ 15 + (37913 / 843750) * alpha * t ^ 17 + (-407503 / 3375000) * alpha * t ^ 19 + (26797 / 1350000) * alpha * t ^ 21 + (41464 / 18984375) * alpha * t ^ 25) * c_sq
theorem v23_40 (t : ℂ) : (momentPoly 23 z23 4 0).eval t = ((-882593 / 4000) * t ^ 4 + (590473 / 2000) * t ^ 6 + (-5508461 / 120000) * t ^ 8 + (-2011721 / 90000) * t ^ 10 + (2874289 / 360000) * t ^ 16 + (184 / 375) * c * t ^ 4 + (8 / 5) * c * t ^ 6 + (-584 / 375) * c * t ^ 8 + (-8 / 15) * c * t ^ 10 + (21839 / 150) * alpha * t ^ 4 + (-152027 / 375) * alpha * t ^ 6 + (61731 / 250) * alpha * t ^ 8 + (19532 / 1125) * alpha * t ^ 10 + (-5033 / 1125) * alpha * t ^ 16 + (941 / 375) * alpha * c * t ^ 4 + (-1183 / 250) * alpha * c * t ^ 6 + (4214 / 5625) * alpha * c * t ^ 8 + (57907 / 33750) * alpha * c * t ^ 10 + (584 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_10, v22_20, v22_30, v22_40]
  try simp only [phase22_00, phase22_10, phase22_20, phase22_30, phase22_40]
  try simp only [star_one, star_neg]
  linear_combination ((941 / 750) * t ^ 4 + (-613 / 300) * t ^ 6 + (60307 / 67500) * t ^ 10 + (-292 / 1125) * c * t ^ 4 + (292 / 1125) * c * t ^ 8 + (8 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-121 / 375) * t ^ 4 + (121 / 375) * t ^ 6 + (-8 / 5625) * t ^ 8 + (568 / 16875) * t ^ 10 + (-292 / 1125) * alpha * t ^ 4 + (292 / 1125) * alpha * t ^ 6) * c_sq
theorem v23_41 (t : ℂ) : (momentPoly 23 z23 4 1).eval t = ((-8256 / 25) * t ^ 3 + (301541 / 625) * t ^ 5 + (-188846 / 1875) * t ^ 7 + (57464 / 1875) * t ^ 9 + (-466564 / 5625) * t ^ 11 + (4441 / 5625) * t ^ 17 + (5203 / 25) * c * t ^ 3 + (-36864077 / 90000) * c * t ^ 5 + (2746439 / 15000) * c * t ^ 7 + (33193 / 180000) * c * t ^ 9 + (256997 / 15000) * c * t ^ 11 + (-171391 / 180000) * c * t ^ 17 + (-30057 / 100) * alpha * t ^ 3 + (57283687 / 90000) * alpha * t ^ 5 + (-3638999 / 15000) * alpha * t ^ 7 + (-60665003 / 180000) * alpha * t ^ 9 + (3510533 / 15000) * alpha * t ^ 11 + (610301 / 180000) * alpha * t ^ 17 + (12556 / 75) * alpha * c * t ^ 3 + (-1941127 / 5625) * alpha * c * t ^ 5 + (1159354 / 5625) * alpha * c * t ^ 7 + (-164461 / 5625) * alpha * c * t ^ 9 + (3536 / 16875) * alpha * c * t ^ 11 + (10066 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_01, v22_10, v22_11, v22_20, v22_21, v22_30, v22_31, v22_40, v22_41]
  try simp only [phase22_00, phase22_01, phase22_10, phase22_11, phase22_20, phase22_21, phase22_30, phase22_31, phase22_40, phase22_41]
  try simp only [star_one, star_neg]
  linear_combination ((6278 / 75) * t ^ 3 + (-1636673 / 11250) * t ^ 5 + (50683 / 1125) * t ^ 7 + (163877 / 11250) * t ^ 9 + (41432 / 16875) * t ^ 11 + (-5033 / 16875) * t ^ 17 + (-1048 / 3375) * c * t ^ 5 + (1438 / 5625) * c * t ^ 7 + (242 / 5625) * c * t ^ 9 + (584 / 253125) * c * t ^ 17 + (292 / 16875) * c ^ 2 * t ^ 7 + (-292 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((16 / 225) * t ^ 5 + (-1184 / 5625) * t ^ 7 + (584 / 5625) * t ^ 9 + (8 / 225) * t ^ 11 + (-8789 / 16875) * alpha * t ^ 5 + (7393 / 11250) * alpha * t ^ 7 + (-242 / 5625) * alpha * t ^ 9 + (-1183 / 11250) * alpha * t ^ 11 + (-584 / 253125) * alpha * t ^ 17) * c_sq
theorem v23_42 (t : ℂ) : (momentPoly 23 z23 4 2).eval t = ((-349604 / 15) * t ^ 2 + (39217429 / 500) * t ^ 4 + (-99987800209 / 1200000) * t ^ 6 + (11729097553 / 400000) * t ^ 8 + (-8425162807 / 2400000) * t ^ 10 + (16505147533 / 7200000) * t ^ 12 + (44332603 / 360000) * t ^ 14 + (18626881 / 480000) * t ^ 18 + (-21738229 / 2400000) * t ^ 20 + (-224 / 5) * c * t ^ 4 + (2191369 / 28125) * c * t ^ 6 + (1658917 / 56250) * c * t ^ 8 + (-5382691 / 56250) * c * t ^ 10 + (621623 / 56250) * c * t ^ 12 + (3753767 / 168750) * c * t ^ 14 + (-40264 / 84375) * c * t ^ 18 + (4 / 15) * c * t ^ 20 + (-82928 / 3) * alpha * t ^ 2 + 70227 * alpha * t ^ 4 + (-51605858363 / 900000) * alpha * t ^ 6 + (14942426273 / 900000) * alpha * t ^ 8 + (-7394197529 / 1800000) * alpha * t ^ 10 + (10721136611 / 5400000) * alpha * t ^ 12 + (25931087 / 90000) * alpha * t ^ 14 + (24004871 / 360000) * alpha * t ^ 18 + (-429289769 / 5400000) * alpha * t ^ 20 + (4544 / 45) * alpha * c * t ^ 2 + (18146 / 375) * alpha * c * t ^ 4 + (-98160469 / 225000) * alpha * c * t ^ 6 + (8713613 / 28125) * alpha * c * t ^ 8 + (12182461 / 450000) * alpha * c * t ^ 10 + (-85619129 / 1350000) * alpha * c * t ^ 12 + (10120789 / 675000) * alpha * c * t ^ 14 + (-1496027 / 1350000) * alpha * c * t ^ 18 + (31597 / 270000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_01, v22_02, v22_10, v22_11, v22_12, v22_20, v22_21, v22_22, v22_30, v22_31, v22_32, v22_40, v22_41, v22_42]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_10, phase22_11, phase22_12, phase22_20, phase22_21, phase22_22, phase22_30, phase22_31, phase22_32, phase22_40, phase22_41, phase22_42]
  try simp only [star_one, star_neg]
  linear_combination ((2272 / 45) * t ^ 2 + (-16653 / 125) * t ^ 4 + (62257769 / 450000) * t ^ 6 + (-14974721 / 450000) * t ^ 8 + (-52382957 / 900000) * t ^ 10 + (37633391 / 1350000) * t ^ 12 + (2017091 / 270000) * t ^ 14 + (134819 / 300000) * t ^ 18 + (-152627 / 84375) * c * t ^ 6 + (153427 / 84375) * c * t ^ 8 + (182809 / 84375) * c * t ^ 10 + (-148877 / 84375) * c * t ^ 12 + (-124328 / 253125) * c * t ^ 14 + (31382 / 253125) * c * t ^ 18 + (-2 / 45) * c * t ^ 20 + (-1183 / 84375) * c ^ 2 * t ^ 8 + (4033 / 168750) * c ^ 2 * t ^ 10 + (-242 / 84375) * c ^ 2 * t ^ 12 + (-1183 / 168750) * c ^ 2 * t ^ 14 + (-1168 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((2272 / 45) * t ^ 2 + (-15148 / 125) * t ^ 4 + (43591259 / 450000) * t ^ 6 + (-2170777 / 75000) * t ^ 8 + (4380437 / 900000) * t ^ 10 + (-1524959 / 675000) * t ^ 12 + (20731 / 84375) * t ^ 14 + (16519 / 300000) * t ^ 18 + (1168 / 1265625) * t ^ 20 + (-8176 / 375) * alpha * t ^ 4 + (1228609 / 28125) * alpha * t ^ 6 + (-1968854 / 84375) * alpha * t ^ 8 + (139609 / 84375) * alpha * t ^ 10 + (-616 / 253125) * alpha * t ^ 12 + (-40264 / 253125) * alpha * t ^ 14 + (-10066 / 253125) * alpha * t ^ 18) * c_sq
theorem v23_43 (t : ℂ) : (momentPoly 23 z23 4 3).eval t = ((791904 / 25) * t ^ 3 + (-34014983 / 500) * t ^ 5 + (3240698563 / 150000) * t ^ 7 + (1042993237 / 31250) * t ^ 9 + (-490309621 / 46875) * t ^ 11 + (-2085399733 / 120000) * t ^ 13 + (350962801 / 30000) * t ^ 15 + (-22252136069 / 9000000) * t ^ 17 + (-174215081 / 1687500) * t ^ 19 + (320600639 / 9000000) * t ^ 21 + (1429672199 / 27000000) * t ^ 25 + (-511546 / 15) * c * t + (2606232 / 25) * c * t ^ 3 + (-308639397 / 2500) * c * t ^ 5 + (15660519983 / 200000) * c * t ^ 7 + (-101522147951 / 3000000) * c * t ^ 9 + (59922556307 / 6000000) * c * t ^ 11 + (-29282053169 / 18000000) * c * t ^ 13 + (720313621 / 1500000) * c * t ^ 15 + (10560889 / 4500000) * c * t ^ 17 + (-230958779 / 18000000) * c * t ^ 19 + (185644819 / 18000000) * c * t ^ 21 + (-5500291 / 4500000) * c * t ^ 25 + (-511546 / 15) * alpha * t + (1949928 / 25) * alpha * t ^ 3 + (-426985947 / 10000) * alpha * t ^ 5 + (-48668797241 / 2400000) * alpha * t ^ 7 + (679252387583 / 24000000) * alpha * t ^ 9 + (-29366101503 / 8000000) * alpha * t ^ 11 + (-1795068509947 / 144000000) * alpha * t ^ 13 + (3382054677 / 500000) * alpha * t ^ 15 + (9805815559 / 144000000) * alpha * t ^ 17 + (2924265013 / 72000000) * alpha * t ^ 19 + (2123583211 / 144000000) * alpha * t ^ 21 + (1029108997 / 48000000) * alpha * t ^ 25 + (263968 / 25) * alpha * c * t ^ 3 + (-2182042 / 75) * alpha * c * t ^ 5 + (158440781 / 6000) * alpha * c * t ^ 7 + (-19442484857 / 2250000) * alpha * c * t ^ 9 + (6462571993 / 4500000) * alpha * c * t ^ 11 + (-1177900967 / 2700000) * alpha * c * t ^ 13 + (-43743223 / 225000) * alpha * c * t ^ 15 + (-26782717 / 843750) * alpha * c * t ^ 17 + (-1342478203 / 40500000) * alpha * c * t ^ 19 + (382299817 / 13500000) * alpha * c * t ^ 21 + (758486 / 1265625) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_01, v22_02, v22_03, v22_10, v22_11, v22_12, v22_13, v22_20, v22_21, v22_22, v22_23, v22_30, v22_31, v22_32, v22_33, v22_40, v22_41, v22_42, v22_43]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_10, phase22_11, phase22_12, phase22_13, phase22_20, phase22_21, phase22_22, phase22_23, phase22_30, phase22_31, phase22_32, phase22_33, phase22_40, phase22_41, phase22_42, phase22_43]
  try simp only [star_one, star_neg]
  linear_combination ((-131984 / 25) * t ^ 3 + (1091021 / 75) * t ^ 5 + (-158338381 / 12000) * t ^ 7 + (19400355881 / 4500000) * t ^ 9 + (-9414579049 / 9000000) * t ^ 11 + (23350445587 / 27000000) * t ^ 13 + (-550103833 / 2250000) * t ^ 15 + (36216817 / 843750) * t ^ 17 + (1127915131 / 81000000) * t ^ 19 + (-382261417 / 27000000) * t ^ 21 + (-1112293 / 1265625) * t ^ 25 + (369229 / 11250) * c * t ^ 5 + (-1442251 / 25000) * c * t ^ 7 + (6159059 / 750000) * c * t ^ 9 + (4339919 / 187500) * c * t ^ 11 + (-4482359 / 20250000) * c * t ^ 13 + (-2646737 / 337500) * c * t ^ 15 + (2017091 / 1350000) * c * t ^ 17 + (196741 / 675000) * c * t ^ 19 + (-1434673 / 6750000) * c * t ^ 21 + (4402411 / 75937500) * c * t ^ 25 + (-584 / 135) * c ^ 2 * t ^ 7 + (3671227 / 421875) * c ^ 2 * t ^ 9 + (-218806 / 46875) * c ^ 2 * t ^ 11 + (141961 / 421875) * c ^ 2 * t ^ 13 + (-2956 / 140625) * c ^ 2 * t ^ 15 + (-20132 / 1265625) * c ^ 2 * t ^ 17 + (-21316 / 1265625) * c ^ 2 * t ^ 19 + (2 / 225) * c ^ 2 * t ^ 21) * alpha_sq + ((328 / 75) * t ^ 5 + (1537331 / 56250) * t ^ 7 + (-42838091 / 562500) * t ^ 9 + (27145597 / 562500) * t ^ 11 + (3417901 / 1687500) * t ^ 13 + (-3384311 / 562500) * t ^ 15 + (40864 / 421875) * t ^ 17 + (59782 / 421875) * t ^ 19 + (-4 / 75) * t ^ 21 + (-369229 / 11250) * alpha * t ^ 5 + (15937759 / 225000) * alpha * t ^ 7 + (-94564567 / 2250000) * alpha * t ^ 9 + (577841 / 2250000) * alpha * t ^ 11 + (52940687 / 10125000) * alpha * t ^ 13 + (-10421687 / 6750000) * alpha * t ^ 15 + (-37913 / 843750) * alpha * t ^ 17 + (407503 / 3375000) * alpha * t ^ 19 + (-26797 / 1350000) * alpha * t ^ 21 + (-41464 / 18984375) * alpha * t ^ 25) * c_sq
theorem v23_44 (t : ℂ) : (momentPoly 23 z23 4 4).eval t = (5882779 + (-18163544) * t ^ 2 + (10432354309 / 500) * t ^ 4 + (-1418082949 / 100) * t ^ 6 + (526595406970051 / 48000000) * t ^ 8 + (-17607727648927 / 2400000) * t ^ 10 + (528008047720841 / 240000000) * t ^ 12 + (-50199435409727 / 120000000) * t ^ 14 + (404051011760629 / 2880000000) * t ^ 16 + (15542562037387 / 360000000) * t ^ 18 + (-23995477433719 / 2160000000) * t ^ 20 + (727093366401 / 40000000) * t ^ 22 + (-99914063503 / 11520000) * t ^ 24 + (-154131708763 / 216000000) * t ^ 26 + (877721548943 / 8640000000) * t ^ 32 + (-6043232 / 375) * c * t ^ 4 + (1174432 / 125) * c * t ^ 6 + (20179263853 / 281250) * c * t ^ 8 + (-68516772 / 625) * c * t ^ 10 + (112094147147 / 2812500) * c * t ^ 12 + (120236034841 / 8437500) * c * t ^ 14 + (-101640595253 / 8437500) * c * t ^ 16 + (20369248993 / 8437500) * c * t ^ 18 + (5687043317 / 25312500) * c * t ^ 20 + (-425467949 / 8437500) * c * t ^ 22 + (4113 / 62500) * c * t ^ 24 + (-27532931 / 562500) * c * t ^ 26 + (-5878544 / 6328125) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z23, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v22_00, v22_01, v22_02, v22_03, v22_04, v22_10, v22_11, v22_12, v22_13, v22_14, v22_20, v22_21, v22_22, v22_23, v22_24, v22_30, v22_31, v22_32, v22_33, v22_34, v22_40, v22_41, v22_42, v22_43, v22_44]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04, phase22_10, phase22_11, phase22_12, phase22_13, phase22_14, phase22_20, phase22_21, phase22_22, phase22_23, phase22_24, phase22_30, phase22_31, phase22_32, phase22_33, phase22_34, phase22_40, phase22_41, phase22_42, phase22_43, phase22_44]
  try simp only [star_one, star_neg]
  linear_combination ((-1911952 / 225) * t ^ 2 + (7440212 / 375) * t ^ 4 + (-869034 / 125) * t ^ 6 + (-82757129383 / 4500000) * t ^ 8 + (186973156903 / 9000000) * t ^ 10 + (-37875239227 / 9000000) * t ^ 12 + (-1307145986159 / 270000000) * t ^ 14 + (39907289663 / 16875000) * t ^ 16 + (-404817434251 / 810000000) * t ^ 18 + (51652879343 / 135000000) * t ^ 20 + (2974664807 / 270000000) * t ^ 22 + (796078979 / 54000000) * t ^ 26 + (3021616 / 1125) * c * t ^ 4 + (-355072 / 75) * c * t ^ 6 + (-1291289857 / 1687500) * c * t ^ 8 + (443966921 / 93750) * c * t ^ 10 + (-31046751337 / 16875000) * c * t ^ 12 + (382456633 / 6328125) * c * t ^ 14 + (-4191246247 / 50625000) * c * t ^ 16 + (-744782977 / 12656250) * c * t ^ 18 + (-2314529627 / 151875000) * c * t ^ 20 + (88963768 / 6328125) * c * t ^ 22 + (-1371 / 125000) * c * t ^ 24 + (4672 / 253125) * c * t ^ 26 + (2939272 / 18984375) * c * t ^ 32 + (-3053512 / 253125) * c ^ 2 * t ^ 8 + (11668669 / 421875) * c ^ 2 * t ^ 10 + (-36637373 / 2109375) * c ^ 2 * t ^ 12 + (-3560573 / 4218750) * c ^ 2 * t ^ 14 + (27299719 / 8437500) * c ^ 2 * t ^ 16 + (-2830259 / 4218750) * c ^ 2 * t ^ 18 + (-345436 / 6328125) * c ^ 2 * t ^ 20 + (925657 / 6328125) * c ^ 2 * t ^ 22 + (-416641 / 25312500) * c ^ 2 * t ^ 24 + (-172718 / 6328125) * c ^ 2 * t ^ 26 + (-170528 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((1911952 / 225) * t ^ 2 + (-9944428 / 375) * t ^ 4 + (3930058 / 125) * t ^ 6 + (-25820327819 / 1350000) * t ^ 8 + (17337334007 / 2250000) * t ^ 10 + (-52246879379 / 22500000) * t ^ 12 + (32873055733 / 67500000) * t ^ 14 + (-2656283221 / 16875000) * t ^ 16 + (-38310151 / 25312500) * t ^ 18 + (-6729233 / 13500000) * t ^ 20 + (-99575069 / 22500000) * t ^ 22 + (416641 / 8437500) * t ^ 24 + (4900291 / 8437500) * t ^ 26 + (170528 / 94921875) * t ^ 32) * c_sq
#print axioms v23_00
#print axioms v23_11
#print axioms v23_22
#print axioms v23_33
#print axioms v23_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
noncomputable def z24 : Fin 24 → ℂ := Fin.snoc z23 (r ^ 2 * thetaPlus)
theorem v24_00 (t : ℂ) : (momentPoly 24 z24 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00]
  try simp only [phase22_00]
  try simp only [star_one, star_neg]
  ring
theorem v24_01 (t : ℂ) : (momentPoly 24 z24 0 1).eval t = ((-1 / 5) * c * t + (1 / 5) * alpha * t) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_01]
  try simp only [phase22_00, phase22_01]
  try simp only [star_one, star_neg]
  ring
theorem v24_02 (t : ℂ) : (momentPoly 24 z24 0 2).eval t = ((-21 / 100) * t ^ 2 + (897 / 100) * t ^ 4 + (73 / 15) * alpha * t ^ 2 + (-73 / 15) * alpha * t ^ 4 + (-4 / 75) * alpha * c * t ^ 2 + (-2 / 75) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_01, v23_02]
  try simp only [phase22_00, phase22_01, phase22_02]
  try simp only [star_one, star_neg]
  linear_combination ((4 / 225) * t ^ 2) * alpha_sq + ((4 / 225) * t ^ 2) * c_sq
theorem v24_03 (t : ℂ) : (momentPoly 24 z24 0 3).eval t = ((-169 / 25) * t ^ 3 + (144 / 25) * t ^ 5 + 1 * t ^ 9 + (4877 / 1500) * c * t ^ 3 + (-2383 / 500) * c * t ^ 5 + (-71 / 375) * c * t ^ 9 + (10391 / 3000) * alpha * t ^ 3 + (-3413 / 2000) * alpha * t ^ 5 + (21281 / 6000) * alpha * t ^ 9 + (-73 / 25) * alpha * c * t ^ 3 + (73 / 25) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_01, v23_02, v23_03]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-4 / 1125) * c * t ^ 3 + (-8 / 1125) * c * t ^ 5) * alpha_sq + ((4 / 1125) * alpha * t ^ 3 + (8 / 1125) * alpha * t ^ 5) * c_sq
theorem v24_04 (t : ℂ) : (momentPoly 24 z24 0 4).eval t = ((-1466833 / 4000) * t ^ 4 + (4405417 / 10000) * t ^ 6 + (6609 / 40000) * t ^ 8 + (-312071 / 30000) * t ^ 10 + (1065467 / 120000) * t ^ 16 + (384 / 125) * c * t ^ 4 + (8 / 125) * c * t ^ 6 + (-292 / 125) * c * t ^ 8 + (-4 / 5) * c * t ^ 10 + (-23531 / 750) * alpha * t ^ 4 + (119753 / 375) * alpha * t ^ 6 + (-206509 / 750) * alpha * t ^ 8 + (-19232 / 1125) * alpha * t ^ 10 + (5033 / 1125) * alpha * t ^ 16 + (-699 / 250) * alpha * c * t ^ 4 + (41303 / 7500) * alpha * c * t ^ 6 + (-2399 / 1875) * alpha * c * t ^ 8 + (-62579 / 22500) * alpha * c * t ^ 10 + (-292 / 5625) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_01, v23_02, v23_03, v23_04]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04]
  try simp only [star_one, star_neg]
  linear_combination ((233 / 250) * t ^ 4 + (-31643 / 22500) * t ^ 6 + (67379 / 67500) * t ^ 10 + (-584 / 1125) * c * t ^ 4 + (292 / 1125) * c * t ^ 6 + (292 / 1125) * c * t ^ 8 + (16 / 16875) * c ^ 2 * t ^ 6 + (16 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-242 / 375) * t ^ 4 + (1394 / 1875) * t ^ 6 + (-16 / 5625) * t ^ 8 + (1136 / 16875) * t ^ 10 + (584 / 1125) * alpha * t ^ 4 + (-584 / 1125) * alpha * t ^ 6) * c_sq
theorem v24_10 (t : ℂ) : (momentPoly 24 z24 1 0).eval t = ((-1 / 5) * c * t + (-1 / 5) * alpha * t) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_10]
  try simp only [phase22_00, phase22_10]
  try simp only [star_one, star_neg]
  ring
theorem v24_11 (t : ℂ) : (momentPoly 24 z24 1 1).eval t = (24 + (-15) * t ^ 2) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_01, v23_10, v23_11]
  try simp only [phase22_00, phase22_01, phase22_10, phase22_11]
  try simp only [star_one, star_neg]
  linear_combination ((-4 / 225) * t ^ 2) * alpha_sq + ((4 / 225) * t ^ 2) * c_sq
theorem v24_12 (t : ℂ) : (momentPoly 24 z24 1 2).eval t = ((73 / 25) * t ^ 3 + (-73 / 25) * t ^ 5 + (-47 / 5) * c * t + (921 / 100) * c * t ^ 3 + (-161 / 100) * c * t ^ 5 + (47 / 5) * alpha * t + (-679 / 100) * alpha * t ^ 3 + (-81 / 100) * alpha * t ^ 5 + (-73 / 75) * alpha * c * t ^ 3 + (73 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_01, v23_02, v23_10, v23_11, v23_12]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_10, phase22_11, phase22_12]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 225) * t ^ 3 + (73 / 225) * t ^ 5 + (4 / 3375) * c * t ^ 3 + (8 / 3375) * c * t ^ 5) * alpha_sq + ((4 / 3375) * alpha * t ^ 3 + (8 / 3375) * alpha * t ^ 5) * c_sq
theorem v24_13 (t : ℂ) : (momentPoly 24 z24 1 3).eval t = ((-1449 / 100) * t ^ 2 + (499479 / 1000) * t ^ 4 + (-815427 / 2000) * t ^ 6 + (3129 / 2000) * t ^ 10 + (-2 / 5) * c * t ^ 4 + (3 / 5) * c * t ^ 6 + (-1 / 5) * c * t ^ 10 + (1679 / 5) * alpha * t ^ 2 + (-7963 / 15) * alpha * t ^ 4 + (952 / 5) * alpha * t ^ 6 + (14 / 3) * alpha * t ^ 10 + (-92 / 25) * alpha * c * t ^ 2 + (931 / 3000) * alpha * c * t ^ 4 + (6589 / 2000) * alpha * c * t ^ 6 + (-3869 / 6000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_01, v23_02, v23_03, v23_10, v23_11, v23_12, v23_13]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_10, phase22_11, phase22_12, phase22_13]
  try simp only [star_one, star_neg]
  linear_combination ((92 / 75) * t ^ 2 + (-143 / 120) * t ^ 4 + (19523 / 90000) * t ^ 6 + (-67379 / 270000) * t ^ 10) * alpha_sq + ((92 / 75) * t ^ 2 + (-541 / 375) * t ^ 4 + (2107 / 5625) * t ^ 6 + (284 / 16875) * t ^ 10 + (292 / 1125) * alpha * t ^ 4 + (-292 / 1125) * alpha * t ^ 6) * c_sq
theorem v24_14 (t : ℂ) : (momentPoly 24 z24 1 4).eval t = ((-3042 / 5) * t ^ 3 + (1173373 / 1250) * t ^ 5 + (-173473 / 625) * t ^ 7 + (24989 / 1250) * t ^ 9 + (-139532 / 1875) * t ^ 11 + (3158 / 1875) * t ^ 17 + (14631 / 50) * c * t ^ 3 + (-38204557 / 60000) * c * t ^ 5 + (3150959 / 10000) * c * t ^ 7 + (-355069 / 40000) * c * t ^ 9 + (725551 / 30000) * c * t ^ 11 + (-194111 / 120000) * c * t ^ 17 + (31173 / 100) * alpha * t ^ 3 + (-14959457 / 60000) * alpha * t ^ 5 + (-2032321 / 10000) * alpha * t ^ 7 + (15601751 / 40000) * alpha * t ^ 9 + (-5953909 / 30000) * alpha * t ^ 11 + (-362131 / 120000) * alpha * t ^ 17 + (-1314 / 5) * alpha * c * t ^ 3 + (1941127 / 3750) * alpha * c * t ^ 5 + (-568727 / 1875) * alpha * c * t ^ 7 + (186361 / 3750) * alpha * c * t ^ 9 + (-1768 / 5625) * alpha * c * t ^ 11 + (-5033 / 5625) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_01, v23_02, v23_03, v23_04, v23_10, v23_11, v23_12, v23_13, v23_14]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04, phase22_10, phase22_11, phase22_12, phase22_13, phase22_14]
  try simp only [star_one, star_neg]
  linear_combination ((438 / 5) * t ^ 3 + (-109087 / 750) * t ^ 5 + (220873 / 5625) * t ^ 7 + (20577 / 1250) * t ^ 9 + (40832 / 16875) * t ^ 11 + (-5033 / 16875) * t ^ 17 + (-8 / 25) * c * t ^ 3 + (-6646 / 16875) * c * t ^ 5 + (3118 / 5625) * c * t ^ 7 + (7244 / 84375) * c * t ^ 9 + (1136 / 253125) * c * t ^ 11 + (1168 / 253125) * c * t ^ 17 + (584 / 16875) * c ^ 2 * t ^ 7 + (-584 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((24 / 625) * t ^ 5 + (-1784 / 5625) * t ^ 7 + (1168 / 5625) * t ^ 9 + (16 / 225) * t ^ 11 + (8 / 25) * alpha * t ^ 3 + (12292 / 16875) * alpha * t ^ 5 + (-7151 / 5625) * alpha * t ^ 7 + (8444 / 84375) * alpha * t ^ 9 + (56771 / 253125) * alpha * t ^ 11 + (1168 / 253125) * alpha * t ^ 17) * c_sq
theorem v24_20 (t : ℂ) : (momentPoly 24 z24 2 0).eval t = ((-21 / 100) * t ^ 2 + (897 / 100) * t ^ 4 + (-73 / 15) * alpha * t ^ 2 + (73 / 15) * alpha * t ^ 4 + (4 / 75) * alpha * c * t ^ 2 + (2 / 75) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_10, v23_20]
  try simp only [phase22_00, phase22_10, phase22_20]
  try simp only [star_one, star_neg]
  linear_combination ((4 / 225) * t ^ 2) * alpha_sq + ((4 / 225) * t ^ 2) * c_sq
theorem v24_21 (t : ℂ) : (momentPoly 24 z24 2 1).eval t = ((73 / 25) * t ^ 3 + (-73 / 25) * t ^ 5 + (-47 / 5) * c * t + (921 / 100) * c * t ^ 3 + (-161 / 100) * c * t ^ 5 + (-47 / 5) * alpha * t + (679 / 100) * alpha * t ^ 3 + (81 / 100) * alpha * t ^ 5 + (73 / 75) * alpha * c * t ^ 3 + (-73 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_01, v23_10, v23_11, v23_20, v23_21]
  try simp only [phase22_00, phase22_01, phase22_10, phase22_11, phase22_20, phase22_21]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 225) * t ^ 3 + (73 / 225) * t ^ 5 + (4 / 3375) * c * t ^ 3 + (8 / 3375) * c * t ^ 5) * alpha_sq + ((-4 / 3375) * alpha * t ^ 3 + (-8 / 3375) * alpha * t ^ 5) * c_sq
theorem v24_22 (t : ℂ) : (momentPoly 24 z24 2 2).eval t = (1128 + (-1380) * t ^ 2 + (1733951 / 6000) * t ^ 4 + (-251939 / 3000) * t ^ 6 + (767927 / 6000) * t ^ 8 + (-584 / 375) * c * t ^ 4 + (292 / 375) * c * t ^ 6 + (292 / 375) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_01, v23_02, v23_10, v23_11, v23_12, v23_20, v23_21, v23_22]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_10, phase22_11, phase22_12, phase22_20, phase22_21, phase22_22]
  try simp only [star_one, star_neg]
  linear_combination ((-368 / 225) * t ^ 2 + (1438 / 1125) * t ^ 4 + (202 / 1125) * t ^ 6 + (584 / 3375) * c * t ^ 4 + (-292 / 3375) * c * t ^ 6 + (-292 / 3375) * c * t ^ 8 + (-16 / 50625) * c ^ 2 * t ^ 6 + (-16 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((368 / 225) * t ^ 2 + (-1922 / 1125) * t ^ 4 + (4246 / 16875) * t ^ 6 + (16 / 16875) * t ^ 8) * c_sq
theorem v24_23 (t : ℂ) : (momentPoly 24 z24 2 3).eval t = ((1971 / 5) * t ^ 3 + (-9183787 / 15000) * t ^ 5 + (5099087 / 30000) * t ^ 7 + (334829 / 10000) * t ^ 9 + (1722413 / 30000) * t ^ 11 + (-1284413 / 30000) * t ^ 13 + (-3244 / 5) * c * t + (24867 / 20) * c * t ^ 3 + (-24530969 / 30000) * c * t ^ 5 + (4089829 / 15000) * c * t ^ 7 + (-133233 / 2000) * c * t ^ 9 + (5048 / 1875) * c * t ^ 11 + (-26731 / 15000) * c * t ^ 13 + (3244 / 5) * alpha * t + (-18333 / 20) * alpha * t ^ 3 + (499289 / 2400) * alpha * t ^ 5 + (8849429 / 120000) * alpha * t ^ 7 + (-1074401 / 40000) * alpha * t ^ 9 + (-149597 / 24000) * alpha * t ^ 11 + (4243309 / 120000) * alpha * t ^ 13 + (-657 / 5) * alpha * c * t ^ 3 + (1352341 / 5625) * alpha * c * t ^ 5 + (-604018 / 5625) * alpha * c * t ^ 7 + (434 / 1875) * alpha * c * t ^ 9 + (-5467 / 5625) * alpha * c * t ^ 11 + (-5033 / 5625) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_01, v23_02, v23_03, v23_10, v23_11, v23_12, v23_13, v23_20, v23_21, v23_22, v23_23]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_10, phase22_11, phase22_12, phase22_13, phase22_20, phase22_21, phase22_22, phase22_23]
  try simp only [star_one, star_neg]
  linear_combination ((-219 / 5) * t ^ 3 + (3491 / 45) * t ^ 5 + (-2486 / 75) * t ^ 7 + (-26783 / 16875) * t ^ 11 + (16133 / 16875) * t ^ 13 + (4 / 25) * c * t ^ 3 + (9469 / 33750) * c * t ^ 5 + (-4543 / 11250) * c * t ^ 7 + (-43763 / 675000) * c * t ^ 9 + (59171 / 1012500) * c * t ^ 11 + (67379 / 2025000) * c * t ^ 13 + (-584 / 16875) * c ^ 2 * t ^ 7 + (584 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((784 / 5625) * t ^ 5 + (284 / 5625) * t ^ 7 + (-1168 / 5625) * t ^ 9 + (4 / 225) * t ^ 11 + (4 / 25) * alpha * t ^ 3 + (9469 / 33750) * alpha * t ^ 5 + (-1141 / 2500) * alpha * t ^ 7 + (16 / 84375) * alpha * t ^ 9 + (54499 / 1012500) * alpha * t ^ 11 + (-568 / 253125) * alpha * t ^ 13) * c_sq
theorem v24_24 (t : ℂ) : (momentPoly 24 z24 2 4).eval t = ((-65247 / 50) * t ^ 2 + (17380527 / 500) * t ^ 4 + (-61697951377 / 1200000) * t ^ 6 + (7115302717 / 400000) * t ^ 8 + (-2898558791 / 2400000) * t ^ 10 + (13098085337 / 7200000) * t ^ 12 + (360462751 / 1800000) * t ^ 14 + (447605791 / 7200000) * t ^ 18 + (45204797 / 7200000) * t ^ 20 + (-352 / 5) * c * t ^ 4 + (2526623 / 18750) * c * t ^ 6 + (43369 / 7500) * c * t ^ 8 + (-301777 / 2500) * c * t ^ 10 + (195629 / 12500) * c * t ^ 12 + (1334941 / 37500) * c * t ^ 14 + (-10066 / 9375) * c * t ^ 18 + (2 / 5) * c * t ^ 20 + (453622 / 15) * alpha * t ^ 2 + (-968963 / 15) * alpha * t ^ 4 + (3929694131 / 100000) * alpha * t ^ 6 + (-1866409459 / 300000) * alpha * t ^ 8 + (738546753 / 200000) * alpha * t ^ 10 + (-3960233713 / 1800000) * alpha * t ^ 12 + (-111076799 / 450000) * alpha * t ^ 14 + (-96270179 / 1800000) * alpha * t ^ 18 + (158772707 / 1800000) * alpha * t ^ 20 + (-24856 / 75) * alpha * c * t ^ 2 + (79732 / 375) * alpha * c * t ^ 4 + (1568926 / 3125) * alpha * c * t ^ 6 + (-396109 / 1000) * alpha * c * t ^ 8 + (-15813 / 250) * alpha * c * t ^ 10 + (84936301 / 900000) * alpha * c * t ^ 12 + (-11846801 / 450000) * alpha * c * t ^ 14 + (798349 / 450000) * alpha * c * t ^ 18 + (-36397 / 180000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_01, v23_02, v23_03, v23_04, v23_10, v23_11, v23_12, v23_13, v23_14, v23_20, v23_21, v23_22, v23_23, v23_24]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04, phase22_10, phase22_11, phase22_12, phase22_13, phase22_14, phase22_20, phase22_21, phase22_22, phase22_23, phase22_24]
  try simp only [star_one, star_neg]
  linear_combination ((24856 / 225) * t ^ 2 + (-3146 / 15) * t ^ 4 + (40750889 / 337500) * t ^ 6 + (37319 / 30000) * t ^ 8 + (-2123261 / 33750) * t ^ 10 + (40815433 / 1350000) * t ^ 12 + (792269 / 90000) * t ^ 14 + (610301 / 1350000) * t ^ 18 + (-304454 / 84375) * c * t ^ 6 + (542377 / 84375) * c * t ^ 8 + (-23732 / 84375) * c * t ^ 10 + (-154793 / 84375) * c * t ^ 12 + (-69464 / 84375) * c * t ^ 14 + (13816 / 84375) * c * t ^ 18 + (-2 / 45) * c * t ^ 20 + (-1882 / 84375) * c ^ 2 * t ^ 8 + (1183 / 28125) * c ^ 2 * t ^ 10 + (-8428 / 1265625) * c ^ 2 * t ^ 12 + (-57907 / 3796875) * c ^ 2 * t ^ 14 + (-1168 / 3796875) * c ^ 2 * t ^ 18 + (-2336 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((24856 / 225) * t ^ 2 + (-95216 / 375) * t ^ 4 + (138833441 / 675000) * t ^ 6 + (-7723511 / 112500) * t ^ 8 + (15913439 / 1350000) * t ^ 10 + (-2516381 / 562500) * t ^ 12 + (714202 / 1265625) * t ^ 14 + (2589553 / 20250000) * t ^ 18 + (2336 / 1265625) * t ^ 20 + (51392 / 1125) * alpha * t ^ 4 + (-7547654 / 84375) * alpha * t ^ 6 + (147724 / 3125) * alpha * t ^ 8 + (-328858 / 84375) * alpha * t ^ 10 + (32 / 253125) * alpha * t ^ 12 + (80528 / 253125) * alpha * t ^ 14 + (20132 / 253125) * alpha * t ^ 18) * c_sq
theorem v24_30 (t : ℂ) : (momentPoly 24 z24 3 0).eval t = ((-169 / 25) * t ^ 3 + (144 / 25) * t ^ 5 + 1 * t ^ 9 + (4877 / 1500) * c * t ^ 3 + (-2383 / 500) * c * t ^ 5 + (-71 / 375) * c * t ^ 9 + (-10391 / 3000) * alpha * t ^ 3 + (3413 / 2000) * alpha * t ^ 5 + (-21281 / 6000) * alpha * t ^ 9 + (73 / 25) * alpha * c * t ^ 3 + (-73 / 25) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_10, v23_20, v23_30]
  try simp only [phase22_00, phase22_10, phase22_20, phase22_30]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-4 / 1125) * c * t ^ 3 + (-8 / 1125) * c * t ^ 5) * alpha_sq + ((-4 / 1125) * alpha * t ^ 3 + (-8 / 1125) * alpha * t ^ 5) * c_sq
theorem v24_31 (t : ℂ) : (momentPoly 24 z24 3 1).eval t = ((-1449 / 100) * t ^ 2 + (499479 / 1000) * t ^ 4 + (-815427 / 2000) * t ^ 6 + (3129 / 2000) * t ^ 10 + (-2 / 5) * c * t ^ 4 + (3 / 5) * c * t ^ 6 + (-1 / 5) * c * t ^ 10 + (-1679 / 5) * alpha * t ^ 2 + (7963 / 15) * alpha * t ^ 4 + (-952 / 5) * alpha * t ^ 6 + (-14 / 3) * alpha * t ^ 10 + (92 / 25) * alpha * c * t ^ 2 + (-931 / 3000) * alpha * c * t ^ 4 + (-6589 / 2000) * alpha * c * t ^ 6 + (3869 / 6000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_01, v23_10, v23_11, v23_20, v23_21, v23_30, v23_31]
  try simp only [phase22_00, phase22_01, phase22_10, phase22_11, phase22_20, phase22_21, phase22_30, phase22_31]
  try simp only [star_one, star_neg]
  linear_combination ((92 / 75) * t ^ 2 + (-143 / 120) * t ^ 4 + (19523 / 90000) * t ^ 6 + (-67379 / 270000) * t ^ 10) * alpha_sq + ((92 / 75) * t ^ 2 + (-541 / 375) * t ^ 4 + (2107 / 5625) * t ^ 6 + (284 / 16875) * t ^ 10 + (-292 / 1125) * alpha * t ^ 4 + (292 / 1125) * alpha * t ^ 6) * c_sq
theorem v24_32 (t : ℂ) : (momentPoly 24 z24 3 2).eval t = ((1971 / 5) * t ^ 3 + (-9183787 / 15000) * t ^ 5 + (5099087 / 30000) * t ^ 7 + (334829 / 10000) * t ^ 9 + (1722413 / 30000) * t ^ 11 + (-1284413 / 30000) * t ^ 13 + (-3244 / 5) * c * t + (24867 / 20) * c * t ^ 3 + (-24530969 / 30000) * c * t ^ 5 + (4089829 / 15000) * c * t ^ 7 + (-133233 / 2000) * c * t ^ 9 + (5048 / 1875) * c * t ^ 11 + (-26731 / 15000) * c * t ^ 13 + (-3244 / 5) * alpha * t + (18333 / 20) * alpha * t ^ 3 + (-499289 / 2400) * alpha * t ^ 5 + (-8849429 / 120000) * alpha * t ^ 7 + (1074401 / 40000) * alpha * t ^ 9 + (149597 / 24000) * alpha * t ^ 11 + (-4243309 / 120000) * alpha * t ^ 13 + (657 / 5) * alpha * c * t ^ 3 + (-1352341 / 5625) * alpha * c * t ^ 5 + (604018 / 5625) * alpha * c * t ^ 7 + (-434 / 1875) * alpha * c * t ^ 9 + (5467 / 5625) * alpha * c * t ^ 11 + (5033 / 5625) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_01, v23_02, v23_10, v23_11, v23_12, v23_20, v23_21, v23_22, v23_30, v23_31, v23_32]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_10, phase22_11, phase22_12, phase22_20, phase22_21, phase22_22, phase22_30, phase22_31, phase22_32]
  try simp only [star_one, star_neg]
  linear_combination ((-219 / 5) * t ^ 3 + (3491 / 45) * t ^ 5 + (-2486 / 75) * t ^ 7 + (-26783 / 16875) * t ^ 11 + (16133 / 16875) * t ^ 13 + (4 / 25) * c * t ^ 3 + (9469 / 33750) * c * t ^ 5 + (-4543 / 11250) * c * t ^ 7 + (-43763 / 675000) * c * t ^ 9 + (59171 / 1012500) * c * t ^ 11 + (67379 / 2025000) * c * t ^ 13 + (-584 / 16875) * c ^ 2 * t ^ 7 + (584 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((784 / 5625) * t ^ 5 + (284 / 5625) * t ^ 7 + (-1168 / 5625) * t ^ 9 + (4 / 225) * t ^ 11 + (-4 / 25) * alpha * t ^ 3 + (-9469 / 33750) * alpha * t ^ 5 + (1141 / 2500) * alpha * t ^ 7 + (-16 / 84375) * alpha * t ^ 9 + (-54499 / 1012500) * alpha * t ^ 11 + (568 / 253125) * alpha * t ^ 13) * c_sq
theorem v24_33 (t : ℂ) : (momentPoly 24 z24 3 3).eval t = (77856 + (-139815) * t ^ 2 + (57220383 / 1000) * t ^ 4 + (-1783074529 / 200000) * t ^ 6 + (6061831609 / 200000) * t ^ 8 + (-12548481393 / 800000) * t ^ 10 + (7761841 / 200000) * t ^ 12 + (-120829601 / 400000) * t ^ 14 + (18158511 / 800000) * t ^ 18 + (-38544 / 125) * c * t ^ 4 + (2491429 / 7500) * c * t ^ 6 + (46437 / 200) * c * t ^ 8 + (-1229931 / 5000) * c * t ^ 10 + (-831211 / 15000) * c * t ^ 12 + (228777 / 5000) * c * t ^ 14 + (-142 / 375) * c * t ^ 18) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_01, v23_02, v23_03, v23_10, v23_11, v23_12, v23_13, v23_20, v23_21, v23_22, v23_23, v23_30, v23_31, v23_32, v23_33]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_10, phase22_11, phase22_12, phase22_13, phase22_20, phase22_21, phase22_22, phase22_23, phase22_30, phase22_31, phase22_32, phase22_33]
  try simp only [star_one, star_neg]
  linear_combination ((-12428 / 75) * t ^ 2 + (31636 / 125) * t ^ 4 + (-7756267 / 150000) * t ^ 6 + (-15115781 / 300000) * t ^ 8 + (5541259 / 300000) * t ^ 10 + (5159899 / 900000) * t ^ 12 + (-139574033 / 13500000) * t ^ 14 + (-13327847 / 10125000) * t ^ 18 + (12848 / 375) * c * t ^ 4 + (-52868 / 1125) * c * t ^ 6 + (-3948 / 3125) * c * t ^ 8 + (372332 / 28125) * c * t ^ 10 + (232 / 225) * c * t ^ 12 + (-308 / 1125) * c * t ^ 14 + (-1072 / 16875) * c ^ 2 * t ^ 6 + (-3949 / 84375) * c ^ 2 * t ^ 8 + (2303 / 18750) * c ^ 2 * t ^ 10 + (-3709 / 168750) * c ^ 2 * t ^ 14) * alpha_sq + ((12428 / 75) * t ^ 2 + (-42284 / 125) * t ^ 4 + (25387841 / 112500) * t ^ 6 + (-1865276 / 28125) * t ^ 8 + (569683 / 37500) * t ^ 10 + (-13423 / 11250) * t ^ 12 + (354829 / 421875) * t ^ 14 + (20164 / 1265625) * t ^ 18) * c_sq
theorem v24_34 (t : ℂ) : (momentPoly 24 z24 3 4).eval t = ((1302174 / 25) * t ^ 3 + (-270970741 / 2500) * t ^ 5 + (87860695361 / 1500000) * t ^ 7 + (-6809511329 / 1500000) * t ^ 9 + (43104092929 / 3000000) * t ^ 11 + (-85342973017 / 4500000) * t ^ 13 + (902765941 / 93750) * t ^ 15 + (-8441820127 / 3000000) * t ^ 17 + (-650207129 / 9000000) * t ^ 19 + (24182863 / 375000) * t ^ 21 + (508339117 / 9000000) * t ^ 25 + (-292239 / 5) * c * t + (8214399 / 50) * c * t ^ 3 + (-918166817 / 5000) * c * t ^ 5 + (710180493803 / 6000000) * c * t ^ 7 + (-333086019569 / 6000000) * c * t ^ 9 + (199476488321 / 12000000) * c * t ^ 11 + (-10265602199 / 4000000) * c * t ^ 13 + (764538429 / 1000000) * c * t ^ 15 + (-18964343 / 3000000) * c * t ^ 17 + (-87339153 / 4000000) * c * t ^ 19 + (17557091 / 2400000) * c * t ^ 21 + (-6100291 / 3000000) * c * t ^ 25 + (292239 / 5) * alpha * t + (-6056001 / 50) * alpha * t ^ 3 + (1078799 / 16) * alpha * t ^ 5 + (-1187448523 / 4000000) * alpha * t ^ 7 + (-41727137807 / 4800000) * alpha * t ^ 9 + (-1163638703 / 8000000) * alpha * t ^ 11 + (1725119354983 / 144000000) * alpha * t ^ 13 + (-21295199959 / 3000000) * alpha * t ^ 15 + (-695337011 / 3200000) * alpha * t ^ 17 + (-7409233099 / 72000000) * alpha * t ^ 19 + (-124916503 / 16000000) * alpha * t ^ 21 + (-3605219039 / 144000000) * alpha * t ^ 25 + (-434058 / 25) * alpha * c * t ^ 3 + (85318301 / 1875) * alpha * c * t ^ 5 + (-58490102587 / 1500000) * alpha * c * t ^ 7 + (54614853299 / 4500000) * alpha * c * t ^ 9 + (-21509294299 / 9000000) * alpha * c * t ^ 11 + (20507560409 / 27000000) * alpha * c * t ^ 13 + (655086517 / 2250000) * alpha * c * t ^ 15 + (29980117 / 562500) * alpha * c * t ^ 17 + (1366487099 / 27000000) * alpha * c * t ^ 19 + (-430048169 / 9000000) * alpha * c * t ^ 21 + (-379243 / 421875) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_01, v23_02, v23_03, v23_04, v23_10, v23_11, v23_12, v23_13, v23_14, v23_20, v23_21, v23_22, v23_23, v23_24, v23_30, v23_31, v23_32, v23_33, v23_34]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04, phase22_10, phase22_11, phase22_12, phase22_13, phase22_14, phase22_20, phase22_21, phase22_22, phase22_23, phase22_24, phase22_30, phase22_31, phase22_32, phase22_33, phase22_34]
  try simp only [star_one, star_neg]
  linear_combination ((-144686 / 25) * t ^ 3 + (1088023 / 75) * t ^ 5 + (-52500818363 / 4500000) * t ^ 7 + (14942426273 / 4500000) * t ^ 9 + (-1080624081 / 1000000) * t ^ 11 + (23760101251 / 27000000) * t ^ 13 + (-1467175567 / 6750000) * t ^ 15 + (1515839 / 31250) * t ^ 17 + (1055212603 / 81000000) * t ^ 19 + (-429289769 / 27000000) * t ^ 21 + (-1112293 / 1265625) * t ^ 25 + (7928 / 375) * c * t ^ 3 + (60269 / 1875) * c * t ^ 5 + (-128751869 / 1125000) * c * t ^ 7 + (87300083 / 1687500) * c * t ^ 9 + (67041097 / 3375000) * c * t ^ 11 + (-98446357 / 20250000) * c * t ^ 13 + (-46770293 / 6750000) * c * t ^ 15 + (182447149 / 101250000) * c * t ^ 17 + (151790761 / 303750000) * c * t ^ 19 + (-1001531 / 6328125) * c * t ^ 21 + (4918667 / 75937500) * c * t ^ 25 + (-153008 / 16875) * c ^ 2 * t ^ 7 + (7518454 / 421875) * c ^ 2 * t ^ 9 + (-3985844 / 421875) * c ^ 2 * t ^ 11 + (330058 / 421875) * c ^ 2 * t ^ 13 + (-17336 / 421875) * c ^ 2 * t ^ 15 + (-40264 / 1265625) * c ^ 2 * t ^ 17 + (-42632 / 1265625) * c ^ 2 * t ^ 19 + (4 / 225) * c ^ 2 * t ^ 21) * alpha_sq + ((67424 / 1875) * t ^ 5 + (487801 / 140625) * t ^ 7 + (-473177 / 3750) * t ^ 9 + (26554889 / 281250) * t ^ 11 + (736633 / 168750) * t ^ 13 + (-10503461 / 843750) * t ^ 15 + (81728 / 421875) * t ^ 17 + (139696 / 421875) * t ^ 19 + (-8 / 75) * t ^ 21 + (7928 / 375) * alpha * t ^ 3 + (60269 / 1875) * alpha * t ^ 5 + (-144249169 / 1125000) * alpha * t ^ 7 + (273223199 / 3375000) * alpha * t ^ 9 + (9892771 / 6750000) * alpha * t ^ 11 + (-27011629 / 2531250) * alpha * t ^ 13 + (12217547 / 3375000) * alpha * t ^ 15 + (655159 / 6328125) * alpha * t ^ 17 + (-78750239 / 303750000) * alpha * t ^ 19 + (2351087 / 50625000) * alpha * t ^ 21 + (82928 / 18984375) * alpha * t ^ 25) * c_sq
theorem v24_40 (t : ℂ) : (momentPoly 24 z24 4 0).eval t = ((-1466833 / 4000) * t ^ 4 + (4405417 / 10000) * t ^ 6 + (6609 / 40000) * t ^ 8 + (-312071 / 30000) * t ^ 10 + (1065467 / 120000) * t ^ 16 + (384 / 125) * c * t ^ 4 + (8 / 125) * c * t ^ 6 + (-292 / 125) * c * t ^ 8 + (-4 / 5) * c * t ^ 10 + (23531 / 750) * alpha * t ^ 4 + (-119753 / 375) * alpha * t ^ 6 + (206509 / 750) * alpha * t ^ 8 + (19232 / 1125) * alpha * t ^ 10 + (-5033 / 1125) * alpha * t ^ 16 + (699 / 250) * alpha * c * t ^ 4 + (-41303 / 7500) * alpha * c * t ^ 6 + (2399 / 1875) * alpha * c * t ^ 8 + (62579 / 22500) * alpha * c * t ^ 10 + (292 / 5625) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_10, v23_20, v23_30, v23_40]
  try simp only [phase22_00, phase22_10, phase22_20, phase22_30, phase22_40]
  try simp only [star_one, star_neg]
  linear_combination ((233 / 250) * t ^ 4 + (-31643 / 22500) * t ^ 6 + (67379 / 67500) * t ^ 10 + (-584 / 1125) * c * t ^ 4 + (292 / 1125) * c * t ^ 6 + (292 / 1125) * c * t ^ 8 + (16 / 16875) * c ^ 2 * t ^ 6 + (16 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-242 / 375) * t ^ 4 + (1394 / 1875) * t ^ 6 + (-16 / 5625) * t ^ 8 + (1136 / 16875) * t ^ 10 + (-584 / 1125) * alpha * t ^ 4 + (584 / 1125) * alpha * t ^ 6) * c_sq
theorem v24_41 (t : ℂ) : (momentPoly 24 z24 4 1).eval t = ((-3042 / 5) * t ^ 3 + (1173373 / 1250) * t ^ 5 + (-173473 / 625) * t ^ 7 + (24989 / 1250) * t ^ 9 + (-139532 / 1875) * t ^ 11 + (3158 / 1875) * t ^ 17 + (14631 / 50) * c * t ^ 3 + (-38204557 / 60000) * c * t ^ 5 + (3150959 / 10000) * c * t ^ 7 + (-355069 / 40000) * c * t ^ 9 + (725551 / 30000) * c * t ^ 11 + (-194111 / 120000) * c * t ^ 17 + (-31173 / 100) * alpha * t ^ 3 + (14959457 / 60000) * alpha * t ^ 5 + (2032321 / 10000) * alpha * t ^ 7 + (-15601751 / 40000) * alpha * t ^ 9 + (5953909 / 30000) * alpha * t ^ 11 + (362131 / 120000) * alpha * t ^ 17 + (1314 / 5) * alpha * c * t ^ 3 + (-1941127 / 3750) * alpha * c * t ^ 5 + (568727 / 1875) * alpha * c * t ^ 7 + (-186361 / 3750) * alpha * c * t ^ 9 + (1768 / 5625) * alpha * c * t ^ 11 + (5033 / 5625) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_01, v23_10, v23_11, v23_20, v23_21, v23_30, v23_31, v23_40, v23_41]
  try simp only [phase22_00, phase22_01, phase22_10, phase22_11, phase22_20, phase22_21, phase22_30, phase22_31, phase22_40, phase22_41]
  try simp only [star_one, star_neg]
  linear_combination ((438 / 5) * t ^ 3 + (-109087 / 750) * t ^ 5 + (220873 / 5625) * t ^ 7 + (20577 / 1250) * t ^ 9 + (40832 / 16875) * t ^ 11 + (-5033 / 16875) * t ^ 17 + (-8 / 25) * c * t ^ 3 + (-6646 / 16875) * c * t ^ 5 + (3118 / 5625) * c * t ^ 7 + (7244 / 84375) * c * t ^ 9 + (1136 / 253125) * c * t ^ 11 + (1168 / 253125) * c * t ^ 17 + (584 / 16875) * c ^ 2 * t ^ 7 + (-584 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((24 / 625) * t ^ 5 + (-1784 / 5625) * t ^ 7 + (1168 / 5625) * t ^ 9 + (16 / 225) * t ^ 11 + (-8 / 25) * alpha * t ^ 3 + (-12292 / 16875) * alpha * t ^ 5 + (7151 / 5625) * alpha * t ^ 7 + (-8444 / 84375) * alpha * t ^ 9 + (-56771 / 253125) * alpha * t ^ 11 + (-1168 / 253125) * alpha * t ^ 17) * c_sq
theorem v24_42 (t : ℂ) : (momentPoly 24 z24 4 2).eval t = ((-65247 / 50) * t ^ 2 + (17380527 / 500) * t ^ 4 + (-61697951377 / 1200000) * t ^ 6 + (7115302717 / 400000) * t ^ 8 + (-2898558791 / 2400000) * t ^ 10 + (13098085337 / 7200000) * t ^ 12 + (360462751 / 1800000) * t ^ 14 + (447605791 / 7200000) * t ^ 18 + (45204797 / 7200000) * t ^ 20 + (-352 / 5) * c * t ^ 4 + (2526623 / 18750) * c * t ^ 6 + (43369 / 7500) * c * t ^ 8 + (-301777 / 2500) * c * t ^ 10 + (195629 / 12500) * c * t ^ 12 + (1334941 / 37500) * c * t ^ 14 + (-10066 / 9375) * c * t ^ 18 + (2 / 5) * c * t ^ 20 + (-453622 / 15) * alpha * t ^ 2 + (968963 / 15) * alpha * t ^ 4 + (-3929694131 / 100000) * alpha * t ^ 6 + (1866409459 / 300000) * alpha * t ^ 8 + (-738546753 / 200000) * alpha * t ^ 10 + (3960233713 / 1800000) * alpha * t ^ 12 + (111076799 / 450000) * alpha * t ^ 14 + (96270179 / 1800000) * alpha * t ^ 18 + (-158772707 / 1800000) * alpha * t ^ 20 + (24856 / 75) * alpha * c * t ^ 2 + (-79732 / 375) * alpha * c * t ^ 4 + (-1568926 / 3125) * alpha * c * t ^ 6 + (396109 / 1000) * alpha * c * t ^ 8 + (15813 / 250) * alpha * c * t ^ 10 + (-84936301 / 900000) * alpha * c * t ^ 12 + (11846801 / 450000) * alpha * c * t ^ 14 + (-798349 / 450000) * alpha * c * t ^ 18 + (36397 / 180000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_01, v23_02, v23_10, v23_11, v23_12, v23_20, v23_21, v23_22, v23_30, v23_31, v23_32, v23_40, v23_41, v23_42]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_10, phase22_11, phase22_12, phase22_20, phase22_21, phase22_22, phase22_30, phase22_31, phase22_32, phase22_40, phase22_41, phase22_42]
  try simp only [star_one, star_neg]
  linear_combination ((24856 / 225) * t ^ 2 + (-3146 / 15) * t ^ 4 + (40750889 / 337500) * t ^ 6 + (37319 / 30000) * t ^ 8 + (-2123261 / 33750) * t ^ 10 + (40815433 / 1350000) * t ^ 12 + (792269 / 90000) * t ^ 14 + (610301 / 1350000) * t ^ 18 + (-304454 / 84375) * c * t ^ 6 + (542377 / 84375) * c * t ^ 8 + (-23732 / 84375) * c * t ^ 10 + (-154793 / 84375) * c * t ^ 12 + (-69464 / 84375) * c * t ^ 14 + (13816 / 84375) * c * t ^ 18 + (-2 / 45) * c * t ^ 20 + (-1882 / 84375) * c ^ 2 * t ^ 8 + (1183 / 28125) * c ^ 2 * t ^ 10 + (-8428 / 1265625) * c ^ 2 * t ^ 12 + (-57907 / 3796875) * c ^ 2 * t ^ 14 + (-1168 / 3796875) * c ^ 2 * t ^ 18 + (-2336 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((24856 / 225) * t ^ 2 + (-95216 / 375) * t ^ 4 + (138833441 / 675000) * t ^ 6 + (-7723511 / 112500) * t ^ 8 + (15913439 / 1350000) * t ^ 10 + (-2516381 / 562500) * t ^ 12 + (714202 / 1265625) * t ^ 14 + (2589553 / 20250000) * t ^ 18 + (2336 / 1265625) * t ^ 20 + (-51392 / 1125) * alpha * t ^ 4 + (7547654 / 84375) * alpha * t ^ 6 + (-147724 / 3125) * alpha * t ^ 8 + (328858 / 84375) * alpha * t ^ 10 + (-32 / 253125) * alpha * t ^ 12 + (-80528 / 253125) * alpha * t ^ 14 + (-20132 / 253125) * alpha * t ^ 18) * c_sq
theorem v24_43 (t : ℂ) : (momentPoly 24 z24 4 3).eval t = ((1302174 / 25) * t ^ 3 + (-270970741 / 2500) * t ^ 5 + (87860695361 / 1500000) * t ^ 7 + (-6809511329 / 1500000) * t ^ 9 + (43104092929 / 3000000) * t ^ 11 + (-85342973017 / 4500000) * t ^ 13 + (902765941 / 93750) * t ^ 15 + (-8441820127 / 3000000) * t ^ 17 + (-650207129 / 9000000) * t ^ 19 + (24182863 / 375000) * t ^ 21 + (508339117 / 9000000) * t ^ 25 + (-292239 / 5) * c * t + (8214399 / 50) * c * t ^ 3 + (-918166817 / 5000) * c * t ^ 5 + (710180493803 / 6000000) * c * t ^ 7 + (-333086019569 / 6000000) * c * t ^ 9 + (199476488321 / 12000000) * c * t ^ 11 + (-10265602199 / 4000000) * c * t ^ 13 + (764538429 / 1000000) * c * t ^ 15 + (-18964343 / 3000000) * c * t ^ 17 + (-87339153 / 4000000) * c * t ^ 19 + (17557091 / 2400000) * c * t ^ 21 + (-6100291 / 3000000) * c * t ^ 25 + (-292239 / 5) * alpha * t + (6056001 / 50) * alpha * t ^ 3 + (-1078799 / 16) * alpha * t ^ 5 + (1187448523 / 4000000) * alpha * t ^ 7 + (41727137807 / 4800000) * alpha * t ^ 9 + (1163638703 / 8000000) * alpha * t ^ 11 + (-1725119354983 / 144000000) * alpha * t ^ 13 + (21295199959 / 3000000) * alpha * t ^ 15 + (695337011 / 3200000) * alpha * t ^ 17 + (7409233099 / 72000000) * alpha * t ^ 19 + (124916503 / 16000000) * alpha * t ^ 21 + (3605219039 / 144000000) * alpha * t ^ 25 + (434058 / 25) * alpha * c * t ^ 3 + (-85318301 / 1875) * alpha * c * t ^ 5 + (58490102587 / 1500000) * alpha * c * t ^ 7 + (-54614853299 / 4500000) * alpha * c * t ^ 9 + (21509294299 / 9000000) * alpha * c * t ^ 11 + (-20507560409 / 27000000) * alpha * c * t ^ 13 + (-655086517 / 2250000) * alpha * c * t ^ 15 + (-29980117 / 562500) * alpha * c * t ^ 17 + (-1366487099 / 27000000) * alpha * c * t ^ 19 + (430048169 / 9000000) * alpha * c * t ^ 21 + (379243 / 421875) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_01, v23_02, v23_03, v23_10, v23_11, v23_12, v23_13, v23_20, v23_21, v23_22, v23_23, v23_30, v23_31, v23_32, v23_33, v23_40, v23_41, v23_42, v23_43]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_10, phase22_11, phase22_12, phase22_13, phase22_20, phase22_21, phase22_22, phase22_23, phase22_30, phase22_31, phase22_32, phase22_33, phase22_40, phase22_41, phase22_42, phase22_43]
  try simp only [star_one, star_neg]
  linear_combination ((-144686 / 25) * t ^ 3 + (1088023 / 75) * t ^ 5 + (-52500818363 / 4500000) * t ^ 7 + (14942426273 / 4500000) * t ^ 9 + (-1080624081 / 1000000) * t ^ 11 + (23760101251 / 27000000) * t ^ 13 + (-1467175567 / 6750000) * t ^ 15 + (1515839 / 31250) * t ^ 17 + (1055212603 / 81000000) * t ^ 19 + (-429289769 / 27000000) * t ^ 21 + (-1112293 / 1265625) * t ^ 25 + (7928 / 375) * c * t ^ 3 + (60269 / 1875) * c * t ^ 5 + (-128751869 / 1125000) * c * t ^ 7 + (87300083 / 1687500) * c * t ^ 9 + (67041097 / 3375000) * c * t ^ 11 + (-98446357 / 20250000) * c * t ^ 13 + (-46770293 / 6750000) * c * t ^ 15 + (182447149 / 101250000) * c * t ^ 17 + (151790761 / 303750000) * c * t ^ 19 + (-1001531 / 6328125) * c * t ^ 21 + (4918667 / 75937500) * c * t ^ 25 + (-153008 / 16875) * c ^ 2 * t ^ 7 + (7518454 / 421875) * c ^ 2 * t ^ 9 + (-3985844 / 421875) * c ^ 2 * t ^ 11 + (330058 / 421875) * c ^ 2 * t ^ 13 + (-17336 / 421875) * c ^ 2 * t ^ 15 + (-40264 / 1265625) * c ^ 2 * t ^ 17 + (-42632 / 1265625) * c ^ 2 * t ^ 19 + (4 / 225) * c ^ 2 * t ^ 21) * alpha_sq + ((67424 / 1875) * t ^ 5 + (487801 / 140625) * t ^ 7 + (-473177 / 3750) * t ^ 9 + (26554889 / 281250) * t ^ 11 + (736633 / 168750) * t ^ 13 + (-10503461 / 843750) * t ^ 15 + (81728 / 421875) * t ^ 17 + (139696 / 421875) * t ^ 19 + (-8 / 75) * t ^ 21 + (-7928 / 375) * alpha * t ^ 3 + (-60269 / 1875) * alpha * t ^ 5 + (144249169 / 1125000) * alpha * t ^ 7 + (-273223199 / 3375000) * alpha * t ^ 9 + (-9892771 / 6750000) * alpha * t ^ 11 + (27011629 / 2531250) * alpha * t ^ 13 + (-12217547 / 3375000) * alpha * t ^ 15 + (-655159 / 6328125) * alpha * t ^ 17 + (78750239 / 303750000) * alpha * t ^ 19 + (-2351087 / 50625000) * alpha * t ^ 21 + (-82928 / 18984375) * alpha * t ^ 25) * c_sq
theorem v24_44 (t : ℂ) : (momentPoly 24 z24 4 4).eval t = (7013736 + (-16432200) * t ^ 2 + (2463944371 / 250) * t ^ 4 + (-859774646 / 3125) * t ^ 6 + (30674632370887 / 9600000) * t ^ 8 + (-277770603617531 / 60000000) * t ^ 10 + (328597510376761 / 240000000) * t ^ 12 + (-75118829980601 / 360000000) * t ^ 14 + (43492099652977 / 576000000) * t ^ 16 + (16967559091631 / 360000000) * t ^ 18 + (-28113683048359 / 2160000000) * t ^ 20 + (6381504576917 / 360000000) * t ^ 22 + (-12723053012339 / 1440000000) * t ^ 24 + (-553902368699 / 1080000000) * t ^ 26 + (1008058975247 / 8640000000) * t ^ 32 + (-6638912 / 125) * c * t ^ 4 + (53994932 / 625) * c * t ^ 6 + (815690431 / 18750) * c * t ^ 8 + (-125918520511 / 937500) * c * t ^ 10 + (14833947703 / 312500) * c * t ^ 12 + (33423551321 / 1406250) * c * t ^ 14 + (-20397421813 / 1125000) * c * t ^ 16 + (23925428681 / 5625000) * c * t ^ 18 + (821926166 / 2109375) * c * t ^ 20 + (-388678859 / 2812500) * c * t ^ 22 + (3321079 / 5625000) * c * t ^ 24 + (-1358598599 / 16875000) * c * t ^ 26 + (-2939272 / 2109375) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z24, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v23_00, v23_01, v23_02, v23_03, v23_04, v23_10, v23_11, v23_12, v23_13, v23_14, v23_20, v23_21, v23_22, v23_23, v23_24, v23_30, v23_31, v23_32, v23_33, v23_34, v23_40, v23_41, v23_42, v23_43, v23_44]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04, phase22_10, phase22_11, phase22_12, phase22_13, phase22_14, phase22_20, phase22_21, phase22_22, phase22_23, phase22_24, phase22_30, phase22_31, phase22_32, phase22_33, phase22_34, phase22_40, phase22_41, phase22_42, phase22_43, phase22_44]
  try simp only [star_one, star_neg]
  linear_combination ((-97376 / 5) * t ^ 2 + (16347184 / 375) * t ^ 4 + (-217411507 / 9375) * t ^ 6 + (-50482690961 / 4500000) * t ^ 8 + (685901898383 / 45000000) * t ^ 10 + (-107043488909 / 45000000) * t ^ 12 + (-4648693975633 / 810000000) * t ^ 14 + (27221616977 / 8437500) * t ^ 16 + (-134623455193 / 270000000) * t ^ 18 + (10515448753 / 27000000) * t ^ 20 + (2123583211 / 270000000) * t ^ 22 + (2715605929 / 162000000) * t ^ 26 + (6638912 / 1125) * c * t ^ 4 + (-14610632 / 1125) * c * t ^ 6 + (1124871779 / 168750) * c * t ^ 8 + (13316165449 / 8437500) * c * t ^ 10 + (-310808314 / 421875) * c * t ^ 12 + (-17041800571 / 50625000) * c * t ^ 14 + (9501769 / 1125000) * c * t ^ 16 + (-1184762137 / 12656250) * c * t ^ 18 + (-1700090891 / 75937500) * c * t ^ 20 + (1114796713 / 50625000) * c * t ^ 22 + (-3321079 / 50625000) * c * t ^ 24 + (12457888 / 18984375) * c * t ^ 26 + (2939272 / 18984375) * c * t ^ 32 + (-187424 / 16875) * c ^ 2 * t ^ 6 + (-1368896 / 253125) * c ^ 2 * t ^ 8 + (99542269 / 2109375) * c ^ 2 * t ^ 10 + (-69708904 / 2109375) * c ^ 2 * t ^ 12 + (-38030983 / 12656250) * c ^ 2 * t ^ 14 + (85619129 / 12656250) * c ^ 2 * t ^ 16 + (-10120789 / 6328125) * c ^ 2 * t ^ 18 + (-549544 / 6328125) * c ^ 2 * t ^ 20 + (3568643 / 12656250) * c ^ 2 * t ^ 22 + (-7291727 / 189843750) * c ^ 2 * t ^ 24 + (-16908844 / 284765625) * c ^ 2 * t ^ 26 + (-341056 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((97376 / 5) * t ^ 2 + (-21849296 / 375) * t ^ 4 + (1903337104 / 28125) * t ^ 6 + (-142684380007 / 3375000) * t ^ 8 + (33808670333 / 1875000) * t ^ 10 + (-60082973843 / 11250000) * t ^ 12 + (4407299723 / 4050000) * t ^ 14 + (-3112167797 / 8437500) * t ^ 16 + (14837203 / 4218750) * t ^ 18 + (-52197109 / 33750000) * t ^ 20 + (-214193963 / 33750000) * t ^ 22 + (7291727 / 63281250) * t ^ 24 + (248839943 / 189843750) * t ^ 26 + (341056 / 94921875) * t ^ 32) * c_sq
#print axioms v24_00
#print axioms v24_11
#print axioms v24_22
#print axioms v24_33
#print axioms v24_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
noncomputable def z25 : Fin 25 → ℂ := Fin.snoc z24 (r ^ 2 * thetaPlus)
theorem v25_00 (t : ℂ) : (momentPoly 25 z25 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00]
  try simp only [phase22_00]
  try simp only [star_one, star_neg]
  ring
theorem v25_01 (t : ℂ) : (momentPoly 25 z25 0 1).eval t = ((-4 / 15) * c * t + (4 / 15) * alpha * t) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_01]
  try simp only [phase22_00, phase22_01]
  try simp only [star_one, star_neg]
  ring
theorem v25_02 (t : ℂ) : (momentPoly 25 z25 0 2).eval t = ((563 / 100) * t ^ 2 + (2983 / 300) * t ^ 4 + (73 / 15) * alpha * t ^ 2 + (-73 / 15) * alpha * t ^ 4 + (-8 / 75) * alpha * c * t ^ 2 + (-8 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_01, v24_02]
  try simp only [phase22_00, phase22_01, phase22_02]
  try simp only [star_one, star_neg]
  linear_combination ((2 / 75) * t ^ 2) * alpha_sq + ((2 / 75) * t ^ 2) * c_sq
theorem v25_03 (t : ℂ) : (momentPoly 25 z25 0 3).eval t = ((-242 / 25) * t ^ 3 + (217 / 25) * t ^ 5 + 1 * t ^ 9 + (1247 / 375) * c * t ^ 3 + (-889 / 125) * c * t ^ 5 + (-284 / 1125) * c * t ^ 9 + (17369 / 3000) * alpha * t ^ 3 + (6079 / 2000) * alpha * t ^ 5 + (67379 / 18000) * alpha * t ^ 9 + (-292 / 75) * alpha * c * t ^ 3 + (292 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_01, v24_02, v24_03]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-4 / 375) * c * t ^ 3 + (-4 / 375) * c * t ^ 5) * alpha_sq + ((4 / 375) * alpha * t ^ 3 + (4 / 375) * alpha * t ^ 5) * c_sq
theorem v25_04 (t : ℂ) : (momentPoly 25 z25 0 4).eval t = ((-33717487 / 60000) * t ^ 4 + (7209333 / 10000) * t ^ 6 + (2064113 / 40000) * t ^ 8 + (261173 / 30000) * t ^ 10 + (3518513 / 360000) * t ^ 16 + (2704 / 375) * c * t ^ 4 + (-1136 / 375) * c * t ^ 6 + (-1168 / 375) * c * t ^ 8 + (-16 / 15) * c * t ^ 10 + (20953 / 150) * alpha * t ^ 4 + (66163 / 375) * alpha * t ^ 6 + (-9113 / 30) * alpha * t ^ 8 + (-18932 / 1125) * alpha * t ^ 10 + (5033 / 1125) * alpha * t ^ 16 + (-16046 / 5625) * alpha * c * t ^ 4 + (8233 / 1875) * alpha * c * t ^ 6 + (-1196 / 625) * alpha * c * t ^ 8 + (-22417 / 5625) * alpha * c * t ^ 10 + (-1168 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_01, v24_02, v24_03, v24_04]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04]
  try simp only [star_one, star_neg]
  linear_combination ((10391 / 11250) * t ^ 4 + (-3413 / 7500) * t ^ 6 + (24817 / 22500) * t ^ 10 + (-292 / 375) * c * t ^ 4 + (584 / 1125) * c * t ^ 6 + (292 / 1125) * c * t ^ 8 + (16 / 5625) * c ^ 2 * t ^ 6 + (8 / 5625) * c ^ 2 * t ^ 8) * alpha_sq + ((-4877 / 5625) * t ^ 4 + (789 / 625) * t ^ 6 + (-8 / 1875) * t ^ 8 + (568 / 5625) * t ^ 10 + (292 / 375) * alpha * t ^ 4 + (-292 / 375) * alpha * t ^ 6) * c_sq
theorem v25_10 (t : ℂ) : (momentPoly 25 z25 1 0).eval t = ((-4 / 15) * c * t + (-4 / 15) * alpha * t) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_10]
  try simp only [phase22_00, phase22_10]
  try simp only [star_one, star_neg]
  ring
theorem v25_11 (t : ℂ) : (momentPoly 25 z25 1 1).eval t = (25 + (-9) * t ^ 2) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_01, v24_10, v24_11]
  try simp only [phase22_00, phase22_01, phase22_10, phase22_11]
  try simp only [star_one, star_neg]
  linear_combination ((-2 / 75) * t ^ 2) * alpha_sq + ((2 / 75) * t ^ 2) * c_sq
theorem v25_12 (t : ℂ) : (momentPoly 25 z25 1 2).eval t = ((292 / 75) * t ^ 3 + (-292 / 75) * t ^ 5 + (-196 / 15) * c * t + (841 / 75) * c * t ^ 3 + (-181 / 75) * c * t ^ 5 + (196 / 15) * alpha * t + (-599 / 75) * alpha * t ^ 3 + (-61 / 75) * alpha * t ^ 5 + (-292 / 225) * alpha * c * t ^ 3 + (292 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_01, v24_02, v24_10, v24_11, v24_12]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_10, phase22_11, phase22_12]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 225) * t ^ 3 + (73 / 225) * t ^ 5 + (4 / 1125) * c * t ^ 3 + (4 / 1125) * c * t ^ 5) * alpha_sq + ((4 / 1125) * alpha * t ^ 3 + (4 / 1125) * alpha * t ^ 5) * c_sq
theorem v25_13 (t : ℂ) : (momentPoly 25 z25 1 3).eval t = ((10134 / 25) * t ^ 2 + (54437 / 375) * t ^ 4 + (-77337 / 250) * t ^ 6 + (1999 / 250) * t ^ 10 + (-8 / 15) * c * t ^ 4 + (4 / 5) * c * t ^ 6 + (-4 / 15) * c * t ^ 10 + (1752 / 5) * alpha * t ^ 2 + (-458) * alpha * t ^ 4 + 103 * alpha * t ^ 6 + (23 / 5) * alpha * t ^ 10 + (-192 / 25) * alpha * c * t ^ 2 + (5251 / 2250) * alpha * c * t ^ 4 + (1983 / 500) * alpha * c * t ^ 6 + (-1343 / 1500) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_01, v24_02, v24_03, v24_10, v24_11, v24_12, v24_13]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_10, phase22_11, phase22_12, phase22_13]
  try simp only [star_one, star_neg]
  linear_combination ((48 / 25) * t ^ 2 + (-71501 / 45000) * t ^ 4 + (-1447 / 30000) * t ^ 6 + (-24817 / 90000) * t ^ 10) * alpha_sq + ((48 / 25) * t ^ 2 + (-23161 / 11250) * t ^ 4 + (2399 / 3750) * t ^ 6 + (142 / 5625) * t ^ 10 + (146 / 375) * alpha * t ^ 4 + (-146 / 375) * alpha * t ^ 6) * c_sq
theorem v25_14 (t : ℂ) : (momentPoly 25 z25 1 4).eval t = ((-22748 / 25) * t ^ 3 + (852632 / 625) * t ^ 5 + (-787492 / 1875) * t ^ 7 + (39403 / 1875) * t ^ 9 + (-325628 / 5625) * t ^ 11 + (14507 / 5625) * t ^ 17 + (117218 / 375) * c * t ^ 3 + (-4115333 / 5000) * c * t ^ 5 + (3342119 / 7500) * c * t ^ 7 + (-2299927 / 90000) * c * t ^ 9 + (70519 / 2500) * c * t ^ 11 + (-72277 / 30000) * c * t ^ 17 + (816343 / 1500) * alpha * t ^ 3 + (742543 / 7500) * alpha * t ^ 5 + (-5749231 / 7500) * alpha * t ^ 7 + (20544449 / 45000) * alpha * t ^ 9 + (-162253 / 1250) * alpha * t ^ 11 + (-33781 / 15000) * alpha * t ^ 17 + (-27448 / 75) * alpha * c * t ^ 3 + (3794654 / 5625) * alpha * c * t ^ 5 + (-2143508 / 5625) * alpha * c * t ^ 7 + (416522 / 5625) * alpha * c * t ^ 9 + (-7072 / 16875) * alpha * c * t ^ 11 + (-20132 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_01, v24_02, v24_03, v24_04, v24_10, v24_11, v24_12, v24_13, v24_14]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04, phase22_10, phase22_11, phase22_12, phase22_13, phase22_14]
  try simp only [star_one, star_neg]
  linear_combination ((6862 / 75) * t ^ 3 + (-530323 / 3750) * t ^ 5 + (165847 / 5625) * t ^ 7 + (206509 / 11250) * t ^ 9 + (40232 / 16875) * t ^ 11 + (-5033 / 16875) * t ^ 17 + (-376 / 375) * c * t ^ 3 + (-1406 / 5625) * c * t ^ 5 + (24568 / 28125) * c * t ^ 7 + (3614 / 28125) * c * t ^ 9 + (1136 / 84375) * c * t ^ 11 + (584 / 84375) * c * t ^ 17 + (292 / 5625) * c ^ 2 * t ^ 7 + (-292 / 5625) * c ^ 2 * t ^ 9) * alpha_sq + ((-184 / 1875) * t ^ 5 + (-8 / 25) * t ^ 7 + (584 / 1875) * t ^ 9 + (8 / 75) * t ^ 11 + (376 / 375) * alpha * t ^ 3 + (3503 / 5625) * alpha * t ^ 5 + (-97699 / 56250) * alpha * t ^ 7 + (4814 / 28125) * alpha * t ^ 9 + (60307 / 168750) * alpha * t ^ 11 + (584 / 84375) * alpha * t ^ 17) * c_sq
theorem v25_20 (t : ℂ) : (momentPoly 25 z25 2 0).eval t = ((563 / 100) * t ^ 2 + (2983 / 300) * t ^ 4 + (-73 / 15) * alpha * t ^ 2 + (73 / 15) * alpha * t ^ 4 + (8 / 75) * alpha * c * t ^ 2 + (8 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_10, v24_20]
  try simp only [phase22_00, phase22_10, phase22_20]
  try simp only [star_one, star_neg]
  linear_combination ((2 / 75) * t ^ 2) * alpha_sq + ((2 / 75) * t ^ 2) * c_sq
theorem v25_21 (t : ℂ) : (momentPoly 25 z25 2 1).eval t = ((292 / 75) * t ^ 3 + (-292 / 75) * t ^ 5 + (-196 / 15) * c * t + (841 / 75) * c * t ^ 3 + (-181 / 75) * c * t ^ 5 + (-196 / 15) * alpha * t + (599 / 75) * alpha * t ^ 3 + (61 / 75) * alpha * t ^ 5 + (292 / 225) * alpha * c * t ^ 3 + (-292 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_01, v24_10, v24_11, v24_20, v24_21]
  try simp only [phase22_00, phase22_01, phase22_10, phase22_11, phase22_20, phase22_21]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 225) * t ^ 3 + (73 / 225) * t ^ 5 + (4 / 1125) * c * t ^ 3 + (4 / 1125) * c * t ^ 5) * alpha_sq + ((-4 / 1125) * alpha * t ^ 3 + (-4 / 1125) * alpha * t ^ 5) * c_sq
theorem v25_22 (t : ℂ) : (momentPoly 25 z25 2 2).eval t = (1225 + (-864) * t ^ 2 + (-1570033 / 6000) * t ^ 4 + (10907 / 1000) * t ^ 6 + (874591 / 6000) * t ^ 8 + (-1168 / 375) * c * t ^ 4 + (2336 / 1125) * c * t ^ 6 + (1168 / 1125) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_01, v24_02, v24_10, v24_11, v24_12, v24_20, v24_21, v24_22]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_10, phase22_11, phase22_12, phase22_20, phase22_21, phase22_22]
  try simp only [star_one, star_neg]
  linear_combination ((-64 / 25) * t ^ 2 + (679 / 375) * t ^ 4 + (27 / 125) * t ^ 6 + (292 / 1125) * c * t ^ 4 + (-584 / 3375) * c * t ^ 6 + (-292 / 3375) * c * t ^ 8 + (-16 / 16875) * c ^ 2 * t ^ 6 + (-8 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((64 / 25) * t ^ 2 + (-307 / 125) * t ^ 4 + (2431 / 5625) * t ^ 6 + (8 / 5625) * t ^ 8) * c_sq
theorem v25_23 (t : ℂ) : (momentPoly 25 z25 2 3).eval t = ((13724 / 25) * t ^ 3 + (-11460803 / 15000) * t ^ 5 + (6909487 / 30000) * t ^ 7 + (-385827 / 10000) * t ^ 9 + (6126167 / 90000) * t ^ 11 + (-4023767 / 90000) * t ^ 13 + (-14116 / 15) * c * t + (39527 / 25) * c * t ^ 3 + (-2455101 / 2500) * c * t ^ 5 + (704324 / 1875) * c * t ^ 7 + (-760829 / 7500) * c * t ^ 9 + (4967 / 2250) * c * t ^ 11 + (-29731 / 11250) * c * t ^ 13 + (14116 / 15) * alpha * t + (-28153 / 25) * alpha * t ^ 3 + (12790943 / 60000) * alpha * t ^ 5 + (-444609 / 40000) * alpha * t ^ 7 + (-10367 / 24000) * alpha * t ^ 9 + (4268437 / 360000) * alpha * t ^ 11 + (14338091 / 360000) * alpha * t ^ 13 + (-13724 / 75) * alpha * c * t ^ 3 + (198596 / 625) * alpha * c * t ^ 5 + (-249056 / 1875) * alpha * c * t ^ 7 + (968 / 1875) * alpha * c * t ^ 9 + (-21268 / 16875) * alpha * c * t ^ 11 + (-20132 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_01, v24_02, v24_03, v24_10, v24_11, v24_12, v24_13, v24_20, v24_21, v24_22, v24_23]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_10, phase22_11, phase22_12, phase22_13, phase22_20, phase22_21, phase22_22, phase22_23]
  try simp only [star_one, star_neg]
  linear_combination ((-3431 / 75) * t ^ 3 + (3229 / 45) * t ^ 5 + (-1904 / 75) * t ^ 7 + (-26633 / 16875) * t ^ 11 + (16133 / 16875) * t ^ 13 + (188 / 375) * c * t ^ 3 + (4909 / 22500) * c * t ^ 5 + (-397943 / 675000) * c * t ^ 7 + (-8273 / 225000) * c * t ^ 9 + (65107 / 675000) * c * t ^ 11 + (24817 / 675000) * c * t ^ 13 + (-292 / 5625) * c ^ 2 * t ^ 7 + (292 / 5625) * c ^ 2 * t ^ 9) * alpha_sq + ((228 / 625) * t ^ 5 + (-2 / 25) * t ^ 7 + (-584 / 1875) * t ^ 9 + (2 / 75) * t ^ 11 + (188 / 375) * alpha * t ^ 3 + (4909 / 22500) * alpha * t ^ 5 + (-442777 / 675000) * alpha * t ^ 7 + (16 / 28125) * alpha * t ^ 9 + (55763 / 675000) * alpha * t ^ 11 + (-284 / 84375) * alpha * t ^ 13) * c_sq
theorem v25_24 (t : ℂ) : (momentPoly 25 z25 2 4).eval t = ((953159 / 25) * t ^ 2 + (-56449333 / 1500) * t ^ 4 + (5646234503 / 1200000) * t ^ 6 + (-1553454577 / 240000) * t ^ 8 + (586133343 / 160000) * t ^ 10 + (7866326981 / 7200000) * t ^ 12 + (669827191 / 1800000) * t ^ 14 + (786728231 / 7200000) * t ^ 18 + (169640281 / 7200000) * t ^ 20 + (-1472 / 15) * c * t ^ 4 + (5433226 / 28125) * c * t ^ 6 + (-243151 / 5625) * c * t ^ 8 + (-3329563 / 28125) * c * t ^ 10 + (492151 / 28125) * c * t ^ 12 + (4255879 / 84375) * c * t ^ 14 + (-161056 / 84375) * c * t ^ 18 + (8 / 15) * c * t ^ 20 + (494356 / 15) * alpha * t ^ 2 + (-263899 / 5) * alpha * t ^ 4 + (9564762619 / 900000) * alpha * t ^ 6 + (551411297 / 60000) * alpha * t ^ 8 + (919110181 / 360000) * alpha * t ^ 10 + (-4395855809 / 1800000) * alpha * t ^ 12 + (-231186137 / 1350000) * alpha * t ^ 14 + (-170519657 / 5400000) * alpha * t ^ 18 + (523346473 / 5400000) * alpha * t ^ 20 + (-54176 / 75) * alpha * c * t ^ 2 + (741932 / 1125) * alpha * c * t ^ 4 + (16829161 / 37500) * alpha * c * t ^ 6 + (-711329 / 1875) * alpha * c * t ^ 8 + (-9153121 / 75000) * alpha * c * t ^ 10 + (2936099 / 25000) * alpha * c * t ^ 12 + (-1518757 / 37500) * alpha * c * t ^ 14 + (1649369 / 675000) * alpha * c * t ^ 18 + (-41197 / 135000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_01, v24_02, v24_03, v24_04, v24_10, v24_11, v24_12, v24_13, v24_14, v24_20, v24_21, v24_22, v24_23, v24_24]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04, phase22_10, phase22_11, phase22_12, phase22_13, phase22_14, phase22_20, phase22_21, phase22_22, phase22_23, phase22_24]
  try simp only [star_one, star_neg]
  linear_combination ((13544 / 75) * t ^ 2 + (-1644523 / 5625) * t ^ 4 + (4426343 / 50000) * t ^ 6 + (4208671 / 90000) * t ^ 8 + (-60821299 / 900000) * t ^ 10 + (1506753 / 50000) * t ^ 12 + (181189 / 18000) * t ^ 14 + (362131 / 900000) * t ^ 18 + (-414017 / 84375) * c * t ^ 6 + (324253 / 28125) * c * t ^ 8 + (-314369 / 84375) * c * t ^ 10 + (-160309 / 84375) * c * t ^ 12 + (-292456 / 253125) * c * t ^ 14 + (51514 / 253125) * c * t ^ 18 + (-2 / 45) * c * t ^ 20 + (-233 / 9375) * c ^ 2 * t ^ 8 + (41303 / 843750) * c ^ 2 * t ^ 10 + (-4798 / 421875) * c ^ 2 * t ^ 12 + (-62579 / 2531250) * c ^ 2 * t ^ 14 + (-1168 / 1265625) * c ^ 2 * t ^ 18 + (-1168 / 1265625) * c ^ 2 * t ^ 20) * alpha_sq + ((13544 / 75) * t ^ 2 + (-2130812 / 5625) * t ^ 4 + (45826651 / 150000) * t ^ 6 + (-25795417 / 225000) * t ^ 8 + (31874729 / 1500000) * t ^ 10 + (-7012691 / 1125000) * t ^ 12 + (403237 / 421875) * t ^ 14 + (2949041 / 13500000) * t ^ 18 + (1168 / 421875) * t ^ 20 + (26864 / 375) * alpha * t ^ 4 + (-2272829 / 16875) * alpha * t ^ 6 + (5837746 / 84375) * alpha * t ^ 8 + (-63083 / 9375) * alpha * t ^ 10 + (-584 / 84375) * alpha * t ^ 12 + (40264 / 84375) * alpha * t ^ 14 + (10066 / 84375) * alpha * t ^ 18) * c_sq
theorem v25_30 (t : ℂ) : (momentPoly 25 z25 3 0).eval t = ((-242 / 25) * t ^ 3 + (217 / 25) * t ^ 5 + 1 * t ^ 9 + (1247 / 375) * c * t ^ 3 + (-889 / 125) * c * t ^ 5 + (-284 / 1125) * c * t ^ 9 + (-17369 / 3000) * alpha * t ^ 3 + (-6079 / 2000) * alpha * t ^ 5 + (-67379 / 18000) * alpha * t ^ 9 + (292 / 75) * alpha * c * t ^ 3 + (-292 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_10, v24_20, v24_30]
  try simp only [phase22_00, phase22_10, phase22_20, phase22_30]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-4 / 375) * c * t ^ 3 + (-4 / 375) * c * t ^ 5) * alpha_sq + ((-4 / 375) * alpha * t ^ 3 + (-4 / 375) * alpha * t ^ 5) * c_sq
theorem v25_31 (t : ℂ) : (momentPoly 25 z25 3 1).eval t = ((10134 / 25) * t ^ 2 + (54437 / 375) * t ^ 4 + (-77337 / 250) * t ^ 6 + (1999 / 250) * t ^ 10 + (-8 / 15) * c * t ^ 4 + (4 / 5) * c * t ^ 6 + (-4 / 15) * c * t ^ 10 + (-1752 / 5) * alpha * t ^ 2 + 458 * alpha * t ^ 4 + (-103) * alpha * t ^ 6 + (-23 / 5) * alpha * t ^ 10 + (192 / 25) * alpha * c * t ^ 2 + (-5251 / 2250) * alpha * c * t ^ 4 + (-1983 / 500) * alpha * c * t ^ 6 + (1343 / 1500) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_01, v24_10, v24_11, v24_20, v24_21, v24_30, v24_31]
  try simp only [phase22_00, phase22_01, phase22_10, phase22_11, phase22_20, phase22_21, phase22_30, phase22_31]
  try simp only [star_one, star_neg]
  linear_combination ((48 / 25) * t ^ 2 + (-71501 / 45000) * t ^ 4 + (-1447 / 30000) * t ^ 6 + (-24817 / 90000) * t ^ 10) * alpha_sq + ((48 / 25) * t ^ 2 + (-23161 / 11250) * t ^ 4 + (2399 / 3750) * t ^ 6 + (142 / 5625) * t ^ 10 + (-146 / 375) * alpha * t ^ 4 + (146 / 375) * alpha * t ^ 6) * c_sq
theorem v25_32 (t : ℂ) : (momentPoly 25 z25 3 2).eval t = ((13724 / 25) * t ^ 3 + (-11460803 / 15000) * t ^ 5 + (6909487 / 30000) * t ^ 7 + (-385827 / 10000) * t ^ 9 + (6126167 / 90000) * t ^ 11 + (-4023767 / 90000) * t ^ 13 + (-14116 / 15) * c * t + (39527 / 25) * c * t ^ 3 + (-2455101 / 2500) * c * t ^ 5 + (704324 / 1875) * c * t ^ 7 + (-760829 / 7500) * c * t ^ 9 + (4967 / 2250) * c * t ^ 11 + (-29731 / 11250) * c * t ^ 13 + (-14116 / 15) * alpha * t + (28153 / 25) * alpha * t ^ 3 + (-12790943 / 60000) * alpha * t ^ 5 + (444609 / 40000) * alpha * t ^ 7 + (10367 / 24000) * alpha * t ^ 9 + (-4268437 / 360000) * alpha * t ^ 11 + (-14338091 / 360000) * alpha * t ^ 13 + (13724 / 75) * alpha * c * t ^ 3 + (-198596 / 625) * alpha * c * t ^ 5 + (249056 / 1875) * alpha * c * t ^ 7 + (-968 / 1875) * alpha * c * t ^ 9 + (21268 / 16875) * alpha * c * t ^ 11 + (20132 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_01, v24_02, v24_10, v24_11, v24_12, v24_20, v24_21, v24_22, v24_30, v24_31, v24_32]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_10, phase22_11, phase22_12, phase22_20, phase22_21, phase22_22, phase22_30, phase22_31, phase22_32]
  try simp only [star_one, star_neg]
  linear_combination ((-3431 / 75) * t ^ 3 + (3229 / 45) * t ^ 5 + (-1904 / 75) * t ^ 7 + (-26633 / 16875) * t ^ 11 + (16133 / 16875) * t ^ 13 + (188 / 375) * c * t ^ 3 + (4909 / 22500) * c * t ^ 5 + (-397943 / 675000) * c * t ^ 7 + (-8273 / 225000) * c * t ^ 9 + (65107 / 675000) * c * t ^ 11 + (24817 / 675000) * c * t ^ 13 + (-292 / 5625) * c ^ 2 * t ^ 7 + (292 / 5625) * c ^ 2 * t ^ 9) * alpha_sq + ((228 / 625) * t ^ 5 + (-2 / 25) * t ^ 7 + (-584 / 1875) * t ^ 9 + (2 / 75) * t ^ 11 + (-188 / 375) * alpha * t ^ 3 + (-4909 / 22500) * alpha * t ^ 5 + (442777 / 675000) * alpha * t ^ 7 + (-16 / 28125) * alpha * t ^ 9 + (-55763 / 675000) * alpha * t ^ 11 + (284 / 84375) * alpha * t ^ 13) * c_sq
theorem v25_33 (t : ℂ) : (momentPoly 25 z25 3 3).eval t = (88225 + (-91422) * t ^ 2 + (-108332277 / 2000) * t ^ 4 + (12732574219 / 200000) * t ^ 6 + (411880859 / 40000) * t ^ 8 + (-9840284841 / 800000) * t ^ 10 + (-176860867 / 600000) * t ^ 12 + (24874419 / 400000) * t ^ 14 + (77241709 / 2400000) * t ^ 18 + (-80592 / 125) * c * t ^ 4 + (1547063 / 1875) * c * t ^ 6 + (94297 / 750) * c * t ^ 8 + (-357577 / 1250) * c * t ^ 10 + (-924011 / 11250) * c * t ^ 12 + (78259 / 1250) * c * t ^ 14 + (-568 / 1125) * c * t ^ 18) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_01, v24_02, v24_03, v24_10, v24_11, v24_12, v24_13, v24_20, v24_21, v24_22, v24_23, v24_30, v24_31, v24_32, v24_33]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_10, phase22_11, phase22_12, phase22_13, phase22_20, phase22_21, phase22_22, phase22_23, phase22_30, phase22_31, phase22_32, phase22_33]
  try simp only [star_one, star_neg]
  linear_combination ((-6772 / 25) * t ^ 2 + (46851 / 125) * t ^ 4 + (-493457 / 6000) * t ^ 6 + (-8849429 / 300000) * t ^ 8 + (1074401 / 100000) * t ^ 10 + (15288037 / 13500000) * t ^ 12 + (-60632543 / 4500000) * t ^ 14 + (-4703101 / 3375000) * t ^ 18 + (6716 / 125) * c * t ^ 4 + (-2226532 / 28125) * c * t ^ 6 + (134812 / 9375) * c * t ^ 8 + (31444 / 3125) * c * t ^ 10 + (192 / 125) * c * t ^ 12 + (-608 / 1125) * c * t ^ 14 + (-224 / 1125) * c ^ 2 * t ^ 6 + (851 / 56250) * c ^ 2 * t ^ 8 + (6589 / 37500) * c ^ 2 * t ^ 10 + (-3869 / 112500) * c ^ 2 * t ^ 14) * alpha_sq + ((6772 / 25) * t ^ 2 + (-63549 / 125) * t ^ 4 + (8240223 / 25000) * t ^ 6 + (-4091531 / 37500) * t ^ 8 + (652987 / 25000) * t ^ 10 + (-1254907 / 843750) * t ^ 12 + (398693 / 281250) * t ^ 14 + (10082 / 421875) * t ^ 18) * c_sq
theorem v25_34 (t : ℂ) : (momentPoly 25 z25 3 4).eval t = ((1895664 / 25) * t ^ 3 + (-66980107 / 500) * t ^ 5 + (25759564021 / 375000) * t ^ 7 + (-30598138501 / 750000) * t ^ 9 + (2845488401 / 60000) * t ^ 11 + (-20145477093 / 1000000) * t ^ 13 + (13393634929 / 2250000) * t ^ 15 + (-28455587893 / 9000000) * t ^ 17 + (225448573 / 13500000) * t ^ 19 + (91963721 / 1000000) * t ^ 21 + (1620362503 / 27000000) * t ^ 25 + (-1328068 / 15) * c * t + (5459772 / 25) * c * t ^ 3 + (-55078397 / 250) * c * t ^ 5 + (71695582547 / 500000) * c * t ^ 7 + (-112544982743 / 1500000) * c * t ^ 9 + (4710149141 / 200000) * c * t ^ 11 + (-3453936753 / 1000000) * c * t ^ 13 + (244648887 / 250000) * c * t ^ 15 + (-2083583 / 90000) * c * t ^ 17 + (-70964903 / 1800000) * c * t ^ 19 + (-24473909 / 9000000) * c * t ^ 21 + (-6700291 / 2250000) * c * t ^ 25 + (1328068 / 15) * alpha * t + (-3888708 / 25) * alpha * t ^ 3 + (145340327 / 2000) * alpha * t ^ 5 + (-3357195389 / 160000) * alpha * t ^ 7 + (82668190933 / 4800000) * alpha * t ^ 9 + (-6154949241 / 1600000) * alpha * t ^ 11 + (1501947580979 / 144000000) * alpha * t ^ 13 + (-5086029229 / 750000) * alpha * t ^ 15 + (-55412226407 / 144000000) * alpha * t ^ 17 + (-4741046827 / 24000000) * alpha * t ^ 19 + (39227849 / 28800000) * alpha * t ^ 21 + (-4103911087 / 144000000) * alpha * t ^ 25 + (-631888 / 25) * alpha * c * t ^ 3 + (23130772 / 375) * alpha * c * t ^ 5 + (-18101022617 / 375000) * alpha * c * t ^ 7 + (15312420713 / 1125000) * alpha * c * t ^ 9 + (-1518536549 / 450000) * alpha * c * t ^ 11 + (7962244643 / 6750000) * alpha * c * t ^ 13 + (630586289 / 1687500) * alpha * c * t ^ 15 + (33177517 / 421875) * alpha * c * t ^ 17 + (1344756091 / 20250000) * alpha * c * t ^ 19 + (-159265507 / 2250000) * alpha * c * t ^ 21 + (-1516972 / 1265625) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_01, v24_02, v24_03, v24_04, v24_10, v24_11, v24_12, v24_13, v24_14, v24_20, v24_21, v24_22, v24_23, v24_24, v24_30, v24_31, v24_32, v24_33, v24_34]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04, phase22_10, phase22_11, phase22_12, phase22_13, phase22_14, phase22_20, phase22_21, phase22_22, phase22_23, phase22_24, phase22_30, phase22_31, phase22_32, phase22_33, phase22_34]
  try simp only [star_one, star_neg]
  linear_combination ((-157972 / 25) * t ^ 3 + (1000961 / 75) * t ^ 5 + (-4005854131 / 500000) * t ^ 7 + (1866409459 / 1500000) * t ^ 9 + (-1009012353 / 1000000) * t ^ 11 + (23387417971 / 27000000) * t ^ 13 + (-1100097811 / 6750000) * t ^ 15 + (45638489 / 843750) * t ^ 17 + (841425019 / 81000000) * t ^ 19 + (-158772707 / 9000000) * t ^ 21 + (-1112293 / 1265625) * t ^ 25 + (8656 / 125) * c * t ^ 3 + (-5363 / 750) * c * t ^ 5 + (-243376613 / 1687500) * c * t ^ 7 + (20880347 / 250000) * c * t ^ 9 + (32856563 / 2250000) * c * t ^ 11 + (-63847373 / 6750000) * c * t ^ 13 + (-68008511 / 16875000) * c * t ^ 15 + (72132499 / 33750000) * c * t ^ 17 + (15353083 / 20250000) * c * t ^ 19 + (-2347691 / 33750000) * c * t ^ 21 + (1811641 / 25312500) * c * t ^ 25 + (-80008 / 5625) * c ^ 2 * t ^ 7 + (2264069 / 84375) * c ^ 2 * t ^ 9 + (-5828434 / 421875) * c ^ 2 * t ^ 11 + (62699 / 46875) * c ^ 2 * t ^ 13 + (-8468 / 140625) * c ^ 2 * t ^ 15 + (-20132 / 421875) * c ^ 2 * t ^ 17 + (-21316 / 421875) * c ^ 2 * t ^ 19 + (2 / 75) * c ^ 2 * t ^ 21) * alpha_sq + ((12312 / 125) * t ^ 5 + (-20890759 / 281250) * t ^ 7 + (-16257053 / 112500) * t ^ 9 + (73881631 / 562500) * t ^ 11 + (4242029 / 562500) * t ^ 13 + (-10853989 / 562500) * t ^ 15 + (40864 / 140625) * t ^ 17 + (26638 / 46875) * t ^ 19 + (-4 / 25) * t ^ 21 + (8656 / 125) * alpha * t ^ 3 + (-5363 / 750) * alpha * t ^ 5 + (-274087903 / 1687500) * alpha * t ^ 7 + (26463721 / 250000) * alpha * t ^ 9 + (6849131 / 1125000) * alpha * t ^ 11 + (-51689969 / 3375000) * alpha * t ^ 13 + (210961553 / 33750000) * alpha * t ^ 15 + (741623 / 4218750) * alpha * t ^ 17 + (-8066309 / 20250000) * alpha * t ^ 19 + (2692399 / 33750000) * alpha * t ^ 21 + (41464 / 6328125) * alpha * t ^ 25) * c_sq
theorem v25_40 (t : ℂ) : (momentPoly 25 z25 4 0).eval t = ((-33717487 / 60000) * t ^ 4 + (7209333 / 10000) * t ^ 6 + (2064113 / 40000) * t ^ 8 + (261173 / 30000) * t ^ 10 + (3518513 / 360000) * t ^ 16 + (2704 / 375) * c * t ^ 4 + (-1136 / 375) * c * t ^ 6 + (-1168 / 375) * c * t ^ 8 + (-16 / 15) * c * t ^ 10 + (-20953 / 150) * alpha * t ^ 4 + (-66163 / 375) * alpha * t ^ 6 + (9113 / 30) * alpha * t ^ 8 + (18932 / 1125) * alpha * t ^ 10 + (-5033 / 1125) * alpha * t ^ 16 + (16046 / 5625) * alpha * c * t ^ 4 + (-8233 / 1875) * alpha * c * t ^ 6 + (1196 / 625) * alpha * c * t ^ 8 + (22417 / 5625) * alpha * c * t ^ 10 + (1168 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_10, v24_20, v24_30, v24_40]
  try simp only [phase22_00, phase22_10, phase22_20, phase22_30, phase22_40]
  try simp only [star_one, star_neg]
  linear_combination ((10391 / 11250) * t ^ 4 + (-3413 / 7500) * t ^ 6 + (24817 / 22500) * t ^ 10 + (-292 / 375) * c * t ^ 4 + (584 / 1125) * c * t ^ 6 + (292 / 1125) * c * t ^ 8 + (16 / 5625) * c ^ 2 * t ^ 6 + (8 / 5625) * c ^ 2 * t ^ 8) * alpha_sq + ((-4877 / 5625) * t ^ 4 + (789 / 625) * t ^ 6 + (-8 / 1875) * t ^ 8 + (568 / 5625) * t ^ 10 + (-292 / 375) * alpha * t ^ 4 + (292 / 375) * alpha * t ^ 6) * c_sq
theorem v25_41 (t : ℂ) : (momentPoly 25 z25 4 1).eval t = ((-22748 / 25) * t ^ 3 + (852632 / 625) * t ^ 5 + (-787492 / 1875) * t ^ 7 + (39403 / 1875) * t ^ 9 + (-325628 / 5625) * t ^ 11 + (14507 / 5625) * t ^ 17 + (117218 / 375) * c * t ^ 3 + (-4115333 / 5000) * c * t ^ 5 + (3342119 / 7500) * c * t ^ 7 + (-2299927 / 90000) * c * t ^ 9 + (70519 / 2500) * c * t ^ 11 + (-72277 / 30000) * c * t ^ 17 + (-816343 / 1500) * alpha * t ^ 3 + (-742543 / 7500) * alpha * t ^ 5 + (5749231 / 7500) * alpha * t ^ 7 + (-20544449 / 45000) * alpha * t ^ 9 + (162253 / 1250) * alpha * t ^ 11 + (33781 / 15000) * alpha * t ^ 17 + (27448 / 75) * alpha * c * t ^ 3 + (-3794654 / 5625) * alpha * c * t ^ 5 + (2143508 / 5625) * alpha * c * t ^ 7 + (-416522 / 5625) * alpha * c * t ^ 9 + (7072 / 16875) * alpha * c * t ^ 11 + (20132 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_01, v24_10, v24_11, v24_20, v24_21, v24_30, v24_31, v24_40, v24_41]
  try simp only [phase22_00, phase22_01, phase22_10, phase22_11, phase22_20, phase22_21, phase22_30, phase22_31, phase22_40, phase22_41]
  try simp only [star_one, star_neg]
  linear_combination ((6862 / 75) * t ^ 3 + (-530323 / 3750) * t ^ 5 + (165847 / 5625) * t ^ 7 + (206509 / 11250) * t ^ 9 + (40232 / 16875) * t ^ 11 + (-5033 / 16875) * t ^ 17 + (-376 / 375) * c * t ^ 3 + (-1406 / 5625) * c * t ^ 5 + (24568 / 28125) * c * t ^ 7 + (3614 / 28125) * c * t ^ 9 + (1136 / 84375) * c * t ^ 11 + (584 / 84375) * c * t ^ 17 + (292 / 5625) * c ^ 2 * t ^ 7 + (-292 / 5625) * c ^ 2 * t ^ 9) * alpha_sq + ((-184 / 1875) * t ^ 5 + (-8 / 25) * t ^ 7 + (584 / 1875) * t ^ 9 + (8 / 75) * t ^ 11 + (-376 / 375) * alpha * t ^ 3 + (-3503 / 5625) * alpha * t ^ 5 + (97699 / 56250) * alpha * t ^ 7 + (-4814 / 28125) * alpha * t ^ 9 + (-60307 / 168750) * alpha * t ^ 11 + (-584 / 84375) * alpha * t ^ 17) * c_sq
theorem v25_42 (t : ℂ) : (momentPoly 25 z25 4 2).eval t = ((953159 / 25) * t ^ 2 + (-56449333 / 1500) * t ^ 4 + (5646234503 / 1200000) * t ^ 6 + (-1553454577 / 240000) * t ^ 8 + (586133343 / 160000) * t ^ 10 + (7866326981 / 7200000) * t ^ 12 + (669827191 / 1800000) * t ^ 14 + (786728231 / 7200000) * t ^ 18 + (169640281 / 7200000) * t ^ 20 + (-1472 / 15) * c * t ^ 4 + (5433226 / 28125) * c * t ^ 6 + (-243151 / 5625) * c * t ^ 8 + (-3329563 / 28125) * c * t ^ 10 + (492151 / 28125) * c * t ^ 12 + (4255879 / 84375) * c * t ^ 14 + (-161056 / 84375) * c * t ^ 18 + (8 / 15) * c * t ^ 20 + (-494356 / 15) * alpha * t ^ 2 + (263899 / 5) * alpha * t ^ 4 + (-9564762619 / 900000) * alpha * t ^ 6 + (-551411297 / 60000) * alpha * t ^ 8 + (-919110181 / 360000) * alpha * t ^ 10 + (4395855809 / 1800000) * alpha * t ^ 12 + (231186137 / 1350000) * alpha * t ^ 14 + (170519657 / 5400000) * alpha * t ^ 18 + (-523346473 / 5400000) * alpha * t ^ 20 + (54176 / 75) * alpha * c * t ^ 2 + (-741932 / 1125) * alpha * c * t ^ 4 + (-16829161 / 37500) * alpha * c * t ^ 6 + (711329 / 1875) * alpha * c * t ^ 8 + (9153121 / 75000) * alpha * c * t ^ 10 + (-2936099 / 25000) * alpha * c * t ^ 12 + (1518757 / 37500) * alpha * c * t ^ 14 + (-1649369 / 675000) * alpha * c * t ^ 18 + (41197 / 135000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_01, v24_02, v24_10, v24_11, v24_12, v24_20, v24_21, v24_22, v24_30, v24_31, v24_32, v24_40, v24_41, v24_42]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_10, phase22_11, phase22_12, phase22_20, phase22_21, phase22_22, phase22_30, phase22_31, phase22_32, phase22_40, phase22_41, phase22_42]
  try simp only [star_one, star_neg]
  linear_combination ((13544 / 75) * t ^ 2 + (-1644523 / 5625) * t ^ 4 + (4426343 / 50000) * t ^ 6 + (4208671 / 90000) * t ^ 8 + (-60821299 / 900000) * t ^ 10 + (1506753 / 50000) * t ^ 12 + (181189 / 18000) * t ^ 14 + (362131 / 900000) * t ^ 18 + (-414017 / 84375) * c * t ^ 6 + (324253 / 28125) * c * t ^ 8 + (-314369 / 84375) * c * t ^ 10 + (-160309 / 84375) * c * t ^ 12 + (-292456 / 253125) * c * t ^ 14 + (51514 / 253125) * c * t ^ 18 + (-2 / 45) * c * t ^ 20 + (-233 / 9375) * c ^ 2 * t ^ 8 + (41303 / 843750) * c ^ 2 * t ^ 10 + (-4798 / 421875) * c ^ 2 * t ^ 12 + (-62579 / 2531250) * c ^ 2 * t ^ 14 + (-1168 / 1265625) * c ^ 2 * t ^ 18 + (-1168 / 1265625) * c ^ 2 * t ^ 20) * alpha_sq + ((13544 / 75) * t ^ 2 + (-2130812 / 5625) * t ^ 4 + (45826651 / 150000) * t ^ 6 + (-25795417 / 225000) * t ^ 8 + (31874729 / 1500000) * t ^ 10 + (-7012691 / 1125000) * t ^ 12 + (403237 / 421875) * t ^ 14 + (2949041 / 13500000) * t ^ 18 + (1168 / 421875) * t ^ 20 + (-26864 / 375) * alpha * t ^ 4 + (2272829 / 16875) * alpha * t ^ 6 + (-5837746 / 84375) * alpha * t ^ 8 + (63083 / 9375) * alpha * t ^ 10 + (584 / 84375) * alpha * t ^ 12 + (-40264 / 84375) * alpha * t ^ 14 + (-10066 / 84375) * alpha * t ^ 18) * c_sq
theorem v25_43 (t : ℂ) : (momentPoly 25 z25 4 3).eval t = ((1895664 / 25) * t ^ 3 + (-66980107 / 500) * t ^ 5 + (25759564021 / 375000) * t ^ 7 + (-30598138501 / 750000) * t ^ 9 + (2845488401 / 60000) * t ^ 11 + (-20145477093 / 1000000) * t ^ 13 + (13393634929 / 2250000) * t ^ 15 + (-28455587893 / 9000000) * t ^ 17 + (225448573 / 13500000) * t ^ 19 + (91963721 / 1000000) * t ^ 21 + (1620362503 / 27000000) * t ^ 25 + (-1328068 / 15) * c * t + (5459772 / 25) * c * t ^ 3 + (-55078397 / 250) * c * t ^ 5 + (71695582547 / 500000) * c * t ^ 7 + (-112544982743 / 1500000) * c * t ^ 9 + (4710149141 / 200000) * c * t ^ 11 + (-3453936753 / 1000000) * c * t ^ 13 + (244648887 / 250000) * c * t ^ 15 + (-2083583 / 90000) * c * t ^ 17 + (-70964903 / 1800000) * c * t ^ 19 + (-24473909 / 9000000) * c * t ^ 21 + (-6700291 / 2250000) * c * t ^ 25 + (-1328068 / 15) * alpha * t + (3888708 / 25) * alpha * t ^ 3 + (-145340327 / 2000) * alpha * t ^ 5 + (3357195389 / 160000) * alpha * t ^ 7 + (-82668190933 / 4800000) * alpha * t ^ 9 + (6154949241 / 1600000) * alpha * t ^ 11 + (-1501947580979 / 144000000) * alpha * t ^ 13 + (5086029229 / 750000) * alpha * t ^ 15 + (55412226407 / 144000000) * alpha * t ^ 17 + (4741046827 / 24000000) * alpha * t ^ 19 + (-39227849 / 28800000) * alpha * t ^ 21 + (4103911087 / 144000000) * alpha * t ^ 25 + (631888 / 25) * alpha * c * t ^ 3 + (-23130772 / 375) * alpha * c * t ^ 5 + (18101022617 / 375000) * alpha * c * t ^ 7 + (-15312420713 / 1125000) * alpha * c * t ^ 9 + (1518536549 / 450000) * alpha * c * t ^ 11 + (-7962244643 / 6750000) * alpha * c * t ^ 13 + (-630586289 / 1687500) * alpha * c * t ^ 15 + (-33177517 / 421875) * alpha * c * t ^ 17 + (-1344756091 / 20250000) * alpha * c * t ^ 19 + (159265507 / 2250000) * alpha * c * t ^ 21 + (1516972 / 1265625) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_01, v24_02, v24_03, v24_10, v24_11, v24_12, v24_13, v24_20, v24_21, v24_22, v24_23, v24_30, v24_31, v24_32, v24_33, v24_40, v24_41, v24_42, v24_43]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_10, phase22_11, phase22_12, phase22_13, phase22_20, phase22_21, phase22_22, phase22_23, phase22_30, phase22_31, phase22_32, phase22_33, phase22_40, phase22_41, phase22_42, phase22_43]
  try simp only [star_one, star_neg]
  linear_combination ((-157972 / 25) * t ^ 3 + (1000961 / 75) * t ^ 5 + (-4005854131 / 500000) * t ^ 7 + (1866409459 / 1500000) * t ^ 9 + (-1009012353 / 1000000) * t ^ 11 + (23387417971 / 27000000) * t ^ 13 + (-1100097811 / 6750000) * t ^ 15 + (45638489 / 843750) * t ^ 17 + (841425019 / 81000000) * t ^ 19 + (-158772707 / 9000000) * t ^ 21 + (-1112293 / 1265625) * t ^ 25 + (8656 / 125) * c * t ^ 3 + (-5363 / 750) * c * t ^ 5 + (-243376613 / 1687500) * c * t ^ 7 + (20880347 / 250000) * c * t ^ 9 + (32856563 / 2250000) * c * t ^ 11 + (-63847373 / 6750000) * c * t ^ 13 + (-68008511 / 16875000) * c * t ^ 15 + (72132499 / 33750000) * c * t ^ 17 + (15353083 / 20250000) * c * t ^ 19 + (-2347691 / 33750000) * c * t ^ 21 + (1811641 / 25312500) * c * t ^ 25 + (-80008 / 5625) * c ^ 2 * t ^ 7 + (2264069 / 84375) * c ^ 2 * t ^ 9 + (-5828434 / 421875) * c ^ 2 * t ^ 11 + (62699 / 46875) * c ^ 2 * t ^ 13 + (-8468 / 140625) * c ^ 2 * t ^ 15 + (-20132 / 421875) * c ^ 2 * t ^ 17 + (-21316 / 421875) * c ^ 2 * t ^ 19 + (2 / 75) * c ^ 2 * t ^ 21) * alpha_sq + ((12312 / 125) * t ^ 5 + (-20890759 / 281250) * t ^ 7 + (-16257053 / 112500) * t ^ 9 + (73881631 / 562500) * t ^ 11 + (4242029 / 562500) * t ^ 13 + (-10853989 / 562500) * t ^ 15 + (40864 / 140625) * t ^ 17 + (26638 / 46875) * t ^ 19 + (-4 / 25) * t ^ 21 + (-8656 / 125) * alpha * t ^ 3 + (5363 / 750) * alpha * t ^ 5 + (274087903 / 1687500) * alpha * t ^ 7 + (-26463721 / 250000) * alpha * t ^ 9 + (-6849131 / 1125000) * alpha * t ^ 11 + (51689969 / 3375000) * alpha * t ^ 13 + (-210961553 / 33750000) * alpha * t ^ 15 + (-741623 / 4218750) * alpha * t ^ 17 + (8066309 / 20250000) * alpha * t ^ 19 + (-2692399 / 33750000) * alpha * t ^ 21 + (-41464 / 6328125) * alpha * t ^ 25) * c_sq
theorem v25_44 (t : ℂ) : (momentPoly 25 z25 4 4).eval t = (8300425 + (-11231496) * t ^ 2 + (-4881232597 / 500) * t ^ 4 + (275273106793 / 12500) * t ^ 6 + (-2427924427329841 / 240000000) * t ^ 8 + (64563563389889 / 60000000) * t ^ 10 + (-3805116591503 / 9600000) * t ^ 12 + (62070059389211 / 360000000) * t ^ 14 + (-138538867294859 / 2880000000) * t ^ 16 + (19791758923987 / 360000000) * t ^ 18 + (-32039856477367 / 2160000000) * t ^ 20 + (2173112154299 / 120000000) * t ^ 22 + (-12553878340499 / 1440000000) * t ^ 24 + (-107570533679 / 1080000000) * t ^ 26 + (1155676401551 / 8640000000) * t ^ 32 + (-14525248 / 125) * c * t ^ 4 + (406251616 / 1875) * c * t ^ 6 + (-19452681493 / 703125) * c * t ^ 8 + (-89760169022 / 703125) * c * t ^ 10 + (3376716727 / 93750) * c * t ^ 12 + (149065093087 / 4218750) * c * t ^ 14 + (-32630656687 / 1406250) * c * t ^ 16 + (3071192041 / 468750) * c * t ^ 18 + (2337216761 / 4218750) * c * t ^ 20 + (-1170744191 / 4218750) * c * t ^ 22 + (6086903 / 4218750) * c * t ^ 24 + (-1478215303 / 12656250) * c * t ^ 26 + (-11757088 / 6328125) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z25, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v24_00, v24_01, v24_02, v24_03, v24_04, v24_10, v24_11, v24_12, v24_13, v24_14, v24_20, v24_21, v24_22, v24_23, v24_24, v24_30, v24_31, v24_32, v24_33, v24_34, v24_40, v24_41, v24_42, v24_43, v24_44]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04, phase22_10, phase22_11, phase22_12, phase22_13, phase22_14, phase22_20, phase22_21, phase22_22, phase22_23, phase22_24, phase22_30, phase22_31, phase22_32, phase22_33, phase22_34, phase22_40, phase22_41, phase22_42, phase22_43, phase22_44]
  try simp only [star_one, star_neg]
  linear_combination ((-2495888 / 75) * t ^ 2 + (8444044 / 125) * t ^ 4 + (-2746732 / 75) * t ^ 6 + (-194145759 / 2500000) * t ^ 8 + (42500706527 / 9000000) * t ^ 10 + (-53705993993 / 135000000) * t ^ 12 + (-1649153797799 / 270000000) * t ^ 14 + (7697257241 / 1875000) * t ^ 16 + (-135718201433 / 270000000) * t ^ 18 + (49515277547 / 135000000) * t ^ 20 + (124916503 / 30000000) * t ^ 22 + (977142851 / 54000000) * t ^ 26 + (3631312 / 375) * c * t ^ 4 + (-610846064 / 28125) * c * t ^ 6 + (118953354161 / 8437500) * c * t ^ 8 + (-939844786 / 421875) * c * t ^ 10 + (3482043029 / 3375000) * c * t ^ 12 + (-4176991331 / 5062500) * c * t ^ 14 + (1463494907 / 16875000) * c * t ^ 16 + (-112096703 / 843750) * c * t ^ 18 + (-1396448923 / 50625000) * c * t ^ 20 + (780409993 / 25312500) * c * t ^ 22 + (-6086903 / 50625000) * c * t ^ 24 + (24565376 / 18984375) * c * t ^ 26 + (2939272 / 18984375) * c * t ^ 32 + (-22752 / 625) * c ^ 2 * t ^ 6 + (1920776 / 84375) * c ^ 2 * t ^ 8 + (38313124 / 703125) * c ^ 2 * t ^ 10 + (-396109 / 9375) * c ^ 2 * t ^ 12 + (-584744 / 84375) * c ^ 2 * t ^ 14 + (84936301 / 8437500) * c ^ 2 * t ^ 16 + (-11846801 / 4218750) * c ^ 2 * t ^ 18 + (-68036 / 703125) * c ^ 2 * t ^ 20 + (24035711 / 63281250) * c ^ 2 * t ^ 22 + (-8333839 / 126562500) * c ^ 2 * t ^ 24 + (-9136534 / 94921875) * c ^ 2 * t ^ 26 + (-170528 / 94921875) * c ^ 2 * t ^ 32) * alpha_sq + ((2495888 / 75) * t ^ 2 + (-11453556 / 125) * t ^ 4 + (943769926 / 9375) * t ^ 6 + (-720764393803 / 11250000) * t ^ 8 + (333645183617 / 11250000) * t ^ 10 + (-600538335203 / 67500000) * t ^ 12 + (116041345447 / 67500000) * t ^ 14 + (-223890683 / 375000) * t ^ 16 + (138148729 / 8437500) * t ^ 18 + (-18579191 / 67500000) * t ^ 20 + (-1701353201 / 337500000) * t ^ 22 + (8333839 / 42187500) * t ^ 24 + (277166791 / 126562500) * t ^ 26 + (170528 / 31640625) * t ^ 32) * c_sq
#print axioms v25_00
#print axioms v25_11
#print axioms v25_22
#print axioms v25_33
#print axioms v25_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
noncomputable def z26 : Fin 26 → ℂ := Fin.snoc z25 (r ^ 2 * thetaPlus)
theorem v26_00 (t : ℂ) : (momentPoly 26 z26 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00]
  try simp only [phase22_00]
  try simp only [star_one, star_neg]
  ring
theorem v26_01 (t : ℂ) : (momentPoly 26 z26 0 1).eval t = ((-1 / 3) * c * t + (1 / 3) * alpha * t) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_01]
  try simp only [phase22_00, phase22_01]
  try simp only [star_one, star_neg]
  ring
theorem v26_02 (t : ℂ) : (momentPoly 26 z26 0 2).eval t = ((161 / 12) * t ^ 2 + (131 / 12) * t ^ 4 + (73 / 15) * alpha * t ^ 2 + (-73 / 15) * alpha * t ^ 4 + (-8 / 45) * alpha * c * t ^ 2 + (-2 / 45) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_01, v25_02]
  try simp only [phase22_00, phase22_01, phase22_02]
  try simp only [star_one, star_neg]
  linear_combination ((8 / 225) * t ^ 2) * alpha_sq + ((8 / 225) * t ^ 2) * c_sq
theorem v26_03 (t : ℂ) : (momentPoly 26 z26 0 3).eval t = ((-63 / 5) * t ^ 3 + (58 / 5) * t ^ 5 + 1 * t ^ 9 + (679 / 300) * c * t ^ 3 + (-2951 / 300) * c * t ^ 5 + (-71 / 225) * c * t ^ 9 + (6991 / 600) * alpha * t ^ 3 + (10757 / 1200) * alpha * t ^ 5 + (14183 / 3600) * alpha * t ^ 9 + (-73 / 15) * alpha * c * t ^ 3 + (73 / 15) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_01, v25_02, v25_03]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-8 / 375) * c * t ^ 3 + (-16 / 1125) * c * t ^ 5) * alpha_sq + ((8 / 375) * alpha * t ^ 3 + (16 / 1125) * alpha * t ^ 5) * c_sq
theorem v26_04 (t : ℂ) : (momentPoly 26 z26 0 4).eval t = ((-1832279 / 2400) * t ^ 4 + (467449 / 400) * t ^ 6 + (520363 / 4800) * t ^ 8 + (125899 / 3600) * t ^ 10 + (6145 / 576) * t ^ 16 + (968 / 75) * c * t ^ 4 + (-192 / 25) * c * t ^ 6 + (-292 / 75) * c * t ^ 8 + (-4 / 3) * c * t ^ 10 + (275693 / 750) * alpha * t ^ 4 + (-8743 / 375) * alpha * t ^ 6 + (-83047 / 250) * alpha * t ^ 8 + (-18632 / 1125) * alpha * t ^ 10 + (5033 / 1125) * alpha * t ^ 16 + (-7897 / 2250) * alpha * c * t ^ 4 + (1141 / 1500) * alpha * c * t ^ 6 + (-2983 / 1125) * alpha * c * t ^ 8 + (-71923 / 13500) * alpha * c * t ^ 10 + (-292 / 3375) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_01, v25_02, v25_03, v25_04]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04]
  try simp only [star_one, star_neg]
  linear_combination ((17369 / 11250) * t ^ 4 + (6079 / 7500) * t ^ 6 + (81523 / 67500) * t ^ 10 + (-1168 / 1125) * c * t ^ 4 + (292 / 375) * c * t ^ 6 + (292 / 1125) * c * t ^ 8 + (32 / 5625) * c ^ 2 * t ^ 6 + (32 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-4988 / 5625) * t ^ 4 + (3524 / 1875) * t ^ 6 + (-32 / 5625) * t ^ 8 + (2272 / 16875) * t ^ 10 + (1168 / 1125) * alpha * t ^ 4 + (-1168 / 1125) * alpha * t ^ 6) * c_sq
theorem v26_10 (t : ℂ) : (momentPoly 26 z26 1 0).eval t = ((-1 / 3) * c * t + (-1 / 3) * alpha * t) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_10]
  try simp only [phase22_00, phase22_10]
  try simp only [star_one, star_neg]
  ring
theorem v26_11 (t : ℂ) : (momentPoly 26 z26 1 1).eval t = (26 + (-1) * t ^ 2) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_01, v25_10, v25_11]
  try simp only [phase22_00, phase22_01, phase22_10, phase22_11]
  try simp only [star_one, star_neg]
  linear_combination ((-8 / 225) * t ^ 2) * alpha_sq + ((8 / 225) * t ^ 2) * c_sq
theorem v26_12 (t : ℂ) : (momentPoly 26 z26 1 2).eval t = ((73 / 15) * t ^ 3 + (-73 / 15) * t ^ 5 + (-17) * c * t + (721 / 60) * c * t ^ 3 + (-67 / 20) * c * t ^ 5 + 17 * alpha * t + (-479 / 60) * alpha * t ^ 3 + (-41 / 60) * alpha * t ^ 5 + (-73 / 45) * alpha * c * t ^ 3 + (73 / 45) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_01, v25_02, v25_10, v25_11, v25_12]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_10, phase22_11, phase22_12]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 225) * t ^ 3 + (73 / 225) * t ^ 5 + (8 / 1125) * c * t ^ 3 + (16 / 3375) * c * t ^ 5) * alpha_sq + ((8 / 1125) * alpha * t ^ 3 + (16 / 3375) * alpha * t ^ 5) * c_sq
theorem v26_13 (t : ℂ) : (momentPoly 26 z26 1 3).eval t = ((4025 / 4) * t ^ 2 + (-175301 / 600) * t ^ 4 + (-48849 / 400) * t ^ 6 + (19649 / 1200) * t ^ 10 + (-2 / 3) * c * t ^ 4 + 1 * c * t ^ 6 + (-1 / 3) * c * t ^ 10 + 365 * alpha * t ^ 2 + (-5339 / 15) * alpha * t ^ 4 + (-68 / 5) * alpha * t ^ 6 + (68 / 15) * alpha * t ^ 10 + (-40 / 3) * alpha * c * t ^ 2 + (8611 / 1800) * alpha * c * t ^ 4 + (1663 / 400) * alpha * c * t ^ 6 + (-4189 / 3600) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_01, v25_02, v25_03, v25_10, v25_11, v25_12, v25_13]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_10, phase22_11, phase22_12, phase22_13]
  try simp only [star_one, star_neg]
  linear_combination ((8 / 3) * t ^ 2 + (-89249 / 45000) * t ^ 4 + (-3653 / 10000) * t ^ 6 + (-81523 / 270000) * t ^ 10) * alpha_sq + ((8 / 3) * t ^ 2 + (-13862 / 5625) * t ^ 4 + (598 / 625) * t ^ 6 + (568 / 16875) * t ^ 10 + (584 / 1125) * alpha * t ^ 4 + (-584 / 1125) * alpha * t ^ 6) * c_sq
theorem v26_14 (t : ℂ) : (momentPoly 26 z26 1 4).eval t = ((-6174 / 5) * t ^ 3 + (430991 / 250) * t ^ 5 + (-184873 / 375) * t ^ 7 + (25289 / 750) * t ^ 9 + (-37532 / 1125) * t ^ 11 + (3908 / 1125) * t ^ 17 + (33271 / 150) * c * t ^ 3 + (-33637037 / 36000) * c * t ^ 5 + (3251759 / 6000) * c * t ^ 7 + (-3670967 / 72000) * c * t ^ 9 + (166117 / 6000) * c * t ^ 11 + (-239551 / 72000) * c * t ^ 17 + (342559 / 300) * alpha * t ^ 3 + (11976983 / 36000) * alpha * t ^ 5 + (-8257801 / 6000) * alpha * t ^ 7 + (38884493 / 72000) * alpha * t ^ 9 + (-140023 / 6000) * alpha * t ^ 11 + (-78731 / 72000) * alpha * t ^ 17 + (-7154 / 15) * alpha * c * t ^ 3 + (1809727 / 2250) * alpha * c * t ^ 5 + (-481127 / 1125) * alpha * c * t ^ 7 + (230161 / 2250) * alpha * c * t ^ 9 + (-1768 / 3375) * alpha * c * t ^ 11 + (-5033 / 3375) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_01, v25_02, v25_03, v25_04, v25_10, v25_11, v25_12, v25_13, v25_14]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04, phase22_10, phase22_11, phase22_12, phase22_13, phase22_14]
  try simp only [star_one, star_neg]
  linear_combination ((7154 / 75) * t ^ 3 + (-300133 / 2250) * t ^ 5 + (88337 / 5625) * t ^ 7 + (9113 / 450) * t ^ 9 + (39632 / 16875) * t ^ 11 + (-5033 / 16875) * t ^ 17 + (-784 / 375) * c * t ^ 3 + (7756 / 84375) * c * t ^ 5 + (11164 / 9375) * c * t ^ 7 + (4808 / 28125) * c * t ^ 9 + (2272 / 84375) * c * t ^ 11 + (2336 / 253125) * c * t ^ 17 + (1168 / 16875) * c ^ 2 * t ^ 7 + (-1168 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((-1904 / 5625) * t ^ 5 + (-1232 / 5625) * t ^ 7 + (2336 / 5625) * t ^ 9 + (32 / 225) * t ^ 11 + (784 / 375) * alpha * t ^ 3 + (2704 / 9375) * alpha * t ^ 5 + (-18266 / 9375) * alpha * t ^ 7 + (7208 / 28125) * alpha * t ^ 9 + (42562 / 84375) * alpha * t ^ 11 + (2336 / 253125) * alpha * t ^ 17) * c_sq
theorem v26_20 (t : ℂ) : (momentPoly 26 z26 2 0).eval t = ((161 / 12) * t ^ 2 + (131 / 12) * t ^ 4 + (-73 / 15) * alpha * t ^ 2 + (73 / 15) * alpha * t ^ 4 + (8 / 45) * alpha * c * t ^ 2 + (2 / 45) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_10, v25_20]
  try simp only [phase22_00, phase22_10, phase22_20]
  try simp only [star_one, star_neg]
  linear_combination ((8 / 225) * t ^ 2) * alpha_sq + ((8 / 225) * t ^ 2) * c_sq
theorem v26_21 (t : ℂ) : (momentPoly 26 z26 2 1).eval t = ((73 / 15) * t ^ 3 + (-73 / 15) * t ^ 5 + (-17) * c * t + (721 / 60) * c * t ^ 3 + (-67 / 20) * c * t ^ 5 + (-17) * alpha * t + (479 / 60) * alpha * t ^ 3 + (41 / 60) * alpha * t ^ 5 + (73 / 45) * alpha * c * t ^ 3 + (-73 / 45) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_01, v25_10, v25_11, v25_20, v25_21]
  try simp only [phase22_00, phase22_01, phase22_10, phase22_11, phase22_20, phase22_21]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 225) * t ^ 3 + (73 / 225) * t ^ 5 + (8 / 1125) * c * t ^ 3 + (16 / 3375) * c * t ^ 5) * alpha_sq + ((-8 / 1125) * alpha * t ^ 3 + (-16 / 3375) * alpha * t ^ 5) * c_sq
theorem v26_22 (t : ℂ) : (momentPoly 26 z26 2 2).eval t = (1326 + (-100) * t ^ 2 + (-1118269 / 1200) * t ^ 4 + (99209 / 600) * t ^ 6 + (66217 / 400) * t ^ 8 + (-1168 / 225) * c * t ^ 4 + (292 / 75) * c * t ^ 6 + (292 / 225) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_01, v25_02, v25_10, v25_11, v25_12, v25_20, v25_21, v25_22]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_10, phase22_11, phase22_12, phase22_20, phase22_21, phase22_22]
  try simp only [star_one, star_neg]
  linear_combination ((-32 / 9) * t ^ 2 + (2396 / 1125) * t ^ 4 + (244 / 1125) * t ^ 6 + (1168 / 3375) * c * t ^ 4 + (-292 / 1125) * c * t ^ 6 + (-292 / 3375) * c * t ^ 8 + (-32 / 16875) * c ^ 2 * t ^ 6 + (-32 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((32 / 9) * t ^ 2 + (-3364 / 1125) * t ^ 4 + (3652 / 5625) * t ^ 6 + (32 / 16875) * t ^ 8) * c_sq
theorem v26_23 (t : ℂ) : (momentPoly 26 z26 2 3).eval t = ((3577 / 5) * t ^ 3 + (-2458367 / 3000) * t ^ 5 + (244423 / 1200) * t ^ 7 + (-802181 / 6000) * t ^ 9 + (1452059 / 18000) * t ^ 11 + (-838859 / 18000) * t ^ 13 + (-3826 / 3) * c * t + (35329 / 20) * c * t ^ 3 + (-6026107 / 6000) * c * t ^ 5 + (90551 / 200) * c * t ^ 7 + (-867493 / 6000) * c * t ^ 9 + (1643 / 4500) * c * t ^ 11 + (-32731 / 9000) * c * t ^ 13 + (3826 / 3) * alpha * t + (-23471 / 20) * alpha * t ^ 3 + (1282273 / 12000) * alpha * t ^ 5 + (-185513 / 1600) * alpha * t ^ 7 + (823369 / 24000) * alpha * t ^ 9 + (2657089 / 72000) * alpha * t ^ 11 + (3198851 / 72000) * alpha * t ^ 13 + (-3577 / 15) * alpha * c * t ^ 3 + (435407 / 1125) * alpha * c * t ^ 5 + (-1318 / 9) * alpha * c * t ^ 7 + (1018 / 1125) * alpha * c * t ^ 9 + (-5167 / 3375) * alpha * c * t ^ 11 + (-5033 / 3375) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_01, v25_02, v25_03, v25_10, v25_11, v25_12, v25_13, v25_20, v25_21, v25_22, v25_23]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_10, phase22_11, phase22_12, phase22_13, phase22_20, phase22_21, phase22_22, phase22_23]
  try simp only [star_one, star_neg]
  linear_combination ((-3577 / 75) * t ^ 3 + (1551 / 25) * t ^ 5 + (-206 / 15) * t ^ 7 + (-26483 / 16875) * t ^ 11 + (16133 / 16875) * t ^ 13 + (392 / 375) * c * t ^ 3 + (829 / 16875) * c * t ^ 5 + (-232981 / 337500) * c * t ^ 7 + (1199 / 225000) * c * t ^ 9 + (23681 / 168750) * c * t ^ 11 + (81523 / 2025000) * c * t ^ 13 + (-1168 / 16875) * c ^ 2 * t ^ 7 + (1168 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((3904 / 5625) * t ^ 5 + (-1768 / 5625) * t ^ 7 + (-2336 / 5625) * t ^ 9 + (8 / 225) * t ^ 11 + (392 / 375) * alpha * t ^ 3 + (829 / 16875) * alpha * t ^ 5 + (-134707 / 168750) * alpha * t ^ 7 + (32 / 28125) * alpha * t ^ 9 + (19009 / 168750) * alpha * t ^ 11 + (-1136 / 253125) * alpha * t ^ 13) * c_sq
theorem v26_24 (t : ℂ) : (momentPoly 26 z26 2 4).eval t = ((591997 / 6) * t ^ 2 + (-13296057 / 100) * t ^ 4 + (19280931083 / 240000) * t ^ 6 + (-10621631389 / 240000) * t ^ 8 + (9369901 / 768) * t ^ 10 + (476752733 / 1440000) * t ^ 12 + (238360867 / 360000) * t ^ 14 + (29751523 / 160000) * t ^ 18 + (20539451 / 480000) * t ^ 20 + (-128) * c * t ^ 4 + (35681 / 150) * c * t ^ 6 + (-164557 / 1500) * c * t ^ 8 + (-358283 / 4500) * c * t ^ 10 + (67483 / 4500) * c * t ^ 12 + (901387 / 13500) * c * t ^ 14 + (-10066 / 3375) * c * t ^ 18 + (2 / 3) * c * t ^ 20 + (536842 / 15) * alpha * t ^ 2 + (-34073) * alpha * t ^ 4 + (-1014474749 / 36000) * alpha * t ^ 6 + (1030961423 / 36000) * alpha * t ^ 8 + (35661521 / 72000) * alpha * t ^ 10 + (-586015019 / 216000) * alpha * t ^ 12 + (-368149 / 6000) * alpha * t ^ 14 + (-23113 / 24000) * alpha * t ^ 18 + (22814993 / 216000) * alpha * t ^ 20 + (-58832 / 45) * alpha * c * t ^ 2 + (30786 / 25) * alpha * c * t ^ 4 + (304847 / 1000) * alpha * c * t ^ 6 + (-681791 / 3000) * alpha * c * t ^ 8 + (-152263 / 720) * alpha * c * t ^ 10 + (13611649 / 108000) * alpha * c * t ^ 12 + (-623473 / 10800) * alpha * c * t ^ 14 + (41351 / 13500) * alpha * c * t ^ 18 + (-45997 / 108000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_01, v25_02, v25_03, v25_04, v25_10, v25_11, v25_12, v25_13, v25_14, v25_20, v25_21, v25_22, v25_23, v25_24]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04, phase22_10, phase22_11, phase22_12, phase22_13, phase22_14, phase22_20, phase22_21, phase22_22, phase22_23, phase22_24]
  try simp only [star_one, star_neg]
  linear_combination ((58832 / 225) * t ^ 2 + (-713992 / 1875) * t ^ 4 + (9492001 / 225000) * t ^ 6 + (44660021 / 450000) * t ^ 8 + (-32561147 / 450000) * t ^ 10 + (288841 / 10800) * t ^ 12 + (121607 / 10800) * t ^ 14 + (33781 / 112500) * t ^ 18 + (-439852 / 84375) * c * t ^ 6 + (51967 / 3125) * c * t ^ 8 + (-689102 / 84375) * c * t ^ 10 + (-6617 / 3375) * c * t ^ 12 + (-75304 / 50625) * c * t ^ 14 + (12316 / 50625) * c * t ^ 18 + (-2 / 45) * c * t ^ 20 + (-32092 / 1265625) * c ^ 2 * t ^ 8 + (16466 / 421875) * c ^ 2 * t ^ 10 + (-2392 / 140625) * c ^ 2 * t ^ 12 + (-44834 / 1265625) * c ^ 2 * t ^ 14 + (-2336 / 1265625) * c ^ 2 * t ^ 18 + (-4672 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((58832 / 225) * t ^ 2 + (-887168 / 1875) * t ^ 4 + (14079257 / 37500) * t ^ 6 + (-134586481 / 843750) * t ^ 8 + (12653059 / 375000) * t ^ 10 + (-6015439 / 843750) * t ^ 12 + (599164 / 421875) * t ^ 14 + (1102843 / 3375000) * t ^ 18 + (4672 / 1265625) * t ^ 20 + (37376 / 375) * alpha * t ^ 4 + (-14913964 / 84375) * alpha * t ^ 6 + (810568 / 9375) * alpha * t ^ 8 + (-856276 / 84375) * alpha * t ^ 10 + (-4736 / 253125) * alpha * t ^ 12 + (161056 / 253125) * alpha * t ^ 14 + (40264 / 253125) * alpha * t ^ 18) * c_sq
theorem v26_30 (t : ℂ) : (momentPoly 26 z26 3 0).eval t = ((-63 / 5) * t ^ 3 + (58 / 5) * t ^ 5 + 1 * t ^ 9 + (679 / 300) * c * t ^ 3 + (-2951 / 300) * c * t ^ 5 + (-71 / 225) * c * t ^ 9 + (-6991 / 600) * alpha * t ^ 3 + (-10757 / 1200) * alpha * t ^ 5 + (-14183 / 3600) * alpha * t ^ 9 + (73 / 15) * alpha * c * t ^ 3 + (-73 / 15) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_10, v25_20, v25_30]
  try simp only [phase22_00, phase22_10, phase22_20, phase22_30]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-8 / 375) * c * t ^ 3 + (-16 / 1125) * c * t ^ 5) * alpha_sq + ((-8 / 375) * alpha * t ^ 3 + (-16 / 1125) * alpha * t ^ 5) * c_sq
theorem v26_31 (t : ℂ) : (momentPoly 26 z26 3 1).eval t = ((4025 / 4) * t ^ 2 + (-175301 / 600) * t ^ 4 + (-48849 / 400) * t ^ 6 + (19649 / 1200) * t ^ 10 + (-2 / 3) * c * t ^ 4 + 1 * c * t ^ 6 + (-1 / 3) * c * t ^ 10 + (-365) * alpha * t ^ 2 + (5339 / 15) * alpha * t ^ 4 + (68 / 5) * alpha * t ^ 6 + (-68 / 15) * alpha * t ^ 10 + (40 / 3) * alpha * c * t ^ 2 + (-8611 / 1800) * alpha * c * t ^ 4 + (-1663 / 400) * alpha * c * t ^ 6 + (4189 / 3600) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_01, v25_10, v25_11, v25_20, v25_21, v25_30, v25_31]
  try simp only [phase22_00, phase22_01, phase22_10, phase22_11, phase22_20, phase22_21, phase22_30, phase22_31]
  try simp only [star_one, star_neg]
  linear_combination ((8 / 3) * t ^ 2 + (-89249 / 45000) * t ^ 4 + (-3653 / 10000) * t ^ 6 + (-81523 / 270000) * t ^ 10) * alpha_sq + ((8 / 3) * t ^ 2 + (-13862 / 5625) * t ^ 4 + (598 / 625) * t ^ 6 + (568 / 16875) * t ^ 10 + (-584 / 1125) * alpha * t ^ 4 + (584 / 1125) * alpha * t ^ 6) * c_sq
theorem v26_32 (t : ℂ) : (momentPoly 26 z26 3 2).eval t = ((3577 / 5) * t ^ 3 + (-2458367 / 3000) * t ^ 5 + (244423 / 1200) * t ^ 7 + (-802181 / 6000) * t ^ 9 + (1452059 / 18000) * t ^ 11 + (-838859 / 18000) * t ^ 13 + (-3826 / 3) * c * t + (35329 / 20) * c * t ^ 3 + (-6026107 / 6000) * c * t ^ 5 + (90551 / 200) * c * t ^ 7 + (-867493 / 6000) * c * t ^ 9 + (1643 / 4500) * c * t ^ 11 + (-32731 / 9000) * c * t ^ 13 + (-3826 / 3) * alpha * t + (23471 / 20) * alpha * t ^ 3 + (-1282273 / 12000) * alpha * t ^ 5 + (185513 / 1600) * alpha * t ^ 7 + (-823369 / 24000) * alpha * t ^ 9 + (-2657089 / 72000) * alpha * t ^ 11 + (-3198851 / 72000) * alpha * t ^ 13 + (3577 / 15) * alpha * c * t ^ 3 + (-435407 / 1125) * alpha * c * t ^ 5 + (1318 / 9) * alpha * c * t ^ 7 + (-1018 / 1125) * alpha * c * t ^ 9 + (5167 / 3375) * alpha * c * t ^ 11 + (5033 / 3375) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_01, v25_02, v25_10, v25_11, v25_12, v25_20, v25_21, v25_22, v25_30, v25_31, v25_32]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_10, phase22_11, phase22_12, phase22_20, phase22_21, phase22_22, phase22_30, phase22_31, phase22_32]
  try simp only [star_one, star_neg]
  linear_combination ((-3577 / 75) * t ^ 3 + (1551 / 25) * t ^ 5 + (-206 / 15) * t ^ 7 + (-26483 / 16875) * t ^ 11 + (16133 / 16875) * t ^ 13 + (392 / 375) * c * t ^ 3 + (829 / 16875) * c * t ^ 5 + (-232981 / 337500) * c * t ^ 7 + (1199 / 225000) * c * t ^ 9 + (23681 / 168750) * c * t ^ 11 + (81523 / 2025000) * c * t ^ 13 + (-1168 / 16875) * c ^ 2 * t ^ 7 + (1168 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((3904 / 5625) * t ^ 5 + (-1768 / 5625) * t ^ 7 + (-2336 / 5625) * t ^ 9 + (8 / 225) * t ^ 11 + (-392 / 375) * alpha * t ^ 3 + (-829 / 16875) * alpha * t ^ 5 + (134707 / 168750) * alpha * t ^ 7 + (-32 / 28125) * alpha * t ^ 9 + (-19009 / 168750) * alpha * t ^ 11 + (1136 / 253125) * alpha * t ^ 13) * c_sq
theorem v26_33 (t : ℂ) : (momentPoly 26 z26 3 3).eval t = (99476 + (-11031) * t ^ 2 + (-10064421 / 50) * t ^ 4 + (6181551539 / 40000) * t ^ 6 + (-837480527 / 40000) * t ^ 8 + (-838419789 / 160000) * t ^ 10 + (-67551253 / 120000) * t ^ 12 + (50082043 / 80000) * t ^ 14 + (20961577 / 480000) * t ^ 18 + (-28032 / 25) * c * t ^ 4 + (2224823 / 1500) * c * t ^ 6 + (-9101 / 200) * c * t ^ 8 + (-281817 / 1000) * c * t ^ 10 + (-1028171 / 9000) * c * t ^ 12 + (80259 / 1000) * c * t ^ 14 + (-142 / 225) * c * t ^ 18) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_01, v25_02, v25_03, v25_10, v25_11, v25_12, v25_13, v25_20, v25_21, v25_22, v25_23, v25_30, v25_31, v25_32, v25_33]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_10, phase22_11, phase22_12, phase22_13, phase22_20, phase22_21, phase22_22, phase22_23, phase22_30, phase22_31, phase22_32, phase22_33]
  try simp only [star_one, star_neg]
  linear_combination ((-29416 / 75) * t ^ 2 + (57504 / 125) * t ^ 4 + (-12644543 / 150000) * t ^ 6 + (444609 / 100000) * t ^ 8 + (10367 / 60000) * t ^ 10 + (-94734947 / 13500000) * t ^ 12 + (-8562699 / 500000) * t ^ 14 + (-14890759 / 10125000) * t ^ 18 + (9344 / 125) * c * t ^ 4 + (-3085628 / 28125) * c * t ^ 6 + (800036 / 28125) * c * t ^ 8 + (49564 / 9375) * c * t ^ 10 + (2288 / 1125) * c * t ^ 12 + (-908 / 1125) * c * t ^ 14 + (-2336 / 5625) * c ^ 2 * t ^ 6 + (10342 / 84375) * c ^ 2 * t ^ 8 + (661 / 3125) * c ^ 2 * t ^ 10 + (-1343 / 28125) * c ^ 2 * t ^ 14) * alpha_sq + ((29416 / 75) * t ^ 2 + (-80736 / 125) * t ^ 4 + (7442963 / 18750) * t ^ 6 + (-4236286 / 28125) * t ^ 8 + (748931 / 18750) * t ^ 10 + (-549599 / 421875) * t ^ 12 + (32782 / 15625) * t ^ 14 + (40328 / 1265625) * t ^ 18) * c_sq
theorem v26_34 (t : ℂ) : (momentPoly 26 z26 3 4).eval t = ((515526 / 5) * t ^ 3 + (-66260949 / 500) * t ^ 5 + (10110524491 / 300000) * t ^ 7 + (-19646737231 / 300000) * t ^ 9 + (16892431069 / 200000) * t ^ 11 + (-928459627 / 45000) * t ^ 13 + (39688397 / 75000) * t ^ 15 + (-6328503721 / 1800000) * t ^ 17 + (968846963 / 5400000) * t ^ 19 + (106245497 / 900000) * t ^ 21 + (343141531 / 5400000) * t ^ 25 + (-375251 / 3) * c * t + (2545851 / 10) * c * t ^ 3 + (-215379479 / 1000) * c * t ^ 5 + (169107541313 / 1200000) * c * t ^ 7 + (-34535050561 / 400000) * c * t ^ 9 + (23583392577 / 800000) * c * t ^ 11 + (-6133365673 / 1440000) * c * t ^ 13 + (606938317 / 600000) * c * t ^ 15 + (-88814807 / 1800000) * c * t ^ 17 + (-523779947 / 7200000) * c * t ^ 19 + (-151133273 / 7200000) * c * t ^ 21 + (-7300291 / 1800000) * c * t ^ 25 + (375251 / 3) * alpha * t + (-1691349 / 10) * alpha * t ^ 3 + (87945931 / 2000) * alpha * t ^ 5 + (-27421539491 / 800000) * alpha * t ^ 7 + (211671468601 / 4800000) * alpha * t ^ 9 + (-29962039741 / 4800000) * alpha * t ^ 11 + (47198066359 / 5760000) * alpha * t ^ 13 + (-1114475627 / 200000) * alpha * t ^ 15 + (-16399839659 / 28800000) * alpha * t ^ 17 + (-4709217563 / 14400000) * alpha * t ^ 19 + (402076021 / 28800000) * alpha * t ^ 21 + (-101853403 / 3200000) * alpha * t ^ 25 + (-171842 / 5) * alpha * c * t ^ 3 + (28607683 / 375) * alpha * c * t ^ 5 + (-46748083067 / 900000) * alpha * c * t ^ 7 + (3604390699 / 300000) * alpha * c * t ^ 9 + (-2536462243 / 600000) * alpha * c * t ^ 11 + (1854327031 / 1080000) * alpha * c * t ^ 13 + (21579543 / 50000) * alpha * c * t ^ 15 + (36374917 / 337500) * alpha * c * t ^ 17 + (1277285179 / 16200000) * alpha * c * t ^ 19 + (-525544873 / 5400000) * alpha * c * t ^ 21 + (-379243 / 253125) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_01, v25_02, v25_03, v25_04, v25_10, v25_11, v25_12, v25_13, v25_14, v25_20, v25_21, v25_22, v25_23, v25_24, v25_30, v25_31, v25_32, v25_33, v25_34]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04, phase22_10, phase22_11, phase22_12, phase22_13, phase22_14, phase22_20, phase22_21, phase22_22, phase22_23, phase22_24, phase22_30, phase22_31, phase22_32, phase22_33, phase22_34]
  try simp only [star_one, star_neg]
  linear_combination ((-171842 / 25) * t ^ 3 + (819323 / 75) * t ^ 5 + (-9935562619 / 4500000) * t ^ 7 + (-551411297 / 300000) * t ^ 9 + (-1426502501 / 1800000) * t ^ 11 + (22241035747 / 27000000) * t ^ 13 + (-183026077 / 2250000) * t ^ 15 + (2013973 / 33750) * t ^ 17 + (486552379 / 81000000) * t ^ 19 + (-523346473 / 27000000) * t ^ 21 + (-1112293 / 1265625) * t ^ 25 + (18832 / 125) * c * t ^ 3 + (-462154 / 5625) * c * t ^ 5 + (-234767279 / 1687500) * c * t ^ 7 + (4045783 / 45000) * c * t ^ 9 + (7640777 / 750000) * c * t ^ 11 + (-420415043 / 33750000) * c * t ^ 13 + (14535359 / 11250000) * c * t ^ 15 + (84377623 / 33750000) * c * t ^ 17 + (18526943 / 16875000) * c * t ^ 19 + (301343 / 5625000) * c * t ^ 21 + (5951179 / 75937500) * c * t ^ 25 + (-334048 / 16875) * c ^ 2 * t ^ 7 + (14855564 / 421875) * c ^ 2 * t ^ 9 + (-7275688 / 421875) * c ^ 2 * t ^ 11 + (168932 / 84375) * c ^ 2 * t ^ 13 + (-11024 / 140625) * c ^ 2 * t ^ 15 + (-80528 / 1265625) * c ^ 2 * t ^ 17 + (-85264 / 1265625) * c ^ 2 * t ^ 19 + (8 / 225) * c ^ 2 * t ^ 21) * alpha_sq + ((366976 / 1875) * t ^ 5 + (-28463686 / 140625) * t ^ 7 + (-18529859 / 140625) * t ^ 9 + (21362561 / 140625) * t ^ 11 + (5094493 / 421875) * t ^ 13 + (-3734839 / 140625) * t ^ 15 + (163456 / 421875) * t ^ 17 + (71984 / 84375) * t ^ 19 + (-16 / 75) * t ^ 21 + (18832 / 125) * alpha * t ^ 3 + (-462154 / 5625) * alpha * t ^ 5 + (-286866469 / 1687500) * alpha * t ^ 7 + (59797513 / 562500) * alpha * t ^ 9 + (5630477 / 375000) * alpha * t ^ 11 + (-113946994 / 6328125) * alpha * t ^ 13 + (26602261 / 2812500) * alpha * t ^ 15 + (552058 / 2109375) * alpha * t ^ 17 + (-8787677 / 16875000) * alpha * t ^ 19 + (337079 / 2812500) * alpha * t ^ 21 + (165856 / 18984375) * alpha * t ^ 25) * c_sq
theorem v26_40 (t : ℂ) : (momentPoly 26 z26 4 0).eval t = ((-1832279 / 2400) * t ^ 4 + (467449 / 400) * t ^ 6 + (520363 / 4800) * t ^ 8 + (125899 / 3600) * t ^ 10 + (6145 / 576) * t ^ 16 + (968 / 75) * c * t ^ 4 + (-192 / 25) * c * t ^ 6 + (-292 / 75) * c * t ^ 8 + (-4 / 3) * c * t ^ 10 + (-275693 / 750) * alpha * t ^ 4 + (8743 / 375) * alpha * t ^ 6 + (83047 / 250) * alpha * t ^ 8 + (18632 / 1125) * alpha * t ^ 10 + (-5033 / 1125) * alpha * t ^ 16 + (7897 / 2250) * alpha * c * t ^ 4 + (-1141 / 1500) * alpha * c * t ^ 6 + (2983 / 1125) * alpha * c * t ^ 8 + (71923 / 13500) * alpha * c * t ^ 10 + (292 / 3375) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_10, v25_20, v25_30, v25_40]
  try simp only [phase22_00, phase22_10, phase22_20, phase22_30, phase22_40]
  try simp only [star_one, star_neg]
  linear_combination ((17369 / 11250) * t ^ 4 + (6079 / 7500) * t ^ 6 + (81523 / 67500) * t ^ 10 + (-1168 / 1125) * c * t ^ 4 + (292 / 375) * c * t ^ 6 + (292 / 1125) * c * t ^ 8 + (32 / 5625) * c ^ 2 * t ^ 6 + (32 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-4988 / 5625) * t ^ 4 + (3524 / 1875) * t ^ 6 + (-32 / 5625) * t ^ 8 + (2272 / 16875) * t ^ 10 + (-1168 / 1125) * alpha * t ^ 4 + (1168 / 1125) * alpha * t ^ 6) * c_sq
theorem v26_41 (t : ℂ) : (momentPoly 26 z26 4 1).eval t = ((-6174 / 5) * t ^ 3 + (430991 / 250) * t ^ 5 + (-184873 / 375) * t ^ 7 + (25289 / 750) * t ^ 9 + (-37532 / 1125) * t ^ 11 + (3908 / 1125) * t ^ 17 + (33271 / 150) * c * t ^ 3 + (-33637037 / 36000) * c * t ^ 5 + (3251759 / 6000) * c * t ^ 7 + (-3670967 / 72000) * c * t ^ 9 + (166117 / 6000) * c * t ^ 11 + (-239551 / 72000) * c * t ^ 17 + (-342559 / 300) * alpha * t ^ 3 + (-11976983 / 36000) * alpha * t ^ 5 + (8257801 / 6000) * alpha * t ^ 7 + (-38884493 / 72000) * alpha * t ^ 9 + (140023 / 6000) * alpha * t ^ 11 + (78731 / 72000) * alpha * t ^ 17 + (7154 / 15) * alpha * c * t ^ 3 + (-1809727 / 2250) * alpha * c * t ^ 5 + (481127 / 1125) * alpha * c * t ^ 7 + (-230161 / 2250) * alpha * c * t ^ 9 + (1768 / 3375) * alpha * c * t ^ 11 + (5033 / 3375) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_01, v25_10, v25_11, v25_20, v25_21, v25_30, v25_31, v25_40, v25_41]
  try simp only [phase22_00, phase22_01, phase22_10, phase22_11, phase22_20, phase22_21, phase22_30, phase22_31, phase22_40, phase22_41]
  try simp only [star_one, star_neg]
  linear_combination ((7154 / 75) * t ^ 3 + (-300133 / 2250) * t ^ 5 + (88337 / 5625) * t ^ 7 + (9113 / 450) * t ^ 9 + (39632 / 16875) * t ^ 11 + (-5033 / 16875) * t ^ 17 + (-784 / 375) * c * t ^ 3 + (7756 / 84375) * c * t ^ 5 + (11164 / 9375) * c * t ^ 7 + (4808 / 28125) * c * t ^ 9 + (2272 / 84375) * c * t ^ 11 + (2336 / 253125) * c * t ^ 17 + (1168 / 16875) * c ^ 2 * t ^ 7 + (-1168 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((-1904 / 5625) * t ^ 5 + (-1232 / 5625) * t ^ 7 + (2336 / 5625) * t ^ 9 + (32 / 225) * t ^ 11 + (-784 / 375) * alpha * t ^ 3 + (-2704 / 9375) * alpha * t ^ 5 + (18266 / 9375) * alpha * t ^ 7 + (-7208 / 28125) * alpha * t ^ 9 + (-42562 / 84375) * alpha * t ^ 11 + (-2336 / 253125) * alpha * t ^ 17) * c_sq
theorem v26_42 (t : ℂ) : (momentPoly 26 z26 4 2).eval t = ((591997 / 6) * t ^ 2 + (-13296057 / 100) * t ^ 4 + (19280931083 / 240000) * t ^ 6 + (-10621631389 / 240000) * t ^ 8 + (9369901 / 768) * t ^ 10 + (476752733 / 1440000) * t ^ 12 + (238360867 / 360000) * t ^ 14 + (29751523 / 160000) * t ^ 18 + (20539451 / 480000) * t ^ 20 + (-128) * c * t ^ 4 + (35681 / 150) * c * t ^ 6 + (-164557 / 1500) * c * t ^ 8 + (-358283 / 4500) * c * t ^ 10 + (67483 / 4500) * c * t ^ 12 + (901387 / 13500) * c * t ^ 14 + (-10066 / 3375) * c * t ^ 18 + (2 / 3) * c * t ^ 20 + (-536842 / 15) * alpha * t ^ 2 + 34073 * alpha * t ^ 4 + (1014474749 / 36000) * alpha * t ^ 6 + (-1030961423 / 36000) * alpha * t ^ 8 + (-35661521 / 72000) * alpha * t ^ 10 + (586015019 / 216000) * alpha * t ^ 12 + (368149 / 6000) * alpha * t ^ 14 + (23113 / 24000) * alpha * t ^ 18 + (-22814993 / 216000) * alpha * t ^ 20 + (58832 / 45) * alpha * c * t ^ 2 + (-30786 / 25) * alpha * c * t ^ 4 + (-304847 / 1000) * alpha * c * t ^ 6 + (681791 / 3000) * alpha * c * t ^ 8 + (152263 / 720) * alpha * c * t ^ 10 + (-13611649 / 108000) * alpha * c * t ^ 12 + (623473 / 10800) * alpha * c * t ^ 14 + (-41351 / 13500) * alpha * c * t ^ 18 + (45997 / 108000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_01, v25_02, v25_10, v25_11, v25_12, v25_20, v25_21, v25_22, v25_30, v25_31, v25_32, v25_40, v25_41, v25_42]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_10, phase22_11, phase22_12, phase22_20, phase22_21, phase22_22, phase22_30, phase22_31, phase22_32, phase22_40, phase22_41, phase22_42]
  try simp only [star_one, star_neg]
  linear_combination ((58832 / 225) * t ^ 2 + (-713992 / 1875) * t ^ 4 + (9492001 / 225000) * t ^ 6 + (44660021 / 450000) * t ^ 8 + (-32561147 / 450000) * t ^ 10 + (288841 / 10800) * t ^ 12 + (121607 / 10800) * t ^ 14 + (33781 / 112500) * t ^ 18 + (-439852 / 84375) * c * t ^ 6 + (51967 / 3125) * c * t ^ 8 + (-689102 / 84375) * c * t ^ 10 + (-6617 / 3375) * c * t ^ 12 + (-75304 / 50625) * c * t ^ 14 + (12316 / 50625) * c * t ^ 18 + (-2 / 45) * c * t ^ 20 + (-32092 / 1265625) * c ^ 2 * t ^ 8 + (16466 / 421875) * c ^ 2 * t ^ 10 + (-2392 / 140625) * c ^ 2 * t ^ 12 + (-44834 / 1265625) * c ^ 2 * t ^ 14 + (-2336 / 1265625) * c ^ 2 * t ^ 18 + (-4672 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((58832 / 225) * t ^ 2 + (-887168 / 1875) * t ^ 4 + (14079257 / 37500) * t ^ 6 + (-134586481 / 843750) * t ^ 8 + (12653059 / 375000) * t ^ 10 + (-6015439 / 843750) * t ^ 12 + (599164 / 421875) * t ^ 14 + (1102843 / 3375000) * t ^ 18 + (4672 / 1265625) * t ^ 20 + (-37376 / 375) * alpha * t ^ 4 + (14913964 / 84375) * alpha * t ^ 6 + (-810568 / 9375) * alpha * t ^ 8 + (856276 / 84375) * alpha * t ^ 10 + (4736 / 253125) * alpha * t ^ 12 + (-161056 / 253125) * alpha * t ^ 14 + (-40264 / 253125) * alpha * t ^ 18) * c_sq
theorem v26_43 (t : ℂ) : (momentPoly 26 z26 4 3).eval t = ((515526 / 5) * t ^ 3 + (-66260949 / 500) * t ^ 5 + (10110524491 / 300000) * t ^ 7 + (-19646737231 / 300000) * t ^ 9 + (16892431069 / 200000) * t ^ 11 + (-928459627 / 45000) * t ^ 13 + (39688397 / 75000) * t ^ 15 + (-6328503721 / 1800000) * t ^ 17 + (968846963 / 5400000) * t ^ 19 + (106245497 / 900000) * t ^ 21 + (343141531 / 5400000) * t ^ 25 + (-375251 / 3) * c * t + (2545851 / 10) * c * t ^ 3 + (-215379479 / 1000) * c * t ^ 5 + (169107541313 / 1200000) * c * t ^ 7 + (-34535050561 / 400000) * c * t ^ 9 + (23583392577 / 800000) * c * t ^ 11 + (-6133365673 / 1440000) * c * t ^ 13 + (606938317 / 600000) * c * t ^ 15 + (-88814807 / 1800000) * c * t ^ 17 + (-523779947 / 7200000) * c * t ^ 19 + (-151133273 / 7200000) * c * t ^ 21 + (-7300291 / 1800000) * c * t ^ 25 + (-375251 / 3) * alpha * t + (1691349 / 10) * alpha * t ^ 3 + (-87945931 / 2000) * alpha * t ^ 5 + (27421539491 / 800000) * alpha * t ^ 7 + (-211671468601 / 4800000) * alpha * t ^ 9 + (29962039741 / 4800000) * alpha * t ^ 11 + (-47198066359 / 5760000) * alpha * t ^ 13 + (1114475627 / 200000) * alpha * t ^ 15 + (16399839659 / 28800000) * alpha * t ^ 17 + (4709217563 / 14400000) * alpha * t ^ 19 + (-402076021 / 28800000) * alpha * t ^ 21 + (101853403 / 3200000) * alpha * t ^ 25 + (171842 / 5) * alpha * c * t ^ 3 + (-28607683 / 375) * alpha * c * t ^ 5 + (46748083067 / 900000) * alpha * c * t ^ 7 + (-3604390699 / 300000) * alpha * c * t ^ 9 + (2536462243 / 600000) * alpha * c * t ^ 11 + (-1854327031 / 1080000) * alpha * c * t ^ 13 + (-21579543 / 50000) * alpha * c * t ^ 15 + (-36374917 / 337500) * alpha * c * t ^ 17 + (-1277285179 / 16200000) * alpha * c * t ^ 19 + (525544873 / 5400000) * alpha * c * t ^ 21 + (379243 / 253125) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_01, v25_02, v25_03, v25_10, v25_11, v25_12, v25_13, v25_20, v25_21, v25_22, v25_23, v25_30, v25_31, v25_32, v25_33, v25_40, v25_41, v25_42, v25_43]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_10, phase22_11, phase22_12, phase22_13, phase22_20, phase22_21, phase22_22, phase22_23, phase22_30, phase22_31, phase22_32, phase22_33, phase22_40, phase22_41, phase22_42, phase22_43]
  try simp only [star_one, star_neg]
  linear_combination ((-171842 / 25) * t ^ 3 + (819323 / 75) * t ^ 5 + (-9935562619 / 4500000) * t ^ 7 + (-551411297 / 300000) * t ^ 9 + (-1426502501 / 1800000) * t ^ 11 + (22241035747 / 27000000) * t ^ 13 + (-183026077 / 2250000) * t ^ 15 + (2013973 / 33750) * t ^ 17 + (486552379 / 81000000) * t ^ 19 + (-523346473 / 27000000) * t ^ 21 + (-1112293 / 1265625) * t ^ 25 + (18832 / 125) * c * t ^ 3 + (-462154 / 5625) * c * t ^ 5 + (-234767279 / 1687500) * c * t ^ 7 + (4045783 / 45000) * c * t ^ 9 + (7640777 / 750000) * c * t ^ 11 + (-420415043 / 33750000) * c * t ^ 13 + (14535359 / 11250000) * c * t ^ 15 + (84377623 / 33750000) * c * t ^ 17 + (18526943 / 16875000) * c * t ^ 19 + (301343 / 5625000) * c * t ^ 21 + (5951179 / 75937500) * c * t ^ 25 + (-334048 / 16875) * c ^ 2 * t ^ 7 + (14855564 / 421875) * c ^ 2 * t ^ 9 + (-7275688 / 421875) * c ^ 2 * t ^ 11 + (168932 / 84375) * c ^ 2 * t ^ 13 + (-11024 / 140625) * c ^ 2 * t ^ 15 + (-80528 / 1265625) * c ^ 2 * t ^ 17 + (-85264 / 1265625) * c ^ 2 * t ^ 19 + (8 / 225) * c ^ 2 * t ^ 21) * alpha_sq + ((366976 / 1875) * t ^ 5 + (-28463686 / 140625) * t ^ 7 + (-18529859 / 140625) * t ^ 9 + (21362561 / 140625) * t ^ 11 + (5094493 / 421875) * t ^ 13 + (-3734839 / 140625) * t ^ 15 + (163456 / 421875) * t ^ 17 + (71984 / 84375) * t ^ 19 + (-16 / 75) * t ^ 21 + (-18832 / 125) * alpha * t ^ 3 + (462154 / 5625) * alpha * t ^ 5 + (286866469 / 1687500) * alpha * t ^ 7 + (-59797513 / 562500) * alpha * t ^ 9 + (-5630477 / 375000) * alpha * t ^ 11 + (113946994 / 6328125) * alpha * t ^ 13 + (-26602261 / 2812500) * alpha * t ^ 15 + (-552058 / 2109375) * alpha * t ^ 17 + (8787677 / 16875000) * alpha * t ^ 19 + (-337079 / 2812500) * alpha * t ^ 21 + (-165856 / 18984375) * alpha * t ^ 25) * c_sq
theorem v26_44 (t : ℂ) : (momentPoly 26 z26 4 4).eval t = (9756526 + (-1413944) * t ^ 2 + (-947173843 / 25) * t ^ 4 + (63068035161 / 1250) * t ^ 6 + (-443305655650783 / 16000000) * t ^ 8 + (39500444049603 / 4000000) * t ^ 10 + (-10491411963061 / 3200000) * t ^ 12 + (17921140184593 / 24000000) * t ^ 14 + (-129002727019279 / 576000000) * t ^ 16 + (5033066639051 / 72000000) * t ^ 18 + (-6564213168059 / 432000000) * t ^ 20 + (497399755667 / 24000000) * t ^ 22 + (-2385978784471 / 288000000) * t ^ 24 + (124035392249 / 216000000) * t ^ 26 + (264114765571 / 1728000000) * t ^ 32 + (-15828736 / 75) * c * t ^ 4 + (148032796 / 375) * c * t ^ 6 + (-5877042766 / 46875) * c * t ^ 8 + (-50500435877 / 562500) * c * t ^ 10 + (-1769023 / 1875) * c * t ^ 12 + (83350125829 / 1687500) * c * t ^ 14 + (-89031178241 / 3375000) * c * t ^ 16 + (31515148057 / 3375000) * c * t ^ 18 + (3427340563 / 5062500) * c * t ^ 20 + (-200703421 / 421875) * c * t ^ 22 + (2950909 / 1125000) * c * t ^ 24 + (-532610669 / 3375000) * c * t ^ 26 + (-2939272 / 1265625) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z26, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v25_00, v25_01, v25_02, v25_03, v25_04, v25_10, v25_11, v25_12, v25_13, v25_14, v25_20, v25_21, v25_22, v25_23, v25_24, v25_30, v25_31, v25_32, v25_33, v25_34, v25_40, v25_41, v25_42, v25_43, v25_44]
  try simp only [phase22_00, phase22_01, phase22_02, phase22_03, phase22_04, phase22_10, phase22_11, phase22_12, phase22_13, phase22_14, phase22_20, phase22_21, phase22_22, phase22_23, phase22_24, phase22_30, phase22_31, phase22_32, phase22_33, phase22_34, phase22_40, phase22_41, phase22_42, phase22_43, phase22_44]
  try simp only [star_one, star_neg]
  linear_combination ((-11311552 / 225) * t ^ 2 + (32470592 / 375) * t ^ 4 + (-369721889 / 9375) * t ^ 6 + (673573201 / 60000) * t ^ 8 + (-82655750533 / 9000000) * t ^ 10 + (31031740369 / 27000000) * t ^ 12 + (-1579658832787 / 270000000) * t ^ 14 + (20340407891 / 4218750) * t ^ 16 + (-419689736971 / 810000000) * t ^ 18 + (309348279 / 1000000) * t ^ 20 + (-39227849 / 54000000) * t ^ 22 + (1011901603 / 54000000) * t ^ 26 + (15828736 / 1125) * c * t ^ 4 + (-852256504 / 28125) * c * t ^ 6 + (14349439817 / 703125) * c * t ^ 8 + (-51451659433 / 8437500) * c * t ^ 10 + (5678999149 / 1687500) * c * t ^ 12 + (-23928052811 / 16875000) * c * t ^ 14 + (7040829101 / 50625000) * c * t ^ 16 + (-2234848201 / 12656250) * c * t ^ 18 + (-1136201219 / 37968750) * c * t ^ 20 + (2049779963 / 50625000) * c * t ^ 22 + (-2950909 / 16875000) * c * t ^ 24 + (12224288 / 6328125) * c * t ^ 26 + (2939272 / 18984375) * c * t ^ 32 + (-89152 / 1125) * c ^ 2 * t ^ 6 + (3594688 / 50625) * c ^ 2 * t ^ 8 + (34451522 / 703125) * c ^ 2 * t ^ 10 + (-5690632 / 140625) * c ^ 2 * t ^ 12 + (-27996563 / 2109375) * c ^ 2 * t ^ 14 + (2936099 / 234375) * c ^ 2 * t ^ 16 + (-3037514 / 703125) * c ^ 2 * t ^ 18 + (-9370864 / 94921875) * c ^ 2 * t ^ 20 + (4351639 / 10546875) * c ^ 2 * t ^ 22 + (-3125317 / 31640625) * c ^ 2 * t ^ 24 + (-13091528 / 94921875) * c ^ 2 * t ^ 26 + (-682112 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((11311552 / 225) * t ^ 2 + (-45588928 / 375) * t ^ 4 + (377776784 / 3125) * t ^ 6 + (-657199852523 / 8437500) * t ^ 8 + (113044559279 / 2812500) * t ^ 10 + (-1701750533 / 135000) * t ^ 12 + (12991059587 / 5625000) * t ^ 14 + (-26476409 / 33750) * t ^ 16 + (242601209 / 6328125) * t ^ 18 + (1792403357 / 253125000) * t ^ 20 + (17930209 / 84375000) * t ^ 22 + (3125317 / 10546875) * t ^ 24 + (101831213 / 31640625) * t ^ 26 + (682112 / 94921875) * t ^ 32) * c_sq
#print axioms v26_00
#print axioms v26_11
#print axioms v26_22
#print axioms v26_33
#print axioms v26_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
theorem site27 : ((r ^ 2 * thetaMinus) : ℂ) = ((1 / 15) * c + (-1 / 15) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 40) * c + (1 / 40) * alpha + (-1 / 120) * alpha * c + (1 / 120) * alpha ^ 2) * alpha_sq
theorem phase27_00 : ((r ^ 2 * thetaMinus) : ℂ) ^ 0 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 0 = (1) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase27_01 : ((r ^ 2 * thetaMinus) : ℂ) ^ 0 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 1 = ((1 / 15) * c + (1 / 15) * alpha) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase27_02 : ((r ^ 2 * thetaMinus) : ℂ) ^ 0 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 2 = ((73 / 75) + (2 / 225) * alpha * c) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 225)) * alpha_sq + ((1 / 225)) * c_sq
theorem phase27_03 : ((r ^ 2 * thetaMinus) : ℂ) ^ 0 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 3 = ((71 / 1125) * c + (221 / 1125) * alpha) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 1125) * c + (1 / 3375) * alpha) * alpha_sq + ((1 / 3375) * c + (1 / 1125) * alpha) * c_sq
theorem phase27_04 : ((r ^ 2 * thetaMinus) : ℂ) ^ 0 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 4 = ((5033 / 5625) + (292 / 16875) * alpha * c) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 16875) + (2 / 16875) * c ^ 2 + (4 / 50625) * alpha * c + (1 / 50625) * alpha ^ 2) * alpha_sq + ((68 / 16875) + (1 / 50625) * c ^ 2 + (4 / 50625) * alpha * c) * c_sq
theorem phase27_10 : ((r ^ 2 * thetaMinus) : ℂ) ^ 1 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 0 = ((1 / 15) * c + (-1 / 15) * alpha) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase27_11 : ((r ^ 2 * thetaMinus) : ℂ) ^ 1 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 1 = (1) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 225)) * alpha_sq + ((1 / 225)) * c_sq
theorem phase27_12 : ((r ^ 2 * thetaMinus) : ℂ) ^ 1 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 2 = ((1 / 15) * c + (1 / 15) * alpha) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 3375) * c + (-1 / 3375) * alpha) * alpha_sq + ((1 / 3375) * c + (1 / 3375) * alpha) * c_sq
theorem phase27_13 : ((r ^ 2 * thetaMinus) : ℂ) ^ 1 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 3 = ((73 / 75) + (2 / 225) * alpha * c) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 16875) + (-2 / 50625) * alpha * c + (-1 / 50625) * alpha ^ 2) * alpha_sq + ((74 / 16875) + (1 / 50625) * c ^ 2 + (2 / 50625) * alpha * c) * c_sq
theorem phase27_14 : ((r ^ 2 * thetaMinus) : ℂ) ^ 1 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 4 = ((71 / 1125) * c + (221 / 1125) * alpha) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 84375) * c + (2 / 759375) * c ^ 3 + (1 / 253125) * alpha + (-2 / 759375) * alpha * c ^ 2 + (-1 / 253125) * alpha ^ 2 * c + (-1 / 759375) * alpha ^ 3) * alpha_sq + ((8 / 28125) * c + (1 / 759375) * c ^ 3 + (224 / 253125) * alpha + (1 / 253125) * alpha * c ^ 2) * c_sq
theorem phase27_20 : ((r ^ 2 * thetaMinus) : ℂ) ^ 2 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 0 = ((73 / 75) + (-2 / 225) * alpha * c) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 225)) * alpha_sq + ((1 / 225)) * c_sq
theorem phase27_21 : ((r ^ 2 * thetaMinus) : ℂ) ^ 2 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 1 = ((1 / 15) * c + (-1 / 15) * alpha) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 3375) * c + (1 / 3375) * alpha) * alpha_sq + ((1 / 3375) * c + (-1 / 3375) * alpha) * c_sq
theorem phase27_22 : ((r ^ 2 * thetaMinus) : ℂ) ^ 2 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 2 = (1) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 16875) + (-2 / 50625) * c ^ 2 + (1 / 50625) * alpha ^ 2) * alpha_sq + ((76 / 16875) + (1 / 50625) * c ^ 2) * c_sq
theorem phase27_23 : ((r ^ 2 * thetaMinus) : ℂ) ^ 2 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 3 = ((1 / 15) * c + (1 / 15) * alpha) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 253125) * c + (-2 / 759375) * c ^ 3 + (-1 / 253125) * alpha + (-2 / 759375) * alpha * c ^ 2 + (1 / 759375) * alpha ^ 2 * c + (1 / 759375) * alpha ^ 3) * alpha_sq + ((76 / 253125) * c + (1 / 759375) * c ^ 3 + (76 / 253125) * alpha + (1 / 759375) * alpha * c ^ 2) * c_sq
theorem phase27_24 : ((r ^ 2 * thetaMinus) : ℂ) ^ 2 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 4 = ((73 / 75) + (2 / 225) * alpha * c) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 1265625) + (1 / 3796875) * c ^ 2 + (-1 / 11390625) * c ^ 4 + (-2 / 3796875) * alpha * c + (-4 / 11390625) * alpha * c ^ 3 + (-1 / 3796875) * alpha ^ 2 + (-1 / 11390625) * alpha ^ 2 * c ^ 2 + (2 / 11390625) * alpha ^ 3 * c + (1 / 11390625) * alpha ^ 4) * alpha_sq + ((5549 / 1265625) + (1 / 50625) * c ^ 2 + (1 / 11390625) * c ^ 4 + (152 / 3796875) * alpha * c + (2 / 11390625) * alpha * c ^ 3) * c_sq
theorem phase27_30 : ((r ^ 2 * thetaMinus) : ℂ) ^ 3 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 0 = ((71 / 1125) * c + (-221 / 1125) * alpha) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 1125) * c + (-1 / 3375) * alpha) * alpha_sq + ((1 / 3375) * c + (-1 / 1125) * alpha) * c_sq
theorem phase27_31 : ((r ^ 2 * thetaMinus) : ℂ) ^ 3 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 1 = ((73 / 75) + (-2 / 225) * alpha * c) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 16875) + (2 / 50625) * alpha * c + (-1 / 50625) * alpha ^ 2) * alpha_sq + ((74 / 16875) + (1 / 50625) * c ^ 2 + (-2 / 50625) * alpha * c) * c_sq
theorem phase27_32 : ((r ^ 2 * thetaMinus) : ℂ) ^ 3 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 2 = ((1 / 15) * c + (-1 / 15) * alpha) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 253125) * c + (-2 / 759375) * c ^ 3 + (1 / 253125) * alpha + (2 / 759375) * alpha * c ^ 2 + (1 / 759375) * alpha ^ 2 * c + (-1 / 759375) * alpha ^ 3) * alpha_sq + ((76 / 253125) * c + (1 / 759375) * c ^ 3 + (-76 / 253125) * alpha + (-1 / 759375) * alpha * c ^ 2) * c_sq
theorem phase27_33 : ((r ^ 2 * thetaMinus) : ℂ) ^ 3 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 3 = (1) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 1265625) + (-1 / 1265625) * c ^ 2 + (-1 / 3796875) * c ^ 4 + (1 / 3796875) * alpha ^ 2 + (1 / 3796875) * alpha ^ 2 * c ^ 2 + (-1 / 11390625) * alpha ^ 4) * alpha_sq + ((5701 / 1265625) + (77 / 3796875) * c ^ 2 + (1 / 11390625) * c ^ 4) * c_sq
theorem phase27_34 : ((r ^ 2 * thetaMinus) : ℂ) ^ 3 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 4 = ((1 / 15) * c + (1 / 15) * alpha) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 18984375) * c + (-1 / 18984375) * c ^ 3 + (-1 / 56953125) * c ^ 5 + (-1 / 18984375) * alpha + (-1 / 18984375) * alpha * c ^ 2 + (-1 / 56953125) * alpha * c ^ 4 + (1 / 56953125) * alpha ^ 2 * c + (1 / 56953125) * alpha ^ 2 * c ^ 3 + (1 / 56953125) * alpha ^ 3 + (1 / 56953125) * alpha ^ 3 * c ^ 2 + (-1 / 170859375) * alpha ^ 4 * c + (-1 / 170859375) * alpha ^ 5) * alpha_sq + ((5701 / 18984375) * c + (77 / 56953125) * c ^ 3 + (1 / 170859375) * c ^ 5 + (5701 / 18984375) * alpha + (77 / 56953125) * alpha * c ^ 2 + (1 / 170859375) * alpha * c ^ 4) * c_sq
theorem phase27_40 : ((r ^ 2 * thetaMinus) : ℂ) ^ 4 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 0 = ((5033 / 5625) + (-292 / 16875) * alpha * c) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 16875) + (2 / 16875) * c ^ 2 + (-4 / 50625) * alpha * c + (1 / 50625) * alpha ^ 2) * alpha_sq + ((68 / 16875) + (1 / 50625) * c ^ 2 + (-4 / 50625) * alpha * c) * c_sq
theorem phase27_41 : ((r ^ 2 * thetaMinus) : ℂ) ^ 4 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 1 = ((71 / 1125) * c + (-221 / 1125) * alpha) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 84375) * c + (2 / 759375) * c ^ 3 + (-1 / 253125) * alpha + (2 / 759375) * alpha * c ^ 2 + (-1 / 253125) * alpha ^ 2 * c + (1 / 759375) * alpha ^ 3) * alpha_sq + ((8 / 28125) * c + (1 / 759375) * c ^ 3 + (-224 / 253125) * alpha + (-1 / 253125) * alpha * c ^ 2) * c_sq
theorem phase27_42 : ((r ^ 2 * thetaMinus) : ℂ) ^ 4 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 2 = ((73 / 75) + (-2 / 225) * alpha * c) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 1265625) + (1 / 3796875) * c ^ 2 + (-1 / 11390625) * c ^ 4 + (2 / 3796875) * alpha * c + (4 / 11390625) * alpha * c ^ 3 + (-1 / 3796875) * alpha ^ 2 + (-1 / 11390625) * alpha ^ 2 * c ^ 2 + (-2 / 11390625) * alpha ^ 3 * c + (1 / 11390625) * alpha ^ 4) * alpha_sq + ((5549 / 1265625) + (1 / 50625) * c ^ 2 + (1 / 11390625) * c ^ 4 + (-152 / 3796875) * alpha * c + (-2 / 11390625) * alpha * c ^ 3) * c_sq
theorem phase27_43 : ((r ^ 2 * thetaMinus) : ℂ) ^ 4 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 3 = ((1 / 15) * c + (-1 / 15) * alpha) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 18984375) * c + (-1 / 18984375) * c ^ 3 + (-1 / 56953125) * c ^ 5 + (1 / 18984375) * alpha + (1 / 18984375) * alpha * c ^ 2 + (1 / 56953125) * alpha * c ^ 4 + (1 / 56953125) * alpha ^ 2 * c + (1 / 56953125) * alpha ^ 2 * c ^ 3 + (-1 / 56953125) * alpha ^ 3 + (-1 / 56953125) * alpha ^ 3 * c ^ 2 + (-1 / 170859375) * alpha ^ 4 * c + (1 / 170859375) * alpha ^ 5) * alpha_sq + ((5701 / 18984375) * c + (77 / 56953125) * c ^ 3 + (1 / 170859375) * c ^ 5 + (-5701 / 18984375) * alpha + (-77 / 56953125) * alpha * c ^ 2 + (-1 / 170859375) * alpha * c ^ 4) * c_sq
theorem phase27_44 : ((r ^ 2 * thetaMinus) : ℂ) ^ 4 * star ((r ^ 2 * thetaMinus) : ℂ) ^ 4 = (1) := by
  rw [site27]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 94921875) + (-4 / 284765625) * c ^ 2 + (-2 / 284765625) * c ^ 4 + (-4 / 2562890625) * c ^ 6 + (1 / 284765625) * alpha ^ 2 + (4 / 854296875) * alpha ^ 2 * c ^ 2 + (2 / 854296875) * alpha ^ 2 * c ^ 4 + (-1 / 854296875) * alpha ^ 4 + (-4 / 2562890625) * alpha ^ 4 * c ^ 2 + (1 / 2562890625) * alpha ^ 6) * alpha_sq + ((427576 / 94921875) + (214 / 10546875) * c ^ 2 + (26 / 284765625) * c ^ 4 + (1 / 2562890625) * c ^ 6) * c_sq
noncomputable def z27 : Fin 27 → ℂ := Fin.snoc z26 (r ^ 2 * thetaMinus)
theorem v27_00 (t : ℂ) : (momentPoly 27 z27 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00]
  try simp only [phase27_00]
  try simp only [star_one, star_neg]
  ring
theorem v27_01 (t : ℂ) : (momentPoly 27 z27 0 1).eval t = ((-4 / 15) * c * t + (2 / 5) * alpha * t) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_01]
  try simp only [phase27_00, phase27_01]
  try simp only [star_one, star_neg]
  ring
theorem v27_02 (t : ℂ) : (momentPoly 27 z27 0 2).eval t = ((41 / 12) * t ^ 2 + (1189 / 100) * t ^ 4 + (73 / 15) * alpha * t ^ 2 + (-73 / 15) * alpha * t ^ 4 + (-8 / 45) * alpha * c * t ^ 2 + (-8 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_01, v26_02]
  try simp only [phase27_00, phase27_01, phase27_02]
  try simp only [star_one, star_neg]
  linear_combination ((2 / 45) * t ^ 2) * alpha_sq + ((-2 / 45) * t ^ 2) * c_sq
theorem v27_03 (t : ℂ) : (momentPoly 27 z27 0 3).eval t = ((-388 / 25) * t ^ 3 + (363 / 25) * t ^ 5 + 1 * t ^ 9 + (379 / 75) * c * t ^ 3 + (-647 / 75) * c * t ^ 5 + (-284 / 1125) * c * t ^ 9 + (773 / 120) * alpha * t ^ 3 + (9809 / 1200) * alpha * t ^ 5 + (24817 / 6000) * alpha * t ^ 9 + (-292 / 75) * alpha * c * t ^ 3 + (292 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_01, v26_02, v26_03]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-8 / 225) * c * t ^ 3) * alpha_sq + ((-8 / 225) * alpha * t ^ 3 + (-4 / 225) * alpha * t ^ 5) * c_sq
theorem v27_04 (t : ℂ) : (momentPoly 27 z27 0 4).eval t = ((-7665379 / 12000) * t ^ 4 + (1327577 / 2000) * t ^ 6 + (4169783 / 24000) * t ^ 8 + (-113893 / 18000) * t ^ 10 + (1387579 / 120000) * t ^ 16 + (336 / 25) * c * t ^ 4 + (-3472 / 375) * c * t ^ 6 + (-1168 / 375) * c * t ^ 8 + (-16 / 15) * c * t ^ 10 + (19031 / 250) * alpha * t ^ 4 + (22223 / 75) * alpha * t ^ 6 + (-270457 / 750) * alpha * t ^ 8 + (-18332 / 1125) * alpha * t ^ 10 + (5033 / 1125) * alpha * t ^ 16 + (226 / 1125) * alpha * c * t ^ 4 + (77 / 375) * alpha * c * t ^ 6 + (-524 / 225) * alpha * c * t ^ 8 + (-15319 / 3375) * alpha * c * t ^ 10 + (-1168 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_01, v26_02, v26_03, v26_04]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04]
  try simp only [star_one, star_neg]
  linear_combination ((6991 / 2250) * t ^ 4 + (10757 / 4500) * t ^ 6 + (17719 / 13500) * t ^ 10 + (-292 / 225) * c * t ^ 4 + (584 / 375) * c * t ^ 6 + (-292 / 1125) * c * t ^ 8 + (-32 / 3375) * c ^ 2 * t ^ 6 + (-8 / 3375) * c ^ 2 * t ^ 8) * alpha_sq + ((679 / 1125) * t ^ 4 + (-973 / 375) * t ^ 6 + (8 / 1125) * t ^ 8 + (-568 / 3375) * t ^ 10 + (-292 / 225) * alpha * t ^ 4 + (292 / 225) * alpha * t ^ 6) * c_sq
theorem v27_10 (t : ℂ) : (momentPoly 27 z27 1 0).eval t = ((-4 / 15) * c * t + (-2 / 5) * alpha * t) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_10]
  try simp only [phase27_00, phase27_10]
  try simp only [star_one, star_neg]
  ring
theorem v27_11 (t : ℂ) : (momentPoly 27 z27 1 1).eval t = (27 + (-161 / 15) * t ^ 2) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_01, v26_10, v26_11]
  try simp only [phase27_00, phase27_01, phase27_10, phase27_11]
  try simp only [star_one, star_neg]
  linear_combination ((-2 / 45) * t ^ 2) * alpha_sq + ((-2 / 45) * t ^ 2) * c_sq
theorem v27_12 (t : ℂ) : (momentPoly 27 z27 1 2).eval t = ((146 / 25) * t ^ 3 + (-146 / 25) * t ^ 5 + (-212 / 15) * c * t + (2867 / 225) * c * t ^ 3 + (-221 / 75) * c * t ^ 5 + (106 / 5) * alpha * t + (-5239 / 450) * alpha * t ^ 3 + (-1373 / 450) * alpha * t ^ 5 + (-292 / 225) * alpha * c * t ^ 3 + (292 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_01, v26_02, v26_10, v26_11, v26_12]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_10, phase27_11, phase27_12]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 225) * t ^ 3 + (73 / 225) * t ^ 5 + (8 / 675) * c * t ^ 3) * alpha_sq + ((-8 / 675) * alpha * t ^ 3 + (-4 / 675) * alpha * t ^ 5) * c_sq
theorem v27_13 (t : ℂ) : (momentPoly 27 z27 1 3).eval t = ((533 / 2) * t ^ 2 + (587449 / 1500) * t ^ 4 + (-1251487 / 3000) * t ^ 6 + (72163 / 9000) * t ^ 10 + (-8 / 15) * c * t ^ 4 + (4 / 5) * c * t ^ 6 + (-4 / 15) * c * t ^ 10 + (1898 / 5) * alpha * t ^ 2 + (-38458 / 75) * alpha * t ^ 4 + (9653 / 75) * alpha * t ^ 6 + (67 / 15) * alpha * t ^ 10 + (-208 / 15) * alpha * c * t ^ 2 + (5089 / 750) * alpha * c * t ^ 4 + (20599 / 4500) * alpha * c * t ^ 6 + (-4349 / 4500) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_01, v26_02, v26_03, v26_10, v26_11, v26_12, v26_13]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_10, phase27_11, phase27_12, phase27_13]
  try simp only [star_one, star_neg]
  linear_combination ((52 / 15) * t ^ 2 + (-21361 / 9000) * t ^ 4 + (-13217 / 18000) * t ^ 6 + (-17719 / 54000) * t ^ 10) * alpha_sq + ((-52 / 15) * t ^ 2 + (5747 / 2250) * t ^ 4 + (-2983 / 2250) * t ^ 6 + (-142 / 3375) * t ^ 10 + (-146 / 225) * alpha * t ^ 4 + (146 / 225) * alpha * t ^ 6) * c_sq
theorem v27_14 (t : ℂ) : (momentPoly 27 z27 1 4).eval t = ((-39576 / 25) * t ^ 3 + (1428763 / 625) * t ^ 5 + (-853498 / 1875) * t ^ 7 + (-323218 / 1875) * t ^ 9 + (-149564 / 1875) * t ^ 11 + (8191 / 1875) * t ^ 17 + (12886 / 25) * c * t ^ 3 + (-6029797 / 5000) * c * t ^ 5 + (1638957 / 2500) * c * t ^ 7 + (-5254103 / 90000) * c * t ^ 9 + (2294797 / 67500) * c * t ^ 11 + (-262271 / 90000) * c * t ^ 17 + (13141 / 20) * alpha * t ^ 3 + (4698839 / 10000) * alpha * t ^ 5 + (-5668689 / 5000) * alpha * t ^ 7 + (87538141 / 180000) * alpha * t ^ 9 + (-22926059 / 135000) * alpha * t ^ 11 + (-2518513 / 540000) * alpha * t ^ 17 + (-9928 / 25) * alpha * c * t ^ 3 + (4220974 / 5625) * alpha * c * t ^ 5 + (-2482228 / 5625) * alpha * c * t ^ 7 + (504122 / 5625) * alpha * c * t ^ 9 + (-7072 / 16875) * alpha * c * t ^ 11 + (-20132 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_01, v26_02, v26_03, v26_04, v26_10, v26_11, v26_12, v26_13, v26_14]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04, phase27_10, phase27_11, phase27_12, phase27_13, phase27_14]
  try simp only [star_one, star_neg]
  linear_combination ((2482 / 25) * t ^ 3 + (-455131 / 3750) * t ^ 5 + (-11657 / 5625) * t ^ 7 + (83047 / 3750) * t ^ 9 + (39032 / 16875) * t ^ 11 + (-5033 / 16875) * t ^ 17 + (-272 / 75) * c * t ^ 3 + (40676 / 16875) * c * t ^ 5 + (3556 / 5625) * c * t ^ 7 + (2368 / 16875) * c * t ^ 9 + (2272 / 50625) * c * t ^ 11 + (-292 / 3375) * c ^ 2 * t ^ 7 + (292 / 3375) * c ^ 2 * t ^ 9) * alpha_sq + ((256 / 375) * t ^ 5 + (16 / 1125) * t ^ 7 + (-584 / 1125) * t ^ 9 + (-8 / 45) * t ^ 11 + (-272 / 75) * alpha * t ^ 3 + (593 / 5625) * alpha * t ^ 5 + (6751 / 3750) * alpha * t ^ 7 + (-5998 / 16875) * alpha * t ^ 9 + (-67379 / 101250) * alpha * t ^ 11 + (-584 / 50625) * alpha * t ^ 17) * c_sq
theorem v27_20 (t : ℂ) : (momentPoly 27 z27 2 0).eval t = ((41 / 12) * t ^ 2 + (1189 / 100) * t ^ 4 + (-73 / 15) * alpha * t ^ 2 + (73 / 15) * alpha * t ^ 4 + (8 / 45) * alpha * c * t ^ 2 + (8 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_10, v26_20]
  try simp only [phase27_00, phase27_10, phase27_20]
  try simp only [star_one, star_neg]
  linear_combination ((2 / 45) * t ^ 2) * alpha_sq + ((-2 / 45) * t ^ 2) * c_sq
theorem v27_21 (t : ℂ) : (momentPoly 27 z27 2 1).eval t = ((146 / 25) * t ^ 3 + (-146 / 25) * t ^ 5 + (-212 / 15) * c * t + (2867 / 225) * c * t ^ 3 + (-221 / 75) * c * t ^ 5 + (-106 / 5) * alpha * t + (5239 / 450) * alpha * t ^ 3 + (1373 / 450) * alpha * t ^ 5 + (292 / 225) * alpha * c * t ^ 3 + (-292 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_01, v26_10, v26_11, v26_20, v26_21]
  try simp only [phase27_00, phase27_01, phase27_10, phase27_11, phase27_20, phase27_21]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 225) * t ^ 3 + (73 / 225) * t ^ 5 + (8 / 675) * c * t ^ 3) * alpha_sq + ((8 / 675) * alpha * t ^ 3 + (4 / 675) * alpha * t ^ 5) * c_sq
theorem v27_22 (t : ℂ) : (momentPoly 27 z27 2 2).eval t = (1431 + (-16744 / 15) * t ^ 2 + (-272269 / 1200) * t ^ 4 + (-85549 / 9000) * t ^ 6 + (3352813 / 18000) * t ^ 8 + (-1168 / 225) * c * t ^ 4 + (4672 / 1125) * c * t ^ 6 + (1168 / 1125) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_01, v26_02, v26_10, v26_11, v26_12, v26_20, v26_21, v26_22]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_10, phase27_11, phase27_12, phase27_20, phase27_21, phase27_22]
  try simp only [star_one, star_neg]
  linear_combination ((-208 / 45) * t ^ 2 + (479 / 225) * t ^ 4 + (41 / 225) * t ^ 6 + (292 / 675) * c * t ^ 4 + (-584 / 1125) * c * t ^ 6 + (292 / 3375) * c * t ^ 8 + (32 / 10125) * c ^ 2 * t ^ 6 + (8 / 10125) * c ^ 2 * t ^ 8) * alpha_sq + ((-208 / 45) * t ^ 2 + (721 / 225) * t ^ 4 + (-3047 / 3375) * t ^ 6 + (-8 / 3375) * t ^ 8) * c_sq
theorem v27_23 (t : ℂ) : (momentPoly 27 z27 2 3).eval t = ((22338 / 25) * t ^ 3 + (-3732503 / 3000) * t ^ 5 + (2070211 / 6000) * t ^ 7 + (-25649 / 1200) * t ^ 9 + (754847 / 10000) * t ^ 11 + (-1454941 / 30000) * t ^ 13 + (-3308 / 3) * c * t + (48739 / 25) * c * t ^ 3 + (-647313 / 500) * c * t ^ 5 + (2858447 / 5625) * c * t ^ 7 + (-2939527 / 22500) * c * t ^ 9 + (95339 / 33750) * c * t ^ 11 + (-35731 / 11250) * c * t ^ 13 + 1654 * alpha * t + (-89063 / 50) * alpha * t ^ 3 + (-428143 / 7200) * alpha * t ^ 5 + (56805727 / 360000) * alpha * t ^ 7 + (27977407 / 360000) * alpha * t ^ 9 + (5836663 / 1080000) * alpha * t ^ 11 + (11157061 / 216000) * alpha * t ^ 13 + (-4964 / 25) * alpha * c * t ^ 3 + (130268 / 375) * alpha * c * t ^ 5 + (-55264 / 375) * alpha * c * t ^ 7 + (1048 / 1125) * alpha * c * t ^ 9 + (-20068 / 16875) * alpha * c * t ^ 11 + (-20132 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_01, v26_02, v26_03, v26_10, v26_11, v26_12, v26_13, v26_20, v26_21, v26_22, v26_23]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_10, phase27_11, phase27_12, phase27_13, phase27_20, phase27_21, phase27_22, phase27_23]
  try simp only [star_one, star_neg]
  linear_combination ((-1241 / 25) * t ^ 3 + (10897 / 225) * t ^ 5 + (136 / 75) * t ^ 7 + (-26333 / 16875) * t ^ 11 + (16133 / 16875) * t ^ 13 + (136 / 75) * c * t ^ 3 + (-4897 / 4500) * c * t ^ 5 + (-60077 / 135000) * c * t ^ 7 + (-8297 / 135000) * c * t ^ 9 + (76979 / 405000) * c * t ^ 11 + (-1183 / 45000) * c * t ^ 13 + (292 / 3375) * c ^ 2 * t ^ 7 + (-292 / 3375) * c ^ 2 * t ^ 9) * alpha_sq + ((-1268 / 1125) * t ^ 5 + (734 / 1125) * t ^ 7 + (584 / 1125) * t ^ 9 + (-2 / 45) * t ^ 11 + (-136 / 75) * alpha * t ^ 3 + (2291 / 13500) * alpha * t ^ 5 + (115379 / 135000) * alpha * t ^ 7 + (-32 / 16875) * alpha * t ^ 9 + (-58291 / 405000) * alpha * t ^ 11 + (284 / 50625) * alpha * t ^ 13) * c_sq
theorem v27_24 (t : ℂ) : (momentPoly 27 z27 2 4).eval t = ((81590 / 3) * t ^ 2 + (-747217 / 60) * t ^ 4 + (-6816347143 / 720000) * t ^ 6 + (-29072034839 / 3600000) * t ^ 8 + (26078359051 / 7200000) * t ^ 10 + (20480839421 / 7200000) * t ^ 12 + (1211865301 / 5400000) * t ^ 14 + (2094841981 / 21600000) * t ^ 18 + (1337424563 / 21600000) * t ^ 20 + (-320 / 3) * c * t ^ 4 + (1510426 / 5625) * c * t ^ 6 + (-5146427 / 28125) * c * t ^ 8 + (-1640851 / 28125) * c * t ^ 10 + (714679 / 28125) * c * t ^ 12 + (1585997 / 28125) * c * t ^ 14 + (-80528 / 28125) * c * t ^ 18 + (8 / 15) * c * t ^ 20 + (116216 / 3) * alpha * t ^ 2 + (-196193 / 3) * alpha * t ^ 4 + (371044743 / 20000) * alpha * t ^ 6 + (6930202879 / 900000) * alpha * t ^ 8 + (6500115289 / 1800000) * alpha * t ^ 10 + (-16193275043 / 5400000) * alpha * t ^ 12 + (-364898321 / 1350000) * alpha * t ^ 14 + (-269578601 / 5400000) * alpha * t ^ 18 + (68600353 / 600000) * alpha * t ^ 20 + (-12736 / 9) * alpha * c * t ^ 2 + (24428 / 15) * alpha * c * t ^ 4 + (17826631 / 67500) * alpha * c * t ^ 6 + (-37086748 / 84375) * alpha * c * t ^ 8 + (-4722561 / 25000) * alpha * c * t ^ 10 + (32830051 / 225000) * alpha * c * t ^ 12 + (-55492559 / 1012500) * alpha * c * t ^ 14 + (7597957 / 2025000) * alpha * c * t ^ 18 + (-50797 / 135000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_01, v26_02, v26_03, v26_04, v26_10, v26_11, v26_12, v26_13, v26_14, v26_20, v26_21, v26_22, v26_23, v26_24]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04, phase27_10, phase27_11, phase27_12, phase27_13, phase27_14, phase27_20, phase27_21, phase27_22, phase27_23, phase27_24]
  try simp only [star_one, star_neg]
  linear_combination ((3184 / 9) * t ^ 2 + (-21361 / 45) * t ^ 4 + (-1015273 / 54000) * t ^ 6 + (13732907 / 90000) * t ^ 8 + (-41795759 / 540000) * t ^ 10 + (5190971 / 270000) * t ^ 12 + (1114609 / 90000) * t ^ 14 + (78731 / 540000) * t ^ 18 + (-68099 / 16875) * c * t ^ 6 + (1240577 / 84375) * c * t ^ 8 + (-1112959 / 84375) * c * t ^ 10 + (328141 / 84375) * c * t ^ 12 + (-386056 / 253125) * c * t ^ 14 + (29014 / 253125) * c * t ^ 18 + (2 / 45) * c * t ^ 20 + (7897 / 253125) * c ^ 2 * t ^ 8 + (-1141 / 168750) * c ^ 2 * t ^ 10 + (5966 / 253125) * c ^ 2 * t ^ 12 + (71923 / 1518750) * c ^ 2 * t ^ 14 + (2336 / 759375) * c ^ 2 * t ^ 18 + (1168 / 759375) * c ^ 2 * t ^ 20) * alpha_sq + ((-3184 / 9) * t ^ 2 + (22988 / 45) * t ^ 4 + (-107382161 / 270000) * t ^ 6 + (130209109 / 675000) * t ^ 8 + (-134327227 / 2700000) * t ^ 10 + (1519129 / 225000) * t ^ 12 + (-495509 / 253125) * t ^ 14 + (-3668017 / 8100000) * t ^ 18 + (-1168 / 253125) * t ^ 20 + (-1168 / 9) * alpha * t ^ 4 + (239677 / 1125) * alpha * t ^ 6 + (-1627862 / 16875) * alpha * t ^ 8 + (238889 / 16875) * alpha * t ^ 10 + (1784 / 50625) * alpha * t ^ 12 + (-40264 / 50625) * alpha * t ^ 14 + (-10066 / 50625) * alpha * t ^ 18) * c_sq
theorem v27_30 (t : ℂ) : (momentPoly 27 z27 3 0).eval t = ((-388 / 25) * t ^ 3 + (363 / 25) * t ^ 5 + 1 * t ^ 9 + (379 / 75) * c * t ^ 3 + (-647 / 75) * c * t ^ 5 + (-284 / 1125) * c * t ^ 9 + (-773 / 120) * alpha * t ^ 3 + (-9809 / 1200) * alpha * t ^ 5 + (-24817 / 6000) * alpha * t ^ 9 + (292 / 75) * alpha * c * t ^ 3 + (-292 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_10, v26_20, v26_30]
  try simp only [phase27_00, phase27_10, phase27_20, phase27_30]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-8 / 225) * c * t ^ 3) * alpha_sq + ((8 / 225) * alpha * t ^ 3 + (4 / 225) * alpha * t ^ 5) * c_sq
theorem v27_31 (t : ℂ) : (momentPoly 27 z27 3 1).eval t = ((533 / 2) * t ^ 2 + (587449 / 1500) * t ^ 4 + (-1251487 / 3000) * t ^ 6 + (72163 / 9000) * t ^ 10 + (-8 / 15) * c * t ^ 4 + (4 / 5) * c * t ^ 6 + (-4 / 15) * c * t ^ 10 + (-1898 / 5) * alpha * t ^ 2 + (38458 / 75) * alpha * t ^ 4 + (-9653 / 75) * alpha * t ^ 6 + (-67 / 15) * alpha * t ^ 10 + (208 / 15) * alpha * c * t ^ 2 + (-5089 / 750) * alpha * c * t ^ 4 + (-20599 / 4500) * alpha * c * t ^ 6 + (4349 / 4500) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_01, v26_10, v26_11, v26_20, v26_21, v26_30, v26_31]
  try simp only [phase27_00, phase27_01, phase27_10, phase27_11, phase27_20, phase27_21, phase27_30, phase27_31]
  try simp only [star_one, star_neg]
  linear_combination ((52 / 15) * t ^ 2 + (-21361 / 9000) * t ^ 4 + (-13217 / 18000) * t ^ 6 + (-17719 / 54000) * t ^ 10) * alpha_sq + ((-52 / 15) * t ^ 2 + (5747 / 2250) * t ^ 4 + (-2983 / 2250) * t ^ 6 + (-142 / 3375) * t ^ 10 + (146 / 225) * alpha * t ^ 4 + (-146 / 225) * alpha * t ^ 6) * c_sq
theorem v27_32 (t : ℂ) : (momentPoly 27 z27 3 2).eval t = ((22338 / 25) * t ^ 3 + (-3732503 / 3000) * t ^ 5 + (2070211 / 6000) * t ^ 7 + (-25649 / 1200) * t ^ 9 + (754847 / 10000) * t ^ 11 + (-1454941 / 30000) * t ^ 13 + (-3308 / 3) * c * t + (48739 / 25) * c * t ^ 3 + (-647313 / 500) * c * t ^ 5 + (2858447 / 5625) * c * t ^ 7 + (-2939527 / 22500) * c * t ^ 9 + (95339 / 33750) * c * t ^ 11 + (-35731 / 11250) * c * t ^ 13 + (-1654) * alpha * t + (89063 / 50) * alpha * t ^ 3 + (428143 / 7200) * alpha * t ^ 5 + (-56805727 / 360000) * alpha * t ^ 7 + (-27977407 / 360000) * alpha * t ^ 9 + (-5836663 / 1080000) * alpha * t ^ 11 + (-11157061 / 216000) * alpha * t ^ 13 + (4964 / 25) * alpha * c * t ^ 3 + (-130268 / 375) * alpha * c * t ^ 5 + (55264 / 375) * alpha * c * t ^ 7 + (-1048 / 1125) * alpha * c * t ^ 9 + (20068 / 16875) * alpha * c * t ^ 11 + (20132 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_01, v26_02, v26_10, v26_11, v26_12, v26_20, v26_21, v26_22, v26_30, v26_31, v26_32]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_10, phase27_11, phase27_12, phase27_20, phase27_21, phase27_22, phase27_30, phase27_31, phase27_32]
  try simp only [star_one, star_neg]
  linear_combination ((-1241 / 25) * t ^ 3 + (10897 / 225) * t ^ 5 + (136 / 75) * t ^ 7 + (-26333 / 16875) * t ^ 11 + (16133 / 16875) * t ^ 13 + (136 / 75) * c * t ^ 3 + (-4897 / 4500) * c * t ^ 5 + (-60077 / 135000) * c * t ^ 7 + (-8297 / 135000) * c * t ^ 9 + (76979 / 405000) * c * t ^ 11 + (-1183 / 45000) * c * t ^ 13 + (292 / 3375) * c ^ 2 * t ^ 7 + (-292 / 3375) * c ^ 2 * t ^ 9) * alpha_sq + ((-1268 / 1125) * t ^ 5 + (734 / 1125) * t ^ 7 + (584 / 1125) * t ^ 9 + (-2 / 45) * t ^ 11 + (136 / 75) * alpha * t ^ 3 + (-2291 / 13500) * alpha * t ^ 5 + (-115379 / 135000) * alpha * t ^ 7 + (32 / 16875) * alpha * t ^ 9 + (58291 / 405000) * alpha * t ^ 11 + (-284 / 50625) * alpha * t ^ 13) * c_sq
theorem v27_33 (t : ℂ) : (momentPoly 27 z27 3 3).eval t = (111645 + (-128156) * t ^ 2 + (-816807 / 16) * t ^ 4 + (8585856701 / 120000) * t ^ 6 + (2297305669 / 120000) * t ^ 8 + (-2976539621 / 160000) * t ^ 10 + (-736317677 / 1800000) * t ^ 12 + (524220371 / 3600000) * t ^ 14 + (852579733 / 21600000) * t ^ 18 + (-1168) * c * t ^ 4 + (3213911 / 1875) * c * t ^ 6 + (-142279 / 750) * c * t ^ 8 + (-1239547 / 3750) * c * t ^ 10 + (-1025291 / 11250) * c * t ^ 12 + (82259 / 1250) * c * t ^ 14 + (-568 / 1125) * c * t ^ 18) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_01, v26_02, v26_03, v26_10, v26_11, v26_12, v26_13, v26_20, v26_21, v26_22, v26_23, v26_30, v26_31, v26_32, v26_33]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_10, phase27_11, phase27_12, phase27_13, phase27_20, phase27_21, phase27_22, phase27_23, phase27_30, phase27_31, phase27_32, phase27_33]
  try simp only [star_one, star_neg]
  linear_combination ((-1592 / 3) * t ^ 2 + 479 * t ^ 4 + (-1257673 / 30000) * t ^ 6 + (185513 / 4000) * t ^ 8 + (-823369 / 60000) * t ^ 10 + (-52216423 / 2700000) * t ^ 12 + (-57491953 / 2700000) * t ^ 14 + (-3134443 / 2025000) * t ^ 18 + (292 / 3) * c * t ^ 4 + (-330908 / 1875) * c * t ^ 6 + (87548 / 1125) * c * t ^ 8 + (2044 / 5625) * c * t ^ 10 + (568 / 225) * c * t ^ 12 + (-584 / 375) * c * t ^ 14 + (2432 / 3375) * c ^ 2 * t ^ 6 + (-8531 / 33750) * c ^ 2 * t ^ 8 + (-1663 / 7500) * c ^ 2 * t ^ 10 + (4189 / 67500) * c ^ 2 * t ^ 14) * alpha_sq + ((-1592 / 3) * t ^ 2 + 721 * t ^ 4 + (-18356501 / 45000) * t ^ 6 + (4091857 / 22500) * t ^ 8 + (-171503 / 3000) * t ^ 10 + (36427 / 84375) * t ^ 12 + (-486421 / 168750) * t ^ 14 + (-10082 / 253125) * t ^ 18) * c_sq
theorem v27_34 (t : ℂ) : (momentPoly 27 z27 3 4).eval t = ((3353328 / 25) * t ^ 3 + (-118655567 / 500) * t ^ 5 + (15329562433 / 150000) * t ^ 7 + (-28630663 / 1000) * t ^ 9 + (2664117111 / 50000) * t ^ 11 + (-254104710419 / 9000000) * t ^ 13 + (18947051527 / 2250000) * t ^ 15 + (-36821571557 / 9000000) * t ^ 17 + (-213168629 / 2250000) * t ^ 19 + (156688877 / 600000) * t ^ 21 + (603684269 / 9000000) * t ^ 25 + (-112556) * c * t + (7316584 / 25) * c * t ^ 3 + (-78949081 / 250) * c * t ^ 5 + (193448324471 / 900000) * c * t ^ 7 + (-99964445657 / 900000) * c * t ^ 9 + (12503710289 / 360000) * c * t ^ 11 + (-144916951619 / 27000000) * c * t ^ 13 + (3187070239 / 2250000) * c * t ^ 15 + (-392800213 / 6750000) * c * t ^ 17 + (-1537928419 / 81000000) * c * t ^ 19 + (-832324727 / 27000000) * c * t ^ 21 + (-7900291 / 2250000) * c * t ^ 25 + 168834 * alpha * t + (-6684964 / 25) * alpha * t ^ 3 + (3971111 / 80) * alpha * t ^ 5 + (49304257927 / 1440000) * alpha * t ^ 7 + (459572229143 / 14400000) * alpha * t ^ 9 + (-271902957709 / 14400000) * alpha * t ^ 11 + (5919559220929 / 432000000) * alpha * t ^ 13 + (-40914635023 / 4500000) * alpha * t ^ 15 + (-401935860053 / 432000000) * alpha * t ^ 17 + (-143687890549 / 648000000) * alpha * t ^ 19 + (-18494395697 / 432000000) * alpha * t ^ 21 + (-2067088351 / 51840000) * alpha * t ^ 25 + (-745184 / 25) * alpha * c * t ^ 3 + (27592612 / 375) * alpha * c * t ^ 5 + (-1473065687 / 25000) * alpha * c * t ^ 7 + (3996492869 / 225000) * alpha * c * t ^ 9 + (-2099111941 / 450000) * alpha * c * t ^ 11 + (3418350593 / 2250000) * alpha * c * t ^ 13 + (749633513 / 1687500) * alpha * c * t ^ 15 + (39572317 / 421875) * alpha * c * t ^ 17 + (1640800123 / 20250000) * alpha * c * t ^ 19 + (-22931729 / 270000) * alpha * c * t ^ 21 + (-1516972 / 1265625) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_01, v26_02, v26_03, v26_04, v26_10, v26_11, v26_12, v26_13, v26_14, v26_20, v26_21, v26_22, v26_23, v26_24, v26_30, v26_31, v26_32, v26_33, v26_34]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04, phase27_10, phase27_11, phase27_12, phase27_13, phase27_14, phase27_20, phase27_21, phase27_22, phase27_23, phase27_24, phase27_30, phase27_31, phase27_32, phase27_33, phase27_34]
  try simp only [star_one, star_neg]
  linear_combination ((-186296 / 25) * t ^ 3 + (532597 / 75) * t ^ 5 + (1016433149 / 180000) * t ^ 7 + (-1030961423 / 180000) * t ^ 9 + (-15694537 / 40000) * t ^ 11 + (20329594579 / 27000000) * t ^ 13 + (185883173 / 6750000) * t ^ 15 + (18353387 / 281250) * t ^ 17 + (-9405317 / 81000000) * t ^ 19 + (-22814993 / 1080000) * t ^ 21 + (-1112293 / 1265625) * t ^ 25 + (20416 / 75) * c * t ^ 3 + (-239953 / 750) * c * t ^ 5 + (-856399 / 27000) * c * t ^ 7 + (41358689 / 1350000) * c * t ^ 9 + (16316957 / 168750) * c * t ^ 11 + (-225896921 / 5062500) * c * t ^ 13 + (22894673 / 3375000) * c * t ^ 15 + (-37434877 / 20250000) * c * t ^ 17 + (3483097 / 3037500) * c * t ^ 19 + (-412837 / 10125000) * c * t ^ 21 + (-86359 / 1687500) * c * t ^ 25 + (87016 / 3375) * c ^ 2 * t ^ 7 + (-716111 / 16875) * c ^ 2 * t ^ 9 + (540418 / 28125) * c ^ 2 * t ^ 11 + (-234233 / 84375) * c ^ 2 * t ^ 13 + (8068 / 84375) * c ^ 2 * t ^ 15 + (20132 / 253125) * c ^ 2 * t ^ 17 + (21316 / 253125) * c ^ 2 * t ^ 19 + (-2 / 45) * c ^ 2 * t ^ 21) * alpha_sq + ((-124264 / 375) * t ^ 5 + (464029 / 1250) * t ^ 7 + (2132783 / 22500) * t ^ 9 + (-16760941 / 112500) * t ^ 11 + (-6240557 / 337500) * t ^ 13 + (2311009 / 67500) * t ^ 15 + (-40864 / 84375) * t ^ 17 + (-100046 / 84375) * t ^ 19 + (4 / 15) * t ^ 21 + (-20416 / 75) * alpha * t ^ 3 + (135193 / 750) * alpha * t ^ 5 + (20761991 / 135000) * alpha * t ^ 7 + (-100047677 / 1350000) * alpha * t ^ 9 + (-40678079 / 1350000) * alpha * t ^ 11 + (176638607 / 10125000) * alpha * t ^ 13 + (-89546531 / 6750000) * alpha * t ^ 15 + (-914551 / 2531250) * alpha * t ^ 17 + (9253531 / 15187500) * alpha * t ^ 19 + (-3375023 / 20250000) * alpha * t ^ 21 + (-41464 / 3796875) * alpha * t ^ 25) * c_sq
theorem v27_40 (t : ℂ) : (momentPoly 27 z27 4 0).eval t = ((-7665379 / 12000) * t ^ 4 + (1327577 / 2000) * t ^ 6 + (4169783 / 24000) * t ^ 8 + (-113893 / 18000) * t ^ 10 + (1387579 / 120000) * t ^ 16 + (336 / 25) * c * t ^ 4 + (-3472 / 375) * c * t ^ 6 + (-1168 / 375) * c * t ^ 8 + (-16 / 15) * c * t ^ 10 + (-19031 / 250) * alpha * t ^ 4 + (-22223 / 75) * alpha * t ^ 6 + (270457 / 750) * alpha * t ^ 8 + (18332 / 1125) * alpha * t ^ 10 + (-5033 / 1125) * alpha * t ^ 16 + (-226 / 1125) * alpha * c * t ^ 4 + (-77 / 375) * alpha * c * t ^ 6 + (524 / 225) * alpha * c * t ^ 8 + (15319 / 3375) * alpha * c * t ^ 10 + (1168 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_10, v26_20, v26_30, v26_40]
  try simp only [phase27_00, phase27_10, phase27_20, phase27_30, phase27_40]
  try simp only [star_one, star_neg]
  linear_combination ((6991 / 2250) * t ^ 4 + (10757 / 4500) * t ^ 6 + (17719 / 13500) * t ^ 10 + (-292 / 225) * c * t ^ 4 + (584 / 375) * c * t ^ 6 + (-292 / 1125) * c * t ^ 8 + (-32 / 3375) * c ^ 2 * t ^ 6 + (-8 / 3375) * c ^ 2 * t ^ 8) * alpha_sq + ((679 / 1125) * t ^ 4 + (-973 / 375) * t ^ 6 + (8 / 1125) * t ^ 8 + (-568 / 3375) * t ^ 10 + (292 / 225) * alpha * t ^ 4 + (-292 / 225) * alpha * t ^ 6) * c_sq
theorem v27_41 (t : ℂ) : (momentPoly 27 z27 4 1).eval t = ((-39576 / 25) * t ^ 3 + (1428763 / 625) * t ^ 5 + (-853498 / 1875) * t ^ 7 + (-323218 / 1875) * t ^ 9 + (-149564 / 1875) * t ^ 11 + (8191 / 1875) * t ^ 17 + (12886 / 25) * c * t ^ 3 + (-6029797 / 5000) * c * t ^ 5 + (1638957 / 2500) * c * t ^ 7 + (-5254103 / 90000) * c * t ^ 9 + (2294797 / 67500) * c * t ^ 11 + (-262271 / 90000) * c * t ^ 17 + (-13141 / 20) * alpha * t ^ 3 + (-4698839 / 10000) * alpha * t ^ 5 + (5668689 / 5000) * alpha * t ^ 7 + (-87538141 / 180000) * alpha * t ^ 9 + (22926059 / 135000) * alpha * t ^ 11 + (2518513 / 540000) * alpha * t ^ 17 + (9928 / 25) * alpha * c * t ^ 3 + (-4220974 / 5625) * alpha * c * t ^ 5 + (2482228 / 5625) * alpha * c * t ^ 7 + (-504122 / 5625) * alpha * c * t ^ 9 + (7072 / 16875) * alpha * c * t ^ 11 + (20132 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_01, v26_10, v26_11, v26_20, v26_21, v26_30, v26_31, v26_40, v26_41]
  try simp only [phase27_00, phase27_01, phase27_10, phase27_11, phase27_20, phase27_21, phase27_30, phase27_31, phase27_40, phase27_41]
  try simp only [star_one, star_neg]
  linear_combination ((2482 / 25) * t ^ 3 + (-455131 / 3750) * t ^ 5 + (-11657 / 5625) * t ^ 7 + (83047 / 3750) * t ^ 9 + (39032 / 16875) * t ^ 11 + (-5033 / 16875) * t ^ 17 + (-272 / 75) * c * t ^ 3 + (40676 / 16875) * c * t ^ 5 + (3556 / 5625) * c * t ^ 7 + (2368 / 16875) * c * t ^ 9 + (2272 / 50625) * c * t ^ 11 + (-292 / 3375) * c ^ 2 * t ^ 7 + (292 / 3375) * c ^ 2 * t ^ 9) * alpha_sq + ((256 / 375) * t ^ 5 + (16 / 1125) * t ^ 7 + (-584 / 1125) * t ^ 9 + (-8 / 45) * t ^ 11 + (272 / 75) * alpha * t ^ 3 + (-593 / 5625) * alpha * t ^ 5 + (-6751 / 3750) * alpha * t ^ 7 + (5998 / 16875) * alpha * t ^ 9 + (67379 / 101250) * alpha * t ^ 11 + (584 / 50625) * alpha * t ^ 17) * c_sq
theorem v27_42 (t : ℂ) : (momentPoly 27 z27 4 2).eval t = ((81590 / 3) * t ^ 2 + (-747217 / 60) * t ^ 4 + (-6816347143 / 720000) * t ^ 6 + (-29072034839 / 3600000) * t ^ 8 + (26078359051 / 7200000) * t ^ 10 + (20480839421 / 7200000) * t ^ 12 + (1211865301 / 5400000) * t ^ 14 + (2094841981 / 21600000) * t ^ 18 + (1337424563 / 21600000) * t ^ 20 + (-320 / 3) * c * t ^ 4 + (1510426 / 5625) * c * t ^ 6 + (-5146427 / 28125) * c * t ^ 8 + (-1640851 / 28125) * c * t ^ 10 + (714679 / 28125) * c * t ^ 12 + (1585997 / 28125) * c * t ^ 14 + (-80528 / 28125) * c * t ^ 18 + (8 / 15) * c * t ^ 20 + (-116216 / 3) * alpha * t ^ 2 + (196193 / 3) * alpha * t ^ 4 + (-371044743 / 20000) * alpha * t ^ 6 + (-6930202879 / 900000) * alpha * t ^ 8 + (-6500115289 / 1800000) * alpha * t ^ 10 + (16193275043 / 5400000) * alpha * t ^ 12 + (364898321 / 1350000) * alpha * t ^ 14 + (269578601 / 5400000) * alpha * t ^ 18 + (-68600353 / 600000) * alpha * t ^ 20 + (12736 / 9) * alpha * c * t ^ 2 + (-24428 / 15) * alpha * c * t ^ 4 + (-17826631 / 67500) * alpha * c * t ^ 6 + (37086748 / 84375) * alpha * c * t ^ 8 + (4722561 / 25000) * alpha * c * t ^ 10 + (-32830051 / 225000) * alpha * c * t ^ 12 + (55492559 / 1012500) * alpha * c * t ^ 14 + (-7597957 / 2025000) * alpha * c * t ^ 18 + (50797 / 135000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_01, v26_02, v26_10, v26_11, v26_12, v26_20, v26_21, v26_22, v26_30, v26_31, v26_32, v26_40, v26_41, v26_42]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_10, phase27_11, phase27_12, phase27_20, phase27_21, phase27_22, phase27_30, phase27_31, phase27_32, phase27_40, phase27_41, phase27_42]
  try simp only [star_one, star_neg]
  linear_combination ((3184 / 9) * t ^ 2 + (-21361 / 45) * t ^ 4 + (-1015273 / 54000) * t ^ 6 + (13732907 / 90000) * t ^ 8 + (-41795759 / 540000) * t ^ 10 + (5190971 / 270000) * t ^ 12 + (1114609 / 90000) * t ^ 14 + (78731 / 540000) * t ^ 18 + (-68099 / 16875) * c * t ^ 6 + (1240577 / 84375) * c * t ^ 8 + (-1112959 / 84375) * c * t ^ 10 + (328141 / 84375) * c * t ^ 12 + (-386056 / 253125) * c * t ^ 14 + (29014 / 253125) * c * t ^ 18 + (2 / 45) * c * t ^ 20 + (7897 / 253125) * c ^ 2 * t ^ 8 + (-1141 / 168750) * c ^ 2 * t ^ 10 + (5966 / 253125) * c ^ 2 * t ^ 12 + (71923 / 1518750) * c ^ 2 * t ^ 14 + (2336 / 759375) * c ^ 2 * t ^ 18 + (1168 / 759375) * c ^ 2 * t ^ 20) * alpha_sq + ((-3184 / 9) * t ^ 2 + (22988 / 45) * t ^ 4 + (-107382161 / 270000) * t ^ 6 + (130209109 / 675000) * t ^ 8 + (-134327227 / 2700000) * t ^ 10 + (1519129 / 225000) * t ^ 12 + (-495509 / 253125) * t ^ 14 + (-3668017 / 8100000) * t ^ 18 + (-1168 / 253125) * t ^ 20 + (1168 / 9) * alpha * t ^ 4 + (-239677 / 1125) * alpha * t ^ 6 + (1627862 / 16875) * alpha * t ^ 8 + (-238889 / 16875) * alpha * t ^ 10 + (-1784 / 50625) * alpha * t ^ 12 + (40264 / 50625) * alpha * t ^ 14 + (10066 / 50625) * alpha * t ^ 18) * c_sq
theorem v27_43 (t : ℂ) : (momentPoly 27 z27 4 3).eval t = ((3353328 / 25) * t ^ 3 + (-118655567 / 500) * t ^ 5 + (15329562433 / 150000) * t ^ 7 + (-28630663 / 1000) * t ^ 9 + (2664117111 / 50000) * t ^ 11 + (-254104710419 / 9000000) * t ^ 13 + (18947051527 / 2250000) * t ^ 15 + (-36821571557 / 9000000) * t ^ 17 + (-213168629 / 2250000) * t ^ 19 + (156688877 / 600000) * t ^ 21 + (603684269 / 9000000) * t ^ 25 + (-112556) * c * t + (7316584 / 25) * c * t ^ 3 + (-78949081 / 250) * c * t ^ 5 + (193448324471 / 900000) * c * t ^ 7 + (-99964445657 / 900000) * c * t ^ 9 + (12503710289 / 360000) * c * t ^ 11 + (-144916951619 / 27000000) * c * t ^ 13 + (3187070239 / 2250000) * c * t ^ 15 + (-392800213 / 6750000) * c * t ^ 17 + (-1537928419 / 81000000) * c * t ^ 19 + (-832324727 / 27000000) * c * t ^ 21 + (-7900291 / 2250000) * c * t ^ 25 + (-168834) * alpha * t + (6684964 / 25) * alpha * t ^ 3 + (-3971111 / 80) * alpha * t ^ 5 + (-49304257927 / 1440000) * alpha * t ^ 7 + (-459572229143 / 14400000) * alpha * t ^ 9 + (271902957709 / 14400000) * alpha * t ^ 11 + (-5919559220929 / 432000000) * alpha * t ^ 13 + (40914635023 / 4500000) * alpha * t ^ 15 + (401935860053 / 432000000) * alpha * t ^ 17 + (143687890549 / 648000000) * alpha * t ^ 19 + (18494395697 / 432000000) * alpha * t ^ 21 + (2067088351 / 51840000) * alpha * t ^ 25 + (745184 / 25) * alpha * c * t ^ 3 + (-27592612 / 375) * alpha * c * t ^ 5 + (1473065687 / 25000) * alpha * c * t ^ 7 + (-3996492869 / 225000) * alpha * c * t ^ 9 + (2099111941 / 450000) * alpha * c * t ^ 11 + (-3418350593 / 2250000) * alpha * c * t ^ 13 + (-749633513 / 1687500) * alpha * c * t ^ 15 + (-39572317 / 421875) * alpha * c * t ^ 17 + (-1640800123 / 20250000) * alpha * c * t ^ 19 + (22931729 / 270000) * alpha * c * t ^ 21 + (1516972 / 1265625) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_01, v26_02, v26_03, v26_10, v26_11, v26_12, v26_13, v26_20, v26_21, v26_22, v26_23, v26_30, v26_31, v26_32, v26_33, v26_40, v26_41, v26_42, v26_43]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_10, phase27_11, phase27_12, phase27_13, phase27_20, phase27_21, phase27_22, phase27_23, phase27_30, phase27_31, phase27_32, phase27_33, phase27_40, phase27_41, phase27_42, phase27_43]
  try simp only [star_one, star_neg]
  linear_combination ((-186296 / 25) * t ^ 3 + (532597 / 75) * t ^ 5 + (1016433149 / 180000) * t ^ 7 + (-1030961423 / 180000) * t ^ 9 + (-15694537 / 40000) * t ^ 11 + (20329594579 / 27000000) * t ^ 13 + (185883173 / 6750000) * t ^ 15 + (18353387 / 281250) * t ^ 17 + (-9405317 / 81000000) * t ^ 19 + (-22814993 / 1080000) * t ^ 21 + (-1112293 / 1265625) * t ^ 25 + (20416 / 75) * c * t ^ 3 + (-239953 / 750) * c * t ^ 5 + (-856399 / 27000) * c * t ^ 7 + (41358689 / 1350000) * c * t ^ 9 + (16316957 / 168750) * c * t ^ 11 + (-225896921 / 5062500) * c * t ^ 13 + (22894673 / 3375000) * c * t ^ 15 + (-37434877 / 20250000) * c * t ^ 17 + (3483097 / 3037500) * c * t ^ 19 + (-412837 / 10125000) * c * t ^ 21 + (-86359 / 1687500) * c * t ^ 25 + (87016 / 3375) * c ^ 2 * t ^ 7 + (-716111 / 16875) * c ^ 2 * t ^ 9 + (540418 / 28125) * c ^ 2 * t ^ 11 + (-234233 / 84375) * c ^ 2 * t ^ 13 + (8068 / 84375) * c ^ 2 * t ^ 15 + (20132 / 253125) * c ^ 2 * t ^ 17 + (21316 / 253125) * c ^ 2 * t ^ 19 + (-2 / 45) * c ^ 2 * t ^ 21) * alpha_sq + ((-124264 / 375) * t ^ 5 + (464029 / 1250) * t ^ 7 + (2132783 / 22500) * t ^ 9 + (-16760941 / 112500) * t ^ 11 + (-6240557 / 337500) * t ^ 13 + (2311009 / 67500) * t ^ 15 + (-40864 / 84375) * t ^ 17 + (-100046 / 84375) * t ^ 19 + (4 / 15) * t ^ 21 + (20416 / 75) * alpha * t ^ 3 + (-135193 / 750) * alpha * t ^ 5 + (-20761991 / 135000) * alpha * t ^ 7 + (100047677 / 1350000) * alpha * t ^ 9 + (40678079 / 1350000) * alpha * t ^ 11 + (-176638607 / 10125000) * alpha * t ^ 13 + (89546531 / 6750000) * alpha * t ^ 15 + (914551 / 2531250) * alpha * t ^ 17 + (-9253531 / 15187500) * alpha * t ^ 19 + (3375023 / 20250000) * alpha * t ^ 21 + (41464 / 3796875) * alpha * t ^ 25) * c_sq
theorem v27_44 (t : ℂ) : (momentPoly 27 z27 4 4).eval t = (11396295 + (-85547672 / 5) * t ^ 2 + (-1001677651 / 100) * t ^ 4 + (209070602389 / 7500) * t ^ 6 + (-1808387305178551 / 144000000) * t ^ 8 + (5928579179573 / 12000000) * t ^ 10 + (-14837542545227 / 48000000) * t ^ 12 + (61977306771397 / 216000000) * t ^ 14 + (-26514619120591 / 576000000) * t ^ 16 + (308622597233 / 4800000) * t ^ 18 + (-49216388419319 / 2160000000) * t ^ 20 + (8193700509913 / 360000000) * t ^ 22 + (-33187218415609 / 4320000000) * t ^ 24 + (-1280354957509 / 3240000000) * t ^ 26 + (4404878324653 / 25920000000) * t ^ 32 + (-17188288 / 75) * c * t ^ 4 + (905373184 / 1875) * c * t ^ 6 + (-9593917189 / 46875) * c * t ^ 8 + (-16401168964 / 140625) * c * t ^ 10 + (1273003683 / 31250) * c * t ^ 12 + (38955866017 / 843750) * c * t ^ 14 + (-2659225369 / 93750) * c * t ^ 16 + (7496801357 / 843750) * c * t ^ 18 + (11906907361 / 12656250) * c * t ^ 20 + (-2614807249 / 4218750) * c * t ^ 22 + (11618551 / 4218750) * c * t ^ 24 + (-1717448711 / 12656250) * c * t ^ 26 + (-11757088 / 6328125) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z27, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v26_00, v26_01, v26_02, v26_03, v26_04, v26_10, v26_11, v26_12, v26_13, v26_14, v26_20, v26_21, v26_22, v26_23, v26_24, v26_30, v26_31, v26_32, v26_33, v26_34, v26_40, v26_41, v26_42, v26_43, v26_44]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04, phase27_10, phase27_11, phase27_12, phase27_13, phase27_14, phase27_20, phase27_21, phase27_22, phase27_23, phase27_24, phase27_30, phase27_31, phase27_32, phase27_33, phase27_34, phase27_40, phase27_41, phase27_42, phase27_43, phase27_44]
  try simp only [star_one, star_neg]
  linear_combination ((-1062704 / 15) * t ^ 2 + (7048964 / 75) * t ^ 4 + (-44610002 / 1875) * t ^ 6 + (27978078491 / 1500000) * t ^ 8 + (-212659511401 / 9000000) * t ^ 10 + (4194629327 / 3000000) * t ^ 12 + (-817986151481 / 162000000) * t ^ 14 + (17330176727 / 3375000) * t ^ 16 + (-29766356677 / 54000000) * t ^ 18 + (1899820073 / 9000000) * t ^ 20 + (-402076021 / 54000000) * t ^ 22 + (3028434697 / 162000000) * t ^ 26 + (4297072 / 225) * c * t ^ 4 + (-85972592 / 1875) * c * t ^ 6 + (5982638563 / 187500) * c * t ^ 8 + (-1434789188 / 421875) * c * t ^ 10 + (-42741967 / 1125000) * c * t ^ 12 + (-3774520819 / 1687500) * c * t ^ 14 + (7404544739 / 10125000) * c * t ^ 16 + (-535857611 / 2531250) * c * t ^ 18 + (-8193449479 / 151875000) * c * t ^ 20 + (445628681 / 8437500) * c * t ^ 22 + (11618551 / 50625000) * c * t ^ 24 + (23514176 / 6328125) * c * t ^ 26 + (-2939272 / 18984375) * c * t ^ 32 + (96704 / 675) * c ^ 2 * t ^ 6 + (-6718424 / 50625) * c ^ 2 * t ^ 8 + (-947801 / 28125) * c ^ 2 * t ^ 10 + (681791 / 28125) * c ^ 2 * t ^ 12 + (2317457 / 101250) * c ^ 2 * t ^ 14 + (-13611649 / 1012500) * c ^ 2 * t ^ 16 + (623473 / 101250) * c ^ 2 * t ^ 18 + (2305924 / 18984375) * c ^ 2 * t ^ 20 + (-744712 / 2109375) * c ^ 2 * t ^ 22 + (10418063 / 75937500) * c ^ 2 * t ^ 24 + (10500758 / 56953125) * c ^ 2 * t ^ 26 + (170528 / 56953125) * c ^ 2 * t ^ 32) * alpha_sq + ((-1062704 / 15) * t ^ 2 + (10610236 / 75) * t ^ 4 + (-666694658 / 5625) * t ^ 6 + (519789501539 / 6750000) * t ^ 8 + (-34806223681 / 750000) * t ^ 10 + (70937262691 / 4500000) * t ^ 12 + (-114559737071 / 40500000) * t ^ 14 + (2880430997 / 3375000) * t ^ 16 + (-119289683 / 1687500) * t ^ 18 + (-5099855093 / 202500000) * t ^ 20 + (-684174013 / 67500000) * t ^ 22 + (-10418063 / 25312500) * t ^ 24 + (-333820487 / 75937500) * t ^ 26 + (-170528 / 18984375) * t ^ 32) * c_sq
#print axioms v27_00
#print axioms v27_11
#print axioms v27_22
#print axioms v27_33
#print axioms v27_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
noncomputable def z28 : Fin 28 → ℂ := Fin.snoc z27 (r ^ 2 * thetaMinus)
theorem v28_00 (t : ℂ) : (momentPoly 28 z28 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00]
  try simp only [phase27_00]
  try simp only [star_one, star_neg]
  ring
theorem v28_01 (t : ℂ) : (momentPoly 28 z28 0 1).eval t = ((-1 / 5) * c * t + (7 / 15) * alpha * t) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_01]
  try simp only [phase27_00, phase27_01]
  try simp only [star_one, star_neg]
  ring
theorem v28_02 (t : ℂ) : (momentPoly 28 z28 0 2).eval t = ((-1391 / 300) * t ^ 2 + (3859 / 300) * t ^ 4 + (73 / 15) * alpha * t ^ 2 + (-73 / 15) * alpha * t ^ 4 + (-4 / 25) * alpha * c * t ^ 2 + (-2 / 75) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_01, v27_02]
  try simp only [phase27_00, phase27_01, phase27_02]
  try simp only [star_one, star_neg]
  linear_combination ((4 / 75) * t ^ 2) * alpha_sq + ((-8 / 225) * t ^ 2) * c_sq
theorem v28_03 (t : ℂ) : (momentPoly 28 z28 0 3).eval t = ((-461 / 25) * t ^ 3 + (436 / 25) * t ^ 5 + 1 * t ^ 9 + (1753 / 300) * c * t ^ 3 + (-3519 / 500) * c * t ^ 5 + (-71 / 375) * c * t ^ 9 + (-461 / 600) * alpha * t ^ 3 + (51377 / 6000) * alpha * t ^ 5 + (77987 / 18000) * alpha * t ^ 9 + (-73 / 25) * alpha * c * t ^ 3 + (73 / 25) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_01, v27_02, v27_03]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-8 / 225) * c * t ^ 3 + (4 / 1125) * c * t ^ 5) * alpha_sq + ((-8 / 225) * alpha * t ^ 3 + (-16 / 1125) * alpha * t ^ 5) * c_sq
theorem v28_04 (t : ℂ) : (momentPoly 28 z28 0 4).eval t = ((-4137331 / 12000) * t ^ 4 + (345637 / 2000) * t ^ 6 + (29332979 / 120000) * t ^ 8 + (-3642181 / 90000) * t ^ 10 + (4484849 / 360000) * t ^ 16 + (1552 / 125) * c * t ^ 4 + (-232 / 25) * c * t ^ 6 + (-292 / 125) * c * t ^ 8 + (-4 / 5) * c * t ^ 10 + (-317 / 2) * alpha * t ^ 4 + (209657 / 375) * alpha * t ^ 6 + (-291773 / 750) * alpha * t ^ 8 + (-18032 / 1125) * alpha * t ^ 10 + (5033 / 1125) * alpha * t ^ 16 + (7349 / 2250) * alpha * c * t ^ 4 + (-1157 / 1500) * alpha * c * t ^ 6 + (-1189 / 625) * alpha * c * t ^ 8 + (-27089 / 7500) * alpha * c * t ^ 10 + (-292 / 5625) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_01, v27_02, v27_03, v27_04]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04]
  try simp only [star_one, star_neg]
  linear_combination ((773 / 450) * t ^ 4 + (9809 / 4500) * t ^ 6 + (31889 / 22500) * t ^ 10 + (-1168 / 1125) * c * t ^ 4 + (292 / 225) * c * t ^ 6 + (-292 / 1125) * c * t ^ 8 + (-32 / 3375) * c ^ 2 * t ^ 6 + (-32 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((1516 / 1125) * t ^ 4 + (-284 / 125) * t ^ 6 + (32 / 5625) * t ^ 8 + (-2272 / 16875) * t ^ 10 + (-1168 / 1125) * alpha * t ^ 4 + (1168 / 1125) * alpha * t ^ 6) * c_sq
theorem v28_10 (t : ℂ) : (momentPoly 28 z28 1 0).eval t = ((-1 / 5) * c * t + (-7 / 15) * alpha * t) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_10]
  try simp only [phase27_00, phase27_10]
  try simp only [star_one, star_neg]
  ring
theorem v28_11 (t : ℂ) : (momentPoly 28 z28 1 1).eval t = (28 + (-277 / 15) * t ^ 2) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_01, v27_10, v27_11]
  try simp only [phase27_00, phase27_01, phase27_10, phase27_11]
  try simp only [star_one, star_neg]
  linear_combination ((-4 / 75) * t ^ 2) * alpha_sq + ((-8 / 225) * t ^ 2) * c_sq
theorem v28_12 (t : ℂ) : (momentPoly 28 z28 1 2).eval t = ((511 / 75) * t ^ 3 + (-511 / 75) * t ^ 5 + (-11) * c * t + (3451 / 300) * c * t ^ 3 + (-241 / 100) * c * t ^ 5 + (77 / 3) * alpha * t + (-14339 / 900) * alpha * t ^ 3 + (-4757 / 900) * alpha * t ^ 5 + (-73 / 75) * alpha * c * t ^ 3 + (73 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_01, v27_02, v27_10, v27_11, v27_12]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_10, phase27_11, phase27_12]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 225) * t ^ 3 + (73 / 225) * t ^ 5 + (8 / 675) * c * t ^ 3 + (-4 / 3375) * c * t ^ 5) * alpha_sq + ((-8 / 675) * alpha * t ^ 3 + (-16 / 3375) * alpha * t ^ 5) * c_sq
theorem v28_13 (t : ℂ) : (momentPoly 28 z28 1 3).eval t = ((-37557 / 100) * t ^ 2 + (3467801 / 3000) * t ^ 4 + (-4221269 / 6000) * t ^ 6 + (28957 / 18000) * t ^ 10 + (-2 / 5) * c * t ^ 4 + (3 / 5) * c * t ^ 6 + (-1 / 5) * c * t ^ 10 + (1971 / 5) * alpha * t ^ 2 + (-48031 / 75) * alpha * t ^ 4 + (18136 / 75) * alpha * t ^ 6 + (22 / 5) * alpha * t ^ 10 + (-324 / 25) * alpha * c * t ^ 2 + (69481 / 9000) * alpha * c * t ^ 4 + (25271 / 6000) * alpha * c * t ^ 6 + (-1503 / 2000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_01, v27_02, v27_03, v27_10, v27_11, v27_12, v27_13]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_10, phase27_11, phase27_12, phase27_13]
  try simp only [star_one, star_neg]
  linear_combination ((108 / 25) * t ^ 2 + (-24821 / 9000) * t ^ 4 + (-6931 / 6000) * t ^ 6 + (-31889 / 90000) * t ^ 10) * alpha_sq + ((-72 / 25) * t ^ 2 + (1082 / 375) * t ^ 4 + (-262 / 225) * t ^ 6 + (-568 / 16875) * t ^ 10 + (-584 / 1125) * alpha * t ^ 4 + (584 / 1125) * alpha * t ^ 6) * c_sq
theorem v28_14 (t : ℂ) : (momentPoly 28 z28 1 4).eval t = ((-48866 / 25) * t ^ 3 + (11035211 / 3750) * t ^ 5 + (-953191 / 1875) * t ^ 7 + (-1375517 / 3750) * t ^ 9 + (-664724 / 5625) * t ^ 11 + (29606 / 5625) * t ^ 17 + (92909 / 150) * c * t ^ 3 + (-227919079 / 180000) * c * t ^ 5 + (19837453 / 30000) * c * t ^ 7 + (-6973559 / 120000) * c * t ^ 9 + (2958221 / 90000) * c * t ^ 11 + (-94997 / 40000) * c * t ^ 17 + (-24433 / 300) * alpha * t ^ 3 + (60707203 / 60000) * alpha * t ^ 5 + (-9323261 / 10000) * alpha * t ^ 7 + (51062737 / 120000) * alpha * t ^ 9 + (-81023449 / 270000) * alpha * t ^ 11 + (-8468767 / 1080000) * alpha * t ^ 17 + (-7738 / 25) * alpha * c * t ^ 3 + (789149 / 1250) * alpha * c * t ^ 5 + (-246029 / 625) * alpha * c * t ^ 7 + (273961 / 3750) * alpha * c * t ^ 9 + (-1768 / 5625) * alpha * c * t ^ 11 + (-5033 / 5625) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_01, v27_02, v27_03, v27_04, v27_10, v27_11, v27_12, v27_13, v27_14]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04, phase27_10, phase27_11, phase27_12, phase27_13, phase27_14]
  try simp only [star_one, star_neg]
  linear_combination ((7738 / 75) * t ^ 3 + (-1617313 / 11250) * t ^ 5 + (1821 / 125) * t ^ 7 + (270457 / 11250) * t ^ 9 + (38432 / 16875) * t ^ 11 + (-5033 / 16875) * t ^ 17 + (-848 / 225) * c * t ^ 3 + (49388 / 16875) * c * t ^ 5 + (1978 / 3375) * c * t ^ 7 + (-14 / 1875) * c * t ^ 9 + (2272 / 50625) * c * t ^ 11 + (-584 / 253125) * c * t ^ 17 + (-1168 / 16875) * c ^ 2 * t ^ 7 + (1168 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((848 / 1125) * t ^ 5 + (-368 / 1875) * t ^ 7 + (-2336 / 5625) * t ^ 9 + (-32 / 225) * t ^ 11 + (-848 / 225) * alpha * t ^ 3 + (392 / 375) * alpha * t ^ 5 + (10766 / 5625) * alpha * t ^ 7 + (-5272 / 16875) * alpha * t ^ 9 + (-28366 / 50625) * alpha * t ^ 11 + (-2336 / 253125) * alpha * t ^ 17) * c_sq
theorem v28_20 (t : ℂ) : (momentPoly 28 z28 2 0).eval t = ((-1391 / 300) * t ^ 2 + (3859 / 300) * t ^ 4 + (-73 / 15) * alpha * t ^ 2 + (73 / 15) * alpha * t ^ 4 + (4 / 25) * alpha * c * t ^ 2 + (2 / 75) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_10, v27_20]
  try simp only [phase27_00, phase27_10, phase27_20]
  try simp only [star_one, star_neg]
  linear_combination ((4 / 75) * t ^ 2) * alpha_sq + ((-8 / 225) * t ^ 2) * c_sq
theorem v28_21 (t : ℂ) : (momentPoly 28 z28 2 1).eval t = ((511 / 75) * t ^ 3 + (-511 / 75) * t ^ 5 + (-11) * c * t + (3451 / 300) * c * t ^ 3 + (-241 / 100) * c * t ^ 5 + (-77 / 3) * alpha * t + (14339 / 900) * alpha * t ^ 3 + (4757 / 900) * alpha * t ^ 5 + (73 / 75) * alpha * c * t ^ 3 + (-73 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_01, v27_10, v27_11, v27_20, v27_21]
  try simp only [phase27_00, phase27_01, phase27_10, phase27_11, phase27_20, phase27_21]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 225) * t ^ 3 + (73 / 225) * t ^ 5 + (8 / 675) * c * t ^ 3 + (-4 / 3375) * c * t ^ 5) * alpha_sq + ((8 / 675) * alpha * t ^ 3 + (16 / 3375) * alpha * t ^ 5) * c_sq
theorem v28_22 (t : ℂ) : (momentPoly 28 z28 2 2).eval t = (1540 + (-9972 / 5) * t ^ 2 + (9326429 / 18000) * t ^ 4 + (-327317 / 1800) * t ^ 6 + (3761861 / 18000) * t ^ 8 + (-584 / 125) * c * t ^ 4 + (292 / 75) * c * t ^ 6 + (292 / 375) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_01, v27_02, v27_10, v27_11, v27_12, v27_20, v27_21, v27_22]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_10, phase27_11, phase27_12, phase27_20, phase27_21, phase27_22]
  try simp only [star_one, star_neg]
  linear_combination ((-144 / 25) * t ^ 2 + (10478 / 3375) * t ^ 4 + (2746 / 3375) * t ^ 6 + (1168 / 3375) * c * t ^ 4 + (-292 / 675) * c * t ^ 6 + (292 / 3375) * c * t ^ 8 + (32 / 10125) * c ^ 2 * t ^ 6 + (32 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((-96 / 25) * t ^ 2 + (11468 / 3375) * t ^ 4 + (-2684 / 3375) * t ^ 6 + (-32 / 16875) * t ^ 8) * c_sq
theorem v28_23 (t : ℂ) : (momentPoly 28 z28 2 3).eval t = ((27083 / 25) * t ^ 3 + (-1733509 / 1000) * t ^ 5 + (5604357 / 10000) * t ^ 7 + (2036999 / 30000) * t ^ 9 + (6502151 / 90000) * t ^ 11 + (-4535351 / 90000) * t ^ 13 + (-4456 / 5) * c * t + (182903 / 100) * c * t ^ 3 + (-120642011 / 90000) * c * t ^ 5 + (22222931 / 45000) * c * t ^ 7 + (-132503 / 1200) * c * t ^ 9 + (8141 / 2250) * c * t ^ 11 + (-38731 / 15000) * c * t ^ 13 + (31192 / 15) * alpha * t + (-759967 / 300) * alpha * t ^ 3 + (-22658773 / 180000) * alpha * t ^ 5 + (54328453 / 120000) * alpha * t ^ 7 + (47308663 / 360000) * alpha * t ^ 9 + (-22798313 / 1080000) * alpha * t ^ 11 + (12746369 / 216000) * alpha * t ^ 13 + (-3869 / 25) * alpha * c * t ^ 3 + (64093 / 225) * alpha * c * t ^ 5 + (-726706 / 5625) * alpha * c * t ^ 7 + (534 / 625) * alpha * c * t ^ 9 + (-4867 / 5625) * alpha * c * t ^ 11 + (-5033 / 5625) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_01, v27_02, v27_03, v27_10, v27_11, v27_12, v27_13, v27_20, v27_21, v27_22, v27_23]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_10, phase27_11, phase27_12, phase27_13, phase27_20, phase27_21, phase27_22, phase27_23]
  try simp only [star_one, star_neg]
  linear_combination ((-3869 / 75) * t ^ 3 + (78011 / 1125) * t ^ 5 + (-19306 / 1125) * t ^ 7 + (-26183 / 16875) * t ^ 11 + (16133 / 16875) * t ^ 13 + (424 / 225) * c * t ^ 3 + (-8269 / 5625) * c * t ^ 5 + (-24107 / 67500) * c * t ^ 7 + (47 / 5400) * c * t ^ 9 + (16583 / 101250) * c * t ^ 11 + (-60307 / 2025000) * c * t ^ 13 + (1168 / 16875) * c ^ 2 * t ^ 7 + (-1168 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((-416 / 375) * t ^ 5 + (456 / 625) * t ^ 7 + (2336 / 5625) * t ^ 9 + (-8 / 225) * t ^ 11 + (-424 / 225) * alpha * t ^ 3 + (8707 / 16875) * alpha * t ^ 5 + (30551 / 33750) * alpha * t ^ 7 + (-32 / 16875) * alpha * t ^ 9 + (-11911 / 101250) * alpha * t ^ 11 + (1136 / 253125) * alpha * t ^ 13) * c_sq
theorem v28_24 (t : ℂ) : (momentPoly 28 z28 2 4).eval t = ((-1194869 / 30) * t ^ 2 + (201409669 / 1500) * t ^ 4 + (-159035902561 / 1200000) * t ^ 6 + (139996517813 / 3600000) * t ^ 8 + (-41851306789 / 7200000) * t ^ 10 + (126913760731 / 21600000) * t ^ 12 + (-45422267 / 216000) * t ^ 14 + (42630473 / 4320000) * t ^ 18 + (1792621831 / 21600000) * t ^ 20 + (-416 / 5) * c * t ^ 4 + (15153637 / 56250) * c * t ^ 6 + (-25367609 / 112500) * c * t ^ 8 + (-383077 / 12500) * c * t ^ 10 + (343981 / 12500) * c * t ^ 12 + (5009047 / 112500) * c * t ^ 14 + (-70462 / 28125) * c * t ^ 18 + (2 / 5) * c * t ^ 20 + (125414 / 3) * alpha * t ^ 2 + (-6978103 / 75) * alpha * t ^ 4 + (55956973003 / 900000) * alpha * t ^ 6 + (-12552607033 / 900000) * alpha * t ^ 8 + (12109900169 / 1800000) * alpha * t ^ 10 + (-17852564371 / 5400000) * alpha * t ^ 12 + (-40043651 / 90000) * alpha * t ^ 14 + (-6492379 / 72000) * alpha * t ^ 18 + (664431529 / 5400000) * alpha * t ^ 20 + (-6872 / 5) * alpha * c * t ^ 2 + (2054096 / 1125) * alpha * c * t ^ 4 + (34579651 / 337500) * alpha * c * t ^ 6 + (-342063067 / 675000) * alpha * c * t ^ 8 + (-35948653 / 225000) * alpha * c * t ^ 10 + (126004061 / 900000) * alpha * c * t ^ 12 + (-64512643 / 1350000) * alpha * c * t ^ 14 + (5044897 / 1350000) * alpha * c * t ^ 18 + (-55597 / 180000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_01, v27_02, v27_03, v27_04, v27_10, v27_11, v27_12, v27_13, v27_14, v27_20, v27_21, v27_22, v27_23, v27_24]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04, phase27_10, phase27_11, phase27_12, phase27_13, phase27_14, phase27_20, phase27_21, phase27_22, phase27_23, phase27_24]
  try simp only [star_one, star_neg]
  linear_combination ((6872 / 15) * t ^ 2 + (-645346 / 1125) * t ^ 4 + (-14028019 / 168750) * t ^ 6 + (260878531 / 1350000) * t ^ 8 + (-13958479 / 225000) * t ^ 10 + (134591107 / 4050000) * t ^ 12 + (65495161 / 4050000) * t ^ 14 + (2518513 / 4050000) * t ^ 18 + (-625868 / 84375) * c * t ^ 6 + (1591523 / 84375) * c * t ^ 8 + (-1209514 / 84375) * c * t ^ 10 + (334457 / 84375) * c * t ^ 12 + (-100664 / 84375) * c * t ^ 14 + (6316 / 84375) * c * t ^ 18 + (2 / 45) * c * t ^ 20 + (-452 / 253125) * c ^ 2 * t ^ 8 + (-154 / 84375) * c ^ 2 * t ^ 10 + (1048 / 50625) * c ^ 2 * t ^ 12 + (30638 / 759375) * c ^ 2 * t ^ 14 + (2336 / 759375) * c ^ 2 * t ^ 18 + (4672 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-13744 / 45) * t ^ 2 + (225056 / 375) * t ^ 4 + (-57452171 / 112500) * t ^ 6 + (37619093 / 168750) * t ^ 8 + (-31243103 / 675000) * t ^ 10 + (4273169 / 506250) * t ^ 12 + (-433316 / 253125) * t ^ 14 + (-805501 / 2025000) * t ^ 18 + (-4672 / 1265625) * t ^ 20 + (-121472 / 1125) * alpha * t ^ 4 + (16433228 / 84375) * alpha * t ^ 6 + (-8313736 / 84375) * alpha * t ^ 8 + (39068 / 3125) * alpha * t ^ 10 + (9536 / 253125) * alpha * t ^ 12 + (-161056 / 253125) * alpha * t ^ 14 + (-40264 / 253125) * alpha * t ^ 18) * c_sq
theorem v28_30 (t : ℂ) : (momentPoly 28 z28 3 0).eval t = ((-461 / 25) * t ^ 3 + (436 / 25) * t ^ 5 + 1 * t ^ 9 + (1753 / 300) * c * t ^ 3 + (-3519 / 500) * c * t ^ 5 + (-71 / 375) * c * t ^ 9 + (461 / 600) * alpha * t ^ 3 + (-51377 / 6000) * alpha * t ^ 5 + (-77987 / 18000) * alpha * t ^ 9 + (73 / 25) * alpha * c * t ^ 3 + (-73 / 25) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_10, v27_20, v27_30]
  try simp only [phase27_00, phase27_10, phase27_20, phase27_30]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-8 / 225) * c * t ^ 3 + (4 / 1125) * c * t ^ 5) * alpha_sq + ((8 / 225) * alpha * t ^ 3 + (16 / 1125) * alpha * t ^ 5) * c_sq
theorem v28_31 (t : ℂ) : (momentPoly 28 z28 3 1).eval t = ((-37557 / 100) * t ^ 2 + (3467801 / 3000) * t ^ 4 + (-4221269 / 6000) * t ^ 6 + (28957 / 18000) * t ^ 10 + (-2 / 5) * c * t ^ 4 + (3 / 5) * c * t ^ 6 + (-1 / 5) * c * t ^ 10 + (-1971 / 5) * alpha * t ^ 2 + (48031 / 75) * alpha * t ^ 4 + (-18136 / 75) * alpha * t ^ 6 + (-22 / 5) * alpha * t ^ 10 + (324 / 25) * alpha * c * t ^ 2 + (-69481 / 9000) * alpha * c * t ^ 4 + (-25271 / 6000) * alpha * c * t ^ 6 + (1503 / 2000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_01, v27_10, v27_11, v27_20, v27_21, v27_30, v27_31]
  try simp only [phase27_00, phase27_01, phase27_10, phase27_11, phase27_20, phase27_21, phase27_30, phase27_31]
  try simp only [star_one, star_neg]
  linear_combination ((108 / 25) * t ^ 2 + (-24821 / 9000) * t ^ 4 + (-6931 / 6000) * t ^ 6 + (-31889 / 90000) * t ^ 10) * alpha_sq + ((-72 / 25) * t ^ 2 + (1082 / 375) * t ^ 4 + (-262 / 225) * t ^ 6 + (-568 / 16875) * t ^ 10 + (584 / 1125) * alpha * t ^ 4 + (-584 / 1125) * alpha * t ^ 6) * c_sq
theorem v28_32 (t : ℂ) : (momentPoly 28 z28 3 2).eval t = ((27083 / 25) * t ^ 3 + (-1733509 / 1000) * t ^ 5 + (5604357 / 10000) * t ^ 7 + (2036999 / 30000) * t ^ 9 + (6502151 / 90000) * t ^ 11 + (-4535351 / 90000) * t ^ 13 + (-4456 / 5) * c * t + (182903 / 100) * c * t ^ 3 + (-120642011 / 90000) * c * t ^ 5 + (22222931 / 45000) * c * t ^ 7 + (-132503 / 1200) * c * t ^ 9 + (8141 / 2250) * c * t ^ 11 + (-38731 / 15000) * c * t ^ 13 + (-31192 / 15) * alpha * t + (759967 / 300) * alpha * t ^ 3 + (22658773 / 180000) * alpha * t ^ 5 + (-54328453 / 120000) * alpha * t ^ 7 + (-47308663 / 360000) * alpha * t ^ 9 + (22798313 / 1080000) * alpha * t ^ 11 + (-12746369 / 216000) * alpha * t ^ 13 + (3869 / 25) * alpha * c * t ^ 3 + (-64093 / 225) * alpha * c * t ^ 5 + (726706 / 5625) * alpha * c * t ^ 7 + (-534 / 625) * alpha * c * t ^ 9 + (4867 / 5625) * alpha * c * t ^ 11 + (5033 / 5625) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_01, v27_02, v27_10, v27_11, v27_12, v27_20, v27_21, v27_22, v27_30, v27_31, v27_32]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_10, phase27_11, phase27_12, phase27_20, phase27_21, phase27_22, phase27_30, phase27_31, phase27_32]
  try simp only [star_one, star_neg]
  linear_combination ((-3869 / 75) * t ^ 3 + (78011 / 1125) * t ^ 5 + (-19306 / 1125) * t ^ 7 + (-26183 / 16875) * t ^ 11 + (16133 / 16875) * t ^ 13 + (424 / 225) * c * t ^ 3 + (-8269 / 5625) * c * t ^ 5 + (-24107 / 67500) * c * t ^ 7 + (47 / 5400) * c * t ^ 9 + (16583 / 101250) * c * t ^ 11 + (-60307 / 2025000) * c * t ^ 13 + (1168 / 16875) * c ^ 2 * t ^ 7 + (-1168 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((-416 / 375) * t ^ 5 + (456 / 625) * t ^ 7 + (2336 / 5625) * t ^ 9 + (-8 / 225) * t ^ 11 + (424 / 225) * alpha * t ^ 3 + (-8707 / 16875) * alpha * t ^ 5 + (-30551 / 33750) * alpha * t ^ 7 + (32 / 16875) * alpha * t ^ 9 + (11911 / 101250) * alpha * t ^ 11 + (-1136 / 253125) * alpha * t ^ 13) * c_sq
theorem v28_33 (t : ℂ) : (momentPoly 28 z28 3 3).eval t = (124768 + (-237943) * t ^ 2 + (121243577 / 1000) * t ^ 4 + (-1038945851 / 24000) * t ^ 6 + (13746329457 / 200000) * t ^ 8 + (-77724194611 / 2400000) * t ^ 10 + (-4570159 / 1800000) * t ^ 12 + (-42340993 / 144000) * t ^ 14 + (805088501 / 21600000) * t ^ 18 + (-136656 / 125) * c * t ^ 4 + (12973733 / 7500) * c * t ^ 6 + (-4576937 / 15000) * c * t ^ 8 + (-1563563 / 5000) * c * t ^ 10 + (-1033771 / 15000) * c * t ^ 12 + (252777 / 5000) * c * t ^ 14 + (-142 / 375) * c * t ^ 18) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_01, v27_02, v27_03, v27_10, v27_11, v27_12, v27_13, v27_20, v27_21, v27_22, v27_23, v27_30, v27_31, v27_32, v27_33]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_10, phase27_11, phase27_12, phase27_13, phase27_20, phase27_21, phase27_22, phase27_23, phase27_30, phase27_31, phase27_32, phase27_33]
  try simp only [star_one, star_neg]
  linear_combination ((-3436 / 5) * t ^ 2 + (272428 / 375) * t ^ 4 + (494047 / 18000) * t ^ 6 + (-56805727 / 900000) * t ^ 8 + (-27977407 / 900000) * t ^ 10 + (-12669983 / 2700000) * t ^ 12 + (-7161829 / 300000) * t ^ 14 + (-5484557 / 3375000) * t ^ 18 + (30368 / 375) * c * t ^ 4 + (-905708 / 5625) * c * t ^ 6 + (162292 / 1875) * c * t ^ 8 + (-40708 / 5625) * c * t ^ 10 + (752 / 375) * c * t ^ 12 + (-484 / 375) * c * t ^ 14 + (2528 / 3375) * c ^ 2 * t ^ 6 + (-30374 / 84375) * c ^ 2 * t ^ 8 + (-20599 / 84375) * c ^ 2 * t ^ 10 + (4349 / 84375) * c ^ 2 * t ^ 14) * alpha_sq + ((-6872 / 15) * t ^ 2 + (298168 / 375) * t ^ 4 + (-5890877 / 11250) * t ^ 6 + (1915756 / 9375) * t ^ 8 + (-2898329 / 56250) * t ^ 10 + (16573 / 9375) * t ^ 12 + (-212114 / 84375) * t ^ 14 + (-40328 / 1265625) * t ^ 18) * c_sq
theorem v28_34 (t : ℂ) : (momentPoly 28 z28 3 4).eval t = ((4228014 / 25) * t ^ 3 + (-184090297 / 500) * t ^ 5 + (65620712393 / 300000) * t ^ 7 + (-27146290709 / 1500000) * t ^ 9 + (68030990501 / 3000000) * t ^ 11 + (-6281240503 / 180000) * t ^ 13 + (1711085557 / 112500) * t ^ 15 + (-42057427709 / 9000000) * t ^ 17 + (-9974576311 / 27000000) * t ^ 19 + (302142337 / 750000) * t ^ 21 + (1906397959 / 27000000) * t ^ 25 + (-472663 / 5) * c * t + (14276787 / 50) * c * t ^ 3 + (-1763919337 / 5000) * c * t ^ 5 + (903148942141 / 3600000) * c * t ^ 7 + (-2165608788131 / 18000000) * c * t ^ 9 + (1269797527763 / 36000000) * c * t ^ 11 + (-611692325117 / 108000000) * c * t ^ 13 + (13660627013 / 9000000) * c * t ^ 15 + (-105991201 / 1800000) * c * t ^ 17 + (529716023 / 36000000) * c * t ^ 19 + (-250889927 / 7200000) * c * t ^ 21 + (-8500291 / 3000000) * c * t ^ 25 + (3308641 / 15) * alpha * t + (-19773481 / 50) * alpha * t ^ 3 + (2620984877 / 30000) * alpha * t ^ 5 + (82193921097 / 800000) * alpha * t ^ 7 + (332909356933 / 24000000) * alpha * t ^ 9 + (-492023020339 / 14400000) * alpha * t ^ 11 + (8627177785477 / 432000000) * alpha * t ^ 13 + (-349346536571 / 27000000) * alpha * t ^ 15 + (-577335850277 / 432000000) * alpha * t ^ 17 + (-1354563859 / 25920000) * alpha * t ^ 19 + (-46967386973 / 432000000) * alpha * t ^ 21 + (-12386197867 / 259200000) * alpha * t ^ 25 + (-604002 / 25) * alpha * c * t ^ 3 + (319923 / 5) * alpha * c * t ^ 5 + (-50741001149 / 900000) * alpha * c * t ^ 7 + (29001991537 / 1500000) * alpha * c * t ^ 9 + (-40711820699 / 9000000) * alpha * c * t ^ 11 + (1369012481 / 1080000) * alpha * c * t ^ 13 + (178636193 / 450000) * alpha * c * t ^ 15 + (42769717 / 562500) * alpha * c * t ^ 17 + (1958575163 / 27000000) * alpha * c * t ^ 19 + (-207013859 / 3000000) * alpha * c * t ^ 21 + (-379243 / 421875) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_01, v27_02, v27_03, v27_04, v27_10, v27_11, v27_12, v27_13, v27_14, v27_20, v27_21, v27_22, v27_23, v27_24, v27_30, v27_31, v27_32, v27_33, v27_34]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04, phase27_10, phase27_11, phase27_12, phase27_13, phase27_14, phase27_20, phase27_21, phase27_22, phase27_23, phase27_24, phase27_30, phase27_31, phase27_32, phase27_33, phase27_34]
  try simp only [star_one, star_neg]
  linear_combination ((-201334 / 25) * t ^ 3 + (5059387 / 375) * t ^ 5 + (-1144023829 / 300000) * t ^ 7 + (-6930202879 / 4500000) * t ^ 9 + (-9242619289 / 9000000) * t ^ 11 + (8915316929 / 9000000) * t ^ 13 + (-710664479 / 6750000) * t ^ 15 + (59770997 / 843750) * t ^ 17 + (783729211 / 81000000) * t ^ 19 + (-68600353 / 3000000) * t ^ 21 + (-1112293 / 1265625) * t ^ 25 + (22064 / 75) * c * t ^ 3 + (-2371534 / 5625) * c * t ^ 5 + (7428479 / 337500) * c * t ^ 7 + (66306377 / 843750) * c * t ^ 9 + (481760171 / 6750000) * c * t ^ 11 + (-524404321 / 10125000) * c * t ^ 13 + (234182929 / 20250000) * c * t ^ 15 + (-3101399 / 1350000) * c * t ^ 17 + (23971477 / 30375000) * c * t ^ 19 + (235639 / 4050000) * c * t ^ 21 + (-4402411 / 75937500) * c * t ^ 25 + (72416 / 3375) * c ^ 2 * t ^ 7 + (-5458276 / 140625) * c ^ 2 * t ^ 9 + (8280296 / 421875) * c ^ 2 * t ^ 11 + (-114356 / 46875) * c ^ 2 * t ^ 13 + (31472 / 421875) * c ^ 2 * t ^ 15 + (80528 / 1265625) * c ^ 2 * t ^ 17 + (85264 / 1265625) * c ^ 2 * t ^ 19 + (-8 / 225) * c ^ 2 * t ^ 21) * alpha_sq + ((-42432 / 125) * t ^ 5 + (2542766 / 5625) * t ^ 7 + (4289651 / 140625) * t ^ 9 + (-22346617 / 140625) * t ^ 11 + (-174823 / 15625) * t ^ 13 + (11905573 / 421875) * t ^ 15 + (-163456 / 421875) * t ^ 17 + (-146816 / 140625) * t ^ 19 + (16 / 75) * t ^ 21 + (-22064 / 75) * alpha * t ^ 3 + (1523234 / 5625) * alpha * t ^ 5 + (49913771 / 337500) * alpha * t ^ 7 + (-70202653 / 562500) * alpha * t ^ 9 + (-17144539 / 675000) * alpha * t ^ 11 + (27953527 / 1265625) * alpha * t ^ 13 + (-65103953 / 5062500) * alpha * t ^ 15 + (-400406 / 1265625) * alpha * t ^ 17 + (24159407 / 30375000) * alpha * t ^ 19 + (-743267 / 5062500) * alpha * t ^ 21 + (-165856 / 18984375) * alpha * t ^ 25) * c_sq
theorem v28_40 (t : ℂ) : (momentPoly 28 z28 4 0).eval t = ((-4137331 / 12000) * t ^ 4 + (345637 / 2000) * t ^ 6 + (29332979 / 120000) * t ^ 8 + (-3642181 / 90000) * t ^ 10 + (4484849 / 360000) * t ^ 16 + (1552 / 125) * c * t ^ 4 + (-232 / 25) * c * t ^ 6 + (-292 / 125) * c * t ^ 8 + (-4 / 5) * c * t ^ 10 + (317 / 2) * alpha * t ^ 4 + (-209657 / 375) * alpha * t ^ 6 + (291773 / 750) * alpha * t ^ 8 + (18032 / 1125) * alpha * t ^ 10 + (-5033 / 1125) * alpha * t ^ 16 + (-7349 / 2250) * alpha * c * t ^ 4 + (1157 / 1500) * alpha * c * t ^ 6 + (1189 / 625) * alpha * c * t ^ 8 + (27089 / 7500) * alpha * c * t ^ 10 + (292 / 5625) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_10, v27_20, v27_30, v27_40]
  try simp only [phase27_00, phase27_10, phase27_20, phase27_30, phase27_40]
  try simp only [star_one, star_neg]
  linear_combination ((773 / 450) * t ^ 4 + (9809 / 4500) * t ^ 6 + (31889 / 22500) * t ^ 10 + (-1168 / 1125) * c * t ^ 4 + (292 / 225) * c * t ^ 6 + (-292 / 1125) * c * t ^ 8 + (-32 / 3375) * c ^ 2 * t ^ 6 + (-32 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((1516 / 1125) * t ^ 4 + (-284 / 125) * t ^ 6 + (32 / 5625) * t ^ 8 + (-2272 / 16875) * t ^ 10 + (1168 / 1125) * alpha * t ^ 4 + (-1168 / 1125) * alpha * t ^ 6) * c_sq
theorem v28_41 (t : ℂ) : (momentPoly 28 z28 4 1).eval t = ((-48866 / 25) * t ^ 3 + (11035211 / 3750) * t ^ 5 + (-953191 / 1875) * t ^ 7 + (-1375517 / 3750) * t ^ 9 + (-664724 / 5625) * t ^ 11 + (29606 / 5625) * t ^ 17 + (92909 / 150) * c * t ^ 3 + (-227919079 / 180000) * c * t ^ 5 + (19837453 / 30000) * c * t ^ 7 + (-6973559 / 120000) * c * t ^ 9 + (2958221 / 90000) * c * t ^ 11 + (-94997 / 40000) * c * t ^ 17 + (24433 / 300) * alpha * t ^ 3 + (-60707203 / 60000) * alpha * t ^ 5 + (9323261 / 10000) * alpha * t ^ 7 + (-51062737 / 120000) * alpha * t ^ 9 + (81023449 / 270000) * alpha * t ^ 11 + (8468767 / 1080000) * alpha * t ^ 17 + (7738 / 25) * alpha * c * t ^ 3 + (-789149 / 1250) * alpha * c * t ^ 5 + (246029 / 625) * alpha * c * t ^ 7 + (-273961 / 3750) * alpha * c * t ^ 9 + (1768 / 5625) * alpha * c * t ^ 11 + (5033 / 5625) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_01, v27_10, v27_11, v27_20, v27_21, v27_30, v27_31, v27_40, v27_41]
  try simp only [phase27_00, phase27_01, phase27_10, phase27_11, phase27_20, phase27_21, phase27_30, phase27_31, phase27_40, phase27_41]
  try simp only [star_one, star_neg]
  linear_combination ((7738 / 75) * t ^ 3 + (-1617313 / 11250) * t ^ 5 + (1821 / 125) * t ^ 7 + (270457 / 11250) * t ^ 9 + (38432 / 16875) * t ^ 11 + (-5033 / 16875) * t ^ 17 + (-848 / 225) * c * t ^ 3 + (49388 / 16875) * c * t ^ 5 + (1978 / 3375) * c * t ^ 7 + (-14 / 1875) * c * t ^ 9 + (2272 / 50625) * c * t ^ 11 + (-584 / 253125) * c * t ^ 17 + (-1168 / 16875) * c ^ 2 * t ^ 7 + (1168 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((848 / 1125) * t ^ 5 + (-368 / 1875) * t ^ 7 + (-2336 / 5625) * t ^ 9 + (-32 / 225) * t ^ 11 + (848 / 225) * alpha * t ^ 3 + (-392 / 375) * alpha * t ^ 5 + (-10766 / 5625) * alpha * t ^ 7 + (5272 / 16875) * alpha * t ^ 9 + (28366 / 50625) * alpha * t ^ 11 + (2336 / 253125) * alpha * t ^ 17) * c_sq
theorem v28_42 (t : ℂ) : (momentPoly 28 z28 4 2).eval t = ((-1194869 / 30) * t ^ 2 + (201409669 / 1500) * t ^ 4 + (-159035902561 / 1200000) * t ^ 6 + (139996517813 / 3600000) * t ^ 8 + (-41851306789 / 7200000) * t ^ 10 + (126913760731 / 21600000) * t ^ 12 + (-45422267 / 216000) * t ^ 14 + (42630473 / 4320000) * t ^ 18 + (1792621831 / 21600000) * t ^ 20 + (-416 / 5) * c * t ^ 4 + (15153637 / 56250) * c * t ^ 6 + (-25367609 / 112500) * c * t ^ 8 + (-383077 / 12500) * c * t ^ 10 + (343981 / 12500) * c * t ^ 12 + (5009047 / 112500) * c * t ^ 14 + (-70462 / 28125) * c * t ^ 18 + (2 / 5) * c * t ^ 20 + (-125414 / 3) * alpha * t ^ 2 + (6978103 / 75) * alpha * t ^ 4 + (-55956973003 / 900000) * alpha * t ^ 6 + (12552607033 / 900000) * alpha * t ^ 8 + (-12109900169 / 1800000) * alpha * t ^ 10 + (17852564371 / 5400000) * alpha * t ^ 12 + (40043651 / 90000) * alpha * t ^ 14 + (6492379 / 72000) * alpha * t ^ 18 + (-664431529 / 5400000) * alpha * t ^ 20 + (6872 / 5) * alpha * c * t ^ 2 + (-2054096 / 1125) * alpha * c * t ^ 4 + (-34579651 / 337500) * alpha * c * t ^ 6 + (342063067 / 675000) * alpha * c * t ^ 8 + (35948653 / 225000) * alpha * c * t ^ 10 + (-126004061 / 900000) * alpha * c * t ^ 12 + (64512643 / 1350000) * alpha * c * t ^ 14 + (-5044897 / 1350000) * alpha * c * t ^ 18 + (55597 / 180000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_01, v27_02, v27_10, v27_11, v27_12, v27_20, v27_21, v27_22, v27_30, v27_31, v27_32, v27_40, v27_41, v27_42]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_10, phase27_11, phase27_12, phase27_20, phase27_21, phase27_22, phase27_30, phase27_31, phase27_32, phase27_40, phase27_41, phase27_42]
  try simp only [star_one, star_neg]
  linear_combination ((6872 / 15) * t ^ 2 + (-645346 / 1125) * t ^ 4 + (-14028019 / 168750) * t ^ 6 + (260878531 / 1350000) * t ^ 8 + (-13958479 / 225000) * t ^ 10 + (134591107 / 4050000) * t ^ 12 + (65495161 / 4050000) * t ^ 14 + (2518513 / 4050000) * t ^ 18 + (-625868 / 84375) * c * t ^ 6 + (1591523 / 84375) * c * t ^ 8 + (-1209514 / 84375) * c * t ^ 10 + (334457 / 84375) * c * t ^ 12 + (-100664 / 84375) * c * t ^ 14 + (6316 / 84375) * c * t ^ 18 + (2 / 45) * c * t ^ 20 + (-452 / 253125) * c ^ 2 * t ^ 8 + (-154 / 84375) * c ^ 2 * t ^ 10 + (1048 / 50625) * c ^ 2 * t ^ 12 + (30638 / 759375) * c ^ 2 * t ^ 14 + (2336 / 759375) * c ^ 2 * t ^ 18 + (4672 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-13744 / 45) * t ^ 2 + (225056 / 375) * t ^ 4 + (-57452171 / 112500) * t ^ 6 + (37619093 / 168750) * t ^ 8 + (-31243103 / 675000) * t ^ 10 + (4273169 / 506250) * t ^ 12 + (-433316 / 253125) * t ^ 14 + (-805501 / 2025000) * t ^ 18 + (-4672 / 1265625) * t ^ 20 + (121472 / 1125) * alpha * t ^ 4 + (-16433228 / 84375) * alpha * t ^ 6 + (8313736 / 84375) * alpha * t ^ 8 + (-39068 / 3125) * alpha * t ^ 10 + (-9536 / 253125) * alpha * t ^ 12 + (161056 / 253125) * alpha * t ^ 14 + (40264 / 253125) * alpha * t ^ 18) * c_sq
theorem v28_43 (t : ℂ) : (momentPoly 28 z28 4 3).eval t = ((4228014 / 25) * t ^ 3 + (-184090297 / 500) * t ^ 5 + (65620712393 / 300000) * t ^ 7 + (-27146290709 / 1500000) * t ^ 9 + (68030990501 / 3000000) * t ^ 11 + (-6281240503 / 180000) * t ^ 13 + (1711085557 / 112500) * t ^ 15 + (-42057427709 / 9000000) * t ^ 17 + (-9974576311 / 27000000) * t ^ 19 + (302142337 / 750000) * t ^ 21 + (1906397959 / 27000000) * t ^ 25 + (-472663 / 5) * c * t + (14276787 / 50) * c * t ^ 3 + (-1763919337 / 5000) * c * t ^ 5 + (903148942141 / 3600000) * c * t ^ 7 + (-2165608788131 / 18000000) * c * t ^ 9 + (1269797527763 / 36000000) * c * t ^ 11 + (-611692325117 / 108000000) * c * t ^ 13 + (13660627013 / 9000000) * c * t ^ 15 + (-105991201 / 1800000) * c * t ^ 17 + (529716023 / 36000000) * c * t ^ 19 + (-250889927 / 7200000) * c * t ^ 21 + (-8500291 / 3000000) * c * t ^ 25 + (-3308641 / 15) * alpha * t + (19773481 / 50) * alpha * t ^ 3 + (-2620984877 / 30000) * alpha * t ^ 5 + (-82193921097 / 800000) * alpha * t ^ 7 + (-332909356933 / 24000000) * alpha * t ^ 9 + (492023020339 / 14400000) * alpha * t ^ 11 + (-8627177785477 / 432000000) * alpha * t ^ 13 + (349346536571 / 27000000) * alpha * t ^ 15 + (577335850277 / 432000000) * alpha * t ^ 17 + (1354563859 / 25920000) * alpha * t ^ 19 + (46967386973 / 432000000) * alpha * t ^ 21 + (12386197867 / 259200000) * alpha * t ^ 25 + (604002 / 25) * alpha * c * t ^ 3 + (-319923 / 5) * alpha * c * t ^ 5 + (50741001149 / 900000) * alpha * c * t ^ 7 + (-29001991537 / 1500000) * alpha * c * t ^ 9 + (40711820699 / 9000000) * alpha * c * t ^ 11 + (-1369012481 / 1080000) * alpha * c * t ^ 13 + (-178636193 / 450000) * alpha * c * t ^ 15 + (-42769717 / 562500) * alpha * c * t ^ 17 + (-1958575163 / 27000000) * alpha * c * t ^ 19 + (207013859 / 3000000) * alpha * c * t ^ 21 + (379243 / 421875) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_01, v27_02, v27_03, v27_10, v27_11, v27_12, v27_13, v27_20, v27_21, v27_22, v27_23, v27_30, v27_31, v27_32, v27_33, v27_40, v27_41, v27_42, v27_43]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_10, phase27_11, phase27_12, phase27_13, phase27_20, phase27_21, phase27_22, phase27_23, phase27_30, phase27_31, phase27_32, phase27_33, phase27_40, phase27_41, phase27_42, phase27_43]
  try simp only [star_one, star_neg]
  linear_combination ((-201334 / 25) * t ^ 3 + (5059387 / 375) * t ^ 5 + (-1144023829 / 300000) * t ^ 7 + (-6930202879 / 4500000) * t ^ 9 + (-9242619289 / 9000000) * t ^ 11 + (8915316929 / 9000000) * t ^ 13 + (-710664479 / 6750000) * t ^ 15 + (59770997 / 843750) * t ^ 17 + (783729211 / 81000000) * t ^ 19 + (-68600353 / 3000000) * t ^ 21 + (-1112293 / 1265625) * t ^ 25 + (22064 / 75) * c * t ^ 3 + (-2371534 / 5625) * c * t ^ 5 + (7428479 / 337500) * c * t ^ 7 + (66306377 / 843750) * c * t ^ 9 + (481760171 / 6750000) * c * t ^ 11 + (-524404321 / 10125000) * c * t ^ 13 + (234182929 / 20250000) * c * t ^ 15 + (-3101399 / 1350000) * c * t ^ 17 + (23971477 / 30375000) * c * t ^ 19 + (235639 / 4050000) * c * t ^ 21 + (-4402411 / 75937500) * c * t ^ 25 + (72416 / 3375) * c ^ 2 * t ^ 7 + (-5458276 / 140625) * c ^ 2 * t ^ 9 + (8280296 / 421875) * c ^ 2 * t ^ 11 + (-114356 / 46875) * c ^ 2 * t ^ 13 + (31472 / 421875) * c ^ 2 * t ^ 15 + (80528 / 1265625) * c ^ 2 * t ^ 17 + (85264 / 1265625) * c ^ 2 * t ^ 19 + (-8 / 225) * c ^ 2 * t ^ 21) * alpha_sq + ((-42432 / 125) * t ^ 5 + (2542766 / 5625) * t ^ 7 + (4289651 / 140625) * t ^ 9 + (-22346617 / 140625) * t ^ 11 + (-174823 / 15625) * t ^ 13 + (11905573 / 421875) * t ^ 15 + (-163456 / 421875) * t ^ 17 + (-146816 / 140625) * t ^ 19 + (16 / 75) * t ^ 21 + (22064 / 75) * alpha * t ^ 3 + (-1523234 / 5625) * alpha * t ^ 5 + (-49913771 / 337500) * alpha * t ^ 7 + (70202653 / 562500) * alpha * t ^ 9 + (17144539 / 675000) * alpha * t ^ 11 + (-27953527 / 1265625) * alpha * t ^ 13 + (65103953 / 5062500) * alpha * t ^ 15 + (400406 / 1265625) * alpha * t ^ 17 + (-24159407 / 30375000) * alpha * t ^ 19 + (743267 / 5062500) * alpha * t ^ 21 + (165856 / 18984375) * alpha * t ^ 25) * c_sq
theorem v28_44 (t : ℂ) : (momentPoly 28 z28 4 4).eval t = (13234564 + (-495513112 / 15) * t ^ 2 + (18568920139 / 750) * t ^ 4 + (-224747769 / 25) * t ^ 6 + (1959137622586793 / 144000000) * t ^ 8 + (-94315865078249 / 7200000) * t ^ 10 + (889065097276729 / 240000000) * t ^ 12 + (-465472912231067 / 1080000000) * t ^ 14 + (70034240906189 / 320000000) * t ^ 16 + (2040703582727 / 40000000) * t ^ 18 + (-152388560049013 / 6480000000) * t ^ 20 + (7788163280741 / 360000000) * t ^ 22 + (-5813443996613 / 864000000) * t ^ 24 + (-867840287213 / 648000000) * t ^ 26 + (4899875165741 / 25920000000) * t ^ 32 + (-27905856 / 125) * c * t ^ 4 + (7705084 / 15) * c * t ^ 6 + (-76044019817 / 281250) * c * t ^ 8 + (-2241475349 / 22500) * c * t ^ 10 + (163380599033 / 2812500) * c * t ^ 12 + (83565729946 / 2109375) * c * t ^ 14 + (-147016652153 / 5625000) * c * t ^ 16 + (43611985513 / 5625000) * c * t ^ 18 + (4259301223 / 4218750) * c * t ^ 20 + (-1832741917 / 2812500) * c * t ^ 22 + (4603 / 1800) * c * t ^ 24 + (-367413083 / 3375000) * c * t ^ 26 + (-2939272 / 2109375) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z28, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v27_00, v27_01, v27_02, v27_03, v27_04, v27_10, v27_11, v27_12, v27_13, v27_14, v27_20, v27_21, v27_22, v27_23, v27_24, v27_30, v27_31, v27_32, v27_33, v27_34, v27_40, v27_41, v27_42, v27_43, v27_44]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04, phase27_10, phase27_11, phase27_12, phase27_13, phase27_14, phase27_20, phase27_21, phase27_22, phase27_23, phase27_24, phase27_30, phase27_31, phase27_32, phase27_33, phase27_34, phase27_40, phase27_41, phase27_42, phase27_43, phase27_44]
  try simp only [star_one, star_neg]
  linear_combination ((-7155424 / 75) * t ^ 2 + (166893584 / 1125) * t ^ 4 + (-3284253 / 125) * t ^ 6 + (-405340763 / 21600) * t ^ 8 + (-466286806823 / 27000000) * t ^ 10 + (243282746269 / 27000000) * t ^ 12 + (-6661992749473 / 810000000) * t ^ 14 + (55947998251 / 8437500) * t ^ 16 + (-222399047819 / 810000000) * t ^ 18 + (93590813809 / 243000000) * t ^ 20 + (18494395697 / 810000000) * t ^ 22 + (69488132711 / 2430000000) * t ^ 26 + (18603904 / 1125) * c * t ^ 4 + (-10034824 / 225) * c * t ^ 6 + (16461188383 / 421875) * c * t ^ 8 + (-19392183763 / 1687500) * c * t ^ 10 + (19410462131 / 8437500) * c * t ^ 12 + (-120402815639 / 50625000) * c * t ^ 14 + (39307771667 / 50625000) * c * t ^ 16 + (-683611381 / 4218750) * c * t ^ 18 + (-1715820467 / 37968750) * c * t ^ 20 + (681207407 / 16875000) * c * t ^ 22 + (4603 / 16200) * c * t ^ 24 + (11687008 / 3796875) * c * t ^ 26 + (-2939272 / 18984375) * c * t ^ 32 + (174272 / 1125) * c ^ 2 * t ^ 6 + (-548864 / 3125) * c ^ 2 * t ^ 8 + (-37301182 / 1265625) * c ^ 2 * t ^ 10 + (296693984 / 6328125) * c ^ 2 * t ^ 12 + (129248747 / 6328125) * c ^ 2 * t ^ 14 + (-32830051 / 2109375) * c ^ 2 * t ^ 16 + (110985118 / 18984375) * c ^ 2 * t ^ 18 + (-131984 / 18984375) * c ^ 2 * t ^ 20 + (-7732861 / 18984375) * c ^ 2 * t ^ 22 + (458407 / 3796875) * c ^ 2 * t ^ 24 + (8946296 / 56953125) * c ^ 2 * t ^ 26 + (682112 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((-14310848 / 225) * t ^ 2 + (182662304 / 1125) * t ^ 4 + (-21630208 / 125) * t ^ 6 + (197081593271 / 1687500) * t ^ 8 + (-100520727409 / 1687500) * t ^ 10 + (314806350953 / 16875000) * t ^ 12 + (-179578267811 / 50625000) * t ^ 14 + (4780441909 / 4218750) * t ^ 16 + (-6107561 / 78125) * t ^ 18 + (1072128589 / 151875000) * t ^ 20 + (-85606871 / 5625000) * t ^ 22 + (-458407 / 1265625) * t ^ 24 + (-72429467 / 18984375) * t ^ 26 + (-682112 / 94921875) * t ^ 32) * c_sq
#print axioms v28_00
#print axioms v28_11
#print axioms v28_22
#print axioms v28_33
#print axioms v28_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
noncomputable def z29 : Fin 29 → ℂ := Fin.snoc z28 (r ^ 2 * thetaMinus)
theorem v29_00 (t : ℂ) : (momentPoly 29 z29 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00]
  try simp only [phase27_00]
  try simp only [star_one, star_neg]
  ring
theorem v29_01 (t : ℂ) : (momentPoly 29 z29 0 1).eval t = ((-2 / 15) * c * t + (8 / 15) * alpha * t) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_01]
  try simp only [phase27_00, phase27_01]
  try simp only [star_one, star_neg]
  ring
theorem v29_02 (t : ℂ) : (momentPoly 29 z29 0 2).eval t = ((-3223 / 300) * t ^ 2 + (4151 / 300) * t ^ 4 + (73 / 15) * alpha * t ^ 2 + (-73 / 15) * alpha * t ^ 4 + (-28 / 225) * alpha * c * t ^ 2 + (-4 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_01, v28_02]
  try simp only [phase27_00, phase27_01, phase27_02]
  try simp only [star_one, star_neg]
  linear_combination ((14 / 225) * t ^ 2) * alpha_sq + ((-2 / 75) * t ^ 2) * c_sq
theorem v29_03 (t : ℂ) : (momentPoly 29 z29 0 3).eval t = ((-534 / 25) * t ^ 3 + (509 / 25) * t ^ 5 + 1 * t ^ 9 + (1253 / 250) * c * t ^ 3 + (-3803 / 750) * c * t ^ 5 + (-142 / 1125) * c * t ^ 9 + (-26399 / 3000) * alpha * t ^ 3 + (60781 / 6000) * alpha * t ^ 5 + (81523 / 18000) * alpha * t ^ 9 + (-146 / 75) * alpha * c * t ^ 3 + (146 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_01, v28_02, v28_03]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-4 / 125) * c * t ^ 3 + (8 / 1125) * c * t ^ 5) * alpha_sq + ((-4 / 125) * alpha * t ^ 3 + (-4 / 375) * alpha * t ^ 5) * c_sq
theorem v29_04 (t : ℂ) : (momentPoly 29 z29 0 4).eval t = ((21149 / 12000) * t ^ 4 + (-2720763 / 10000) * t ^ 6 + (38461267 / 120000) * t ^ 8 + (-6070673 / 90000) * t ^ 10 + (4806961 / 360000) * t ^ 16 + (3688 / 375) * c * t ^ 4 + (-968 / 125) * c * t ^ 6 + (-584 / 375) * c * t ^ 8 + (-8 / 15) * c * t ^ 10 + (-252211 / 750) * alpha * t ^ 4 + (286883 / 375) * alpha * t ^ 6 + (-104363 / 250) * alpha * t ^ 8 + (-17732 / 1125) * alpha * t ^ 10 + (5033 / 1125) * alpha * t ^ 16 + (5197 / 1125) * alpha * c * t ^ 4 + (-1933 / 1250) * alpha * c * t ^ 6 + (-7718 / 5625) * alpha * c * t ^ 8 + (-85939 / 33750) * alpha * c * t ^ 10 + (-584 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_01, v28_02, v28_03, v28_04]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04]
  try simp only [star_one, star_neg]
  linear_combination ((-461 / 2250) * t ^ 4 + (51377 / 22500) * t ^ 6 + (102739 / 67500) * t ^ 10 + (-292 / 375) * c * t ^ 4 + (1168 / 1125) * c * t ^ 6 + (-292 / 1125) * c * t ^ 8 + (-16 / 1875) * c ^ 2 * t ^ 6 + (-8 / 5625) * c ^ 2 * t ^ 8) * alpha_sq + ((1753 / 1125) * t ^ 4 + (-1157 / 625) * t ^ 6 + (8 / 1875) * t ^ 8 + (-568 / 5625) * t ^ 10 + (-292 / 375) * alpha * t ^ 4 + (292 / 375) * alpha * t ^ 6) * c_sq
theorem v29_10 (t : ℂ) : (momentPoly 29 z29 1 0).eval t = ((-2 / 15) * c * t + (-8 / 15) * alpha * t) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_10]
  try simp only [phase27_00, phase27_10]
  try simp only [star_one, star_neg]
  ring
theorem v29_11 (t : ℂ) : (momentPoly 29 z29 1 1).eval t = (29 + (-121 / 5) * t ^ 2) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_01, v28_10, v28_11]
  try simp only [phase27_00, phase27_01, phase27_10, phase27_11]
  try simp only [star_one, star_neg]
  linear_combination ((-14 / 225) * t ^ 2) * alpha_sq + ((-2 / 75) * t ^ 2) * c_sq
theorem v29_12 (t : ℂ) : (momentPoly 29 z29 1 2).eval t = ((584 / 75) * t ^ 3 + (-584 / 75) * t ^ 5 + (-38 / 5) * c * t + (87 / 10) * c * t ^ 3 + (-87 / 50) * c * t ^ 5 + (152 / 5) * alpha * t + (-1534 / 75) * alpha * t ^ 3 + (-554 / 75) * alpha * t ^ 5 + (-146 / 225) * alpha * c * t ^ 3 + (146 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_01, v28_02, v28_10, v28_11, v28_12]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_10, phase27_11, phase27_12]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 225) * t ^ 3 + (73 / 225) * t ^ 5 + (4 / 375) * c * t ^ 3 + (-8 / 3375) * c * t ^ 5) * alpha_sq + ((-4 / 375) * alpha * t ^ 3 + (-4 / 1125) * alpha * t ^ 5) * c_sq
theorem v29_13 (t : ℂ) : (momentPoly 29 z29 1 3).eval t = ((-22561 / 25) * t ^ 2 + (470973 / 250) * t ^ 4 + (-3855 / 4) * t ^ 6 + (-1427 / 500) * t ^ 10 + (-4 / 15) * c * t ^ 4 + (2 / 5) * c * t ^ 6 + (-2 / 15) * c * t ^ 10 + (2044 / 5) * alpha * t ^ 2 + (-55414 / 75) * alpha * t ^ 4 + (8143 / 25) * alpha * t ^ 6 + (13 / 3) * alpha * t ^ 10 + (-784 / 75) * alpha * c * t ^ 2 + (31811 / 4500) * alpha * c * t ^ 4 + (9661 / 3000) * alpha * c * t ^ 6 + (-4669 / 9000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_01, v28_02, v28_03, v28_10, v28_11, v28_12, v28_13]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_10, phase27_11, phase27_12, phase27_13]
  try simp only [star_one, star_neg]
  linear_combination ((392 / 75) * t ^ 2 + (-28217 / 9000) * t ^ 4 + (-48839 / 30000) * t ^ 6 + (-102739 / 270000) * t ^ 10) * alpha_sq + ((-56 / 25) * t ^ 2 + (6053 / 2250) * t ^ 4 + (-1189 / 1250) * t ^ 6 + (-142 / 5625) * t ^ 10 + (-146 / 375) * alpha * t ^ 4 + (146 / 375) * alpha * t ^ 6) * c_sq
theorem v29_14 (t : ℂ) : (momentPoly 29 z29 1 4).eval t = ((-11748 / 5) * t ^ 3 + (2286894 / 625) * t ^ 5 + (-1157744 / 1875) * t ^ 7 + (-1030399 / 1875) * t ^ 9 + (-835756 / 5625) * t ^ 11 + (34639 / 5625) * t ^ 17 + (13783 / 25) * c * t ^ 3 + (-97076333 / 90000) * c * t ^ 5 + (2756813 / 5000) * c * t ^ 7 + (-1765867 / 36000) * c * t ^ 9 + (46471 / 1800) * c * t ^ 11 + (-307711 / 180000) * c * t ^ 17 + (-290389 / 300) * alpha * t ^ 3 + (85739029 / 45000) * alpha * t ^ 5 + (-531487 / 625) * alpha * t ^ 7 + (32507803 / 90000) * alpha * t ^ 9 + (-3070613 / 7500) * alpha * t ^ 11 + (-106261 / 10000) * alpha * t ^ 17 + (-3212 / 15) * alpha * c * t ^ 3 + (2580607 / 5625) * alpha * c * t ^ 5 + (-1667434 / 5625) * alpha * c * t ^ 7 + (295861 / 5625) * alpha * c * t ^ 9 + (-3536 / 16875) * alpha * c * t ^ 11 + (-10066 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_01, v28_02, v28_03, v28_04, v28_10, v28_11, v28_12, v28_13, v28_14]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04, phase27_10, phase27_11, phase27_12, phase27_13, phase27_14]
  try simp only [star_one, star_neg]
  linear_combination ((1606 / 15) * t ^ 3 + (-364853 / 2250) * t ^ 5 + (17007 / 625) * t ^ 7 + (291773 / 11250) * t ^ 9 + (37832 / 16875) * t ^ 11 + (-5033 / 16875) * t ^ 17 + (-88 / 25) * c * t ^ 3 + (54266 / 16875) * c * t ^ 5 + (5482 / 16875) * c * t ^ 7 + (-13084 / 84375) * c * t ^ 9 + (1136 / 28125) * c * t ^ 11 + (-1168 / 253125) * c * t ^ 17 + (-292 / 5625) * c ^ 2 * t ^ 7 + (292 / 5625) * c ^ 2 * t ^ 9) * alpha_sq + ((1352 / 1875) * t ^ 5 + (-568 / 1875) * t ^ 7 + (-584 / 1875) * t ^ 9 + (-8 / 75) * t ^ 11 + (-88 / 25) * alpha * t ^ 3 + (209 / 125) * alpha * t ^ 5 + (18959 / 11250) * alpha * t ^ 7 + (-798 / 3125) * alpha * t ^ 9 + (-24817 / 56250) * alpha * t ^ 11 + (-584 / 84375) * alpha * t ^ 17) * c_sq
theorem v29_20 (t : ℂ) : (momentPoly 29 z29 2 0).eval t = ((-3223 / 300) * t ^ 2 + (4151 / 300) * t ^ 4 + (-73 / 15) * alpha * t ^ 2 + (73 / 15) * alpha * t ^ 4 + (28 / 225) * alpha * c * t ^ 2 + (4 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_10, v28_20]
  try simp only [phase27_00, phase27_10, phase27_20]
  try simp only [star_one, star_neg]
  linear_combination ((14 / 225) * t ^ 2) * alpha_sq + ((-2 / 75) * t ^ 2) * c_sq
theorem v29_21 (t : ℂ) : (momentPoly 29 z29 2 1).eval t = ((584 / 75) * t ^ 3 + (-584 / 75) * t ^ 5 + (-38 / 5) * c * t + (87 / 10) * c * t ^ 3 + (-87 / 50) * c * t ^ 5 + (-152 / 5) * alpha * t + (1534 / 75) * alpha * t ^ 3 + (554 / 75) * alpha * t ^ 5 + (146 / 225) * alpha * c * t ^ 3 + (-146 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_01, v28_10, v28_11, v28_20, v28_21]
  try simp only [phase27_00, phase27_01, phase27_10, phase27_11, phase27_20, phase27_21]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 225) * t ^ 3 + (73 / 225) * t ^ 5 + (4 / 375) * c * t ^ 3 + (-8 / 3375) * c * t ^ 5) * alpha_sq + ((4 / 375) * alpha * t ^ 3 + (4 / 1125) * alpha * t ^ 5) * c_sq
theorem v29_22 (t : ℂ) : (momentPoly 29 z29 2 2).eval t = (1653 + (-13552 / 5) * t ^ 2 + (2372773 / 2000) * t ^ 4 + (-1018991 / 3000) * t ^ 6 + (1402303 / 6000) * t ^ 8 + (-4088 / 1125) * c * t ^ 4 + (1168 / 375) * c * t ^ 6 + (584 / 1125) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_01, v28_02, v28_10, v28_11, v28_12, v28_20, v28_21, v28_22]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_10, phase27_11, phase27_12, phase27_20, phase27_21, phase27_22]
  try simp only [star_one, star_neg]
  linear_combination ((-1568 / 225) * t ^ 2 + (14339 / 3375) * t ^ 4 + (4757 / 3375) * t ^ 6 + (292 / 1125) * c * t ^ 4 + (-1168 / 3375) * c * t ^ 6 + (292 / 3375) * c * t ^ 8 + (16 / 5625) * c ^ 2 * t ^ 6 + (8 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((-224 / 75) * t ^ 2 + (3451 / 1125) * t ^ 4 + (-407 / 625) * t ^ 6 + (-8 / 5625) * t ^ 8) * c_sq
theorem v29_23 (t : ℂ) : (momentPoly 29 z29 2 3).eval t = ((6424 / 5) * t ^ 3 + (-33791267 / 15000) * t ^ 5 + (8151589 / 10000) * t ^ 7 + (4023767 / 30000) * t ^ 9 + (6385879 / 90000) * t ^ 11 + (-4705879 / 90000) * t ^ 13 + (-9578 / 15) * c * t + (2871 / 2) * c * t ^ 3 + (-50488277 / 45000) * c * t ^ 5 + (2268761 / 5625) * c * t ^ 7 + (-1240541 / 15000) * c * t ^ 9 + (7863 / 2500) * c * t ^ 11 + (-41731 / 22500) * c * t ^ 13 + (38312 / 15) * alpha * t + (-16874 / 5) * alpha * t ^ 3 + (-22517771 / 180000) * alpha * t ^ 5 + (53077531 / 72000) * alpha * t ^ 7 + (23592101 / 120000) * alpha * t ^ 9 + (-15205531 / 360000) * alpha * t ^ 11 + (1596053 / 24000) * alpha * t ^ 13 + (-1606 / 15) * alpha * c * t ^ 3 + (381478 / 1875) * alpha * c * t ^ 5 + (-179824 / 1875) * alpha * c * t ^ 7 + (3788 / 5625) * alpha * c * t ^ 9 + (-9434 / 16875) * alpha * c * t ^ 11 + (-10066 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_01, v28_02, v28_03, v28_10, v28_11, v28_12, v28_13, v28_20, v28_21, v28_22, v28_23]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_10, phase27_11, phase27_12, phase27_13, phase27_20, phase27_21, phase27_22, phase27_23]
  try simp only [star_one, star_neg]
  linear_combination ((-803 / 15) * t ^ 3 + (97157 / 1125) * t ^ 5 + (-36272 / 1125) * t ^ 7 + (-26033 / 16875) * t ^ 11 + (16133 / 16875) * t ^ 13 + (44 / 25) * c * t ^ 3 + (-38627 / 22500) * c * t ^ 5 + (-1169 / 9000) * c * t ^ 7 + (43763 / 675000) * c * t ^ 9 + (29617 / 225000) * c * t ^ 11 + (-67379 / 2025000) * c * t ^ 13 + (292 / 5625) * c ^ 2 * t ^ 7 + (-292 / 5625) * c ^ 2 * t ^ 9) * alpha_sq + ((-1852 / 1875) * t ^ 5 + (1318 / 1875) * t ^ 7 + (584 / 1875) * t ^ 9 + (-2 / 75) * t ^ 11 + (-44 / 25) * alpha * t ^ 3 + (49081 / 67500) * alpha * t ^ 5 + (110213 / 135000) * alpha * t ^ 7 + (-16 / 9375) * alpha * t ^ 9 + (-20273 / 225000) * alpha * t ^ 11 + (284 / 84375) * alpha * t ^ 13) * c_sq
theorem v29_24 (t : ℂ) : (momentPoly 29 z29 2 4).eval t = ((-7448353 / 75) * t ^ 2 + (141921761 / 500) * t ^ 4 + (-106841894851 / 400000) * t ^ 6 + (107605099259 / 1200000) * t ^ 8 + (-37101051359 / 2400000) * t ^ 10 + (64900154933 / 7200000) * t ^ 12 + (-1113569641 / 1800000) * t ^ 14 + (-55647009 / 800000) * t ^ 18 + (763289033 / 7200000) * t ^ 20 + (-288 / 5) * c * t ^ 4 + (712917 / 3125) * c * t ^ 6 + (-815077 / 3750) * c * t ^ 8 + (-63311 / 11250) * c * t ^ 10 + (1289207 / 56250) * c * t ^ 12 + (5260103 / 168750) * c * t ^ 14 + (-161056 / 84375) * c * t ^ 18 + (4 / 15) * c * t ^ 20 + (674812 / 15) * alpha * t ^ 2 + (-2907583 / 25) * alpha * t ^ 4 + (89226489979 / 900000) * alpha * t ^ 6 + (-29937879217 / 900000) * alpha * t ^ 8 + (17372342777 / 1800000) * alpha * t ^ 10 + (-19636883459 / 5400000) * alpha * t ^ 12 + (-263367619 / 450000) * alpha * t ^ 14 + (-219083299 / 1800000) * alpha * t ^ 18 + (711459881 / 5400000) * alpha * t ^ 20 + (-258832 / 225) * alpha * c * t ^ 2 + (631898 / 375) * alpha * c * t ^ 4 + (-13683833 / 225000) * alpha * c * t ^ 6 + (-4870549 / 11250) * alpha * c * t ^ 8 + (-10956643 / 90000) * alpha * c * t ^ 10 + (150023969 / 1350000) * alpha * c * t ^ 12 + (-911367 / 25000) * alpha * c * t ^ 14 + (153551 / 50000) * alpha * c * t ^ 18 + (-60397 / 270000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_01, v28_02, v28_03, v28_04, v28_10, v28_11, v28_12, v28_13, v28_14, v28_20, v28_21, v28_22, v28_23, v28_24]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04, phase27_10, phase27_11, phase27_12, phase27_13, phase27_14, phase27_20, phase27_21, phase27_22, phase27_23, phase27_24]
  try simp only [star_one, star_neg]
  linear_combination ((129416 / 225) * t ^ 2 + (-84651 / 125) * t ^ 4 + (-9449207 / 54000) * t ^ 6 + (110268019 / 450000) * t ^ 8 + (-7775987 / 180000) * t ^ 10 + (189951289 / 4050000) * t ^ 12 + (80552597 / 4050000) * t ^ 14 + (8468767 / 8100000) * t ^ 18 + (-693041 / 84375) * c * t ^ 6 + (1640573 / 84375) * c * t ^ 8 + (-1221973 / 84375) * c * t ^ 10 + (340373 / 84375) * c * t ^ 12 + (-217928 / 253125) * c * t ^ 14 + (8882 / 253125) * c * t ^ 18 + (2 / 45) * c * t ^ 20 + (-7349 / 253125) * c ^ 2 * t ^ 8 + (1157 / 168750) * c ^ 2 * t ^ 10 + (2378 / 140625) * c ^ 2 * t ^ 12 + (27089 / 843750) * c ^ 2 * t ^ 14 + (1168 / 421875) * c ^ 2 * t ^ 18 + (1168 / 1265625) * c ^ 2 * t ^ 20) * alpha_sq + ((-18488 / 75) * t ^ 2 + (72636 / 125) * t ^ 4 + (-238541201 / 450000) * t ^ 6 + (43989 / 200) * t ^ 8 + (-36060031 / 900000) * t ^ 10 + (27677129 / 3375000) * t ^ 12 + (-65309 / 46875) * t ^ 14 + (-1462331 / 4500000) * t ^ 18 + (-1168 / 421875) * t ^ 20 + (-10512 / 125) * alpha * t ^ 4 + (13643041 / 84375) * alpha * t ^ 6 + (-7365682 / 84375) * alpha * t ^ 8 + (288529 / 28125) * alpha * t ^ 10 + (2984 / 84375) * alpha * t ^ 12 + (-40264 / 84375) * alpha * t ^ 14 + (-10066 / 84375) * alpha * t ^ 18) * c_sq
theorem v29_30 (t : ℂ) : (momentPoly 29 z29 3 0).eval t = ((-534 / 25) * t ^ 3 + (509 / 25) * t ^ 5 + 1 * t ^ 9 + (1253 / 250) * c * t ^ 3 + (-3803 / 750) * c * t ^ 5 + (-142 / 1125) * c * t ^ 9 + (26399 / 3000) * alpha * t ^ 3 + (-60781 / 6000) * alpha * t ^ 5 + (-81523 / 18000) * alpha * t ^ 9 + (146 / 75) * alpha * c * t ^ 3 + (-146 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_10, v28_20, v28_30]
  try simp only [phase27_00, phase27_10, phase27_20, phase27_30]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-4 / 125) * c * t ^ 3 + (8 / 1125) * c * t ^ 5) * alpha_sq + ((4 / 125) * alpha * t ^ 3 + (4 / 375) * alpha * t ^ 5) * c_sq
theorem v29_31 (t : ℂ) : (momentPoly 29 z29 3 1).eval t = ((-22561 / 25) * t ^ 2 + (470973 / 250) * t ^ 4 + (-3855 / 4) * t ^ 6 + (-1427 / 500) * t ^ 10 + (-4 / 15) * c * t ^ 4 + (2 / 5) * c * t ^ 6 + (-2 / 15) * c * t ^ 10 + (-2044 / 5) * alpha * t ^ 2 + (55414 / 75) * alpha * t ^ 4 + (-8143 / 25) * alpha * t ^ 6 + (-13 / 3) * alpha * t ^ 10 + (784 / 75) * alpha * c * t ^ 2 + (-31811 / 4500) * alpha * c * t ^ 4 + (-9661 / 3000) * alpha * c * t ^ 6 + (4669 / 9000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_01, v28_10, v28_11, v28_20, v28_21, v28_30, v28_31]
  try simp only [phase27_00, phase27_01, phase27_10, phase27_11, phase27_20, phase27_21, phase27_30, phase27_31]
  try simp only [star_one, star_neg]
  linear_combination ((392 / 75) * t ^ 2 + (-28217 / 9000) * t ^ 4 + (-48839 / 30000) * t ^ 6 + (-102739 / 270000) * t ^ 10) * alpha_sq + ((-56 / 25) * t ^ 2 + (6053 / 2250) * t ^ 4 + (-1189 / 1250) * t ^ 6 + (-142 / 5625) * t ^ 10 + (146 / 375) * alpha * t ^ 4 + (-146 / 375) * alpha * t ^ 6) * c_sq
theorem v29_32 (t : ℂ) : (momentPoly 29 z29 3 2).eval t = ((6424 / 5) * t ^ 3 + (-33791267 / 15000) * t ^ 5 + (8151589 / 10000) * t ^ 7 + (4023767 / 30000) * t ^ 9 + (6385879 / 90000) * t ^ 11 + (-4705879 / 90000) * t ^ 13 + (-9578 / 15) * c * t + (2871 / 2) * c * t ^ 3 + (-50488277 / 45000) * c * t ^ 5 + (2268761 / 5625) * c * t ^ 7 + (-1240541 / 15000) * c * t ^ 9 + (7863 / 2500) * c * t ^ 11 + (-41731 / 22500) * c * t ^ 13 + (-38312 / 15) * alpha * t + (16874 / 5) * alpha * t ^ 3 + (22517771 / 180000) * alpha * t ^ 5 + (-53077531 / 72000) * alpha * t ^ 7 + (-23592101 / 120000) * alpha * t ^ 9 + (15205531 / 360000) * alpha * t ^ 11 + (-1596053 / 24000) * alpha * t ^ 13 + (1606 / 15) * alpha * c * t ^ 3 + (-381478 / 1875) * alpha * c * t ^ 5 + (179824 / 1875) * alpha * c * t ^ 7 + (-3788 / 5625) * alpha * c * t ^ 9 + (9434 / 16875) * alpha * c * t ^ 11 + (10066 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_01, v28_02, v28_10, v28_11, v28_12, v28_20, v28_21, v28_22, v28_30, v28_31, v28_32]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_10, phase27_11, phase27_12, phase27_20, phase27_21, phase27_22, phase27_30, phase27_31, phase27_32]
  try simp only [star_one, star_neg]
  linear_combination ((-803 / 15) * t ^ 3 + (97157 / 1125) * t ^ 5 + (-36272 / 1125) * t ^ 7 + (-26033 / 16875) * t ^ 11 + (16133 / 16875) * t ^ 13 + (44 / 25) * c * t ^ 3 + (-38627 / 22500) * c * t ^ 5 + (-1169 / 9000) * c * t ^ 7 + (43763 / 675000) * c * t ^ 9 + (29617 / 225000) * c * t ^ 11 + (-67379 / 2025000) * c * t ^ 13 + (292 / 5625) * c ^ 2 * t ^ 7 + (-292 / 5625) * c ^ 2 * t ^ 9) * alpha_sq + ((-1852 / 1875) * t ^ 5 + (1318 / 1875) * t ^ 7 + (584 / 1875) * t ^ 9 + (-2 / 75) * t ^ 11 + (44 / 25) * alpha * t ^ 3 + (-49081 / 67500) * alpha * t ^ 5 + (-110213 / 135000) * alpha * t ^ 7 + (16 / 9375) * alpha * t ^ 9 + (20273 / 225000) * alpha * t ^ 11 + (-284 / 84375) * alpha * t ^ 13) * c_sq
theorem v29_33 (t : ℂ) : (momentPoly 29 z29 3 3).eval t = (138881 + (-1677786 / 5) * t ^ 2 + (576583839 / 2000) * t ^ 4 + (-100474791679 / 600000) * t ^ 6 + (73264895069 / 600000) * t ^ 8 + (-36793364041 / 800000) * t ^ 10 + (821268143 / 1800000) * t ^ 12 + (-262771517 / 400000) * t ^ 14 + (266932423 / 7200000) * t ^ 18 + (-110376 / 125) * c * t ^ 4 + (5521783 / 3750) * c * t ^ 6 + (-2509187 / 7500) * c * t ^ 8 + (-605833 / 2500) * c * t ^ 10 + (-1053611 / 22500) * c * t ^ 12 + (86259 / 2500) * c * t ^ 14 + (-284 / 1125) * c * t ^ 18) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_01, v28_02, v28_03, v28_10, v28_11, v28_12, v28_13, v28_20, v28_21, v28_22, v28_23, v28_30, v28_31, v28_32, v28_33]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_10, phase27_11, phase27_12, phase27_13, phase27_20, phase27_21, phase27_22, phase27_23, phase27_30, phase27_31, phase27_32, phase27_33]
  try simp only [star_one, star_neg]
  linear_combination ((-64708 / 75) * t ^ 2 + (129051 / 125) * t ^ 4 + (25512973 / 450000) * t ^ 6 + (-54328453 / 300000) * t ^ 8 + (-47308663 / 900000) * t ^ 10 + (23613361 / 2700000) * t ^ 12 + (-121358831 / 4500000) * t ^ 14 + (-17235127 / 10125000) * t ^ 18 + (7884 / 125) * c * t ^ 4 + (-51148 / 375) * c * t ^ 6 + (2421332 / 28125) * c * t ^ 8 + (-372332 / 28125) * c * t ^ 10 + (112 / 75) * c * t ^ 12 + (-128 / 125) * c * t ^ 14 + (1312 / 1875) * c ^ 2 * t ^ 6 + (-69241 / 168750) * c ^ 2 * t ^ 8 + (-25271 / 112500) * c ^ 2 * t ^ 10 + (501 / 12500) * c ^ 2 * t ^ 14) * alpha_sq + ((-9244 / 25) * t ^ 2 + (93177 / 125) * t ^ 4 + (-121765031 / 225000) * t ^ 6 + (22361413 / 112500) * t ^ 8 + (-3262033 / 75000) * t ^ 10 + (368693 / 168750) * t ^ 12 + (-191383 / 93750) * t ^ 14 + (-10082 / 421875) * t ^ 18) * c_sq
theorem v29_34 (t : ℂ) : (momentPoly 29 z29 3 4).eval t = ((5206944 / 25) * t ^ 3 + (-1290507551 / 2500) * t ^ 5 + (5755489626 / 15625) * t ^ 7 + (-25194782207 / 750000) * t ^ 9 + (-1757016773 / 1500000) * t ^ 11 + (-370306762009 / 9000000) * t ^ 13 + (5189035061 / 250000) * t ^ 15 + (-47350087061 / 9000000) * t ^ 17 + (-8489151481 / 13500000) * t ^ 19 + (4888579637 / 9000000) * t ^ 21 + (2001743111 / 27000000) * t ^ 25 + (-1054258 / 15) * c * t + (1163538 / 5) * c * t ^ 3 + (-2340402331 / 7500) * c * t ^ 5 + (2072446127227 / 9000000) * c * t ^ 7 + (-321315232039 / 3000000) * c * t ^ 9 + (541923338081 / 18000000) * c * t ^ 11 + (-264790766491 / 54000000) * c * t ^ 13 + (5855431247 / 4500000) * c * t ^ 15 + (-75323533 / 1500000) * c * t ^ 17 + (1512536647 / 54000000) * c * t ^ 19 + (-573258181 / 18000000) * c * t ^ 21 + (-9100291 / 4500000) * c * t ^ 25 + (4217032 / 15) * alpha * t + (-13677144 / 25) * alpha * t ^ 3 + (4503229337 / 30000) * alpha * t ^ 5 + (1940804014889 / 12000000) * alpha * t ^ 7 + (-6738554797 / 8000000) * alpha * t ^ 9 + (-750562023193 / 14400000) * alpha * t ^ 11 + (2233163065621 / 86400000) * alpha * t ^ 13 + (-473490254 / 28125) * alpha * t ^ 15 + (-257226388519 / 144000000) * alpha * t ^ 17 + (31425172597 / 216000000) * alpha * t ^ 19 + (-26289811171 / 144000000) * alpha * t ^ 21 + (-4800797993 / 86400000) * alpha * t ^ 25 + (-433912 / 25) * alpha * c * t ^ 3 + (90033154 / 1875) * alpha * c * t ^ 5 + (-100750452427 / 2250000) * alpha * c * t ^ 7 + (37187369033 / 2250000) * alpha * c * t ^ 9 + (-16712589113 / 4500000) * alpha * c * t ^ 11 + (12734748643 / 13500000) * alpha * c * t ^ 13 + (337763339 / 1125000) * alpha * c * t ^ 15 + (45967117 / 843750) * alpha * c * t ^ 17 + (2230610299 / 40500000) * alpha * c * t ^ 19 + (-668789929 / 13500000) * alpha * c * t ^ 21 + (-758486 / 1265625) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_01, v28_02, v28_03, v28_04, v28_10, v28_11, v28_12, v28_13, v28_14, v28_20, v28_21, v28_22, v28_23, v28_24, v28_30, v28_31, v28_32, v28_33, v28_34]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04, phase27_10, phase27_11, phase27_12, phase27_13, phase27_14, phase27_20, phase27_21, phase27_22, phase27_23, phase27_24, phase27_30, phase27_31, phase27_32, phase27_33, phase27_34]
  try simp only [star_one, star_neg]
  linear_combination ((-216956 / 25) * t ^ 3 + (2390319 / 125) * t ^ 5 + (-56827501003 / 4500000) * t ^ 7 + (12552607033 / 4500000) * t ^ 9 + (-14955175369 / 9000000) * t ^ 11 + (32357696051 / 27000000) * t ^ 13 + (-1423270307 / 6750000) * t ^ 15 + (64481833 / 843750) * t ^ 17 + (1435778683 / 81000000) * t ^ 19 + (-664431529 / 27000000) * t ^ 21 + (-1112293 / 1265625) * t ^ 25 + (35664 / 125) * c * t ^ 3 + (-5456173 / 11250) * c * t ^ 5 + (48575831 / 421875) * c * t ^ 7 + (183024197 / 2250000) * c * t ^ 9 + (97986559 / 2250000) * c * t ^ 11 + (-53868163 / 1012500) * c * t ^ 13 + (78608203 / 5062500) * c * t ^ 15 + (-280820489 / 101250000) * c * t ^ 17 + (57302033 / 101250000) * c * t ^ 19 + (776531 / 6328125) * c * t ^ 21 + (-4918667 / 75937500) * c * t ^ 25 + (94024 / 5625) * c ^ 2 * t ^ 7 + (-13599241 / 421875) * c ^ 2 * t ^ 9 + (7335346 / 421875) * c ^ 2 * t ^ 11 + (-280369 / 140625) * c ^ 2 * t ^ 13 + (852 / 15625) * c ^ 2 * t ^ 15 + (20132 / 421875) * c ^ 2 * t ^ 17 + (21316 / 421875) * c ^ 2 * t ^ 19 + (-2 / 75) * c ^ 2 * t ^ 21) * alpha_sq + ((-196312 / 625) * t ^ 5 + (44078789 / 93750) * t ^ 7 + (-1080961 / 37500) * t ^ 9 + (-79785967 / 562500) * t ^ 11 + (-77633 / 12500) * t ^ 13 + (1361789 / 62500) * t ^ 15 + (-40864 / 140625) * t ^ 17 + (-120178 / 140625) * t ^ 19 + (4 / 25) * t ^ 21 + (-35664 / 125) * alpha * t ^ 3 + (3629573 / 11250) * alpha * t ^ 5 + (89362813 / 843750) * alpha * t ^ 7 + (-312940393 / 2250000) * alpha * t ^ 9 + (-17337871 / 843750) * alpha * t ^ 11 + (222047087 / 10125000) * alpha * t ^ 13 + (-76632077 / 6750000) * alpha * t ^ 15 + (-40277 / 156250) * alpha * t ^ 17 + (82039487 / 101250000) * alpha * t ^ 19 + (-1352549 / 11250000) * alpha * t ^ 21 + (-41464 / 6328125) * alpha * t ^ 25) * c_sq
theorem v29_40 (t : ℂ) : (momentPoly 29 z29 4 0).eval t = ((21149 / 12000) * t ^ 4 + (-2720763 / 10000) * t ^ 6 + (38461267 / 120000) * t ^ 8 + (-6070673 / 90000) * t ^ 10 + (4806961 / 360000) * t ^ 16 + (3688 / 375) * c * t ^ 4 + (-968 / 125) * c * t ^ 6 + (-584 / 375) * c * t ^ 8 + (-8 / 15) * c * t ^ 10 + (252211 / 750) * alpha * t ^ 4 + (-286883 / 375) * alpha * t ^ 6 + (104363 / 250) * alpha * t ^ 8 + (17732 / 1125) * alpha * t ^ 10 + (-5033 / 1125) * alpha * t ^ 16 + (-5197 / 1125) * alpha * c * t ^ 4 + (1933 / 1250) * alpha * c * t ^ 6 + (7718 / 5625) * alpha * c * t ^ 8 + (85939 / 33750) * alpha * c * t ^ 10 + (584 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_10, v28_20, v28_30, v28_40]
  try simp only [phase27_00, phase27_10, phase27_20, phase27_30, phase27_40]
  try simp only [star_one, star_neg]
  linear_combination ((-461 / 2250) * t ^ 4 + (51377 / 22500) * t ^ 6 + (102739 / 67500) * t ^ 10 + (-292 / 375) * c * t ^ 4 + (1168 / 1125) * c * t ^ 6 + (-292 / 1125) * c * t ^ 8 + (-16 / 1875) * c ^ 2 * t ^ 6 + (-8 / 5625) * c ^ 2 * t ^ 8) * alpha_sq + ((1753 / 1125) * t ^ 4 + (-1157 / 625) * t ^ 6 + (8 / 1875) * t ^ 8 + (-568 / 5625) * t ^ 10 + (292 / 375) * alpha * t ^ 4 + (-292 / 375) * alpha * t ^ 6) * c_sq
theorem v29_41 (t : ℂ) : (momentPoly 29 z29 4 1).eval t = ((-11748 / 5) * t ^ 3 + (2286894 / 625) * t ^ 5 + (-1157744 / 1875) * t ^ 7 + (-1030399 / 1875) * t ^ 9 + (-835756 / 5625) * t ^ 11 + (34639 / 5625) * t ^ 17 + (13783 / 25) * c * t ^ 3 + (-97076333 / 90000) * c * t ^ 5 + (2756813 / 5000) * c * t ^ 7 + (-1765867 / 36000) * c * t ^ 9 + (46471 / 1800) * c * t ^ 11 + (-307711 / 180000) * c * t ^ 17 + (290389 / 300) * alpha * t ^ 3 + (-85739029 / 45000) * alpha * t ^ 5 + (531487 / 625) * alpha * t ^ 7 + (-32507803 / 90000) * alpha * t ^ 9 + (3070613 / 7500) * alpha * t ^ 11 + (106261 / 10000) * alpha * t ^ 17 + (3212 / 15) * alpha * c * t ^ 3 + (-2580607 / 5625) * alpha * c * t ^ 5 + (1667434 / 5625) * alpha * c * t ^ 7 + (-295861 / 5625) * alpha * c * t ^ 9 + (3536 / 16875) * alpha * c * t ^ 11 + (10066 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_01, v28_10, v28_11, v28_20, v28_21, v28_30, v28_31, v28_40, v28_41]
  try simp only [phase27_00, phase27_01, phase27_10, phase27_11, phase27_20, phase27_21, phase27_30, phase27_31, phase27_40, phase27_41]
  try simp only [star_one, star_neg]
  linear_combination ((1606 / 15) * t ^ 3 + (-364853 / 2250) * t ^ 5 + (17007 / 625) * t ^ 7 + (291773 / 11250) * t ^ 9 + (37832 / 16875) * t ^ 11 + (-5033 / 16875) * t ^ 17 + (-88 / 25) * c * t ^ 3 + (54266 / 16875) * c * t ^ 5 + (5482 / 16875) * c * t ^ 7 + (-13084 / 84375) * c * t ^ 9 + (1136 / 28125) * c * t ^ 11 + (-1168 / 253125) * c * t ^ 17 + (-292 / 5625) * c ^ 2 * t ^ 7 + (292 / 5625) * c ^ 2 * t ^ 9) * alpha_sq + ((1352 / 1875) * t ^ 5 + (-568 / 1875) * t ^ 7 + (-584 / 1875) * t ^ 9 + (-8 / 75) * t ^ 11 + (88 / 25) * alpha * t ^ 3 + (-209 / 125) * alpha * t ^ 5 + (-18959 / 11250) * alpha * t ^ 7 + (798 / 3125) * alpha * t ^ 9 + (24817 / 56250) * alpha * t ^ 11 + (584 / 84375) * alpha * t ^ 17) * c_sq
theorem v29_42 (t : ℂ) : (momentPoly 29 z29 4 2).eval t = ((-7448353 / 75) * t ^ 2 + (141921761 / 500) * t ^ 4 + (-106841894851 / 400000) * t ^ 6 + (107605099259 / 1200000) * t ^ 8 + (-37101051359 / 2400000) * t ^ 10 + (64900154933 / 7200000) * t ^ 12 + (-1113569641 / 1800000) * t ^ 14 + (-55647009 / 800000) * t ^ 18 + (763289033 / 7200000) * t ^ 20 + (-288 / 5) * c * t ^ 4 + (712917 / 3125) * c * t ^ 6 + (-815077 / 3750) * c * t ^ 8 + (-63311 / 11250) * c * t ^ 10 + (1289207 / 56250) * c * t ^ 12 + (5260103 / 168750) * c * t ^ 14 + (-161056 / 84375) * c * t ^ 18 + (4 / 15) * c * t ^ 20 + (-674812 / 15) * alpha * t ^ 2 + (2907583 / 25) * alpha * t ^ 4 + (-89226489979 / 900000) * alpha * t ^ 6 + (29937879217 / 900000) * alpha * t ^ 8 + (-17372342777 / 1800000) * alpha * t ^ 10 + (19636883459 / 5400000) * alpha * t ^ 12 + (263367619 / 450000) * alpha * t ^ 14 + (219083299 / 1800000) * alpha * t ^ 18 + (-711459881 / 5400000) * alpha * t ^ 20 + (258832 / 225) * alpha * c * t ^ 2 + (-631898 / 375) * alpha * c * t ^ 4 + (13683833 / 225000) * alpha * c * t ^ 6 + (4870549 / 11250) * alpha * c * t ^ 8 + (10956643 / 90000) * alpha * c * t ^ 10 + (-150023969 / 1350000) * alpha * c * t ^ 12 + (911367 / 25000) * alpha * c * t ^ 14 + (-153551 / 50000) * alpha * c * t ^ 18 + (60397 / 270000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_01, v28_02, v28_10, v28_11, v28_12, v28_20, v28_21, v28_22, v28_30, v28_31, v28_32, v28_40, v28_41, v28_42]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_10, phase27_11, phase27_12, phase27_20, phase27_21, phase27_22, phase27_30, phase27_31, phase27_32, phase27_40, phase27_41, phase27_42]
  try simp only [star_one, star_neg]
  linear_combination ((129416 / 225) * t ^ 2 + (-84651 / 125) * t ^ 4 + (-9449207 / 54000) * t ^ 6 + (110268019 / 450000) * t ^ 8 + (-7775987 / 180000) * t ^ 10 + (189951289 / 4050000) * t ^ 12 + (80552597 / 4050000) * t ^ 14 + (8468767 / 8100000) * t ^ 18 + (-693041 / 84375) * c * t ^ 6 + (1640573 / 84375) * c * t ^ 8 + (-1221973 / 84375) * c * t ^ 10 + (340373 / 84375) * c * t ^ 12 + (-217928 / 253125) * c * t ^ 14 + (8882 / 253125) * c * t ^ 18 + (2 / 45) * c * t ^ 20 + (-7349 / 253125) * c ^ 2 * t ^ 8 + (1157 / 168750) * c ^ 2 * t ^ 10 + (2378 / 140625) * c ^ 2 * t ^ 12 + (27089 / 843750) * c ^ 2 * t ^ 14 + (1168 / 421875) * c ^ 2 * t ^ 18 + (1168 / 1265625) * c ^ 2 * t ^ 20) * alpha_sq + ((-18488 / 75) * t ^ 2 + (72636 / 125) * t ^ 4 + (-238541201 / 450000) * t ^ 6 + (43989 / 200) * t ^ 8 + (-36060031 / 900000) * t ^ 10 + (27677129 / 3375000) * t ^ 12 + (-65309 / 46875) * t ^ 14 + (-1462331 / 4500000) * t ^ 18 + (-1168 / 421875) * t ^ 20 + (10512 / 125) * alpha * t ^ 4 + (-13643041 / 84375) * alpha * t ^ 6 + (7365682 / 84375) * alpha * t ^ 8 + (-288529 / 28125) * alpha * t ^ 10 + (-2984 / 84375) * alpha * t ^ 12 + (40264 / 84375) * alpha * t ^ 14 + (10066 / 84375) * alpha * t ^ 18) * c_sq
theorem v29_43 (t : ℂ) : (momentPoly 29 z29 4 3).eval t = ((5206944 / 25) * t ^ 3 + (-1290507551 / 2500) * t ^ 5 + (5755489626 / 15625) * t ^ 7 + (-25194782207 / 750000) * t ^ 9 + (-1757016773 / 1500000) * t ^ 11 + (-370306762009 / 9000000) * t ^ 13 + (5189035061 / 250000) * t ^ 15 + (-47350087061 / 9000000) * t ^ 17 + (-8489151481 / 13500000) * t ^ 19 + (4888579637 / 9000000) * t ^ 21 + (2001743111 / 27000000) * t ^ 25 + (-1054258 / 15) * c * t + (1163538 / 5) * c * t ^ 3 + (-2340402331 / 7500) * c * t ^ 5 + (2072446127227 / 9000000) * c * t ^ 7 + (-321315232039 / 3000000) * c * t ^ 9 + (541923338081 / 18000000) * c * t ^ 11 + (-264790766491 / 54000000) * c * t ^ 13 + (5855431247 / 4500000) * c * t ^ 15 + (-75323533 / 1500000) * c * t ^ 17 + (1512536647 / 54000000) * c * t ^ 19 + (-573258181 / 18000000) * c * t ^ 21 + (-9100291 / 4500000) * c * t ^ 25 + (-4217032 / 15) * alpha * t + (13677144 / 25) * alpha * t ^ 3 + (-4503229337 / 30000) * alpha * t ^ 5 + (-1940804014889 / 12000000) * alpha * t ^ 7 + (6738554797 / 8000000) * alpha * t ^ 9 + (750562023193 / 14400000) * alpha * t ^ 11 + (-2233163065621 / 86400000) * alpha * t ^ 13 + (473490254 / 28125) * alpha * t ^ 15 + (257226388519 / 144000000) * alpha * t ^ 17 + (-31425172597 / 216000000) * alpha * t ^ 19 + (26289811171 / 144000000) * alpha * t ^ 21 + (4800797993 / 86400000) * alpha * t ^ 25 + (433912 / 25) * alpha * c * t ^ 3 + (-90033154 / 1875) * alpha * c * t ^ 5 + (100750452427 / 2250000) * alpha * c * t ^ 7 + (-37187369033 / 2250000) * alpha * c * t ^ 9 + (16712589113 / 4500000) * alpha * c * t ^ 11 + (-12734748643 / 13500000) * alpha * c * t ^ 13 + (-337763339 / 1125000) * alpha * c * t ^ 15 + (-45967117 / 843750) * alpha * c * t ^ 17 + (-2230610299 / 40500000) * alpha * c * t ^ 19 + (668789929 / 13500000) * alpha * c * t ^ 21 + (758486 / 1265625) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_01, v28_02, v28_03, v28_10, v28_11, v28_12, v28_13, v28_20, v28_21, v28_22, v28_23, v28_30, v28_31, v28_32, v28_33, v28_40, v28_41, v28_42, v28_43]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_10, phase27_11, phase27_12, phase27_13, phase27_20, phase27_21, phase27_22, phase27_23, phase27_30, phase27_31, phase27_32, phase27_33, phase27_40, phase27_41, phase27_42, phase27_43]
  try simp only [star_one, star_neg]
  linear_combination ((-216956 / 25) * t ^ 3 + (2390319 / 125) * t ^ 5 + (-56827501003 / 4500000) * t ^ 7 + (12552607033 / 4500000) * t ^ 9 + (-14955175369 / 9000000) * t ^ 11 + (32357696051 / 27000000) * t ^ 13 + (-1423270307 / 6750000) * t ^ 15 + (64481833 / 843750) * t ^ 17 + (1435778683 / 81000000) * t ^ 19 + (-664431529 / 27000000) * t ^ 21 + (-1112293 / 1265625) * t ^ 25 + (35664 / 125) * c * t ^ 3 + (-5456173 / 11250) * c * t ^ 5 + (48575831 / 421875) * c * t ^ 7 + (183024197 / 2250000) * c * t ^ 9 + (97986559 / 2250000) * c * t ^ 11 + (-53868163 / 1012500) * c * t ^ 13 + (78608203 / 5062500) * c * t ^ 15 + (-280820489 / 101250000) * c * t ^ 17 + (57302033 / 101250000) * c * t ^ 19 + (776531 / 6328125) * c * t ^ 21 + (-4918667 / 75937500) * c * t ^ 25 + (94024 / 5625) * c ^ 2 * t ^ 7 + (-13599241 / 421875) * c ^ 2 * t ^ 9 + (7335346 / 421875) * c ^ 2 * t ^ 11 + (-280369 / 140625) * c ^ 2 * t ^ 13 + (852 / 15625) * c ^ 2 * t ^ 15 + (20132 / 421875) * c ^ 2 * t ^ 17 + (21316 / 421875) * c ^ 2 * t ^ 19 + (-2 / 75) * c ^ 2 * t ^ 21) * alpha_sq + ((-196312 / 625) * t ^ 5 + (44078789 / 93750) * t ^ 7 + (-1080961 / 37500) * t ^ 9 + (-79785967 / 562500) * t ^ 11 + (-77633 / 12500) * t ^ 13 + (1361789 / 62500) * t ^ 15 + (-40864 / 140625) * t ^ 17 + (-120178 / 140625) * t ^ 19 + (4 / 25) * t ^ 21 + (35664 / 125) * alpha * t ^ 3 + (-3629573 / 11250) * alpha * t ^ 5 + (-89362813 / 843750) * alpha * t ^ 7 + (312940393 / 2250000) * alpha * t ^ 9 + (17337871 / 843750) * alpha * t ^ 11 + (-222047087 / 10125000) * alpha * t ^ 13 + (76632077 / 6750000) * alpha * t ^ 15 + (40277 / 156250) * alpha * t ^ 17 + (-82039487 / 101250000) * alpha * t ^ 19 + (1352549 / 11250000) * alpha * t ^ 21 + (41464 / 6328125) * alpha * t ^ 25) * c_sq
theorem v29_44 (t : ℂ) : (momentPoly 29 z29 4 4).eval t = (15286741 + (-48373864) * t ^ 2 + (30587416743 / 500) * t ^ 4 + (-1981920326729 / 37500) * t ^ 6 + (1344128007958901 / 28800000) * t ^ 8 + (-589585052503013 / 20000000) * t ^ 10 + (5987679636524827 / 720000000) * t ^ 12 + (-465424735594549 / 360000000) * t ^ 14 + (12122775458137 / 23040000) * t ^ 16 + (11572066313059 / 360000000) * t ^ 18 + (-43482000157751 / 2160000000) * t ^ 20 + (6482269628033 / 360000000) * t ^ 22 + (-7758055489811 / 1440000000) * t ^ 24 + (-2386829517311 / 1080000000) * t ^ 26 + (67243358109 / 320000000) * t ^ 32 + (-70264544 / 375) * c * t ^ 4 + (859485904 / 1875) * c * t ^ 6 + (-15723692969 / 56250) * c * t ^ 8 + (-42080756053 / 703125) * c * t ^ 10 + (49220349191 / 937500) * c * t ^ 12 + (252700582379 / 8437500) * c * t ^ 14 + (-34152341977 / 1687500) * c * t ^ 16 + (49899084241 / 8437500) * c * t ^ 18 + (22104488663 / 25312500) * c * t ^ 20 + (-4757657123 / 8437500) * c * t ^ 22 + (5716733 / 2812500) * c * t ^ 24 + (-652227373 / 8437500) * c * t ^ 26 + (-5878544 / 6328125) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z29, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v28_00, v28_01, v28_02, v28_03, v28_04, v28_10, v28_11, v28_12, v28_13, v28_14, v28_20, v28_21, v28_22, v28_23, v28_24, v28_30, v28_31, v28_32, v28_33, v28_34, v28_40, v28_41, v28_42, v28_43, v28_44]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04, phase27_10, phase27_11, phase27_12, phase27_13, phase27_14, phase27_20, phase27_21, phase27_22, phase27_23, phase27_24, phase27_30, phase27_31, phase27_32, phase27_33, phase27_34, phase27_40, phase27_41, phase27_42, phase27_43, phase27_44]
  try simp only [star_one, star_neg]
  linear_combination ((-5596976 / 45) * t ^ 2 + (246458732 / 1125) * t ^ 4 + (-432895784 / 9375) * t ^ 6 + (-84367059217 / 1500000) * t ^ 8 + (-351832822133 / 45000000) * t ^ 10 + (165778430273 / 9000000) * t ^ 12 + (-2015799675329 / 162000000) * t ^ 14 + (423522401087 / 50625000) * t ^ 16 + (10049031847 / 270000000) * t ^ 18 + (606861927803 / 1215000000) * t ^ 20 + (46967386973 / 810000000) * t ^ 22 + (91876549447 / 2430000000) * t ^ 26 + (5018896 / 375) * c * t ^ 4 + (-8912608 / 225) * c * t ^ 6 + (2536828167 / 62500) * c * t ^ 8 + (-23927728069 / 1406250) * c * t ^ 10 + (14829933353 / 3375000) * c * t ^ 12 + (-30233373221 / 12656250) * c * t ^ 14 + (307623203 / 405000) * c * t ^ 16 + (-455223661 / 4218750) * c * t ^ 18 + (-551958857 / 16875000) * c * t ^ 20 + (342633913 / 12656250) * c * t ^ 22 + (5716733 / 16875000) * c * t ^ 24 + (46327552 / 18984375) * c * t ^ 26 + (-2939272 / 18984375) * c * t ^ 32 + (281824 / 1875) * c ^ 2 * t ^ 6 + (-49853432 / 253125) * c ^ 2 * t ^ 8 + (-76740602 / 6328125) * c ^ 2 * t ^ 10 + (342063067 / 6328125) * c ^ 2 * t ^ 12 + (36399553 / 2109375) * c ^ 2 * t ^ 14 + (-126004061 / 8437500) * c ^ 2 * t ^ 16 + (64512643 / 12656250) * c ^ 2 * t ^ 18 + (-2145908 / 18984375) * c ^ 2 * t ^ 20 + (-4707053 / 12656250) * c ^ 2 * t ^ 22 + (1389143 / 14062500) * c ^ 2 * t ^ 24 + (3954994 / 31640625) * c ^ 2 * t ^ 26 + (170528 / 94921875) * c ^ 2 * t ^ 32) * alpha_sq + ((-799568 / 15) * t ^ 2 + (59315788 / 375) * t ^ 4 + (-5425299002 / 28125) * t ^ 6 + (917804223581 / 6750000) * t ^ 8 + (-725435402833 / 11250000) * t ^ 10 + (1280941111219 / 67500000) * t ^ 12 + (-83780686397 / 22500000) * t ^ 14 + (20050488031 / 16875000) * t ^ 16 + (-71374577 / 937500) * t ^ 18 + (5018356181 / 202500000) * t ^ 20 + (-1179136787 / 67500000) * t ^ 22 + (-1389143 / 4687500) * t ^ 24 + (-130158061 / 42187500) * t ^ 26 + (-170528 / 31640625) * t ^ 32) * c_sq
#print axioms v29_00
#print axioms v29_11
#print axioms v29_22
#print axioms v29_33
#print axioms v29_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
noncomputable def z30 : Fin 30 → ℂ := Fin.snoc z29 (r ^ 2 * thetaMinus)
theorem v30_00 (t : ℂ) : (momentPoly 30 z30 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00]
  try simp only [phase27_00]
  try simp only [star_one, star_neg]
  ring
theorem v30_01 (t : ℂ) : (momentPoly 30 z30 0 1).eval t = ((-1 / 15) * c * t + (3 / 5) * alpha * t) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_01]
  try simp only [phase27_00, phase27_01]
  try simp only [star_one, star_neg]
  ring
theorem v30_02 (t : ℂ) : (momentPoly 30 z30 0 2).eval t = ((-4471 / 300) * t ^ 2 + (1481 / 100) * t ^ 4 + (73 / 15) * alpha * t ^ 2 + (-73 / 15) * alpha * t ^ 4 + (-16 / 225) * alpha * c * t ^ 2 + (-2 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_01, v29_02]
  try simp only [phase27_00, phase27_01, phase27_02]
  try simp only [star_one, star_neg]
  linear_combination ((16 / 225) * t ^ 2) * alpha_sq + ((-4 / 225) * t ^ 2) * c_sq
theorem v30_03 (t : ℂ) : (momentPoly 30 z30 0 3).eval t = ((-607 / 25) * t ^ 3 + (582 / 25) * t ^ 5 + 1 * t ^ 9 + (1469 / 500) * c * t ^ 3 + (-4087 / 1500) * c * t ^ 5 + (-71 / 1125) * c * t ^ 9 + (-49421 / 3000) * alpha * t ^ 3 + (77257 / 6000) * alpha * t ^ 5 + (9451 / 2000) * alpha * t ^ 9 + (-73 / 75) * alpha * c * t ^ 3 + (73 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_01, v29_02, v29_03]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-28 / 1125) * c * t ^ 3 + (4 / 375) * c * t ^ 5) * alpha_sq + ((-28 / 1125) * alpha * t ^ 3 + (-8 / 1125) * alpha * t ^ 5) * c_sq
theorem v30_04 (t : ℂ) : (momentPoly 30 z30 0 4).eval t = ((6110251 / 20000) * t ^ 4 + (-6386847 / 10000) * t ^ 6 + (48233779 / 120000) * t ^ 8 + (-7854941 / 90000) * t ^ 10 + (569897 / 40000) * t ^ 16 + (712 / 125) * c * t ^ 4 + (-1744 / 375) * c * t ^ 6 + (-292 / 375) * c * t ^ 8 + (-4 / 15) * c * t ^ 10 + (-22861 / 50) * alpha * t ^ 4 + (342793 / 375) * alpha * t ^ 6 + (-66881 / 150) * alpha * t ^ 8 + (-17432 / 1125) * alpha * t ^ 10 + (5033 / 1125) * alpha * t ^ 16 + (40607 / 11250) * alpha * c * t ^ 4 + (-11227 / 7500) * alpha * c * t ^ 6 + (-4151 / 5625) * alpha * c * t ^ 8 + (-90611 / 67500) * alpha * c * t ^ 10 + (-292 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_01, v29_02, v29_03, v29_04]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04]
  try simp only [star_one, star_neg]
  linear_combination ((-26399 / 11250) * t ^ 4 + (60781 / 22500) * t ^ 6 + (109811 / 67500) * t ^ 10 + (-584 / 1125) * c * t ^ 4 + (292 / 375) * c * t ^ 6 + (-292 / 1125) * c * t ^ 8 + (-112 / 16875) * c ^ 2 * t ^ 6 + (-16 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((2506 / 1875) * t ^ 4 + (-2498 / 1875) * t ^ 6 + (16 / 5625) * t ^ 8 + (-1136 / 16875) * t ^ 10 + (-584 / 1125) * alpha * t ^ 4 + (584 / 1125) * alpha * t ^ 6) * c_sq
theorem v30_10 (t : ℂ) : (momentPoly 30 z30 1 0).eval t = ((-1 / 15) * c * t + (-3 / 5) * alpha * t) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_10]
  try simp only [phase27_00, phase27_10]
  try simp only [star_one, star_neg]
  ring
theorem v30_11 (t : ℂ) : (momentPoly 30 z30 1 1).eval t = (30 + (-419 / 15) * t ^ 2) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_01, v29_10, v29_11]
  try simp only [phase27_00, phase27_01, phase27_10, phase27_11]
  try simp only [star_one, star_neg]
  linear_combination ((-16 / 225) * t ^ 2) * alpha_sq + ((-4 / 225) * t ^ 2) * c_sq
theorem v30_12 (t : ℂ) : (momentPoly 30 z30 1 2).eval t = ((219 / 25) * t ^ 3 + (-219 / 25) * t ^ 5 + (-59 / 15) * c * t + (4259 / 900) * c * t ^ 3 + (-281 / 300) * c * t ^ 5 + (177 / 5) * alpha * t + (-893 / 36) * alpha * t ^ 3 + (-8419 / 900) * alpha * t ^ 5 + (-73 / 225) * alpha * c * t ^ 3 + (73 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_01, v29_02, v29_10, v29_11, v29_12]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_10, phase27_11, phase27_12]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 225) * t ^ 3 + (73 / 225) * t ^ 5 + (28 / 3375) * c * t ^ 3 + (-4 / 1125) * c * t ^ 5) * alpha_sq + ((-28 / 3375) * alpha * t ^ 3 + (-8 / 3375) * alpha * t ^ 5) * c_sq
theorem v30_13 (t : ℂ) : (momentPoly 30 z30 1 3).eval t = ((-129659 / 100) * t ^ 2 + (99281 / 40) * t ^ 4 + (-7081547 / 6000) * t ^ 6 + (-96661 / 18000) * t ^ 10 + (-2 / 15) * c * t ^ 4 + (1 / 5) * c * t ^ 6 + (-1 / 15) * c * t ^ 10 + (2117 / 5) * alpha * t ^ 2 + (-60607 / 75) * alpha * t ^ 4 + (28532 / 75) * alpha * t ^ 6 + (64 / 15) * alpha * t ^ 10 + (-464 / 75) * alpha * c * t ^ 2 + (40739 / 9000) * alpha * c * t ^ 4 + (6347 / 3600) * alpha * c * t ^ 6 + (-4829 / 18000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_01, v29_02, v29_03, v29_10, v29_11, v29_12, v29_13]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_10, phase27_11, phase27_12, phase27_13]
  try simp only [star_one, star_neg]
  linear_combination ((464 / 75) * t ^ 2 + (-157681 / 45000) * t ^ 4 + (-193741 / 90000) * t ^ 6 + (-109811 / 270000) * t ^ 10) * alpha_sq + ((-116 / 75) * t ^ 2 + (3889 / 1875) * t ^ 4 + (-3859 / 5625) * t ^ 6 + (-284 / 16875) * t ^ 10 + (-292 / 1125) * alpha * t ^ 4 + (292 / 1125) * alpha * t ^ 6) * c_sq
theorem v30_14 (t : ℂ) : (momentPoly 30 z30 1 4).eval t = ((-69198 / 25) * t ^ 3 + (5499879 / 1250) * t ^ 5 + (-1401457 / 1875) * t ^ 7 + (-2702279 / 3750) * t ^ 9 + (-320596 / 1875) * t ^ 11 + (4408 / 625) * t ^ 17 + (83733 / 250) * c * t ^ 3 + (-116175469 / 180000) * c * t ^ 5 + (392903 / 1200) * c * t ^ 7 + (-10821431 / 360000) * c * t ^ 9 + (3876109 / 270000) * c * t ^ 11 + (-330431 / 360000) * c * t ^ 17 + (-938999 / 500) * alpha * t ^ 3 + (544946207 / 180000) * alpha * t ^ 5 + (-28137697 / 30000) * alpha * t ^ 7 + (21375649 / 72000) * alpha * t ^ 9 + (-26627003 / 54000) * alpha * t ^ 11 + (-14059289 / 1080000) * alpha * t ^ 17 + (-2774 / 25) * alpha * c * t ^ 3 + (2749967 / 11250) * alpha * c * t ^ 5 + (-907447 / 5625) * alpha * c * t ^ 7 + (317761 / 11250) * alpha * c * t ^ 9 + (-1768 / 16875) * alpha * c * t ^ 11 + (-5033 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_01, v29_02, v29_03, v29_04, v29_10, v29_11, v29_12, v29_13, v29_14]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04, phase27_10, phase27_11, phase27_12, phase27_13, phase27_14]
  try simp only [star_one, star_neg]
  linear_combination ((2774 / 25) * t ^ 3 + (-662083 / 3750) * t ^ 5 + (201697 / 5625) * t ^ 7 + (104363 / 3750) * t ^ 9 + (37232 / 16875) * t ^ 11 + (-5033 / 16875) * t ^ 17 + (-1064 / 375) * c * t ^ 3 + (18058 / 5625) * c * t ^ 5 + (-3628 / 28125) * c * t ^ 7 + (-25522 / 84375) * c * t ^ 9 + (7952 / 253125) * c * t ^ 11 + (-584 / 84375) * c * t ^ 17 + (-584 / 16875) * c ^ 2 * t ^ 7 + (584 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((1096 / 1875) * t ^ 5 + (-344 / 1125) * t ^ 7 + (-1168 / 5625) * t ^ 9 + (-16 / 225) * t ^ 11 + (-1064 / 375) * alpha * t ^ 3 + (29968 / 16875) * alpha * t ^ 5 + (34303 / 28125) * alpha * t ^ 7 + (-15548 / 84375) * alpha * t ^ 9 + (-77987 / 253125) * alpha * t ^ 11 + (-1168 / 253125) * alpha * t ^ 17) * c_sq
theorem v30_20 (t : ℂ) : (momentPoly 30 z30 2 0).eval t = ((-4471 / 300) * t ^ 2 + (1481 / 100) * t ^ 4 + (-73 / 15) * alpha * t ^ 2 + (73 / 15) * alpha * t ^ 4 + (16 / 225) * alpha * c * t ^ 2 + (2 / 225) * alpha * c * t ^ 4) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_10, v29_20]
  try simp only [phase27_00, phase27_10, phase27_20]
  try simp only [star_one, star_neg]
  linear_combination ((16 / 225) * t ^ 2) * alpha_sq + ((-4 / 225) * t ^ 2) * c_sq
theorem v30_21 (t : ℂ) : (momentPoly 30 z30 2 1).eval t = ((219 / 25) * t ^ 3 + (-219 / 25) * t ^ 5 + (-59 / 15) * c * t + (4259 / 900) * c * t ^ 3 + (-281 / 300) * c * t ^ 5 + (-177 / 5) * alpha * t + (893 / 36) * alpha * t ^ 3 + (8419 / 900) * alpha * t ^ 5 + (73 / 225) * alpha * c * t ^ 3 + (-73 / 225) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_01, v29_10, v29_11, v29_20, v29_21]
  try simp only [phase27_00, phase27_01, phase27_10, phase27_11, phase27_20, phase27_21]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 225) * t ^ 3 + (73 / 225) * t ^ 5 + (28 / 3375) * c * t ^ 3 + (-4 / 1125) * c * t ^ 5) * alpha_sq + ((28 / 3375) * alpha * t ^ 3 + (8 / 3375) * alpha * t ^ 5) * c_sq
theorem v30_22 (t : ℂ) : (momentPoly 30 z30 2 2).eval t = (1770 + (-48604 / 15) * t ^ 2 + (10110383 / 6000) * t ^ 4 + (-4238713 / 9000) * t ^ 6 + (4687957 / 18000) * t ^ 8 + (-2336 / 1125) * c * t ^ 4 + (2044 / 1125) * c * t ^ 6 + (292 / 1125) * c * t ^ 8) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_01, v29_02, v29_10, v29_11, v29_12, v29_20, v29_21, v29_22]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_10, phase27_11, phase27_12, phase27_20, phase27_21, phase27_22]
  try simp only [star_one, star_neg]
  linear_combination ((-1856 / 225) * t ^ 2 + (6136 / 1125) * t ^ 4 + (2216 / 1125) * t ^ 6 + (584 / 3375) * c * t ^ 4 + (-292 / 1125) * c * t ^ 6 + (292 / 3375) * c * t ^ 8 + (112 / 50625) * c ^ 2 * t ^ 6 + (16 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((-464 / 225) * t ^ 2 + (58 / 25) * t ^ 4 + (-7942 / 16875) * t ^ 6 + (-16 / 16875) * t ^ 8) * c_sq
theorem v30_23 (t : ℂ) : (momentPoly 30 z30 2 3).eval t = ((37449 / 25) * t ^ 3 + (-41507483 / 15000) * t ^ 5 + (32234287 / 30000) * t ^ 7 + (5319079 / 30000) * t ^ 9 + (2148269 / 30000) * t ^ 11 + (-541823 / 10000) * t ^ 13 + (-5134 / 15) * c * t + (80921 / 100) * c * t ^ 3 + (-11850221 / 18000) * c * t ^ 5 + (2129419 / 9000) * c * t ^ 7 + (-4166671 / 90000) * c * t ^ 9 + (121891 / 67500) * c * t ^ 11 + (-44731 / 45000) * c * t ^ 13 + (15402 / 5) * alpha * t + (-16967 / 4) * alpha * t ^ 3 + (-2259249 / 20000) * alpha * t ^ 5 + (118301933 / 120000) * alpha * t ^ 7 + (98812327 / 360000) * alpha * t ^ 9 + (-62186177 / 1080000) * alpha * t ^ 11 + (3202277 / 43200) * alpha * t ^ 13 + (-1387 / 25) * alpha * c * t ^ 3 + (602831 / 5625) * alpha * c * t ^ 5 + (-289742 / 5625) * alpha * c * t ^ 7 + (2186 / 5625) * alpha * c * t ^ 9 + (-4567 / 16875) * alpha * c * t ^ 11 + (-5033 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_01, v29_02, v29_03, v29_10, v29_11, v29_12, v29_13, v29_20, v29_21, v29_22, v29_23]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_10, phase27_11, phase27_12, phase27_13, phase27_20, phase27_21, phase27_22, phase27_23]
  try simp only [star_one, star_neg]
  linear_combination ((-1387 / 25) * t ^ 3 + (111923 / 1125) * t ^ 5 + (-16286 / 375) * t ^ 7 + (-25883 / 16875) * t ^ 11 + (16133 / 16875) * t ^ 13 + (532 / 375) * c * t ^ 3 + (-59371 / 33750) * c * t ^ 5 + (16391 / 84375) * c * t ^ 7 + (72179 / 675000) * c * t ^ 9 + (94787 / 1012500) * c * t ^ 11 + (-24817 / 675000) * c * t ^ 13 + (584 / 16875) * c ^ 2 * t ^ 7 + (-584 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((-4288 / 5625) * t ^ 5 + (644 / 1125) * t ^ 7 + (1168 / 5625) * t ^ 9 + (-4 / 225) * t ^ 11 + (-532 / 375) * alpha * t ^ 3 + (8257 / 11250) * alpha * t ^ 5 + (23131 / 37500) * alpha * t ^ 7 + (-112 / 84375) * alpha * t ^ 9 + (-62083 / 1012500) * alpha * t ^ 11 + (568 / 253125) * alpha * t ^ 13) * c_sq
theorem v30_24 (t : ℂ) : (momentPoly 30 z30 2 4).eval t = ((-22180631 / 150) * t ^ 2 + (41437519 / 100) * t ^ 4 + (-1400041953739 / 3600000) * t ^ 6 + (97845376633 / 720000) * t ^ 8 + (-35224086649 / 1440000) * t ^ 10 + (85985460289 / 7200000) * t ^ 12 + (-5277447443 / 5400000) * t ^ 14 + (-2925878843 / 21600000) * t ^ 18 + (2829160367 / 21600000) * t ^ 20 + (-448 / 15) * c * t ^ 4 + (7785923 / 56250) * c * t ^ 6 + (-3257351 / 22500) * c * t ^ 8 + (857177 / 112500) * c * t ^ 10 + (1486471 / 112500) * c * t ^ 12 + (204117 / 12500) * c * t ^ 14 + (-10066 / 9375) * c * t ^ 18 + (2 / 15) * c * t ^ 20 + (724306 / 15) * alpha * t ^ 2 + (-10086203 / 75) * alpha * t ^ 4 + (113850707659 / 900000) * alpha * t ^ 6 + (-191225609 / 4000) * alpha * t ^ 8 + (877555729 / 72000) * alpha * t ^ 10 + (-21554872307 / 5400000) * alpha * t ^ 12 + (-933242597 / 1350000) * alpha * t ^ 14 + (-780543017 / 5400000) * alpha * t ^ 18 + (252829411 / 1800000) * alpha * t ^ 20 + (-158752 / 225) * alpha * c * t ^ 2 + (1236302 / 1125) * alpha * c * t ^ 4 + (-26835479 / 225000) * alpha * c * t ^ 6 + (-11157409 / 45000) * alpha * c * t ^ 8 + (-31745041 / 450000) * alpha * c * t ^ 10 + (56657959 / 900000) * alpha * c * t ^ 12 + (-83416811 / 4050000) * alpha * c * t ^ 14 + (3660367 / 2025000) * alpha * c * t ^ 18 + (-65197 / 540000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_01, v29_02, v29_03, v29_04, v29_10, v29_11, v29_12, v29_13, v29_14, v29_20, v29_21, v29_22, v29_23, v29_24]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04, phase27_10, phase27_11, phase27_12, phase27_13, phase27_14, phase27_20, phase27_21, phase27_22, phase27_23, phase27_24]
  try simp only [star_one, star_neg]
  linear_combination ((158752 / 225) * t ^ 2 + (-4415068 / 5625) * t ^ 4 + (-199808059 / 675000) * t ^ 6 + (418455911 / 1350000) * t ^ 8 + (-28400963 / 1350000) * t ^ 10 + (80186077 / 1350000) * t ^ 12 + (31776571 / 1350000) * t ^ 14 + (106261 / 75000) * t ^ 18 + (-583478 / 84375) * c * t ^ 6 + (52933 / 3125) * c * t ^ 8 + (-1150336 / 84375) * c * t ^ 10 + (345889 / 84375) * c * t ^ 12 + (-133864 / 253125) * c * t ^ 14 + (-1184 / 253125) * c * t ^ 18 + (2 / 45) * c * t ^ 20 + (-10394 / 253125) * c ^ 2 * t ^ 8 + (1933 / 140625) * c ^ 2 * t ^ 10 + (15436 / 1265625) * c ^ 2 * t ^ 12 + (85939 / 3796875) * c ^ 2 * t ^ 14 + (8176 / 3796875) * c ^ 2 * t ^ 18 + (2336 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-39688 / 225) * t ^ 2 + (871136 / 1875) * t ^ 4 + (-300881761 / 675000) * t ^ 6 + (61153069 / 337500) * t ^ 8 + (-206581147 / 6750000) * t ^ 10 + (10868671 / 1687500) * t ^ 12 + (-1267834 / 1265625) * t ^ 14 + (-4746481 / 20250000) * t ^ 18 + (-2336 / 1265625) * t ^ 20 + (-65408 / 1125) * alpha * t ^ 4 + (393062 / 3375) * alpha * t ^ 6 + (-1838828 / 28125) * alpha * t ^ 8 + (626698 / 84375) * alpha * t ^ 10 + (7168 / 253125) * alpha * t ^ 12 + (-80528 / 253125) * alpha * t ^ 14 + (-20132 / 253125) * alpha * t ^ 18) * c_sq
theorem v30_30 (t : ℂ) : (momentPoly 30 z30 3 0).eval t = ((-607 / 25) * t ^ 3 + (582 / 25) * t ^ 5 + 1 * t ^ 9 + (1469 / 500) * c * t ^ 3 + (-4087 / 1500) * c * t ^ 5 + (-71 / 1125) * c * t ^ 9 + (49421 / 3000) * alpha * t ^ 3 + (-77257 / 6000) * alpha * t ^ 5 + (-9451 / 2000) * alpha * t ^ 9 + (73 / 75) * alpha * c * t ^ 3 + (-73 / 75) * alpha * c * t ^ 5) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_10, v29_20, v29_30]
  try simp only [phase27_00, phase27_10, phase27_20, phase27_30]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-28 / 1125) * c * t ^ 3 + (4 / 375) * c * t ^ 5) * alpha_sq + ((28 / 1125) * alpha * t ^ 3 + (8 / 1125) * alpha * t ^ 5) * c_sq
theorem v30_31 (t : ℂ) : (momentPoly 30 z30 3 1).eval t = ((-129659 / 100) * t ^ 2 + (99281 / 40) * t ^ 4 + (-7081547 / 6000) * t ^ 6 + (-96661 / 18000) * t ^ 10 + (-2 / 15) * c * t ^ 4 + (1 / 5) * c * t ^ 6 + (-1 / 15) * c * t ^ 10 + (-2117 / 5) * alpha * t ^ 2 + (60607 / 75) * alpha * t ^ 4 + (-28532 / 75) * alpha * t ^ 6 + (-64 / 15) * alpha * t ^ 10 + (464 / 75) * alpha * c * t ^ 2 + (-40739 / 9000) * alpha * c * t ^ 4 + (-6347 / 3600) * alpha * c * t ^ 6 + (4829 / 18000) * alpha * c * t ^ 10) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_01, v29_10, v29_11, v29_20, v29_21, v29_30, v29_31]
  try simp only [phase27_00, phase27_01, phase27_10, phase27_11, phase27_20, phase27_21, phase27_30, phase27_31]
  try simp only [star_one, star_neg]
  linear_combination ((464 / 75) * t ^ 2 + (-157681 / 45000) * t ^ 4 + (-193741 / 90000) * t ^ 6 + (-109811 / 270000) * t ^ 10) * alpha_sq + ((-116 / 75) * t ^ 2 + (3889 / 1875) * t ^ 4 + (-3859 / 5625) * t ^ 6 + (-284 / 16875) * t ^ 10 + (292 / 1125) * alpha * t ^ 4 + (-292 / 1125) * alpha * t ^ 6) * c_sq
theorem v30_32 (t : ℂ) : (momentPoly 30 z30 3 2).eval t = ((37449 / 25) * t ^ 3 + (-41507483 / 15000) * t ^ 5 + (32234287 / 30000) * t ^ 7 + (5319079 / 30000) * t ^ 9 + (2148269 / 30000) * t ^ 11 + (-541823 / 10000) * t ^ 13 + (-5134 / 15) * c * t + (80921 / 100) * c * t ^ 3 + (-11850221 / 18000) * c * t ^ 5 + (2129419 / 9000) * c * t ^ 7 + (-4166671 / 90000) * c * t ^ 9 + (121891 / 67500) * c * t ^ 11 + (-44731 / 45000) * c * t ^ 13 + (-15402 / 5) * alpha * t + (16967 / 4) * alpha * t ^ 3 + (2259249 / 20000) * alpha * t ^ 5 + (-118301933 / 120000) * alpha * t ^ 7 + (-98812327 / 360000) * alpha * t ^ 9 + (62186177 / 1080000) * alpha * t ^ 11 + (-3202277 / 43200) * alpha * t ^ 13 + (1387 / 25) * alpha * c * t ^ 3 + (-602831 / 5625) * alpha * c * t ^ 5 + (289742 / 5625) * alpha * c * t ^ 7 + (-2186 / 5625) * alpha * c * t ^ 9 + (4567 / 16875) * alpha * c * t ^ 11 + (5033 / 16875) * alpha * c * t ^ 13) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_01, v29_02, v29_10, v29_11, v29_12, v29_20, v29_21, v29_22, v29_30, v29_31, v29_32]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_10, phase27_11, phase27_12, phase27_20, phase27_21, phase27_22, phase27_30, phase27_31, phase27_32]
  try simp only [star_one, star_neg]
  linear_combination ((-1387 / 25) * t ^ 3 + (111923 / 1125) * t ^ 5 + (-16286 / 375) * t ^ 7 + (-25883 / 16875) * t ^ 11 + (16133 / 16875) * t ^ 13 + (532 / 375) * c * t ^ 3 + (-59371 / 33750) * c * t ^ 5 + (16391 / 84375) * c * t ^ 7 + (72179 / 675000) * c * t ^ 9 + (94787 / 1012500) * c * t ^ 11 + (-24817 / 675000) * c * t ^ 13 + (584 / 16875) * c ^ 2 * t ^ 7 + (-584 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((-4288 / 5625) * t ^ 5 + (644 / 1125) * t ^ 7 + (1168 / 5625) * t ^ 9 + (-4 / 225) * t ^ 11 + (532 / 375) * alpha * t ^ 3 + (-8257 / 11250) * alpha * t ^ 5 + (-23131 / 37500) * alpha * t ^ 7 + (112 / 84375) * alpha * t ^ 9 + (62083 / 1012500) * alpha * t ^ 11 + (-568 / 253125) * alpha * t ^ 13) * c_sq
theorem v30_33 (t : ℂ) : (momentPoly 30 z30 3 3).eval t = (154020 + (-2078659 / 5) * t ^ 2 + (212318043 / 500) * t ^ 4 + (-55298823777 / 200000) * t ^ 6 + (20669473307 / 120000) * t ^ 8 + (-46890960417 / 800000) * t ^ 10 + (162987957 / 200000) * t ^ 12 + (-3265436113 / 3600000) * t ^ 14 + (839706037 / 21600000) * t ^ 18 + (-65408 / 125) * c * t ^ 4 + (2256829 / 2500) * c * t ^ 6 + (-1197313 / 5000) * c * t ^ 8 + (-400271 / 3000) * c * t ^ 10 + (-1084811 / 45000) * c * t ^ 12 + (88259 / 5000) * c * t ^ 14 + (-142 / 1125) * c * t ^ 18) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_01, v29_02, v29_03, v29_10, v29_11, v29_12, v29_13, v29_20, v29_21, v29_22, v29_23, v29_30, v29_31, v29_32, v29_33]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_10, phase27_11, phase27_12, phase27_13, phase27_20, phase27_21, phase27_22, phase27_23, phase27_30, phase27_31, phase27_32, phase27_33]
  try simp only [star_one, star_neg]
  linear_combination ((-79376 / 75) * t ^ 2 + (171808 / 125) * t ^ 4 + (26506571 / 450000) * t ^ 6 + (-53077531 / 180000) * t ^ 8 + (-23592101 / 300000) * t ^ 10 + (274756397 / 13500000) * t ^ 12 + (-412842329 / 13500000) * t ^ 14 + (-18016583 / 10125000) * t ^ 18 + (16352 / 375) * c * t ^ 4 + (-2931268 / 28125) * c * t ^ 6 + (243836 / 3125) * c * t ^ 8 + (-496156 / 28125) * c * t ^ 10 + (1112 / 1125) * c * t ^ 12 + (-284 / 375) * c * t ^ 14 + (1904 / 3375) * c ^ 2 * t ^ 6 + (-10577 / 28125) * c ^ 2 * t ^ 8 + (-9661 / 56250) * c ^ 2 * t ^ 10 + (4669 / 168750) * c ^ 2 * t ^ 14) * alpha_sq + ((-19844 / 75) * t ^ 2 + (14616 / 25) * t ^ 4 + (-50913577 / 112500) * t ^ 6 + (4569253 / 28125) * t ^ 8 + (-407073 / 12500) * t ^ 10 + (531761 / 281250) * t ^ 12 + (-618013 / 421875) * t ^ 14 + (-20164 / 1265625) * t ^ 18) * c_sq
theorem v30_34 (t : ℂ) : (momentPoly 30 z30 3 4).eval t = ((6295374 / 25) * t ^ 3 + (-335392093 / 500) * t ^ 5 + (794327600419 / 1500000) * t ^ 7 + (-34138410069 / 500000) * t ^ 9 + (-8327879957 / 600000) * t ^ 11 + (-106636896553 / 2250000) * t ^ 13 + (28036274777 / 1125000) * t ^ 15 + (-52699549613 / 9000000) * t ^ 17 + (-7714027663 / 9000000) * t ^ 19 + (341052663 / 500000) * t ^ 21 + (233009807 / 3000000) * t ^ 25 + (-195209 / 5) * c * t + (6801623 / 50) * c * t ^ 3 + (-114802453 / 600) * c * t ^ 5 + (2615714319379 / 18000000) * c * t ^ 7 + (-403147418899 / 6000000) * c * t ^ 9 + (44333946167 / 2400000) * c * t ^ 11 + (-324309737111 / 108000000) * c * t ^ 13 + (7027936967 / 9000000) * c * t ^ 15 + (-836667589 / 27000000) * c * t ^ 17 + (7177857197 / 324000000) * c * t ^ 19 + (-2228299451 / 108000000) * c * t ^ 21 + (-9700291 / 9000000) * c * t ^ 25 + (1756881 / 5) * alpha * t + (-1426121 / 2) * alpha * t ^ 3 + (1329303089 / 6000) * alpha * t ^ 5 + (834265760521 / 4000000) * alpha * t ^ 7 + (-235945894969 / 72000000) * alpha * t ^ 9 + (-1046855376431 / 14400000) * alpha * t ^ 11 + (523439229173 / 17280000) * alpha * t ^ 13 + (-184280928947 / 9000000) * alpha * t ^ 15 + (-984447405893 / 432000000) * alpha * t ^ 17 + (218486678153 / 648000000) * alpha * t ^ 19 + (-113682135317 / 432000000) * alpha * t ^ 21 + (-16384030091 / 259200000) * alpha * t ^ 25 + (-233162 / 25) * alpha * c * t ^ 3 + (3298629 / 125) * alpha * c * t ^ 5 + (-38035421737 / 1500000) * alpha * c * t ^ 7 + (4884993177 / 500000) * alpha * c * t ^ 9 + (-439990381 / 200000) * alpha * c * t ^ 11 + (14236942483 / 27000000) * alpha * c * t ^ 13 + (1109960669 / 6750000) * alpha * c * t ^ 15 + (49164517 / 1687500) * alpha * c * t ^ 17 + (2456905531 / 81000000) * alpha * c * t ^ 19 + (-716538281 / 27000000) * alpha * c * t ^ 21 + (-379243 / 1265625) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_01, v29_02, v29_03, v29_04, v29_10, v29_11, v29_12, v29_13, v29_14, v29_20, v29_21, v29_22, v29_23, v29_24, v29_30, v29_31, v29_32, v29_33, v29_34]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04, phase27_10, phase27_11, phase27_12, phase27_13, phase27_14, phase27_20, phase27_21, phase27_22, phase27_23, phase27_24, phase27_30, phase27_31, phase27_32, phase27_33, phase27_34]
  try simp only [star_one, star_neg]
  linear_combination ((-233162 / 25) * t ^ 3 + (1789027 / 75) * t ^ 5 + (-90399081979 / 4500000) * t ^ 7 + (29937879217 / 4500000) * t ^ 9 + (-6773463059 / 3000000) * t ^ 11 + (37173470371 / 27000000) * t ^ 13 + (-1951934311 / 6750000) * t ^ 15 + (23064223 / 281250) * t ^ 17 + (1946743099 / 81000000) * t ^ 19 + (-711459881 / 27000000) * t ^ 21 + (-1112293 / 1265625) * t ^ 25 + (89432 / 375) * c * t ^ 3 + (-108481 / 225) * c * t ^ 5 + (735356459 / 3375000) * c * t ^ 7 + (144716233 / 3375000) * c * t ^ 9 + (18461861 / 1125000) * c * t ^ 11 + (-495678341 / 10125000) * c * t ^ 13 + (205139899 / 11250000) * c * t ^ 15 + (-331821077 / 101250000) * c * t ^ 17 + (27089723 / 60750000) * c * t ^ 19 + (15472193 / 101250000) * c * t ^ 21 + (-1811641 / 25312500) * c * t ^ 25 + (195056 / 16875) * c ^ 2 * t ^ 7 + (-391894 / 16875) * c ^ 2 * t ^ 9 + (5492756 / 421875) * c ^ 2 * t ^ 11 + (-606874 / 421875) * c ^ 2 * t ^ 13 + (14936 / 421875) * c ^ 2 * t ^ 15 + (40264 / 1265625) * c ^ 2 * t ^ 17 + (42632 / 1265625) * c ^ 2 * t ^ 19 + (-4 / 225) * c ^ 2 * t ^ 21) * alpha_sq + ((-94336 / 375) * t ^ 5 + (57328283 / 140625) * t ^ 7 + (-9359 / 150) * t ^ 9 + (-29507057 / 281250) * t ^ 11 + (-2560349 / 843750) * t ^ 13 + (12606629 / 843750) * t ^ 15 + (-81728 / 421875) * t ^ 17 + (-260488 / 421875) * t ^ 19 + (8 / 75) * t ^ 21 + (-89432 / 375) * alpha * t ^ 3 + (69253 / 225) * alpha * t ^ 5 + (59648387 / 1125000) * alpha * t ^ 7 + (-79425527 / 675000) * alpha * t ^ 9 + (-103224089 / 6750000) * alpha * t ^ 11 + (22322906 / 1265625) * alpha * t ^ 13 + (-147187151 / 16875000) * alpha * t ^ 15 + (-1173943 / 6328125) * alpha * t ^ 17 + (40774813 / 60750000) * alpha * t ^ 19 + (-4398959 / 50625000) * alpha * t ^ 21 + (-82928 / 18984375) * alpha * t ^ 25) * c_sq
theorem v30_40 (t : ℂ) : (momentPoly 30 z30 4 0).eval t = ((6110251 / 20000) * t ^ 4 + (-6386847 / 10000) * t ^ 6 + (48233779 / 120000) * t ^ 8 + (-7854941 / 90000) * t ^ 10 + (569897 / 40000) * t ^ 16 + (712 / 125) * c * t ^ 4 + (-1744 / 375) * c * t ^ 6 + (-292 / 375) * c * t ^ 8 + (-4 / 15) * c * t ^ 10 + (22861 / 50) * alpha * t ^ 4 + (-342793 / 375) * alpha * t ^ 6 + (66881 / 150) * alpha * t ^ 8 + (17432 / 1125) * alpha * t ^ 10 + (-5033 / 1125) * alpha * t ^ 16 + (-40607 / 11250) * alpha * c * t ^ 4 + (11227 / 7500) * alpha * c * t ^ 6 + (4151 / 5625) * alpha * c * t ^ 8 + (90611 / 67500) * alpha * c * t ^ 10 + (292 / 16875) * alpha * c * t ^ 16) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_10, v29_20, v29_30, v29_40]
  try simp only [phase27_00, phase27_10, phase27_20, phase27_30, phase27_40]
  try simp only [star_one, star_neg]
  linear_combination ((-26399 / 11250) * t ^ 4 + (60781 / 22500) * t ^ 6 + (109811 / 67500) * t ^ 10 + (-584 / 1125) * c * t ^ 4 + (292 / 375) * c * t ^ 6 + (-292 / 1125) * c * t ^ 8 + (-112 / 16875) * c ^ 2 * t ^ 6 + (-16 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((2506 / 1875) * t ^ 4 + (-2498 / 1875) * t ^ 6 + (16 / 5625) * t ^ 8 + (-1136 / 16875) * t ^ 10 + (584 / 1125) * alpha * t ^ 4 + (-584 / 1125) * alpha * t ^ 6) * c_sq
theorem v30_41 (t : ℂ) : (momentPoly 30 z30 4 1).eval t = ((-69198 / 25) * t ^ 3 + (5499879 / 1250) * t ^ 5 + (-1401457 / 1875) * t ^ 7 + (-2702279 / 3750) * t ^ 9 + (-320596 / 1875) * t ^ 11 + (4408 / 625) * t ^ 17 + (83733 / 250) * c * t ^ 3 + (-116175469 / 180000) * c * t ^ 5 + (392903 / 1200) * c * t ^ 7 + (-10821431 / 360000) * c * t ^ 9 + (3876109 / 270000) * c * t ^ 11 + (-330431 / 360000) * c * t ^ 17 + (938999 / 500) * alpha * t ^ 3 + (-544946207 / 180000) * alpha * t ^ 5 + (28137697 / 30000) * alpha * t ^ 7 + (-21375649 / 72000) * alpha * t ^ 9 + (26627003 / 54000) * alpha * t ^ 11 + (14059289 / 1080000) * alpha * t ^ 17 + (2774 / 25) * alpha * c * t ^ 3 + (-2749967 / 11250) * alpha * c * t ^ 5 + (907447 / 5625) * alpha * c * t ^ 7 + (-317761 / 11250) * alpha * c * t ^ 9 + (1768 / 16875) * alpha * c * t ^ 11 + (5033 / 16875) * alpha * c * t ^ 17) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_01, v29_10, v29_11, v29_20, v29_21, v29_30, v29_31, v29_40, v29_41]
  try simp only [phase27_00, phase27_01, phase27_10, phase27_11, phase27_20, phase27_21, phase27_30, phase27_31, phase27_40, phase27_41]
  try simp only [star_one, star_neg]
  linear_combination ((2774 / 25) * t ^ 3 + (-662083 / 3750) * t ^ 5 + (201697 / 5625) * t ^ 7 + (104363 / 3750) * t ^ 9 + (37232 / 16875) * t ^ 11 + (-5033 / 16875) * t ^ 17 + (-1064 / 375) * c * t ^ 3 + (18058 / 5625) * c * t ^ 5 + (-3628 / 28125) * c * t ^ 7 + (-25522 / 84375) * c * t ^ 9 + (7952 / 253125) * c * t ^ 11 + (-584 / 84375) * c * t ^ 17 + (-584 / 16875) * c ^ 2 * t ^ 7 + (584 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((1096 / 1875) * t ^ 5 + (-344 / 1125) * t ^ 7 + (-1168 / 5625) * t ^ 9 + (-16 / 225) * t ^ 11 + (1064 / 375) * alpha * t ^ 3 + (-29968 / 16875) * alpha * t ^ 5 + (-34303 / 28125) * alpha * t ^ 7 + (15548 / 84375) * alpha * t ^ 9 + (77987 / 253125) * alpha * t ^ 11 + (1168 / 253125) * alpha * t ^ 17) * c_sq
theorem v30_42 (t : ℂ) : (momentPoly 30 z30 4 2).eval t = ((-22180631 / 150) * t ^ 2 + (41437519 / 100) * t ^ 4 + (-1400041953739 / 3600000) * t ^ 6 + (97845376633 / 720000) * t ^ 8 + (-35224086649 / 1440000) * t ^ 10 + (85985460289 / 7200000) * t ^ 12 + (-5277447443 / 5400000) * t ^ 14 + (-2925878843 / 21600000) * t ^ 18 + (2829160367 / 21600000) * t ^ 20 + (-448 / 15) * c * t ^ 4 + (7785923 / 56250) * c * t ^ 6 + (-3257351 / 22500) * c * t ^ 8 + (857177 / 112500) * c * t ^ 10 + (1486471 / 112500) * c * t ^ 12 + (204117 / 12500) * c * t ^ 14 + (-10066 / 9375) * c * t ^ 18 + (2 / 15) * c * t ^ 20 + (-724306 / 15) * alpha * t ^ 2 + (10086203 / 75) * alpha * t ^ 4 + (-113850707659 / 900000) * alpha * t ^ 6 + (191225609 / 4000) * alpha * t ^ 8 + (-877555729 / 72000) * alpha * t ^ 10 + (21554872307 / 5400000) * alpha * t ^ 12 + (933242597 / 1350000) * alpha * t ^ 14 + (780543017 / 5400000) * alpha * t ^ 18 + (-252829411 / 1800000) * alpha * t ^ 20 + (158752 / 225) * alpha * c * t ^ 2 + (-1236302 / 1125) * alpha * c * t ^ 4 + (26835479 / 225000) * alpha * c * t ^ 6 + (11157409 / 45000) * alpha * c * t ^ 8 + (31745041 / 450000) * alpha * c * t ^ 10 + (-56657959 / 900000) * alpha * c * t ^ 12 + (83416811 / 4050000) * alpha * c * t ^ 14 + (-3660367 / 2025000) * alpha * c * t ^ 18 + (65197 / 540000) * alpha * c * t ^ 20) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_01, v29_02, v29_10, v29_11, v29_12, v29_20, v29_21, v29_22, v29_30, v29_31, v29_32, v29_40, v29_41, v29_42]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_10, phase27_11, phase27_12, phase27_20, phase27_21, phase27_22, phase27_30, phase27_31, phase27_32, phase27_40, phase27_41, phase27_42]
  try simp only [star_one, star_neg]
  linear_combination ((158752 / 225) * t ^ 2 + (-4415068 / 5625) * t ^ 4 + (-199808059 / 675000) * t ^ 6 + (418455911 / 1350000) * t ^ 8 + (-28400963 / 1350000) * t ^ 10 + (80186077 / 1350000) * t ^ 12 + (31776571 / 1350000) * t ^ 14 + (106261 / 75000) * t ^ 18 + (-583478 / 84375) * c * t ^ 6 + (52933 / 3125) * c * t ^ 8 + (-1150336 / 84375) * c * t ^ 10 + (345889 / 84375) * c * t ^ 12 + (-133864 / 253125) * c * t ^ 14 + (-1184 / 253125) * c * t ^ 18 + (2 / 45) * c * t ^ 20 + (-10394 / 253125) * c ^ 2 * t ^ 8 + (1933 / 140625) * c ^ 2 * t ^ 10 + (15436 / 1265625) * c ^ 2 * t ^ 12 + (85939 / 3796875) * c ^ 2 * t ^ 14 + (8176 / 3796875) * c ^ 2 * t ^ 18 + (2336 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-39688 / 225) * t ^ 2 + (871136 / 1875) * t ^ 4 + (-300881761 / 675000) * t ^ 6 + (61153069 / 337500) * t ^ 8 + (-206581147 / 6750000) * t ^ 10 + (10868671 / 1687500) * t ^ 12 + (-1267834 / 1265625) * t ^ 14 + (-4746481 / 20250000) * t ^ 18 + (-2336 / 1265625) * t ^ 20 + (65408 / 1125) * alpha * t ^ 4 + (-393062 / 3375) * alpha * t ^ 6 + (1838828 / 28125) * alpha * t ^ 8 + (-626698 / 84375) * alpha * t ^ 10 + (-7168 / 253125) * alpha * t ^ 12 + (80528 / 253125) * alpha * t ^ 14 + (20132 / 253125) * alpha * t ^ 18) * c_sq
theorem v30_43 (t : ℂ) : (momentPoly 30 z30 4 3).eval t = ((6295374 / 25) * t ^ 3 + (-335392093 / 500) * t ^ 5 + (794327600419 / 1500000) * t ^ 7 + (-34138410069 / 500000) * t ^ 9 + (-8327879957 / 600000) * t ^ 11 + (-106636896553 / 2250000) * t ^ 13 + (28036274777 / 1125000) * t ^ 15 + (-52699549613 / 9000000) * t ^ 17 + (-7714027663 / 9000000) * t ^ 19 + (341052663 / 500000) * t ^ 21 + (233009807 / 3000000) * t ^ 25 + (-195209 / 5) * c * t + (6801623 / 50) * c * t ^ 3 + (-114802453 / 600) * c * t ^ 5 + (2615714319379 / 18000000) * c * t ^ 7 + (-403147418899 / 6000000) * c * t ^ 9 + (44333946167 / 2400000) * c * t ^ 11 + (-324309737111 / 108000000) * c * t ^ 13 + (7027936967 / 9000000) * c * t ^ 15 + (-836667589 / 27000000) * c * t ^ 17 + (7177857197 / 324000000) * c * t ^ 19 + (-2228299451 / 108000000) * c * t ^ 21 + (-9700291 / 9000000) * c * t ^ 25 + (-1756881 / 5) * alpha * t + (1426121 / 2) * alpha * t ^ 3 + (-1329303089 / 6000) * alpha * t ^ 5 + (-834265760521 / 4000000) * alpha * t ^ 7 + (235945894969 / 72000000) * alpha * t ^ 9 + (1046855376431 / 14400000) * alpha * t ^ 11 + (-523439229173 / 17280000) * alpha * t ^ 13 + (184280928947 / 9000000) * alpha * t ^ 15 + (984447405893 / 432000000) * alpha * t ^ 17 + (-218486678153 / 648000000) * alpha * t ^ 19 + (113682135317 / 432000000) * alpha * t ^ 21 + (16384030091 / 259200000) * alpha * t ^ 25 + (233162 / 25) * alpha * c * t ^ 3 + (-3298629 / 125) * alpha * c * t ^ 5 + (38035421737 / 1500000) * alpha * c * t ^ 7 + (-4884993177 / 500000) * alpha * c * t ^ 9 + (439990381 / 200000) * alpha * c * t ^ 11 + (-14236942483 / 27000000) * alpha * c * t ^ 13 + (-1109960669 / 6750000) * alpha * c * t ^ 15 + (-49164517 / 1687500) * alpha * c * t ^ 17 + (-2456905531 / 81000000) * alpha * c * t ^ 19 + (716538281 / 27000000) * alpha * c * t ^ 21 + (379243 / 1265625) * alpha * c * t ^ 25) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_01, v29_02, v29_03, v29_10, v29_11, v29_12, v29_13, v29_20, v29_21, v29_22, v29_23, v29_30, v29_31, v29_32, v29_33, v29_40, v29_41, v29_42, v29_43]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_10, phase27_11, phase27_12, phase27_13, phase27_20, phase27_21, phase27_22, phase27_23, phase27_30, phase27_31, phase27_32, phase27_33, phase27_40, phase27_41, phase27_42, phase27_43]
  try simp only [star_one, star_neg]
  linear_combination ((-233162 / 25) * t ^ 3 + (1789027 / 75) * t ^ 5 + (-90399081979 / 4500000) * t ^ 7 + (29937879217 / 4500000) * t ^ 9 + (-6773463059 / 3000000) * t ^ 11 + (37173470371 / 27000000) * t ^ 13 + (-1951934311 / 6750000) * t ^ 15 + (23064223 / 281250) * t ^ 17 + (1946743099 / 81000000) * t ^ 19 + (-711459881 / 27000000) * t ^ 21 + (-1112293 / 1265625) * t ^ 25 + (89432 / 375) * c * t ^ 3 + (-108481 / 225) * c * t ^ 5 + (735356459 / 3375000) * c * t ^ 7 + (144716233 / 3375000) * c * t ^ 9 + (18461861 / 1125000) * c * t ^ 11 + (-495678341 / 10125000) * c * t ^ 13 + (205139899 / 11250000) * c * t ^ 15 + (-331821077 / 101250000) * c * t ^ 17 + (27089723 / 60750000) * c * t ^ 19 + (15472193 / 101250000) * c * t ^ 21 + (-1811641 / 25312500) * c * t ^ 25 + (195056 / 16875) * c ^ 2 * t ^ 7 + (-391894 / 16875) * c ^ 2 * t ^ 9 + (5492756 / 421875) * c ^ 2 * t ^ 11 + (-606874 / 421875) * c ^ 2 * t ^ 13 + (14936 / 421875) * c ^ 2 * t ^ 15 + (40264 / 1265625) * c ^ 2 * t ^ 17 + (42632 / 1265625) * c ^ 2 * t ^ 19 + (-4 / 225) * c ^ 2 * t ^ 21) * alpha_sq + ((-94336 / 375) * t ^ 5 + (57328283 / 140625) * t ^ 7 + (-9359 / 150) * t ^ 9 + (-29507057 / 281250) * t ^ 11 + (-2560349 / 843750) * t ^ 13 + (12606629 / 843750) * t ^ 15 + (-81728 / 421875) * t ^ 17 + (-260488 / 421875) * t ^ 19 + (8 / 75) * t ^ 21 + (89432 / 375) * alpha * t ^ 3 + (-69253 / 225) * alpha * t ^ 5 + (-59648387 / 1125000) * alpha * t ^ 7 + (79425527 / 675000) * alpha * t ^ 9 + (103224089 / 6750000) * alpha * t ^ 11 + (-22322906 / 1265625) * alpha * t ^ 13 + (147187151 / 16875000) * alpha * t ^ 15 + (1173943 / 6328125) * alpha * t ^ 17 + (-40774813 / 60750000) * alpha * t ^ 19 + (4398959 / 50625000) * alpha * t ^ 21 + (82928 / 18984375) * alpha * t ^ 25) * c_sq
theorem v30_44 (t : ℂ) : (momentPoly 30 z30 4 4).eval t = (17568810 + (-310733752 / 5) * t ^ 2 + (11687602748 / 125) * t ^ 4 + (-1768522396931 / 18750) * t ^ 6 + (57560394050827213 / 720000000) * t ^ 8 + (-2766485084419459 / 60000000) * t ^ 10 + (1854857982210607 / 144000000) * t ^ 12 + (-772232328784081 / 360000000) * t ^ 14 + (2373857773881269 / 2880000000) * t ^ 16 + (1239692586541 / 120000000) * t ^ 18 + (-33497918687783 / 2160000000) * t ^ 20 + (513064948037 / 40000000) * t ^ 22 + (-15652537874713 / 4320000000) * t ^ 24 + (-9588696305113 / 3240000000) * t ^ 26 + (6045388847917 / 25920000000) * t ^ 32 + (-43206656 / 375) * c * t ^ 4 + (549480556 / 1875) * c * t ^ 6 + (-138445070677 / 703125) * c * t ^ 8 + (-18826696859 / 937500) * c * t ^ 10 + (1687955509 / 56250) * c * t ^ 12 + (142981619531 / 8437500) * c * t ^ 14 + (-21175146089 / 1875000) * c * t ^ 16 + (56345302969 / 16875000) * c * t ^ 18 + (13483836809 / 25312500) * c * t ^ 20 + (-1472831779 / 4218750) * c * t ^ 22 + (19916023 / 16875000) * c * t ^ 24 + (-2076298823 / 50625000) * c * t ^ 26 + (-2939272 / 6328125) * c * t ^ 32) := by
  rw [momentPoly]
  simp only [z30, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v29_00, v29_01, v29_02, v29_03, v29_04, v29_10, v29_11, v29_12, v29_13, v29_14, v29_20, v29_21, v29_22, v29_23, v29_24, v29_30, v29_31, v29_32, v29_33, v29_34, v29_40, v29_41, v29_42, v29_43, v29_44]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04, phase27_10, phase27_11, phase27_12, phase27_13, phase27_14, phase27_20, phase27_21, phase27_22, phase27_23, phase27_24, phase27_30, phase27_31, phase27_32, phase27_33, phase27_34, phase27_40, phase27_41, phase27_42, phase27_43, phase27_44]
  try simp only [star_one, star_neg]
  linear_combination ((-11865728 / 75) * t ^ 2 + (113491456 / 375) * t ^ 4 + (-746563661 / 9375) * t ^ 6 + (-664627181963 / 7500000) * t ^ 8 + (-2698285603 / 15000000) * t ^ 10 + (795657358249 / 27000000) * t ^ 12 + (-4592156667139 / 270000000) * t ^ 14 + (21758617208 / 2109375) * t ^ 16 + (6802744297 / 18000000) * t ^ 18 + (45831865807 / 81000000) * t ^ 20 + (26289811171 / 270000000) * t ^ 22 + (37530590221 / 810000000) * t ^ 26 + (10801664 / 1125) * c * t ^ 4 + (-292293992 / 9375) * c * t ^ 6 + (155270493227 / 4218750) * c * t ^ 8 + (-32880227689 / 1687500) * c * t ^ 10 + (4953078353 / 843750) * c * t ^ 12 + (-4568290969 / 2025000) * c * t ^ 14 + (35114749819 / 50625000) * c * t ^ 16 + (-24951943 / 506250) * c * t ^ 18 + (-1321856363 / 75937500) * c * t ^ 20 + (218170793 / 16875000) * c * t ^ 22 + (19916023 / 50625000) * c * t ^ 24 + (11406688 / 6328125) * c * t ^ 26 + (-2939272 / 18984375) * c * t ^ 32 + (2121056 / 16875) * c ^ 2 * t ^ 6 + (-46005152 / 253125) * c ^ 2 * t ^ 8 + (1305737 / 234375) * c ^ 2 * t ^ 10 + (19482196 / 421875) * c ^ 2 * t ^ 12 + (33243449 / 2531250) * c ^ 2 * t ^ 14 + (-150023969 / 12656250) * c ^ 2 * t ^ 16 + (303789 / 78125) * c ^ 2 * t ^ 18 + (-3035048 / 18984375) * c ^ 2 * t ^ 20 + (-5780923 / 21093750) * c ^ 2 * t ^ 22 + (13544399 / 189843750) * c ^ 2 * t ^ 24 + (25094188 / 284765625) * c ^ 2 * t ^ 26 + (341056 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((-2966432 / 75) * t ^ 2 + (3218304 / 25) * t ^ 4 + (-4792543096 / 28125) * t ^ 6 + (2103427263227 / 16875000) * t ^ 8 + (-322897894303 / 5625000) * t ^ 10 + (547067189921 / 33750000) * t ^ 12 + (-21651965093 / 6750000) * t ^ 14 + (944920429 / 937500) * t ^ 16 + (-53389687 / 843750) * t ^ 18 + (576174763 / 20250000) * t ^ 20 + (-2727548753 / 168750000) * t ^ 22 + (-13544399 / 63281250) * t ^ 24 + (-418801031 / 189843750) * t ^ 26 + (-341056 / 94921875) * t ^ 32) * c_sq
#print axioms v30_00
#print axioms v30_11
#print axioms v30_22
#print axioms v30_33
#print axioms v30_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
noncomputable def z31 : Fin 31 → ℂ := Fin.snoc z30 (r ^ 2 * thetaMinus)
theorem v31_00 (t : ℂ) : (momentPoly 31 z31 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00]
  try simp only [phase27_00]
  try simp only [star_one, star_neg]
  ring
theorem v31_01 (t : ℂ) : (momentPoly 31 z31 0 1).eval t = ((2 / 3) * alpha * t) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_01]
  try simp only [phase27_00, phase27_01]
  try simp only [star_one, star_neg]
  ring
theorem v31_02 (t : ℂ) : (momentPoly 31 z31 0 2).eval t = ((-1027 / 60) * t ^ 2 + (947 / 60) * t ^ 4 + (73 / 15) * alpha * t ^ 2 + (-73 / 15) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_01, v30_02]
  try simp only [phase27_00, phase27_01, phase27_02]
  try simp only [star_one, star_neg]
  linear_combination ((2 / 25) * t ^ 2) * alpha_sq + ((-2 / 225) * t ^ 2) * c_sq
theorem v31_03 (t : ℂ) : (momentPoly 31 z31 0 3).eval t = ((-136 / 5) * t ^ 3 + (131 / 5) * t ^ 5 + 1 * t ^ 9 + (-13567 / 600) * alpha * t ^ 3 + (20161 / 1200) * alpha * t ^ 5 + (17719 / 3600) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_01, v30_02, v30_03]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-16 / 1125) * c * t ^ 3 + (16 / 1125) * c * t ^ 5) * alpha_sq + ((-16 / 1125) * alpha * t ^ 3 + (-4 / 1125) * alpha * t ^ 5) * c_sq
theorem v31_04 (t : ℂ) : (momentPoly 31 z31 0 4).eval t = ((5911453 / 12000) * t ^ 4 + (-1789591 / 2000) * t ^ 6 + (11730103 / 24000) * t ^ 8 + (-1798997 / 18000) * t ^ 10 + (1090237 / 72000) * t ^ 16 + (-130329 / 250) * alpha * t ^ 4 + (377387 / 375) * alpha * t ^ 6 + (-355721 / 750) * alpha * t ^ 8 + (-17132 / 1125) * alpha * t ^ 10 + (5033 / 1125) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_01, v30_02, v30_03, v30_04]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04]
  try simp only [star_one, star_neg]
  linear_combination ((-49421 / 11250) * t ^ 4 + (77257 / 22500) * t ^ 6 + (4329 / 2500) * t ^ 10 + (-292 / 1125) * c * t ^ 4 + (584 / 1125) * c * t ^ 6 + (-292 / 1125) * c * t ^ 8 + (-64 / 16875) * c ^ 2 * t ^ 6 + (-8 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((1469 / 1875) * t ^ 4 + (-447 / 625) * t ^ 6 + (8 / 5625) * t ^ 8 + (-568 / 16875) * t ^ 10 + (-292 / 1125) * alpha * t ^ 4 + (292 / 1125) * alpha * t ^ 6) * c_sq
theorem v31_10 (t : ℂ) : (momentPoly 31 z31 1 0).eval t = ((-2 / 3) * alpha * t) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_10]
  try simp only [phase27_00, phase27_10]
  try simp only [star_one, star_neg]
  ring
theorem v31_11 (t : ℂ) : (momentPoly 31 z31 1 1).eval t = (31 + (-89 / 3) * t ^ 2) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_01, v30_10, v30_11]
  try simp only [phase27_00, phase27_01, phase27_10, phase27_11]
  try simp only [star_one, star_neg]
  linear_combination ((-2 / 25) * t ^ 2) * alpha_sq + ((-2 / 225) * t ^ 2) * c_sq
theorem v31_12 (t : ℂ) : (momentPoly 31 z31 1 2).eval t = ((146 / 15) * t ^ 3 + (-146 / 15) * t ^ 5 + (122 / 3) * alpha * t + (-2573 / 90) * alpha * t ^ 3 + (-1007 / 90) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_01, v30_02, v30_10, v30_11, v30_12]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_10, phase27_11, phase27_12]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 225) * t ^ 3 + (73 / 225) * t ^ 5 + (16 / 3375) * c * t ^ 3 + (-16 / 3375) * c * t ^ 5) * alpha_sq + ((-16 / 3375) * alpha * t ^ 3 + (-4 / 3375) * alpha * t ^ 5) * c_sq
theorem v31_13 (t : ℂ) : (momentPoly 31 z31 1 3).eval t = ((-3081 / 2) * t ^ 2 + (288021 / 100) * t ^ 4 + (-801329 / 600) * t ^ 6 + (-10691 / 1800) * t ^ 10 + 438 * alpha * t ^ 2 + (-12722 / 15) * alpha * t ^ 4 + (6089 / 15) * alpha * t ^ 6 + (21 / 5) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_01, v30_02, v30_03, v30_10, v30_11, v30_12, v30_13]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_10, phase27_11, phase27_12, phase27_13]
  try simp only [star_one, star_neg]
  linear_combination ((36 / 5) * t ^ 2 + (-57943 / 15000) * t ^ 4 + (-27293 / 10000) * t ^ 6 + (-4329 / 10000) * t ^ 10) * alpha_sq + ((-4 / 5) * t ^ 2 + (12851 / 11250) * t ^ 4 + (-4151 / 11250) * t ^ 6 + (-142 / 16875) * t ^ 10 + (-146 / 1125) * alpha * t ^ 4 + (146 / 1125) * alpha * t ^ 6) * c_sq
theorem v31_14 (t : ℂ) : (momentPoly 31 z31 1 4).eval t = ((-16048 / 5) * t ^ 3 + (1923863 / 375) * t ^ 5 + (-323726 / 375) * t ^ 7 + (-329996 / 375) * t ^ 9 + (-208564 / 1125) * t ^ 11 + (8941 / 1125) * t ^ 17 + (-800453 / 300) * alpha * t ^ 3 + (75761857 / 18000) * alpha * t ^ 5 + (-3650089 / 3000) * alpha * t ^ 7 + (2833409 / 12000) * alpha * t ^ 9 + (-14752933 / 27000) * alpha * t ^ 11 + (-1621807 / 108000) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_01, v30_02, v30_03, v30_04, v30_10, v30_11, v30_12, v30_13, v30_14]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04, phase27_10, phase27_11, phase27_12, phase27_13, phase27_14]
  try simp only [star_one, star_neg]
  linear_combination ((8614 / 75) * t ^ 3 + (-420653 / 2250) * t ^ 5 + (75949 / 1875) * t ^ 7 + (66881 / 2250) * t ^ 9 + (36632 / 16875) * t ^ 11 + (-5033 / 16875) * t ^ 17 + (-1888 / 1125) * c * t ^ 3 + (242344 / 84375) * c * t ^ 5 + (-63536 / 84375) * c * t ^ 7 + (-4216 / 9375) * c * t ^ 9 + (4544 / 253125) * c * t ^ 11 + (-2336 / 253125) * c * t ^ 17 + (-292 / 16875) * c ^ 2 * t ^ 7 + (292 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((1936 / 5625) * t ^ 5 + (-128 / 625) * t ^ 7 + (-584 / 5625) * t ^ 9 + (-8 / 225) * t ^ 11 + (-1888 / 1125) * alpha * t ^ 3 + (103951 / 84375) * alpha * t ^ 5 + (35029 / 56250) * alpha * t ^ 7 + (-8366 / 84375) * alpha * t ^ 9 + (-81523 / 506250) * alpha * t ^ 11 + (-584 / 253125) * alpha * t ^ 17) * c_sq
theorem v31_20 (t : ℂ) : (momentPoly 31 z31 2 0).eval t = ((-1027 / 60) * t ^ 2 + (947 / 60) * t ^ 4 + (-73 / 15) * alpha * t ^ 2 + (73 / 15) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_10, v30_20]
  try simp only [phase27_00, phase27_10, phase27_20]
  try simp only [star_one, star_neg]
  linear_combination ((2 / 25) * t ^ 2) * alpha_sq + ((-2 / 225) * t ^ 2) * c_sq
theorem v31_21 (t : ℂ) : (momentPoly 31 z31 2 1).eval t = ((146 / 15) * t ^ 3 + (-146 / 15) * t ^ 5 + (-122 / 3) * alpha * t + (2573 / 90) * alpha * t ^ 3 + (1007 / 90) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_01, v30_10, v30_11, v30_20, v30_21]
  try simp only [phase27_00, phase27_01, phase27_10, phase27_11, phase27_20, phase27_21]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 225) * t ^ 3 + (73 / 225) * t ^ 5 + (16 / 3375) * c * t ^ 3 + (-16 / 3375) * c * t ^ 5) * alpha_sq + ((16 / 3375) * alpha * t ^ 3 + (4 / 3375) * alpha * t ^ 5) * c_sq
theorem v31_22 (t : ℂ) : (momentPoly 31 z31 2 2).eval t = (1891 + (-3560) * t ^ 2 + (7003321 / 3600) * t ^ 4 + (-1014761 / 1800) * t ^ 6 + (1041001 / 3600) * t ^ 8) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_01, v30_02, v30_10, v30_11, v30_12, v30_20, v30_21, v30_22]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_10, phase27_11, phase27_12, phase27_20, phase27_21, phase27_22]
  try simp only [star_one, star_neg]
  linear_combination ((-48 / 5) * t ^ 2 + (893 / 135) * t ^ 4 + (8419 / 3375) * t ^ 6 + (292 / 3375) * c * t ^ 4 + (-584 / 3375) * c * t ^ 6 + (292 / 3375) * c * t ^ 8 + (64 / 50625) * c ^ 2 * t ^ 6 + (8 / 50625) * c ^ 2 * t ^ 8) * alpha_sq + ((-16 / 15) * t ^ 2 + (4259 / 3375) * t ^ 4 + (-4279 / 16875) * t ^ 6 + (-8 / 16875) * t ^ 8) * c_sq
theorem v31_23 (t : ℂ) : (momentPoly 31 z31 2 3).eval t = ((8614 / 5) * t ^ 3 + (-9726071 / 3000) * t ^ 5 + (1564391 / 1200) * t ^ 7 + (1184587 / 6000) * t ^ 9 + (1335787 / 18000) * t ^ 11 + (-1009387 / 18000) * t ^ 13 + (10982 / 3) * alpha * t + (-151807 / 30) * alpha * t ^ 3 + (-1925617 / 12000) * alpha * t ^ 5 + (16989479 / 14400) * alpha * t ^ 7 + (26369747 / 72000) * alpha * t ^ 9 + (-14415013 / 216000) * alpha * t ^ 11 + (17687093 / 216000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_01, v30_02, v30_03, v30_10, v30_11, v30_12, v30_13, v30_20, v30_21, v30_22, v30_23]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_10, phase27_11, phase27_12, phase27_13, phase27_20, phase27_21, phase27_22, phase27_23]
  try simp only [star_one, star_neg]
  linear_combination ((-4307 / 75) * t ^ 3 + (122309 / 1125) * t ^ 5 + (-57064 / 1125) * t ^ 7 + (-25733 / 16875) * t ^ 11 + (16133 / 16875) * t ^ 13 + (944 / 1125) * c * t ^ 3 + (-105059 / 67500) * c * t ^ 5 + (14321 / 25000) * c * t ^ 7 + (91123 / 675000) * c * t ^ 9 + (100723 / 2025000) * c * t ^ 11 + (-81523 / 2025000) * c * t ^ 13 + (292 / 16875) * c ^ 2 * t ^ 7 + (-292 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((-812 / 1875) * t ^ 5 + (634 / 1875) * t ^ 7 + (584 / 5625) * t ^ 9 + (-2 / 225) * t ^ 11 + (-944 / 1125) * alpha * t ^ 3 + (11153 / 22500) * alpha * t ^ 5 + (75409 / 225000) * alpha * t ^ 7 + (-64 / 84375) * alpha * t ^ 9 + (-63347 / 2025000) * alpha * t ^ 11 + (284 / 253125) * alpha * t ^ 13) * c_sq
theorem v31_24 (t : ℂ) : (momentPoly 31 z31 2 4).eval t = ((-2727712 / 15) * t ^ 2 + (50641377 / 100) * t ^ 4 + (-341679801623 / 720000) * t ^ 6 + (121385135909 / 720000) * t ^ 8 + (-9145306669 / 288000) * t ^ 10 + (62370712667 / 4320000) * t ^ 12 + (-1363925647 / 1080000) * t ^ 14 + (-786186487 / 4320000) * t ^ 18 + (682100327 / 4320000) * t ^ 20 + (775552 / 15) * alpha * t ^ 2 + (-2203181 / 15) * alpha * t ^ 4 + (8514095509 / 60000) * alpha * t ^ 6 + (-3343537807 / 60000) * alpha * t ^ 8 + (203688013 / 14400) * alpha * t ^ 10 + (-4723034183 / 1080000) * alpha * t ^ 12 + (-22890533 / 30000) * alpha * t ^ 14 + (-19040173 / 120000) * alpha * t ^ 18 + (161103317 / 1080000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_01, v30_02, v30_03, v30_04, v30_10, v30_11, v30_12, v30_13, v30_14, v30_20, v30_21, v30_22, v30_23, v30_24]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04, phase27_10, phase27_11, phase27_12, phase27_13, phase27_14, phase27_20, phase27_21, phase27_22, phase27_23, phase27_24]
  try simp only [star_one, star_neg]
  linear_combination ((21248 / 25) * t ^ 2 + (-1680347 / 1875) * t ^ 4 + (-600350909 / 1350000) * t ^ 6 + (174577327 / 450000) * t ^ 8 + (3867643 / 900000) * t ^ 10 + (283025053 / 4050000) * t ^ 12 + (109826509 / 4050000) * t ^ 14 + (14059289 / 8100000) * t ^ 18 + (-37627 / 9375) * c * t ^ 6 + (332947 / 28125) * c * t ^ 8 + (-994603 / 84375) * c * t ^ 10 + (70201 / 16875) * c * t ^ 12 + (-664 / 3375) * c * t ^ 14 + (-2 / 45) * c * t ^ 18 + (2 / 45) * c * t ^ 20 + (-40607 / 1265625) * c ^ 2 * t ^ 8 + (11227 / 843750) * c ^ 2 * t ^ 10 + (8302 / 1265625) * c ^ 2 * t ^ 12 + (90611 / 7593750) * c ^ 2 * t ^ 14 + (4672 / 3796875) * c ^ 2 * t ^ 18 + (1168 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-21248 / 225) * t ^ 2 + (1490716 / 5625) * t ^ 4 + (-355172369 / 1350000) * t ^ 6 + (360605381 / 3375000) * t ^ 8 + (-235058491 / 13500000) * t ^ 10 + (36152497 / 10125000) * t ^ 12 + (-680053 / 1265625) * t ^ 14 + (-5105969 / 40500000) * t ^ 18 + (-1168 / 1265625) * t ^ 20 + (-33872 / 1125) * alpha * t ^ 4 + (5205091 / 84375) * alpha * t ^ 6 + (-331942 / 9375) * alpha * t ^ 8 + (112723 / 28125) * alpha * t ^ 10 + (4184 / 253125) * alpha * t ^ 12 + (-40264 / 253125) * alpha * t ^ 14 + (-10066 / 253125) * alpha * t ^ 18) * c_sq
theorem v31_30 (t : ℂ) : (momentPoly 31 z31 3 0).eval t = ((-136 / 5) * t ^ 3 + (131 / 5) * t ^ 5 + 1 * t ^ 9 + (13567 / 600) * alpha * t ^ 3 + (-20161 / 1200) * alpha * t ^ 5 + (-17719 / 3600) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_10, v30_20, v30_30]
  try simp only [phase27_00, phase27_10, phase27_20, phase27_30]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 75) * t ^ 3 + (-73 / 75) * t ^ 5 + (-16 / 1125) * c * t ^ 3 + (16 / 1125) * c * t ^ 5) * alpha_sq + ((16 / 1125) * alpha * t ^ 3 + (4 / 1125) * alpha * t ^ 5) * c_sq
theorem v31_31 (t : ℂ) : (momentPoly 31 z31 3 1).eval t = ((-3081 / 2) * t ^ 2 + (288021 / 100) * t ^ 4 + (-801329 / 600) * t ^ 6 + (-10691 / 1800) * t ^ 10 + (-438) * alpha * t ^ 2 + (12722 / 15) * alpha * t ^ 4 + (-6089 / 15) * alpha * t ^ 6 + (-21 / 5) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_01, v30_10, v30_11, v30_20, v30_21, v30_30, v30_31]
  try simp only [phase27_00, phase27_01, phase27_10, phase27_11, phase27_20, phase27_21, phase27_30, phase27_31]
  try simp only [star_one, star_neg]
  linear_combination ((36 / 5) * t ^ 2 + (-57943 / 15000) * t ^ 4 + (-27293 / 10000) * t ^ 6 + (-4329 / 10000) * t ^ 10) * alpha_sq + ((-4 / 5) * t ^ 2 + (12851 / 11250) * t ^ 4 + (-4151 / 11250) * t ^ 6 + (-142 / 16875) * t ^ 10 + (146 / 1125) * alpha * t ^ 4 + (-146 / 1125) * alpha * t ^ 6) * c_sq
theorem v31_32 (t : ℂ) : (momentPoly 31 z31 3 2).eval t = ((8614 / 5) * t ^ 3 + (-9726071 / 3000) * t ^ 5 + (1564391 / 1200) * t ^ 7 + (1184587 / 6000) * t ^ 9 + (1335787 / 18000) * t ^ 11 + (-1009387 / 18000) * t ^ 13 + (-10982 / 3) * alpha * t + (151807 / 30) * alpha * t ^ 3 + (1925617 / 12000) * alpha * t ^ 5 + (-16989479 / 14400) * alpha * t ^ 7 + (-26369747 / 72000) * alpha * t ^ 9 + (14415013 / 216000) * alpha * t ^ 11 + (-17687093 / 216000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_01, v30_02, v30_10, v30_11, v30_12, v30_20, v30_21, v30_22, v30_30, v30_31, v30_32]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_10, phase27_11, phase27_12, phase27_20, phase27_21, phase27_22, phase27_30, phase27_31, phase27_32]
  try simp only [star_one, star_neg]
  linear_combination ((-4307 / 75) * t ^ 3 + (122309 / 1125) * t ^ 5 + (-57064 / 1125) * t ^ 7 + (-25733 / 16875) * t ^ 11 + (16133 / 16875) * t ^ 13 + (944 / 1125) * c * t ^ 3 + (-105059 / 67500) * c * t ^ 5 + (14321 / 25000) * c * t ^ 7 + (91123 / 675000) * c * t ^ 9 + (100723 / 2025000) * c * t ^ 11 + (-81523 / 2025000) * c * t ^ 13 + (292 / 16875) * c ^ 2 * t ^ 7 + (-292 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((-812 / 1875) * t ^ 5 + (634 / 1875) * t ^ 7 + (584 / 5625) * t ^ 9 + (-2 / 225) * t ^ 11 + (944 / 1125) * alpha * t ^ 3 + (-11153 / 22500) * alpha * t ^ 5 + (-75409 / 225000) * alpha * t ^ 7 + (64 / 84375) * alpha * t ^ 9 + (63347 / 2025000) * alpha * t ^ 11 + (-284 / 253125) * alpha * t ^ 13) * c_sq
theorem v31_33 (t : ℂ) : (momentPoly 31 z31 3 3).eval t = (170221 + (-472768) * t ^ 2 + (203096309 / 400) * t ^ 4 + (-13899763137 / 40000) * t ^ 6 + (25382983213 / 120000) * t ^ 8 + (-33228251279 / 480000) * t ^ 10 + (348878927 / 360000) * t ^ 12 + (-726080441 / 720000) * t ^ 14 + (184362961 / 4320000) * t ^ 18) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_01, v30_02, v30_03, v30_10, v30_11, v30_12, v30_13, v30_20, v30_21, v30_22, v30_23, v30_30, v30_31, v30_32, v30_33]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_10, phase27_11, phase27_12, phase27_13, phase27_20, phase27_21, phase27_22, phase27_23, phase27_30, phase27_31, phase27_32, phase27_33]
  try simp only [star_one, star_neg]
  linear_combination ((-31872 / 25) * t ^ 2 + (25897 / 15) * t ^ 4 + (8461547 / 150000) * t ^ 6 + (-118301933 / 300000) * t ^ 8 + (-98812327 / 900000) * t ^ 10 + (14752119 / 500000) * t ^ 12 + (-156193271 / 4500000) * t ^ 14 + (-2088671 / 1125000) * t ^ 18 + (8468 / 375) * c * t ^ 4 + (-1859012 / 28125) * c * t ^ 6 + (1798924 / 28125) * c * t ^ 8 + (-575012 / 28125) * c * t ^ 10 + (184 / 375) * c * t ^ 12 + (-184 / 375) * c * t ^ 14 + (5632 / 16875) * c ^ 2 * t ^ 6 + (-13553 / 56250) * c ^ 2 * t ^ 8 + (-6347 / 67500) * c ^ 2 * t ^ 10 + (4829 / 337500) * c ^ 2 * t ^ 14) * alpha_sq + ((-10624 / 75) * t ^ 2 + (123511 / 375) * t ^ 4 + (-11945857 / 45000) * t ^ 6 + (10728413 / 112500) * t ^ 8 + (-4103201 / 225000) * t ^ 10 + (461176 / 421875) * t ^ 12 + (-661877 / 843750) * t ^ 14 + (-10082 / 1265625) * t ^ 18) * c_sq
theorem v31_34 (t : ℂ) : (momentPoly 31 z31 3 4).eval t = ((1499712 / 5) * t ^ 3 + (-409831447 / 500) * t ^ 5 + (33802601653 / 50000) * t ^ 7 + (-1381225797 / 12500) * t ^ 9 + (-964885643 / 75000) * t ^ 11 + (-19418357431 / 360000) * t ^ 13 + (12404419591 / 450000) * t ^ 15 + (-11621163073 / 1800000) * t ^ 17 + (-700969897 / 675000) * t ^ 19 + (491787529 / 600000) * t ^ 21 + (438486683 / 5400000) * t ^ 25 + (1296602 / 3) * alpha * t + (-4404976 / 5) * alpha * t ^ 3 + (1664780893 / 6000) * alpha * t ^ 5 + (1778705137691 / 7200000) * alpha * t ^ 7 + (198118414663 / 14400000) * alpha * t ^ 9 + (-1376838984293 / 14400000) * alpha * t ^ 11 + (112022936741 / 3456000) * alpha * t ^ 13 + (-63518802047 / 2700000) * alpha * t ^ 15 + (-243024434257 / 86400000) * alpha * t ^ 17 + (63512382103 / 129600000) * alpha * t ^ 19 + (-30177418477 / 86400000) * alpha * t ^ 21 + (-18331106203 / 259200000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_01, v30_02, v30_03, v30_04, v30_10, v30_11, v30_12, v30_13, v30_14, v30_20, v30_21, v30_22, v30_23, v30_24, v30_30, v30_31, v30_32, v30_33, v30_34]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04, phase27_10, phase27_11, phase27_12, phase27_13, phase27_14, phase27_20, phase27_21, phase27_22, phase27_23, phase27_24, phase27_30, phase27_31, phase27_32, phase27_33, phase27_34]
  try simp only [star_one, star_neg]
  linear_combination ((-249952 / 25) * t ^ 3 + (10329361 / 375) * t ^ 5 + (-115220243659 / 4500000) * t ^ 7 + (191225609 / 20000) * t ^ 9 + (-999588433 / 360000) * t ^ 11 + (13733971249 / 9000000) * t ^ 13 + (-2296656491 / 6750000) * t ^ 15 + (14780701 / 168750) * t ^ 17 + (2316622459 / 81000000) * t ^ 19 + (-252829411 / 9000000) * t ^ 21 + (-1112293 / 1265625) * t ^ 25 + (54784 / 375) * c * t ^ 3 + (-4404203 / 11250) * c * t ^ 5 + (1019187847 / 3375000) * c * t ^ 7 + (-33182507 / 1350000) * c * t ^ 9 + (-1042571 / 125000) * c * t ^ 11 + (-333915263 / 8437500) * c * t ^ 13 + (974435197 / 50625000) * c * t ^ 15 + (-128535563 / 33750000) * c * t ^ 17 + (60453623 / 151875000) * c * t ^ 19 + (7517033 / 50625000) * c * t ^ 21 + (-5951179 / 75937500) * c * t ^ 25 + (101032 / 16875) * c ^ 2 * t ^ 7 + (-5190491 / 421875) * c ^ 2 * t ^ 9 + (2973862 / 421875) * c ^ 2 * t ^ 11 + (-21767 / 28125) * c ^ 2 * t ^ 13 + (7268 / 421875) * c ^ 2 * t ^ 15 + (20132 / 1265625) * c ^ 2 * t ^ 17 + (21316 / 1265625) * c ^ 2 * t ^ 19 + (-2 / 225) * c ^ 2 * t ^ 21) * alpha_sq + ((-92568 / 625) * t ^ 5 + (23699131 / 93750) * t ^ 7 + (-31268981 / 562500) * t ^ 9 + (-10360607 / 187500) * t ^ 11 + (-640271 / 562500) * t ^ 13 + (12957157 / 1687500) * t ^ 15 + (-40864 / 421875) * t ^ 17 + (-3118 / 9375) * t ^ 19 + (4 / 75) * t ^ 21 + (-54784 / 375) * alpha * t ^ 3 + (2303203 / 11250) * alpha * t ^ 5 + (41118773 / 3375000) * alpha * t ^ 7 + (-455571701 / 6750000) * alpha * t ^ 9 + (-59809553 / 6750000) * alpha * t ^ 11 + (506864083 / 50625000) * alpha * t ^ 13 + (-500722969 / 101250000) * alpha * t ^ 15 + (-1260407 / 12656250) * alpha * t ^ 17 + (60045577 / 151875000) * alpha * t ^ 19 + (-4740271 / 101250000) * alpha * t ^ 21 + (-41464 / 18984375) * alpha * t ^ 25) * c_sq
theorem v31_40 (t : ℂ) : (momentPoly 31 z31 4 0).eval t = ((5911453 / 12000) * t ^ 4 + (-1789591 / 2000) * t ^ 6 + (11730103 / 24000) * t ^ 8 + (-1798997 / 18000) * t ^ 10 + (1090237 / 72000) * t ^ 16 + (130329 / 250) * alpha * t ^ 4 + (-377387 / 375) * alpha * t ^ 6 + (355721 / 750) * alpha * t ^ 8 + (17132 / 1125) * alpha * t ^ 10 + (-5033 / 1125) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_10, v30_20, v30_30, v30_40]
  try simp only [phase27_00, phase27_10, phase27_20, phase27_30, phase27_40]
  try simp only [star_one, star_neg]
  linear_combination ((-49421 / 11250) * t ^ 4 + (77257 / 22500) * t ^ 6 + (4329 / 2500) * t ^ 10 + (-292 / 1125) * c * t ^ 4 + (584 / 1125) * c * t ^ 6 + (-292 / 1125) * c * t ^ 8 + (-64 / 16875) * c ^ 2 * t ^ 6 + (-8 / 16875) * c ^ 2 * t ^ 8) * alpha_sq + ((1469 / 1875) * t ^ 4 + (-447 / 625) * t ^ 6 + (8 / 5625) * t ^ 8 + (-568 / 16875) * t ^ 10 + (292 / 1125) * alpha * t ^ 4 + (-292 / 1125) * alpha * t ^ 6) * c_sq
theorem v31_41 (t : ℂ) : (momentPoly 31 z31 4 1).eval t = ((-16048 / 5) * t ^ 3 + (1923863 / 375) * t ^ 5 + (-323726 / 375) * t ^ 7 + (-329996 / 375) * t ^ 9 + (-208564 / 1125) * t ^ 11 + (8941 / 1125) * t ^ 17 + (800453 / 300) * alpha * t ^ 3 + (-75761857 / 18000) * alpha * t ^ 5 + (3650089 / 3000) * alpha * t ^ 7 + (-2833409 / 12000) * alpha * t ^ 9 + (14752933 / 27000) * alpha * t ^ 11 + (1621807 / 108000) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_01, v30_10, v30_11, v30_20, v30_21, v30_30, v30_31, v30_40, v30_41]
  try simp only [phase27_00, phase27_01, phase27_10, phase27_11, phase27_20, phase27_21, phase27_30, phase27_31, phase27_40, phase27_41]
  try simp only [star_one, star_neg]
  linear_combination ((8614 / 75) * t ^ 3 + (-420653 / 2250) * t ^ 5 + (75949 / 1875) * t ^ 7 + (66881 / 2250) * t ^ 9 + (36632 / 16875) * t ^ 11 + (-5033 / 16875) * t ^ 17 + (-1888 / 1125) * c * t ^ 3 + (242344 / 84375) * c * t ^ 5 + (-63536 / 84375) * c * t ^ 7 + (-4216 / 9375) * c * t ^ 9 + (4544 / 253125) * c * t ^ 11 + (-2336 / 253125) * c * t ^ 17 + (-292 / 16875) * c ^ 2 * t ^ 7 + (292 / 16875) * c ^ 2 * t ^ 9) * alpha_sq + ((1936 / 5625) * t ^ 5 + (-128 / 625) * t ^ 7 + (-584 / 5625) * t ^ 9 + (-8 / 225) * t ^ 11 + (1888 / 1125) * alpha * t ^ 3 + (-103951 / 84375) * alpha * t ^ 5 + (-35029 / 56250) * alpha * t ^ 7 + (8366 / 84375) * alpha * t ^ 9 + (81523 / 506250) * alpha * t ^ 11 + (584 / 253125) * alpha * t ^ 17) * c_sq
theorem v31_42 (t : ℂ) : (momentPoly 31 z31 4 2).eval t = ((-2727712 / 15) * t ^ 2 + (50641377 / 100) * t ^ 4 + (-341679801623 / 720000) * t ^ 6 + (121385135909 / 720000) * t ^ 8 + (-9145306669 / 288000) * t ^ 10 + (62370712667 / 4320000) * t ^ 12 + (-1363925647 / 1080000) * t ^ 14 + (-786186487 / 4320000) * t ^ 18 + (682100327 / 4320000) * t ^ 20 + (-775552 / 15) * alpha * t ^ 2 + (2203181 / 15) * alpha * t ^ 4 + (-8514095509 / 60000) * alpha * t ^ 6 + (3343537807 / 60000) * alpha * t ^ 8 + (-203688013 / 14400) * alpha * t ^ 10 + (4723034183 / 1080000) * alpha * t ^ 12 + (22890533 / 30000) * alpha * t ^ 14 + (19040173 / 120000) * alpha * t ^ 18 + (-161103317 / 1080000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_01, v30_02, v30_10, v30_11, v30_12, v30_20, v30_21, v30_22, v30_30, v30_31, v30_32, v30_40, v30_41, v30_42]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_10, phase27_11, phase27_12, phase27_20, phase27_21, phase27_22, phase27_30, phase27_31, phase27_32, phase27_40, phase27_41, phase27_42]
  try simp only [star_one, star_neg]
  linear_combination ((21248 / 25) * t ^ 2 + (-1680347 / 1875) * t ^ 4 + (-600350909 / 1350000) * t ^ 6 + (174577327 / 450000) * t ^ 8 + (3867643 / 900000) * t ^ 10 + (283025053 / 4050000) * t ^ 12 + (109826509 / 4050000) * t ^ 14 + (14059289 / 8100000) * t ^ 18 + (-37627 / 9375) * c * t ^ 6 + (332947 / 28125) * c * t ^ 8 + (-994603 / 84375) * c * t ^ 10 + (70201 / 16875) * c * t ^ 12 + (-664 / 3375) * c * t ^ 14 + (-2 / 45) * c * t ^ 18 + (2 / 45) * c * t ^ 20 + (-40607 / 1265625) * c ^ 2 * t ^ 8 + (11227 / 843750) * c ^ 2 * t ^ 10 + (8302 / 1265625) * c ^ 2 * t ^ 12 + (90611 / 7593750) * c ^ 2 * t ^ 14 + (4672 / 3796875) * c ^ 2 * t ^ 18 + (1168 / 3796875) * c ^ 2 * t ^ 20) * alpha_sq + ((-21248 / 225) * t ^ 2 + (1490716 / 5625) * t ^ 4 + (-355172369 / 1350000) * t ^ 6 + (360605381 / 3375000) * t ^ 8 + (-235058491 / 13500000) * t ^ 10 + (36152497 / 10125000) * t ^ 12 + (-680053 / 1265625) * t ^ 14 + (-5105969 / 40500000) * t ^ 18 + (-1168 / 1265625) * t ^ 20 + (33872 / 1125) * alpha * t ^ 4 + (-5205091 / 84375) * alpha * t ^ 6 + (331942 / 9375) * alpha * t ^ 8 + (-112723 / 28125) * alpha * t ^ 10 + (-4184 / 253125) * alpha * t ^ 12 + (40264 / 253125) * alpha * t ^ 14 + (10066 / 253125) * alpha * t ^ 18) * c_sq
theorem v31_43 (t : ℂ) : (momentPoly 31 z31 4 3).eval t = ((1499712 / 5) * t ^ 3 + (-409831447 / 500) * t ^ 5 + (33802601653 / 50000) * t ^ 7 + (-1381225797 / 12500) * t ^ 9 + (-964885643 / 75000) * t ^ 11 + (-19418357431 / 360000) * t ^ 13 + (12404419591 / 450000) * t ^ 15 + (-11621163073 / 1800000) * t ^ 17 + (-700969897 / 675000) * t ^ 19 + (491787529 / 600000) * t ^ 21 + (438486683 / 5400000) * t ^ 25 + (-1296602 / 3) * alpha * t + (4404976 / 5) * alpha * t ^ 3 + (-1664780893 / 6000) * alpha * t ^ 5 + (-1778705137691 / 7200000) * alpha * t ^ 7 + (-198118414663 / 14400000) * alpha * t ^ 9 + (1376838984293 / 14400000) * alpha * t ^ 11 + (-112022936741 / 3456000) * alpha * t ^ 13 + (63518802047 / 2700000) * alpha * t ^ 15 + (243024434257 / 86400000) * alpha * t ^ 17 + (-63512382103 / 129600000) * alpha * t ^ 19 + (30177418477 / 86400000) * alpha * t ^ 21 + (18331106203 / 259200000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_01, v30_02, v30_03, v30_10, v30_11, v30_12, v30_13, v30_20, v30_21, v30_22, v30_23, v30_30, v30_31, v30_32, v30_33, v30_40, v30_41, v30_42, v30_43]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_10, phase27_11, phase27_12, phase27_13, phase27_20, phase27_21, phase27_22, phase27_23, phase27_30, phase27_31, phase27_32, phase27_33, phase27_40, phase27_41, phase27_42, phase27_43]
  try simp only [star_one, star_neg]
  linear_combination ((-249952 / 25) * t ^ 3 + (10329361 / 375) * t ^ 5 + (-115220243659 / 4500000) * t ^ 7 + (191225609 / 20000) * t ^ 9 + (-999588433 / 360000) * t ^ 11 + (13733971249 / 9000000) * t ^ 13 + (-2296656491 / 6750000) * t ^ 15 + (14780701 / 168750) * t ^ 17 + (2316622459 / 81000000) * t ^ 19 + (-252829411 / 9000000) * t ^ 21 + (-1112293 / 1265625) * t ^ 25 + (54784 / 375) * c * t ^ 3 + (-4404203 / 11250) * c * t ^ 5 + (1019187847 / 3375000) * c * t ^ 7 + (-33182507 / 1350000) * c * t ^ 9 + (-1042571 / 125000) * c * t ^ 11 + (-333915263 / 8437500) * c * t ^ 13 + (974435197 / 50625000) * c * t ^ 15 + (-128535563 / 33750000) * c * t ^ 17 + (60453623 / 151875000) * c * t ^ 19 + (7517033 / 50625000) * c * t ^ 21 + (-5951179 / 75937500) * c * t ^ 25 + (101032 / 16875) * c ^ 2 * t ^ 7 + (-5190491 / 421875) * c ^ 2 * t ^ 9 + (2973862 / 421875) * c ^ 2 * t ^ 11 + (-21767 / 28125) * c ^ 2 * t ^ 13 + (7268 / 421875) * c ^ 2 * t ^ 15 + (20132 / 1265625) * c ^ 2 * t ^ 17 + (21316 / 1265625) * c ^ 2 * t ^ 19 + (-2 / 225) * c ^ 2 * t ^ 21) * alpha_sq + ((-92568 / 625) * t ^ 5 + (23699131 / 93750) * t ^ 7 + (-31268981 / 562500) * t ^ 9 + (-10360607 / 187500) * t ^ 11 + (-640271 / 562500) * t ^ 13 + (12957157 / 1687500) * t ^ 15 + (-40864 / 421875) * t ^ 17 + (-3118 / 9375) * t ^ 19 + (4 / 75) * t ^ 21 + (54784 / 375) * alpha * t ^ 3 + (-2303203 / 11250) * alpha * t ^ 5 + (-41118773 / 3375000) * alpha * t ^ 7 + (455571701 / 6750000) * alpha * t ^ 9 + (59809553 / 6750000) * alpha * t ^ 11 + (-506864083 / 50625000) * alpha * t ^ 13 + (500722969 / 101250000) * alpha * t ^ 15 + (1260407 / 12656250) * alpha * t ^ 17 + (-60045577 / 151875000) * alpha * t ^ 19 + (4740271 / 101250000) * alpha * t ^ 21 + (41464 / 18984375) * alpha * t ^ 25) * c_sq
theorem v31_44 (t : ℂ) : (momentPoly 31 z31 4 4).eval t = (20097331 + (-219575816 / 3) * t ^ 2 + (34757482123 / 300) * t ^ 4 + (-925128331583 / 7500) * t ^ 6 + (15180976048605001 / 144000000) * t ^ 8 + (-2146467665382961 / 36000000) * t ^ 10 + (159015796590961 / 9600000) * t ^ 12 + (-22527356568753 / 8000000) * t ^ 14 + (610668374242097 / 576000000) * t ^ 16 + (-89557614537 / 8000000) * t ^ 18 + (-16111309461089 / 1296000000) * t ^ 20 + (527870594837 / 72000000) * t ^ 22 + (-1209362839781 / 864000000) * t ^ 24 + (-2293660939121 / 648000000) * t ^ 26 + (1339181137801 / 5184000000) * t ^ 32) := by
  rw [momentPoly]
  simp only [z31, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v30_00, v30_01, v30_02, v30_03, v30_04, v30_10, v30_11, v30_12, v30_13, v30_14, v30_20, v30_21, v30_22, v30_23, v30_24, v30_30, v30_31, v30_32, v30_33, v30_34, v30_40, v30_41, v30_42, v30_43, v30_44]
  try simp only [phase27_00, phase27_01, phase27_02, phase27_03, phase27_04, phase27_10, phase27_11, phase27_12, phase27_13, phase27_14, phase27_20, phase27_21, phase27_22, phase27_23, phase27_24, phase27_30, phase27_31, phase27_32, phase27_33, phase27_34, phase27_40, phase27_41, phase27_42, phase27_43, phase27_44]
  try simp only [star_one, star_neg]
  linear_combination ((-4934288 / 25) * t ^ 2 + (17727836 / 45) * t ^ 4 + (-3312249202 / 28125) * t ^ 6 + (-857926147121 / 7500000) * t ^ 8 + (117371102569 / 135000000) * t ^ 10 + (1132216492351 / 27000000) * t ^ 12 + (-17148367770349 / 810000000) * t ^ 14 + (41830930619 / 3375000) * t ^ 16 + (600510559093 / 810000000) * t ^ 18 + (723044147927 / 1215000000) * t ^ 20 + (113682135317 / 810000000) * t ^ 22 + (131633796359 / 2430000000) * t ^ 26 + (5796784 / 1125) * c * t ^ 4 + (-184590992 / 9375) * c * t ^ 6 + (238475266811 / 8437500) * c * t ^ 8 + (-39684790763 / 2109375) * c * t ^ 10 + (21766835519 / 3375000) * c * t ^ 12 + (-16598658397 / 8437500) * c * t ^ 14 + (29949959999 / 50625000) * c * t ^ 16 + (58261027 / 4218750) * c * t ^ 18 + (-28750619 / 151875000) * c * t ^ 20 + (-17407933 / 8437500) * c * t ^ 22 + (22681847 / 50625000) * c * t ^ 24 + (22112576 / 18984375) * c * t ^ 26 + (-2939272 / 18984375) * c * t ^ 32 + (86656 / 1125) * c ^ 2 * t ^ 6 + (-5999384 / 50625) * c ^ 2 * t ^ 8 + (77332937 / 6328125) * c ^ 2 * t ^ 10 + (11157409 / 421875) * c ^ 2 * t ^ 12 + (96200923 / 12656250) * c ^ 2 * t ^ 14 + (-56657959 / 8437500) * c ^ 2 * t ^ 16 + (83416811 / 37968750) * c ^ 2 * t ^ 18 + (-11857244 / 94921875) * c ^ 2 * t ^ 20 + (-13384409 / 94921875) * c ^ 2 * t ^ 22 + (14586511 / 379687500) * c ^ 2 * t ^ 24 + (13229206 / 284765625) * c ^ 2 * t ^ 26 + (170528 / 284765625) * c ^ 2 * t ^ 32) * alpha_sq + ((-4934288 / 225) * t ^ 2 + (84549668 / 1125) * t ^ 4 + (-587179186 / 5625) * t ^ 6 + (2653266115379 / 33750000) * t ^ 8 + (-1215679588889 / 33750000) * t ^ 10 + (134311659397 / 13500000) * t ^ 12 + (-131945914709 / 67500000) * t ^ 14 + (1128610669 / 1875000) * t ^ 16 + (-107792753 / 2812500) * t ^ 18 + (59043880529 / 3037500000) * t ^ 20 + (-3571065389 / 337500000) * t ^ 22 + (-14586511 / 126562500) * t ^ 24 + (-447127879 / 379687500) * t ^ 26 + (-170528 / 94921875) * t ^ 32) * c_sq
#print axioms v31_00
#print axioms v31_11
#print axioms v31_22
#print axioms v31_33
#print axioms v31_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
theorem site32 : ((r ^ 2 * phiPlus) : ℂ) = ((1 / 16) + (-1 / 48) * d + (1 / 48) * alpha + (1 / 48) * alpha * d) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 48) + (1 / 96) * d + (-1 / 96) * alpha) * alpha_sq
theorem phase32_00 : ((r ^ 2 * phiPlus) : ℂ) ^ 0 * star ((r ^ 2 * phiPlus) : ℂ) ^ 0 = (1) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase32_01 : ((r ^ 2 * phiPlus) : ℂ) ^ 0 * star ((r ^ 2 * phiPlus) : ℂ) ^ 1 = ((1 / 16) + (-1 / 48) * d + (-1 / 48) * alpha + (-1 / 48) * alpha * d) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase32_02 : ((r ^ 2 * phiPlus) : ℂ) ^ 0 * star ((r ^ 2 * phiPlus) : ℂ) ^ 2 = ((-95 / 192) + (-1 / 192) * d + (95 / 192) * alpha + (-1 / 576) * alpha * d) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 2304) + (1 / 1152) * d + (1 / 2304) * d ^ 2) * alpha_sq + ((-1 / 1152) + (1 / 1152) * alpha) * d_sq
theorem phase32_03 : ((r ^ 2 * phiPlus) : ℂ) ^ 0 * star ((r ^ 2 * phiPlus) : ℂ) ^ 3 = ((47 / 1152) * d + (143 / 1152) * alpha) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 12288) + (5 / 36864) * d + (1 / 36864) * d ^ 2 + (-1 / 36864) * d ^ 3 + (-1 / 110592) * alpha + (-1 / 36864) * alpha * d + (-1 / 36864) * alpha * d ^ 2 + (-1 / 110592) * alpha * d ^ 3) * alpha_sq + ((1 / 13824) * d + (1 / 4608) * alpha) * d_sq
theorem phase32_04 : ((r ^ 2 * phiPlus) : ℂ) ^ 0 * star ((r ^ 2 * phiPlus) : ℂ) ^ 4 = ((-4417 / 9216) + (95 / 9216) * d + (-4417 / 9216) * alpha + (-95 / 27648) * alpha * d) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((17 / 1769472) + (5 / 442368) * d + (-5 / 884736) * d ^ 2 + (-1 / 147456) * d ^ 3 + (1 / 1769472) * d ^ 4 + (-1 / 442368) * alpha + (-1 / 165888) * alpha * d + (-1 / 221184) * alpha * d ^ 2 + (1 / 1327104) * alpha * d ^ 4 + (1 / 5308416) * alpha ^ 2 + (1 / 1327104) * alpha ^ 2 * d + (1 / 884736) * alpha ^ 2 * d ^ 2 + (1 / 1327104) * alpha ^ 2 * d ^ 3 + (1 / 5308416) * alpha ^ 2 * d ^ 4) * alpha_sq + ((-185 / 221184) + (1 / 55296) * d + (-1 / 663552) * d ^ 2 + (-185 / 221184) * alpha + (-1 / 165888) * alpha * d + (-1 / 663552) * alpha * d ^ 2) * d_sq
theorem phase32_10 : ((r ^ 2 * phiPlus) : ℂ) ^ 1 * star ((r ^ 2 * phiPlus) : ℂ) ^ 0 = ((1 / 16) + (-1 / 48) * d + (1 / 48) * alpha + (1 / 48) * alpha * d) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase32_11 : ((r ^ 2 * phiPlus) : ℂ) ^ 1 * star ((r ^ 2 * phiPlus) : ℂ) ^ 1 = (1) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 2304) + (-1 / 1152) * d + (-1 / 2304) * d ^ 2) * alpha_sq + ((1 / 576)) * d_sq
theorem phase32_12 : ((r ^ 2 * phiPlus) : ℂ) ^ 1 * star ((r ^ 2 * phiPlus) : ℂ) ^ 2 = ((1 / 16) + (-1 / 48) * d + (-1 / 48) * alpha + (-1 / 48) * alpha * d) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 36864) + (-5 / 110592) * d + (-1 / 110592) * d ^ 2 + (1 / 110592) * d ^ 3 + (1 / 110592) * alpha + (1 / 36864) * alpha * d + (1 / 36864) * alpha * d ^ 2 + (1 / 110592) * alpha * d ^ 3) * alpha_sq + ((1 / 9216) + (-1 / 27648) * d + (-1 / 27648) * alpha + (-1 / 27648) * alpha * d) * d_sq
theorem phase32_13 : ((r ^ 2 * phiPlus) : ℂ) ^ 1 * star ((r ^ 2 * phiPlus) : ℂ) ^ 3 = ((-95 / 192) + (-1 / 192) * d + (95 / 192) * alpha + (-1 / 576) * alpha * d) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 1769472) + (1 / 442368) * d + (1 / 294912) * d ^ 2 + (1 / 442368) * d ^ 3 + (1 / 1769472) * d ^ 4 + (1 / 884736) * alpha + (1 / 331776) * alpha * d + (1 / 442368) * alpha * d ^ 2 + (-1 / 2654208) * alpha * d ^ 4 + (-1 / 5308416) * alpha ^ 2 + (-1 / 1327104) * alpha ^ 2 * d + (-1 / 884736) * alpha ^ 2 * d ^ 2 + (-1 / 1327104) * alpha ^ 2 * d ^ 3 + (-1 / 5308416) * alpha ^ 2 * d ^ 4) * alpha_sq + ((-191 / 221184) + (-1 / 110592) * d + (-1 / 663552) * d ^ 2 + (191 / 221184) * alpha + (-1 / 331776) * alpha * d + (1 / 663552) * alpha * d ^ 2) * d_sq
theorem phase32_14 : ((r ^ 2 * phiPlus) : ℂ) ^ 1 * star ((r ^ 2 * phiPlus) : ℂ) ^ 4 = ((47 / 1152) * d + (143 / 1152) * alpha) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 3145728) + (17 / 28311552) * d + (5 / 14155776) * d ^ 2 + (17 / 127401984) * d ^ 3 + (5 / 254803968) * d ^ 4 + (-11 / 254803968) * d ^ 5 + (5 / 84934656) * alpha + (1 / 9437184) * alpha * d + (-5 / 127401984) * alpha * d ^ 2 + (-7 / 42467328) * alpha * d ^ 3 + (-7 / 84934656) * alpha * d ^ 4 + (-1 / 254803968) * alpha * d ^ 5 + (-1 / 28311552) * alpha ^ 2 + (-11 / 84934656) * alpha ^ 2 * d + (-7 / 42467328) * alpha ^ 2 * d ^ 2 + (-1 / 14155776) * alpha ^ 2 * d ^ 3 + (1 / 84934656) * alpha ^ 2 * d ^ 4 + (1 / 84934656) * alpha ^ 2 * d ^ 5 + (1 / 254803968) * alpha ^ 3 + (5 / 254803968) * alpha ^ 3 * d + (5 / 127401984) * alpha ^ 3 * d ^ 2 + (5 / 127401984) * alpha ^ 3 * d ^ 3 + (5 / 254803968) * alpha ^ 3 * d ^ 4 + (1 / 254803968) * alpha ^ 3 * d ^ 5) * alpha_sq + ((7 / 98304) * d + (1 / 7962624) * d ^ 3 + (575 / 2654208) * alpha + (1 / 2654208) * alpha * d ^ 2) * d_sq
theorem phase32_20 : ((r ^ 2 * phiPlus) : ℂ) ^ 2 * star ((r ^ 2 * phiPlus) : ℂ) ^ 0 = ((-95 / 192) + (-1 / 192) * d + (-95 / 192) * alpha + (1 / 576) * alpha * d) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 2304) + (1 / 1152) * d + (1 / 2304) * d ^ 2) * alpha_sq + ((-1 / 1152) + (-1 / 1152) * alpha) * d_sq
theorem phase32_21 : ((r ^ 2 * phiPlus) : ℂ) ^ 2 * star ((r ^ 2 * phiPlus) : ℂ) ^ 1 = ((1 / 16) + (-1 / 48) * d + (1 / 48) * alpha + (1 / 48) * alpha * d) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 36864) + (-5 / 110592) * d + (-1 / 110592) * d ^ 2 + (1 / 110592) * d ^ 3 + (-1 / 110592) * alpha + (-1 / 36864) * alpha * d + (-1 / 36864) * alpha * d ^ 2 + (-1 / 110592) * alpha * d ^ 3) * alpha_sq + ((1 / 9216) + (-1 / 27648) * d + (1 / 27648) * alpha + (1 / 27648) * alpha * d) * d_sq
theorem phase32_22 : ((r ^ 2 * phiPlus) : ℂ) ^ 2 * star ((r ^ 2 * phiPlus) : ℂ) ^ 2 = (1) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-7 / 1769472) + (-1 / 147456) * d + (-7 / 2654208) * d ^ 2 + (-1 / 1327104) * d ^ 3 + (-5 / 5308416) * d ^ 4 + (1 / 5308416) * alpha ^ 2 + (1 / 1327104) * alpha ^ 2 * d + (1 / 884736) * alpha ^ 2 * d ^ 2 + (1 / 1327104) * alpha ^ 2 * d ^ 3 + (1 / 5308416) * alpha ^ 2 * d ^ 4) * alpha_sq + ((193 / 110592) + (1 / 331776) * d ^ 2) * d_sq
theorem phase32_23 : ((r ^ 2 * phiPlus) : ℂ) ^ 2 * star ((r ^ 2 * phiPlus) : ℂ) ^ 3 = ((1 / 16) + (-1 / 48) * d + (-1 / 48) * alpha + (-1 / 48) * alpha * d) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-7 / 28311552) + (-29 / 84934656) * d + (-1 / 42467328) * d ^ 2 + (1 / 127401984) * d ^ 3 + (-11 / 254803968) * d ^ 4 + (5 / 254803968) * d ^ 5 + (7 / 84934656) * alpha + (19 / 84934656) * alpha * d + (25 / 127401984) * alpha * d ^ 2 + (1 / 14155776) * alpha * d ^ 3 + (1 / 28311552) * alpha * d ^ 4 + (5 / 254803968) * alpha * d ^ 5 + (1 / 84934656) * alpha ^ 2 + (11 / 254803968) * alpha ^ 2 * d + (7 / 127401984) * alpha ^ 2 * d ^ 2 + (1 / 42467328) * alpha ^ 2 * d ^ 3 + (-1 / 254803968) * alpha ^ 2 * d ^ 4 + (-1 / 254803968) * alpha ^ 2 * d ^ 5 + (-1 / 254803968) * alpha ^ 3 + (-5 / 254803968) * alpha ^ 3 * d + (-5 / 127401984) * alpha ^ 3 * d ^ 2 + (-5 / 127401984) * alpha ^ 3 * d ^ 3 + (-5 / 254803968) * alpha ^ 3 * d ^ 4 + (-1 / 254803968) * alpha ^ 3 * d ^ 5) * alpha_sq + ((193 / 1769472) + (-193 / 5308416) * d + (1 / 5308416) * d ^ 2 + (-1 / 15925248) * d ^ 3 + (-193 / 5308416) * alpha + (-193 / 5308416) * alpha * d + (-1 / 15925248) * alpha * d ^ 2 + (-1 / 15925248) * alpha * d ^ 3) * d_sq
theorem phase32_24 : ((r ^ 2 * phiPlus) : ℂ) ^ 2 * star ((r ^ 2 * phiPlus) : ℂ) ^ 4 = ((-95 / 192) + (-1 / 192) * d + (95 / 192) * alpha + (-1 / 576) * alpha * d) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-5 / 1358954496) + (5 / 679477248) * d + (103 / 4076863488) * d ^ 2 + (17 / 1019215872) * d ^ 3 + (77 / 12230590464) * d ^ 4 + (29 / 6115295232) * d ^ 5 + (11 / 12230590464) * d ^ 6 + (7 / 679477248) * alpha + (25 / 1019215872) * alpha * d + (31 / 2038431744) * alpha * d ^ 2 + (1 / 1528823808) * alpha * d ^ 3 + (1 / 679477248) * alpha * d ^ 4 + (1 / 1019215872) * alpha * d ^ 5 + (-5 / 6115295232) * alpha * d ^ 6 + (-1 / 1019215872) * alpha ^ 2 + (-1 / 254803968) * alpha ^ 2 * d + (-19 / 3057647616) * alpha ^ 2 * d ^ 2 + (-1 / 191102976) * alpha ^ 2 * d ^ 3 + (-1 / 339738624) * alpha ^ 2 * d ^ 4 + (-1 / 764411904) * alpha ^ 2 * d ^ 5 + (-1 / 3057647616) * alpha ^ 2 * d ^ 6 + (-1 / 2038431744) * alpha ^ 3 + (-7 / 3057647616) * alpha ^ 3 * d + (-25 / 6115295232) * alpha ^ 3 * d ^ 2 + (-5 / 1528823808) * alpha ^ 3 * d ^ 3 + (-5 / 6115295232) * alpha ^ 3 * d ^ 4 + (1 / 3057647616) * alpha ^ 3 * d ^ 5 + (1 / 6115295232) * alpha ^ 3 * d ^ 6 + (1 / 12230590464) * alpha ^ 4 + (1 / 2038431744) * alpha ^ 4 * d + (5 / 4076863488) * alpha ^ 4 * d ^ 2 + (5 / 3057647616) * alpha ^ 4 * d ^ 3 + (5 / 4076863488) * alpha ^ 4 * d ^ 4 + (1 / 2038431744) * alpha ^ 4 * d ^ 5 + (1 / 12230590464) * alpha ^ 4 * d ^ 6) * alpha_sq + ((-36671 / 42467328) + (-193 / 21233664) * d + (-1 / 663552) * d ^ 2 + (-1 / 63700992) * d ^ 3 + (-1 / 382205952) * d ^ 4 + (36671 / 42467328) * alpha + (-193 / 63700992) * alpha * d + (1 / 663552) * alpha * d ^ 2 + (-1 / 191102976) * alpha * d ^ 3 + (1 / 382205952) * alpha * d ^ 4) * d_sq
theorem phase32_30 : ((r ^ 2 * phiPlus) : ℂ) ^ 3 * star ((r ^ 2 * phiPlus) : ℂ) ^ 0 = ((47 / 1152) * d + (-143 / 1152) * alpha) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 12288) + (5 / 36864) * d + (1 / 36864) * d ^ 2 + (-1 / 36864) * d ^ 3 + (1 / 110592) * alpha + (1 / 36864) * alpha * d + (1 / 36864) * alpha * d ^ 2 + (1 / 110592) * alpha * d ^ 3) * alpha_sq + ((1 / 13824) * d + (-1 / 4608) * alpha) * d_sq
theorem phase32_31 : ((r ^ 2 * phiPlus) : ℂ) ^ 3 * star ((r ^ 2 * phiPlus) : ℂ) ^ 1 = ((-95 / 192) + (-1 / 192) * d + (-95 / 192) * alpha + (1 / 576) * alpha * d) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 1769472) + (1 / 442368) * d + (1 / 294912) * d ^ 2 + (1 / 442368) * d ^ 3 + (1 / 1769472) * d ^ 4 + (-1 / 884736) * alpha + (-1 / 331776) * alpha * d + (-1 / 442368) * alpha * d ^ 2 + (1 / 2654208) * alpha * d ^ 4 + (-1 / 5308416) * alpha ^ 2 + (-1 / 1327104) * alpha ^ 2 * d + (-1 / 884736) * alpha ^ 2 * d ^ 2 + (-1 / 1327104) * alpha ^ 2 * d ^ 3 + (-1 / 5308416) * alpha ^ 2 * d ^ 4) * alpha_sq + ((-191 / 221184) + (-1 / 110592) * d + (-1 / 663552) * d ^ 2 + (-191 / 221184) * alpha + (1 / 331776) * alpha * d + (-1 / 663552) * alpha * d ^ 2) * d_sq
theorem phase32_32 : ((r ^ 2 * phiPlus) : ℂ) ^ 3 * star ((r ^ 2 * phiPlus) : ℂ) ^ 2 = ((1 / 16) + (-1 / 48) * d + (1 / 48) * alpha + (1 / 48) * alpha * d) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-7 / 28311552) + (-29 / 84934656) * d + (-1 / 42467328) * d ^ 2 + (1 / 127401984) * d ^ 3 + (-11 / 254803968) * d ^ 4 + (5 / 254803968) * d ^ 5 + (-7 / 84934656) * alpha + (-19 / 84934656) * alpha * d + (-25 / 127401984) * alpha * d ^ 2 + (-1 / 14155776) * alpha * d ^ 3 + (-1 / 28311552) * alpha * d ^ 4 + (-5 / 254803968) * alpha * d ^ 5 + (1 / 84934656) * alpha ^ 2 + (11 / 254803968) * alpha ^ 2 * d + (7 / 127401984) * alpha ^ 2 * d ^ 2 + (1 / 42467328) * alpha ^ 2 * d ^ 3 + (-1 / 254803968) * alpha ^ 2 * d ^ 4 + (-1 / 254803968) * alpha ^ 2 * d ^ 5 + (1 / 254803968) * alpha ^ 3 + (5 / 254803968) * alpha ^ 3 * d + (5 / 127401984) * alpha ^ 3 * d ^ 2 + (5 / 127401984) * alpha ^ 3 * d ^ 3 + (5 / 254803968) * alpha ^ 3 * d ^ 4 + (1 / 254803968) * alpha ^ 3 * d ^ 5) * alpha_sq + ((193 / 1769472) + (-193 / 5308416) * d + (1 / 5308416) * d ^ 2 + (-1 / 15925248) * d ^ 3 + (193 / 5308416) * alpha + (193 / 5308416) * alpha * d + (1 / 15925248) * alpha * d ^ 2 + (1 / 15925248) * alpha * d ^ 3) * d_sq
theorem phase32_33 : ((r ^ 2 * phiPlus) : ℂ) ^ 3 * star ((r ^ 2 * phiPlus) : ℂ) ^ 3 = (1) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-37 / 1358954496) + (-1 / 25165824) * d + (-19 / 1358954496) * d ^ 2 + (-5 / 339738624) * d ^ 3 + (-49 / 4076863488) * d ^ 4 + (-1 / 2038431744) * d ^ 5 + (-7 / 4076863488) * d ^ 6 + (5 / 2038431744) * alpha ^ 2 + (1 / 113246208) * alpha ^ 2 * d + (23 / 2038431744) * alpha ^ 2 * d ^ 2 + (1 / 169869312) * alpha ^ 2 * d ^ 3 + (1 / 679477248) * alpha ^ 2 * d ^ 4 + (1 / 1019215872) * alpha ^ 2 * d ^ 5 + (1 / 2038431744) * alpha ^ 2 * d ^ 6 + (-1 / 12230590464) * alpha ^ 4 + (-1 / 2038431744) * alpha ^ 4 * d + (-5 / 4076863488) * alpha ^ 4 * d ^ 2 + (-5 / 3057647616) * alpha ^ 4 * d ^ 3 + (-5 / 4076863488) * alpha ^ 4 * d ^ 4 + (-1 / 2038431744) * alpha ^ 4 * d ^ 5 + (-1 / 12230590464) * alpha ^ 4 * d ^ 6) * alpha_sq + ((37057 / 21233664) + (97 / 31850496) * d ^ 2 + (1 / 191102976) * d ^ 4) * d_sq
theorem phase32_34 : ((r ^ 2 * phiPlus) : ℂ) ^ 3 * star ((r ^ 2 * phiPlus) : ℂ) ^ 4 = ((1 / 16) + (-1 / 48) * d + (-1 / 48) * alpha + (-1 / 48) * alpha * d) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-37 / 21743271936) + (-125 / 65229815808) * d + (-1 / 21743271936) * d ^ 2 + (-41 / 65229815808) * d ^ 3 + (-29 / 65229815808) * d ^ 4 + (43 / 195689447424) * d ^ 5 + (-19 / 195689447424) * d ^ 6 + (7 / 195689447424) * d ^ 7 + (37 / 65229815808) * alpha + (91 / 65229815808) * alpha * d + (73 / 65229815808) * alpha * d ^ 2 + (13 / 21743271936) * alpha * d ^ 3 + (109 / 195689447424) * alpha * d ^ 4 + (17 / 65229815808) * alpha * d ^ 5 + (1 / 21743271936) * alpha * d ^ 6 + (7 / 195689447424) * alpha * d ^ 7 + (5 / 32614907904) * alpha ^ 2 + (49 / 97844723712) * alpha ^ 2 * d + (17 / 32614907904) * alpha ^ 2 * d ^ 2 + (13 / 97844723712) * alpha ^ 2 * d ^ 3 + (-1 / 32614907904) * alpha ^ 2 * d ^ 4 + (1 / 32614907904) * alpha ^ 2 * d ^ 5 + (1 / 97844723712) * alpha ^ 2 * d ^ 6 + (-1 / 97844723712) * alpha ^ 2 * d ^ 7 + (-5 / 97844723712) * alpha ^ 3 + (-23 / 97844723712) * alpha ^ 3 * d + (-41 / 97844723712) * alpha ^ 3 * d ^ 2 + (-35 / 97844723712) * alpha ^ 3 * d ^ 3 + (-5 / 32614907904) * alpha ^ 3 * d ^ 4 + (-5 / 97844723712) * alpha ^ 3 * d ^ 5 + (-1 / 32614907904) * alpha ^ 3 * d ^ 6 + (-1 / 97844723712) * alpha ^ 3 * d ^ 7 + (-1 / 195689447424) * alpha ^ 4 + (-17 / 587068342272) * alpha ^ 4 * d + (-13 / 195689447424) * alpha ^ 4 * d ^ 2 + (-5 / 65229815808) * alpha ^ 4 * d ^ 3 + (-25 / 587068342272) * alpha ^ 4 * d ^ 4 + (-1 / 195689447424) * alpha ^ 4 * d ^ 5 + (1 / 195689447424) * alpha ^ 4 * d ^ 6 + (1 / 587068342272) * alpha ^ 4 * d ^ 7 + (1 / 587068342272) * alpha ^ 5 + (7 / 587068342272) * alpha ^ 5 * d + (7 / 195689447424) * alpha ^ 5 * d ^ 2 + (35 / 587068342272) * alpha ^ 5 * d ^ 3 + (35 / 587068342272) * alpha ^ 5 * d ^ 4 + (7 / 195689447424) * alpha ^ 5 * d ^ 5 + (7 / 587068342272) * alpha ^ 5 * d ^ 6 + (1 / 587068342272) * alpha ^ 5 * d ^ 7) * alpha_sq + ((37057 / 339738624) + (-37057 / 1019215872) * d + (97 / 509607936) * d ^ 2 + (-97 / 1528823808) * d ^ 3 + (1 / 3057647616) * d ^ 4 + (-1 / 9172942848) * d ^ 5 + (-37057 / 1019215872) * alpha + (-37057 / 1019215872) * alpha * d + (-97 / 1528823808) * alpha * d ^ 2 + (-97 / 1528823808) * alpha * d ^ 3 + (-1 / 9172942848) * alpha * d ^ 4 + (-1 / 9172942848) * alpha * d ^ 5) * d_sq
theorem phase32_40 : ((r ^ 2 * phiPlus) : ℂ) ^ 4 * star ((r ^ 2 * phiPlus) : ℂ) ^ 0 = ((-4417 / 9216) + (95 / 9216) * d + (4417 / 9216) * alpha + (95 / 27648) * alpha * d) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((17 / 1769472) + (5 / 442368) * d + (-5 / 884736) * d ^ 2 + (-1 / 147456) * d ^ 3 + (1 / 1769472) * d ^ 4 + (1 / 442368) * alpha + (1 / 165888) * alpha * d + (1 / 221184) * alpha * d ^ 2 + (-1 / 1327104) * alpha * d ^ 4 + (1 / 5308416) * alpha ^ 2 + (1 / 1327104) * alpha ^ 2 * d + (1 / 884736) * alpha ^ 2 * d ^ 2 + (1 / 1327104) * alpha ^ 2 * d ^ 3 + (1 / 5308416) * alpha ^ 2 * d ^ 4) * alpha_sq + ((-185 / 221184) + (1 / 55296) * d + (-1 / 663552) * d ^ 2 + (185 / 221184) * alpha + (1 / 165888) * alpha * d + (1 / 663552) * alpha * d ^ 2) * d_sq
theorem phase32_41 : ((r ^ 2 * phiPlus) : ℂ) ^ 4 * star ((r ^ 2 * phiPlus) : ℂ) ^ 1 = ((47 / 1152) * d + (-143 / 1152) * alpha) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 3145728) + (17 / 28311552) * d + (5 / 14155776) * d ^ 2 + (17 / 127401984) * d ^ 3 + (5 / 254803968) * d ^ 4 + (-11 / 254803968) * d ^ 5 + (-5 / 84934656) * alpha + (-1 / 9437184) * alpha * d + (5 / 127401984) * alpha * d ^ 2 + (7 / 42467328) * alpha * d ^ 3 + (7 / 84934656) * alpha * d ^ 4 + (1 / 254803968) * alpha * d ^ 5 + (-1 / 28311552) * alpha ^ 2 + (-11 / 84934656) * alpha ^ 2 * d + (-7 / 42467328) * alpha ^ 2 * d ^ 2 + (-1 / 14155776) * alpha ^ 2 * d ^ 3 + (1 / 84934656) * alpha ^ 2 * d ^ 4 + (1 / 84934656) * alpha ^ 2 * d ^ 5 + (-1 / 254803968) * alpha ^ 3 + (-5 / 254803968) * alpha ^ 3 * d + (-5 / 127401984) * alpha ^ 3 * d ^ 2 + (-5 / 127401984) * alpha ^ 3 * d ^ 3 + (-5 / 254803968) * alpha ^ 3 * d ^ 4 + (-1 / 254803968) * alpha ^ 3 * d ^ 5) * alpha_sq + ((7 / 98304) * d + (1 / 7962624) * d ^ 3 + (-575 / 2654208) * alpha + (-1 / 2654208) * alpha * d ^ 2) * d_sq
theorem phase32_42 : ((r ^ 2 * phiPlus) : ℂ) ^ 4 * star ((r ^ 2 * phiPlus) : ℂ) ^ 2 = ((-95 / 192) + (-1 / 192) * d + (-95 / 192) * alpha + (1 / 576) * alpha * d) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-5 / 1358954496) + (5 / 679477248) * d + (103 / 4076863488) * d ^ 2 + (17 / 1019215872) * d ^ 3 + (77 / 12230590464) * d ^ 4 + (29 / 6115295232) * d ^ 5 + (11 / 12230590464) * d ^ 6 + (-7 / 679477248) * alpha + (-25 / 1019215872) * alpha * d + (-31 / 2038431744) * alpha * d ^ 2 + (-1 / 1528823808) * alpha * d ^ 3 + (-1 / 679477248) * alpha * d ^ 4 + (-1 / 1019215872) * alpha * d ^ 5 + (5 / 6115295232) * alpha * d ^ 6 + (-1 / 1019215872) * alpha ^ 2 + (-1 / 254803968) * alpha ^ 2 * d + (-19 / 3057647616) * alpha ^ 2 * d ^ 2 + (-1 / 191102976) * alpha ^ 2 * d ^ 3 + (-1 / 339738624) * alpha ^ 2 * d ^ 4 + (-1 / 764411904) * alpha ^ 2 * d ^ 5 + (-1 / 3057647616) * alpha ^ 2 * d ^ 6 + (1 / 2038431744) * alpha ^ 3 + (7 / 3057647616) * alpha ^ 3 * d + (25 / 6115295232) * alpha ^ 3 * d ^ 2 + (5 / 1528823808) * alpha ^ 3 * d ^ 3 + (5 / 6115295232) * alpha ^ 3 * d ^ 4 + (-1 / 3057647616) * alpha ^ 3 * d ^ 5 + (-1 / 6115295232) * alpha ^ 3 * d ^ 6 + (1 / 12230590464) * alpha ^ 4 + (1 / 2038431744) * alpha ^ 4 * d + (5 / 4076863488) * alpha ^ 4 * d ^ 2 + (5 / 3057647616) * alpha ^ 4 * d ^ 3 + (5 / 4076863488) * alpha ^ 4 * d ^ 4 + (1 / 2038431744) * alpha ^ 4 * d ^ 5 + (1 / 12230590464) * alpha ^ 4 * d ^ 6) * alpha_sq + ((-36671 / 42467328) + (-193 / 21233664) * d + (-1 / 663552) * d ^ 2 + (-1 / 63700992) * d ^ 3 + (-1 / 382205952) * d ^ 4 + (-36671 / 42467328) * alpha + (193 / 63700992) * alpha * d + (-1 / 663552) * alpha * d ^ 2 + (1 / 191102976) * alpha * d ^ 3 + (-1 / 382205952) * alpha * d ^ 4) * d_sq
theorem phase32_43 : ((r ^ 2 * phiPlus) : ℂ) ^ 4 * star ((r ^ 2 * phiPlus) : ℂ) ^ 3 = ((1 / 16) + (-1 / 48) * d + (1 / 48) * alpha + (1 / 48) * alpha * d) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-37 / 21743271936) + (-125 / 65229815808) * d + (-1 / 21743271936) * d ^ 2 + (-41 / 65229815808) * d ^ 3 + (-29 / 65229815808) * d ^ 4 + (43 / 195689447424) * d ^ 5 + (-19 / 195689447424) * d ^ 6 + (7 / 195689447424) * d ^ 7 + (-37 / 65229815808) * alpha + (-91 / 65229815808) * alpha * d + (-73 / 65229815808) * alpha * d ^ 2 + (-13 / 21743271936) * alpha * d ^ 3 + (-109 / 195689447424) * alpha * d ^ 4 + (-17 / 65229815808) * alpha * d ^ 5 + (-1 / 21743271936) * alpha * d ^ 6 + (-7 / 195689447424) * alpha * d ^ 7 + (5 / 32614907904) * alpha ^ 2 + (49 / 97844723712) * alpha ^ 2 * d + (17 / 32614907904) * alpha ^ 2 * d ^ 2 + (13 / 97844723712) * alpha ^ 2 * d ^ 3 + (-1 / 32614907904) * alpha ^ 2 * d ^ 4 + (1 / 32614907904) * alpha ^ 2 * d ^ 5 + (1 / 97844723712) * alpha ^ 2 * d ^ 6 + (-1 / 97844723712) * alpha ^ 2 * d ^ 7 + (5 / 97844723712) * alpha ^ 3 + (23 / 97844723712) * alpha ^ 3 * d + (41 / 97844723712) * alpha ^ 3 * d ^ 2 + (35 / 97844723712) * alpha ^ 3 * d ^ 3 + (5 / 32614907904) * alpha ^ 3 * d ^ 4 + (5 / 97844723712) * alpha ^ 3 * d ^ 5 + (1 / 32614907904) * alpha ^ 3 * d ^ 6 + (1 / 97844723712) * alpha ^ 3 * d ^ 7 + (-1 / 195689447424) * alpha ^ 4 + (-17 / 587068342272) * alpha ^ 4 * d + (-13 / 195689447424) * alpha ^ 4 * d ^ 2 + (-5 / 65229815808) * alpha ^ 4 * d ^ 3 + (-25 / 587068342272) * alpha ^ 4 * d ^ 4 + (-1 / 195689447424) * alpha ^ 4 * d ^ 5 + (1 / 195689447424) * alpha ^ 4 * d ^ 6 + (1 / 587068342272) * alpha ^ 4 * d ^ 7 + (-1 / 587068342272) * alpha ^ 5 + (-7 / 587068342272) * alpha ^ 5 * d + (-7 / 195689447424) * alpha ^ 5 * d ^ 2 + (-35 / 587068342272) * alpha ^ 5 * d ^ 3 + (-35 / 587068342272) * alpha ^ 5 * d ^ 4 + (-7 / 195689447424) * alpha ^ 5 * d ^ 5 + (-7 / 587068342272) * alpha ^ 5 * d ^ 6 + (-1 / 587068342272) * alpha ^ 5 * d ^ 7) * alpha_sq + ((37057 / 339738624) + (-37057 / 1019215872) * d + (97 / 509607936) * d ^ 2 + (-97 / 1528823808) * d ^ 3 + (1 / 3057647616) * d ^ 4 + (-1 / 9172942848) * d ^ 5 + (37057 / 1019215872) * alpha + (37057 / 1019215872) * alpha * d + (97 / 1528823808) * alpha * d ^ 2 + (97 / 1528823808) * alpha * d ^ 3 + (1 / 9172942848) * alpha * d ^ 4 + (1 / 9172942848) * alpha * d ^ 5) * d_sq
theorem phase32_44 : ((r ^ 2 * phiPlus) : ℂ) ^ 4 * star ((r ^ 2 * phiPlus) : ℂ) ^ 4 = (1) := by
  rw [site32]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-175 / 1043677052928) + (-1 / 4831838208) * d + (-67 / 782757789696) * d ^ 2 + (-7 / 43486543872) * d ^ 3 + (-151 / 1565515579392) * d ^ 4 + (-7 / 391378894848) * d ^ 5 + (-235 / 7044820107264) * d ^ 6 + (-1 / 3522410053632) * d ^ 7 + (-85 / 28179280429056) * d ^ 8 + (67 / 3131031158784) * alpha ^ 2 + (1 / 14495514624) * alpha ^ 2 * d + (175 / 2348273369088) * alpha ^ 2 * d ^ 2 + (13 / 391378894848) * alpha ^ 2 * d ^ 3 + (91 / 4696546738176) * alpha ^ 2 * d ^ 4 + (23 / 1174136684544) * alpha ^ 2 * d ^ 5 + (5 / 782757789696) * alpha ^ 2 * d ^ 6 + (1 / 1174136684544) * alpha ^ 2 * d ^ 7 + (1 / 1043677052928) * alpha ^ 2 * d ^ 8 + (-13 / 9393093476352) * alpha ^ 4 + (-1 / 130459631616) * alpha ^ 4 * d + (-121 / 7044820107264) * alpha ^ 4 * d ^ 2 + (-23 / 1174136684544) * alpha ^ 4 * d ^ 3 + (-55 / 4696546738176) * alpha ^ 4 * d ^ 4 + (-13 / 3522410053632) * alpha ^ 4 * d ^ 5 + (-1 / 782757789696) * alpha ^ 4 * d ^ 6 + (-1 / 1174136684544) * alpha ^ 4 * d ^ 7 + (-7 / 28179280429056) * alpha ^ 4 * d ^ 8 + (1 / 28179280429056) * alpha ^ 6 + (1 / 3522410053632) * alpha ^ 6 * d + (7 / 7044820107264) * alpha ^ 6 * d ^ 2 + (7 / 3522410053632) * alpha ^ 6 * d ^ 3 + (35 / 14089640214528) * alpha ^ 6 * d ^ 4 + (7 / 3522410053632) * alpha ^ 6 * d ^ 5 + (7 / 7044820107264) * alpha ^ 6 * d ^ 6 + (1 / 3522410053632) * alpha ^ 6 * d ^ 7 + (1 / 28179280429056) * alpha ^ 6 * d ^ 8) * alpha_sq + ((7114945 / 4076863488) + (4139 / 1358954496) * d ^ 2 + (65 / 12230590464) * d ^ 4 + (1 / 110075314176) * d ^ 6) * d_sq
noncomputable def z32 : Fin 32 → ℂ := Fin.snoc z31 (r ^ 2 * phiPlus)
theorem v32_00 (t : ℂ) : (momentPoly 32 z32 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00]
  try simp only [phase32_00]
  try simp only [star_one, star_neg]
  ring
theorem v32_01 (t : ℂ) : (momentPoly 32 z32 0 1).eval t = ((1 / 16) * t + (-1 / 48) * d * t + (31 / 48) * alpha * t + (-1 / 48) * alpha * d * t) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_01]
  try simp only [phase32_00, phase32_01]
  try simp only [star_one, star_neg]
  ring
theorem v32_02 (t : ℂ) : (momentPoly 32 z32 0 2).eval t = ((-511 / 30) * t ^ 2 + (14677 / 960) * t ^ 4 + (1 / 12) * d * t ^ 2 + (-1 / 192) * d * t ^ 4 + (99 / 20) * alpha * t ^ 2 + (-1399 / 320) * alpha * t ^ 4 + (-1 / 36) * alpha * d * t ^ 2 + (-1 / 576) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_01, v31_02]
  try simp only [phase32_00, phase32_01, phase32_02]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 36) * t ^ 2 + (-1 / 36) * d * t ^ 2) * alpha_sq
theorem v32_03 (t : ℂ) : (momentPoly 32 z32 0 3).eval t = ((-9439 / 320) * t ^ 3 + (8089 / 320) * t ^ 5 + 1 * t ^ 9 + (1903 / 960) * d * t ^ 3 + (-1813 / 960) * d * t ^ 5 + (47 / 1152) * d * t ^ 9 + (-33007 / 1600) * alpha * t ^ 3 + (66779 / 4800) * alpha * t ^ 5 + (145327 / 28800) * alpha * t ^ 9 + (49 / 64) * alpha * d * t ^ 3 + (-133 / 192) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_01, v31_02, v31_03]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 240) * t ^ 3 + (207 / 160) * t ^ 5 + (-73 / 240) * d * t ^ 3 + (433 / 1440) * d * t ^ 5) * alpha_sq
theorem v32_04 (t : ℂ) : (momentPoly 32 z32 0 4).eval t = ((2881009 / 6000) * t ^ 4 + (-14025183 / 16000) * t ^ 6 + (23291581 / 48000) * t ^ 8 + (-7160893 / 72000) * t ^ 10 + (16891667 / 1152000) * t ^ 16 + (-2709 / 800) * d * t ^ 4 + (25957 / 9600) * d * t ^ 6 + (-413 / 640) * d * t ^ 8 + (16519 / 14400) * d * t ^ 10 + (95 / 9216) * d * t ^ 16 + (-2098809 / 4000) * alpha * t ^ 4 + (15089907 / 16000) * alpha * t ^ 6 + (-19823519 / 48000) * alpha * t ^ 8 + (-337951 / 24000) * alpha * t ^ 10 + (1533889 / 384000) * alpha * t ^ 16 + (29887 / 7200) * alpha * d * t ^ 4 + (-11383 / 3200) * alpha * d * t ^ 6 + (-71 / 5760) * alpha * d * t ^ 8 + (-16619 / 43200) * alpha * d * t ^ 10 + (-95 / 27648) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_01, v31_02, v31_03, v31_04]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_04]
  try simp only [star_one, star_neg]
  linear_combination ((13567 / 7200) * t ^ 4 + (187889 / 14400) * t ^ 6 + (-1387 / 96) * t ^ 8 + (-3419 / 43200) * t ^ 10 + (13567 / 7200) * d * t ^ 4 + (-20891 / 14400) * d * t ^ 6 + (73 / 1440) * d * t ^ 8 + (-17719 / 43200) * d * t ^ 10) * alpha_sq
theorem v32_10 (t : ℂ) : (momentPoly 32 z32 1 0).eval t = ((1 / 16) * t + (-1 / 48) * d * t + (-31 / 48) * alpha * t + (1 / 48) * alpha * d * t) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_10]
  try simp only [phase32_00, phase32_10]
  try simp only [star_one, star_neg]
  ring
theorem v32_11 (t : ℂ) : (momentPoly 32 z32 1 1).eval t = (32 + (-119 / 4) * t ^ 2 + (-1 / 12) * d * t ^ 2) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_01, v31_10, v31_11]
  try simp only [phase32_00, phase32_01, phase32_10, phase32_11]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 36) * t ^ 2 + (1 / 36) * d * t ^ 2) * alpha_sq
theorem v32_12 (t : ℂ) : (momentPoly 32 z32 1 2).eval t = ((63 / 16) * t + (893 / 192) * t ^ 3 + (-477 / 64) * t ^ 5 + (-21 / 16) * d * t + (1237 / 960) * d * t ^ 3 + (-9 / 320) * d * t ^ 5 + (651 / 16) * alpha * t + (-26309 / 960) * alpha * t ^ 3 + (-3467 / 320) * alpha * t ^ 5 + (-21 / 16) * alpha * d * t + (249 / 320) * alpha * d * t ^ 3 + (1249 / 2880) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_01, v31_02, v31_10, v31_11, v31_12]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_10, phase32_11, phase32_12]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 720) * t ^ 3 + (-69 / 160) * t ^ 5 + (73 / 720) * d * t ^ 3 + (-433 / 4320) * d * t ^ 5) * alpha_sq
theorem v32_13 (t : ℂ) : (momentPoly 32 z32 1 3).eval t = ((-15841 / 10) * t ^ 2 + (27621383 / 9600) * t ^ 4 + (-8287023 / 6400) * t ^ 6 + (-113977 / 19200) * t ^ 10 + (31 / 4) * d * t ^ 2 + (-14331 / 3200) * d * t ^ 4 + (-50341 / 19200) * d * t ^ 6 + (-18919 / 57600) * d * t ^ 10 + (9207 / 20) * alpha * t ^ 2 + (-2637349 / 3200) * alpha * t ^ 4 + (6950461 / 19200) * alpha * t ^ 6 + (260839 / 57600) * alpha * t ^ 10 + (-31 / 12) * alpha * d * t ^ 2 + (2943 / 3200) * alpha * d * t ^ 4 + (10611 / 6400) * alpha * d * t ^ 6 + (-697 / 6400) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_01, v31_02, v31_03, v31_10, v31_11, v31_12, v31_13]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_10, phase32_11, phase32_12, phase32_13]
  try simp only [star_one, star_neg]
  linear_combination ((-31 / 12) * t ^ 2 + (12631 / 9600) * t ^ 4 + (20147 / 19200) * t ^ 6 + (3419 / 172800) * t ^ 10 + (-31 / 12) * d * t ^ 2 + (12631 / 9600) * d * t ^ 4 + (20147 / 19200) * d * t ^ 6 + (17719 / 172800) * d * t ^ 10) * alpha_sq
theorem v32_14 (t : ℂ) : (momentPoly 32 z32 1 4).eval t = ((-575779 / 160) * t ^ 3 + (348444127 / 64000) * t ^ 5 + (-94922081 / 96000) * t ^ 7 + (-87968243 / 128000) * t ^ 9 + (-18347503 / 96000) * t ^ 11 + (8819459 / 1152000) * t ^ 17 + (116083 / 480) * d * t ^ 3 + (-248972957 / 576000) * d * t ^ 5 + (16063219 / 96000) * d * t ^ 7 + (28241713 / 1152000) * d * t ^ 9 + (-8401 / 32000) * d * t ^ 11 + (-77049 / 128000) * d * t ^ 17 + (-2013427 / 800) * alpha * t ^ 3 + (2117363741 / 576000) * alpha * t ^ 5 + (-81205627 / 96000) * alpha * t ^ 7 + (295121471 / 1152000) * alpha * t ^ 9 + (-162035783 / 288000) * alpha * t ^ 11 + (-16245667 / 1152000) * alpha * t ^ 17 + (2989 / 32) * alpha * d * t ^ 3 + (-5793229 / 38400) * alpha * d * t ^ 5 + (2226379 / 57600) * alpha * d * t ^ 7 + (945311 / 46080) * alpha * d * t ^ 9 + (-279929 / 172800) * alpha * d * t ^ 11 + (1985 / 9216) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_01, v31_02, v31_03, v31_04, v31_10, v31_11, v31_12, v31_13, v31_14]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_04, phase32_10, phase32_11, phase32_12, phase32_13, phase32_14]
  try simp only [star_one, star_neg]
  linear_combination ((-4453 / 120) * t ^ 3 + (6569063 / 36000) * t ^ 5 + (-7036927 / 72000) * t ^ 7 + (-3103067 / 72000) * t ^ 9 + (-2252 / 3375) * t ^ 11 + (237727 / 576000) * t ^ 17 + (-4453 / 120) * d * t ^ 3 + (6479689 / 108000) * d * t ^ 5 + (-2713831 / 216000) * d * t ^ 7 + (-2109151 / 216000) * d * t ^ 9 + (-2252 / 3375) * d * t ^ 11 + (495043 / 5184000) * d * t ^ 17) * alpha_sq
theorem v32_20 (t : ℂ) : (momentPoly 32 z32 2 0).eval t = ((-511 / 30) * t ^ 2 + (14677 / 960) * t ^ 4 + (1 / 12) * d * t ^ 2 + (-1 / 192) * d * t ^ 4 + (-99 / 20) * alpha * t ^ 2 + (1399 / 320) * alpha * t ^ 4 + (1 / 36) * alpha * d * t ^ 2 + (1 / 576) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_10, v31_20]
  try simp only [phase32_00, phase32_10, phase32_20]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 36) * t ^ 2 + (-1 / 36) * d * t ^ 2) * alpha_sq
theorem v32_21 (t : ℂ) : (momentPoly 32 z32 2 1).eval t = ((63 / 16) * t + (893 / 192) * t ^ 3 + (-477 / 64) * t ^ 5 + (-21 / 16) * d * t + (1237 / 960) * d * t ^ 3 + (-9 / 320) * d * t ^ 5 + (-651 / 16) * alpha * t + (26309 / 960) * alpha * t ^ 3 + (3467 / 320) * alpha * t ^ 5 + (21 / 16) * alpha * d * t + (-249 / 320) * alpha * d * t ^ 3 + (-1249 / 2880) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_01, v31_10, v31_11, v31_20, v31_21]
  try simp only [phase32_00, phase32_01, phase32_10, phase32_11, phase32_20, phase32_21]
  try simp only [star_one, star_neg]
  linear_combination ((73 / 720) * t ^ 3 + (-69 / 160) * t ^ 5 + (73 / 720) * d * t ^ 3 + (-433 / 4320) * d * t ^ 5) * alpha_sq
theorem v32_22 (t : ℂ) : (momentPoly 32 z32 2 2).eval t = (2016 + (-3689) * t ^ 2 + (781979 / 400) * t ^ 4 + (-1702419 / 3200) * t ^ 6 + (2487361 / 9600) * t ^ 8 + (-31 / 3) * d * t ^ 2 + (2281 / 360) * d * t ^ 4 + (2391 / 640) * d * t ^ 6 + (-131 / 1152) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_01, v31_02, v31_10, v31_11, v31_12, v31_20, v31_21, v31_22]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_10, phase32_11, phase32_12, phase32_20, phase32_21, phase32_22]
  try simp only [star_one, star_neg]
  linear_combination ((31 / 9) * t ^ 2 + (-2573 / 1080) * t ^ 4 + (-24833 / 4320) * t ^ 6 + (1387 / 288) * t ^ 8 + (31 / 9) * d * t ^ 2 + (-2573 / 1080) * d * t ^ 4 + (-791 / 864) * d * t ^ 6 + (-73 / 4320) * d * t ^ 8) * alpha_sq
theorem v32_23 (t : ℂ) : (momentPoly 32 z32 2 3).eval t = ((1465 / 4) * t + (54473 / 64) * t ^ 3 + (-73045749 / 32000) * t ^ 5 + (10475597 / 12800) * t ^ 7 + (87647063 / 384000) * t ^ 9 + (10764761 / 144000) * t ^ 11 + (-58842043 / 1152000) * t ^ 13 + (-1465 / 12) * d * t + (75457 / 320) * d * t ^ 3 + (-314021 / 2304) * d * t ^ 5 + (4688063 / 115200) * d * t ^ 7 + (-276019 / 15360) * d * t ^ 9 + (-12491 / 12800) * d * t ^ 11 + (141257 / 230400) * d * t ^ 13 + (45415 / 12) * alpha * t + (-1604849 / 320) * alpha * t ^ 3 + (-78939793 / 288000) * alpha * t ^ 5 + (139024649 / 115200) * alpha * t ^ 7 + (113602819 / 384000) * alpha * t ^ 9 + (-39504023 / 576000) * alpha * t ^ 11 + (93212671 / 1152000) * alpha * t ^ 13 + (-1465 / 12) * alpha * d * t + (45567 / 320) * alpha * d * t ^ 3 + (2056043 / 57600) * alpha * d * t ^ 5 + (-483249 / 12800) * alpha * d * t ^ 7 + (-840457 / 46080) * alpha * d * t ^ 9 + (-53657 / 86400) * alpha * d * t ^ 11 + (120721 / 691200) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_01, v31_02, v31_03, v31_10, v31_11, v31_12, v31_13, v31_20, v31_21, v31_22, v31_23]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_10, phase32_11, phase32_12, phase32_13, phase32_20, phase32_21, phase32_22, phase32_23]
  try simp only [star_one, star_neg]
  linear_combination ((4453 / 240) * t ^ 3 + (-139201 / 1440) * t ^ 5 + (1625209 / 23040) * t ^ 7 + (382261 / 46080) * t ^ 9 + (-1483 / 3456) * t ^ 11 + (-84383 / 46080) * t ^ 13 + (4453 / 240) * d * t ^ 3 + (-153053 / 4320) * d * t ^ 5 + (5780413 / 345600) * d * t ^ 7 + (-20119 / 691200) * d * t ^ 9 + (7 / 40) * d * t ^ 11 + (17719 / 2073600) * d * t ^ 13) * alpha_sq
theorem v32_24 (t : ℂ) : (momentPoly 32 z32 2 4).eval t = ((-579985 / 3) * t ^ 2 + (167326629 / 320) * t ^ 4 + (-114072548951 / 240000) * t ^ 6 + (207952172261 / 1280000) * t ^ 8 + (-10802051423 / 384000) * t ^ 10 + (291173708539 / 23040000) * t ^ 12 + (-7178469799 / 5760000) * t ^ 14 + (-4099067159 / 23040000) * t ^ 18 + (1802591897 / 11520000) * t ^ 20 + (5675 / 6) * d * t ^ 2 + (-325669 / 320) * d * t ^ 4 + (-9832577 / 24000) * d * t ^ 6 + (722836919 / 2304000) * d * t ^ 8 + (112876457 / 1152000) * d * t ^ 10 + (210279697 / 4608000) * d * t ^ 12 + (83482073 / 3456000) * d * t ^ 14 + (3647699 / 2764800) * d * t ^ 18 + (127523 / 1152000) * d * t ^ 20 + (112365 / 2) * alpha * t ^ 2 + (-47956341 / 320) * alpha * t ^ 4 + (8125994479 / 60000) * alpha * t ^ 6 + (-191761392473 / 3840000) * alpha * t ^ 8 + (14421908071 / 1152000) * alpha * t ^ 10 + (-249933117167 / 69120000) * alpha * t ^ 12 + (-438860719 / 640000) * alpha * t ^ 14 + (-3448580791 / 23040000) * alpha * t ^ 18 + (4477831819 / 34560000) * alpha * t ^ 20 + (-5675 / 18) * alpha * d * t ^ 2 + (230171 / 960) * alpha * d * t ^ 4 + (1315577 / 3600) * alpha * d * t ^ 6 + (-96272497 / 460800) * alpha * d * t ^ 8 + (-7788893 / 76800) * alpha * d * t ^ 10 + (89356661 / 4608000) * alpha * d * t ^ 12 + (-1447619 / 3456000) * alpha * d * t ^ 14 + (13346971 / 13824000) * alpha * d * t ^ 18 + (-3727 / 3456000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_01, v31_02, v31_03, v31_04, v31_10, v31_11, v31_12, v31_13, v31_14, v31_20, v31_21, v31_22, v31_23, v31_24]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_04, phase32_10, phase32_11, phase32_12, phase32_13, phase32_14, phase32_20, phase32_21, phase32_22, phase32_23, phase32_24]
  try simp only [star_one, star_neg]
  linear_combination ((-5675 / 18) * t ^ 2 + (12631 / 40) * t ^ 4 + (41675969 / 216000) * t ^ 6 + (94114127 / 864000) * t ^ 8 + (-3877711 / 7200) * t ^ 10 + (600480091 / 2592000) * t ^ 12 + (16243487 / 2592000) * t ^ 14 + (17695847 / 10368000) * t ^ 18 + (-3142237 / 691200) * t ^ 20 + (-5675 / 18) * d * t ^ 2 + (12631 / 40) * d * t ^ 4 + (41675969 / 216000) * d * t ^ 6 + (-129530437 / 864000) * d * t ^ 8 + (-2000699 / 108000) * d * t ^ 10 + (-3115403 / 172800) * d * t ^ 12 + (-17755621 / 2592000) * d * t ^ 14 + (-6313853 / 10368000) * d * t ^ 18 + (-30949 / 3456000) * d * t ^ 20) * alpha_sq
theorem v32_30 (t : ℂ) : (momentPoly 32 z32 3 0).eval t = ((-9439 / 320) * t ^ 3 + (8089 / 320) * t ^ 5 + 1 * t ^ 9 + (1903 / 960) * d * t ^ 3 + (-1813 / 960) * d * t ^ 5 + (47 / 1152) * d * t ^ 9 + (33007 / 1600) * alpha * t ^ 3 + (-66779 / 4800) * alpha * t ^ 5 + (-145327 / 28800) * alpha * t ^ 9 + (-49 / 64) * alpha * d * t ^ 3 + (133 / 192) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_10, v31_20, v31_30]
  try simp only [phase32_00, phase32_10, phase32_20, phase32_30]
  try simp only [star_one, star_neg]
  linear_combination ((-73 / 240) * t ^ 3 + (207 / 160) * t ^ 5 + (-73 / 240) * d * t ^ 3 + (433 / 1440) * d * t ^ 5) * alpha_sq
theorem v32_31 (t : ℂ) : (momentPoly 32 z32 3 1).eval t = ((-15841 / 10) * t ^ 2 + (27621383 / 9600) * t ^ 4 + (-8287023 / 6400) * t ^ 6 + (-113977 / 19200) * t ^ 10 + (31 / 4) * d * t ^ 2 + (-14331 / 3200) * d * t ^ 4 + (-50341 / 19200) * d * t ^ 6 + (-18919 / 57600) * d * t ^ 10 + (-9207 / 20) * alpha * t ^ 2 + (2637349 / 3200) * alpha * t ^ 4 + (-6950461 / 19200) * alpha * t ^ 6 + (-260839 / 57600) * alpha * t ^ 10 + (31 / 12) * alpha * d * t ^ 2 + (-2943 / 3200) * alpha * d * t ^ 4 + (-10611 / 6400) * alpha * d * t ^ 6 + (697 / 6400) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_01, v31_10, v31_11, v31_20, v31_21, v31_30, v31_31]
  try simp only [phase32_00, phase32_01, phase32_10, phase32_11, phase32_20, phase32_21, phase32_30, phase32_31]
  try simp only [star_one, star_neg]
  linear_combination ((-31 / 12) * t ^ 2 + (12631 / 9600) * t ^ 4 + (20147 / 19200) * t ^ 6 + (3419 / 172800) * t ^ 10 + (-31 / 12) * d * t ^ 2 + (12631 / 9600) * d * t ^ 4 + (20147 / 19200) * d * t ^ 6 + (17719 / 172800) * d * t ^ 10) * alpha_sq
theorem v32_32 (t : ℂ) : (momentPoly 32 z32 3 2).eval t = ((1465 / 4) * t + (54473 / 64) * t ^ 3 + (-73045749 / 32000) * t ^ 5 + (10475597 / 12800) * t ^ 7 + (87647063 / 384000) * t ^ 9 + (10764761 / 144000) * t ^ 11 + (-58842043 / 1152000) * t ^ 13 + (-1465 / 12) * d * t + (75457 / 320) * d * t ^ 3 + (-314021 / 2304) * d * t ^ 5 + (4688063 / 115200) * d * t ^ 7 + (-276019 / 15360) * d * t ^ 9 + (-12491 / 12800) * d * t ^ 11 + (141257 / 230400) * d * t ^ 13 + (-45415 / 12) * alpha * t + (1604849 / 320) * alpha * t ^ 3 + (78939793 / 288000) * alpha * t ^ 5 + (-139024649 / 115200) * alpha * t ^ 7 + (-113602819 / 384000) * alpha * t ^ 9 + (39504023 / 576000) * alpha * t ^ 11 + (-93212671 / 1152000) * alpha * t ^ 13 + (1465 / 12) * alpha * d * t + (-45567 / 320) * alpha * d * t ^ 3 + (-2056043 / 57600) * alpha * d * t ^ 5 + (483249 / 12800) * alpha * d * t ^ 7 + (840457 / 46080) * alpha * d * t ^ 9 + (53657 / 86400) * alpha * d * t ^ 11 + (-120721 / 691200) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_01, v31_02, v31_10, v31_11, v31_12, v31_20, v31_21, v31_22, v31_30, v31_31, v31_32]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_10, phase32_11, phase32_12, phase32_20, phase32_21, phase32_22, phase32_30, phase32_31, phase32_32]
  try simp only [star_one, star_neg]
  linear_combination ((4453 / 240) * t ^ 3 + (-139201 / 1440) * t ^ 5 + (1625209 / 23040) * t ^ 7 + (382261 / 46080) * t ^ 9 + (-1483 / 3456) * t ^ 11 + (-84383 / 46080) * t ^ 13 + (4453 / 240) * d * t ^ 3 + (-153053 / 4320) * d * t ^ 5 + (5780413 / 345600) * d * t ^ 7 + (-20119 / 691200) * d * t ^ 9 + (7 / 40) * d * t ^ 11 + (17719 / 2073600) * d * t ^ 13) * alpha_sq
theorem v32_33 (t : ℂ) : (momentPoly 32 z32 3 3).eval t = (187520 + (-2025975 / 4) * t ^ 2 + (21113433 / 40) * t ^ 4 + (-165673619299 / 480000) * t ^ 6 + (190060117429 / 960000) * t ^ 8 + (-19746744441 / 320000) * t ^ 10 + (723687919 / 720000) * t ^ 12 + (-1905846941 / 1920000) * t ^ 14 + (266932423 / 5760000) * t ^ 18 + (-5675 / 4) * d * t ^ 2 + (6843 / 4) * d * t ^ 4 + (9916837 / 19200) * d * t ^ 6 + (-5139727 / 7680) * d * t ^ 8 + (-1702027 / 12800) * d * t ^ 10 + (1558693 / 115200) * d * t ^ 12 + (-275263 / 12800) * d * t ^ 14 + (47 / 576) * d * t ^ 18) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_01, v31_02, v31_03, v31_10, v31_11, v31_12, v31_13, v31_20, v31_21, v31_22, v31_23, v31_30, v31_31, v31_32, v31_33]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_10, phase32_11, phase32_12, phase32_13, phase32_20, phase32_21, phase32_22, phase32_23, phase32_30, phase32_31, phase32_32, phase32_33]
  try simp only [star_one, star_neg]
  linear_combination ((5675 / 12) * t ^ 2 + (-2573 / 4) * t ^ 4 + (-128545417 / 96000) * t ^ 6 + (308715479 / 115200) * t ^ 8 + (-667776253 / 576000) * t ^ 10 + (-98221 / 36000) * t ^ 12 + (-7377643 / 1152000) * t ^ 14 + (-2533817 / 2073600) * t ^ 18 + (5675 / 12) * d * t ^ 2 + (-2573 / 4) * d * t ^ 4 + (-5656651 / 288000) * d * t ^ 6 + (15965879 / 115200) * d * t ^ 8 + (28805347 / 576000) * d * t ^ 10 + (-14415013 / 1728000) * d * t ^ 12 + (17762693 / 1728000) * d * t ^ 14) * alpha_sq
theorem v32_34 (t : ℂ) : (momentPoly 32 z32 3 4).eval t = ((715295 / 16) * t + (4905249 / 32) * t ^ 3 + (-9135874323 / 16000) * t ^ 5 + (8243505188657 / 19200000) * t ^ 7 + (122241833593 / 19200000) * t ^ 9 + (-1333862376571 / 38400000) * t ^ 11 + (-120949083517 / 2560000) * t ^ 13 + (484344472921 / 19200000) * t ^ 15 + (-330454816561 / 57600000) * t ^ 17 + (-681553625833 / 691200000) * t ^ 19 + (325278440327 / 460800000) * t ^ 21 + (104110038773 / 1382400000) * t ^ 25 + (-715295 / 48) * d * t + (6794841 / 160) * d * t ^ 3 + (-90918509 / 1920) * d * t ^ 5 + (373826226787 / 11520000) * d * t ^ 7 + (-68594091247 / 3840000) * d * t ^ 9 + (110614899851 / 23040000) * d * t ^ 11 + (5551108073 / 17280000) * d * t ^ 13 + (180789263 / 2880000) * d * t ^ 15 + (35267803 / 1843200) * d * t ^ 17 + (4489197811 / 138240000) * d * t ^ 19 + (-3468011353 / 92160000) * d * t ^ 21 + (31925251 / 55296000) * d * t ^ 25 + (22174145 / 48) * alpha * t + (-144515337 / 160) * alpha * t ^ 3 + (11884822663 / 48000) * alpha * t ^ 5 + (1830978460497 / 6400000) * alpha * t ^ 7 + (-454415466461 / 19200000) * alpha * t ^ 9 + (-9249136969939 / 115200000) * alpha * t ^ 11 + (646108895971 / 17280000) * alpha * t ^ 13 + (-665483284783 / 28800000) * alpha * t ^ 15 + (-71599012103 / 25600000) * alpha * t ^ 17 + (315906081851 / 691200000) * alpha * t ^ 19 + (-140751120629 / 460800000) * alpha * t ^ 21 + (-32588604547 / 460800000) * alpha * t ^ 25 + (-715295 / 48) * alpha * d * t + (4103271 / 160) * alpha * d * t ^ 3 + (-3708311 / 3200) * alpha * d * t ^ 5 + (-114595066643 / 11520000) * alpha * d * t ^ 7 + (-42931659671 / 11520000) * alpha * d * t ^ 9 + (65969677381 / 23040000) * alpha * d * t ^ 11 + (83889322847 / 69120000) * alpha * d * t ^ 13 + (372332527 / 11520000) * alpha * d * t ^ 15 + (-22405291 / 1382400) * alpha * d * t ^ 17 + (-2485841647 / 414720000) * alpha * d * t ^ 19 + (154292621 / 276480000) * alpha * d * t ^ 21 + (21292003 / 165888000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_01, v31_02, v31_03, v31_04, v31_10, v31_11, v31_12, v31_13, v31_14, v31_20, v31_21, v31_22, v31_23, v31_24, v31_30, v31_31, v31_32, v31_33, v31_34]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_04, phase32_10, phase32_11, phase32_12, phase32_13, phase32_14, phase32_20, phase32_21, phase32_22, phase32_23, phase32_24, phase32_30, phase32_31, phase32_32, phase32_33, phase32_34]
  try simp only [star_one, star_neg]
  linear_combination ((133663 / 40) * t ^ 3 + (-1968251 / 96) * t ^ 5 + (81123765277 / 2880000) * t ^ 7 + (-3319560887 / 360000) * t ^ 9 + (-158323289 / 153600) * t ^ 11 + (-3551616223 / 2880000) * t ^ 13 + (21946462219 / 34560000) * t ^ 15 + (-1273329011 / 6912000) * t ^ 17 + (-8687988973 / 414720000) * t ^ 19 + (10966798097 / 276480000) * t ^ 21 + (99733361 / 55296000) * t ^ 25 + (133663 / 40) * d * t ^ 3 + (-2693831 / 288) * d * t ^ 5 + (76921683931 / 8640000) * d * t ^ 7 + (-14958941849 / 4320000) * d * t ^ 9 + (6159044317 / 6912000) * d * t ^ 11 + (-3476451461 / 12960000) * d * t ^ 13 + (-5311488853 / 103680000) * d * t ^ 15 + (17687093 / 20736000) * d * t ^ 17 + (-4144898993 / 414720000) * d * t ^ 19 + (7715969311 / 829440000) * d * t ^ 21 + (336661 / 19906560) * d * t ^ 25) * alpha_sq
theorem v32_40 (t : ℂ) : (momentPoly 32 z32 4 0).eval t = ((2881009 / 6000) * t ^ 4 + (-14025183 / 16000) * t ^ 6 + (23291581 / 48000) * t ^ 8 + (-7160893 / 72000) * t ^ 10 + (16891667 / 1152000) * t ^ 16 + (-2709 / 800) * d * t ^ 4 + (25957 / 9600) * d * t ^ 6 + (-413 / 640) * d * t ^ 8 + (16519 / 14400) * d * t ^ 10 + (95 / 9216) * d * t ^ 16 + (2098809 / 4000) * alpha * t ^ 4 + (-15089907 / 16000) * alpha * t ^ 6 + (19823519 / 48000) * alpha * t ^ 8 + (337951 / 24000) * alpha * t ^ 10 + (-1533889 / 384000) * alpha * t ^ 16 + (-29887 / 7200) * alpha * d * t ^ 4 + (11383 / 3200) * alpha * d * t ^ 6 + (71 / 5760) * alpha * d * t ^ 8 + (16619 / 43200) * alpha * d * t ^ 10 + (95 / 27648) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_10, v31_20, v31_30, v31_40]
  try simp only [phase32_00, phase32_10, phase32_20, phase32_30, phase32_40]
  try simp only [star_one, star_neg]
  linear_combination ((13567 / 7200) * t ^ 4 + (187889 / 14400) * t ^ 6 + (-1387 / 96) * t ^ 8 + (-3419 / 43200) * t ^ 10 + (13567 / 7200) * d * t ^ 4 + (-20891 / 14400) * d * t ^ 6 + (73 / 1440) * d * t ^ 8 + (-17719 / 43200) * d * t ^ 10) * alpha_sq
theorem v32_41 (t : ℂ) : (momentPoly 32 z32 4 1).eval t = ((-575779 / 160) * t ^ 3 + (348444127 / 64000) * t ^ 5 + (-94922081 / 96000) * t ^ 7 + (-87968243 / 128000) * t ^ 9 + (-18347503 / 96000) * t ^ 11 + (8819459 / 1152000) * t ^ 17 + (116083 / 480) * d * t ^ 3 + (-248972957 / 576000) * d * t ^ 5 + (16063219 / 96000) * d * t ^ 7 + (28241713 / 1152000) * d * t ^ 9 + (-8401 / 32000) * d * t ^ 11 + (-77049 / 128000) * d * t ^ 17 + (2013427 / 800) * alpha * t ^ 3 + (-2117363741 / 576000) * alpha * t ^ 5 + (81205627 / 96000) * alpha * t ^ 7 + (-295121471 / 1152000) * alpha * t ^ 9 + (162035783 / 288000) * alpha * t ^ 11 + (16245667 / 1152000) * alpha * t ^ 17 + (-2989 / 32) * alpha * d * t ^ 3 + (5793229 / 38400) * alpha * d * t ^ 5 + (-2226379 / 57600) * alpha * d * t ^ 7 + (-945311 / 46080) * alpha * d * t ^ 9 + (279929 / 172800) * alpha * d * t ^ 11 + (-1985 / 9216) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_01, v31_10, v31_11, v31_20, v31_21, v31_30, v31_31, v31_40, v31_41]
  try simp only [phase32_00, phase32_01, phase32_10, phase32_11, phase32_20, phase32_21, phase32_30, phase32_31, phase32_40, phase32_41]
  try simp only [star_one, star_neg]
  linear_combination ((-4453 / 120) * t ^ 3 + (6569063 / 36000) * t ^ 5 + (-7036927 / 72000) * t ^ 7 + (-3103067 / 72000) * t ^ 9 + (-2252 / 3375) * t ^ 11 + (237727 / 576000) * t ^ 17 + (-4453 / 120) * d * t ^ 3 + (6479689 / 108000) * d * t ^ 5 + (-2713831 / 216000) * d * t ^ 7 + (-2109151 / 216000) * d * t ^ 9 + (-2252 / 3375) * d * t ^ 11 + (495043 / 5184000) * d * t ^ 17) * alpha_sq
theorem v32_42 (t : ℂ) : (momentPoly 32 z32 4 2).eval t = ((-579985 / 3) * t ^ 2 + (167326629 / 320) * t ^ 4 + (-114072548951 / 240000) * t ^ 6 + (207952172261 / 1280000) * t ^ 8 + (-10802051423 / 384000) * t ^ 10 + (291173708539 / 23040000) * t ^ 12 + (-7178469799 / 5760000) * t ^ 14 + (-4099067159 / 23040000) * t ^ 18 + (1802591897 / 11520000) * t ^ 20 + (5675 / 6) * d * t ^ 2 + (-325669 / 320) * d * t ^ 4 + (-9832577 / 24000) * d * t ^ 6 + (722836919 / 2304000) * d * t ^ 8 + (112876457 / 1152000) * d * t ^ 10 + (210279697 / 4608000) * d * t ^ 12 + (83482073 / 3456000) * d * t ^ 14 + (3647699 / 2764800) * d * t ^ 18 + (127523 / 1152000) * d * t ^ 20 + (-112365 / 2) * alpha * t ^ 2 + (47956341 / 320) * alpha * t ^ 4 + (-8125994479 / 60000) * alpha * t ^ 6 + (191761392473 / 3840000) * alpha * t ^ 8 + (-14421908071 / 1152000) * alpha * t ^ 10 + (249933117167 / 69120000) * alpha * t ^ 12 + (438860719 / 640000) * alpha * t ^ 14 + (3448580791 / 23040000) * alpha * t ^ 18 + (-4477831819 / 34560000) * alpha * t ^ 20 + (5675 / 18) * alpha * d * t ^ 2 + (-230171 / 960) * alpha * d * t ^ 4 + (-1315577 / 3600) * alpha * d * t ^ 6 + (96272497 / 460800) * alpha * d * t ^ 8 + (7788893 / 76800) * alpha * d * t ^ 10 + (-89356661 / 4608000) * alpha * d * t ^ 12 + (1447619 / 3456000) * alpha * d * t ^ 14 + (-13346971 / 13824000) * alpha * d * t ^ 18 + (3727 / 3456000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_01, v31_02, v31_10, v31_11, v31_12, v31_20, v31_21, v31_22, v31_30, v31_31, v31_32, v31_40, v31_41, v31_42]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_10, phase32_11, phase32_12, phase32_20, phase32_21, phase32_22, phase32_30, phase32_31, phase32_32, phase32_40, phase32_41, phase32_42]
  try simp only [star_one, star_neg]
  linear_combination ((-5675 / 18) * t ^ 2 + (12631 / 40) * t ^ 4 + (41675969 / 216000) * t ^ 6 + (94114127 / 864000) * t ^ 8 + (-3877711 / 7200) * t ^ 10 + (600480091 / 2592000) * t ^ 12 + (16243487 / 2592000) * t ^ 14 + (17695847 / 10368000) * t ^ 18 + (-3142237 / 691200) * t ^ 20 + (-5675 / 18) * d * t ^ 2 + (12631 / 40) * d * t ^ 4 + (41675969 / 216000) * d * t ^ 6 + (-129530437 / 864000) * d * t ^ 8 + (-2000699 / 108000) * d * t ^ 10 + (-3115403 / 172800) * d * t ^ 12 + (-17755621 / 2592000) * d * t ^ 14 + (-6313853 / 10368000) * d * t ^ 18 + (-30949 / 3456000) * d * t ^ 20) * alpha_sq
theorem v32_43 (t : ℂ) : (momentPoly 32 z32 4 3).eval t = ((715295 / 16) * t + (4905249 / 32) * t ^ 3 + (-9135874323 / 16000) * t ^ 5 + (8243505188657 / 19200000) * t ^ 7 + (122241833593 / 19200000) * t ^ 9 + (-1333862376571 / 38400000) * t ^ 11 + (-120949083517 / 2560000) * t ^ 13 + (484344472921 / 19200000) * t ^ 15 + (-330454816561 / 57600000) * t ^ 17 + (-681553625833 / 691200000) * t ^ 19 + (325278440327 / 460800000) * t ^ 21 + (104110038773 / 1382400000) * t ^ 25 + (-715295 / 48) * d * t + (6794841 / 160) * d * t ^ 3 + (-90918509 / 1920) * d * t ^ 5 + (373826226787 / 11520000) * d * t ^ 7 + (-68594091247 / 3840000) * d * t ^ 9 + (110614899851 / 23040000) * d * t ^ 11 + (5551108073 / 17280000) * d * t ^ 13 + (180789263 / 2880000) * d * t ^ 15 + (35267803 / 1843200) * d * t ^ 17 + (4489197811 / 138240000) * d * t ^ 19 + (-3468011353 / 92160000) * d * t ^ 21 + (31925251 / 55296000) * d * t ^ 25 + (-22174145 / 48) * alpha * t + (144515337 / 160) * alpha * t ^ 3 + (-11884822663 / 48000) * alpha * t ^ 5 + (-1830978460497 / 6400000) * alpha * t ^ 7 + (454415466461 / 19200000) * alpha * t ^ 9 + (9249136969939 / 115200000) * alpha * t ^ 11 + (-646108895971 / 17280000) * alpha * t ^ 13 + (665483284783 / 28800000) * alpha * t ^ 15 + (71599012103 / 25600000) * alpha * t ^ 17 + (-315906081851 / 691200000) * alpha * t ^ 19 + (140751120629 / 460800000) * alpha * t ^ 21 + (32588604547 / 460800000) * alpha * t ^ 25 + (715295 / 48) * alpha * d * t + (-4103271 / 160) * alpha * d * t ^ 3 + (3708311 / 3200) * alpha * d * t ^ 5 + (114595066643 / 11520000) * alpha * d * t ^ 7 + (42931659671 / 11520000) * alpha * d * t ^ 9 + (-65969677381 / 23040000) * alpha * d * t ^ 11 + (-83889322847 / 69120000) * alpha * d * t ^ 13 + (-372332527 / 11520000) * alpha * d * t ^ 15 + (22405291 / 1382400) * alpha * d * t ^ 17 + (2485841647 / 414720000) * alpha * d * t ^ 19 + (-154292621 / 276480000) * alpha * d * t ^ 21 + (-21292003 / 165888000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_01, v31_02, v31_03, v31_10, v31_11, v31_12, v31_13, v31_20, v31_21, v31_22, v31_23, v31_30, v31_31, v31_32, v31_33, v31_40, v31_41, v31_42, v31_43]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_10, phase32_11, phase32_12, phase32_13, phase32_20, phase32_21, phase32_22, phase32_23, phase32_30, phase32_31, phase32_32, phase32_33, phase32_40, phase32_41, phase32_42, phase32_43]
  try simp only [star_one, star_neg]
  linear_combination ((133663 / 40) * t ^ 3 + (-1968251 / 96) * t ^ 5 + (81123765277 / 2880000) * t ^ 7 + (-3319560887 / 360000) * t ^ 9 + (-158323289 / 153600) * t ^ 11 + (-3551616223 / 2880000) * t ^ 13 + (21946462219 / 34560000) * t ^ 15 + (-1273329011 / 6912000) * t ^ 17 + (-8687988973 / 414720000) * t ^ 19 + (10966798097 / 276480000) * t ^ 21 + (99733361 / 55296000) * t ^ 25 + (133663 / 40) * d * t ^ 3 + (-2693831 / 288) * d * t ^ 5 + (76921683931 / 8640000) * d * t ^ 7 + (-14958941849 / 4320000) * d * t ^ 9 + (6159044317 / 6912000) * d * t ^ 11 + (-3476451461 / 12960000) * d * t ^ 13 + (-5311488853 / 103680000) * d * t ^ 15 + (17687093 / 20736000) * d * t ^ 17 + (-4144898993 / 414720000) * d * t ^ 19 + (7715969311 / 829440000) * d * t ^ 21 + (336661 / 19906560) * d * t ^ 25) * alpha_sq
theorem v32_44 (t : ℂ) : (momentPoly 32 z32 4 4).eval t = (22889440 + (-81112066) * t ^ 2 + (6233154609 / 50) * t ^ 4 + (-15293085152759 / 120000) * t ^ 6 + (14878648746228011 / 144000000) * t ^ 8 + (-1773075925981337 / 32000000) * t ^ 10 + (168420250342337 / 11520000) * t ^ 12 + (-155024784986299 / 64000000) * t ^ 14 + (264524525912071 / 288000000) * t ^ 16 + (-5099993050427 / 288000000) * t ^ 18 + (-31787702312051 / 2304000000) * t ^ 20 + (4762395196037 / 1152000000) * t ^ 22 + (5599999130543 / 4608000000) * t ^ 24 + (-11642513001857 / 3456000000) * t ^ 26 + (3192654578261 / 13824000000) * t ^ 32 + (-681614 / 3) * d * t ^ 2 + (6060617 / 15) * d * t ^ 4 + (47827127 / 4800) * d * t ^ 6 + (-84431988623 / 320000) * d * t ^ 8 + (359272547269 / 11520000) * d * t ^ 10 + (483455114353 / 11520000) * d * t ^ 12 + (-319521588203 / 69120000) * d * t ^ 14 + (432533592577 / 69120000) * d * t ^ 16 + (3210143147 / 1382400) * d * t ^ 18 + (-92531504659 / 829440000) * d * t ^ 20 + (2782250723 / 138240000) * d * t ^ 22 + (24443291 / 36864000) * d * t ^ 24 + (626914411 / 27648000) * d * t ^ 26 + (583775 / 2654208) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z32, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v31_00, v31_01, v31_02, v31_03, v31_04, v31_10, v31_11, v31_12, v31_13, v31_14, v31_20, v31_21, v31_22, v31_23, v31_24, v31_30, v31_31, v31_32, v31_33, v31_34, v31_40, v31_41, v31_42, v31_43, v31_44]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_04, phase32_10, phase32_11, phase32_12, phase32_13, phase32_14, phase32_20, phase32_21, phase32_22, phase32_23, phase32_24, phase32_30, phase32_31, phase32_32, phase32_33, phase32_34, phase32_40, phase32_41, phase32_42, phase32_43, phase32_44]
  try simp only [star_one, star_neg]
  linear_combination ((681614 / 9) * t ^ 2 + (-6836461 / 45) * t ^ 4 + (-301366094 / 1125) * t ^ 6 + (40085440174691 / 43200000) * t ^ 8 + (-73121071290887 / 86400000) * t ^ 10 + (27435512899357 / 86400000) * t ^ 12 + (-1716208084649 / 20736000) * t ^ 14 + (6027200514223 / 259200000) * t ^ 16 + (220161909827 / 57600000) * t ^ 18 + (24218402657 / 194400000) * t ^ 20 + (958278532673 / 518400000) * t ^ 22 + (-115804567 / 86400) * t ^ 24 + (-17840879303 / 1555200000) * t ^ 26 + (22230761 / 5184000) * t ^ 32 + (681614 / 9) * d * t ^ 2 + (-6836461 / 45) * d * t ^ 4 + (47173847 / 1000) * d * t ^ 6 + (565147604897 / 14400000) * d * t ^ 8 + (487133456333 / 86400000) * d * t ^ 10 + (-494303707901 / 28800000) * d * t ^ 12 + (119836376459 / 20736000) * d * t ^ 14 + (-346638667889 / 86400000) * d * t ^ 16 + (-251265026137 / 518400000) * d * t ^ 18 + (3795412483 / 48600000) * d * t ^ 20 + (-3145095283 / 57600000) * d * t ^ 22 + (-1310693 / 8640000) * d * t ^ 24 + (-18493860203 / 1555200000) * d * t ^ 26 + (95627 / 3110400) * d * t ^ 32) * alpha_sq
#print axioms v32_00
#print axioms v32_11
#print axioms v32_22
#print axioms v32_33
#print axioms v32_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
noncomputable def z33 : Fin 33 → ℂ := Fin.snoc z32 (r ^ 2 * phiPlus)
theorem v33_00 (t : ℂ) : (momentPoly 33 z33 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00]
  try simp only [phase32_00]
  try simp only [star_one, star_neg]
  ring
theorem v33_01 (t : ℂ) : (momentPoly 33 z33 0 1).eval t = ((1 / 8) * t + (-1 / 24) * d * t + (5 / 8) * alpha * t + (-1 / 24) * alpha * d * t) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_01]
  try simp only [phase32_00, phase32_01]
  try simp only [star_one, star_neg]
  ring
theorem v33_02 (t : ℂ) : (momentPoly 33 z33 0 2).eval t = ((-8611 / 480) * t ^ 2 + (2367 / 160) * t ^ 4 + (5 / 32) * d * t ^ 2 + (-1 / 96) * d * t ^ 4 + (2891 / 480) * alpha * t ^ 2 + (-1861 / 480) * alpha * t ^ 4 + (-17 / 288) * alpha * d * t ^ 2 + (-1 / 288) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_01, v32_02]
  try simp only [phase32_00, phase32_01, phase32_02]
  try simp only [star_one, star_neg]
  linear_combination ((-31 / 1152) * t ^ 2 + (-5 / 192) * d * t ^ 2 + (1 / 1152) * d ^ 2 * t ^ 2) * alpha_sq + ((-1 / 576) * t ^ 2 + (1 / 576) * alpha * t ^ 2) * d_sq
theorem v33_03 (t : ℂ) : (momentPoly 33 z33 0 3).eval t = ((-6037 / 160) * t ^ 3 + (3897 / 160) * t ^ 5 + 1 * t ^ 9 + (1913 / 480) * d * t ^ 3 + (-3391 / 960) * d * t ^ 5 + (47 / 576) * d * t ^ 9 + (-16501 / 800) * alpha * t ^ 3 + (56489 / 4800) * alpha * t ^ 5 + (24817 / 4800) * alpha * t ^ 9 + (145 / 96) * alpha * d * t ^ 3 + (-133 / 96) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_01, v32_02, v32_03]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03]
  try simp only [star_one, star_neg]
  linear_combination ((-99 / 320) * t ^ 3 + (9461 / 7680) * t ^ 5 + (-443 / 1440) * d * t ^ 3 + (153 / 640) * d * t ^ 5 + (1 / 576) * d ^ 2 * t ^ 3 + (1 / 4608) * d ^ 2 * t ^ 5) * alpha_sq + ((-1 / 96) * t ^ 3 + (-1 / 288) * alpha * t ^ 3 + (1 / 1152) * alpha * t ^ 5) * d_sq
theorem v33_04 (t : ℂ) : (momentPoly 33 z33 0 4).eval t = ((11583791 / 24000) * t ^ 4 + (-3485347 / 4000) * t ^ 6 + (91939699 / 192000) * t ^ 8 + (-14803721 / 144000) * t ^ 10 + (2723257 / 192000) * t ^ 16 + (-25913 / 4800) * d * t ^ 4 + (9881 / 2400) * d * t ^ 6 + (-9437 / 7680) * d * t ^ 8 + (22817 / 9600) * d * t ^ 10 + (95 / 4608) * d * t ^ 16 + (-15806749 / 24000) * alpha * t ^ 4 + (12029789 / 12000) * alpha * t ^ 6 + (-68075701 / 192000) * alpha * t ^ 8 + (-2414641 / 144000) * alpha * t ^ 10 + (2024771 / 576000) * alpha * t ^ 16 + (13367 / 1600) * alpha * d * t ^ 4 + (-5189 / 800) * alpha * d * t ^ 6 + (-1043 / 23040) * alpha * d * t ^ 8 + (-68851 / 86400) * alpha * d * t ^ 10 + (-95 / 13824) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_01, v32_02, v32_03, v32_04]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_04]
  try simp only [star_one, star_neg]
  linear_combination ((33007 / 19200) * t ^ 4 + (779671 / 57600) * t ^ 6 + (-26581 / 2048) * t ^ 8 + (-17251 / 172800) * t ^ 10 + (5297 / 3200) * d * t ^ 4 + (-35587 / 28800) * d * t ^ 6 + (1861 / 46080) * d * t ^ 8 + (-24817 / 57600) * d * t ^ 10 + (-49 / 768) * d ^ 2 * t ^ 4 + (401 / 6912) * d ^ 2 * t ^ 6 + (1 / 55296) * d ^ 2 * t ^ 8) * alpha_sq + ((151 / 5760) * t ^ 4 + (-37 / 1920) * t ^ 6 + (1 / 9216) * t ^ 8 + (-47 / 6912) * t ^ 10 + (-1319 / 5760) * alpha * t ^ 4 + (413 / 1920) * alpha * t ^ 6 + (1 / 9216) * alpha * t ^ 8 + (-47 / 6912) * alpha * t ^ 10) * d_sq
theorem v33_10 (t : ℂ) : (momentPoly 33 z33 1 0).eval t = ((1 / 8) * t + (-1 / 24) * d * t + (-5 / 8) * alpha * t + (1 / 24) * alpha * d * t) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_10]
  try simp only [phase32_00, phase32_10]
  try simp only [star_one, star_neg]
  ring
theorem v33_11 (t : ℂ) : (momentPoly 33 z33 1 1).eval t = (33 + (-167 / 6) * t ^ 2 + (-1 / 6) * d * t ^ 2) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_01, v32_10, v32_11]
  try simp only [phase32_00, phase32_01, phase32_10, phase32_11]
  try simp only [star_one, star_neg]
  linear_combination ((31 / 1152) * t ^ 2 + (5 / 192) * d * t ^ 2 + (-1 / 1152) * d ^ 2 * t ^ 2) * alpha_sq + ((1 / 288) * t ^ 2) * d_sq
theorem v33_12 (t : ℂ) : (momentPoly 33 z33 1 2).eval t = ((65 / 8) * t + (743 / 480) * t ^ 3 + (-2423 / 480) * t ^ 5 + (-65 / 24) * d * t + (3701 / 1440) * d * t ^ 3 + (-47 / 480) * d * t ^ 5 + (325 / 8) * alpha * t + (-32969 / 1440) * alpha * t ^ 3 + (-15151 / 1440) * alpha * t ^ 5 + (-65 / 24) * alpha * d * t + (2251 / 1440) * alpha * d * t ^ 3 + (1189 / 1440) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_01, v32_02, v32_10, v32_11, v32_12]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_10, phase32_11, phase32_12]
  try simp only [star_one, star_neg]
  linear_combination ((33 / 320) * t ^ 3 + (-9461 / 23040) * t ^ 5 + (443 / 4320) * d * t ^ 3 + (-51 / 640) * d * t ^ 5 + (-1 / 1728) * d ^ 2 * t ^ 3 + (-1 / 13824) * d ^ 2 * t ^ 5) * alpha_sq + ((1 / 288) * t ^ 3 + (1 / 2304) * t ^ 5 + (5 / 864) * alpha * t ^ 3 + (-1 / 6912) * alpha * t ^ 5) * d_sq
theorem v33_13 (t : ℂ) : (momentPoly 33 z33 1 3).eval t = ((-8611 / 5) * t ^ 2 + (2742383 / 960) * t ^ 4 + (-2222797 / 1920) * t ^ 6 + (-7975 / 1152) * t ^ 10 + 15 * d * t ^ 2 + (-38693 / 4800) * d * t ^ 4 + (-47941 / 9600) * d * t ^ 6 + (-19219 / 28800) * d * t ^ 10 + (2891 / 5) * alpha * t ^ 2 + (-4109347 / 4800) * alpha * t ^ 4 + (2775581 / 9600) * alpha * t ^ 6 + (168379 / 28800) * alpha * t ^ 10 + (-17 / 3) * alpha * d * t ^ 2 + (30787 / 14400) * alpha * d * t ^ 4 + (88399 / 28800) * alpha * d * t ^ 6 + (-6373 / 28800) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_01, v32_02, v32_03, v32_10, v32_11, v32_12, v32_13]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_10, phase32_11, phase32_12, phase32_13]
  try simp only [star_one, star_neg]
  linear_combination ((-31 / 12) * t ^ 2 + (16423 / 12800) * t ^ 4 + (111397 / 115200) * t ^ 6 + (17251 / 691200) * t ^ 10 + (-5 / 2) * d * t ^ 2 + (24007 / 19200) * d * t ^ 4 + (26653 / 28800) * d * t ^ 6 + (24817 / 230400) * d * t ^ 10 + (1 / 12) * d ^ 2 * t ^ 2 + (-251 / 7680) * d ^ 2 * t ^ 4 + (-319 / 7680) * d ^ 2 * t ^ 6) * alpha_sq + ((-1 / 6) * t ^ 2 + (-137 / 5760) * t ^ 4 + (481 / 2880) * t ^ 6 + (-47 / 27648) * t ^ 10 + (1 / 6) * alpha * t ^ 2 + (-299 / 2880) * alpha * t ^ 4 + (-287 / 5760) * alpha * t ^ 6 + (47 / 27648) * alpha * t ^ 10) * d_sq
theorem v33_14 (t : ℂ) : (momentPoly 33 z33 1 4).eval t = ((-380331 / 80) * t ^ 3 + (574564853 / 96000) * t ^ 5 + (-31524853 / 48000) * t ^ 7 + (-31493009 / 64000) * t ^ 9 + (-29438567 / 144000) * t ^ 11 + (1413889 / 192000) * t ^ 17 + (40173 / 80) * d * t ^ 3 + (-245036957 / 288000) * d * t ^ 5 + (15045119 / 48000) * d * t ^ 7 + (24030763 / 576000) * d * t ^ 9 + (-238577 / 432000) * d * t ^ 11 + (-646441 / 576000) * d * t ^ 17 + (-1039563 / 400) * alpha * t ^ 3 + (939265549 / 288000) * alpha * t ^ 5 + (-6599861 / 16000) * alpha * t ^ 7 + (156418889 / 576000) * alpha * t ^ 9 + (-233085931 / 432000) * alpha * t ^ 11 + (-22359089 / 1728000) * alpha * t ^ 17 + (3045 / 16) * alpha * d * t ^ 3 + (-17607647 / 57600) * alpha * d * t ^ 5 + (2340559 / 28800) * alpha * d * t ^ 7 + (293827 / 7680) * alpha * d * t ^ 9 + (-95693 / 28800) * alpha * d * t ^ 11 + (1985 / 4608) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_01, v32_02, v32_03, v32_04, v32_10, v32_11, v32_12, v32_13, v32_14]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_04, phase32_10, phase32_11, phase32_12, phase32_13, phase32_14]
  try simp only [star_one, star_neg]
  linear_combination ((-6237 / 160) * t ^ 3 + (51945229 / 288000) * t ^ 5 + (-105843257 / 1152000) * t ^ 7 + (-23482661 / 576000) * t ^ 9 + (-72439 / 108000) * t ^ 11 + (10858771 / 27648000) * t ^ 17 + (-3101 / 80) * d * t ^ 3 + (5825539 / 108000) * d * t ^ 5 + (-2342983 / 288000) * d * t ^ 7 + (-12448283 / 1728000) * d * t ^ 9 + (-867893 / 1296000) * d * t ^ 11 + (1042073 / 13824000) * d * t ^ 17 + (7 / 32) * d ^ 2 * t ^ 3 + (55 / 2304) * d ^ 2 * t ^ 5 + (-677 / 3072) * d ^ 2 * t ^ 7 + (-11 / 2304) * d ^ 2 * t ^ 9 + (11 / 10368) * d ^ 2 * t ^ 11 + (-95 / 663552) * d ^ 2 * t ^ 17) * alpha_sq + ((-21 / 16) * t ^ 3 + (1193 / 2880) * t ^ 5 + (18041 / 23040) * t ^ 7 + (11 / 384) * t ^ 9 + (-23 / 1728) * t ^ 11 + (-7 / 16) * alpha * t ^ 3 + (8453 / 43200) * alpha * t ^ 5 + (19933 / 115200) * alpha * t ^ 7 + (-457 / 17280) * alpha * t ^ 9 + (17719 / 259200) * alpha * t ^ 11 + (95 / 165888) * alpha * t ^ 17) * d_sq
theorem v33_20 (t : ℂ) : (momentPoly 33 z33 2 0).eval t = ((-8611 / 480) * t ^ 2 + (2367 / 160) * t ^ 4 + (5 / 32) * d * t ^ 2 + (-1 / 96) * d * t ^ 4 + (-2891 / 480) * alpha * t ^ 2 + (1861 / 480) * alpha * t ^ 4 + (17 / 288) * alpha * d * t ^ 2 + (1 / 288) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_10, v32_20]
  try simp only [phase32_00, phase32_10, phase32_20]
  try simp only [star_one, star_neg]
  linear_combination ((-31 / 1152) * t ^ 2 + (-5 / 192) * d * t ^ 2 + (1 / 1152) * d ^ 2 * t ^ 2) * alpha_sq + ((-1 / 576) * t ^ 2 + (-1 / 576) * alpha * t ^ 2) * d_sq
theorem v33_21 (t : ℂ) : (momentPoly 33 z33 2 1).eval t = ((65 / 8) * t + (743 / 480) * t ^ 3 + (-2423 / 480) * t ^ 5 + (-65 / 24) * d * t + (3701 / 1440) * d * t ^ 3 + (-47 / 480) * d * t ^ 5 + (-325 / 8) * alpha * t + (32969 / 1440) * alpha * t ^ 3 + (15151 / 1440) * alpha * t ^ 5 + (65 / 24) * alpha * d * t + (-2251 / 1440) * alpha * d * t ^ 3 + (-1189 / 1440) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_01, v32_10, v32_11, v32_20, v32_21]
  try simp only [phase32_00, phase32_01, phase32_10, phase32_11, phase32_20, phase32_21]
  try simp only [star_one, star_neg]
  linear_combination ((33 / 320) * t ^ 3 + (-9461 / 23040) * t ^ 5 + (443 / 4320) * d * t ^ 3 + (-51 / 640) * d * t ^ 5 + (-1 / 1728) * d ^ 2 * t ^ 3 + (-1 / 13824) * d ^ 2 * t ^ 5) * alpha_sq + ((1 / 288) * t ^ 3 + (1 / 2304) * t ^ 5 + (-5 / 864) * alpha * t ^ 3 + (1 / 6912) * alpha * t ^ 5) * d_sq
theorem v33_22 (t : ℂ) : (momentPoly 33 z33 2 2).eval t = (2145 + (-10688 / 3) * t ^ 2 + (8591843 / 4800) * t ^ 4 + (-1009301 / 1800) * t ^ 6 + (3326879 / 14400) * t ^ 8 + (-64 / 3) * d * t ^ 2 + (37231 / 2880) * d * t ^ 4 + (311 / 45) * d * t ^ 6 + (-131 / 576) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_01, v32_02, v32_10, v32_11, v32_12, v32_20, v32_21, v32_22]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_10, phase32_11, phase32_12, phase32_20, phase32_21, phase32_22]
  try simp only [star_one, star_neg]
  linear_combination ((31 / 9) * t ^ 2 + (-26309 / 11520) * t ^ 4 + (-22277 / 3840) * t ^ 6 + (26581 / 6144) * t ^ 8 + (10 / 3) * d * t ^ 2 + (-12781 / 5760) * d * t ^ 4 + (-947 / 1152) * d * t ^ 6 + (-1861 / 138240) * d * t ^ 8 + (-1 / 9) * d ^ 2 * t ^ 2 + (83 / 1280) * d ^ 2 * t ^ 4 + (3737 / 103680) * d ^ 2 * t ^ 6 + (-1 / 165888) * d ^ 2 * t ^ 8) * alpha_sq + ((4 / 9) * t ^ 2 + (-1739 / 5760) * t ^ 4 + (-1843 / 17280) * t ^ 6 + (1 / 13824) * t ^ 8) * d_sq
theorem v33_23 (t : ℂ) : (momentPoly 33 z33 2 3).eval t = ((6241 / 8) * t + (46809 / 160) * t ^ 3 + (-141986447 / 96000) * t ^ 5 + (1151449 / 7680) * t ^ 7 + (49139279 / 192000) * t ^ 9 + (5944381 / 64000) * t ^ 11 + (-26469659 / 576000) * t ^ 13 + (-6241 / 24) * d * t + (77721 / 160) * d * t ^ 3 + (-16115063 / 57600) * d * t ^ 5 + (217951 / 2560) * d * t ^ 7 + (-742447 / 23040) * d * t ^ 9 + (-700633 / 345600) * d * t ^ 11 + (136457 / 115200) * d * t ^ 13 + (31205 / 8) * alpha * t + (-692349 / 160) * alpha * t ^ 3 + (-213459953 / 288000) * alpha * t ^ 5 + (113958001 / 115200) * alpha * t ^ 7 + (139010731 / 576000) * alpha * t ^ 9 + (-129550559 / 1728000) * alpha * t ^ 11 + (138069269 / 1728000) * alpha * t ^ 13 + (-6241 / 24) * alpha * d * t + (47271 / 160) * alpha * d * t ^ 3 + (3904273 / 57600) * alpha * d * t ^ 5 + (-2778721 / 38400) * alpha * d * t ^ 7 + (-251179 / 7680) * alpha * d * t ^ 9 + (-17639 / 13824) * alpha * d * t ^ 11 + (106321 / 345600) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_01, v32_02, v32_03, v32_10, v32_11, v32_12, v32_13, v32_20, v32_21, v32_22, v32_23]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_10, phase32_11, phase32_12, phase32_13, phase32_20, phase32_21, phase32_22, phase32_23]
  try simp only [star_one, star_neg]
  linear_combination ((6237 / 320) * t ^ 3 + (-22037377 / 230400) * t ^ 5 + (30399121 / 460800) * t ^ 7 + (423871 / 46080) * t ^ 9 + (-588581 / 1382400) * t ^ 11 + (-1080521 / 552960) * t ^ 13 + (3101 / 160) * d * t ^ 3 + (-11194847 / 345600) * d * t ^ 5 + (1032203 / 76800) * d * t ^ 7 + (-230359 / 691200) * d * t ^ 9 + (388999 / 2073600) * d * t ^ 11 + (24817 / 2764800) * d * t ^ 13 + (-7 / 64) * d ^ 2 * t ^ 3 + (21637 / 691200) * d ^ 2 * t ^ 5 + (34313 / 460800) * d ^ 2 * t ^ 7 + (73 / 69120) * d ^ 2 * t ^ 9 + (-697 / 153600) * d ^ 2 * t ^ 11) * alpha_sq + ((21 / 32) * t ^ 3 + (-3613 / 12800) * t ^ 5 + (-14519 / 38400) * t ^ 7 + (131 / 9216) * t ^ 9 + (7073 / 230400) * t ^ 11 + (-47 / 110592) * t ^ 13 + (35 / 32) * alpha * t ^ 3 + (-219443 / 345600) * alpha * t ^ 5 + (-140633 / 345600) * alpha * t ^ 7 + (397 / 27648) * alpha * t ^ 9 + (-16619 / 2073600) * alpha * t ^ 11 + (47 / 331776) * alpha * t ^ 13) * d_sq
theorem v33_24 (t : ℂ) : (momentPoly 33 z33 2 4).eval t = ((-5209655 / 24) * t ^ 2 + (256952489 / 480) * t ^ 4 + (-282692368571 / 640000) * t ^ 6 + (272448695609 / 1920000) * t ^ 8 + (-33051977687 / 1152000) * t ^ 10 + (4041720311 / 360000) * t ^ 12 + (-1334658487 / 1080000) * t ^ 14 + (-1508060639 / 8640000) * t ^ 18 + (2662274383 / 17280000) * t ^ 20 + (15125 / 8) * d * t ^ 2 + (-4505357 / 2400) * d * t ^ 4 + (-353261611 / 384000) * d * t ^ 6 + (736306441 / 1152000) * d * t ^ 8 + (8593117 / 64000) * d * t ^ 10 + (36250939 / 384000) * d * t ^ 12 + (41230069 / 864000) * d * t ^ 14 + (8413073 / 3456000) * d * t ^ 18 + (121523 / 576000) * d * t ^ 20 + (1749055 / 24) * alpha * t ^ 2 + (-400662613 / 2400) * alpha * t ^ 4 + (726335734429 / 5760000) * alpha * t ^ 6 + (-237009388597 / 5760000) * alpha * t ^ 8 + (4971161359 / 384000) * alpha * t ^ 10 + (-12726128167 / 4320000) * alpha * t ^ 12 + (-10269559 / 15000) * alpha * t ^ 14 + (-153695509 / 960000) * alpha * t ^ 18 + (1917278747 / 17280000) * alpha * t ^ 20 + (-51425 / 72) * alpha * d * t ^ 2 + (4110163 / 7200) * alpha * d * t ^ 4 + (2288631289 / 3456000) * alpha * d * t ^ 6 + (-1323779393 / 3456000) * alpha * d * t ^ 8 + (-34907821 / 192000) * alpha * d * t ^ 10 + (27277331 / 691200) * alpha * d * t ^ 12 + (-4238021 / 2592000) * alpha * d * t ^ 14 + (18954407 / 10368000) * alpha * d * t ^ 18 + (-9727 / 1728000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_01, v32_02, v32_03, v32_04, v32_10, v32_11, v32_12, v32_13, v32_14, v32_20, v32_21, v32_22, v32_23, v32_24]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_04, phase32_10, phase32_11, phase32_12, phase32_13, phase32_14, phase32_20, phase32_21, phase32_22, phase32_23, phase32_24]
  try simp only [star_one, star_neg]
  linear_combination ((-93775 / 288) * t ^ 2 + (509113 / 1600) * t ^ 4 + (828864491 / 4608000) * t ^ 6 + (855741569 / 6912000) * t ^ 8 + (-864983173 / 1728000) * t ^ 10 + (221431783 / 1105920) * t ^ 12 + (38735257 / 6912000) * t ^ 14 + (49346783 / 27648000) * t ^ 18 + (-10006801 / 2457600) * t ^ 20 + (-15125 / 48) * d * t ^ 2 + (744217 / 2400) * d * t ^ 4 + (1178138689 / 6912000) * d * t ^ 6 + (-154392463 / 1152000) * d * t ^ 8 + (-49280153 / 6912000) * d * t ^ 10 + (-260449687 / 13824000) * d * t ^ 12 + (-70572949 / 10368000) * d * t ^ 14 + (-23843063 / 41472000) * d * t ^ 18 + (-24949 / 3456000) * d * t ^ 20 + (3025 / 288) * d ^ 2 * t ^ 2 + (-7781 / 960) * d ^ 2 * t ^ 4 + (-26063219 / 2764800) * d ^ 2 * t ^ 6 + (19756747 / 4147200) * d ^ 2 * t ^ 8 + (818561 / 345600) * d ^ 2 * t ^ 10 + (-261559 / 16588800) * d ^ 2 * t ^ 12 + (-189391 / 12441600) * d ^ 2 * t ^ 14 + (17675 / 1990656) * d ^ 2 * t ^ 18 + (-95 / 7962624) * d ^ 2 * t ^ 20) * alpha_sq + ((-3025 / 144) * t ^ 2 + (-4247 / 720) * t ^ 4 + (44650919 / 768000) * t ^ 6 + (-9536689 / 384000) * t ^ 8 + (-48243427 / 6912000) * t ^ 10 + (4931843 / 13824000) * t ^ 12 + (-16577 / 1036800) * t ^ 14 + (-28901 / 41472000) * t ^ 18 + (-95 / 1327104) * t ^ 20 + (3025 / 144) * alpha * t ^ 2 + (-9269 / 360) * alpha * t ^ 4 + (-23730041 / 6912000) * alpha * t ^ 6 + (17358691 / 3456000) * alpha * t ^ 8 + (7805309 / 2304000) * alpha * t ^ 10 + (2603461 / 41472000) * alpha * t ^ 12 + (-22883 / 172800) * alpha * t ^ 14 + (-470783 / 13824000) * alpha * t ^ 18 + (95 / 1327104) * alpha * t ^ 20) * d_sq
theorem v33_30 (t : ℂ) : (momentPoly 33 z33 3 0).eval t = ((-6037 / 160) * t ^ 3 + (3897 / 160) * t ^ 5 + 1 * t ^ 9 + (1913 / 480) * d * t ^ 3 + (-3391 / 960) * d * t ^ 5 + (47 / 576) * d * t ^ 9 + (16501 / 800) * alpha * t ^ 3 + (-56489 / 4800) * alpha * t ^ 5 + (-24817 / 4800) * alpha * t ^ 9 + (-145 / 96) * alpha * d * t ^ 3 + (133 / 96) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_10, v32_20, v32_30]
  try simp only [phase32_00, phase32_10, phase32_20, phase32_30]
  try simp only [star_one, star_neg]
  linear_combination ((-99 / 320) * t ^ 3 + (9461 / 7680) * t ^ 5 + (-443 / 1440) * d * t ^ 3 + (153 / 640) * d * t ^ 5 + (1 / 576) * d ^ 2 * t ^ 3 + (1 / 4608) * d ^ 2 * t ^ 5) * alpha_sq + ((-1 / 96) * t ^ 3 + (1 / 288) * alpha * t ^ 3 + (-1 / 1152) * alpha * t ^ 5) * d_sq
theorem v33_31 (t : ℂ) : (momentPoly 33 z33 3 1).eval t = ((-8611 / 5) * t ^ 2 + (2742383 / 960) * t ^ 4 + (-2222797 / 1920) * t ^ 6 + (-7975 / 1152) * t ^ 10 + 15 * d * t ^ 2 + (-38693 / 4800) * d * t ^ 4 + (-47941 / 9600) * d * t ^ 6 + (-19219 / 28800) * d * t ^ 10 + (-2891 / 5) * alpha * t ^ 2 + (4109347 / 4800) * alpha * t ^ 4 + (-2775581 / 9600) * alpha * t ^ 6 + (-168379 / 28800) * alpha * t ^ 10 + (17 / 3) * alpha * d * t ^ 2 + (-30787 / 14400) * alpha * d * t ^ 4 + (-88399 / 28800) * alpha * d * t ^ 6 + (6373 / 28800) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_01, v32_10, v32_11, v32_20, v32_21, v32_30, v32_31]
  try simp only [phase32_00, phase32_01, phase32_10, phase32_11, phase32_20, phase32_21, phase32_30, phase32_31]
  try simp only [star_one, star_neg]
  linear_combination ((-31 / 12) * t ^ 2 + (16423 / 12800) * t ^ 4 + (111397 / 115200) * t ^ 6 + (17251 / 691200) * t ^ 10 + (-5 / 2) * d * t ^ 2 + (24007 / 19200) * d * t ^ 4 + (26653 / 28800) * d * t ^ 6 + (24817 / 230400) * d * t ^ 10 + (1 / 12) * d ^ 2 * t ^ 2 + (-251 / 7680) * d ^ 2 * t ^ 4 + (-319 / 7680) * d ^ 2 * t ^ 6) * alpha_sq + ((-1 / 6) * t ^ 2 + (-137 / 5760) * t ^ 4 + (481 / 2880) * t ^ 6 + (-47 / 27648) * t ^ 10 + (-1 / 6) * alpha * t ^ 2 + (299 / 2880) * alpha * t ^ 4 + (287 / 5760) * alpha * t ^ 6 + (-47 / 27648) * alpha * t ^ 10) * d_sq
theorem v33_32 (t : ℂ) : (momentPoly 33 z33 3 2).eval t = ((6241 / 8) * t + (46809 / 160) * t ^ 3 + (-141986447 / 96000) * t ^ 5 + (1151449 / 7680) * t ^ 7 + (49139279 / 192000) * t ^ 9 + (5944381 / 64000) * t ^ 11 + (-26469659 / 576000) * t ^ 13 + (-6241 / 24) * d * t + (77721 / 160) * d * t ^ 3 + (-16115063 / 57600) * d * t ^ 5 + (217951 / 2560) * d * t ^ 7 + (-742447 / 23040) * d * t ^ 9 + (-700633 / 345600) * d * t ^ 11 + (136457 / 115200) * d * t ^ 13 + (-31205 / 8) * alpha * t + (692349 / 160) * alpha * t ^ 3 + (213459953 / 288000) * alpha * t ^ 5 + (-113958001 / 115200) * alpha * t ^ 7 + (-139010731 / 576000) * alpha * t ^ 9 + (129550559 / 1728000) * alpha * t ^ 11 + (-138069269 / 1728000) * alpha * t ^ 13 + (6241 / 24) * alpha * d * t + (-47271 / 160) * alpha * d * t ^ 3 + (-3904273 / 57600) * alpha * d * t ^ 5 + (2778721 / 38400) * alpha * d * t ^ 7 + (251179 / 7680) * alpha * d * t ^ 9 + (17639 / 13824) * alpha * d * t ^ 11 + (-106321 / 345600) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_01, v32_02, v32_10, v32_11, v32_12, v32_20, v32_21, v32_22, v32_30, v32_31, v32_32]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_10, phase32_11, phase32_12, phase32_20, phase32_21, phase32_22, phase32_30, phase32_31, phase32_32]
  try simp only [star_one, star_neg]
  linear_combination ((6237 / 320) * t ^ 3 + (-22037377 / 230400) * t ^ 5 + (30399121 / 460800) * t ^ 7 + (423871 / 46080) * t ^ 9 + (-588581 / 1382400) * t ^ 11 + (-1080521 / 552960) * t ^ 13 + (3101 / 160) * d * t ^ 3 + (-11194847 / 345600) * d * t ^ 5 + (1032203 / 76800) * d * t ^ 7 + (-230359 / 691200) * d * t ^ 9 + (388999 / 2073600) * d * t ^ 11 + (24817 / 2764800) * d * t ^ 13 + (-7 / 64) * d ^ 2 * t ^ 3 + (21637 / 691200) * d ^ 2 * t ^ 5 + (34313 / 460800) * d ^ 2 * t ^ 7 + (73 / 69120) * d ^ 2 * t ^ 9 + (-697 / 153600) * d ^ 2 * t ^ 11) * alpha_sq + ((21 / 32) * t ^ 3 + (-3613 / 12800) * t ^ 5 + (-14519 / 38400) * t ^ 7 + (131 / 9216) * t ^ 9 + (7073 / 230400) * t ^ 11 + (-47 / 110592) * t ^ 13 + (-35 / 32) * alpha * t ^ 3 + (219443 / 345600) * alpha * t ^ 5 + (140633 / 345600) * alpha * t ^ 7 + (-397 / 27648) * alpha * t ^ 9 + (16619 / 2073600) * alpha * t ^ 11 + (-47 / 331776) * alpha * t ^ 13) * d_sq
theorem v33_33 (t : ℂ) : (momentPoly 33 z33 3 3).eval t = (205953 + (-505175) * t ^ 2 + (799041399 / 1600) * t ^ 4 + (-81616412527 / 240000) * t ^ 6 + (15156847167 / 80000) * t ^ 8 + (-15821526571 / 320000) * t ^ 10 + (964462859 / 720000) * t ^ 12 + (-1635434317 / 1440000) * t ^ 14 + (449351347 / 8640000) * t ^ 18 + (-3025) * d * t ^ 2 + (1154161 / 320) * d * t ^ 4 + (2807037 / 3200) * d * t ^ 6 + (-23783197 / 19200) * d * t ^ 8 + (-4236281 / 19200) * d * t ^ 10 + (321811 / 11520) * d * t ^ 12 + (-839089 / 19200) * d * t ^ 14 + (47 / 288) * d * t ^ 18) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_01, v32_02, v32_03, v32_10, v32_11, v32_12, v32_13, v32_20, v32_21, v32_22, v32_23, v32_30, v32_31, v32_32, v32_33]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_10, phase32_11, phase32_12, phase32_13, phase32_20, phase32_21, phase32_22, phase32_23, phase32_30, phase32_31, phase32_32, phase32_33]
  try simp only [star_one, star_neg]
  linear_combination ((93775 / 192) * t ^ 2 + (-815579 / 1280) * t ^ 4 + (-3270952693 / 2304000) * t ^ 6 + (1202959747 / 460800) * t ^ 8 + (-265655513 / 256000) * t ^ 10 + (-7952009 / 2304000) * t ^ 12 + (-46887883 / 6912000) * t ^ 14 + (-20781761 / 16588800) * t ^ 18 + (15125 / 32) * d * t ^ 2 + (-396211 / 640) * d * t ^ 4 + (-24309289 / 1152000) * d * t ^ 6 + (10350823 / 76800) * d * t ^ 8 + (19324207 / 576000) * d * t ^ 10 + (-61106417 / 6912000) * d * t ^ 12 + (24603299 / 2304000) * d * t ^ 14 + (-3025 / 192) * d ^ 2 * t ^ 2 + (23157 / 1280) * d ^ 2 * t ^ 4 + (6355349 / 1382400) * d ^ 2 * t ^ 6 + (-6510643 / 1382400) * d ^ 2 * t ^ 8 + (-1042613 / 460800) * d ^ 2 * t ^ 10 + (-53657 / 691200) * d ^ 2 * t ^ 12 + (7153 / 345600) * d ^ 2 * t ^ 14) * alpha_sq + ((3025 / 48) * t ^ 2 + (-53909 / 640) * t ^ 4 + (115603 / 38400) * t ^ 6 + (176299 / 19200) * t ^ 8 + (700111 / 76800) * t ^ 10 + (714173 / 1382400) * t ^ 12 + (-390617 / 1382400) * t ^ 14 + (2209 / 663552) * t ^ 18) * d_sq
theorem v33_34 (t : ℂ) : (momentPoly 33 z33 3 4).eval t = ((786753 / 8) * t + (2177733 / 40) * t ^ 3 + (-5916156567 / 16000) * t ^ 5 + (1177114856981 / 9600000) * t ^ 7 + (258326507769 / 1600000) * t ^ 9 + (-1440807920251 / 38400000) * t ^ 11 + (-2140827516719 / 46080000) * t ^ 13 + (1312084092103 / 57600000) * t ^ 15 + (-1163006992019 / 230400000) * t ^ 17 + (-13901271697 / 12800000) * t ^ 19 + (137597769991 / 230400000) * t ^ 21 + (48070143349 / 691200000) * t ^ 25 + (-262251 / 8) * d * t + (3615877 / 40) * d * t ^ 3 + (-951071063 / 9600) * d * t ^ 5 + (386557033007 / 5760000) * d * t ^ 7 + (-402008436137 / 11520000) * d * t ^ 9 + (196120036267 / 23040000) * d * t ^ 11 + (78964979273 / 138240000) * d * t ^ 13 + (1237072819 / 11520000) * d * t ^ 15 + (208629673 / 5529600) * d * t ^ 17 + (12526328843 / 207360000) * d * t ^ 19 + (-9360394669 / 138240000) * d * t ^ 21 + (30773251 / 27648000) * d * t ^ 25 + (3933765 / 8) * alpha * t + (-32210713 / 40) * alpha * t ^ 3 + (4143510767 / 48000) * alpha * t ^ 5 + (7748645612509 / 28800000) * alpha * t ^ 7 + (-96170619881 / 19200000) * alpha * t ^ 9 + (-2092705594903 / 38400000) * alpha * t ^ 11 + (643942523069 / 15360000) * alpha * t ^ 13 + (-1206754167121 / 57600000) * alpha * t ^ 15 + (-1914151246631 / 691200000) * alpha * t ^ 17 + (444977467979 / 1036800000) * alpha * t ^ 19 + (-179135948621 / 691200000) * alpha * t ^ 21 + (-146734991299 / 2073600000) * alpha * t ^ 25 + (-262251 / 8) * alpha * d * t + (2199227 / 40) * alpha * d * t ^ 3 + (-31242967 / 9600) * alpha * d * t ^ 5 + (-12504950067 / 640000) * alpha * d * t ^ 7 + (-4802270447 / 720000) * alpha * d * t ^ 9 + (117997183667 / 23040000) * alpha * d * t ^ 11 + (288896687863 / 138240000) * alpha * d * t ^ 13 + (2209065757 / 34560000) * alpha * d * t ^ 15 + (-152493073 / 5529600) * alpha * d * t ^ 17 + (-2747909357 / 207360000) * alpha * d * t ^ 19 + (157751087 / 46080000) * alpha * d * t ^ 21 + (17836003 / 82944000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_01, v32_02, v32_03, v32_04, v32_10, v32_11, v32_12, v32_13, v32_14, v32_20, v32_21, v32_22, v32_23, v32_24, v32_30, v32_31, v32_32, v32_33, v32_34]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_04, phase32_10, phase32_11, phase32_12, phase32_13, phase32_14, phase32_20, phase32_21, phase32_22, phase32_23, phase32_24, phase32_30, phase32_31, phase32_32, phase32_33, phase32_34]
  try simp only [star_one, star_neg]
  linear_combination ((290169 / 80) * t ^ 3 + (-67363471 / 3200) * t ^ 5 + (52575767983 / 1920000) * t ^ 7 + (-237377401949 / 30720000) * t ^ 9 + (-32697429389 / 18432000) * t ^ 11 + (-46934560063 / 46080000) * t ^ 13 + (1510010449 / 2160000) * t ^ 15 + (-20896084801 / 110592000) * t ^ 17 + (-32750582567 / 1658880000) * t ^ 19 + (9869952547 / 276480000) * t ^ 21 + (1275754207 / 663552000) * t ^ 25 + (432811 / 120) * d * t ^ 3 + (-526885337 / 57600) * d * t ^ 5 + (3813476677 / 480000) * d * t ^ 7 + (-69148710463 / 23040000) * d * t ^ 9 + (23262202291 / 27648000) * d * t ^ 11 + (-54634653463 / 276480000) * d * t ^ 13 + (-5897563469 / 138240000) * d * t ^ 15 + (54059119 / 165888000) * d * t ^ 17 + (-22137689653 / 2488320000) * d * t ^ 19 + (3077432333 / 414720000) * d * t ^ 21 + (471523 / 26542080) * d * t ^ 25 + (-977 / 48) * d ^ 2 * t ^ 3 + (801541 / 57600) * d ^ 2 * t ^ 5 + (1938869 / 76800) * d ^ 2 * t ^ 7 + (-148939783 / 11059200) * d ^ 2 * t ^ 9 + (-72524003 / 11059200) * d ^ 2 * t ^ 11 + (2311851 / 2048000) * d ^ 2 * t ^ 13 + (-3407821 / 82944000) * d ^ 2 * t ^ 15 + (120721 / 66355200) * d ^ 2 * t ^ 17 + (6964423 / 110592000) * d ^ 2 * t ^ 19 + (-219931 / 165888000) * d ^ 2 * t ^ 21) * alpha_sq + ((977 / 8) * t ^ 3 + (-1133381 / 9600) * t ^ 5 + (-5049031 / 48000) * t ^ 7 + (50492537 / 576000) * t ^ 9 + (203685173 / 9216000) * t ^ 11 + (-16503023 / 2048000) * t ^ 13 + (3390493 / 27648000) * t ^ 15 + (-563411 / 11059200) * t ^ 17 + (-28571 / 108000) * t ^ 19 + (-359513 / 27648000) * t ^ 21 + (4465 / 5308416) * t ^ 25 + (4885 / 24) * alpha * t ^ 3 + (-6551399 / 28800) * alpha * t ^ 5 + (-159226549 / 1728000) * alpha * t ^ 7 + (84002417 / 921600) * alpha * t ^ 9 + (208073213 / 9216000) * alpha * t ^ 11 + (-265919 / 6144000) * alpha * t ^ 13 + (80925419 / 27648000) * alpha * t ^ 15 + (-47489 / 33177600) * alpha * t ^ 17 + (669277 / 248832000) * alpha * t ^ 19 + (1170763 / 82944000) * alpha * t ^ 21 + (-4465 / 15925248) * alpha * t ^ 25) * d_sq
theorem v33_40 (t : ℂ) : (momentPoly 33 z33 4 0).eval t = ((11583791 / 24000) * t ^ 4 + (-3485347 / 4000) * t ^ 6 + (91939699 / 192000) * t ^ 8 + (-14803721 / 144000) * t ^ 10 + (2723257 / 192000) * t ^ 16 + (-25913 / 4800) * d * t ^ 4 + (9881 / 2400) * d * t ^ 6 + (-9437 / 7680) * d * t ^ 8 + (22817 / 9600) * d * t ^ 10 + (95 / 4608) * d * t ^ 16 + (15806749 / 24000) * alpha * t ^ 4 + (-12029789 / 12000) * alpha * t ^ 6 + (68075701 / 192000) * alpha * t ^ 8 + (2414641 / 144000) * alpha * t ^ 10 + (-2024771 / 576000) * alpha * t ^ 16 + (-13367 / 1600) * alpha * d * t ^ 4 + (5189 / 800) * alpha * d * t ^ 6 + (1043 / 23040) * alpha * d * t ^ 8 + (68851 / 86400) * alpha * d * t ^ 10 + (95 / 13824) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_10, v32_20, v32_30, v32_40]
  try simp only [phase32_00, phase32_10, phase32_20, phase32_30, phase32_40]
  try simp only [star_one, star_neg]
  linear_combination ((33007 / 19200) * t ^ 4 + (779671 / 57600) * t ^ 6 + (-26581 / 2048) * t ^ 8 + (-17251 / 172800) * t ^ 10 + (5297 / 3200) * d * t ^ 4 + (-35587 / 28800) * d * t ^ 6 + (1861 / 46080) * d * t ^ 8 + (-24817 / 57600) * d * t ^ 10 + (-49 / 768) * d ^ 2 * t ^ 4 + (401 / 6912) * d ^ 2 * t ^ 6 + (1 / 55296) * d ^ 2 * t ^ 8) * alpha_sq + ((151 / 5760) * t ^ 4 + (-37 / 1920) * t ^ 6 + (1 / 9216) * t ^ 8 + (-47 / 6912) * t ^ 10 + (1319 / 5760) * alpha * t ^ 4 + (-413 / 1920) * alpha * t ^ 6 + (-1 / 9216) * alpha * t ^ 8 + (47 / 6912) * alpha * t ^ 10) * d_sq
theorem v33_41 (t : ℂ) : (momentPoly 33 z33 4 1).eval t = ((-380331 / 80) * t ^ 3 + (574564853 / 96000) * t ^ 5 + (-31524853 / 48000) * t ^ 7 + (-31493009 / 64000) * t ^ 9 + (-29438567 / 144000) * t ^ 11 + (1413889 / 192000) * t ^ 17 + (40173 / 80) * d * t ^ 3 + (-245036957 / 288000) * d * t ^ 5 + (15045119 / 48000) * d * t ^ 7 + (24030763 / 576000) * d * t ^ 9 + (-238577 / 432000) * d * t ^ 11 + (-646441 / 576000) * d * t ^ 17 + (1039563 / 400) * alpha * t ^ 3 + (-939265549 / 288000) * alpha * t ^ 5 + (6599861 / 16000) * alpha * t ^ 7 + (-156418889 / 576000) * alpha * t ^ 9 + (233085931 / 432000) * alpha * t ^ 11 + (22359089 / 1728000) * alpha * t ^ 17 + (-3045 / 16) * alpha * d * t ^ 3 + (17607647 / 57600) * alpha * d * t ^ 5 + (-2340559 / 28800) * alpha * d * t ^ 7 + (-293827 / 7680) * alpha * d * t ^ 9 + (95693 / 28800) * alpha * d * t ^ 11 + (-1985 / 4608) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_01, v32_10, v32_11, v32_20, v32_21, v32_30, v32_31, v32_40, v32_41]
  try simp only [phase32_00, phase32_01, phase32_10, phase32_11, phase32_20, phase32_21, phase32_30, phase32_31, phase32_40, phase32_41]
  try simp only [star_one, star_neg]
  linear_combination ((-6237 / 160) * t ^ 3 + (51945229 / 288000) * t ^ 5 + (-105843257 / 1152000) * t ^ 7 + (-23482661 / 576000) * t ^ 9 + (-72439 / 108000) * t ^ 11 + (10858771 / 27648000) * t ^ 17 + (-3101 / 80) * d * t ^ 3 + (5825539 / 108000) * d * t ^ 5 + (-2342983 / 288000) * d * t ^ 7 + (-12448283 / 1728000) * d * t ^ 9 + (-867893 / 1296000) * d * t ^ 11 + (1042073 / 13824000) * d * t ^ 17 + (7 / 32) * d ^ 2 * t ^ 3 + (55 / 2304) * d ^ 2 * t ^ 5 + (-677 / 3072) * d ^ 2 * t ^ 7 + (-11 / 2304) * d ^ 2 * t ^ 9 + (11 / 10368) * d ^ 2 * t ^ 11 + (-95 / 663552) * d ^ 2 * t ^ 17) * alpha_sq + ((-21 / 16) * t ^ 3 + (1193 / 2880) * t ^ 5 + (18041 / 23040) * t ^ 7 + (11 / 384) * t ^ 9 + (-23 / 1728) * t ^ 11 + (7 / 16) * alpha * t ^ 3 + (-8453 / 43200) * alpha * t ^ 5 + (-19933 / 115200) * alpha * t ^ 7 + (457 / 17280) * alpha * t ^ 9 + (-17719 / 259200) * alpha * t ^ 11 + (-95 / 165888) * alpha * t ^ 17) * d_sq
theorem v33_42 (t : ℂ) : (momentPoly 33 z33 4 2).eval t = ((-5209655 / 24) * t ^ 2 + (256952489 / 480) * t ^ 4 + (-282692368571 / 640000) * t ^ 6 + (272448695609 / 1920000) * t ^ 8 + (-33051977687 / 1152000) * t ^ 10 + (4041720311 / 360000) * t ^ 12 + (-1334658487 / 1080000) * t ^ 14 + (-1508060639 / 8640000) * t ^ 18 + (2662274383 / 17280000) * t ^ 20 + (15125 / 8) * d * t ^ 2 + (-4505357 / 2400) * d * t ^ 4 + (-353261611 / 384000) * d * t ^ 6 + (736306441 / 1152000) * d * t ^ 8 + (8593117 / 64000) * d * t ^ 10 + (36250939 / 384000) * d * t ^ 12 + (41230069 / 864000) * d * t ^ 14 + (8413073 / 3456000) * d * t ^ 18 + (121523 / 576000) * d * t ^ 20 + (-1749055 / 24) * alpha * t ^ 2 + (400662613 / 2400) * alpha * t ^ 4 + (-726335734429 / 5760000) * alpha * t ^ 6 + (237009388597 / 5760000) * alpha * t ^ 8 + (-4971161359 / 384000) * alpha * t ^ 10 + (12726128167 / 4320000) * alpha * t ^ 12 + (10269559 / 15000) * alpha * t ^ 14 + (153695509 / 960000) * alpha * t ^ 18 + (-1917278747 / 17280000) * alpha * t ^ 20 + (51425 / 72) * alpha * d * t ^ 2 + (-4110163 / 7200) * alpha * d * t ^ 4 + (-2288631289 / 3456000) * alpha * d * t ^ 6 + (1323779393 / 3456000) * alpha * d * t ^ 8 + (34907821 / 192000) * alpha * d * t ^ 10 + (-27277331 / 691200) * alpha * d * t ^ 12 + (4238021 / 2592000) * alpha * d * t ^ 14 + (-18954407 / 10368000) * alpha * d * t ^ 18 + (9727 / 1728000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_01, v32_02, v32_10, v32_11, v32_12, v32_20, v32_21, v32_22, v32_30, v32_31, v32_32, v32_40, v32_41, v32_42]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_10, phase32_11, phase32_12, phase32_20, phase32_21, phase32_22, phase32_30, phase32_31, phase32_32, phase32_40, phase32_41, phase32_42]
  try simp only [star_one, star_neg]
  linear_combination ((-93775 / 288) * t ^ 2 + (509113 / 1600) * t ^ 4 + (828864491 / 4608000) * t ^ 6 + (855741569 / 6912000) * t ^ 8 + (-864983173 / 1728000) * t ^ 10 + (221431783 / 1105920) * t ^ 12 + (38735257 / 6912000) * t ^ 14 + (49346783 / 27648000) * t ^ 18 + (-10006801 / 2457600) * t ^ 20 + (-15125 / 48) * d * t ^ 2 + (744217 / 2400) * d * t ^ 4 + (1178138689 / 6912000) * d * t ^ 6 + (-154392463 / 1152000) * d * t ^ 8 + (-49280153 / 6912000) * d * t ^ 10 + (-260449687 / 13824000) * d * t ^ 12 + (-70572949 / 10368000) * d * t ^ 14 + (-23843063 / 41472000) * d * t ^ 18 + (-24949 / 3456000) * d * t ^ 20 + (3025 / 288) * d ^ 2 * t ^ 2 + (-7781 / 960) * d ^ 2 * t ^ 4 + (-26063219 / 2764800) * d ^ 2 * t ^ 6 + (19756747 / 4147200) * d ^ 2 * t ^ 8 + (818561 / 345600) * d ^ 2 * t ^ 10 + (-261559 / 16588800) * d ^ 2 * t ^ 12 + (-189391 / 12441600) * d ^ 2 * t ^ 14 + (17675 / 1990656) * d ^ 2 * t ^ 18 + (-95 / 7962624) * d ^ 2 * t ^ 20) * alpha_sq + ((-3025 / 144) * t ^ 2 + (-4247 / 720) * t ^ 4 + (44650919 / 768000) * t ^ 6 + (-9536689 / 384000) * t ^ 8 + (-48243427 / 6912000) * t ^ 10 + (4931843 / 13824000) * t ^ 12 + (-16577 / 1036800) * t ^ 14 + (-28901 / 41472000) * t ^ 18 + (-95 / 1327104) * t ^ 20 + (-3025 / 144) * alpha * t ^ 2 + (9269 / 360) * alpha * t ^ 4 + (23730041 / 6912000) * alpha * t ^ 6 + (-17358691 / 3456000) * alpha * t ^ 8 + (-7805309 / 2304000) * alpha * t ^ 10 + (-2603461 / 41472000) * alpha * t ^ 12 + (22883 / 172800) * alpha * t ^ 14 + (470783 / 13824000) * alpha * t ^ 18 + (-95 / 1327104) * alpha * t ^ 20) * d_sq
theorem v33_43 (t : ℂ) : (momentPoly 33 z33 4 3).eval t = ((786753 / 8) * t + (2177733 / 40) * t ^ 3 + (-5916156567 / 16000) * t ^ 5 + (1177114856981 / 9600000) * t ^ 7 + (258326507769 / 1600000) * t ^ 9 + (-1440807920251 / 38400000) * t ^ 11 + (-2140827516719 / 46080000) * t ^ 13 + (1312084092103 / 57600000) * t ^ 15 + (-1163006992019 / 230400000) * t ^ 17 + (-13901271697 / 12800000) * t ^ 19 + (137597769991 / 230400000) * t ^ 21 + (48070143349 / 691200000) * t ^ 25 + (-262251 / 8) * d * t + (3615877 / 40) * d * t ^ 3 + (-951071063 / 9600) * d * t ^ 5 + (386557033007 / 5760000) * d * t ^ 7 + (-402008436137 / 11520000) * d * t ^ 9 + (196120036267 / 23040000) * d * t ^ 11 + (78964979273 / 138240000) * d * t ^ 13 + (1237072819 / 11520000) * d * t ^ 15 + (208629673 / 5529600) * d * t ^ 17 + (12526328843 / 207360000) * d * t ^ 19 + (-9360394669 / 138240000) * d * t ^ 21 + (30773251 / 27648000) * d * t ^ 25 + (-3933765 / 8) * alpha * t + (32210713 / 40) * alpha * t ^ 3 + (-4143510767 / 48000) * alpha * t ^ 5 + (-7748645612509 / 28800000) * alpha * t ^ 7 + (96170619881 / 19200000) * alpha * t ^ 9 + (2092705594903 / 38400000) * alpha * t ^ 11 + (-643942523069 / 15360000) * alpha * t ^ 13 + (1206754167121 / 57600000) * alpha * t ^ 15 + (1914151246631 / 691200000) * alpha * t ^ 17 + (-444977467979 / 1036800000) * alpha * t ^ 19 + (179135948621 / 691200000) * alpha * t ^ 21 + (146734991299 / 2073600000) * alpha * t ^ 25 + (262251 / 8) * alpha * d * t + (-2199227 / 40) * alpha * d * t ^ 3 + (31242967 / 9600) * alpha * d * t ^ 5 + (12504950067 / 640000) * alpha * d * t ^ 7 + (4802270447 / 720000) * alpha * d * t ^ 9 + (-117997183667 / 23040000) * alpha * d * t ^ 11 + (-288896687863 / 138240000) * alpha * d * t ^ 13 + (-2209065757 / 34560000) * alpha * d * t ^ 15 + (152493073 / 5529600) * alpha * d * t ^ 17 + (2747909357 / 207360000) * alpha * d * t ^ 19 + (-157751087 / 46080000) * alpha * d * t ^ 21 + (-17836003 / 82944000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_01, v32_02, v32_03, v32_10, v32_11, v32_12, v32_13, v32_20, v32_21, v32_22, v32_23, v32_30, v32_31, v32_32, v32_33, v32_40, v32_41, v32_42, v32_43]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_10, phase32_11, phase32_12, phase32_13, phase32_20, phase32_21, phase32_22, phase32_23, phase32_30, phase32_31, phase32_32, phase32_33, phase32_40, phase32_41, phase32_42, phase32_43]
  try simp only [star_one, star_neg]
  linear_combination ((290169 / 80) * t ^ 3 + (-67363471 / 3200) * t ^ 5 + (52575767983 / 1920000) * t ^ 7 + (-237377401949 / 30720000) * t ^ 9 + (-32697429389 / 18432000) * t ^ 11 + (-46934560063 / 46080000) * t ^ 13 + (1510010449 / 2160000) * t ^ 15 + (-20896084801 / 110592000) * t ^ 17 + (-32750582567 / 1658880000) * t ^ 19 + (9869952547 / 276480000) * t ^ 21 + (1275754207 / 663552000) * t ^ 25 + (432811 / 120) * d * t ^ 3 + (-526885337 / 57600) * d * t ^ 5 + (3813476677 / 480000) * d * t ^ 7 + (-69148710463 / 23040000) * d * t ^ 9 + (23262202291 / 27648000) * d * t ^ 11 + (-54634653463 / 276480000) * d * t ^ 13 + (-5897563469 / 138240000) * d * t ^ 15 + (54059119 / 165888000) * d * t ^ 17 + (-22137689653 / 2488320000) * d * t ^ 19 + (3077432333 / 414720000) * d * t ^ 21 + (471523 / 26542080) * d * t ^ 25 + (-977 / 48) * d ^ 2 * t ^ 3 + (801541 / 57600) * d ^ 2 * t ^ 5 + (1938869 / 76800) * d ^ 2 * t ^ 7 + (-148939783 / 11059200) * d ^ 2 * t ^ 9 + (-72524003 / 11059200) * d ^ 2 * t ^ 11 + (2311851 / 2048000) * d ^ 2 * t ^ 13 + (-3407821 / 82944000) * d ^ 2 * t ^ 15 + (120721 / 66355200) * d ^ 2 * t ^ 17 + (6964423 / 110592000) * d ^ 2 * t ^ 19 + (-219931 / 165888000) * d ^ 2 * t ^ 21) * alpha_sq + ((977 / 8) * t ^ 3 + (-1133381 / 9600) * t ^ 5 + (-5049031 / 48000) * t ^ 7 + (50492537 / 576000) * t ^ 9 + (203685173 / 9216000) * t ^ 11 + (-16503023 / 2048000) * t ^ 13 + (3390493 / 27648000) * t ^ 15 + (-563411 / 11059200) * t ^ 17 + (-28571 / 108000) * t ^ 19 + (-359513 / 27648000) * t ^ 21 + (4465 / 5308416) * t ^ 25 + (-4885 / 24) * alpha * t ^ 3 + (6551399 / 28800) * alpha * t ^ 5 + (159226549 / 1728000) * alpha * t ^ 7 + (-84002417 / 921600) * alpha * t ^ 9 + (-208073213 / 9216000) * alpha * t ^ 11 + (265919 / 6144000) * alpha * t ^ 13 + (-80925419 / 27648000) * alpha * t ^ 15 + (47489 / 33177600) * alpha * t ^ 17 + (-669277 / 248832000) * alpha * t ^ 19 + (-1170763 / 82944000) * alpha * t ^ 21 + (4465 / 15925248) * alpha * t ^ 25) * d_sq
theorem v33_44 (t : ℂ) : (momentPoly 33 z33 4 4).eval t = (25962849 + (-83592852) * t ^ 2 + (48775892711 / 400) * t ^ 4 + (-47383624069 / 375) * t ^ 6 + (7238386242291373 / 72000000) * t ^ 8 + (-193167951574399 / 4000000) * t ^ 10 + (2663897209390151 / 230400000) * t ^ 12 + (-4388452241910923 / 1728000000) * t ^ 14 + (625458422808491 / 768000000) * t ^ 16 + (-1527821246299 / 96000000) * t ^ 18 + (-57604451796149 / 3456000000) * t ^ 20 + (2640391468591 / 576000000) * t ^ 22 + (5711387685563 / 1728000000) * t ^ 24 + (-4391290960057 / 1296000000) * t ^ 26 + (4262711183579 / 20736000000) * t ^ 32 + (-500556) * d * t ^ 2 + (211360387 / 240) * d * t ^ 4 + (-401527 / 12) * d * t ^ 6 + (-931966480171 / 1920000) * d * t ^ 8 + (89435891221 / 1440000) * d * t ^ 10 + (1162665272713 / 15360000) * d * t ^ 12 + (-1140681406811 / 69120000) * d * t ^ 14 + (132353279533 / 10240000) * d * t ^ 16 + (6224557961 / 1382400) * d * t ^ 18 + (-87789598279 / 414720000) * d * t ^ 20 + (2492988653 / 69120000) * d * t ^ 22 + (17711437 / 13824000) * d * t ^ 24 + (488284777 / 10368000) * d * t ^ 26 + (583775 / 1327104) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z33, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v32_00, v32_01, v32_02, v32_03, v32_04, v32_10, v32_11, v32_12, v32_13, v32_14, v32_20, v32_21, v32_22, v32_23, v32_24, v32_30, v32_31, v32_32, v32_33, v32_34, v32_40, v32_41, v32_42, v32_43, v32_44]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_04, phase32_10, phase32_11, phase32_12, phase32_13, phase32_14, phase32_20, phase32_21, phase32_22, phase32_23, phase32_24, phase32_30, phase32_31, phase32_32, phase32_33, phase32_34, phase32_40, phase32_41, phase32_42, phase32_43, phase32_44]
  try simp only [star_one, star_neg]
  linear_combination ((1293103 / 16) * t ^ 2 + (-149356193 / 960) * t ^ 4 + (-2879232431 / 9600) * t ^ 6 + (109644918210491 / 115200000) * t ^ 8 + (-93716965476361 / 115200000) * t ^ 10 + (789560507107919 / 2764800000) * t ^ 12 + (-59516433430667 / 829440000) * t ^ 14 + (102067727405669 / 5529600000) * t ^ 16 + (4625383938973 / 1382400000) * t ^ 18 + (91194820721 / 691200000) * t ^ 20 + (4815817163671 / 2764800000) * t ^ 22 + (-51543618509 / 44236800) * t ^ 24 + (-23391003029 / 2073600000) * t ^ 26 + (6775187713 / 1769472000) * t ^ 32 + (625695 / 8) * d * t ^ 2 + (-72557737 / 480) * d * t ^ 4 + (210883097 / 4800) * d * t ^ 6 + (7358982155629 / 172800000) * d * t ^ 8 + (-209807847443 / 57600000) * d * t ^ 10 + (-5928960358001 / 460800000) * d * t ^ 12 + (3123086716861 / 414720000) * d * t ^ 14 + (-33796722070699 / 8294400000) * d * t ^ 16 + (-173149587883 / 345600000) * d * t ^ 18 + (8888388871 / 115200000) * d * t ^ 20 + (-58677352519 / 1036800000) * d * t ^ 22 + (-239232431 / 1658880000) * d * t ^ 24 + (-25805924029 / 2073600000) * d * t ^ 26 + (38470649 / 1592524800) * d * t ^ 32 + (-41713 / 16) * d ^ 2 * t ^ 2 + (1413573 / 320) * d ^ 2 * t ^ 4 + (-2829163 / 17280) * d ^ 2 * t ^ 6 + (-12983980627 / 7680000) * d ^ 2 * t ^ 8 + (-14553249257 / 23040000) * d ^ 2 * t ^ 10 + (261128492299 / 552960000) * d ^ 2 * t ^ 12 + (166165991569 / 829440000) * d ^ 2 * t ^ 14 + (6404103737 / 1105920000) * d ^ 2 * t ^ 16 + (-449553439 / 165888000) * d ^ 2 * t ^ 18 + (-1207430011 / 1244160000) * d ^ 2 * t ^ 20 + (49036037 / 552960000) * d ^ 2 * t ^ 22 + (-213349 / 1990656000) * d ^ 2 * t ^ 24 + (1749437 / 93312000) * d ^ 2 * t ^ 26 + (-9025 / 382205952) * d ^ 2 * t ^ 32) * alpha_sq + ((41713 / 4) * t ^ 2 + (-9872303 / 480) * t ^ 4 + (24362831 / 2880) * t ^ 6 + (-10811721029 / 34560000) * t ^ 8 + (18877981723 / 3840000) * t ^ 10 + (-596071523443 / 276480000) * t ^ 12 + (-332988977623 / 414720000) * t ^ 14 + (13230341971 / 552960000) * t ^ 16 + (158230547 / 13824000) * t ^ 18 + (-550828781 / 207360000) * t ^ 20 + (1653065471 / 276480000) * t ^ 22 + (-6602677 / 331776000) * t ^ 24 + (-80942131 / 248832000) * t ^ 26 + (9025 / 31850496) * t ^ 32) * d_sq
#print axioms v33_00
#print axioms v33_11
#print axioms v33_22
#print axioms v33_33
#print axioms v33_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
noncomputable def z34 : Fin 34 → ℂ := Fin.snoc z33 (r ^ 2 * phiPlus)
theorem v34_00 (t : ℂ) : (momentPoly 34 z34 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00]
  try simp only [phase32_00]
  try simp only [star_one, star_neg]
  ring
theorem v34_01 (t : ℂ) : (momentPoly 34 z34 0 1).eval t = ((3 / 16) * t + (-1 / 16) * d * t + (29 / 48) * alpha * t + (-1 / 16) * alpha * d * t) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_01]
  try simp only [phase32_00, phase32_01]
  try simp only [star_one, star_neg]
  ring
theorem v34_02 (t : ℂ) : (momentPoly 34 z34 0 2).eval t = ((-9521 / 480) * t ^ 2 + (13727 / 960) * t ^ 4 + (7 / 32) * d * t ^ 2 + (-1 / 64) * d * t ^ 4 + (3881 / 480) * alpha * t ^ 2 + (-3247 / 960) * alpha * t ^ 4 + (-3 / 32) * alpha * d * t ^ 2 + (-1 / 192) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_01, v33_02]
  try simp only [phase32_00, phase32_01, phase32_02]
  try simp only [star_one, star_neg]
  linear_combination ((-5 / 192) * t ^ 2 + (-7 / 288) * d * t ^ 2 + (1 / 576) * d ^ 2 * t ^ 2) * alpha_sq + ((-1 / 288) * t ^ 2 + (1 / 288) * alpha * t ^ 2) * d_sq
theorem v34_03 (t : ℂ) : (momentPoly 34 z34 0 3).eval t = ((-16609 / 320) * t ^ 3 + (7499 / 320) * t ^ 5 + 1 * t ^ 9 + (1501 / 240) * d * t ^ 3 + (-789 / 160) * d * t ^ 5 + (47 / 384) * d * t ^ 9 + (-8743 / 400) * alpha * t ^ 3 + (24887 / 2400) * alpha * t ^ 5 + (152477 / 28800) * alpha * t ^ 9 + (143 / 64) * alpha * d * t ^ 3 + (-133 / 64) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_01, v33_02, v33_03]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03]
  try simp only [star_one, star_neg]
  linear_combination ((-2891 / 7680) * t ^ 3 + (4493 / 3840) * t ^ 5 + (-2147 / 5760) * d * t ^ 3 + (511 / 2880) * d * t ^ 5 + (17 / 4608) * d ^ 2 * t ^ 3 + (1 / 2304) * d ^ 2 * t ^ 5) * alpha_sq + ((-1 / 48) * t ^ 3 + (-7 / 1152) * alpha * t ^ 3 + (1 / 576) * alpha * t ^ 5) * d_sq
theorem v34_04 (t : ℂ) : (momentPoly 34 z34 0 4).eval t = ((3953057 / 8000) * t ^ 4 + (-28682811 / 32000) * t ^ 6 + (90160949 / 192000) * t ^ 8 + (-15837781 / 144000) * t ^ 10 + (15787417 / 1152000) * t ^ 16 + (-9659 / 1600) * d * t ^ 4 + (29509 / 6400) * d * t ^ 6 + (-4481 / 2560) * d * t ^ 8 + (35413 / 9600) * d * t ^ 10 + (95 / 3072) * d * t ^ 16 + (-7384423 / 8000) * alpha * t ^ 4 + (112051307 / 96000) * alpha * t ^ 6 + (-57409451 / 192000) * alpha * t ^ 8 + (-3353701 / 144000) * alpha * t ^ 10 + (3497417 / 1152000) * alpha * t ^ 16 + (190987 / 14400) * alpha * d * t ^ 4 + (-171089 / 19200) * alpha * d * t ^ 6 + (-253 / 2560) * alpha * d * t ^ 8 + (-3957 / 3200) * alpha * d * t ^ 10 + (-95 / 9216) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_01, v33_02, v33_03, v33_04]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_04]
  try simp only [star_one, star_neg]
  linear_combination ((16501 / 9600) * t ^ 4 + (3893719 / 230400) * t ^ 6 + (-35359 / 3072) * t ^ 8 + (-1157 / 9600) * t ^ 10 + (22939 / 14400) * d * t ^ 4 + (-127093 / 115200) * d * t ^ 6 + (77 / 2560) * d * t ^ 8 + (-39013 / 86400) * d * t ^ 10 + (-145 / 1152) * d ^ 2 * t ^ 4 + (3209 / 27648) * d ^ 2 * t ^ 6 + (1 / 27648) * d ^ 2 * t ^ 8) * alpha_sq + ((131 / 2880) * t ^ 4 + (-451 / 7680) * t ^ 6 + (1 / 4608) * t ^ 8 + (-47 / 3456) * t ^ 10 + (-1319 / 2880) * alpha * t ^ 4 + (3149 / 7680) * alpha * t ^ 6 + (1 / 4608) * alpha * t ^ 8 + (-47 / 3456) * alpha * t ^ 10) * d_sq
theorem v34_10 (t : ℂ) : (momentPoly 34 z34 1 0).eval t = ((3 / 16) * t + (-1 / 16) * d * t + (-29 / 48) * alpha * t + (1 / 16) * alpha * d * t) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_10]
  try simp only [phase32_00, phase32_10]
  try simp only [star_one, star_neg]
  ring
theorem v34_11 (t : ℂ) : (momentPoly 34 z34 1 1).eval t = (34 + (-287 / 12) * t ^ 2 + (-1 / 4) * d * t ^ 2) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_01, v33_10, v33_11]
  try simp only [phase32_00, phase32_01, phase32_10, phase32_11]
  try simp only [star_one, star_neg]
  linear_combination ((5 / 192) * t ^ 2 + (7 / 288) * d * t ^ 2 + (-1 / 576) * d ^ 2 * t ^ 2) * alpha_sq + ((1 / 144) * t ^ 2) * d_sq
theorem v34_12 (t : ℂ) : (momentPoly 34 z34 1 2).eval t = ((201 / 16) * t + (767 / 960) * t ^ 3 + (-2417 / 960) * t ^ 5 + (-67 / 16) * d * t + (3571 / 960) * d * t ^ 3 + (-67 / 320) * d * t ^ 5 + (1943 / 48) * alpha * t + (-43729 / 2880) * alpha * t ^ 3 + (-29521 / 2880) * alpha * t ^ 5 + (-67 / 16) * alpha * d * t + (2141 / 960) * alpha * d * t ^ 3 + (1129 / 960) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_01, v33_02, v33_10, v33_11, v33_12]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_10, phase32_11, phase32_12]
  try simp only [star_one, star_neg]
  linear_combination ((2891 / 23040) * t ^ 3 + (-4493 / 11520) * t ^ 5 + (2147 / 17280) * d * t ^ 3 + (-511 / 8640) * d * t ^ 5 + (-17 / 13824) * d ^ 2 * t ^ 3 + (-1 / 6912) * d ^ 2 * t ^ 5) * alpha_sq + ((17 / 2304) * t ^ 3 + (1 / 1152) * t ^ 5 + (79 / 6912) * alpha * t ^ 3 + (-1 / 3456) * alpha * t ^ 5) * d_sq
theorem v34_13 (t : ℂ) : (momentPoly 34 z34 1 3).eval t = ((-314193 / 160) * t ^ 2 + (27078857 / 9600) * t ^ 4 + (-17914231 / 19200) * t ^ 6 + (-512569 / 57600) * t ^ 10 + (693 / 32) * d * t ^ 2 + (-31993 / 3200) * d * t ^ 4 + (-46141 / 6400) * d * t ^ 6 + (-19519 / 19200) * d * t ^ 10 + (128073 / 160) * alpha * t ^ 2 + (-9054821 / 9600) * alpha * t ^ 4 + (3767023 / 19200) * alpha * t ^ 6 + (156559 / 19200) * alpha * t ^ 10 + (-297 / 32) * alpha * d * t ^ 2 + (93361 / 28800) * alpha * d * t ^ 4 + (80699 / 19200) * alpha * d * t ^ 6 + (-6473 / 19200) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_01, v33_02, v33_03, v33_10, v33_11, v33_12, v33_13]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_10, phase32_11, phase32_12, phase32_13]
  try simp only [star_one, star_neg]
  linear_combination ((-165 / 64) * t ^ 2 + (57671 / 57600) * t ^ 4 + (23111 / 25600) * t ^ 6 + (1157 / 38400) * t ^ 10 + (-77 / 32) * d * t ^ 2 + (187 / 200) * d * t ^ 4 + (21051 / 25600) * d * t ^ 6 + (39013 / 345600) * d * t ^ 10 + (11 / 64) * d ^ 2 * t ^ 2 + (-763 / 11520) * d ^ 2 * t ^ 4 + (-103 / 1280) * d ^ 2 * t ^ 6) * alpha_sq + ((-11 / 32) * t ^ 2 + (-259 / 5760) * t ^ 4 + (14917 / 46080) * t ^ 6 + (-47 / 13824) * t ^ 10 + (11 / 32) * alpha * t ^ 2 + (-397 / 1920) * alpha * t ^ 4 + (-4117 / 46080) * alpha * t ^ 6 + (47 / 13824) * alpha * t ^ 10) * d_sq
theorem v34_14 (t : ℂ) : (momentPoly 34 z34 1 4).eval t = ((-215917 / 32) * t ^ 3 + (1291117831 / 192000) * t ^ 5 + (4948519 / 96000) * t ^ 7 + (-113075879 / 384000) * t ^ 9 + (-64896259 / 288000) * t ^ 11 + (8147209 / 1152000) * t ^ 17 + (19513 / 24) * d * t ^ 3 + (-724641271 / 576000) * d * t ^ 5 + (39893707 / 96000) * d * t ^ 7 + (20101813 / 384000) * d * t ^ 9 + (31673 / 288000) * d * t ^ 11 + (-599441 / 384000) * d * t ^ 17 + (-113659 / 40) * alpha * t ^ 3 + (335164619 / 115200) * alpha * t ^ 5 + (930637 / 19200) * alpha * t ^ 7 + (7282893 / 25600) * alpha * t ^ 9 + (-81942679 / 172800) * alpha * t ^ 11 + (-7968271 / 691200) * alpha * t ^ 17 + (9295 / 32) * alpha * d * t ^ 3 + (-17482807 / 38400) * alpha * d * t ^ 5 + (762663 / 6400) * alpha * d * t ^ 7 + (817651 / 15360) * alpha * d * t ^ 9 + (-294229 / 57600) * alpha * d * t ^ 11 + (1985 / 3072) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_01, v33_02, v33_03, v33_04, v33_10, v33_11, v33_12, v33_13, v33_14]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_04, phase32_10, phase32_11, phase32_12, phase32_13, phase32_14]
  try simp only [star_one, star_neg]
  linear_combination ((-37583 / 768) * t ^ 3 + (207300991 / 1152000) * t ^ 5 + (-81997607 / 1152000) * t ^ 7 + (-355944701 / 9216000) * t ^ 9 + (-642469 / 768000) * t ^ 11 + (5153323 / 13824000) * t ^ 17 + (-27911 / 576) * d * t ^ 3 + (42813187 / 864000) * d * t ^ 5 + (552863 / 432000) * d * t ^ 7 + (-22241663 / 4608000) * d * t ^ 9 + (-8654269 / 10368000) * d * t ^ 11 + (1146047 / 20736000) * d * t ^ 17 + (1105 / 2304) * d ^ 2 * t ^ 3 + (3431 / 138240) * d ^ 2 * t ^ 5 + (-56291 / 138240) * d ^ 2 * t ^ 7 + (-2111 / 221184) * d ^ 2 * t ^ 9 + (305 / 165888) * d ^ 2 * t ^ 11 + (-95 / 331776) * d ^ 2 * t ^ 17) * alpha_sq + ((-65 / 24) * t ^ 3 + (18353 / 23040) * t ^ 5 + (33907 / 23040) * t ^ 7 + (11 / 192) * t ^ 9 + (-23 / 864) * t ^ 11 + (-455 / 576) * alpha * t ^ 3 + (111563 / 345600) * alpha * t ^ 5 + (11737 / 38400) * alpha * t ^ 7 + (-13669 / 276480) * alpha * t ^ 9 + (145327 / 1036800) * alpha * t ^ 11 + (95 / 82944) * alpha * t ^ 17) * d_sq
theorem v34_20 (t : ℂ) : (momentPoly 34 z34 2 0).eval t = ((-9521 / 480) * t ^ 2 + (13727 / 960) * t ^ 4 + (7 / 32) * d * t ^ 2 + (-1 / 64) * d * t ^ 4 + (-3881 / 480) * alpha * t ^ 2 + (3247 / 960) * alpha * t ^ 4 + (3 / 32) * alpha * d * t ^ 2 + (1 / 192) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_10, v33_20]
  try simp only [phase32_00, phase32_10, phase32_20]
  try simp only [star_one, star_neg]
  linear_combination ((-5 / 192) * t ^ 2 + (-7 / 288) * d * t ^ 2 + (1 / 576) * d ^ 2 * t ^ 2) * alpha_sq + ((-1 / 288) * t ^ 2 + (-1 / 288) * alpha * t ^ 2) * d_sq
theorem v34_21 (t : ℂ) : (momentPoly 34 z34 2 1).eval t = ((201 / 16) * t + (767 / 960) * t ^ 3 + (-2417 / 960) * t ^ 5 + (-67 / 16) * d * t + (3571 / 960) * d * t ^ 3 + (-67 / 320) * d * t ^ 5 + (-1943 / 48) * alpha * t + (43729 / 2880) * alpha * t ^ 3 + (29521 / 2880) * alpha * t ^ 5 + (67 / 16) * alpha * d * t + (-2141 / 960) * alpha * d * t ^ 3 + (-1129 / 960) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_01, v33_10, v33_11, v33_20, v33_21]
  try simp only [phase32_00, phase32_01, phase32_10, phase32_11, phase32_20, phase32_21]
  try simp only [star_one, star_neg]
  linear_combination ((2891 / 23040) * t ^ 3 + (-4493 / 11520) * t ^ 5 + (2147 / 17280) * d * t ^ 3 + (-511 / 8640) * d * t ^ 5 + (-17 / 13824) * d ^ 2 * t ^ 3 + (-1 / 6912) * d ^ 2 * t ^ 5) * alpha_sq + ((17 / 2304) * t ^ 3 + (1 / 1152) * t ^ 5 + (-79 / 6912) * alpha * t ^ 3 + (1 / 3456) * alpha * t ^ 5) * d_sq
theorem v34_22 (t : ℂ) : (momentPoly 34 z34 2 2).eval t = (2278 + (-3157) * t ^ 2 + (20871739 / 14400) * t ^ 4 + (-18371711 / 28800) * t ^ 6 + (5903033 / 28800) * t ^ 8 + (-33) * d * t ^ 2 + (18023 / 960) * d * t ^ 4 + (18289 / 1920) * d * t ^ 6 + (-131 / 384) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_01, v33_02, v33_10, v33_11, v33_12, v33_20, v33_21, v33_22]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_10, phase32_11, phase32_12, phase32_20, phase32_21, phase32_22]
  try simp only [star_one, star_neg]
  linear_combination ((55 / 16) * t ^ 2 + (-32969 / 17280) * t ^ 4 + (-945143 / 138240) * t ^ 6 + (35359 / 9216) * t ^ 8 + (77 / 24) * d * t ^ 2 + (-15359 / 8640) * d * t ^ 4 + (-10073 / 13824) * d * t ^ 6 + (-77 / 7680) * d * t ^ 8 + (-11 / 48) * d ^ 2 * t ^ 2 + (2251 / 17280) * d ^ 2 * t ^ 4 + (28451 / 414720) * d ^ 2 * t ^ 6 + (-1 / 82944) * d ^ 2 * t ^ 8) * alpha_sq + ((11 / 12) * t ^ 2 + (-5227 / 8640) * t ^ 4 + (-6887 / 34560) * t ^ 6 + (1 / 6912) * t ^ 8) * d_sq
theorem v34_23 (t : ℂ) : (momentPoly 34 z34 2 3).eval t = ((9951 / 8) * t + (9971 / 64) * t ^ 3 + (-21826043 / 24000) * t ^ 5 + (-12552803 / 19200) * t ^ 7 + (108140053 / 384000) * t ^ 9 + (74282339 / 576000) * t ^ 11 + (-46892593 / 1152000) * t ^ 13 + (-3317 / 8) * d * t + (46423 / 64) * d * t ^ 3 + (-23742199 / 57600) * d * t ^ 5 + (7869383 / 57600) * d * t ^ 7 + (-662597 / 15360) * d * t ^ 9 + (-23611 / 7200) * d * t ^ 11 + (131657 / 76800) * d * t ^ 13 + (96193 / 24) * alpha * t + (-568477 / 192) * alpha * t ^ 3 + (-447526613 / 288000) * alpha * t ^ 5 + (33127009 / 57600) * alpha * t ^ 7 + (233122967 / 1152000) * alpha * t ^ 9 + (-74325787 / 864000) * alpha * t ^ 11 + (272495063 / 3456000) * alpha * t ^ 13 + (-3317 / 8) * alpha * d * t + (27833 / 64) * alpha * d * t ^ 3 + (623963 / 5760) * alpha * d * t ^ 5 + (-5458523 / 57600) * alpha * d * t ^ 7 + (-672377 / 15360) * alpha * d * t ^ 9 + (-80249 / 38400) * alpha * d * t ^ 11 + (91921 / 230400) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_01, v33_02, v33_03, v33_10, v33_11, v33_12, v33_13, v33_20, v33_21, v33_22, v33_23]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_10, phase32_11, phase32_12, phase32_13, phase32_20, phase32_21, phase32_22, phase32_23]
  try simp only [star_one, star_neg]
  linear_combination ((37583 / 1536) * t ^ 3 + (-11155387 / 115200) * t ^ 5 + (1439679 / 25600) * t ^ 7 + (1805399 / 184320) * t ^ 9 + (-1393549 / 2764800) * t ^ 11 + (-574223 / 276480) * t ^ 13 + (27911 / 1152) * d * t ^ 3 + (-5451787 / 172800) * d * t ^ 5 + (386723 / 43200) * d * t ^ 7 + (-1588421 / 2764800) * d * t ^ 9 + (2004847 / 8294400) * d * t ^ 11 + (39013 / 4147200) * d * t ^ 13 + (-1105 / 4608) * d ^ 2 * t ^ 3 + (25787 / 345600) * d ^ 2 * t ^ 5 + (95839 / 691200) * d ^ 2 * t ^ 7 + (131 / 69120) * d ^ 2 * t ^ 9 + (-6373 / 691200) * d ^ 2 * t ^ 11) * alpha_sq + ((1105 / 768) * t ^ 3 + (-150343 / 230400) * t ^ 5 + (-161453 / 230400) * t ^ 7 + (1049 / 36864) * t ^ 9 + (170977 / 2764800) * t ^ 11 + (-47 / 55296) * t ^ 13 + (5135 / 2304) * alpha * t ^ 3 + (-872197 / 691200) * alpha * t ^ 5 + (-523807 / 691200) * alpha * t ^ 7 + (3175 / 110592) * alpha * t ^ 9 + (-134177 / 8294400) * alpha * t ^ 11 + (47 / 165888) * alpha * t ^ 13) * d_sq
theorem v34_24 (t : ℂ) : (momentPoly 34 z34 2 4).eval t = ((-61286677 / 240) * t ^ 2 + (2610558421 / 4800) * t ^ 4 + (-2154846767129 / 5760000) * t ^ 6 + (137789913701 / 1280000) * t ^ 8 + (-7449338531 / 230400) * t ^ 10 + (705269497757 / 69120000) * t ^ 12 + (-21485389537 / 17280000) * t ^ 14 + (-12086034697 / 69120000) * t ^ 18 + (5207121841 / 34560000) * t ^ 20 + (45059 / 16) * d * t ^ 2 + (-3783479 / 1600) * d * t ^ 4 + (-1883792051 / 1152000) * d * t ^ 6 + (2089223659 / 2304000) * d * t ^ 8 + (22899137 / 192000) * d * t ^ 10 + (214015411 / 1536000) * d * t ^ 12 + (81294203 / 1152000) * d * t ^ 14 + (15269797 / 4608000) * d * t ^ 18 + (115523 / 384000) * d * t ^ 20 + (24981997 / 240) * alpha * t ^ 2 + (-956647813 / 4800) * alpha * t ^ 4 + (664409717399 / 5760000) * alpha * t ^ 6 + (-354411990619 / 11520000) * alpha * t ^ 8 + (16986474533 / 1152000) * alpha * t ^ 10 + (-162099401027 / 69120000) * alpha * t ^ 12 + (-1435958297 / 1920000) * alpha * t ^ 14 + (-478627499 / 2560000) * alpha * t ^ 18 + (3225483169 / 34560000) * alpha * t ^ 20 + (-19311 / 16) * alpha * d * t ^ 2 + (12885083 / 14400) * alpha * d * t ^ 4 + (3215211467 / 3456000) * alpha * d * t ^ 6 + (-3231866723 / 6912000) * alpha * d * t ^ 8 + (-140192609 / 576000) * alpha * d * t ^ 10 + (260744477 / 4608000) * alpha * d * t ^ 12 + (-12753227 / 3456000) * alpha * d * t ^ 14 + (7126543 / 2764800) * alpha * d * t ^ 18 + (-15727 / 1152000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_01, v33_02, v33_03, v33_04, v33_10, v33_11, v33_12, v33_13, v33_14, v33_20, v33_21, v33_22, v33_23, v33_24]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_04, phase32_10, phase32_11, phase32_12, phase32_13, phase32_14, phase32_20, phase32_21, phase32_22, phase32_23, phase32_24]
  try simp only [star_one, star_neg]
  linear_combination ((-32185 / 96) * t ^ 2 + (57671 / 225) * t ^ 4 + (278229067 / 1382400) * t ^ 6 + (3127748459 / 13824000) * t ^ 8 + (-2417873741 / 4608000) * t ^ 10 + (56590437107 / 331776000) * t ^ 12 + (569214209 / 82944000) * t ^ 14 + (778843313 / 331776000) * t ^ 18 + (-39785417 / 11059200) * t ^ 20 + (-45059 / 144) * d * t ^ 2 + (5984 / 25) * d * t ^ 4 + (42061319 / 230400) * d * t ^ 6 + (-14666143 / 153600) * d * t ^ 8 + (3122591 / 1382400) * d * t ^ 10 + (-13543763 / 768000) * d * t ^ 12 + (-34882457 / 5184000) * d * t ^ 14 + (-10964857 / 20736000) * d * t ^ 18 + (-18949 / 3456000) * d * t ^ 20 + (6437 / 288) * d ^ 2 * t ^ 2 + (-763 / 45) * d ^ 2 * t ^ 4 + (-25861153 / 1382400) * d ^ 2 * t ^ 6 + (26074663 / 2764800) * d ^ 2 * t ^ 8 + (3970547 / 921600) * d ^ 2 * t ^ 10 + (-2136143 / 66355200) * d ^ 2 * t ^ 12 + (-1344703 / 49766400) * d ^ 2 * t ^ 14 + (141305 / 7962624) * d ^ 2 * t ^ 18 + (-95 / 3981312) * d ^ 2 * t ^ 20) * alpha_sq + ((-6437 / 144) * t ^ 2 + (-518 / 45) * t ^ 4 + (400482341 / 3456000) * t ^ 6 + (-112489213 / 2304000) * t ^ 8 + (-87558029 / 6912000) * t ^ 10 + (119683087 / 165888000) * t ^ 12 + (-381607 / 8294400) * t ^ 14 + (-807083 / 165888000) * t ^ 18 + (-95 / 663552) * t ^ 20 + (6437 / 144) * alpha * t ^ 2 + (-794 / 15) * alpha * t ^ 4 + (-17916511 / 3456000) * alpha * t ^ 6 + (58210649 / 6912000) * alpha * t ^ 8 + (13769093 / 2304000) * alpha * t ^ 10 + (22572833 / 165888000) * alpha * t ^ 12 + (-2080393 / 8294400) * alpha * t ^ 14 + (-10722917 / 165888000) * alpha * t ^ 18 + (95 / 663552) * alpha * t ^ 20) * d_sq
theorem v34_30 (t : ℂ) : (momentPoly 34 z34 3 0).eval t = ((-16609 / 320) * t ^ 3 + (7499 / 320) * t ^ 5 + 1 * t ^ 9 + (1501 / 240) * d * t ^ 3 + (-789 / 160) * d * t ^ 5 + (47 / 384) * d * t ^ 9 + (8743 / 400) * alpha * t ^ 3 + (-24887 / 2400) * alpha * t ^ 5 + (-152477 / 28800) * alpha * t ^ 9 + (-143 / 64) * alpha * d * t ^ 3 + (133 / 64) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_10, v33_20, v33_30]
  try simp only [phase32_00, phase32_10, phase32_20, phase32_30]
  try simp only [star_one, star_neg]
  linear_combination ((-2891 / 7680) * t ^ 3 + (4493 / 3840) * t ^ 5 + (-2147 / 5760) * d * t ^ 3 + (511 / 2880) * d * t ^ 5 + (17 / 4608) * d ^ 2 * t ^ 3 + (1 / 2304) * d ^ 2 * t ^ 5) * alpha_sq + ((-1 / 48) * t ^ 3 + (7 / 1152) * alpha * t ^ 3 + (-1 / 576) * alpha * t ^ 5) * d_sq
theorem v34_31 (t : ℂ) : (momentPoly 34 z34 3 1).eval t = ((-314193 / 160) * t ^ 2 + (27078857 / 9600) * t ^ 4 + (-17914231 / 19200) * t ^ 6 + (-512569 / 57600) * t ^ 10 + (693 / 32) * d * t ^ 2 + (-31993 / 3200) * d * t ^ 4 + (-46141 / 6400) * d * t ^ 6 + (-19519 / 19200) * d * t ^ 10 + (-128073 / 160) * alpha * t ^ 2 + (9054821 / 9600) * alpha * t ^ 4 + (-3767023 / 19200) * alpha * t ^ 6 + (-156559 / 19200) * alpha * t ^ 10 + (297 / 32) * alpha * d * t ^ 2 + (-93361 / 28800) * alpha * d * t ^ 4 + (-80699 / 19200) * alpha * d * t ^ 6 + (6473 / 19200) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_01, v33_10, v33_11, v33_20, v33_21, v33_30, v33_31]
  try simp only [phase32_00, phase32_01, phase32_10, phase32_11, phase32_20, phase32_21, phase32_30, phase32_31]
  try simp only [star_one, star_neg]
  linear_combination ((-165 / 64) * t ^ 2 + (57671 / 57600) * t ^ 4 + (23111 / 25600) * t ^ 6 + (1157 / 38400) * t ^ 10 + (-77 / 32) * d * t ^ 2 + (187 / 200) * d * t ^ 4 + (21051 / 25600) * d * t ^ 6 + (39013 / 345600) * d * t ^ 10 + (11 / 64) * d ^ 2 * t ^ 2 + (-763 / 11520) * d ^ 2 * t ^ 4 + (-103 / 1280) * d ^ 2 * t ^ 6) * alpha_sq + ((-11 / 32) * t ^ 2 + (-259 / 5760) * t ^ 4 + (14917 / 46080) * t ^ 6 + (-47 / 13824) * t ^ 10 + (-11 / 32) * alpha * t ^ 2 + (397 / 1920) * alpha * t ^ 4 + (4117 / 46080) * alpha * t ^ 6 + (-47 / 13824) * alpha * t ^ 10) * d_sq
theorem v34_32 (t : ℂ) : (momentPoly 34 z34 3 2).eval t = ((9951 / 8) * t + (9971 / 64) * t ^ 3 + (-21826043 / 24000) * t ^ 5 + (-12552803 / 19200) * t ^ 7 + (108140053 / 384000) * t ^ 9 + (74282339 / 576000) * t ^ 11 + (-46892593 / 1152000) * t ^ 13 + (-3317 / 8) * d * t + (46423 / 64) * d * t ^ 3 + (-23742199 / 57600) * d * t ^ 5 + (7869383 / 57600) * d * t ^ 7 + (-662597 / 15360) * d * t ^ 9 + (-23611 / 7200) * d * t ^ 11 + (131657 / 76800) * d * t ^ 13 + (-96193 / 24) * alpha * t + (568477 / 192) * alpha * t ^ 3 + (447526613 / 288000) * alpha * t ^ 5 + (-33127009 / 57600) * alpha * t ^ 7 + (-233122967 / 1152000) * alpha * t ^ 9 + (74325787 / 864000) * alpha * t ^ 11 + (-272495063 / 3456000) * alpha * t ^ 13 + (3317 / 8) * alpha * d * t + (-27833 / 64) * alpha * d * t ^ 3 + (-623963 / 5760) * alpha * d * t ^ 5 + (5458523 / 57600) * alpha * d * t ^ 7 + (672377 / 15360) * alpha * d * t ^ 9 + (80249 / 38400) * alpha * d * t ^ 11 + (-91921 / 230400) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_01, v33_02, v33_10, v33_11, v33_12, v33_20, v33_21, v33_22, v33_30, v33_31, v33_32]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_10, phase32_11, phase32_12, phase32_20, phase32_21, phase32_22, phase32_30, phase32_31, phase32_32]
  try simp only [star_one, star_neg]
  linear_combination ((37583 / 1536) * t ^ 3 + (-11155387 / 115200) * t ^ 5 + (1439679 / 25600) * t ^ 7 + (1805399 / 184320) * t ^ 9 + (-1393549 / 2764800) * t ^ 11 + (-574223 / 276480) * t ^ 13 + (27911 / 1152) * d * t ^ 3 + (-5451787 / 172800) * d * t ^ 5 + (386723 / 43200) * d * t ^ 7 + (-1588421 / 2764800) * d * t ^ 9 + (2004847 / 8294400) * d * t ^ 11 + (39013 / 4147200) * d * t ^ 13 + (-1105 / 4608) * d ^ 2 * t ^ 3 + (25787 / 345600) * d ^ 2 * t ^ 5 + (95839 / 691200) * d ^ 2 * t ^ 7 + (131 / 69120) * d ^ 2 * t ^ 9 + (-6373 / 691200) * d ^ 2 * t ^ 11) * alpha_sq + ((1105 / 768) * t ^ 3 + (-150343 / 230400) * t ^ 5 + (-161453 / 230400) * t ^ 7 + (1049 / 36864) * t ^ 9 + (170977 / 2764800) * t ^ 11 + (-47 / 55296) * t ^ 13 + (-5135 / 2304) * alpha * t ^ 3 + (872197 / 691200) * alpha * t ^ 5 + (523807 / 691200) * alpha * t ^ 7 + (-3175 / 110592) * alpha * t ^ 9 + (134177 / 8294400) * alpha * t ^ 11 + (-47 / 165888) * alpha * t ^ 13) * d_sq
theorem v34_33 (t : ℂ) : (momentPoly 34 z34 3 3).eval t = (225556 + (-1847419 / 4) * t ^ 2 + (20871739 / 50) * t ^ 4 + (-79253302717 / 240000) * t ^ 6 + (44303646001 / 240000) * t ^ 8 + (-4086565841 / 120000) * t ^ 10 + (1913118707 / 960000) * t ^ 12 + (-8073872863 / 5760000) * t ^ 14 + (1031168119 / 17280000) * t ^ 18 + (-19311 / 4) * d * t ^ 2 + (54069 / 10) * d * t ^ 4 + (4702883 / 3840) * d * t ^ 6 + (-61104997 / 38400) * d * t ^ 8 + (-3502681 / 12800) * d * t ^ 10 + (1620617 / 38400) * d * t ^ 12 + (-852389 / 12800) * d * t ^ 14 + (47 / 192) * d * t ^ 18) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_01, v33_02, v33_03, v33_10, v33_11, v33_12, v33_13, v33_20, v33_21, v33_22, v33_23, v33_30, v33_31, v33_32, v33_33]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_10, phase32_11, phase32_12, phase32_13, phase32_20, phase32_21, phase32_22, phase32_23, phase32_30, phase32_31, phase32_32, phase32_33]
  try simp only [star_one, star_neg]
  linear_combination ((32185 / 64) * t ^ 2 + (-32969 / 60) * t ^ 4 + (-4218635303 / 2304000) * t ^ 6 + (2466893491 / 921600) * t ^ 8 + (-1908096097 / 2304000) * t ^ 10 + (-58761269 / 13824000) * t ^ 12 + (-47420147 / 4608000) * t ^ 14 + (-3548831 / 2764800) * t ^ 18 + (45059 / 96) * d * t ^ 2 + (-15359 / 30) * d * t ^ 4 + (-2330167 / 36000) * d * t ^ 6 + (45762947 / 460800) * d * t ^ 8 + (46030343 / 2304000) * d * t ^ 10 + (-8558699 / 864000) * d * t ^ 12 + (38319761 / 3456000) * d * t ^ 14 + (-6437 / 192) * d ^ 2 * t ^ 2 + (2251 / 60) * d ^ 2 * t ^ 4 + (12058409 / 1382400) * d ^ 2 * t ^ 6 + (-4989403 / 552960) * d ^ 2 * t ^ 8 + (-175229 / 43200) * d ^ 2 * t ^ 10 + (-17639 / 110592) * d ^ 2 * t ^ 12 + (8329 / 230400) * d ^ 2 * t ^ 14) * alpha_sq + ((6437 / 48) * t ^ 2 + (-5227 / 30) * t ^ 4 + (321277 / 38400) * t ^ 6 + (7685839 / 460800) * t ^ 8 + (7535357 / 460800) * t ^ 10 + (730667 / 691200) * t ^ 12 + (-1448443 / 2764800) * t ^ 14 + (2209 / 331776) * t ^ 18) * d_sq
theorem v34_34 (t : ℂ) : (momentPoly 34 z34 3 4).eval t = ((2588457 / 16) * t + (4788381 / 160) * t ^ 3 + (-2020207843 / 8000) * t ^ 5 + (-4142369275733 / 19200000) * t ^ 7 + (3277516419569 / 9600000) * t ^ 9 + (-321410465677 / 12800000) * t ^ 11 + (-792185819749 / 15360000) * t ^ 13 + (2353521796711 / 115200000) * t ^ 15 + (-1010812850669 / 230400000) * t ^ 17 + (-904880209543 / 691200000) * t ^ 19 + (75987507079 / 153600000) * t ^ 21 + (88343334623 / 1382400000) * t ^ 25 + (-862819 / 16) * d * t + (22293753 / 160) * d * t ^ 3 + (-474307389 / 3200) * d * t ^ 5 + (73576740271 / 720000) * d * t ^ 7 + (-589306146823 / 11520000) * d * t ^ 9 + (30711615641 / 2880000) * d * t ^ 11 + (101768633707 / 138240000) * d * t ^ 13 + (4040804377 / 23040000) * d * t ^ 15 + (12766883 / 230400) * d * t ^ 17 + (4006571881 / 46080000) * d * t ^ 19 + (-8351315279 / 92160000) * d * t ^ 21 + (29621251 / 18432000) * d * t ^ 25 + (25021751 / 48) * alpha * t + (-91000049 / 160) * alpha * t ^ 3 + (-10364968669 / 48000) * alpha * t ^ 5 + (23105382349 / 112500) * alpha * t ^ 7 + (3548419767197 / 57600000) * alpha * t ^ 9 + (-123858375521 / 4800000) * alpha * t ^ 11 + (6371968724039 / 138240000) * alpha * t ^ 13 + (-5853664159381 / 345600000) * alpha * t ^ 15 + (-943694216803 / 345600000) * alpha * t ^ 17 + (830797801213 / 2073600000) * alpha * t ^ 19 + (-291412701697 / 1382400000) * alpha * t ^ 21 + (-293815324273 / 4147200000) * alpha * t ^ 25 + (-862819 / 16) * alpha * d * t + (13366263 / 160) * alpha * d * t ^ 3 + (-33373 / 20) * alpha * d * t ^ 5 + (-305676204809 / 11520000) * alpha * d * t ^ 7 + (-414086131 / 40000) * alpha * d * t ^ 9 + (138469648613 / 23040000) * alpha * d * t ^ 11 + (369787688747 / 138240000) * alpha * d * t ^ 13 + (930508709 / 7680000) * alpha * d * t ^ 15 + (-21187703 / 614400) * alpha * d * t ^ 17 + (-2919064427 / 138240000) * alpha * d * t ^ 19 + (757653901 / 92160000) * alpha * d * t ^ 21 + (14380003 / 55296000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_01, v33_02, v33_03, v33_04, v33_10, v33_11, v33_12, v33_13, v33_14, v33_20, v33_21, v33_22, v33_23, v33_24, v33_30, v33_31, v33_32, v33_33, v33_34]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_04, phase32_10, phase32_11, phase32_12, phase32_13, phase32_14, phase32_20, phase32_21, phase32_22, phase32_23, phase32_24, phase32_30, phase32_31, phase32_32, phase32_33, phase32_34]
  try simp only [star_one, star_neg]
  linear_combination ((6016171 / 1280) * t ^ 3 + (-215717323 / 9600) * t ^ 5 + (2288734912829 / 92160000) * t ^ 7 + (-79460461837 / 15360000) * t ^ 9 + (-2769740929 / 1536000) * t ^ 11 + (-445484481971 / 552960000) * t ^ 13 + (197041613167 / 276480000) * t ^ 15 + (-42731496977 / 221184000) * t ^ 17 + (-34360924067 / 1658880000) * t ^ 19 + (35148047363 / 1105920000) * t ^ 21 + (677354041 / 331776000) * t ^ 25 + (4467907 / 960) * d * t ^ 3 + (-281738891 / 28800) * d * t ^ 5 + (155856116111 / 23040000) * d * t ^ 7 + (-5980575077 / 2560000) * d * t ^ 9 + (10001221093 / 11059200) * d * t ^ 11 + (-115689131359 / 829440000) * d * t ^ 13 + (-7979606801 / 207360000) * d * t ^ 15 + (-617579 / 8192000) * d * t ^ 17 + (-22469858953 / 2488320000) * d * t ^ 19 + (18592300709 / 3317760000) * d * t ^ 21 + (741247 / 39813120) * d * t ^ 25 + (-35377 / 768) * d ^ 2 * t ^ 3 + (481639 / 14400) * d ^ 2 * t ^ 5 + (2558429209 / 55296000) * d ^ 2 * t ^ 7 + (-686177849 / 27648000) * d ^ 2 * t ^ 9 + (-649675043 / 55296000) * d ^ 2 * t ^ 11 + (51426697 / 22118400) * d ^ 2 * t ^ 13 + (-7342583 / 55296000) * d ^ 2 * t ^ 15 + (106321 / 33177600) * d ^ 2 * t ^ 17 + (39630689 / 331776000) * d ^ 2 * t ^ 19 + (-237931 / 82944000) * d ^ 2 * t ^ 21) * alpha_sq + ((35377 / 128) * t ^ 3 + (-10679509 / 38400) * t ^ 5 + (-45829023 / 256000) * t ^ 7 + (736983451 / 4608000) * t ^ 9 + (185784817 / 4608000) * t ^ 11 + (-226533037 / 13824000) * t ^ 13 + (556099 / 1152000) * t ^ 15 + (-475607 / 4915200) * t ^ 17 + (-16421213 / 33177600) * t ^ 19 + (-1729361 / 73728000) * t ^ 21 + (4465 / 2654208) * t ^ 25 + (164399 / 384) * alpha * t ^ 3 + (-53740511 / 115200) * alpha * t ^ 5 + (-2387934607 / 13824000) * alpha * t ^ 7 + (2386486141 / 13824000) * alpha * t ^ 9 + (2778359 / 76800) * alpha * t ^ 11 + (528677 / 16588800) * alpha * t ^ 13 + (248471687 / 41472000) * alpha * t ^ 15 + (-606737 / 132710400) * alpha * t ^ 17 + (-685189 / 497664000) * alpha * t ^ 19 + (18168083 / 663552000) * alpha * t ^ 21 + (-4465 / 7962624) * alpha * t ^ 25) * d_sq
theorem v34_40 (t : ℂ) : (momentPoly 34 z34 4 0).eval t = ((3953057 / 8000) * t ^ 4 + (-28682811 / 32000) * t ^ 6 + (90160949 / 192000) * t ^ 8 + (-15837781 / 144000) * t ^ 10 + (15787417 / 1152000) * t ^ 16 + (-9659 / 1600) * d * t ^ 4 + (29509 / 6400) * d * t ^ 6 + (-4481 / 2560) * d * t ^ 8 + (35413 / 9600) * d * t ^ 10 + (95 / 3072) * d * t ^ 16 + (7384423 / 8000) * alpha * t ^ 4 + (-112051307 / 96000) * alpha * t ^ 6 + (57409451 / 192000) * alpha * t ^ 8 + (3353701 / 144000) * alpha * t ^ 10 + (-3497417 / 1152000) * alpha * t ^ 16 + (-190987 / 14400) * alpha * d * t ^ 4 + (171089 / 19200) * alpha * d * t ^ 6 + (253 / 2560) * alpha * d * t ^ 8 + (3957 / 3200) * alpha * d * t ^ 10 + (95 / 9216) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_10, v33_20, v33_30, v33_40]
  try simp only [phase32_00, phase32_10, phase32_20, phase32_30, phase32_40]
  try simp only [star_one, star_neg]
  linear_combination ((16501 / 9600) * t ^ 4 + (3893719 / 230400) * t ^ 6 + (-35359 / 3072) * t ^ 8 + (-1157 / 9600) * t ^ 10 + (22939 / 14400) * d * t ^ 4 + (-127093 / 115200) * d * t ^ 6 + (77 / 2560) * d * t ^ 8 + (-39013 / 86400) * d * t ^ 10 + (-145 / 1152) * d ^ 2 * t ^ 4 + (3209 / 27648) * d ^ 2 * t ^ 6 + (1 / 27648) * d ^ 2 * t ^ 8) * alpha_sq + ((131 / 2880) * t ^ 4 + (-451 / 7680) * t ^ 6 + (1 / 4608) * t ^ 8 + (-47 / 3456) * t ^ 10 + (1319 / 2880) * alpha * t ^ 4 + (-3149 / 7680) * alpha * t ^ 6 + (-1 / 4608) * alpha * t ^ 8 + (47 / 3456) * alpha * t ^ 10) * d_sq
theorem v34_41 (t : ℂ) : (momentPoly 34 z34 4 1).eval t = ((-215917 / 32) * t ^ 3 + (1291117831 / 192000) * t ^ 5 + (4948519 / 96000) * t ^ 7 + (-113075879 / 384000) * t ^ 9 + (-64896259 / 288000) * t ^ 11 + (8147209 / 1152000) * t ^ 17 + (19513 / 24) * d * t ^ 3 + (-724641271 / 576000) * d * t ^ 5 + (39893707 / 96000) * d * t ^ 7 + (20101813 / 384000) * d * t ^ 9 + (31673 / 288000) * d * t ^ 11 + (-599441 / 384000) * d * t ^ 17 + (113659 / 40) * alpha * t ^ 3 + (-335164619 / 115200) * alpha * t ^ 5 + (-930637 / 19200) * alpha * t ^ 7 + (-7282893 / 25600) * alpha * t ^ 9 + (81942679 / 172800) * alpha * t ^ 11 + (7968271 / 691200) * alpha * t ^ 17 + (-9295 / 32) * alpha * d * t ^ 3 + (17482807 / 38400) * alpha * d * t ^ 5 + (-762663 / 6400) * alpha * d * t ^ 7 + (-817651 / 15360) * alpha * d * t ^ 9 + (294229 / 57600) * alpha * d * t ^ 11 + (-1985 / 3072) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_01, v33_10, v33_11, v33_20, v33_21, v33_30, v33_31, v33_40, v33_41]
  try simp only [phase32_00, phase32_01, phase32_10, phase32_11, phase32_20, phase32_21, phase32_30, phase32_31, phase32_40, phase32_41]
  try simp only [star_one, star_neg]
  linear_combination ((-37583 / 768) * t ^ 3 + (207300991 / 1152000) * t ^ 5 + (-81997607 / 1152000) * t ^ 7 + (-355944701 / 9216000) * t ^ 9 + (-642469 / 768000) * t ^ 11 + (5153323 / 13824000) * t ^ 17 + (-27911 / 576) * d * t ^ 3 + (42813187 / 864000) * d * t ^ 5 + (552863 / 432000) * d * t ^ 7 + (-22241663 / 4608000) * d * t ^ 9 + (-8654269 / 10368000) * d * t ^ 11 + (1146047 / 20736000) * d * t ^ 17 + (1105 / 2304) * d ^ 2 * t ^ 3 + (3431 / 138240) * d ^ 2 * t ^ 5 + (-56291 / 138240) * d ^ 2 * t ^ 7 + (-2111 / 221184) * d ^ 2 * t ^ 9 + (305 / 165888) * d ^ 2 * t ^ 11 + (-95 / 331776) * d ^ 2 * t ^ 17) * alpha_sq + ((-65 / 24) * t ^ 3 + (18353 / 23040) * t ^ 5 + (33907 / 23040) * t ^ 7 + (11 / 192) * t ^ 9 + (-23 / 864) * t ^ 11 + (455 / 576) * alpha * t ^ 3 + (-111563 / 345600) * alpha * t ^ 5 + (-11737 / 38400) * alpha * t ^ 7 + (13669 / 276480) * alpha * t ^ 9 + (-145327 / 1036800) * alpha * t ^ 11 + (-95 / 82944) * alpha * t ^ 17) * d_sq
theorem v34_42 (t : ℂ) : (momentPoly 34 z34 4 2).eval t = ((-61286677 / 240) * t ^ 2 + (2610558421 / 4800) * t ^ 4 + (-2154846767129 / 5760000) * t ^ 6 + (137789913701 / 1280000) * t ^ 8 + (-7449338531 / 230400) * t ^ 10 + (705269497757 / 69120000) * t ^ 12 + (-21485389537 / 17280000) * t ^ 14 + (-12086034697 / 69120000) * t ^ 18 + (5207121841 / 34560000) * t ^ 20 + (45059 / 16) * d * t ^ 2 + (-3783479 / 1600) * d * t ^ 4 + (-1883792051 / 1152000) * d * t ^ 6 + (2089223659 / 2304000) * d * t ^ 8 + (22899137 / 192000) * d * t ^ 10 + (214015411 / 1536000) * d * t ^ 12 + (81294203 / 1152000) * d * t ^ 14 + (15269797 / 4608000) * d * t ^ 18 + (115523 / 384000) * d * t ^ 20 + (-24981997 / 240) * alpha * t ^ 2 + (956647813 / 4800) * alpha * t ^ 4 + (-664409717399 / 5760000) * alpha * t ^ 6 + (354411990619 / 11520000) * alpha * t ^ 8 + (-16986474533 / 1152000) * alpha * t ^ 10 + (162099401027 / 69120000) * alpha * t ^ 12 + (1435958297 / 1920000) * alpha * t ^ 14 + (478627499 / 2560000) * alpha * t ^ 18 + (-3225483169 / 34560000) * alpha * t ^ 20 + (19311 / 16) * alpha * d * t ^ 2 + (-12885083 / 14400) * alpha * d * t ^ 4 + (-3215211467 / 3456000) * alpha * d * t ^ 6 + (3231866723 / 6912000) * alpha * d * t ^ 8 + (140192609 / 576000) * alpha * d * t ^ 10 + (-260744477 / 4608000) * alpha * d * t ^ 12 + (12753227 / 3456000) * alpha * d * t ^ 14 + (-7126543 / 2764800) * alpha * d * t ^ 18 + (15727 / 1152000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_01, v33_02, v33_10, v33_11, v33_12, v33_20, v33_21, v33_22, v33_30, v33_31, v33_32, v33_40, v33_41, v33_42]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_10, phase32_11, phase32_12, phase32_20, phase32_21, phase32_22, phase32_30, phase32_31, phase32_32, phase32_40, phase32_41, phase32_42]
  try simp only [star_one, star_neg]
  linear_combination ((-32185 / 96) * t ^ 2 + (57671 / 225) * t ^ 4 + (278229067 / 1382400) * t ^ 6 + (3127748459 / 13824000) * t ^ 8 + (-2417873741 / 4608000) * t ^ 10 + (56590437107 / 331776000) * t ^ 12 + (569214209 / 82944000) * t ^ 14 + (778843313 / 331776000) * t ^ 18 + (-39785417 / 11059200) * t ^ 20 + (-45059 / 144) * d * t ^ 2 + (5984 / 25) * d * t ^ 4 + (42061319 / 230400) * d * t ^ 6 + (-14666143 / 153600) * d * t ^ 8 + (3122591 / 1382400) * d * t ^ 10 + (-13543763 / 768000) * d * t ^ 12 + (-34882457 / 5184000) * d * t ^ 14 + (-10964857 / 20736000) * d * t ^ 18 + (-18949 / 3456000) * d * t ^ 20 + (6437 / 288) * d ^ 2 * t ^ 2 + (-763 / 45) * d ^ 2 * t ^ 4 + (-25861153 / 1382400) * d ^ 2 * t ^ 6 + (26074663 / 2764800) * d ^ 2 * t ^ 8 + (3970547 / 921600) * d ^ 2 * t ^ 10 + (-2136143 / 66355200) * d ^ 2 * t ^ 12 + (-1344703 / 49766400) * d ^ 2 * t ^ 14 + (141305 / 7962624) * d ^ 2 * t ^ 18 + (-95 / 3981312) * d ^ 2 * t ^ 20) * alpha_sq + ((-6437 / 144) * t ^ 2 + (-518 / 45) * t ^ 4 + (400482341 / 3456000) * t ^ 6 + (-112489213 / 2304000) * t ^ 8 + (-87558029 / 6912000) * t ^ 10 + (119683087 / 165888000) * t ^ 12 + (-381607 / 8294400) * t ^ 14 + (-807083 / 165888000) * t ^ 18 + (-95 / 663552) * t ^ 20 + (-6437 / 144) * alpha * t ^ 2 + (794 / 15) * alpha * t ^ 4 + (17916511 / 3456000) * alpha * t ^ 6 + (-58210649 / 6912000) * alpha * t ^ 8 + (-13769093 / 2304000) * alpha * t ^ 10 + (-22572833 / 165888000) * alpha * t ^ 12 + (2080393 / 8294400) * alpha * t ^ 14 + (10722917 / 165888000) * alpha * t ^ 18 + (-95 / 663552) * alpha * t ^ 20) * d_sq
theorem v34_43 (t : ℂ) : (momentPoly 34 z34 4 3).eval t = ((2588457 / 16) * t + (4788381 / 160) * t ^ 3 + (-2020207843 / 8000) * t ^ 5 + (-4142369275733 / 19200000) * t ^ 7 + (3277516419569 / 9600000) * t ^ 9 + (-321410465677 / 12800000) * t ^ 11 + (-792185819749 / 15360000) * t ^ 13 + (2353521796711 / 115200000) * t ^ 15 + (-1010812850669 / 230400000) * t ^ 17 + (-904880209543 / 691200000) * t ^ 19 + (75987507079 / 153600000) * t ^ 21 + (88343334623 / 1382400000) * t ^ 25 + (-862819 / 16) * d * t + (22293753 / 160) * d * t ^ 3 + (-474307389 / 3200) * d * t ^ 5 + (73576740271 / 720000) * d * t ^ 7 + (-589306146823 / 11520000) * d * t ^ 9 + (30711615641 / 2880000) * d * t ^ 11 + (101768633707 / 138240000) * d * t ^ 13 + (4040804377 / 23040000) * d * t ^ 15 + (12766883 / 230400) * d * t ^ 17 + (4006571881 / 46080000) * d * t ^ 19 + (-8351315279 / 92160000) * d * t ^ 21 + (29621251 / 18432000) * d * t ^ 25 + (-25021751 / 48) * alpha * t + (91000049 / 160) * alpha * t ^ 3 + (10364968669 / 48000) * alpha * t ^ 5 + (-23105382349 / 112500) * alpha * t ^ 7 + (-3548419767197 / 57600000) * alpha * t ^ 9 + (123858375521 / 4800000) * alpha * t ^ 11 + (-6371968724039 / 138240000) * alpha * t ^ 13 + (5853664159381 / 345600000) * alpha * t ^ 15 + (943694216803 / 345600000) * alpha * t ^ 17 + (-830797801213 / 2073600000) * alpha * t ^ 19 + (291412701697 / 1382400000) * alpha * t ^ 21 + (293815324273 / 4147200000) * alpha * t ^ 25 + (862819 / 16) * alpha * d * t + (-13366263 / 160) * alpha * d * t ^ 3 + (33373 / 20) * alpha * d * t ^ 5 + (305676204809 / 11520000) * alpha * d * t ^ 7 + (414086131 / 40000) * alpha * d * t ^ 9 + (-138469648613 / 23040000) * alpha * d * t ^ 11 + (-369787688747 / 138240000) * alpha * d * t ^ 13 + (-930508709 / 7680000) * alpha * d * t ^ 15 + (21187703 / 614400) * alpha * d * t ^ 17 + (2919064427 / 138240000) * alpha * d * t ^ 19 + (-757653901 / 92160000) * alpha * d * t ^ 21 + (-14380003 / 55296000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_01, v33_02, v33_03, v33_10, v33_11, v33_12, v33_13, v33_20, v33_21, v33_22, v33_23, v33_30, v33_31, v33_32, v33_33, v33_40, v33_41, v33_42, v33_43]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_10, phase32_11, phase32_12, phase32_13, phase32_20, phase32_21, phase32_22, phase32_23, phase32_30, phase32_31, phase32_32, phase32_33, phase32_40, phase32_41, phase32_42, phase32_43]
  try simp only [star_one, star_neg]
  linear_combination ((6016171 / 1280) * t ^ 3 + (-215717323 / 9600) * t ^ 5 + (2288734912829 / 92160000) * t ^ 7 + (-79460461837 / 15360000) * t ^ 9 + (-2769740929 / 1536000) * t ^ 11 + (-445484481971 / 552960000) * t ^ 13 + (197041613167 / 276480000) * t ^ 15 + (-42731496977 / 221184000) * t ^ 17 + (-34360924067 / 1658880000) * t ^ 19 + (35148047363 / 1105920000) * t ^ 21 + (677354041 / 331776000) * t ^ 25 + (4467907 / 960) * d * t ^ 3 + (-281738891 / 28800) * d * t ^ 5 + (155856116111 / 23040000) * d * t ^ 7 + (-5980575077 / 2560000) * d * t ^ 9 + (10001221093 / 11059200) * d * t ^ 11 + (-115689131359 / 829440000) * d * t ^ 13 + (-7979606801 / 207360000) * d * t ^ 15 + (-617579 / 8192000) * d * t ^ 17 + (-22469858953 / 2488320000) * d * t ^ 19 + (18592300709 / 3317760000) * d * t ^ 21 + (741247 / 39813120) * d * t ^ 25 + (-35377 / 768) * d ^ 2 * t ^ 3 + (481639 / 14400) * d ^ 2 * t ^ 5 + (2558429209 / 55296000) * d ^ 2 * t ^ 7 + (-686177849 / 27648000) * d ^ 2 * t ^ 9 + (-649675043 / 55296000) * d ^ 2 * t ^ 11 + (51426697 / 22118400) * d ^ 2 * t ^ 13 + (-7342583 / 55296000) * d ^ 2 * t ^ 15 + (106321 / 33177600) * d ^ 2 * t ^ 17 + (39630689 / 331776000) * d ^ 2 * t ^ 19 + (-237931 / 82944000) * d ^ 2 * t ^ 21) * alpha_sq + ((35377 / 128) * t ^ 3 + (-10679509 / 38400) * t ^ 5 + (-45829023 / 256000) * t ^ 7 + (736983451 / 4608000) * t ^ 9 + (185784817 / 4608000) * t ^ 11 + (-226533037 / 13824000) * t ^ 13 + (556099 / 1152000) * t ^ 15 + (-475607 / 4915200) * t ^ 17 + (-16421213 / 33177600) * t ^ 19 + (-1729361 / 73728000) * t ^ 21 + (4465 / 2654208) * t ^ 25 + (-164399 / 384) * alpha * t ^ 3 + (53740511 / 115200) * alpha * t ^ 5 + (2387934607 / 13824000) * alpha * t ^ 7 + (-2386486141 / 13824000) * alpha * t ^ 9 + (-2778359 / 76800) * alpha * t ^ 11 + (-528677 / 16588800) * alpha * t ^ 13 + (-248471687 / 41472000) * alpha * t ^ 15 + (606737 / 132710400) * alpha * t ^ 17 + (685189 / 497664000) * alpha * t ^ 19 + (-18168083 / 663552000) * alpha * t ^ 21 + (4465 / 7962624) * alpha * t ^ 25) * d_sq
theorem v34_44 (t : ℂ) : (momentPoly 34 z34 4 4).eval t = (29335846 + (-236657330 / 3) * t ^ 2 + (31578941107 / 300) * t ^ 4 + (-14281552899091 / 120000) * t ^ 6 + (2317697767289701 / 24000000) * t ^ 8 + (-22332275037984421 / 576000000) * t ^ 10 + (200136990203333 / 25600000) * t ^ 12 + (-10380972764428271 / 3456000000) * t ^ 14 + (1707630238392103 / 2304000000) * t ^ 16 + (-469913946457 / 48000000) * t ^ 18 + (-411397921946729 / 20736000000) * t ^ 20 + (1268627228867 / 192000000) * t ^ 22 + (67821170842129 / 13824000000) * t ^ 24 + (-36809277050591 / 10368000000) * t ^ 26 + (7555824999533 / 41472000000) * t ^ 32 + (-824590) * d * t ^ 2 + (27268799 / 20) * d * t ^ 4 + (-58731541 / 960) * d * t ^ 6 + (-3578815032857 / 5760000) * d * t ^ 8 + (1300254169199 / 23040000) * d * t ^ 10 + (4311304752241 / 46080000) * d * t ^ 12 + (-4613888804683 / 138240000) * d * t ^ 14 + (1776681102083 / 92160000) * d * t ^ 16 + (501135269 / 76800) * d * t ^ 18 + (-77520567419 / 276480000) * d * t ^ 20 + (1051732979 / 23040000) * d * t ^ 22 + (68361623 / 36864000) * d * t ^ 24 + (2025534983 / 27648000) * d * t ^ 26 + (583775 / 884736) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z34, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v33_00, v33_01, v33_02, v33_03, v33_04, v33_10, v33_11, v33_12, v33_13, v33_14, v33_20, v33_21, v33_22, v33_23, v33_24, v33_30, v33_31, v33_32, v33_33, v33_34, v33_40, v33_41, v33_42, v33_43, v33_44]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_04, phase32_10, phase32_11, phase32_12, phase32_13, phase32_14, phase32_20, phase32_21, phase32_22, phase32_23, phase32_24, phase32_30, phase32_31, phase32_32, phase32_33, phase32_34, phase32_40, phase32_41, phase32_42, phase32_43, phase32_44]
  try simp only [star_one, star_neg]
  linear_combination ((2061475 / 24) * t ^ 2 + (-49882097 / 360) * t ^ 4 + (-246680078647 / 576000) * t ^ 6 + (181549155349009 / 172800000) * t ^ 8 + (-38599154367611 / 51200000) * t ^ 10 + (328674600666107 / 1382400000) * t ^ 12 + (-30333081139487 / 414720000) * t ^ 14 + (829953955109 / 57600000) * t ^ 16 + (13804668765419 / 4147200000) * t ^ 18 + (-596717199809 / 24883200000) * t ^ 20 + (1937080552051 / 1036800000) * t ^ 22 + (-58902874027 / 58982400) * t ^ 24 + (-747380217071 / 49766400000) * t ^ 26 + (8943413507 / 2654208000) * t ^ 32 + (2886065 / 36) * d * t ^ 2 + (-23238167 / 180) * d * t ^ 4 + (1828133573 / 96000) * d * t ^ 6 + (3071792425247 / 86400000) * d * t ^ 8 + (-2125579839221 / 691200000) * d * t ^ 10 + (-4893035732279 / 691200000) * d * t ^ 12 + (2508700557103 / 276480000) * d * t ^ 14 + (-15997846107527 / 4147200000) * d * t ^ 16 + (-351611511641 / 691200000) * d * t ^ 18 + (118356254611 / 1555200000) * d * t ^ 20 + (-232833035501 / 4147200000) * d * t ^ 22 + (-298635533 / 2211840000) * d * t ^ 24 + (-325097310323 / 24883200000) * d * t ^ 26 + (4663379 / 265420800) * d * t ^ 32 + (-412295 / 72) * d ^ 2 * t ^ 2 + (3405763 / 360) * d ^ 2 * t ^ 4 + (-56332843 / 115200) * d ^ 2 * t ^ 6 + (-343890842309 / 103680000) * d ^ 2 * t ^ 8 + (-312526220993 / 276480000) * d ^ 2 * t ^ 10 + (700305865037 / 829440000) * d ^ 2 * t ^ 12 + (95333319191 / 276480000) * d ^ 2 * t ^ 14 + (352525789 / 30720000) * d ^ 2 * t ^ 16 + (-2304348179 / 497664000) * d ^ 2 * t ^ 18 + (-10705917803 / 4976640000) * d ^ 2 * t ^ 20 + (1403616943 / 2488320000) * d ^ 2 * t ^ 22 + (-3410917 / 7962624000) * d ^ 2 * t ^ 24 + (181327811 / 5971968000) * d ^ 2 * t ^ 26 + (-9025 / 191102976) * d ^ 2 * t ^ 32) * alpha_sq + ((412295 / 18) * t ^ 2 + (-7908451 / 180) * t ^ 4 + (522370109 / 28800) * t ^ 6 + (-6917875633 / 5760000) * t ^ 8 + (1285324330411 / 138240000) * t ^ 10 + (-528677619893 / 138240000) * t ^ 12 + (-588053258771 / 414720000) * t ^ 14 + (2031173981 / 46080000) * t ^ 16 + (252479059 / 13824000) * t ^ 18 + (-9719250929 / 2488320000) * t ^ 20 + (73157257 / 7680000) * t ^ 22 + (-24706583 / 663552000) * t ^ 24 + (-295562399 / 497664000) * t ^ 26 + (9025 / 15925248) * t ^ 32) * d_sq
#print axioms v34_00
#print axioms v34_11
#print axioms v34_22
#print axioms v34_33
#print axioms v34_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
noncomputable def z35 : Fin 35 → ℂ := Fin.snoc z34 (r ^ 2 * phiPlus)
theorem v35_00 (t : ℂ) : (momentPoly 35 z35 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00]
  try simp only [phase32_00]
  try simp only [star_one, star_neg]
  ring
theorem v35_01 (t : ℂ) : (momentPoly 35 z35 0 1).eval t = ((1 / 4) * t + (-1 / 12) * d * t + (7 / 12) * alpha * t + (-1 / 12) * alpha * d * t) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_01]
  try simp only [phase32_00, phase32_01]
  try simp only [star_one, star_neg]
  ring
theorem v35_02 (t : ℂ) : (momentPoly 35 z35 0 2).eval t = ((-5453 / 240) * t ^ 2 + (3313 / 240) * t ^ 4 + (13 / 48) * d * t ^ 2 + (-1 / 48) * d * t ^ 4 + (891 / 80) * alpha * t ^ 2 + (-231 / 80) * alpha * t ^ 4 + (-19 / 144) * alpha * d * t ^ 2 + (-1 / 144) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_01, v34_02]
  try simp only [phase32_00, phase32_01, phase32_02]
  try simp only [star_one, star_neg]
  linear_combination ((-29 / 1152) * t ^ 2 + (-13 / 576) * d * t ^ 2 + (1 / 384) * d ^ 2 * t ^ 2) * alpha_sq + ((-1 / 192) * t ^ 2 + (1 / 192) * alpha * t ^ 2) * d_sq
theorem v35_03 (t : ℂ) : (momentPoly 35 z35 0 3).eval t = ((-5761 / 80) * t ^ 3 + (1801 / 80) * t ^ 5 + 1 * t ^ 9 + (271 / 30) * d * t ^ 3 + (-2921 / 480) * d * t ^ 5 + (47 / 288) * d * t ^ 9 + (-14147 / 600) * alpha * t ^ 3 + (23317 / 2400) * alpha * t ^ 5 + (39013 / 7200) * alpha * t ^ 9 + (47 / 16) * alpha * d * t ^ 3 + (-133 / 48) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_01, v34_02, v34_03]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03]
  try simp only [star_one, star_neg]
  linear_combination ((-3881 / 7680) * t ^ 3 + (2837 / 2560) * t ^ 5 + (-959 / 1920) * d * t ^ 3 + (667 / 5760) * d * t ^ 5 + (3 / 512) * d ^ 2 * t ^ 3 + (1 / 1536) * d ^ 2 * t ^ 5) * alpha_sq + ((-1 / 32) * t ^ 3 + (-1 / 128) * alpha * t ^ 3 + (1 / 384) * alpha * t ^ 5) * d_sq
theorem v35_04 (t : ℂ) : (momentPoly 35 z35 0 4).eval t = ((23862227 / 48000) * t ^ 4 + (-7750649 / 8000) * t ^ 6 + (43915037 / 96000) * t ^ 8 + (-8711983 / 72000) * t ^ 10 + (3808823 / 288000) * t ^ 16 + (-48517 / 9600) * d * t ^ 4 + (21869 / 4800) * d * t ^ 6 + (-2829 / 1280) * d * t ^ 8 + (73201 / 14400) * d * t ^ 10 + (95 / 2304) * d * t ^ 16 + (-63816953 / 48000) * alpha * t ^ 4 + (11360171 / 8000) * alpha * t ^ 6 + (-23647663 / 96000) * alpha * t ^ 8 + (-807481 / 24000) * alpha * t ^ 10 + (245441 / 96000) * alpha * t ^ 16 + (560077 / 28800) * alpha * d * t ^ 4 + (-52583 / 4800) * alpha * d * t ^ 6 + (-1993 / 11520) * alpha * d * t ^ 8 + (-73601 / 43200) * alpha * d * t ^ 10 + (-95 / 6912) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_01, v34_02, v34_03, v34_04]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_04]
  try simp only [star_one, star_neg]
  linear_combination ((8743 / 4800) * t ^ 4 + (5331329 / 230400) * t ^ 6 + (-61693 / 6144) * t ^ 8 + (-24401 / 172800) * t ^ 10 + (31397 / 19200) * d * t ^ 4 + (-121363 / 115200) * d * t ^ 6 + (911 / 46080) * d * t ^ 8 + (-81601 / 172800) * d * t ^ 10 + (-143 / 768) * d ^ 2 * t ^ 4 + (535 / 3072) * d ^ 2 * t ^ 6 + (1 / 18432) * d ^ 2 * t ^ 8) * alpha_sq + ((431 / 11520) * t ^ 4 + (-303 / 2560) * t ^ 6 + (1 / 3072) * t ^ 8 + (-47 / 2304) * t ^ 10 + (-8149 / 11520) * alpha * t ^ 4 + (1497 / 2560) * alpha * t ^ 6 + (1 / 3072) * alpha * t ^ 8 + (-47 / 2304) * alpha * t ^ 10) * d_sq
theorem v35_10 (t : ℂ) : (momentPoly 35 z35 1 0).eval t = ((1 / 4) * t + (-1 / 12) * d * t + (-7 / 12) * alpha * t + (1 / 12) * alpha * d * t) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_10]
  try simp only [phase32_00, phase32_10]
  try simp only [star_one, star_neg]
  ring
theorem v35_11 (t : ℂ) : (momentPoly 35 z35 1 1).eval t = (35 + (-18) * t ^ 2 + (-1 / 3) * d * t ^ 2) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_01, v34_10, v34_11]
  try simp only [phase32_00, phase32_01, phase32_10, phase32_11]
  try simp only [star_one, star_neg]
  linear_combination ((29 / 1152) * t ^ 2 + (13 / 576) * d * t ^ 2 + (-1 / 384) * d ^ 2 * t ^ 2) * alpha_sq + ((1 / 96) * t ^ 2) * d_sq
theorem v35_12 (t : ℂ) : (momentPoly 35 z35 1 2).eval t = ((69 / 4) * t + (667 / 240) * t ^ 3 + (11 / 80) * t ^ 5 + (-23 / 4) * d * t + (369 / 80) * d * t ^ 3 + (-29 / 80) * d * t ^ 5 + (161 / 4) * alpha * t + (-211 / 48) * alpha * t ^ 3 + (-481 / 48) * alpha * t ^ 5 + (-23 / 4) * alpha * d * t + (637 / 240) * alpha * d * t ^ 3 + (1069 / 720) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_01, v34_02, v34_10, v34_11, v34_12]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_10, phase32_11, phase32_12]
  try simp only [star_one, star_neg]
  linear_combination ((3881 / 23040) * t ^ 3 + (-2837 / 7680) * t ^ 5 + (959 / 5760) * d * t ^ 3 + (-667 / 17280) * d * t ^ 5 + (-1 / 512) * d ^ 2 * t ^ 3 + (-1 / 4608) * d ^ 2 * t ^ 5) * alpha_sq + ((3 / 256) * t ^ 3 + (1 / 768) * t ^ 5 + (13 / 768) * alpha * t ^ 3 + (-1 / 2304) * alpha * t ^ 5) * d_sq
theorem v35_13 (t : ℂ) : (momentPoly 35 z35 1 3).eval t = ((-92701 / 40) * t ^ 2 + (6623491 / 2400) * t ^ 4 + (-1007571 / 1600) * t ^ 6 + (-18983 / 1600) * t ^ 10 + (221 / 8) * d * t ^ 2 + (-7731 / 800) * d * t ^ 4 + (-44941 / 4800) * d * t ^ 6 + (-19819 / 14400) * d * t ^ 10 + (45441 / 40) * alpha * t ^ 2 + (-858269 / 800) * alpha * t ^ 4 + (442261 / 4800) * alpha * t ^ 6 + (164899 / 14400) * alpha * t ^ 10 + (-323 / 24) * alpha * d * t ^ 2 + (27187 / 7200) * alpha * d * t ^ 4 + (24133 / 4800) * alpha * d * t ^ 6 + (-2191 / 4800) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_01, v34_02, v34_03, v34_10, v34_11, v34_12, v34_13]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_10, phase32_11, phase32_12, phase32_13]
  try simp only [star_one, star_neg]
  linear_combination ((-493 / 192) * t ^ 2 + (113729 / 230400) * t ^ 4 + (21931 / 25600) * t ^ 6 + (24401 / 691200) * t ^ 10 + (-221 / 96) * d * t ^ 2 + (92339 / 230400) * d * t ^ 4 + (18941 / 25600) * d * t ^ 6 + (81601 / 691200) * d * t ^ 10 + (17 / 64) * d ^ 2 * t ^ 2 + (-713 / 7680) * d ^ 2 * t ^ 4 + (-299 / 2560) * d ^ 2 * t ^ 6) * alpha_sq + ((-17 / 32) * t ^ 2 + (-3883 / 46080) * t ^ 4 + (2407 / 5120) * t ^ 6 + (-47 / 9216) * t ^ 10 + (17 / 32) * alpha * t ^ 2 + (-13277 / 46080) * alpha * t ^ 4 + (-607 / 5120) * alpha * t ^ 6 + (47 / 9216) * alpha * t ^ 10) * d_sq
theorem v35_14 (t : ℂ) : (momentPoly 35 z35 1 4).eval t = ((-385987 / 40) * t ^ 3 + (360836939 / 48000) * t ^ 5 + (25319461 / 24000) * t ^ 7 + (-3021517 / 32000) * t ^ 9 + (-6091657 / 24000) * t ^ 11 + (1952771 / 288000) * t ^ 17 + (18157 / 15) * d * t ^ 3 + (-238479107 / 144000) * d * t ^ 5 + (10962569 / 24000) * d * t ^ 7 + (16454863 / 288000) * d * t ^ 9 + (194641 / 72000) * d * t ^ 11 + (-184147 / 96000) * d * t ^ 17 + (-947849 / 300) * alpha * t ^ 3 + (365839583 / 144000) * alpha * t ^ 5 + (4158673 / 8000) * alpha * t ^ 7 + (85593173 / 288000) * alpha * t ^ 9 + (-26179829 / 72000) * alpha * t ^ 11 + (-2842211 / 288000) * alpha * t ^ 17 + (3149 / 8) * alpha * d * t ^ 3 + (-17019517 / 28800) * alpha * d * t ^ 5 + (2068669 / 14400) * alpha * d * t ^ 7 + (753821 / 11520) * alpha * d * t ^ 9 + (-301379 / 43200) * alpha * d * t ^ 11 + (1985 / 2304) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_01, v34_02, v34_03, v34_04, v34_10, v34_11, v34_12, v34_13, v34_14]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_04, phase32_10, phase32_11, phase32_12, phase32_13, phase32_14]
  try simp only [star_one, star_neg]
  linear_combination ((-260027 / 3840) * t ^ 3 + (208698241 / 1152000) * t ^ 5 + (-171001903 / 4608000) * t ^ 7 + (-337858951 / 9216000) * t ^ 9 + (-8050471 / 6912000) * t ^ 11 + (3251507 / 9216000) * t ^ 17 + (-64253 / 960) * d * t ^ 3 + (13483879 / 288000) * d * t ^ 5 + (98219233 / 6912000) * d * t ^ 7 + (-36401839 / 13824000) * d * t ^ 9 + (-4017173 / 3456000) * d * t ^ 11 + (1457969 / 41472000) * d * t ^ 17 + (201 / 256) * d ^ 2 * t ^ 3 + (7033 / 138240) * d ^ 2 * t ^ 5 + (-11451 / 20480) * d ^ 2 * t ^ 7 + (-1055 / 73728) * d ^ 2 * t ^ 9 + (43 / 18432) * d ^ 2 * t ^ 11 + (-95 / 221184) * d ^ 2 * t ^ 17) * alpha_sq + ((-67 / 16) * t ^ 3 + (21667 / 23040) * t ^ 5 + (7933 / 3840) * t ^ 7 + (11 / 128) * t ^ 9 + (-23 / 576) * t ^ 11 + (-67 / 64) * alpha * t ^ 3 + (39139 / 115200) * alpha * t ^ 5 + (97643 / 230400) * alpha * t ^ 7 + (-2119 / 30720) * alpha * t ^ 9 + (24817 / 115200) * alpha * t ^ 11 + (95 / 55296) * alpha * t ^ 17) * d_sq
theorem v35_20 (t : ℂ) : (momentPoly 35 z35 2 0).eval t = ((-5453 / 240) * t ^ 2 + (3313 / 240) * t ^ 4 + (13 / 48) * d * t ^ 2 + (-1 / 48) * d * t ^ 4 + (-891 / 80) * alpha * t ^ 2 + (231 / 80) * alpha * t ^ 4 + (19 / 144) * alpha * d * t ^ 2 + (1 / 144) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_10, v34_20]
  try simp only [phase32_00, phase32_10, phase32_20]
  try simp only [star_one, star_neg]
  linear_combination ((-29 / 1152) * t ^ 2 + (-13 / 576) * d * t ^ 2 + (1 / 384) * d ^ 2 * t ^ 2) * alpha_sq + ((-1 / 192) * t ^ 2 + (-1 / 192) * alpha * t ^ 2) * d_sq
theorem v35_21 (t : ℂ) : (momentPoly 35 z35 2 1).eval t = ((69 / 4) * t + (667 / 240) * t ^ 3 + (11 / 80) * t ^ 5 + (-23 / 4) * d * t + (369 / 80) * d * t ^ 3 + (-29 / 80) * d * t ^ 5 + (-161 / 4) * alpha * t + (211 / 48) * alpha * t ^ 3 + (481 / 48) * alpha * t ^ 5 + (23 / 4) * alpha * d * t + (-637 / 240) * alpha * d * t ^ 3 + (-1069 / 720) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_01, v34_10, v34_11, v34_20, v34_21]
  try simp only [phase32_00, phase32_01, phase32_10, phase32_11, phase32_20, phase32_21]
  try simp only [star_one, star_neg]
  linear_combination ((3881 / 23040) * t ^ 3 + (-2837 / 7680) * t ^ 5 + (959 / 5760) * d * t ^ 3 + (-667 / 17280) * d * t ^ 5 + (-1 / 512) * d ^ 2 * t ^ 3 + (-1 / 4608) * d ^ 2 * t ^ 5) * alpha_sq + ((3 / 256) * t ^ 3 + (1 / 768) * t ^ 5 + (-13 / 768) * alpha * t ^ 3 + (1 / 2304) * alpha * t ^ 5) * d_sq
theorem v35_22 (t : ℂ) : (momentPoly 35 z35 2 2).eval t = (2415 + (-2448) * t ^ 2 + (2295179 / 2400) * t ^ 4 + (-300623 / 400) * t ^ 6 + (434159 / 2400) * t ^ 8 + (-136 / 3) * d * t ^ 2 + (32941 / 1440) * d * t ^ 4 + (2779 / 240) * d * t ^ 6 + (-131 / 288) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_01, v34_02, v34_10, v34_11, v34_12, v34_20, v34_21, v34_22]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_10, phase32_11, phase32_12, phase32_20, phase32_21, phase32_22]
  try simp only [star_one, star_neg]
  linear_combination ((493 / 144) * t ^ 2 + (-43729 / 34560) * t ^ 4 + (-1224169 / 138240) * t ^ 6 + (61693 / 18432) * t ^ 8 + (221 / 72) * d * t ^ 2 + (-18653 / 17280) * d * t ^ 4 + (-8783 / 13824) * d * t ^ 6 + (-911 / 138240) * d * t ^ 8 + (-17 / 48) * d ^ 2 * t ^ 2 + (2141 / 11520) * d ^ 2 * t ^ 4 + (4501 / 46080) * d ^ 2 * t ^ 6 + (-1 / 55296) * d ^ 2 * t ^ 8) * alpha_sq + ((17 / 12) * t ^ 2 + (-4997 / 5760) * t ^ 4 + (-1067 / 3840) * t ^ 6 + (1 / 4608) * t ^ 8) * d_sq
theorem v35_23 (t : ℂ) : (momentPoly 35 z35 2 3).eval t = ((7039 / 4) * t + (44689 / 80) * t ^ 3 + (-29026361 / 48000) * t ^ 5 + (-29544421 / 19200) * t ^ 7 + (29415887 / 96000) * t ^ 9 + (52811887 / 288000) * t ^ 11 + (-10175467 / 288000) * t ^ 13 + (-7039 / 12) * d * t + (74169 / 80) * d * t ^ 3 + (-1649451 / 3200) * d * t ^ 5 + (3771691 / 19200) * d * t ^ 7 + (-196169 / 3840) * d * t ^ 9 + (-279757 / 57600) * d * t ^ 11 + (126857 / 57600) * d * t ^ 13 + (49273 / 12) * alpha * t + (-14137 / 16) * alpha * t ^ 3 + (-126751183 / 48000) * alpha * t ^ 5 + (40681 / 3840) * alpha * t ^ 7 + (17140081 / 96000) * alpha * t ^ 9 + (-29338519 / 288000) * alpha * t ^ 11 + (22392299 / 288000) * alpha * t ^ 13 + (-7039 / 12) * alpha * d * t + (42679 / 80) * alpha * d * t ^ 3 + (4883327 / 28800) * alpha * d * t ^ 5 + (-1127857 / 11520) * alpha * d * t ^ 7 + (-596977 / 11520) * alpha * d * t ^ 9 + (-550813 / 172800) * alpha * d * t ^ 11 + (77521 / 172800) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_01, v34_02, v34_03, v34_10, v34_11, v34_12, v34_13, v34_20, v34_21, v34_22, v34_23]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_10, phase32_11, phase32_12, phase32_13, phase32_20, phase32_21, phase32_22, phase32_23]
  try simp only [star_one, star_neg]
  linear_combination ((260027 / 7680) * t ^ 3 + (-23085151 / 230400) * t ^ 5 + (12757447 / 307200) * t ^ 7 + (1858789 / 184320) * t ^ 9 + (-1835561 / 2764800) * t ^ 11 + (-405457 / 184320) * t ^ 13 + (64253 / 1920) * d * t ^ 3 + (-11365571 / 345600) * d * t ^ 5 + (10553371 / 2764800) * d * t ^ 7 + (-2081431 / 2764800) * d * t ^ 9 + (310897 / 921600) * d * t ^ 11 + (81601 / 8294400) * d * t ^ 13 + (-201 / 512) * d ^ 2 * t ^ 3 + (77911 / 691200) * d ^ 2 * t ^ 5 + (87839 / 460800) * d ^ 2 * t ^ 7 + (29 / 11520) * d ^ 2 * t ^ 9 + (-6473 / 460800) * d ^ 2 * t ^ 11) * alpha_sq + ((603 / 256) * t ^ 3 + (-236827 / 230400) * t ^ 5 + (-882443 / 921600) * t ^ 7 + (175 / 4096) * t ^ 9 + (86101 / 921600) * t ^ 11 + (-47 / 36864) * t ^ 13 + (871 / 256) * alpha * t ^ 3 + (-1223233 / 691200) * alpha * t ^ 5 + (-2920117 / 2764800) * alpha * t ^ 7 + (529 / 12288) * alpha * t ^ 9 + (-22567 / 921600) * alpha * t ^ 11 + (47 / 110592) * alpha * t ^ 13) * d_sq
theorem v35_24 (t : ℂ) : (momentPoly 35 z35 2 4).eval t = ((-9319177 / 30) * t ^ 2 + (218265999 / 400) * t ^ 4 + (-43637887729 / 160000) * t ^ 6 + (30143072111 / 480000) * t ^ 8 + (-2435634161 / 64000) * t ^ 10 + (3045768947 / 320000) * t ^ 12 + (-922215443 / 720000) * t ^ 14 + (-523627093 / 2880000) * t ^ 18 + (421291243 / 2880000) * t ^ 20 + (22217 / 6) * d * t ^ 2 + (-910067 / 400) * d * t ^ 4 + (-75996481 / 28800) * d * t ^ 6 + (5127499 / 4800) * d * t ^ 8 + (56041 / 900) * d * t ^ 10 + (49808257 / 288000) * d * t ^ 12 + (19996067 / 216000) * d * t ^ 14 + (1696181 / 432000) * d * t ^ 18 + (109523 / 288000) * d * t ^ 20 + (1522719 / 10) * alpha * t ^ 2 + (-97986603 / 400) * alpha * t ^ 4 + (148388571961 / 1440000) * alpha * t ^ 6 + (-30417247193 / 1440000) * alpha * t ^ 8 + (9990352457 / 576000) * alpha * t ^ 10 + (-15108047629 / 8640000) * alpha * t ^ 12 + (-69089433 / 80000) * alpha * t ^ 14 + (-654630827 / 2880000) * alpha * t ^ 18 + (662652211 / 8640000) * alpha * t ^ 20 + (-32471 / 18) * alpha * d * t ^ 2 + (435551 / 400) * alpha * d * t ^ 4 + (175512961 / 144000) * alpha * d * t ^ 6 + (-15157013 / 36000) * alpha * d * t ^ 8 + (-324829 / 1125) * alpha * d * t ^ 10 + (19283957 / 288000) * alpha * d * t ^ 12 + (-477067 / 72000) * alpha * d * t ^ 14 + (1383859 / 432000) * alpha * d * t ^ 18 + (-21727 / 864000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_01, v34_02, v34_03, v34_04, v34_10, v34_11, v34_12, v34_13, v34_14, v34_20, v34_21, v34_22, v34_23, v34_24]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_04, phase32_10, phase32_11, phase32_12, phase32_13, phase32_14, phase32_20, phase32_21, phase32_22, phase32_23, phase32_24]
  try simp only [star_one, star_neg]
  linear_combination ((-49561 / 144) * t ^ 2 + (1251019 / 9600) * t ^ 4 + (130122241 / 512000) * t ^ 6 + (1135812119 / 2764800) * t ^ 8 + (-11102315891 / 18432000) * t ^ 10 + (47409390269 / 331776000) * t ^ 12 + (832964959 / 82944000) * t ^ 14 + (225262571 / 66355200) * t ^ 18 + (-69080459 / 22118400) * t ^ 20 + (-22217 / 72) * d * t ^ 2 + (1015729 / 9600) * d * t ^ 4 + (1559903701 / 6912000) * d * t ^ 6 + (-284841517 / 6912000) * d * t ^ 8 + (8490761 / 864000) * d * t ^ 10 + (-196384381 / 13824000) * d * t ^ 12 + (-68598379 / 10368000) * d * t ^ 14 + (-3903073 / 8294400) * d * t ^ 18 + (-12949 / 3456000) * d * t ^ 20 + (1709 / 48) * d ^ 2 * t ^ 2 + (-7843 / 320) * d ^ 2 * t ^ 4 + (-78698621 / 2764800) * d ^ 2 * t ^ 6 + (21375413 / 1658880) * d ^ 2 * t ^ 8 + (64701061 / 11059200) * d ^ 2 * t ^ 10 + (-859507 / 22118400) * d ^ 2 * t ^ 12 + (-195713 / 5529600) * d ^ 2 * t ^ 14 + (2615 / 98304) * d ^ 2 * t ^ 18 + (-95 / 2654208) * d ^ 2 * t ^ 20) * alpha_sq + ((-1709 / 24) * t ^ 2 + (-42713 / 1920) * t ^ 4 + (400128161 / 2304000) * t ^ 6 + (-156468487 / 2304000) * t ^ 8 + (-158128283 / 9216000) * t ^ 10 + (55964971 / 55296000) * t ^ 12 + (-82997 / 921600) * t ^ 14 + (-76831 / 6144000) * t ^ 18 + (-95 / 442368) * t ^ 20 + (1709 / 24) * alpha * t ^ 2 + (-146047 / 1920) * alpha * t ^ 4 + (-2114359 / 256000) * alpha * t ^ 6 + (59351051 / 6912000) * alpha * t ^ 8 + (72435283 / 9216000) * alpha * t ^ 10 + (16694989 / 55296000) * alpha * t ^ 12 + (-982009 / 2764800) * alpha * t ^ 14 + (-5073521 / 55296000) * alpha * t ^ 18 + (95 / 442368) * alpha * t ^ 20) * d_sq
theorem v35_30 (t : ℂ) : (momentPoly 35 z35 3 0).eval t = ((-5761 / 80) * t ^ 3 + (1801 / 80) * t ^ 5 + 1 * t ^ 9 + (271 / 30) * d * t ^ 3 + (-2921 / 480) * d * t ^ 5 + (47 / 288) * d * t ^ 9 + (14147 / 600) * alpha * t ^ 3 + (-23317 / 2400) * alpha * t ^ 5 + (-39013 / 7200) * alpha * t ^ 9 + (-47 / 16) * alpha * d * t ^ 3 + (133 / 48) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_10, v34_20, v34_30]
  try simp only [phase32_00, phase32_10, phase32_20, phase32_30]
  try simp only [star_one, star_neg]
  linear_combination ((-3881 / 7680) * t ^ 3 + (2837 / 2560) * t ^ 5 + (-959 / 1920) * d * t ^ 3 + (667 / 5760) * d * t ^ 5 + (3 / 512) * d ^ 2 * t ^ 3 + (1 / 1536) * d ^ 2 * t ^ 5) * alpha_sq + ((-1 / 32) * t ^ 3 + (1 / 128) * alpha * t ^ 3 + (-1 / 384) * alpha * t ^ 5) * d_sq
theorem v35_31 (t : ℂ) : (momentPoly 35 z35 3 1).eval t = ((-92701 / 40) * t ^ 2 + (6623491 / 2400) * t ^ 4 + (-1007571 / 1600) * t ^ 6 + (-18983 / 1600) * t ^ 10 + (221 / 8) * d * t ^ 2 + (-7731 / 800) * d * t ^ 4 + (-44941 / 4800) * d * t ^ 6 + (-19819 / 14400) * d * t ^ 10 + (-45441 / 40) * alpha * t ^ 2 + (858269 / 800) * alpha * t ^ 4 + (-442261 / 4800) * alpha * t ^ 6 + (-164899 / 14400) * alpha * t ^ 10 + (323 / 24) * alpha * d * t ^ 2 + (-27187 / 7200) * alpha * d * t ^ 4 + (-24133 / 4800) * alpha * d * t ^ 6 + (2191 / 4800) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_01, v34_10, v34_11, v34_20, v34_21, v34_30, v34_31]
  try simp only [phase32_00, phase32_01, phase32_10, phase32_11, phase32_20, phase32_21, phase32_30, phase32_31]
  try simp only [star_one, star_neg]
  linear_combination ((-493 / 192) * t ^ 2 + (113729 / 230400) * t ^ 4 + (21931 / 25600) * t ^ 6 + (24401 / 691200) * t ^ 10 + (-221 / 96) * d * t ^ 2 + (92339 / 230400) * d * t ^ 4 + (18941 / 25600) * d * t ^ 6 + (81601 / 691200) * d * t ^ 10 + (17 / 64) * d ^ 2 * t ^ 2 + (-713 / 7680) * d ^ 2 * t ^ 4 + (-299 / 2560) * d ^ 2 * t ^ 6) * alpha_sq + ((-17 / 32) * t ^ 2 + (-3883 / 46080) * t ^ 4 + (2407 / 5120) * t ^ 6 + (-47 / 9216) * t ^ 10 + (-17 / 32) * alpha * t ^ 2 + (13277 / 46080) * alpha * t ^ 4 + (607 / 5120) * alpha * t ^ 6 + (-47 / 9216) * alpha * t ^ 10) * d_sq
theorem v35_32 (t : ℂ) : (momentPoly 35 z35 3 2).eval t = ((7039 / 4) * t + (44689 / 80) * t ^ 3 + (-29026361 / 48000) * t ^ 5 + (-29544421 / 19200) * t ^ 7 + (29415887 / 96000) * t ^ 9 + (52811887 / 288000) * t ^ 11 + (-10175467 / 288000) * t ^ 13 + (-7039 / 12) * d * t + (74169 / 80) * d * t ^ 3 + (-1649451 / 3200) * d * t ^ 5 + (3771691 / 19200) * d * t ^ 7 + (-196169 / 3840) * d * t ^ 9 + (-279757 / 57600) * d * t ^ 11 + (126857 / 57600) * d * t ^ 13 + (-49273 / 12) * alpha * t + (14137 / 16) * alpha * t ^ 3 + (126751183 / 48000) * alpha * t ^ 5 + (-40681 / 3840) * alpha * t ^ 7 + (-17140081 / 96000) * alpha * t ^ 9 + (29338519 / 288000) * alpha * t ^ 11 + (-22392299 / 288000) * alpha * t ^ 13 + (7039 / 12) * alpha * d * t + (-42679 / 80) * alpha * d * t ^ 3 + (-4883327 / 28800) * alpha * d * t ^ 5 + (1127857 / 11520) * alpha * d * t ^ 7 + (596977 / 11520) * alpha * d * t ^ 9 + (550813 / 172800) * alpha * d * t ^ 11 + (-77521 / 172800) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_01, v34_02, v34_10, v34_11, v34_12, v34_20, v34_21, v34_22, v34_30, v34_31, v34_32]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_10, phase32_11, phase32_12, phase32_20, phase32_21, phase32_22, phase32_30, phase32_31, phase32_32]
  try simp only [star_one, star_neg]
  linear_combination ((260027 / 7680) * t ^ 3 + (-23085151 / 230400) * t ^ 5 + (12757447 / 307200) * t ^ 7 + (1858789 / 184320) * t ^ 9 + (-1835561 / 2764800) * t ^ 11 + (-405457 / 184320) * t ^ 13 + (64253 / 1920) * d * t ^ 3 + (-11365571 / 345600) * d * t ^ 5 + (10553371 / 2764800) * d * t ^ 7 + (-2081431 / 2764800) * d * t ^ 9 + (310897 / 921600) * d * t ^ 11 + (81601 / 8294400) * d * t ^ 13 + (-201 / 512) * d ^ 2 * t ^ 3 + (77911 / 691200) * d ^ 2 * t ^ 5 + (87839 / 460800) * d ^ 2 * t ^ 7 + (29 / 11520) * d ^ 2 * t ^ 9 + (-6473 / 460800) * d ^ 2 * t ^ 11) * alpha_sq + ((603 / 256) * t ^ 3 + (-236827 / 230400) * t ^ 5 + (-882443 / 921600) * t ^ 7 + (175 / 4096) * t ^ 9 + (86101 / 921600) * t ^ 11 + (-47 / 36864) * t ^ 13 + (-871 / 256) * alpha * t ^ 3 + (1223233 / 691200) * alpha * t ^ 5 + (2920117 / 2764800) * alpha * t ^ 7 + (-529 / 12288) * alpha * t ^ 9 + (22567 / 921600) * alpha * t ^ 11 + (-47 / 110592) * alpha * t ^ 13) * d_sq
theorem v35_33 (t : ℂ) : (momentPoly 35 z35 3 3).eval t = (246365 + (-369144) * t ^ 2 + (227222721 / 800) * t ^ 4 + (-12692546747 / 40000) * t ^ 6 + (14386723667 / 80000) * t ^ 8 + (-678320807 / 40000) * t ^ 10 + (242681421 / 80000) * t ^ 12 + (-421107817 / 240000) * t ^ 14 + (16641577 / 240000) * t ^ 18 + (-6836) * d * t ^ 2 + (1087053 / 160) * d * t ^ 4 + (8212019 / 4800) * d * t ^ 6 + (-5254347 / 3200) * d * t ^ 8 + (-968427 / 3200) * d * t ^ 10 + (1593379 / 28800) * d * t ^ 12 + (-288563 / 3200) * d * t ^ 14 + (47 / 144) * d * t ^ 18) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_01, v34_02, v34_03, v34_10, v34_11, v34_12, v34_13, v34_20, v34_21, v34_22, v34_23, v34_30, v34_31, v34_32, v34_33]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_10, phase32_11, phase32_12, phase32_13, phase32_20, phase32_21, phase32_22, phase32_23, phase32_30, phase32_31, phase32_32, phase32_33]
  try simp only [star_one, star_neg]
  linear_combination ((49561 / 96) * t ^ 2 + (-481019 / 1280) * t ^ 4 + (-5986807913 / 2304000) * t ^ 6 + (2656131953 / 921600) * t ^ 8 + (-641860601 / 1152000) * t ^ 10 + (-36818317 / 6912000) * t ^ 12 + (-77995247 / 4608000) * t ^ 14 + (-21804211 / 16588800) * t ^ 18 + (22217 / 48) * d * t ^ 2 + (-205183 / 640) * d * t ^ 4 + (-113546221 / 768000) * d * t ^ 6 + (9348659 / 230400) * d * t ^ 8 + (21633433 / 2304000) * d * t ^ 10 + (-79965577 / 6912000) * d * t ^ 12 + (79539647 / 6912000) * d * t ^ 14 + (-1709 / 32) * d ^ 2 * t ^ 2 + (70653 / 1280) * d ^ 2 * t ^ 4 + (127957 / 9216) * d ^ 2 * t ^ 6 + (-32657927 / 2764800) * d ^ 2 * t ^ 8 + (-2501239 / 460800) * d ^ 2 * t ^ 10 + (-80249 / 307200) * d ^ 2 * t ^ 12 + (10681 / 230400) * d ^ 2 * t ^ 14) * alpha_sq + ((1709 / 8) * t ^ 2 + (-164901 / 640) * t ^ 4 + (4269829 / 460800) * t ^ 6 + (4301887 / 230400) * t ^ 8 + (3364091 / 153600) * t ^ 10 + (4710991 / 2764800) * t ^ 12 + (-222403 / 307200) * t ^ 14 + (2209 / 221184) * t ^ 18) * d_sq
theorem v35_34 (t : ℂ) : (momentPoly 35 z35 3 4).eval t = ((943637 / 4) * t + (1106553 / 10) * t ^ 3 + (-385825673 / 1600) * t ^ 5 + (-5404025433539 / 9600000) * t ^ 7 + (10050230693623 / 19200000) * t ^ 9 + (-4951447281 / 6400000) * t ^ 11 + (-284851998503 / 4608000) * t ^ 13 + (22092962671 / 1200000) * t ^ 15 + (-432488821097 / 115200000) * t ^ 17 + (-280723334287 / 172800000) * t ^ 19 + (46024446023 / 115200000) * t ^ 21 + (20179795637 / 345600000) * t ^ 25 + (-943637 / 12) * d * t + (1836513 / 10) * d * t ^ 3 + (-11971149 / 64) * d * t ^ 5 + (259812621143 / 1920000) * d * t ^ 7 + (-254431670203 / 3840000) * d * t ^ 9 + (42400521719 / 3840000) * d * t ^ 11 + (18269390371 / 23040000) * d * t ^ 13 + (215507503 / 720000) * d * t ^ 15 + (22058687 / 307200) * d * t ^ 17 + (3965304611 / 34560000) * d * t ^ 19 + (-2458931963 / 23040000) * d * t ^ 21 + (28469251 / 13824000) * d * t ^ 25 + (6605459 / 12) * alpha * t + (-350049 / 2) * alpha * t ^ 3 + (-1029536079 / 1600) * alpha * t ^ 5 + (299020043181 / 3200000) * alpha * t ^ 7 + (3030211077529 / 19200000) * alpha * t ^ 9 + (-2352064529 / 19200000) * alpha * t ^ 11 + (1151183633027 / 23040000) * alpha * t ^ 13 + (-6575361161 / 600000) * alpha * t ^ 15 + (-102952449317 / 38400000) * alpha * t ^ 17 + (63091638139 / 172800000) * alpha * t ^ 19 + (-18516181271 / 115200000) * alpha * t ^ 21 + (-24527788829 / 345600000) * alpha * t ^ 25 + (-943637 / 12) * alpha * d * t + (1056783 / 10) * alpha * d * t ^ 3 + (8523823 / 960) * alpha * d * t ^ 5 + (-167500080061 / 5760000) * alpha * d * t ^ 7 + (-20447182651 / 1280000) * alpha * d * t ^ 9 + (19562228329 / 3840000) * alpha * d * t ^ 11 + (207952237643 / 69120000) * alpha * d * t ^ 13 + (79705339 / 360000) * alpha * d * t ^ 15 + (-103141763 / 2764800) * alpha * d * t ^ 17 + (-3051146857 / 103680000) * alpha * d * t ^ 19 + (1007494541 / 69120000) * alpha * d * t ^ 21 + (10924003 / 41472000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_01, v34_02, v34_03, v34_04, v34_10, v34_11, v34_12, v34_13, v34_14, v34_20, v34_21, v34_22, v34_23, v34_24, v34_30, v34_31, v34_32, v34_33, v34_34]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_04, phase32_10, phase32_11, phase32_12, phase32_13, phase32_14, phase32_20, phase32_21, phase32_22, phase32_23, phase32_24, phase32_30, phase32_31, phase32_32, phase32_33, phase32_34]
  try simp only [star_one, star_neg]
  linear_combination ((2146193 / 320) * t ^ 3 + (-4767877 / 192) * t ^ 5 + (626672989333 / 30720000) * t ^ 7 + (-73173060011 / 46080000) * t ^ 9 + (-11577020741 / 9216000) * t ^ 11 + (-36614344429 / 61440000) * t ^ 13 + (370614357799 / 552960000) * t ^ 15 + (-43564510477 / 221184000) * t ^ 17 + (-77366052659 / 3317760000) * t ^ 19 + (30871903913 / 1105920000) * t ^ 21 + (53098591 / 24576000) * t ^ 25 + (530327 / 80) * d * t ^ 3 + (-43535507 / 3840) * d * t ^ 5 + (382339586333 / 69120000) * d * t ^ 7 + (-3460024697 / 2160000) * d * t ^ 9 + (11320790717 / 11059200) * d * t ^ 11 + (-38040840157 / 414720000) * d * t ^ 13 + (-62264828113 / 1658880000) * d * t ^ 15 + (-232794149 / 663552000) * d * t ^ 17 + (-11288646173 / 1105920000) * d * t ^ 19 + (12782403379 / 3317760000) * d * t ^ 21 + (1550419 / 79626240) * d * t ^ 25 + (-4977 / 64) * d ^ 2 * t ^ 3 + (602819 / 11520) * d ^ 2 * t ^ 5 + (3610893947 / 55296000) * d ^ 2 * t ^ 7 + (-842050657 / 27648000) * d ^ 2 * t ^ 9 + (-866081609 / 55296000) * d ^ 2 * t ^ 11 + (123783451 / 36864000) * d ^ 2 * t ^ 13 + (-15428107 / 55296000) * d ^ 2 * t ^ 15 + (91921 / 22118400) * d ^ 2 * t ^ 17 + (933271 / 5529600) * d ^ 2 * t ^ 19 + (-255931 / 55296000) * d ^ 2 * t ^ 21) * alpha_sq + ((14931 / 32) * t ^ 3 + (-3464341 / 7680) * t ^ 5 + (-7464451 / 32000) * t ^ 7 + (368792479 / 1843200) * t ^ 9 + (21269867 / 384000) * t ^ 11 + (-145311929 / 6144000) * t ^ 13 + (40117657 / 36864000) * t ^ 15 + (-2026819 / 14745600) * t ^ 17 + (-151461911 / 221184000) * t ^ 19 + (-2311979 / 73728000) * t ^ 21 + (4465 / 1769472) * t ^ 25 + (21567 / 32) * alpha * t ^ 3 + (-15516439 / 23040) * alpha * t ^ 5 + (-727260563 / 2764800) * alpha * t ^ 7 + (2091650317 / 9216000) * alpha * t ^ 9 + (590893189 / 13824000) * alpha * t ^ 11 + (31623529 / 165888000) * alpha * t ^ 13 + (1016374343 / 110592000) * alpha * t ^ 15 + (-46309 / 4915200) * alpha * t ^ 17 + (-9517097 / 663552000) * alpha * t ^ 19 + (2933993 / 73728000) * alpha * t ^ 21 + (-4465 / 5308416) * alpha * t ^ 25) * d_sq
theorem v35_40 (t : ℂ) : (momentPoly 35 z35 4 0).eval t = ((23862227 / 48000) * t ^ 4 + (-7750649 / 8000) * t ^ 6 + (43915037 / 96000) * t ^ 8 + (-8711983 / 72000) * t ^ 10 + (3808823 / 288000) * t ^ 16 + (-48517 / 9600) * d * t ^ 4 + (21869 / 4800) * d * t ^ 6 + (-2829 / 1280) * d * t ^ 8 + (73201 / 14400) * d * t ^ 10 + (95 / 2304) * d * t ^ 16 + (63816953 / 48000) * alpha * t ^ 4 + (-11360171 / 8000) * alpha * t ^ 6 + (23647663 / 96000) * alpha * t ^ 8 + (807481 / 24000) * alpha * t ^ 10 + (-245441 / 96000) * alpha * t ^ 16 + (-560077 / 28800) * alpha * d * t ^ 4 + (52583 / 4800) * alpha * d * t ^ 6 + (1993 / 11520) * alpha * d * t ^ 8 + (73601 / 43200) * alpha * d * t ^ 10 + (95 / 6912) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_10, v34_20, v34_30, v34_40]
  try simp only [phase32_00, phase32_10, phase32_20, phase32_30, phase32_40]
  try simp only [star_one, star_neg]
  linear_combination ((8743 / 4800) * t ^ 4 + (5331329 / 230400) * t ^ 6 + (-61693 / 6144) * t ^ 8 + (-24401 / 172800) * t ^ 10 + (31397 / 19200) * d * t ^ 4 + (-121363 / 115200) * d * t ^ 6 + (911 / 46080) * d * t ^ 8 + (-81601 / 172800) * d * t ^ 10 + (-143 / 768) * d ^ 2 * t ^ 4 + (535 / 3072) * d ^ 2 * t ^ 6 + (1 / 18432) * d ^ 2 * t ^ 8) * alpha_sq + ((431 / 11520) * t ^ 4 + (-303 / 2560) * t ^ 6 + (1 / 3072) * t ^ 8 + (-47 / 2304) * t ^ 10 + (8149 / 11520) * alpha * t ^ 4 + (-1497 / 2560) * alpha * t ^ 6 + (-1 / 3072) * alpha * t ^ 8 + (47 / 2304) * alpha * t ^ 10) * d_sq
theorem v35_41 (t : ℂ) : (momentPoly 35 z35 4 1).eval t = ((-385987 / 40) * t ^ 3 + (360836939 / 48000) * t ^ 5 + (25319461 / 24000) * t ^ 7 + (-3021517 / 32000) * t ^ 9 + (-6091657 / 24000) * t ^ 11 + (1952771 / 288000) * t ^ 17 + (18157 / 15) * d * t ^ 3 + (-238479107 / 144000) * d * t ^ 5 + (10962569 / 24000) * d * t ^ 7 + (16454863 / 288000) * d * t ^ 9 + (194641 / 72000) * d * t ^ 11 + (-184147 / 96000) * d * t ^ 17 + (947849 / 300) * alpha * t ^ 3 + (-365839583 / 144000) * alpha * t ^ 5 + (-4158673 / 8000) * alpha * t ^ 7 + (-85593173 / 288000) * alpha * t ^ 9 + (26179829 / 72000) * alpha * t ^ 11 + (2842211 / 288000) * alpha * t ^ 17 + (-3149 / 8) * alpha * d * t ^ 3 + (17019517 / 28800) * alpha * d * t ^ 5 + (-2068669 / 14400) * alpha * d * t ^ 7 + (-753821 / 11520) * alpha * d * t ^ 9 + (301379 / 43200) * alpha * d * t ^ 11 + (-1985 / 2304) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_01, v34_10, v34_11, v34_20, v34_21, v34_30, v34_31, v34_40, v34_41]
  try simp only [phase32_00, phase32_01, phase32_10, phase32_11, phase32_20, phase32_21, phase32_30, phase32_31, phase32_40, phase32_41]
  try simp only [star_one, star_neg]
  linear_combination ((-260027 / 3840) * t ^ 3 + (208698241 / 1152000) * t ^ 5 + (-171001903 / 4608000) * t ^ 7 + (-337858951 / 9216000) * t ^ 9 + (-8050471 / 6912000) * t ^ 11 + (3251507 / 9216000) * t ^ 17 + (-64253 / 960) * d * t ^ 3 + (13483879 / 288000) * d * t ^ 5 + (98219233 / 6912000) * d * t ^ 7 + (-36401839 / 13824000) * d * t ^ 9 + (-4017173 / 3456000) * d * t ^ 11 + (1457969 / 41472000) * d * t ^ 17 + (201 / 256) * d ^ 2 * t ^ 3 + (7033 / 138240) * d ^ 2 * t ^ 5 + (-11451 / 20480) * d ^ 2 * t ^ 7 + (-1055 / 73728) * d ^ 2 * t ^ 9 + (43 / 18432) * d ^ 2 * t ^ 11 + (-95 / 221184) * d ^ 2 * t ^ 17) * alpha_sq + ((-67 / 16) * t ^ 3 + (21667 / 23040) * t ^ 5 + (7933 / 3840) * t ^ 7 + (11 / 128) * t ^ 9 + (-23 / 576) * t ^ 11 + (67 / 64) * alpha * t ^ 3 + (-39139 / 115200) * alpha * t ^ 5 + (-97643 / 230400) * alpha * t ^ 7 + (2119 / 30720) * alpha * t ^ 9 + (-24817 / 115200) * alpha * t ^ 11 + (-95 / 55296) * alpha * t ^ 17) * d_sq
theorem v35_42 (t : ℂ) : (momentPoly 35 z35 4 2).eval t = ((-9319177 / 30) * t ^ 2 + (218265999 / 400) * t ^ 4 + (-43637887729 / 160000) * t ^ 6 + (30143072111 / 480000) * t ^ 8 + (-2435634161 / 64000) * t ^ 10 + (3045768947 / 320000) * t ^ 12 + (-922215443 / 720000) * t ^ 14 + (-523627093 / 2880000) * t ^ 18 + (421291243 / 2880000) * t ^ 20 + (22217 / 6) * d * t ^ 2 + (-910067 / 400) * d * t ^ 4 + (-75996481 / 28800) * d * t ^ 6 + (5127499 / 4800) * d * t ^ 8 + (56041 / 900) * d * t ^ 10 + (49808257 / 288000) * d * t ^ 12 + (19996067 / 216000) * d * t ^ 14 + (1696181 / 432000) * d * t ^ 18 + (109523 / 288000) * d * t ^ 20 + (-1522719 / 10) * alpha * t ^ 2 + (97986603 / 400) * alpha * t ^ 4 + (-148388571961 / 1440000) * alpha * t ^ 6 + (30417247193 / 1440000) * alpha * t ^ 8 + (-9990352457 / 576000) * alpha * t ^ 10 + (15108047629 / 8640000) * alpha * t ^ 12 + (69089433 / 80000) * alpha * t ^ 14 + (654630827 / 2880000) * alpha * t ^ 18 + (-662652211 / 8640000) * alpha * t ^ 20 + (32471 / 18) * alpha * d * t ^ 2 + (-435551 / 400) * alpha * d * t ^ 4 + (-175512961 / 144000) * alpha * d * t ^ 6 + (15157013 / 36000) * alpha * d * t ^ 8 + (324829 / 1125) * alpha * d * t ^ 10 + (-19283957 / 288000) * alpha * d * t ^ 12 + (477067 / 72000) * alpha * d * t ^ 14 + (-1383859 / 432000) * alpha * d * t ^ 18 + (21727 / 864000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_01, v34_02, v34_10, v34_11, v34_12, v34_20, v34_21, v34_22, v34_30, v34_31, v34_32, v34_40, v34_41, v34_42]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_10, phase32_11, phase32_12, phase32_20, phase32_21, phase32_22, phase32_30, phase32_31, phase32_32, phase32_40, phase32_41, phase32_42]
  try simp only [star_one, star_neg]
  linear_combination ((-49561 / 144) * t ^ 2 + (1251019 / 9600) * t ^ 4 + (130122241 / 512000) * t ^ 6 + (1135812119 / 2764800) * t ^ 8 + (-11102315891 / 18432000) * t ^ 10 + (47409390269 / 331776000) * t ^ 12 + (832964959 / 82944000) * t ^ 14 + (225262571 / 66355200) * t ^ 18 + (-69080459 / 22118400) * t ^ 20 + (-22217 / 72) * d * t ^ 2 + (1015729 / 9600) * d * t ^ 4 + (1559903701 / 6912000) * d * t ^ 6 + (-284841517 / 6912000) * d * t ^ 8 + (8490761 / 864000) * d * t ^ 10 + (-196384381 / 13824000) * d * t ^ 12 + (-68598379 / 10368000) * d * t ^ 14 + (-3903073 / 8294400) * d * t ^ 18 + (-12949 / 3456000) * d * t ^ 20 + (1709 / 48) * d ^ 2 * t ^ 2 + (-7843 / 320) * d ^ 2 * t ^ 4 + (-78698621 / 2764800) * d ^ 2 * t ^ 6 + (21375413 / 1658880) * d ^ 2 * t ^ 8 + (64701061 / 11059200) * d ^ 2 * t ^ 10 + (-859507 / 22118400) * d ^ 2 * t ^ 12 + (-195713 / 5529600) * d ^ 2 * t ^ 14 + (2615 / 98304) * d ^ 2 * t ^ 18 + (-95 / 2654208) * d ^ 2 * t ^ 20) * alpha_sq + ((-1709 / 24) * t ^ 2 + (-42713 / 1920) * t ^ 4 + (400128161 / 2304000) * t ^ 6 + (-156468487 / 2304000) * t ^ 8 + (-158128283 / 9216000) * t ^ 10 + (55964971 / 55296000) * t ^ 12 + (-82997 / 921600) * t ^ 14 + (-76831 / 6144000) * t ^ 18 + (-95 / 442368) * t ^ 20 + (-1709 / 24) * alpha * t ^ 2 + (146047 / 1920) * alpha * t ^ 4 + (2114359 / 256000) * alpha * t ^ 6 + (-59351051 / 6912000) * alpha * t ^ 8 + (-72435283 / 9216000) * alpha * t ^ 10 + (-16694989 / 55296000) * alpha * t ^ 12 + (982009 / 2764800) * alpha * t ^ 14 + (5073521 / 55296000) * alpha * t ^ 18 + (-95 / 442368) * alpha * t ^ 20) * d_sq
theorem v35_43 (t : ℂ) : (momentPoly 35 z35 4 3).eval t = ((943637 / 4) * t + (1106553 / 10) * t ^ 3 + (-385825673 / 1600) * t ^ 5 + (-5404025433539 / 9600000) * t ^ 7 + (10050230693623 / 19200000) * t ^ 9 + (-4951447281 / 6400000) * t ^ 11 + (-284851998503 / 4608000) * t ^ 13 + (22092962671 / 1200000) * t ^ 15 + (-432488821097 / 115200000) * t ^ 17 + (-280723334287 / 172800000) * t ^ 19 + (46024446023 / 115200000) * t ^ 21 + (20179795637 / 345600000) * t ^ 25 + (-943637 / 12) * d * t + (1836513 / 10) * d * t ^ 3 + (-11971149 / 64) * d * t ^ 5 + (259812621143 / 1920000) * d * t ^ 7 + (-254431670203 / 3840000) * d * t ^ 9 + (42400521719 / 3840000) * d * t ^ 11 + (18269390371 / 23040000) * d * t ^ 13 + (215507503 / 720000) * d * t ^ 15 + (22058687 / 307200) * d * t ^ 17 + (3965304611 / 34560000) * d * t ^ 19 + (-2458931963 / 23040000) * d * t ^ 21 + (28469251 / 13824000) * d * t ^ 25 + (-6605459 / 12) * alpha * t + (350049 / 2) * alpha * t ^ 3 + (1029536079 / 1600) * alpha * t ^ 5 + (-299020043181 / 3200000) * alpha * t ^ 7 + (-3030211077529 / 19200000) * alpha * t ^ 9 + (2352064529 / 19200000) * alpha * t ^ 11 + (-1151183633027 / 23040000) * alpha * t ^ 13 + (6575361161 / 600000) * alpha * t ^ 15 + (102952449317 / 38400000) * alpha * t ^ 17 + (-63091638139 / 172800000) * alpha * t ^ 19 + (18516181271 / 115200000) * alpha * t ^ 21 + (24527788829 / 345600000) * alpha * t ^ 25 + (943637 / 12) * alpha * d * t + (-1056783 / 10) * alpha * d * t ^ 3 + (-8523823 / 960) * alpha * d * t ^ 5 + (167500080061 / 5760000) * alpha * d * t ^ 7 + (20447182651 / 1280000) * alpha * d * t ^ 9 + (-19562228329 / 3840000) * alpha * d * t ^ 11 + (-207952237643 / 69120000) * alpha * d * t ^ 13 + (-79705339 / 360000) * alpha * d * t ^ 15 + (103141763 / 2764800) * alpha * d * t ^ 17 + (3051146857 / 103680000) * alpha * d * t ^ 19 + (-1007494541 / 69120000) * alpha * d * t ^ 21 + (-10924003 / 41472000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_01, v34_02, v34_03, v34_10, v34_11, v34_12, v34_13, v34_20, v34_21, v34_22, v34_23, v34_30, v34_31, v34_32, v34_33, v34_40, v34_41, v34_42, v34_43]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_10, phase32_11, phase32_12, phase32_13, phase32_20, phase32_21, phase32_22, phase32_23, phase32_30, phase32_31, phase32_32, phase32_33, phase32_40, phase32_41, phase32_42, phase32_43]
  try simp only [star_one, star_neg]
  linear_combination ((2146193 / 320) * t ^ 3 + (-4767877 / 192) * t ^ 5 + (626672989333 / 30720000) * t ^ 7 + (-73173060011 / 46080000) * t ^ 9 + (-11577020741 / 9216000) * t ^ 11 + (-36614344429 / 61440000) * t ^ 13 + (370614357799 / 552960000) * t ^ 15 + (-43564510477 / 221184000) * t ^ 17 + (-77366052659 / 3317760000) * t ^ 19 + (30871903913 / 1105920000) * t ^ 21 + (53098591 / 24576000) * t ^ 25 + (530327 / 80) * d * t ^ 3 + (-43535507 / 3840) * d * t ^ 5 + (382339586333 / 69120000) * d * t ^ 7 + (-3460024697 / 2160000) * d * t ^ 9 + (11320790717 / 11059200) * d * t ^ 11 + (-38040840157 / 414720000) * d * t ^ 13 + (-62264828113 / 1658880000) * d * t ^ 15 + (-232794149 / 663552000) * d * t ^ 17 + (-11288646173 / 1105920000) * d * t ^ 19 + (12782403379 / 3317760000) * d * t ^ 21 + (1550419 / 79626240) * d * t ^ 25 + (-4977 / 64) * d ^ 2 * t ^ 3 + (602819 / 11520) * d ^ 2 * t ^ 5 + (3610893947 / 55296000) * d ^ 2 * t ^ 7 + (-842050657 / 27648000) * d ^ 2 * t ^ 9 + (-866081609 / 55296000) * d ^ 2 * t ^ 11 + (123783451 / 36864000) * d ^ 2 * t ^ 13 + (-15428107 / 55296000) * d ^ 2 * t ^ 15 + (91921 / 22118400) * d ^ 2 * t ^ 17 + (933271 / 5529600) * d ^ 2 * t ^ 19 + (-255931 / 55296000) * d ^ 2 * t ^ 21) * alpha_sq + ((14931 / 32) * t ^ 3 + (-3464341 / 7680) * t ^ 5 + (-7464451 / 32000) * t ^ 7 + (368792479 / 1843200) * t ^ 9 + (21269867 / 384000) * t ^ 11 + (-145311929 / 6144000) * t ^ 13 + (40117657 / 36864000) * t ^ 15 + (-2026819 / 14745600) * t ^ 17 + (-151461911 / 221184000) * t ^ 19 + (-2311979 / 73728000) * t ^ 21 + (4465 / 1769472) * t ^ 25 + (-21567 / 32) * alpha * t ^ 3 + (15516439 / 23040) * alpha * t ^ 5 + (727260563 / 2764800) * alpha * t ^ 7 + (-2091650317 / 9216000) * alpha * t ^ 9 + (-590893189 / 13824000) * alpha * t ^ 11 + (-31623529 / 165888000) * alpha * t ^ 13 + (-1016374343 / 110592000) * alpha * t ^ 15 + (46309 / 4915200) * alpha * t ^ 17 + (9517097 / 663552000) * alpha * t ^ 19 + (-2933993 / 73728000) * alpha * t ^ 21 + (4465 / 5308416) * alpha * t ^ 25) * d_sq
theorem v35_44 (t : ℂ) : (momentPoly 35 z35 4 4).eval t = (33027295 + (-65017872) * t ^ 2 + (14778657581 / 200) * t ^ 4 + (-531368251583 / 5000) * t ^ 6 + (2893742066952573 / 32000000) * t ^ 8 + (-645584505194639 / 24000000) * t ^ 10 + (77908969307419 / 19200000) * t ^ 12 + (-176712372731393 / 48000000) * t ^ 14 + (779754833936729 / 1152000000) * t ^ 16 + (-393581179981 / 144000000) * t ^ 18 + (-19343201808061 / 864000000) * t ^ 20 + (134691432451 / 16000000) * t ^ 22 + (3486994561021 / 576000000) * t ^ 24 + (-1644446796499 / 432000000) * t ^ 26 + (185254767553 / 1152000000) * t ^ 32 + (-3612104 / 3) * d * t ^ 2 + (212107099 / 120) * d * t ^ 4 + (6132431 / 600) * d * t ^ 6 + (-820608397093 / 1280000) * d * t ^ 8 + (-40452428171 / 2880000) * d * t ^ 10 + (360617695169 / 3840000) * d * t ^ 12 + (-918568690303 / 17280000) * d * t ^ 14 + (3377275710941 / 138240000) * d * t ^ 16 + (1157496419 / 138240) * d * t ^ 18 + (-31144356977 / 103680000) * d * t ^ 20 + (806841319 / 17280000) * d * t ^ 22 + (3659861 / 1536000) * d * t ^ 24 + (349655143 / 3456000) * d * t ^ 26 + (583775 / 663552) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z35, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v34_00, v34_01, v34_02, v34_03, v34_04, v34_10, v34_11, v34_12, v34_13, v34_14, v34_20, v34_21, v34_22, v34_23, v34_24, v34_30, v34_31, v34_32, v34_33, v34_34, v34_40, v34_41, v34_42, v34_43, v34_44]
  try simp only [phase32_00, phase32_01, phase32_02, phase32_03, phase32_04, phase32_10, phase32_11, phase32_12, phase32_13, phase32_14, phase32_20, phase32_21, phase32_22, phase32_23, phase32_24, phase32_30, phase32_31, phase32_32, phase32_33, phase32_34, phase32_40, phase32_41, phase32_42, phase32_43, phase32_44]
  try simp only [star_one, star_neg]
  linear_combination ((13093877 / 144) * t ^ 2 + (-281571031 / 2880) * t ^ 4 + (-384952165139 / 576000) * t ^ 6 + (3329405049271 / 2700000) * t ^ 8 + (-936604826884387 / 1382400000) * t ^ 10 + (500770405775659 / 2764800000) * t ^ 12 + (-3816214760537 / 46080000) * t ^ 14 + (183363846642427 / 16588800000) * t ^ 16 + (1277944758587 / 345600000) * t ^ 18 + (-8637073864499 / 24883200000) * t ^ 20 + (72784531967687 / 33177600000) * t ^ 22 + (-148770197351 / 176947200) * t ^ 24 + (-1128896570821 / 49766400000) * t ^ 26 + (15448090889 / 5308416000) * t ^ 32 + (5869669 / 72) * d * t ^ 2 + (-120106667 / 1440) * d * t ^ 4 + (-8120254057 / 288000) * d * t ^ 6 + (7160627710643 / 345600000) * d * t ^ 8 + (141421651287 / 25600000) * d * t ^ 10 + (-2132326855063 / 1382400000) * d * t ^ 12 + (8642451262201 / 829440000) * d * t ^ 14 + (-9140222483803 / 2764800000) * d * t ^ 16 + (-1052104327423 / 2073600000) * d * t ^ 18 + (464687990279 / 6220800000) * d * t ^ 20 + (-295742145743 / 5529600000) * d * t ^ 22 + (-30501587 / 245760000) * d * t ^ 24 + (-342180429173 / 24883200000) * d * t ^ 26 + (17489899 / 1592524800) * d * t ^ 32 + (-451513 / 48) * d ^ 2 * t ^ 2 + (13785899 / 960) * d ^ 2 * t ^ 4 + (-4475923 / 23040) * d ^ 2 * t ^ 6 + (-932776450427 / 207360000) * d ^ 2 * t ^ 8 + (-1451120291801 / 829440000) * d ^ 2 * t ^ 10 + (1642009692941 / 1658880000) * d ^ 2 * t ^ 12 + (365897290877 / 829440000) * d ^ 2 * t ^ 14 + (23635931401 / 1105920000) * d ^ 2 * t ^ 16 + (-483099931 / 82944000) * d ^ 2 * t ^ 18 + (-17060792437 / 4976640000) * d ^ 2 * t ^ 20 + (9041837587 / 6635520000) * d ^ 2 * t ^ 22 + (-94723 / 98304000) * d ^ 2 * t ^ 24 + (23121281 / 663552000) * d ^ 2 * t ^ 26 + (-9025 / 127401984) * d ^ 2 * t ^ 32) * alpha_sq + ((451513 / 12) * t ^ 2 + (-32175683 / 480) * t ^ 4 + (734949443 / 28800) * t ^ 6 + (-243564017909 / 69120000) * t ^ 8 + (641476786843 / 46080000) * t ^ 10 + (-1253219955769 / 276480000) * t ^ 12 + (-258140169583 / 138240000) * t ^ 14 + (18567707803 / 552960000) * t ^ 16 + (24138253 / 1152000) * t ^ 18 + (-3562777367 / 829440000) * t ^ 20 + (6028895311 / 552960000) * t ^ 22 + (-3833743 / 73728000) * t ^ 24 + (-44559379 / 55296000) * t ^ 26 + (9025 / 10616832) * t ^ 32) * d_sq
#print axioms v35_00
#print axioms v35_11
#print axioms v35_22
#print axioms v35_33
#print axioms v35_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
theorem site36 : ((r ^ 2 * phiMinus) : ℂ) = ((1 / 16) + (1 / 48) * d + (1 / 48) * alpha + (-1 / 48) * alpha * d) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 48) + (-1 / 96) * d + (-1 / 96) * alpha) * alpha_sq
theorem phase36_00 : ((r ^ 2 * phiMinus) : ℂ) ^ 0 * star ((r ^ 2 * phiMinus) : ℂ) ^ 0 = (1) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase36_01 : ((r ^ 2 * phiMinus) : ℂ) ^ 0 * star ((r ^ 2 * phiMinus) : ℂ) ^ 1 = ((1 / 16) + (1 / 48) * d + (-1 / 48) * alpha + (1 / 48) * alpha * d) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase36_02 : ((r ^ 2 * phiMinus) : ℂ) ^ 0 * star ((r ^ 2 * phiMinus) : ℂ) ^ 2 = ((-95 / 192) + (1 / 192) * d + (95 / 192) * alpha + (1 / 576) * alpha * d) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 2304) + (-1 / 1152) * d + (1 / 2304) * d ^ 2) * alpha_sq + ((-1 / 1152) + (1 / 1152) * alpha) * d_sq
theorem phase36_03 : ((r ^ 2 * phiMinus) : ℂ) ^ 0 * star ((r ^ 2 * phiMinus) : ℂ) ^ 3 = ((-47 / 1152) * d + (143 / 1152) * alpha) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 12288) + (-5 / 36864) * d + (1 / 36864) * d ^ 2 + (1 / 36864) * d ^ 3 + (-1 / 110592) * alpha + (1 / 36864) * alpha * d + (-1 / 36864) * alpha * d ^ 2 + (1 / 110592) * alpha * d ^ 3) * alpha_sq + ((-1 / 13824) * d + (1 / 4608) * alpha) * d_sq
theorem phase36_04 : ((r ^ 2 * phiMinus) : ℂ) ^ 0 * star ((r ^ 2 * phiMinus) : ℂ) ^ 4 = ((-4417 / 9216) + (-95 / 9216) * d + (-4417 / 9216) * alpha + (95 / 27648) * alpha * d) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((17 / 1769472) + (-5 / 442368) * d + (-5 / 884736) * d ^ 2 + (1 / 147456) * d ^ 3 + (1 / 1769472) * d ^ 4 + (-1 / 442368) * alpha + (1 / 165888) * alpha * d + (-1 / 221184) * alpha * d ^ 2 + (1 / 1327104) * alpha * d ^ 4 + (1 / 5308416) * alpha ^ 2 + (-1 / 1327104) * alpha ^ 2 * d + (1 / 884736) * alpha ^ 2 * d ^ 2 + (-1 / 1327104) * alpha ^ 2 * d ^ 3 + (1 / 5308416) * alpha ^ 2 * d ^ 4) * alpha_sq + ((-185 / 221184) + (-1 / 55296) * d + (-1 / 663552) * d ^ 2 + (-185 / 221184) * alpha + (1 / 165888) * alpha * d + (-1 / 663552) * alpha * d ^ 2) * d_sq
theorem phase36_10 : ((r ^ 2 * phiMinus) : ℂ) ^ 1 * star ((r ^ 2 * phiMinus) : ℂ) ^ 0 = ((1 / 16) + (1 / 48) * d + (1 / 48) * alpha + (-1 / 48) * alpha * d) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase36_11 : ((r ^ 2 * phiMinus) : ℂ) ^ 1 * star ((r ^ 2 * phiMinus) : ℂ) ^ 1 = (1) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 2304) + (1 / 1152) * d + (-1 / 2304) * d ^ 2) * alpha_sq + ((1 / 576)) * d_sq
theorem phase36_12 : ((r ^ 2 * phiMinus) : ℂ) ^ 1 * star ((r ^ 2 * phiMinus) : ℂ) ^ 2 = ((1 / 16) + (1 / 48) * d + (-1 / 48) * alpha + (1 / 48) * alpha * d) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 36864) + (5 / 110592) * d + (-1 / 110592) * d ^ 2 + (-1 / 110592) * d ^ 3 + (1 / 110592) * alpha + (-1 / 36864) * alpha * d + (1 / 36864) * alpha * d ^ 2 + (-1 / 110592) * alpha * d ^ 3) * alpha_sq + ((1 / 9216) + (1 / 27648) * d + (-1 / 27648) * alpha + (1 / 27648) * alpha * d) * d_sq
theorem phase36_13 : ((r ^ 2 * phiMinus) : ℂ) ^ 1 * star ((r ^ 2 * phiMinus) : ℂ) ^ 3 = ((-95 / 192) + (1 / 192) * d + (95 / 192) * alpha + (1 / 576) * alpha * d) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 1769472) + (-1 / 442368) * d + (1 / 294912) * d ^ 2 + (-1 / 442368) * d ^ 3 + (1 / 1769472) * d ^ 4 + (1 / 884736) * alpha + (-1 / 331776) * alpha * d + (1 / 442368) * alpha * d ^ 2 + (-1 / 2654208) * alpha * d ^ 4 + (-1 / 5308416) * alpha ^ 2 + (1 / 1327104) * alpha ^ 2 * d + (-1 / 884736) * alpha ^ 2 * d ^ 2 + (1 / 1327104) * alpha ^ 2 * d ^ 3 + (-1 / 5308416) * alpha ^ 2 * d ^ 4) * alpha_sq + ((-191 / 221184) + (1 / 110592) * d + (-1 / 663552) * d ^ 2 + (191 / 221184) * alpha + (1 / 331776) * alpha * d + (1 / 663552) * alpha * d ^ 2) * d_sq
theorem phase36_14 : ((r ^ 2 * phiMinus) : ℂ) ^ 1 * star ((r ^ 2 * phiMinus) : ℂ) ^ 4 = ((-47 / 1152) * d + (143 / 1152) * alpha) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 3145728) + (-17 / 28311552) * d + (5 / 14155776) * d ^ 2 + (-17 / 127401984) * d ^ 3 + (5 / 254803968) * d ^ 4 + (11 / 254803968) * d ^ 5 + (5 / 84934656) * alpha + (-1 / 9437184) * alpha * d + (-5 / 127401984) * alpha * d ^ 2 + (7 / 42467328) * alpha * d ^ 3 + (-7 / 84934656) * alpha * d ^ 4 + (1 / 254803968) * alpha * d ^ 5 + (-1 / 28311552) * alpha ^ 2 + (11 / 84934656) * alpha ^ 2 * d + (-7 / 42467328) * alpha ^ 2 * d ^ 2 + (1 / 14155776) * alpha ^ 2 * d ^ 3 + (1 / 84934656) * alpha ^ 2 * d ^ 4 + (-1 / 84934656) * alpha ^ 2 * d ^ 5 + (1 / 254803968) * alpha ^ 3 + (-5 / 254803968) * alpha ^ 3 * d + (5 / 127401984) * alpha ^ 3 * d ^ 2 + (-5 / 127401984) * alpha ^ 3 * d ^ 3 + (5 / 254803968) * alpha ^ 3 * d ^ 4 + (-1 / 254803968) * alpha ^ 3 * d ^ 5) * alpha_sq + ((-7 / 98304) * d + (-1 / 7962624) * d ^ 3 + (575 / 2654208) * alpha + (1 / 2654208) * alpha * d ^ 2) * d_sq
theorem phase36_20 : ((r ^ 2 * phiMinus) : ℂ) ^ 2 * star ((r ^ 2 * phiMinus) : ℂ) ^ 0 = ((-95 / 192) + (1 / 192) * d + (-95 / 192) * alpha + (-1 / 576) * alpha * d) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 2304) + (-1 / 1152) * d + (1 / 2304) * d ^ 2) * alpha_sq + ((-1 / 1152) + (-1 / 1152) * alpha) * d_sq
theorem phase36_21 : ((r ^ 2 * phiMinus) : ℂ) ^ 2 * star ((r ^ 2 * phiMinus) : ℂ) ^ 1 = ((1 / 16) + (1 / 48) * d + (1 / 48) * alpha + (-1 / 48) * alpha * d) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 36864) + (5 / 110592) * d + (-1 / 110592) * d ^ 2 + (-1 / 110592) * d ^ 3 + (-1 / 110592) * alpha + (1 / 36864) * alpha * d + (-1 / 36864) * alpha * d ^ 2 + (1 / 110592) * alpha * d ^ 3) * alpha_sq + ((1 / 9216) + (1 / 27648) * d + (1 / 27648) * alpha + (-1 / 27648) * alpha * d) * d_sq
theorem phase36_22 : ((r ^ 2 * phiMinus) : ℂ) ^ 2 * star ((r ^ 2 * phiMinus) : ℂ) ^ 2 = (1) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-7 / 1769472) + (1 / 147456) * d + (-7 / 2654208) * d ^ 2 + (1 / 1327104) * d ^ 3 + (-5 / 5308416) * d ^ 4 + (1 / 5308416) * alpha ^ 2 + (-1 / 1327104) * alpha ^ 2 * d + (1 / 884736) * alpha ^ 2 * d ^ 2 + (-1 / 1327104) * alpha ^ 2 * d ^ 3 + (1 / 5308416) * alpha ^ 2 * d ^ 4) * alpha_sq + ((193 / 110592) + (1 / 331776) * d ^ 2) * d_sq
theorem phase36_23 : ((r ^ 2 * phiMinus) : ℂ) ^ 2 * star ((r ^ 2 * phiMinus) : ℂ) ^ 3 = ((1 / 16) + (1 / 48) * d + (-1 / 48) * alpha + (1 / 48) * alpha * d) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-7 / 28311552) + (29 / 84934656) * d + (-1 / 42467328) * d ^ 2 + (-1 / 127401984) * d ^ 3 + (-11 / 254803968) * d ^ 4 + (-5 / 254803968) * d ^ 5 + (7 / 84934656) * alpha + (-19 / 84934656) * alpha * d + (25 / 127401984) * alpha * d ^ 2 + (-1 / 14155776) * alpha * d ^ 3 + (1 / 28311552) * alpha * d ^ 4 + (-5 / 254803968) * alpha * d ^ 5 + (1 / 84934656) * alpha ^ 2 + (-11 / 254803968) * alpha ^ 2 * d + (7 / 127401984) * alpha ^ 2 * d ^ 2 + (-1 / 42467328) * alpha ^ 2 * d ^ 3 + (-1 / 254803968) * alpha ^ 2 * d ^ 4 + (1 / 254803968) * alpha ^ 2 * d ^ 5 + (-1 / 254803968) * alpha ^ 3 + (5 / 254803968) * alpha ^ 3 * d + (-5 / 127401984) * alpha ^ 3 * d ^ 2 + (5 / 127401984) * alpha ^ 3 * d ^ 3 + (-5 / 254803968) * alpha ^ 3 * d ^ 4 + (1 / 254803968) * alpha ^ 3 * d ^ 5) * alpha_sq + ((193 / 1769472) + (193 / 5308416) * d + (1 / 5308416) * d ^ 2 + (1 / 15925248) * d ^ 3 + (-193 / 5308416) * alpha + (193 / 5308416) * alpha * d + (-1 / 15925248) * alpha * d ^ 2 + (1 / 15925248) * alpha * d ^ 3) * d_sq
theorem phase36_24 : ((r ^ 2 * phiMinus) : ℂ) ^ 2 * star ((r ^ 2 * phiMinus) : ℂ) ^ 4 = ((-95 / 192) + (1 / 192) * d + (95 / 192) * alpha + (1 / 576) * alpha * d) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-5 / 1358954496) + (-5 / 679477248) * d + (103 / 4076863488) * d ^ 2 + (-17 / 1019215872) * d ^ 3 + (77 / 12230590464) * d ^ 4 + (-29 / 6115295232) * d ^ 5 + (11 / 12230590464) * d ^ 6 + (7 / 679477248) * alpha + (-25 / 1019215872) * alpha * d + (31 / 2038431744) * alpha * d ^ 2 + (-1 / 1528823808) * alpha * d ^ 3 + (1 / 679477248) * alpha * d ^ 4 + (-1 / 1019215872) * alpha * d ^ 5 + (-5 / 6115295232) * alpha * d ^ 6 + (-1 / 1019215872) * alpha ^ 2 + (1 / 254803968) * alpha ^ 2 * d + (-19 / 3057647616) * alpha ^ 2 * d ^ 2 + (1 / 191102976) * alpha ^ 2 * d ^ 3 + (-1 / 339738624) * alpha ^ 2 * d ^ 4 + (1 / 764411904) * alpha ^ 2 * d ^ 5 + (-1 / 3057647616) * alpha ^ 2 * d ^ 6 + (-1 / 2038431744) * alpha ^ 3 + (7 / 3057647616) * alpha ^ 3 * d + (-25 / 6115295232) * alpha ^ 3 * d ^ 2 + (5 / 1528823808) * alpha ^ 3 * d ^ 3 + (-5 / 6115295232) * alpha ^ 3 * d ^ 4 + (-1 / 3057647616) * alpha ^ 3 * d ^ 5 + (1 / 6115295232) * alpha ^ 3 * d ^ 6 + (1 / 12230590464) * alpha ^ 4 + (-1 / 2038431744) * alpha ^ 4 * d + (5 / 4076863488) * alpha ^ 4 * d ^ 2 + (-5 / 3057647616) * alpha ^ 4 * d ^ 3 + (5 / 4076863488) * alpha ^ 4 * d ^ 4 + (-1 / 2038431744) * alpha ^ 4 * d ^ 5 + (1 / 12230590464) * alpha ^ 4 * d ^ 6) * alpha_sq + ((-36671 / 42467328) + (193 / 21233664) * d + (-1 / 663552) * d ^ 2 + (1 / 63700992) * d ^ 3 + (-1 / 382205952) * d ^ 4 + (36671 / 42467328) * alpha + (193 / 63700992) * alpha * d + (1 / 663552) * alpha * d ^ 2 + (1 / 191102976) * alpha * d ^ 3 + (1 / 382205952) * alpha * d ^ 4) * d_sq
theorem phase36_30 : ((r ^ 2 * phiMinus) : ℂ) ^ 3 * star ((r ^ 2 * phiMinus) : ℂ) ^ 0 = ((-47 / 1152) * d + (-143 / 1152) * alpha) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 12288) + (-5 / 36864) * d + (1 / 36864) * d ^ 2 + (1 / 36864) * d ^ 3 + (1 / 110592) * alpha + (-1 / 36864) * alpha * d + (1 / 36864) * alpha * d ^ 2 + (-1 / 110592) * alpha * d ^ 3) * alpha_sq + ((-1 / 13824) * d + (-1 / 4608) * alpha) * d_sq
theorem phase36_31 : ((r ^ 2 * phiMinus) : ℂ) ^ 3 * star ((r ^ 2 * phiMinus) : ℂ) ^ 1 = ((-95 / 192) + (1 / 192) * d + (-95 / 192) * alpha + (-1 / 576) * alpha * d) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 1769472) + (-1 / 442368) * d + (1 / 294912) * d ^ 2 + (-1 / 442368) * d ^ 3 + (1 / 1769472) * d ^ 4 + (-1 / 884736) * alpha + (1 / 331776) * alpha * d + (-1 / 442368) * alpha * d ^ 2 + (1 / 2654208) * alpha * d ^ 4 + (-1 / 5308416) * alpha ^ 2 + (1 / 1327104) * alpha ^ 2 * d + (-1 / 884736) * alpha ^ 2 * d ^ 2 + (1 / 1327104) * alpha ^ 2 * d ^ 3 + (-1 / 5308416) * alpha ^ 2 * d ^ 4) * alpha_sq + ((-191 / 221184) + (1 / 110592) * d + (-1 / 663552) * d ^ 2 + (-191 / 221184) * alpha + (-1 / 331776) * alpha * d + (-1 / 663552) * alpha * d ^ 2) * d_sq
theorem phase36_32 : ((r ^ 2 * phiMinus) : ℂ) ^ 3 * star ((r ^ 2 * phiMinus) : ℂ) ^ 2 = ((1 / 16) + (1 / 48) * d + (1 / 48) * alpha + (-1 / 48) * alpha * d) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-7 / 28311552) + (29 / 84934656) * d + (-1 / 42467328) * d ^ 2 + (-1 / 127401984) * d ^ 3 + (-11 / 254803968) * d ^ 4 + (-5 / 254803968) * d ^ 5 + (-7 / 84934656) * alpha + (19 / 84934656) * alpha * d + (-25 / 127401984) * alpha * d ^ 2 + (1 / 14155776) * alpha * d ^ 3 + (-1 / 28311552) * alpha * d ^ 4 + (5 / 254803968) * alpha * d ^ 5 + (1 / 84934656) * alpha ^ 2 + (-11 / 254803968) * alpha ^ 2 * d + (7 / 127401984) * alpha ^ 2 * d ^ 2 + (-1 / 42467328) * alpha ^ 2 * d ^ 3 + (-1 / 254803968) * alpha ^ 2 * d ^ 4 + (1 / 254803968) * alpha ^ 2 * d ^ 5 + (1 / 254803968) * alpha ^ 3 + (-5 / 254803968) * alpha ^ 3 * d + (5 / 127401984) * alpha ^ 3 * d ^ 2 + (-5 / 127401984) * alpha ^ 3 * d ^ 3 + (5 / 254803968) * alpha ^ 3 * d ^ 4 + (-1 / 254803968) * alpha ^ 3 * d ^ 5) * alpha_sq + ((193 / 1769472) + (193 / 5308416) * d + (1 / 5308416) * d ^ 2 + (1 / 15925248) * d ^ 3 + (193 / 5308416) * alpha + (-193 / 5308416) * alpha * d + (1 / 15925248) * alpha * d ^ 2 + (-1 / 15925248) * alpha * d ^ 3) * d_sq
theorem phase36_33 : ((r ^ 2 * phiMinus) : ℂ) ^ 3 * star ((r ^ 2 * phiMinus) : ℂ) ^ 3 = (1) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-37 / 1358954496) + (1 / 25165824) * d + (-19 / 1358954496) * d ^ 2 + (5 / 339738624) * d ^ 3 + (-49 / 4076863488) * d ^ 4 + (1 / 2038431744) * d ^ 5 + (-7 / 4076863488) * d ^ 6 + (5 / 2038431744) * alpha ^ 2 + (-1 / 113246208) * alpha ^ 2 * d + (23 / 2038431744) * alpha ^ 2 * d ^ 2 + (-1 / 169869312) * alpha ^ 2 * d ^ 3 + (1 / 679477248) * alpha ^ 2 * d ^ 4 + (-1 / 1019215872) * alpha ^ 2 * d ^ 5 + (1 / 2038431744) * alpha ^ 2 * d ^ 6 + (-1 / 12230590464) * alpha ^ 4 + (1 / 2038431744) * alpha ^ 4 * d + (-5 / 4076863488) * alpha ^ 4 * d ^ 2 + (5 / 3057647616) * alpha ^ 4 * d ^ 3 + (-5 / 4076863488) * alpha ^ 4 * d ^ 4 + (1 / 2038431744) * alpha ^ 4 * d ^ 5 + (-1 / 12230590464) * alpha ^ 4 * d ^ 6) * alpha_sq + ((37057 / 21233664) + (97 / 31850496) * d ^ 2 + (1 / 191102976) * d ^ 4) * d_sq
theorem phase36_34 : ((r ^ 2 * phiMinus) : ℂ) ^ 3 * star ((r ^ 2 * phiMinus) : ℂ) ^ 4 = ((1 / 16) + (1 / 48) * d + (-1 / 48) * alpha + (1 / 48) * alpha * d) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-37 / 21743271936) + (125 / 65229815808) * d + (-1 / 21743271936) * d ^ 2 + (41 / 65229815808) * d ^ 3 + (-29 / 65229815808) * d ^ 4 + (-43 / 195689447424) * d ^ 5 + (-19 / 195689447424) * d ^ 6 + (-7 / 195689447424) * d ^ 7 + (37 / 65229815808) * alpha + (-91 / 65229815808) * alpha * d + (73 / 65229815808) * alpha * d ^ 2 + (-13 / 21743271936) * alpha * d ^ 3 + (109 / 195689447424) * alpha * d ^ 4 + (-17 / 65229815808) * alpha * d ^ 5 + (1 / 21743271936) * alpha * d ^ 6 + (-7 / 195689447424) * alpha * d ^ 7 + (5 / 32614907904) * alpha ^ 2 + (-49 / 97844723712) * alpha ^ 2 * d + (17 / 32614907904) * alpha ^ 2 * d ^ 2 + (-13 / 97844723712) * alpha ^ 2 * d ^ 3 + (-1 / 32614907904) * alpha ^ 2 * d ^ 4 + (-1 / 32614907904) * alpha ^ 2 * d ^ 5 + (1 / 97844723712) * alpha ^ 2 * d ^ 6 + (1 / 97844723712) * alpha ^ 2 * d ^ 7 + (-5 / 97844723712) * alpha ^ 3 + (23 / 97844723712) * alpha ^ 3 * d + (-41 / 97844723712) * alpha ^ 3 * d ^ 2 + (35 / 97844723712) * alpha ^ 3 * d ^ 3 + (-5 / 32614907904) * alpha ^ 3 * d ^ 4 + (5 / 97844723712) * alpha ^ 3 * d ^ 5 + (-1 / 32614907904) * alpha ^ 3 * d ^ 6 + (1 / 97844723712) * alpha ^ 3 * d ^ 7 + (-1 / 195689447424) * alpha ^ 4 + (17 / 587068342272) * alpha ^ 4 * d + (-13 / 195689447424) * alpha ^ 4 * d ^ 2 + (5 / 65229815808) * alpha ^ 4 * d ^ 3 + (-25 / 587068342272) * alpha ^ 4 * d ^ 4 + (1 / 195689447424) * alpha ^ 4 * d ^ 5 + (1 / 195689447424) * alpha ^ 4 * d ^ 6 + (-1 / 587068342272) * alpha ^ 4 * d ^ 7 + (1 / 587068342272) * alpha ^ 5 + (-7 / 587068342272) * alpha ^ 5 * d + (7 / 195689447424) * alpha ^ 5 * d ^ 2 + (-35 / 587068342272) * alpha ^ 5 * d ^ 3 + (35 / 587068342272) * alpha ^ 5 * d ^ 4 + (-7 / 195689447424) * alpha ^ 5 * d ^ 5 + (7 / 587068342272) * alpha ^ 5 * d ^ 6 + (-1 / 587068342272) * alpha ^ 5 * d ^ 7) * alpha_sq + ((37057 / 339738624) + (37057 / 1019215872) * d + (97 / 509607936) * d ^ 2 + (97 / 1528823808) * d ^ 3 + (1 / 3057647616) * d ^ 4 + (1 / 9172942848) * d ^ 5 + (-37057 / 1019215872) * alpha + (37057 / 1019215872) * alpha * d + (-97 / 1528823808) * alpha * d ^ 2 + (97 / 1528823808) * alpha * d ^ 3 + (-1 / 9172942848) * alpha * d ^ 4 + (1 / 9172942848) * alpha * d ^ 5) * d_sq
theorem phase36_40 : ((r ^ 2 * phiMinus) : ℂ) ^ 4 * star ((r ^ 2 * phiMinus) : ℂ) ^ 0 = ((-4417 / 9216) + (-95 / 9216) * d + (4417 / 9216) * alpha + (-95 / 27648) * alpha * d) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((17 / 1769472) + (-5 / 442368) * d + (-5 / 884736) * d ^ 2 + (1 / 147456) * d ^ 3 + (1 / 1769472) * d ^ 4 + (1 / 442368) * alpha + (-1 / 165888) * alpha * d + (1 / 221184) * alpha * d ^ 2 + (-1 / 1327104) * alpha * d ^ 4 + (1 / 5308416) * alpha ^ 2 + (-1 / 1327104) * alpha ^ 2 * d + (1 / 884736) * alpha ^ 2 * d ^ 2 + (-1 / 1327104) * alpha ^ 2 * d ^ 3 + (1 / 5308416) * alpha ^ 2 * d ^ 4) * alpha_sq + ((-185 / 221184) + (-1 / 55296) * d + (-1 / 663552) * d ^ 2 + (185 / 221184) * alpha + (-1 / 165888) * alpha * d + (1 / 663552) * alpha * d ^ 2) * d_sq
theorem phase36_41 : ((r ^ 2 * phiMinus) : ℂ) ^ 4 * star ((r ^ 2 * phiMinus) : ℂ) ^ 1 = ((-47 / 1152) * d + (-143 / 1152) * alpha) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 3145728) + (-17 / 28311552) * d + (5 / 14155776) * d ^ 2 + (-17 / 127401984) * d ^ 3 + (5 / 254803968) * d ^ 4 + (11 / 254803968) * d ^ 5 + (-5 / 84934656) * alpha + (1 / 9437184) * alpha * d + (5 / 127401984) * alpha * d ^ 2 + (-7 / 42467328) * alpha * d ^ 3 + (7 / 84934656) * alpha * d ^ 4 + (-1 / 254803968) * alpha * d ^ 5 + (-1 / 28311552) * alpha ^ 2 + (11 / 84934656) * alpha ^ 2 * d + (-7 / 42467328) * alpha ^ 2 * d ^ 2 + (1 / 14155776) * alpha ^ 2 * d ^ 3 + (1 / 84934656) * alpha ^ 2 * d ^ 4 + (-1 / 84934656) * alpha ^ 2 * d ^ 5 + (-1 / 254803968) * alpha ^ 3 + (5 / 254803968) * alpha ^ 3 * d + (-5 / 127401984) * alpha ^ 3 * d ^ 2 + (5 / 127401984) * alpha ^ 3 * d ^ 3 + (-5 / 254803968) * alpha ^ 3 * d ^ 4 + (1 / 254803968) * alpha ^ 3 * d ^ 5) * alpha_sq + ((-7 / 98304) * d + (-1 / 7962624) * d ^ 3 + (-575 / 2654208) * alpha + (-1 / 2654208) * alpha * d ^ 2) * d_sq
theorem phase36_42 : ((r ^ 2 * phiMinus) : ℂ) ^ 4 * star ((r ^ 2 * phiMinus) : ℂ) ^ 2 = ((-95 / 192) + (1 / 192) * d + (-95 / 192) * alpha + (-1 / 576) * alpha * d) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-5 / 1358954496) + (-5 / 679477248) * d + (103 / 4076863488) * d ^ 2 + (-17 / 1019215872) * d ^ 3 + (77 / 12230590464) * d ^ 4 + (-29 / 6115295232) * d ^ 5 + (11 / 12230590464) * d ^ 6 + (-7 / 679477248) * alpha + (25 / 1019215872) * alpha * d + (-31 / 2038431744) * alpha * d ^ 2 + (1 / 1528823808) * alpha * d ^ 3 + (-1 / 679477248) * alpha * d ^ 4 + (1 / 1019215872) * alpha * d ^ 5 + (5 / 6115295232) * alpha * d ^ 6 + (-1 / 1019215872) * alpha ^ 2 + (1 / 254803968) * alpha ^ 2 * d + (-19 / 3057647616) * alpha ^ 2 * d ^ 2 + (1 / 191102976) * alpha ^ 2 * d ^ 3 + (-1 / 339738624) * alpha ^ 2 * d ^ 4 + (1 / 764411904) * alpha ^ 2 * d ^ 5 + (-1 / 3057647616) * alpha ^ 2 * d ^ 6 + (1 / 2038431744) * alpha ^ 3 + (-7 / 3057647616) * alpha ^ 3 * d + (25 / 6115295232) * alpha ^ 3 * d ^ 2 + (-5 / 1528823808) * alpha ^ 3 * d ^ 3 + (5 / 6115295232) * alpha ^ 3 * d ^ 4 + (1 / 3057647616) * alpha ^ 3 * d ^ 5 + (-1 / 6115295232) * alpha ^ 3 * d ^ 6 + (1 / 12230590464) * alpha ^ 4 + (-1 / 2038431744) * alpha ^ 4 * d + (5 / 4076863488) * alpha ^ 4 * d ^ 2 + (-5 / 3057647616) * alpha ^ 4 * d ^ 3 + (5 / 4076863488) * alpha ^ 4 * d ^ 4 + (-1 / 2038431744) * alpha ^ 4 * d ^ 5 + (1 / 12230590464) * alpha ^ 4 * d ^ 6) * alpha_sq + ((-36671 / 42467328) + (193 / 21233664) * d + (-1 / 663552) * d ^ 2 + (1 / 63700992) * d ^ 3 + (-1 / 382205952) * d ^ 4 + (-36671 / 42467328) * alpha + (-193 / 63700992) * alpha * d + (-1 / 663552) * alpha * d ^ 2 + (-1 / 191102976) * alpha * d ^ 3 + (-1 / 382205952) * alpha * d ^ 4) * d_sq
theorem phase36_43 : ((r ^ 2 * phiMinus) : ℂ) ^ 4 * star ((r ^ 2 * phiMinus) : ℂ) ^ 3 = ((1 / 16) + (1 / 48) * d + (1 / 48) * alpha + (-1 / 48) * alpha * d) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-37 / 21743271936) + (125 / 65229815808) * d + (-1 / 21743271936) * d ^ 2 + (41 / 65229815808) * d ^ 3 + (-29 / 65229815808) * d ^ 4 + (-43 / 195689447424) * d ^ 5 + (-19 / 195689447424) * d ^ 6 + (-7 / 195689447424) * d ^ 7 + (-37 / 65229815808) * alpha + (91 / 65229815808) * alpha * d + (-73 / 65229815808) * alpha * d ^ 2 + (13 / 21743271936) * alpha * d ^ 3 + (-109 / 195689447424) * alpha * d ^ 4 + (17 / 65229815808) * alpha * d ^ 5 + (-1 / 21743271936) * alpha * d ^ 6 + (7 / 195689447424) * alpha * d ^ 7 + (5 / 32614907904) * alpha ^ 2 + (-49 / 97844723712) * alpha ^ 2 * d + (17 / 32614907904) * alpha ^ 2 * d ^ 2 + (-13 / 97844723712) * alpha ^ 2 * d ^ 3 + (-1 / 32614907904) * alpha ^ 2 * d ^ 4 + (-1 / 32614907904) * alpha ^ 2 * d ^ 5 + (1 / 97844723712) * alpha ^ 2 * d ^ 6 + (1 / 97844723712) * alpha ^ 2 * d ^ 7 + (5 / 97844723712) * alpha ^ 3 + (-23 / 97844723712) * alpha ^ 3 * d + (41 / 97844723712) * alpha ^ 3 * d ^ 2 + (-35 / 97844723712) * alpha ^ 3 * d ^ 3 + (5 / 32614907904) * alpha ^ 3 * d ^ 4 + (-5 / 97844723712) * alpha ^ 3 * d ^ 5 + (1 / 32614907904) * alpha ^ 3 * d ^ 6 + (-1 / 97844723712) * alpha ^ 3 * d ^ 7 + (-1 / 195689447424) * alpha ^ 4 + (17 / 587068342272) * alpha ^ 4 * d + (-13 / 195689447424) * alpha ^ 4 * d ^ 2 + (5 / 65229815808) * alpha ^ 4 * d ^ 3 + (-25 / 587068342272) * alpha ^ 4 * d ^ 4 + (1 / 195689447424) * alpha ^ 4 * d ^ 5 + (1 / 195689447424) * alpha ^ 4 * d ^ 6 + (-1 / 587068342272) * alpha ^ 4 * d ^ 7 + (-1 / 587068342272) * alpha ^ 5 + (7 / 587068342272) * alpha ^ 5 * d + (-7 / 195689447424) * alpha ^ 5 * d ^ 2 + (35 / 587068342272) * alpha ^ 5 * d ^ 3 + (-35 / 587068342272) * alpha ^ 5 * d ^ 4 + (7 / 195689447424) * alpha ^ 5 * d ^ 5 + (-7 / 587068342272) * alpha ^ 5 * d ^ 6 + (1 / 587068342272) * alpha ^ 5 * d ^ 7) * alpha_sq + ((37057 / 339738624) + (37057 / 1019215872) * d + (97 / 509607936) * d ^ 2 + (97 / 1528823808) * d ^ 3 + (1 / 3057647616) * d ^ 4 + (1 / 9172942848) * d ^ 5 + (37057 / 1019215872) * alpha + (-37057 / 1019215872) * alpha * d + (97 / 1528823808) * alpha * d ^ 2 + (-97 / 1528823808) * alpha * d ^ 3 + (1 / 9172942848) * alpha * d ^ 4 + (-1 / 9172942848) * alpha * d ^ 5) * d_sq
theorem phase36_44 : ((r ^ 2 * phiMinus) : ℂ) ^ 4 * star ((r ^ 2 * phiMinus) : ℂ) ^ 4 = (1) := by
  rw [site36]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-175 / 1043677052928) + (1 / 4831838208) * d + (-67 / 782757789696) * d ^ 2 + (7 / 43486543872) * d ^ 3 + (-151 / 1565515579392) * d ^ 4 + (7 / 391378894848) * d ^ 5 + (-235 / 7044820107264) * d ^ 6 + (1 / 3522410053632) * d ^ 7 + (-85 / 28179280429056) * d ^ 8 + (67 / 3131031158784) * alpha ^ 2 + (-1 / 14495514624) * alpha ^ 2 * d + (175 / 2348273369088) * alpha ^ 2 * d ^ 2 + (-13 / 391378894848) * alpha ^ 2 * d ^ 3 + (91 / 4696546738176) * alpha ^ 2 * d ^ 4 + (-23 / 1174136684544) * alpha ^ 2 * d ^ 5 + (5 / 782757789696) * alpha ^ 2 * d ^ 6 + (-1 / 1174136684544) * alpha ^ 2 * d ^ 7 + (1 / 1043677052928) * alpha ^ 2 * d ^ 8 + (-13 / 9393093476352) * alpha ^ 4 + (1 / 130459631616) * alpha ^ 4 * d + (-121 / 7044820107264) * alpha ^ 4 * d ^ 2 + (23 / 1174136684544) * alpha ^ 4 * d ^ 3 + (-55 / 4696546738176) * alpha ^ 4 * d ^ 4 + (13 / 3522410053632) * alpha ^ 4 * d ^ 5 + (-1 / 782757789696) * alpha ^ 4 * d ^ 6 + (1 / 1174136684544) * alpha ^ 4 * d ^ 7 + (-7 / 28179280429056) * alpha ^ 4 * d ^ 8 + (1 / 28179280429056) * alpha ^ 6 + (-1 / 3522410053632) * alpha ^ 6 * d + (7 / 7044820107264) * alpha ^ 6 * d ^ 2 + (-7 / 3522410053632) * alpha ^ 6 * d ^ 3 + (35 / 14089640214528) * alpha ^ 6 * d ^ 4 + (-7 / 3522410053632) * alpha ^ 6 * d ^ 5 + (7 / 7044820107264) * alpha ^ 6 * d ^ 6 + (-1 / 3522410053632) * alpha ^ 6 * d ^ 7 + (1 / 28179280429056) * alpha ^ 6 * d ^ 8) * alpha_sq + ((7114945 / 4076863488) + (4139 / 1358954496) * d ^ 2 + (65 / 12230590464) * d ^ 4 + (1 / 110075314176) * d ^ 6) * d_sq
noncomputable def z36 : Fin 36 → ℂ := Fin.snoc z35 (r ^ 2 * phiMinus)
theorem v36_00 (t : ℂ) : (momentPoly 36 z36 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00]
  try simp only [phase36_00]
  try simp only [star_one, star_neg]
  ring
theorem v36_01 (t : ℂ) : (momentPoly 36 z36 0 1).eval t = ((5 / 16) * t + (-1 / 16) * d * t + (9 / 16) * alpha * t + (-1 / 16) * alpha * d * t) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_01]
  try simp only [phase36_00, phase36_01]
  try simp only [star_one, star_neg]
  ring
theorem v36_02 (t : ℂ) : (momentPoly 36 z36 0 2).eval t = ((-1491 / 80) * t ^ 2 + (4259 / 320) * t ^ 4 + (3 / 16) * d * t ^ 2 + (-1 / 64) * d * t ^ 4 + (1733 / 240) * alpha * t ^ 2 + (-2297 / 960) * alpha * t ^ 4 + (-5 / 48) * alpha * d * t ^ 2 + (-1 / 192) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_01, v35_02]
  try simp only [phase36_00, phase36_01, phase36_02]
  try simp only [star_one, star_neg]
  linear_combination ((-7 / 288) * t ^ 2 + (1 / 36) * d * t ^ 2 + (-1 / 288) * d ^ 2 * t ^ 2) * alpha_sq + ((1 / 144) * t ^ 2 + (-1 / 144) * alpha * t ^ 2) * d_sq
theorem v36_03 (t : ℂ) : (momentPoly 36 z36 0 3).eval t = ((-16099 / 320) * t ^ 3 + (6909 / 320) * t ^ 5 + 1 * t ^ 9 + (5329 / 960) * d * t ^ 3 + (-1343 / 320) * d * t ^ 5 + (47 / 384) * d * t ^ 9 + (-72461 / 4800) * alpha * t ^ 3 + (9323 / 1600) * alpha * t ^ 5 + (53209 / 9600) * alpha * t ^ 9 + (139 / 64) * alpha * d * t ^ 3 + (-133 / 64) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_01, v35_02, v35_03]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03]
  try simp only [star_one, star_neg]
  linear_combination ((-891 / 1280) * t ^ 3 + (2009 / 1920) * t ^ 5 + (4057 / 5760) * d * t ^ 3 + (-433 / 1440) * d * t ^ 5 + (-19 / 2304) * d ^ 2 * t ^ 3 + (-1 / 1152) * d ^ 2 * t ^ 5) * alpha_sq + ((1 / 24) * t ^ 3 + (5 / 576) * alpha * t ^ 3 + (-1 / 288) * alpha * t ^ 5) * d_sq
theorem v36_04 (t : ℂ) : (momentPoly 36 z36 0 4).eval t = ((7740429 / 16000) * t ^ 4 + (-14063353 / 16000) * t ^ 6 + (14141929 / 32000) * t ^ 8 + (-104679 / 1000) * t ^ 10 + (1631463 / 128000) * t ^ 16 + (-20809 / 9600) * d * t ^ 4 + (3527 / 3200) * d * t ^ 6 + (-2003 / 1280) * d * t ^ 8 + (3149 / 800) * d * t ^ 10 + (95 / 3072) * d * t ^ 16 + (-36374693 / 48000) * alpha * t ^ 4 + (43028411 / 48000) * alpha * t ^ 6 + (-18914413 / 96000) * alpha * t ^ 8 + (-149981 / 9000) * alpha * t ^ 10 + (2393167 / 1152000) * alpha * t ^ 16 + (36681 / 3200) * alpha * d * t ^ 4 + (-68617 / 9600) * alpha * d * t ^ 6 + (-617 / 3840) * alpha * d * t ^ 8 + (-9497 / 7200) * alpha * d * t ^ 10 + (-95 / 9216) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_01, v35_02, v35_03, v35_04]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_04]
  try simp only [star_one, star_neg]
  linear_combination ((14147 / 7200) * t ^ 4 + (3715757 / 115200) * t ^ 6 + (-4389 / 512) * t ^ 8 + (-3497 / 21600) * t ^ 10 + (-31819 / 14400) * d * t ^ 4 + (22027 / 28800) * d * t ^ 6 + (-73 / 1440) * d * t ^ 8 + (17719 / 43200) * d * t ^ 10 + (47 / 192) * d ^ 2 * t ^ 4 + (-3211 / 13824) * d ^ 2 * t ^ 6 + (-1 / 13824) * d ^ 2 * t ^ 8) * alpha_sq + ((53 / 2880) * t ^ 4 + (761 / 3840) * t ^ 6 + (-1 / 2304) * t ^ 8 + (47 / 1728) * t ^ 10 + (2873 / 2880) * alpha * t ^ 4 + (-2839 / 3840) * alpha * t ^ 6 + (-1 / 2304) * alpha * t ^ 8 + (47 / 1728) * alpha * t ^ 10) * d_sq
theorem v36_10 (t : ℂ) : (momentPoly 36 z36 1 0).eval t = ((5 / 16) * t + (-1 / 16) * d * t + (-9 / 16) * alpha * t + (1 / 16) * alpha * d * t) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_10]
  try simp only [phase36_00, phase36_10]
  try simp only [star_one, star_neg]
  ring
theorem v36_11 (t : ℂ) : (momentPoly 36 z36 1 1).eval t = (36 + (-26) * t ^ 2 + (-1 / 4) * d * t ^ 2) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_01, v35_10, v35_11]
  try simp only [phase36_00, phase36_01, phase36_10, phase36_11]
  try simp only [star_one, star_neg]
  linear_combination ((7 / 288) * t ^ 2 + (-1 / 36) * d * t ^ 2 + (1 / 288) * d ^ 2 * t ^ 2) * alpha_sq + ((-1 / 72) * t ^ 2) * d_sq
theorem v36_12 (t : ℂ) : (momentPoly 36 z36 1 2).eval t = ((355 / 16) * t + (-883 / 80) * t ^ 3 + (297 / 320) * t ^ 5 + (-71 / 16) * d * t + (651 / 160) * d * t ^ 3 + (-107 / 320) * d * t ^ 5 + (639 / 16) * alpha * t + (-7771 / 480) * alpha * t ^ 3 + (-8803 / 960) * alpha * t ^ 5 + (-71 / 16) * alpha * d * t + (629 / 240) * alpha * d * t ^ 3 + (1009 / 960) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_01, v35_02, v35_10, v35_11, v35_12]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_10, phase36_11, phase36_12]
  try simp only [star_one, star_neg]
  linear_combination ((297 / 1280) * t ^ 3 + (-2009 / 5760) * t ^ 5 + (-4057 / 17280) * d * t ^ 3 + (433 / 4320) * d * t ^ 5 + (19 / 6912) * d ^ 2 * t ^ 3 + (1 / 3456) * d ^ 2 * t ^ 5) * alpha_sq + ((-19 / 1152) * t ^ 3 + (-1 / 576) * t ^ 5 + (-77 / 3456) * alpha * t ^ 3 + (1 / 1728) * alpha * t ^ 5) * d_sq
theorem v36_13 (t : ℂ) : (momentPoly 36 z36 1 3).eval t = ((-31311 / 16) * t ^ 2 + (567697 / 200) * t ^ 4 + (-3044553 / 3200) * t ^ 6 + (-51373 / 6400) * t ^ 10 + (315 / 16) * d * t ^ 2 + (-1411 / 150) * d * t ^ 4 + (-19783 / 3200) * d * t ^ 6 + (-20119 / 19200) * d * t ^ 10 + (12131 / 16) * alpha * t ^ 2 + (-202933 / 240) * alpha * t ^ 4 + (91757 / 640) * alpha * t ^ 6 + (30511 / 3840) * alpha * t ^ 10 + (-175 / 16) * alpha * d * t ^ 2 + (3257 / 600) * alpha * d * t ^ 4 + (11379 / 3200) * alpha * d * t ^ 6 + (-6673 / 19200) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_01, v35_02, v35_03, v35_10, v35_11, v35_12, v35_13]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_10, phase36_11, phase36_12, phase36_13]
  try simp only [star_one, star_neg]
  linear_combination ((-245 / 96) * t ^ 2 + (-12469 / 57600) * t ^ 4 + (95467 / 115200) * t ^ 6 + (3497 / 86400) * t ^ 10 + (35 / 12) * d * t ^ 2 + (6439 / 57600) * d * t ^ 4 + (-112807 / 115200) * d * t ^ 6 + (-17719 / 172800) * d * t ^ 10 + (-35 / 96) * d ^ 2 * t ^ 2 + (67 / 640) * d ^ 2 * t ^ 4 + (289 / 1920) * d ^ 2 * t ^ 6) * alpha_sq + ((35 / 48) * t ^ 2 + (1871 / 11520) * t ^ 4 + (-13967 / 23040) * t ^ 6 + (47 / 6912) * t ^ 10 + (-35 / 48) * alpha * t ^ 2 + (3769 / 11520) * alpha * t ^ 4 + (3167 / 23040) * alpha * t ^ 6 + (-47 / 6912) * alpha * t ^ 10) * d_sq
theorem v36_14 (t : ℂ) : (momentPoly 36 z36 1 4).eval t = ((-1110831 / 160) * t ^ 3 + (471526727 / 64000) * t ^ 5 + (-21375277 / 32000) * t ^ 7 + (-2976343 / 128000) * t ^ 9 + (-7324001 / 32000) * t ^ 11 + (830551 / 128000) * t ^ 17 + (122567 / 160) * d * t ^ 3 + (-227900807 / 192000) * d * t ^ 5 + (13203419 / 32000) * d * t ^ 7 + (4379221 / 128000) * d * t ^ 9 + (-275359 / 96000) * d * t ^ 11 + (-505441 / 384000) * d * t ^ 17 + (-1666603 / 800) * alpha * t ^ 3 + (347035633 / 192000) * alpha * t ^ 5 + (35338997 / 96000) * alpha * t ^ 7 + (157212583 / 384000) * alpha * t ^ 9 + (-156054197 / 288000) * alpha * t ^ 11 + (-12195403 / 1152000) * alpha * t ^ 17 + (9591 / 32) * alpha * d * t ^ 3 + (-18963427 / 38400) * alpha * d * t ^ 5 + (996983 / 6400) * alpha * d * t ^ 7 + (229997 / 5120) * alpha * d * t ^ 9 + (-34281 / 6400) * alpha * d * t ^ 11 + (1985 / 3072) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_01, v35_02, v35_03, v35_04, v35_10, v35_11, v35_12, v35_13, v35_14]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_04, phase36_10, phase36_11, phase36_12, phase36_13, phase36_14]
  try simp only [star_one, star_neg]
  linear_combination ((-61479 / 640) * t ^ 3 + (140323069 / 768000) * t ^ 5 + (10201543 / 1152000) * t ^ 7 + (-160732663 / 4608000) * t ^ 9 + (-5720423 / 3456000) * t ^ 11 + (2300599 / 6912000) * t ^ 17 + (93311 / 960) * d * t ^ 3 + (-136142549 / 1728000) * d * t ^ 5 + (-1059773 / 72000) * d * t ^ 7 + (32595791 / 3456000) * d * t ^ 9 + (4296911 / 2592000) * d * t ^ 11 + (-495043 / 5184000) * d * t ^ 17 + (-437 / 384) * d ^ 2 * t ^ 3 + (-41977 / 276480) * d ^ 2 * t ^ 5 + (31097 / 46080) * d ^ 2 * t ^ 7 + (703 / 36864) * d ^ 2 * t ^ 9 + (-211 / 82944) * d ^ 2 * t ^ 11 + (95 / 165888) * d ^ 2 * t ^ 17) * alpha_sq + ((23 / 4) * t ^ 3 + (-7363 / 11520) * t ^ 5 + (-29557 / 11520) * t ^ 7 + (-11 / 96) * t ^ 9 + (23 / 432) * t ^ 11 + (115 / 96) * alpha * t ^ 3 + (-25987 / 115200) * alpha * t ^ 5 + (-7969 / 14400) * alpha * t ^ 7 + (11759 / 138240) * alpha * t ^ 9 + (-152477 / 518400) * alpha * t ^ 11 + (-95 / 41472) * alpha * t ^ 17) * d_sq
theorem v36_20 (t : ℂ) : (momentPoly 36 z36 2 0).eval t = ((-1491 / 80) * t ^ 2 + (4259 / 320) * t ^ 4 + (3 / 16) * d * t ^ 2 + (-1 / 64) * d * t ^ 4 + (-1733 / 240) * alpha * t ^ 2 + (2297 / 960) * alpha * t ^ 4 + (5 / 48) * alpha * d * t ^ 2 + (1 / 192) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_10, v35_20]
  try simp only [phase36_00, phase36_10, phase36_20]
  try simp only [star_one, star_neg]
  linear_combination ((-7 / 288) * t ^ 2 + (1 / 36) * d * t ^ 2 + (-1 / 288) * d ^ 2 * t ^ 2) * alpha_sq + ((1 / 144) * t ^ 2 + (1 / 144) * alpha * t ^ 2) * d_sq
theorem v36_21 (t : ℂ) : (momentPoly 36 z36 2 1).eval t = ((355 / 16) * t + (-883 / 80) * t ^ 3 + (297 / 320) * t ^ 5 + (-71 / 16) * d * t + (651 / 160) * d * t ^ 3 + (-107 / 320) * d * t ^ 5 + (-639 / 16) * alpha * t + (7771 / 480) * alpha * t ^ 3 + (8803 / 960) * alpha * t ^ 5 + (71 / 16) * alpha * d * t + (-629 / 240) * alpha * d * t ^ 3 + (-1009 / 960) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_01, v35_10, v35_11, v35_20, v35_21]
  try simp only [phase36_00, phase36_01, phase36_10, phase36_11, phase36_20, phase36_21]
  try simp only [star_one, star_neg]
  linear_combination ((297 / 1280) * t ^ 3 + (-2009 / 5760) * t ^ 5 + (-4057 / 17280) * d * t ^ 3 + (433 / 4320) * d * t ^ 5 + (19 / 6912) * d ^ 2 * t ^ 3 + (1 / 3456) * d ^ 2 * t ^ 5) * alpha_sq + ((-19 / 1152) * t ^ 3 + (-1 / 576) * t ^ 5 + (77 / 3456) * alpha * t ^ 3 + (-1 / 1728) * alpha * t ^ 5) * d_sq
theorem v36_22 (t : ℂ) : (momentPoly 36 z36 2 2).eval t = (2556 + (-3640) * t ^ 2 + (3740579 / 2400) * t ^ 4 + (-4773727 / 9600) * t ^ 6 + (1521611 / 9600) * t ^ 8 + (-35) * d * t ^ 2 + (10799 / 480) * d * t ^ 4 + (15059 / 1920) * d * t ^ 6 + (-131 / 384) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_01, v35_02, v35_10, v35_11, v35_12, v35_20, v35_21, v35_22]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_10, phase36_11, phase36_12, phase36_20, phase36_21, phase36_22]
  try simp only [star_one, star_neg]
  linear_combination ((245 / 72) * t ^ 2 + (-211 / 576) * t ^ 4 + (-54635 / 4608) * t ^ 6 + (1463 / 512) * t ^ 8 + (-35 / 9) * d * t ^ 2 + (47 / 80) * d * t ^ 4 + (1513 / 1440) * d * t ^ 6 + (73 / 4320) * d * t ^ 8 + (35 / 72) * d ^ 2 * t ^ 2 + (-637 / 2880) * d ^ 2 * t ^ 4 + (-25561 / 207360) * d ^ 2 * t ^ 6 + (1 / 41472) * d ^ 2 * t ^ 8) * alpha_sq + ((-35 / 18) * t ^ 2 + (503 / 480) * t ^ 4 + (5917 / 17280) * t ^ 6 + (-1 / 3456) * t ^ 8) * d_sq
theorem v36_23 (t : ℂ) : (momentPoly 36 z36 2 3).eval t = (2330 * t + (-182781 / 80) * t ^ 3 + (46380709 / 48000) * t ^ 5 + (-10953143 / 9600) * t ^ 7 + (17031403 / 64000) * t ^ 9 + (43285561 / 384000) * t ^ 11 + (-10707631 / 384000) * t ^ 13 + (-466) * d * t + (134757 / 160) * d * t ^ 3 + (-294223 / 600) * d * t ^ 5 + (167353 / 1200) * d * t ^ 7 + (-86537 / 2560) * d * t ^ 9 + (-48491 / 15360) * d * t ^ 11 + (122057 / 76800) * d * t ^ 13 + 4194 * alpha * t + (-536199 / 160) * alpha * t ^ 3 + (-6071609 / 4000) * alpha * t ^ 5 + (2674481 / 3200) * alpha * t ^ 7 + (6639339 / 64000) * alpha * t ^ 9 + (-32592397 / 384000) * alpha * t ^ 11 + (29170207 / 384000) * alpha * t ^ 13 + (-466) * alpha * d * t + (43401 / 80) * alpha * d * t ^ 3 + (1680773 / 28800) * alpha * d * t ^ 5 + (-397207 / 3600) * alpha * d * t ^ 7 + (-263191 / 7680) * alpha * d * t ^ 9 + (-424507 / 230400) * alpha * d * t ^ 11 + (63121 / 230400) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_01, v35_02, v35_03, v35_10, v35_11, v35_12, v35_13, v35_20, v35_21, v35_22, v35_23]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_10, phase36_11, phase36_12, phase36_13, phase36_20, phase36_21, phase36_22, phase36_23]
  try simp only [star_one, star_neg]
  linear_combination ((61479 / 1280) * t ^ 3 + (-6059827 / 57600) * t ^ 5 + (5075827 / 230400) * t ^ 7 + (927827 / 92160) * t ^ 9 + (-1251599 / 1382400) * t ^ 11 + (-160537 / 69120) * t ^ 13 + (-93311 / 1920) * d * t ^ 3 + (2308817 / 43200) * d * t ^ 5 + (-6192449 / 691200) * d * t ^ 7 + (-1102567 / 1382400) * d * t ^ 9 + (-1989739 / 4147200) * d * t ^ 11 + (-17719 / 2073600) * d * t ^ 13 + (437 / 768) * d ^ 2 * t ^ 3 + (-21887 / 172800) * d ^ 2 * t ^ 5 + (-8771 / 38400) * d ^ 2 * t ^ 7 + (-101 / 34560) * d ^ 2 * t ^ 9 + (2191 / 115200) * d ^ 2 * t ^ 11) * alpha_sq + ((-437 / 128) * t ^ 3 + (151493 / 115200) * t ^ 5 + (262181 / 230400) * t ^ 7 + (-1051 / 18432) * t ^ 9 + (-57809 / 460800) * t ^ 11 + (47 / 27648) * t ^ 13 + (-1771 / 384) * alpha * t ^ 3 + (708847 / 345600) * alpha * t ^ 5 + (902339 / 691200) * alpha * t ^ 7 + (-3173 / 55296) * alpha * t ^ 9 + (136627 / 4147200) * alpha * t ^ 11 + (-47 / 82944) * alpha * t ^ 13) * d_sq
theorem v36_24 (t : ℂ) : (momentPoly 36 z36 2 4).eval t = ((-10805277 / 40) * t ^ 2 + (935879677 / 1600) * t ^ 4 + (-193725887717 / 480000) * t ^ 6 + (196755388429 / 1920000) * t ^ 8 + (-2057199749 / 96000) * t ^ 10 + (89389862627 / 11520000) * t ^ 12 + (-3428254067 / 2880000) * t ^ 14 + (-1973674367 / 11520000) * t ^ 18 + (203375359 / 1440000) * t ^ 20 + (21741 / 8) * d * t ^ 2 + (-11226769 / 4800) * d * t ^ 4 + (-38932793 / 24000) * d * t ^ 6 + (211020503 / 192000) * d * t ^ 8 + (-2179373 / 48000) * d * t ^ 10 + (433423 / 2560) * d * t ^ 12 + (537557 / 8000) * d * t ^ 14 + (583051 / 192000) * d * t ^ 18 + (103523 / 384000) * d * t ^ 20 + (12559051 / 120) * alpha * t ^ 2 + (-188492987 / 960) * alpha * t ^ 4 + (16867772119 / 160000) * alpha * t ^ 6 + (-19395051377 / 960000) * alpha * t ^ 8 + (627893169 / 64000) * alpha * t ^ 10 + (-213539177 / 120000) * alpha * t ^ 12 + (-366746467 / 720000) * alpha * t ^ 14 + (-1094293 / 7500) * alpha * t ^ 18 + (349765649 / 5760000) * alpha * t ^ 20 + (-36235 / 24) * alpha * d * t ^ 2 + (7438757 / 4800) * alpha * d * t ^ 4 + (40214113 / 72000) * alpha * d * t ^ 6 + (-589324201 / 1152000) * alpha * d * t ^ 8 + (-36649471 / 192000) * alpha * d * t ^ 10 + (17723647 / 256000) * alpha * d * t ^ 12 + (-3810287 / 576000) * alpha * d * t ^ 14 + (5486107 / 2304000) * alpha * d * t ^ 18 + (-27727 / 1152000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_01, v35_02, v35_03, v35_04, v35_10, v35_11, v35_12, v35_13, v35_14, v35_20, v35_21, v35_22, v35_23, v35_24]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_04, phase36_10, phase36_11, phase36_12, phase36_13, phase36_14, phase36_20, phase36_21, phase36_22, phase36_23, phase36_24]
  try simp only [star_one, star_neg]
  linear_combination ((-50729 / 144) * t ^ 2 + (-211973 / 3600) * t ^ 4 + (1137802721 / 3456000) * t ^ 6 + (6254090639 / 9216000) * t ^ 8 + (-10019476751 / 13824000) * t ^ 10 + (6491937731 / 55296000) * t ^ 12 + (69781963 / 4608000) * t ^ 14 + (272428337 / 55296000) * t ^ 18 + (-4882507 / 1843200) * t ^ 20 + (7247 / 18) * d * t ^ 2 + (109463 / 3600) * d * t ^ 4 + (-53075599 / 144000) * d * t ^ 6 + (-192797507 / 13824000) * d * t ^ 8 + (103122779 / 6912000) * d * t ^ 10 + (161230631 / 27648000) * d * t ^ 12 + (136983343 / 20736000) * d * t ^ 14 + (28664657 / 82944000) * d * t ^ 18 + (30949 / 3456000) * d * t ^ 20 + (-7247 / 144) * d ^ 2 * t ^ 2 + (1139 / 40) * d ^ 2 * t ^ 4 + (27202331 / 691200) * d ^ 2 * t ^ 6 + (-235199029 / 16588800) * d ^ 2 * t ^ 8 + (-19425167 / 2764800) * d ^ 2 * t ^ 10 + (168217 / 6635520) * d ^ 2 * t ^ 12 + (1003853 / 24883200) * d ^ 2 * t ^ 14 + (-141115 / 3981312) * d ^ 2 * t ^ 18 + (95 / 1990656) * d ^ 2 * t ^ 20) * alpha_sq + ((7247 / 72) * t ^ 2 + (31807 / 720) * t ^ 4 + (-400987231 / 1728000) * t ^ 6 + (1086919111 / 13824000) * t ^ 8 + (142010383 / 6912000) * t ^ 10 + (-31701599 / 27648000) * t ^ 12 + (614357 / 4147200) * t ^ 14 + (1958833 / 82944000) * t ^ 18 + (95 / 331776) * t ^ 20 + (-7247 / 72) * alpha * t ^ 2 + (64073 / 720) * alpha * t ^ 4 + (27020201 / 1728000) * alpha * t ^ 6 + (-20674517 / 4608000) * alpha * t ^ 8 + (-7013987 / 768000) * alpha * t ^ 10 + (-53279123 / 82944000) * alpha * t ^ 12 + (615881 / 1382400) * alpha * t ^ 14 + (1063463 / 9216000) * alpha * t ^ 18 + (-95 / 331776) * alpha * t ^ 20) * d_sq
theorem v36_30 (t : ℂ) : (momentPoly 36 z36 3 0).eval t = ((-16099 / 320) * t ^ 3 + (6909 / 320) * t ^ 5 + 1 * t ^ 9 + (5329 / 960) * d * t ^ 3 + (-1343 / 320) * d * t ^ 5 + (47 / 384) * d * t ^ 9 + (72461 / 4800) * alpha * t ^ 3 + (-9323 / 1600) * alpha * t ^ 5 + (-53209 / 9600) * alpha * t ^ 9 + (-139 / 64) * alpha * d * t ^ 3 + (133 / 64) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_10, v35_20, v35_30]
  try simp only [phase36_00, phase36_10, phase36_20, phase36_30]
  try simp only [star_one, star_neg]
  linear_combination ((-891 / 1280) * t ^ 3 + (2009 / 1920) * t ^ 5 + (4057 / 5760) * d * t ^ 3 + (-433 / 1440) * d * t ^ 5 + (-19 / 2304) * d ^ 2 * t ^ 3 + (-1 / 1152) * d ^ 2 * t ^ 5) * alpha_sq + ((1 / 24) * t ^ 3 + (-5 / 576) * alpha * t ^ 3 + (1 / 288) * alpha * t ^ 5) * d_sq
theorem v36_31 (t : ℂ) : (momentPoly 36 z36 3 1).eval t = ((-31311 / 16) * t ^ 2 + (567697 / 200) * t ^ 4 + (-3044553 / 3200) * t ^ 6 + (-51373 / 6400) * t ^ 10 + (315 / 16) * d * t ^ 2 + (-1411 / 150) * d * t ^ 4 + (-19783 / 3200) * d * t ^ 6 + (-20119 / 19200) * d * t ^ 10 + (-12131 / 16) * alpha * t ^ 2 + (202933 / 240) * alpha * t ^ 4 + (-91757 / 640) * alpha * t ^ 6 + (-30511 / 3840) * alpha * t ^ 10 + (175 / 16) * alpha * d * t ^ 2 + (-3257 / 600) * alpha * d * t ^ 4 + (-11379 / 3200) * alpha * d * t ^ 6 + (6673 / 19200) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_01, v35_10, v35_11, v35_20, v35_21, v35_30, v35_31]
  try simp only [phase36_00, phase36_01, phase36_10, phase36_11, phase36_20, phase36_21, phase36_30, phase36_31]
  try simp only [star_one, star_neg]
  linear_combination ((-245 / 96) * t ^ 2 + (-12469 / 57600) * t ^ 4 + (95467 / 115200) * t ^ 6 + (3497 / 86400) * t ^ 10 + (35 / 12) * d * t ^ 2 + (6439 / 57600) * d * t ^ 4 + (-112807 / 115200) * d * t ^ 6 + (-17719 / 172800) * d * t ^ 10 + (-35 / 96) * d ^ 2 * t ^ 2 + (67 / 640) * d ^ 2 * t ^ 4 + (289 / 1920) * d ^ 2 * t ^ 6) * alpha_sq + ((35 / 48) * t ^ 2 + (1871 / 11520) * t ^ 4 + (-13967 / 23040) * t ^ 6 + (47 / 6912) * t ^ 10 + (35 / 48) * alpha * t ^ 2 + (-3769 / 11520) * alpha * t ^ 4 + (-3167 / 23040) * alpha * t ^ 6 + (47 / 6912) * alpha * t ^ 10) * d_sq
theorem v36_32 (t : ℂ) : (momentPoly 36 z36 3 2).eval t = (2330 * t + (-182781 / 80) * t ^ 3 + (46380709 / 48000) * t ^ 5 + (-10953143 / 9600) * t ^ 7 + (17031403 / 64000) * t ^ 9 + (43285561 / 384000) * t ^ 11 + (-10707631 / 384000) * t ^ 13 + (-466) * d * t + (134757 / 160) * d * t ^ 3 + (-294223 / 600) * d * t ^ 5 + (167353 / 1200) * d * t ^ 7 + (-86537 / 2560) * d * t ^ 9 + (-48491 / 15360) * d * t ^ 11 + (122057 / 76800) * d * t ^ 13 + (-4194) * alpha * t + (536199 / 160) * alpha * t ^ 3 + (6071609 / 4000) * alpha * t ^ 5 + (-2674481 / 3200) * alpha * t ^ 7 + (-6639339 / 64000) * alpha * t ^ 9 + (32592397 / 384000) * alpha * t ^ 11 + (-29170207 / 384000) * alpha * t ^ 13 + 466 * alpha * d * t + (-43401 / 80) * alpha * d * t ^ 3 + (-1680773 / 28800) * alpha * d * t ^ 5 + (397207 / 3600) * alpha * d * t ^ 7 + (263191 / 7680) * alpha * d * t ^ 9 + (424507 / 230400) * alpha * d * t ^ 11 + (-63121 / 230400) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_01, v35_02, v35_10, v35_11, v35_12, v35_20, v35_21, v35_22, v35_30, v35_31, v35_32]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_10, phase36_11, phase36_12, phase36_20, phase36_21, phase36_22, phase36_30, phase36_31, phase36_32]
  try simp only [star_one, star_neg]
  linear_combination ((61479 / 1280) * t ^ 3 + (-6059827 / 57600) * t ^ 5 + (5075827 / 230400) * t ^ 7 + (927827 / 92160) * t ^ 9 + (-1251599 / 1382400) * t ^ 11 + (-160537 / 69120) * t ^ 13 + (-93311 / 1920) * d * t ^ 3 + (2308817 / 43200) * d * t ^ 5 + (-6192449 / 691200) * d * t ^ 7 + (-1102567 / 1382400) * d * t ^ 9 + (-1989739 / 4147200) * d * t ^ 11 + (-17719 / 2073600) * d * t ^ 13 + (437 / 768) * d ^ 2 * t ^ 3 + (-21887 / 172800) * d ^ 2 * t ^ 5 + (-8771 / 38400) * d ^ 2 * t ^ 7 + (-101 / 34560) * d ^ 2 * t ^ 9 + (2191 / 115200) * d ^ 2 * t ^ 11) * alpha_sq + ((-437 / 128) * t ^ 3 + (151493 / 115200) * t ^ 5 + (262181 / 230400) * t ^ 7 + (-1051 / 18432) * t ^ 9 + (-57809 / 460800) * t ^ 11 + (47 / 27648) * t ^ 13 + (1771 / 384) * alpha * t ^ 3 + (-708847 / 345600) * alpha * t ^ 5 + (-902339 / 691200) * alpha * t ^ 7 + (3173 / 55296) * alpha * t ^ 9 + (-136627 / 4147200) * alpha * t ^ 11 + (47 / 82944) * alpha * t ^ 13) * d_sq
theorem v36_33 (t : ℂ) : (momentPoly 36 z36 3 3).eval t = (268416 + (-565266) * t ^ 2 + (190769529 / 400) * t ^ 4 + (-24439044899 / 80000) * t ^ 6 + (24958949959 / 160000) * t ^ 8 + (-4654656843 / 160000) * t ^ 10 + (533684149 / 320000) * t ^ 12 + (-22934531 / 20000) * t ^ 14 + (21038511 / 320000) * t ^ 18 + (-21741 / 4) * d * t ^ 2 + (550749 / 80) * d * t ^ 4 + (2283827 / 9600) * d * t ^ 6 + (-10295639 / 6400) * d * t ^ 8 + (-904503 / 6400) * d * t ^ 10 + (607797 / 12800) * d * t ^ 12 + (-878989 / 12800) * d * t ^ 14 + (47 / 192) * d * t ^ 18) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_01, v35_02, v35_03, v35_10, v35_11, v35_12, v35_13, v35_20, v35_21, v35_22, v35_23, v35_30, v35_31, v35_32, v35_33]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_10, phase36_11, phase36_12, phase36_13, phase36_20, phase36_21, phase36_22, phase36_23, phase36_30, phase36_31, phase36_32, phase36_33]
  try simp only [star_one, star_neg]
  linear_combination ((50729 / 96) * t ^ 2 + (-3587 / 32) * t ^ 4 + (-1435959433 / 384000) * t ^ 6 + (98146687 / 30720) * t ^ 8 + (-32155649 / 128000) * t ^ 10 + (-47555137 / 6912000) * t ^ 12 + (-184475833 / 6912000) * t ^ 14 + (-5578859 / 4147200) * t ^ 18 + (-7247 / 12) * d * t ^ 2 + (7191 / 40) * d * t ^ 4 + (6143797 / 16000) * d * t ^ 6 + (-780257 / 57600) * d * t ^ 8 + (-17157583 / 384000) * d * t ^ 10 + (40110371 / 3456000) * d * t ^ 12 + (-1671641 / 216000) * d * t ^ 14 + (7247 / 96) * d ^ 2 * t ^ 2 + (-10829 / 160) * d ^ 2 * t ^ 4 + (-14936971 / 691200) * d ^ 2 * t ^ 6 + (16863581 / 1382400) * d ^ 2 * t ^ 8 + (185047 / 28800) * d ^ 2 * t ^ 10 + (550813 / 1382400) * d ^ 2 * t ^ 12 + (-17737 / 345600) * d ^ 2 * t ^ 14) * alpha_sq + ((-7247 / 24) * t ^ 2 + (25653 / 80) * t ^ 4 + (130721 / 115200) * t ^ 6 + (-2843983 / 230400) * t ^ 8 + (-664423 / 25600) * t ^ 10 + (-351067 / 138240) * t ^ 12 + (1220393 / 1382400) * t ^ 14 + (-2209 / 165888) * t ^ 18) * d_sq
theorem v36_34 (t : ℂ) : (momentPoly 36 z36 3 4).eval t = ((5146755 / 16) * t + (-18651609 / 40) * t ^ 3 + (1401715739 / 4000) * t ^ 5 + (-11127519811073 / 19200000) * t ^ 7 + (2181269370227 / 4800000) * t ^ 9 + (-1735643589991 / 38400000) * t ^ 11 + (-1980652280683 / 46080000) * t ^ 13 + (188801444919 / 12800000) * t ^ 15 + (-453039724271 / 153600000) * t ^ 17 + (-60568222469 / 57600000) * t ^ 19 + (27250905187 / 76800000) * t ^ 21 + (22645912241 / 460800000) * t ^ 25 + (-1029351 / 16) * d * t + (13751073 / 80) * d * t ^ 3 + (-293497201 / 1600) * d * t ^ 5 + (440093096467 / 3840000) * d * t ^ 7 + (-94152342013 / 1920000) * d * t ^ 9 + (23764879727 / 2560000) * d * t ^ 11 + (38164981219 / 46080000) * d * t ^ 13 + (-25132661 / 7680000) * d * t ^ 15 + (21242157 / 409600) * d * t ^ 17 + (740209579 / 11520000) * d * t ^ 19 + (-356971993 / 5120000) * d * t ^ 21 + (27317251 / 18432000) * d * t ^ 25 + (9264159 / 16) * alpha * t + (-54715611 / 80) * alpha * t ^ 3 + (-1877329811 / 8000) * alpha * t ^ 5 + (6930343148551 / 19200000) * alpha * t ^ 7 + (-174477702133 / 9600000) * alpha * t ^ 9 + (-1243955110423 / 38400000) * alpha * t ^ 11 + (163225708973 / 3072000) * alpha * t ^ 13 + (-220971091083 / 12800000) * alpha * t ^ 15 + (-399782008693 / 153600000) * alpha * t ^ 17 + (20716996943 / 57600000) * alpha * t ^ 19 + (-4305554083 / 25600000) * alpha * t ^ 21 + (-32188257097 / 460800000) * alpha * t ^ 25 + (-1029351 / 16) * alpha * d * t + (4428789 / 40) * alpha * d * t ^ 3 + (-46998047 / 2400) * alpha * d * t ^ 5 + (-120518573033 / 3840000) * alpha * d * t ^ 7 + (-12246374587 / 2880000) * alpha * d * t ^ 9 + (153762255923 / 23040000) * alpha * d * t ^ 11 + (272477694907 / 138240000) * alpha * d * t ^ 13 + (1115210167 / 23040000) * alpha * d * t ^ 15 + (-80764133 / 3686400) * alpha * d * t ^ 17 + (-938625653 / 34560000) * alpha * d * t ^ 19 + (617057903 / 46080000) * alpha * d * t ^ 21 + (7468003 / 55296000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_01, v35_02, v35_03, v35_04, v35_10, v35_11, v35_12, v35_13, v35_14, v35_20, v35_21, v35_22, v35_23, v35_24, v35_30, v35_31, v35_32, v35_33, v35_34]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_04, phase36_10, phase36_11, phase36_12, phase36_13, phase36_14, phase36_20, phase36_21, phase36_22, phase36_23, phase36_24, phase36_30, phase36_31, phase36_32, phase36_33, phase36_34]
  try simp only [star_one, star_neg]
  linear_combination ((6273531 / 640) * t ^ 3 + (-44814019 / 1600) * t ^ 5 + (106362089387 / 7680000) * t ^ 7 + (128488229239 / 46080000) * t ^ 9 + (-145617831 / 512000) * t ^ 11 + (-54246834269 / 138240000) * t ^ 13 + (39133172183 / 69120000) * t ^ 15 + (-22145605051 / 110592000) * t ^ 17 + (-11204233823 / 414720000) * t ^ 19 + (13325689919 / 552960000) * t ^ 21 + (189076979 / 82944000) * t ^ 25 + (-9521779 / 960) * d * t ^ 3 + (3476009 / 200) * d * t ^ 5 + (-590963036453 / 69120000) * d * t ^ 7 + (29009344961 / 17280000) * d * t ^ 9 + (-28303819489 / 27648000) * d * t ^ 11 + (4990580387 / 30720000) * d * t ^ 13 + (10395515059 / 138240000) * d * t ^ 15 + (-703452313 / 331776000) * d * t ^ 17 + (40643292323 / 2488320000) * d * t ^ 19 + (-12248992817 / 1658880000) * d * t ^ 21 + (-336661 / 19906560) * d * t ^ 25 + (44593 / 384) * d ^ 2 * t ^ 3 + (-25107 / 400) * d ^ 2 * t ^ 5 + (-196110521 / 2304000) * d ^ 2 * t ^ 7 + (763477739 / 27648000) * d ^ 2 * t ^ 9 + (169867373 / 9216000) * d ^ 2 * t ^ 11 + (-8163117 / 2048000) * d ^ 2 * t ^ 13 + (40116679 / 82944000) * d ^ 2 * t ^ 15 + (-77521 / 16588800) * d ^ 2 * t ^ 17 + (-11628997 / 55296000) * d ^ 2 * t ^ 19 + (273931 / 41472000) * d ^ 2 * t ^ 21) * alpha_sq + ((-44593 / 64) * t ^ 3 + (3838377 / 6400) * t ^ 5 + (326434049 / 1152000) * t ^ 7 + (-49975001 / 256000) * t ^ 9 + (-15720803 / 230400) * t ^ 11 + (314775383 / 11059200) * t ^ 13 + (-53836687 / 27648000) * t ^ 15 + (3826813 / 22118400) * t ^ 17 + (45763189 / 55296000) * t ^ 19 + (4059833 / 110592000) * t ^ 21 + (-4465 / 1327104) * t ^ 25 + (-180719 / 192) * alpha * t ^ 3 + (15375883 / 19200) * alpha * t ^ 5 + (1328384359 / 3456000) * alpha * t ^ 7 + (-834531019 / 3456000) * alpha * t ^ 9 + (-305291657 / 6912000) * alpha * t ^ 11 + (-63168119 / 165888000) * alpha * t ^ 13 + (-346189271 / 27648000) * alpha * t ^ 15 + (1060387 / 66355200) * alpha * t ^ 17 + (19085941 / 497664000) * alpha * t ^ 19 + (-17039833 / 331776000) * alpha * t ^ 21 + (4465 / 3981312) * alpha * t ^ 25) * d_sq
theorem v36_40 (t : ℂ) : (momentPoly 36 z36 4 0).eval t = ((7740429 / 16000) * t ^ 4 + (-14063353 / 16000) * t ^ 6 + (14141929 / 32000) * t ^ 8 + (-104679 / 1000) * t ^ 10 + (1631463 / 128000) * t ^ 16 + (-20809 / 9600) * d * t ^ 4 + (3527 / 3200) * d * t ^ 6 + (-2003 / 1280) * d * t ^ 8 + (3149 / 800) * d * t ^ 10 + (95 / 3072) * d * t ^ 16 + (36374693 / 48000) * alpha * t ^ 4 + (-43028411 / 48000) * alpha * t ^ 6 + (18914413 / 96000) * alpha * t ^ 8 + (149981 / 9000) * alpha * t ^ 10 + (-2393167 / 1152000) * alpha * t ^ 16 + (-36681 / 3200) * alpha * d * t ^ 4 + (68617 / 9600) * alpha * d * t ^ 6 + (617 / 3840) * alpha * d * t ^ 8 + (9497 / 7200) * alpha * d * t ^ 10 + (95 / 9216) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_10, v35_20, v35_30, v35_40]
  try simp only [phase36_00, phase36_10, phase36_20, phase36_30, phase36_40]
  try simp only [star_one, star_neg]
  linear_combination ((14147 / 7200) * t ^ 4 + (3715757 / 115200) * t ^ 6 + (-4389 / 512) * t ^ 8 + (-3497 / 21600) * t ^ 10 + (-31819 / 14400) * d * t ^ 4 + (22027 / 28800) * d * t ^ 6 + (-73 / 1440) * d * t ^ 8 + (17719 / 43200) * d * t ^ 10 + (47 / 192) * d ^ 2 * t ^ 4 + (-3211 / 13824) * d ^ 2 * t ^ 6 + (-1 / 13824) * d ^ 2 * t ^ 8) * alpha_sq + ((53 / 2880) * t ^ 4 + (761 / 3840) * t ^ 6 + (-1 / 2304) * t ^ 8 + (47 / 1728) * t ^ 10 + (-2873 / 2880) * alpha * t ^ 4 + (2839 / 3840) * alpha * t ^ 6 + (1 / 2304) * alpha * t ^ 8 + (-47 / 1728) * alpha * t ^ 10) * d_sq
theorem v36_41 (t : ℂ) : (momentPoly 36 z36 4 1).eval t = ((-1110831 / 160) * t ^ 3 + (471526727 / 64000) * t ^ 5 + (-21375277 / 32000) * t ^ 7 + (-2976343 / 128000) * t ^ 9 + (-7324001 / 32000) * t ^ 11 + (830551 / 128000) * t ^ 17 + (122567 / 160) * d * t ^ 3 + (-227900807 / 192000) * d * t ^ 5 + (13203419 / 32000) * d * t ^ 7 + (4379221 / 128000) * d * t ^ 9 + (-275359 / 96000) * d * t ^ 11 + (-505441 / 384000) * d * t ^ 17 + (1666603 / 800) * alpha * t ^ 3 + (-347035633 / 192000) * alpha * t ^ 5 + (-35338997 / 96000) * alpha * t ^ 7 + (-157212583 / 384000) * alpha * t ^ 9 + (156054197 / 288000) * alpha * t ^ 11 + (12195403 / 1152000) * alpha * t ^ 17 + (-9591 / 32) * alpha * d * t ^ 3 + (18963427 / 38400) * alpha * d * t ^ 5 + (-996983 / 6400) * alpha * d * t ^ 7 + (-229997 / 5120) * alpha * d * t ^ 9 + (34281 / 6400) * alpha * d * t ^ 11 + (-1985 / 3072) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_01, v35_10, v35_11, v35_20, v35_21, v35_30, v35_31, v35_40, v35_41]
  try simp only [phase36_00, phase36_01, phase36_10, phase36_11, phase36_20, phase36_21, phase36_30, phase36_31, phase36_40, phase36_41]
  try simp only [star_one, star_neg]
  linear_combination ((-61479 / 640) * t ^ 3 + (140323069 / 768000) * t ^ 5 + (10201543 / 1152000) * t ^ 7 + (-160732663 / 4608000) * t ^ 9 + (-5720423 / 3456000) * t ^ 11 + (2300599 / 6912000) * t ^ 17 + (93311 / 960) * d * t ^ 3 + (-136142549 / 1728000) * d * t ^ 5 + (-1059773 / 72000) * d * t ^ 7 + (32595791 / 3456000) * d * t ^ 9 + (4296911 / 2592000) * d * t ^ 11 + (-495043 / 5184000) * d * t ^ 17 + (-437 / 384) * d ^ 2 * t ^ 3 + (-41977 / 276480) * d ^ 2 * t ^ 5 + (31097 / 46080) * d ^ 2 * t ^ 7 + (703 / 36864) * d ^ 2 * t ^ 9 + (-211 / 82944) * d ^ 2 * t ^ 11 + (95 / 165888) * d ^ 2 * t ^ 17) * alpha_sq + ((23 / 4) * t ^ 3 + (-7363 / 11520) * t ^ 5 + (-29557 / 11520) * t ^ 7 + (-11 / 96) * t ^ 9 + (23 / 432) * t ^ 11 + (-115 / 96) * alpha * t ^ 3 + (25987 / 115200) * alpha * t ^ 5 + (7969 / 14400) * alpha * t ^ 7 + (-11759 / 138240) * alpha * t ^ 9 + (152477 / 518400) * alpha * t ^ 11 + (95 / 41472) * alpha * t ^ 17) * d_sq
theorem v36_42 (t : ℂ) : (momentPoly 36 z36 4 2).eval t = ((-10805277 / 40) * t ^ 2 + (935879677 / 1600) * t ^ 4 + (-193725887717 / 480000) * t ^ 6 + (196755388429 / 1920000) * t ^ 8 + (-2057199749 / 96000) * t ^ 10 + (89389862627 / 11520000) * t ^ 12 + (-3428254067 / 2880000) * t ^ 14 + (-1973674367 / 11520000) * t ^ 18 + (203375359 / 1440000) * t ^ 20 + (21741 / 8) * d * t ^ 2 + (-11226769 / 4800) * d * t ^ 4 + (-38932793 / 24000) * d * t ^ 6 + (211020503 / 192000) * d * t ^ 8 + (-2179373 / 48000) * d * t ^ 10 + (433423 / 2560) * d * t ^ 12 + (537557 / 8000) * d * t ^ 14 + (583051 / 192000) * d * t ^ 18 + (103523 / 384000) * d * t ^ 20 + (-12559051 / 120) * alpha * t ^ 2 + (188492987 / 960) * alpha * t ^ 4 + (-16867772119 / 160000) * alpha * t ^ 6 + (19395051377 / 960000) * alpha * t ^ 8 + (-627893169 / 64000) * alpha * t ^ 10 + (213539177 / 120000) * alpha * t ^ 12 + (366746467 / 720000) * alpha * t ^ 14 + (1094293 / 7500) * alpha * t ^ 18 + (-349765649 / 5760000) * alpha * t ^ 20 + (36235 / 24) * alpha * d * t ^ 2 + (-7438757 / 4800) * alpha * d * t ^ 4 + (-40214113 / 72000) * alpha * d * t ^ 6 + (589324201 / 1152000) * alpha * d * t ^ 8 + (36649471 / 192000) * alpha * d * t ^ 10 + (-17723647 / 256000) * alpha * d * t ^ 12 + (3810287 / 576000) * alpha * d * t ^ 14 + (-5486107 / 2304000) * alpha * d * t ^ 18 + (27727 / 1152000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_01, v35_02, v35_10, v35_11, v35_12, v35_20, v35_21, v35_22, v35_30, v35_31, v35_32, v35_40, v35_41, v35_42]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_10, phase36_11, phase36_12, phase36_20, phase36_21, phase36_22, phase36_30, phase36_31, phase36_32, phase36_40, phase36_41, phase36_42]
  try simp only [star_one, star_neg]
  linear_combination ((-50729 / 144) * t ^ 2 + (-211973 / 3600) * t ^ 4 + (1137802721 / 3456000) * t ^ 6 + (6254090639 / 9216000) * t ^ 8 + (-10019476751 / 13824000) * t ^ 10 + (6491937731 / 55296000) * t ^ 12 + (69781963 / 4608000) * t ^ 14 + (272428337 / 55296000) * t ^ 18 + (-4882507 / 1843200) * t ^ 20 + (7247 / 18) * d * t ^ 2 + (109463 / 3600) * d * t ^ 4 + (-53075599 / 144000) * d * t ^ 6 + (-192797507 / 13824000) * d * t ^ 8 + (103122779 / 6912000) * d * t ^ 10 + (161230631 / 27648000) * d * t ^ 12 + (136983343 / 20736000) * d * t ^ 14 + (28664657 / 82944000) * d * t ^ 18 + (30949 / 3456000) * d * t ^ 20 + (-7247 / 144) * d ^ 2 * t ^ 2 + (1139 / 40) * d ^ 2 * t ^ 4 + (27202331 / 691200) * d ^ 2 * t ^ 6 + (-235199029 / 16588800) * d ^ 2 * t ^ 8 + (-19425167 / 2764800) * d ^ 2 * t ^ 10 + (168217 / 6635520) * d ^ 2 * t ^ 12 + (1003853 / 24883200) * d ^ 2 * t ^ 14 + (-141115 / 3981312) * d ^ 2 * t ^ 18 + (95 / 1990656) * d ^ 2 * t ^ 20) * alpha_sq + ((7247 / 72) * t ^ 2 + (31807 / 720) * t ^ 4 + (-400987231 / 1728000) * t ^ 6 + (1086919111 / 13824000) * t ^ 8 + (142010383 / 6912000) * t ^ 10 + (-31701599 / 27648000) * t ^ 12 + (614357 / 4147200) * t ^ 14 + (1958833 / 82944000) * t ^ 18 + (95 / 331776) * t ^ 20 + (7247 / 72) * alpha * t ^ 2 + (-64073 / 720) * alpha * t ^ 4 + (-27020201 / 1728000) * alpha * t ^ 6 + (20674517 / 4608000) * alpha * t ^ 8 + (7013987 / 768000) * alpha * t ^ 10 + (53279123 / 82944000) * alpha * t ^ 12 + (-615881 / 1382400) * alpha * t ^ 14 + (-1063463 / 9216000) * alpha * t ^ 18 + (95 / 331776) * alpha * t ^ 20) * d_sq
theorem v36_43 (t : ℂ) : (momentPoly 36 z36 4 3).eval t = ((5146755 / 16) * t + (-18651609 / 40) * t ^ 3 + (1401715739 / 4000) * t ^ 5 + (-11127519811073 / 19200000) * t ^ 7 + (2181269370227 / 4800000) * t ^ 9 + (-1735643589991 / 38400000) * t ^ 11 + (-1980652280683 / 46080000) * t ^ 13 + (188801444919 / 12800000) * t ^ 15 + (-453039724271 / 153600000) * t ^ 17 + (-60568222469 / 57600000) * t ^ 19 + (27250905187 / 76800000) * t ^ 21 + (22645912241 / 460800000) * t ^ 25 + (-1029351 / 16) * d * t + (13751073 / 80) * d * t ^ 3 + (-293497201 / 1600) * d * t ^ 5 + (440093096467 / 3840000) * d * t ^ 7 + (-94152342013 / 1920000) * d * t ^ 9 + (23764879727 / 2560000) * d * t ^ 11 + (38164981219 / 46080000) * d * t ^ 13 + (-25132661 / 7680000) * d * t ^ 15 + (21242157 / 409600) * d * t ^ 17 + (740209579 / 11520000) * d * t ^ 19 + (-356971993 / 5120000) * d * t ^ 21 + (27317251 / 18432000) * d * t ^ 25 + (-9264159 / 16) * alpha * t + (54715611 / 80) * alpha * t ^ 3 + (1877329811 / 8000) * alpha * t ^ 5 + (-6930343148551 / 19200000) * alpha * t ^ 7 + (174477702133 / 9600000) * alpha * t ^ 9 + (1243955110423 / 38400000) * alpha * t ^ 11 + (-163225708973 / 3072000) * alpha * t ^ 13 + (220971091083 / 12800000) * alpha * t ^ 15 + (399782008693 / 153600000) * alpha * t ^ 17 + (-20716996943 / 57600000) * alpha * t ^ 19 + (4305554083 / 25600000) * alpha * t ^ 21 + (32188257097 / 460800000) * alpha * t ^ 25 + (1029351 / 16) * alpha * d * t + (-4428789 / 40) * alpha * d * t ^ 3 + (46998047 / 2400) * alpha * d * t ^ 5 + (120518573033 / 3840000) * alpha * d * t ^ 7 + (12246374587 / 2880000) * alpha * d * t ^ 9 + (-153762255923 / 23040000) * alpha * d * t ^ 11 + (-272477694907 / 138240000) * alpha * d * t ^ 13 + (-1115210167 / 23040000) * alpha * d * t ^ 15 + (80764133 / 3686400) * alpha * d * t ^ 17 + (938625653 / 34560000) * alpha * d * t ^ 19 + (-617057903 / 46080000) * alpha * d * t ^ 21 + (-7468003 / 55296000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_01, v35_02, v35_03, v35_10, v35_11, v35_12, v35_13, v35_20, v35_21, v35_22, v35_23, v35_30, v35_31, v35_32, v35_33, v35_40, v35_41, v35_42, v35_43]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_10, phase36_11, phase36_12, phase36_13, phase36_20, phase36_21, phase36_22, phase36_23, phase36_30, phase36_31, phase36_32, phase36_33, phase36_40, phase36_41, phase36_42, phase36_43]
  try simp only [star_one, star_neg]
  linear_combination ((6273531 / 640) * t ^ 3 + (-44814019 / 1600) * t ^ 5 + (106362089387 / 7680000) * t ^ 7 + (128488229239 / 46080000) * t ^ 9 + (-145617831 / 512000) * t ^ 11 + (-54246834269 / 138240000) * t ^ 13 + (39133172183 / 69120000) * t ^ 15 + (-22145605051 / 110592000) * t ^ 17 + (-11204233823 / 414720000) * t ^ 19 + (13325689919 / 552960000) * t ^ 21 + (189076979 / 82944000) * t ^ 25 + (-9521779 / 960) * d * t ^ 3 + (3476009 / 200) * d * t ^ 5 + (-590963036453 / 69120000) * d * t ^ 7 + (29009344961 / 17280000) * d * t ^ 9 + (-28303819489 / 27648000) * d * t ^ 11 + (4990580387 / 30720000) * d * t ^ 13 + (10395515059 / 138240000) * d * t ^ 15 + (-703452313 / 331776000) * d * t ^ 17 + (40643292323 / 2488320000) * d * t ^ 19 + (-12248992817 / 1658880000) * d * t ^ 21 + (-336661 / 19906560) * d * t ^ 25 + (44593 / 384) * d ^ 2 * t ^ 3 + (-25107 / 400) * d ^ 2 * t ^ 5 + (-196110521 / 2304000) * d ^ 2 * t ^ 7 + (763477739 / 27648000) * d ^ 2 * t ^ 9 + (169867373 / 9216000) * d ^ 2 * t ^ 11 + (-8163117 / 2048000) * d ^ 2 * t ^ 13 + (40116679 / 82944000) * d ^ 2 * t ^ 15 + (-77521 / 16588800) * d ^ 2 * t ^ 17 + (-11628997 / 55296000) * d ^ 2 * t ^ 19 + (273931 / 41472000) * d ^ 2 * t ^ 21) * alpha_sq + ((-44593 / 64) * t ^ 3 + (3838377 / 6400) * t ^ 5 + (326434049 / 1152000) * t ^ 7 + (-49975001 / 256000) * t ^ 9 + (-15720803 / 230400) * t ^ 11 + (314775383 / 11059200) * t ^ 13 + (-53836687 / 27648000) * t ^ 15 + (3826813 / 22118400) * t ^ 17 + (45763189 / 55296000) * t ^ 19 + (4059833 / 110592000) * t ^ 21 + (-4465 / 1327104) * t ^ 25 + (180719 / 192) * alpha * t ^ 3 + (-15375883 / 19200) * alpha * t ^ 5 + (-1328384359 / 3456000) * alpha * t ^ 7 + (834531019 / 3456000) * alpha * t ^ 9 + (305291657 / 6912000) * alpha * t ^ 11 + (63168119 / 165888000) * alpha * t ^ 13 + (346189271 / 27648000) * alpha * t ^ 15 + (-1060387 / 66355200) * alpha * t ^ 17 + (-19085941 / 497664000) * alpha * t ^ 19 + (17039833 / 331776000) * alpha * t ^ 21 + (-4465 / 3981312) * alpha * t ^ 25) * d_sq
theorem v36_44 (t : ℂ) : (momentPoly 36 z36 4 4).eval t = (37056636 + (-102573744) * t ^ 2 + (12789039601 / 100) * t ^ 4 + (-4870968814111 / 40000) * t ^ 6 + (2872804144291753 / 32000000) * t ^ 8 + (-830211909049849 / 24000000) * t ^ 10 + (36154144732489 / 6400000) * t ^ 12 + (-35645054648363 / 18000000) * t ^ 14 + (714960828085469 / 1152000000) * t ^ 16 + (-5905551247307 / 288000000) * t ^ 18 + (-130010482424483 / 6912000000) * t ^ 20 + (-3882040986983 / 1152000000) * t ^ 22 + (31601952250793 / 4608000000) * t ^ 24 + (-10395194087287 / 3456000000) * t ^ 26 + (1937198098511 / 13824000000) * t ^ 32 + (-986286) * d * t ^ 2 + (36921781 / 20) * d * t ^ 4 + (-796456089 / 1600) * d * t ^ 6 + (-2229498618443 / 3840000) * d * t ^ 8 + (96024110509 / 640000) * d * t ^ 10 + (115928775441 / 1280000) * d * t ^ 12 + (-597461407519 / 11520000) * d * t ^ 14 + (1050326548079 / 46080000) * d * t ^ 16 + (2714277481 / 460800) * d * t ^ 18 + (-94884268139 / 276480000) * d * t ^ 20 + (2618488693 / 46080000) * d * t ^ 22 + (63393373 / 36864000) * d * t ^ 24 + (2170326733 / 27648000) * d * t ^ 26 + (583775 / 884736) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z36, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v35_00, v35_01, v35_02, v35_03, v35_04, v35_10, v35_11, v35_12, v35_13, v35_14, v35_20, v35_21, v35_22, v35_23, v35_24, v35_30, v35_31, v35_32, v35_33, v35_34, v35_40, v35_41, v35_42, v35_43, v35_44]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_04, phase36_10, phase36_11, phase36_12, phase36_13, phase36_14, phase36_20, phase36_21, phase36_22, phase36_23, phase36_24, phase36_30, phase36_31, phase36_32, phase36_33, phase36_34, phase36_40, phase36_41, phase36_42, phase36_43, phase36_44]
  try simp only [star_one, star_neg]
  linear_combination ((1150667 / 12) * t ^ 2 + (-721409 / 24) * t ^ 4 + (-99077914531 / 96000) * t ^ 6 + (9517292232727 / 6400000) * t ^ 8 + (-33800925843373 / 57600000) * t ^ 10 + (7399124362273 / 57600000) * t ^ 12 + (-20174228646307 / 207360000) * t ^ 14 + (5557039137463 / 691200000) * t ^ 16 + (3027714263299 / 691200000) * t ^ 18 + (-14141550019651 / 16588800000) * t ^ 20 + (7420671636841 / 2764800000) * t ^ 22 + (-61179599923 / 88473600) * t ^ 24 + (-94774062997 / 2764800000) * t ^ 26 + (1084112897 / 442368000) * t ^ 32 + (-328762 / 3) * d * t ^ 2 + (482079 / 10) * d * t ^ 4 + (715404031 / 6000) * d * t ^ 6 + (-1891376244467 / 86400000) * d * t ^ 8 + (-494913084131 / 12800000) * d * t ^ 10 + (1214529942287 / 345600000) * d * t ^ 12 + (-823091136851 / 138240000) * d * t ^ 14 + (939752187857 / 691200000) * d * t ^ 16 + (8313153431 / 19200000) * d * t ^ 18 + (-64388311343 / 2073600000) * d * t ^ 20 + (-11044098827 / 2073600000) * d * t ^ 22 + (2033479 / 25920000) * d * t ^ 24 + (4984439401 / 518400000) * d * t ^ 26 + (-95627 / 3110400) * d * t ^ 32 + (164381 / 12) * d ^ 2 * t ^ 2 + (-2177903 / 120) * d ^ 2 * t ^ 4 + (-278647337 / 172800) * d ^ 2 * t ^ 6 + (510277243183 / 103680000) * d ^ 2 * t ^ 8 + (20648007761 / 7680000) * d ^ 2 * t ^ 10 + (-19286693089 / 23040000) * d ^ 2 * t ^ 12 + (-205633084523 / 414720000) * d ^ 2 * t ^ 14 + (-882330211 / 23040000) * d ^ 2 * t ^ 16 + (527158423 / 82944000) * d ^ 2 * t ^ 18 + (47488166837 / 9953280000) * d ^ 2 * t ^ 20 + (-148733417 / 61440000) * d ^ 2 * t ^ 22 + (6819167 / 3981312000) * d ^ 2 * t ^ 24 + (-96127561 / 2985984000) * d ^ 2 * t ^ 26 + (9025 / 95551488) * d ^ 2 * t ^ 32) * alpha_sq + ((-164381 / 3) * t ^ 2 + (1719757 / 20) * t ^ 4 + (-383284909 / 14400) * t ^ 6 + (135489797023 / 17280000) * t ^ 8 + (-222638265451 / 11520000) * t ^ 10 + (46258153943 / 11520000) * t ^ 12 + (449566863631 / 207360000) * t ^ 14 + (915700471 / 34560000) * t ^ 16 + (-138341989 / 6912000) * t ^ 18 + (3343747481 / 829440000) * t ^ 20 + (-1434042497 / 138240000) * t ^ 22 + (21298333 / 331776000) * t ^ 24 + (239150149 / 248832000) * t ^ 26 + (-9025 / 7962624) * t ^ 32) * d_sq
#print axioms v36_00
#print axioms v36_11
#print axioms v36_22
#print axioms v36_33
#print axioms v36_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
noncomputable def z37 : Fin 37 → ℂ := Fin.snoc z36 (r ^ 2 * phiMinus)
theorem v37_00 (t : ℂ) : (momentPoly 37 z37 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00]
  try simp only [phase36_00]
  try simp only [star_one, star_neg]
  ring
theorem v37_01 (t : ℂ) : (momentPoly 37 z37 0 1).eval t = ((3 / 8) * t + (-1 / 24) * d * t + (13 / 24) * alpha * t + (-1 / 24) * alpha * d * t) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_01]
  try simp only [phase36_00, phase36_01]
  try simp only [star_one, star_neg]
  ring
theorem v37_02 (t : ℂ) : (momentPoly 37 z37 0 2).eval t = ((-2487 / 160) * t ^ 2 + (6151 / 480) * t ^ 4 + (11 / 96) * d * t ^ 2 + (-1 / 96) * d * t ^ 4 + (687 / 160) * alpha * t ^ 2 + (-911 / 480) * alpha * t ^ 4 + (-7 / 96) * alpha * d * t ^ 2 + (-1 / 288) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_01, v36_02]
  try simp only [phase36_00, phase36_01, phase36_02]
  try simp only [star_one, star_neg]
  linear_combination ((-3 / 128) * t ^ 2 + (5 / 192) * d * t ^ 2 + (-1 / 384) * d ^ 2 * t ^ 2) * alpha_sq + ((1 / 192) * t ^ 2 + (-1 / 192) * alpha * t ^ 2) * d_sq
theorem v37_03 (t : ℂ) : (momentPoly 37 z37 0 3).eval t = ((-5527 / 160) * t ^ 3 + (3307 / 160) * t ^ 5 + 1 * t ^ 9 + (1463 / 480) * d * t ^ 3 + (-817 / 320) * d * t ^ 5 + (47 / 576) * d * t ^ 9 + (-23023 / 2400) * alpha * t ^ 3 + (4293 / 1600) * alpha * t ^ 5 + (81601 / 14400) * alpha * t ^ 9 + (137 / 96) * alpha * d * t ^ 3 + (-133 / 96) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_01, v36_02, v36_03]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03]
  try simp only [star_one, star_neg]
  linear_combination ((-1733 / 3840) * t ^ 3 + (7561 / 7680) * t ^ 5 + (293 / 640) * d * t ^ 3 + (-153 / 640) * d * t ^ 5 + (-5 / 768) * d ^ 2 * t ^ 3 + (-1 / 1536) * d ^ 2 * t ^ 5) * alpha_sq + ((1 / 32) * t ^ 3 + (1 / 192) * alpha * t ^ 3 + (-1 / 384) * alpha * t ^ 5) * d_sq
theorem v37_04 (t : ℂ) : (momentPoly 37 z37 0 4).eval t = ((20225597 / 48000) * t ^ 4 + (-6228579 / 8000) * t ^ 6 + (27106983 / 64000) * t ^ 8 + (-1475079 / 16000) * t ^ 10 + (7065521 / 576000) * t ^ 16 + (-2097 / 3200) * d * t ^ 4 + (-2693 / 4800) * d * t ^ 6 + (-7537 / 7680) * d * t ^ 8 + (77951 / 28800) * d * t ^ 10 + (95 / 4608) * d * t ^ 16 + (-18653683 / 48000) * alpha * t ^ 4 + (12454523 / 24000) * alpha * t ^ 6 + (-28914451 / 192000) * alpha * t ^ 8 + (-168877 / 48000) * alpha * t ^ 10 + (920521 / 576000) * alpha * t ^ 16 + (175471 / 28800) * alpha * d * t ^ 4 + (-19849 / 4800) * alpha * d * t ^ 6 + (-327 / 2560) * alpha * d * t ^ 8 + (-26117 / 28800) * alpha * d * t ^ 10 + (-95 / 13824) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_01, v36_02, v36_03, v36_04]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_04]
  try simp only [star_one, star_neg]
  linear_combination ((72461 / 57600) * t ^ 4 + (804529 / 38400) * t ^ 6 + (-43643 / 6144) * t ^ 8 + (-10517 / 57600) * t ^ 10 + (-41443 / 28800) * d * t ^ 4 + (1529 / 3600) * d * t ^ 6 + (-1861 / 46080) * d * t ^ 8 + (24817 / 57600) * d * t ^ 10 + (139 / 768) * d ^ 2 * t ^ 4 + (-803 / 4608) * d ^ 2 * t ^ 6 + (-1 / 18432) * d ^ 2 * t ^ 8) * alpha_sq + ((-463 / 5760) * t ^ 4 + (229 / 1280) * t ^ 6 + (-1 / 3072) * t ^ 8 + (47 / 2304) * t ^ 10 + (3707 / 5760) * alpha * t ^ 4 + (-671 / 1280) * alpha * t ^ 6 + (-1 / 3072) * alpha * t ^ 8 + (47 / 2304) * alpha * t ^ 10) * d_sq
theorem v37_10 (t : ℂ) : (momentPoly 37 z37 1 0).eval t = ((3 / 8) * t + (-1 / 24) * d * t + (-13 / 24) * alpha * t + (1 / 24) * alpha * d * t) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_10]
  try simp only [phase36_00, phase36_10]
  try simp only [star_one, star_neg]
  ring
theorem v37_11 (t : ℂ) : (momentPoly 37 z37 1 1).eval t = (37 + (-32) * t ^ 2 + (-1 / 6) * d * t ^ 2) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_01, v36_10, v36_11]
  try simp only [phase36_00, phase36_01, phase36_10, phase36_11]
  try simp only [star_one, star_neg]
  linear_combination ((3 / 128) * t ^ 2 + (-5 / 192) * d * t ^ 2 + (1 / 384) * d ^ 2 * t ^ 2) * alpha_sq + ((-1 / 96) * t ^ 2) * d_sq
theorem v37_12 (t : ℂ) : (momentPoly 37 z37 1 2).eval t = ((219 / 8) * t + (-2243 / 96) * t ^ 3 + (59 / 32) * t ^ 5 + (-73 / 24) * d * t + (1457 / 480) * d * t ^ 3 + (-127 / 480) * d * t ^ 5 + (949 / 24) * alpha * t + (-3919 / 160) * alpha * t ^ 3 + (-4013 / 480) * alpha * t ^ 5 + (-73 / 24) * alpha * d * t + (3001 / 1440) * alpha * d * t ^ 3 + (949 / 1440) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_01, v36_02, v36_10, v36_11, v36_12]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_10, phase36_11, phase36_12]
  try simp only [star_one, star_neg]
  linear_combination ((1733 / 11520) * t ^ 3 + (-7561 / 23040) * t ^ 5 + (-293 / 1920) * d * t ^ 3 + (51 / 640) * d * t ^ 5 + (5 / 2304) * d ^ 2 * t ^ 3 + (1 / 4608) * d ^ 2 * t ^ 5) * alpha_sq + ((-5 / 384) * t ^ 3 + (-1 / 768) * t ^ 5 + (-19 / 1152) * alpha * t ^ 3 + (1 / 2304) * alpha * t ^ 5) * d_sq
theorem v37_13 (t : ℂ) : (momentPoly 37 z37 1 3).eval t = ((-67149 / 40) * t ^ 2 + (6780857 / 2400) * t ^ 4 + (-3728149 / 3200) * t ^ 6 + (-49721 / 9600) * t ^ 10 + (99 / 8) * d * t ^ 2 + (-5653 / 800) * d * t ^ 4 + (-11597 / 3200) * d * t ^ 6 + (-20419 / 28800) * d * t ^ 10 + (18549 / 40) * alpha * t ^ 2 + (-1449373 / 2400) * alpha * t ^ 4 + (492881 / 3200) * alpha * t ^ 6 + (156367 / 28800) * alpha * t ^ 10 + (-63 / 8) * alpha * d * t ^ 2 + (36881 / 7200) * alpha * d * t ^ 4 + (7061 / 3200) * alpha * d * t ^ 6 + (-6773 / 28800) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_01, v36_02, v36_03, v36_10, v36_11, v36_12, v36_13]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_10, phase36_11, phase36_12, phase36_13]
  try simp only [star_one, star_neg]
  linear_combination ((-81 / 32) * t ^ 2 + (160669 / 230400) * t ^ 4 + (26669 / 38400) * t ^ 6 + (10517 / 230400) * t ^ 10 + (45 / 16) * d * t ^ 2 + (-11749 / 14400) * d * t ^ 4 + (-15427 / 19200) * d * t ^ 6 + (-24817 / 230400) * d * t ^ 10 + (-9 / 32) * d ^ 2 * t ^ 2 + (607 / 5120) * d ^ 2 * t ^ 4 + (279 / 2560) * d ^ 2 * t ^ 6) * alpha_sq + ((9 / 16) * t ^ 2 + (329 / 23040) * t ^ 4 + (-3373 / 7680) * t ^ 6 + (47 / 9216) * t ^ 10 + (-9 / 16) * alpha * t ^ 2 + (8011 / 23040) * alpha * t ^ 4 + (673 / 7680) * alpha * t ^ 6 + (-47 / 9216) * alpha * t ^ 10) * d_sq
theorem v37_14 (t : ℂ) : (momentPoly 37 z37 1 4).eval t = ((-392417 / 80) * t ^ 3 + (216519401 / 32000) * t ^ 5 + (-87622703 / 48000) * t ^ 7 + (9667823 / 192000) * t ^ 9 + (-30458317 / 144000) * t ^ 11 + (3569417 / 576000) * t ^ 17 + (103873 / 240) * d * t ^ 3 + (-71019769 / 96000) * d * t ^ 5 + (14390069 / 48000) * d * t ^ 7 + (10102463 / 576000) * d * t ^ 9 + (-651359 / 144000) * d * t ^ 11 + (-458441 / 576000) * d * t ^ 17 + (-1634633 / 1200) * alpha * t ^ 3 + (110797051 / 96000) * alpha * t ^ 5 + (18411929 / 48000) * alpha * t ^ 7 + (293780203 / 576000) * alpha * t ^ 9 + (-98596459 / 144000) * alpha * t ^ 11 + (-6367981 / 576000) * alpha * t ^ 17 + (9727 / 48) * alpha * d * t ^ 3 + (-20521187 / 57600) * alpha * d * t ^ 5 + (3746479 / 28800) * alpha * d * t ^ 7 + (626161 / 23040) * alpha * d * t ^ 9 + (-315679 / 86400) * alpha * d * t ^ 11 + (1985 / 4608) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_01, v36_02, v36_03, v36_04, v36_10, v36_11, v36_12, v36_13, v36_14]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_04, phase36_10, phase36_11, phase36_12, phase36_13, phase36_14]
  try simp only [star_one, star_neg]
  linear_combination ((-123043 / 1920) * t ^ 3 + (44710923 / 256000) * t ^ 5 + (-95235439 / 2304000) * t ^ 7 + (-144357163 / 4608000) * t ^ 9 + (-3488173 / 3456000) * t ^ 11 + (8650271 / 27648000) * t ^ 17 + (20803 / 320) * d * t ^ 3 + (-39205333 / 576000) * d * t ^ 5 + (168469 / 384000) * d * t ^ 7 + (342053 / 48000) * d * t ^ 9 + (1746649 / 1728000) * d * t ^ 11 + (-1042073 / 13824000) * d * t ^ 17 + (-355 / 384) * d ^ 2 * t ^ 3 + (5107 / 30720) * d ^ 2 * t ^ 5 + (43549 / 92160) * d ^ 2 * t ^ 7 + (527 / 36864) * d ^ 2 * t ^ 9 + (-41 / 27648) * d ^ 2 * t ^ 11 + (95 / 221184) * d ^ 2 * t ^ 17) * alpha_sq + ((71 / 16) * t ^ 3 + (-16931 / 11520) * t ^ 5 + (-13691 / 7680) * t ^ 7 + (-11 / 128) * t ^ 9 + (23 / 576) * t ^ 11 + (71 / 96) * alpha * t ^ 3 + (-3031 / 12800) * alpha * t ^ 5 + (-15347 / 57600) * alpha * t ^ 7 + (2701 / 46080) * alpha * t ^ 9 + (-39013 / 172800) * alpha * t ^ 11 + (-95 / 55296) * alpha * t ^ 17) * d_sq
theorem v37_20 (t : ℂ) : (momentPoly 37 z37 2 0).eval t = ((-2487 / 160) * t ^ 2 + (6151 / 480) * t ^ 4 + (11 / 96) * d * t ^ 2 + (-1 / 96) * d * t ^ 4 + (-687 / 160) * alpha * t ^ 2 + (911 / 480) * alpha * t ^ 4 + (7 / 96) * alpha * d * t ^ 2 + (1 / 288) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_10, v36_20]
  try simp only [phase36_00, phase36_10, phase36_20]
  try simp only [star_one, star_neg]
  linear_combination ((-3 / 128) * t ^ 2 + (5 / 192) * d * t ^ 2 + (-1 / 384) * d ^ 2 * t ^ 2) * alpha_sq + ((1 / 192) * t ^ 2 + (1 / 192) * alpha * t ^ 2) * d_sq
theorem v37_21 (t : ℂ) : (momentPoly 37 z37 2 1).eval t = ((219 / 8) * t + (-2243 / 96) * t ^ 3 + (59 / 32) * t ^ 5 + (-73 / 24) * d * t + (1457 / 480) * d * t ^ 3 + (-127 / 480) * d * t ^ 5 + (-949 / 24) * alpha * t + (3919 / 160) * alpha * t ^ 3 + (4013 / 480) * alpha * t ^ 5 + (73 / 24) * alpha * d * t + (-3001 / 1440) * alpha * d * t ^ 3 + (-949 / 1440) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_01, v36_10, v36_11, v36_20, v36_21]
  try simp only [phase36_00, phase36_01, phase36_10, phase36_11, phase36_20, phase36_21]
  try simp only [star_one, star_neg]
  linear_combination ((1733 / 11520) * t ^ 3 + (-7561 / 23040) * t ^ 5 + (-293 / 1920) * d * t ^ 3 + (51 / 640) * d * t ^ 5 + (5 / 2304) * d ^ 2 * t ^ 3 + (1 / 4608) * d ^ 2 * t ^ 5) * alpha_sq + ((-5 / 384) * t ^ 3 + (-1 / 768) * t ^ 5 + (19 / 1152) * alpha * t ^ 3 + (-1 / 2304) * alpha * t ^ 5) * d_sq
theorem v37_22 (t : ℂ) : (momentPoly 37 z37 2 2).eval t = (2701 + (-4608) * t ^ 2 + (10221983 / 4800) * t ^ 4 + (-383719 / 1200) * t ^ 6 + (662893 / 4800) * t ^ 8 + (-24) * d * t ^ 2 + (17177 / 960) * d * t ^ 4 + (3361 / 720) * d * t ^ 6 + (-131 / 576) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_01, v36_02, v36_10, v36_11, v36_12, v36_20, v36_21, v36_22]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_10, phase36_11, phase36_12, phase36_20, phase36_21, phase36_22]
  try simp only [star_one, star_neg]
  linear_combination ((27 / 8) * t ^ 2 + (-7771 / 5760) * t ^ 4 + (-20249 / 2560) * t ^ 6 + (43643 / 18432) * t ^ 8 + (-15 / 4) * d * t ^ 2 + (9029 / 5760) * d * t ^ 4 + (8033 / 8640) * d * t ^ 6 + (1861 / 138240) * d * t ^ 8 + (3 / 8) * d ^ 2 * t ^ 2 + (-629 / 2880) * d ^ 2 * t ^ 4 + (-6029 / 69120) * d ^ 2 * t ^ 6 + (1 / 55296) * d ^ 2 * t ^ 8) * alpha_sq + ((-3 / 2) * t ^ 2 + (1909 / 1920) * t ^ 4 + (679 / 2880) * t ^ 6 + (-1 / 4608) * t ^ 8) * d_sq
theorem v37_23 (t : ℂ) : (momentPoly 37 z37 2 3).eval t = ((23655 / 8) * t + (-159253 / 32) * t ^ 3 + (66297377 / 24000) * t ^ 5 + (-12202799 / 12800) * t ^ 7 + (14531923 / 64000) * t ^ 9 + (34053559 / 576000) * t ^ 11 + (-11699959 / 576000) * t ^ 13 + (-7885 / 24) * d * t + (103447 / 160) * d * t ^ 3 + (-75257 / 192) * d * t ^ 5 + (3542647 / 38400) * d * t ^ 7 + (-50633 / 2560) * d * t ^ 9 + (-214753 / 115200) * d * t ^ 11 + (117257 / 115200) * d * t ^ 13 + (102505 / 24) * alpha * t + (-834747 / 160) * alpha * t ^ 3 + (-1509159 / 4000) * alpha * t ^ 5 + (51459869 / 38400) * alpha * t ^ 7 + (8329247 / 192000) * alpha * t ^ 9 + (-41613703 / 576000) * alpha * t ^ 11 + (42702023 / 576000) * alpha * t ^ 13 + (-7885 / 24) * alpha * d * t + (213071 / 480) * alpha * d * t ^ 3 + (-17611 / 2400) * alpha * d * t ^ 5 + (-10343617 / 115200) * alpha * d * t ^ 7 + (-51283 / 2560) * alpha * d * t ^ 9 + (-327001 / 345600) * alpha * d * t ^ 11 + (48721 / 345600) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_01, v36_02, v36_03, v36_10, v36_11, v36_12, v36_13, v36_20, v36_21, v36_22, v36_23]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_10, phase36_11, phase36_12, phase36_13, phase36_20, phase36_21, phase36_22, phase36_23]
  try simp only [star_one, star_neg]
  linear_combination ((123043 / 3840) * t ^ 3 + (-438773 / 4608) * t ^ 5 + (6907313 / 184320) * t ^ 7 + (54929 / 5120) * t ^ 9 + (-78143 / 138240) * t ^ 11 + (-1352221 / 552960) * t ^ 13 + (-20803 / 640) * d * t ^ 3 + (67273 / 1600) * d * t ^ 5 + (-590561 / 55296) * d * t ^ 7 + (-12653 / 25600) * d * t ^ 9 + (-459809 / 1382400) * d * t ^ 11 + (-24817 / 2764800) * d * t ^ 13 + (355 / 768) * d ^ 2 * t ^ 3 + (-7777 / 38400) * d ^ 2 * t ^ 5 + (-152603 / 921600) * d ^ 2 * t ^ 7 + (-43 / 23040) * d ^ 2 * t ^ 9 + (6673 / 460800) * d ^ 2 * t ^ 11) * alpha_sq + ((-355 / 128) * t ^ 3 + (178651 / 115200) * t ^ 5 + (378709 / 460800) * t ^ 7 + (-263 / 6144) * t ^ 9 + (-43663 / 460800) * t ^ 11 + (47 / 36864) * t ^ 13 + (-1349 / 384) * alpha * t ^ 3 + (238643 / 115200) * alpha * t ^ 5 + (1213571 / 1382400) * alpha * t ^ 7 + (-793 / 18432) * alpha * t ^ 9 + (34463 / 1382400) * alpha * t ^ 11 + (-47 / 110592) * alpha * t ^ 13) * d_sq
theorem v37_24 (t : ℂ) : (momentPoly 37 z37 2 4).eval t = ((-1907529 / 8) * t ^ 2 + (288108847 / 480) * t ^ 4 + (-158994918023 / 320000) * t ^ 6 + (134576362357 / 960000) * t ^ 8 + (-246695911 / 24000) * t ^ 10 + (4369793107 / 720000) * t ^ 12 + (-130707113 / 120000) * t ^ 14 + (-50402717 / 320000) * t ^ 18 + (129786731 / 960000) * t ^ 20 + (42185 / 24) * d * t ^ 2 + (-291743 / 160) * d * t ^ 4 + (-251410073 / 288000) * d * t ^ 6 + (81713657 / 96000) * d * t ^ 8 + (-1350183 / 16000) * d * t ^ 10 + (25957201 / 192000) * d * t ^ 12 + (18672037 / 432000) * d * t ^ 14 + (14273 / 6912) * d * t ^ 18 + (97523 / 576000) * d * t ^ 20 + (526929 / 8) * alpha * t ^ 2 + (-67595543 / 480) * alpha * t ^ 4 + (32991711439 / 360000) * alpha * t ^ 6 + (-7087948847 / 360000) * alpha * t ^ 8 + (583127897 / 115200) * alpha * t ^ 10 + (-1150195657 / 720000) * alpha * t ^ 12 + (-268005893 / 1080000) * alpha * t ^ 14 + (-759965191 / 8640000) * alpha * t ^ 18 + (24699671 / 540000) * alpha * t ^ 20 + (-26845 / 24) * alpha * d * t ^ 2 + (2139811 / 1440) * alpha * d * t ^ 4 + (1370327 / 12800) * alpha * d * t ^ 6 + (-48698323 / 115200) * alpha * d * t ^ 8 + (-713599 / 6400) * alpha * d * t ^ 10 + (1358471 / 24000) * alpha * d * t ^ 12 + (-1195543 / 216000) * alpha * d * t ^ 14 + (2706389 / 1728000) * alpha * d * t ^ 18 + (-33727 / 1728000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_01, v36_02, v36_03, v36_04, v36_10, v36_11, v36_12, v36_13, v36_14, v36_20, v36_21, v36_22, v36_23, v36_24]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_04, phase36_10, phase36_11, phase36_12, phase36_13, phase36_14, phase36_20, phase36_21, phase36_22, phase36_23, phase36_24]
  try simp only [star_one, star_neg]
  linear_combination ((-11505 / 32) * t ^ 2 + (1124683 / 5760) * t ^ 4 + (942711217 / 4608000) * t ^ 6 + (985025461 / 3072000) * t ^ 8 + (-418994281 / 921600) * t ^ 10 + (4977784093 / 55296000) * t ^ 12 + (29805463 / 4608000) * t ^ 14 + (55658573 / 18432000) * t ^ 18 + (-48099709 / 22118400) * t ^ 20 + (19175 / 48) * d * t ^ 2 + (-82243 / 360) * d * t ^ 4 + (-398230297 / 1728000) * d * t ^ 6 + (100821733 / 1536000) * d * t ^ 8 + (706367 / 13824000) * d * t ^ 10 + (80482673 / 5529600) * d * t ^ 12 + (33526037 / 5184000) * d * t ^ 14 + (32620459 / 82944000) * d * t ^ 18 + (24949 / 3456000) * d * t ^ 20 + (-3835 / 96) * d ^ 2 * t ^ 2 + (4249 / 128) * d ^ 2 * t ^ 4 + (14308349 / 552960) * d ^ 2 * t ^ 6 + (-86843927 / 5529600) * d ^ 2 * t ^ 8 + (-6518177 / 1382400) * d ^ 2 * t ^ 10 + (85921 / 1228800) * d ^ 2 * t ^ 12 + (208357 / 8294400) * d ^ 2 * t ^ 14 + (-35255 / 1327104) * d ^ 2 * t ^ 18 + (95 / 2654208) * d ^ 2 * t ^ 20) * alpha_sq + ((3835 / 48) * t ^ 2 + (2303 / 576) * t ^ 4 + (-195249263 / 1152000) * t ^ 6 + (117690323 / 1536000) * t ^ 8 + (21111143 / 1536000) * t ^ 10 + (-11751971 / 9216000) * t ^ 12 + (182683 / 1382400) * t ^ 14 + (633677 / 27648000) * t ^ 18 + (95 / 442368) * t ^ 20 + (-3835 / 48) * alpha * t ^ 2 + (56077 / 576) * alpha * t ^ 4 + (-6162289 / 864000) * alpha * t ^ 6 + (-110263387 / 13824000) * alpha * t ^ 8 + (-27295429 / 4608000) * alpha * t ^ 10 + (-96521 / 1024000) * alpha * t ^ 12 + (432817 / 1382400) * alpha * t ^ 14 + (2248823 / 27648000) * alpha * t ^ 18 + (-95 / 442368) * alpha * t ^ 20) * d_sq
theorem v37_30 (t : ℂ) : (momentPoly 37 z37 3 0).eval t = ((-5527 / 160) * t ^ 3 + (3307 / 160) * t ^ 5 + 1 * t ^ 9 + (1463 / 480) * d * t ^ 3 + (-817 / 320) * d * t ^ 5 + (47 / 576) * d * t ^ 9 + (23023 / 2400) * alpha * t ^ 3 + (-4293 / 1600) * alpha * t ^ 5 + (-81601 / 14400) * alpha * t ^ 9 + (-137 / 96) * alpha * d * t ^ 3 + (133 / 96) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_10, v36_20, v36_30]
  try simp only [phase36_00, phase36_10, phase36_20, phase36_30]
  try simp only [star_one, star_neg]
  linear_combination ((-1733 / 3840) * t ^ 3 + (7561 / 7680) * t ^ 5 + (293 / 640) * d * t ^ 3 + (-153 / 640) * d * t ^ 5 + (-5 / 768) * d ^ 2 * t ^ 3 + (-1 / 1536) * d ^ 2 * t ^ 5) * alpha_sq + ((1 / 32) * t ^ 3 + (-1 / 192) * alpha * t ^ 3 + (1 / 384) * alpha * t ^ 5) * d_sq
theorem v37_31 (t : ℂ) : (momentPoly 37 z37 3 1).eval t = ((-67149 / 40) * t ^ 2 + (6780857 / 2400) * t ^ 4 + (-3728149 / 3200) * t ^ 6 + (-49721 / 9600) * t ^ 10 + (99 / 8) * d * t ^ 2 + (-5653 / 800) * d * t ^ 4 + (-11597 / 3200) * d * t ^ 6 + (-20419 / 28800) * d * t ^ 10 + (-18549 / 40) * alpha * t ^ 2 + (1449373 / 2400) * alpha * t ^ 4 + (-492881 / 3200) * alpha * t ^ 6 + (-156367 / 28800) * alpha * t ^ 10 + (63 / 8) * alpha * d * t ^ 2 + (-36881 / 7200) * alpha * d * t ^ 4 + (-7061 / 3200) * alpha * d * t ^ 6 + (6773 / 28800) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_01, v36_10, v36_11, v36_20, v36_21, v36_30, v36_31]
  try simp only [phase36_00, phase36_01, phase36_10, phase36_11, phase36_20, phase36_21, phase36_30, phase36_31]
  try simp only [star_one, star_neg]
  linear_combination ((-81 / 32) * t ^ 2 + (160669 / 230400) * t ^ 4 + (26669 / 38400) * t ^ 6 + (10517 / 230400) * t ^ 10 + (45 / 16) * d * t ^ 2 + (-11749 / 14400) * d * t ^ 4 + (-15427 / 19200) * d * t ^ 6 + (-24817 / 230400) * d * t ^ 10 + (-9 / 32) * d ^ 2 * t ^ 2 + (607 / 5120) * d ^ 2 * t ^ 4 + (279 / 2560) * d ^ 2 * t ^ 6) * alpha_sq + ((9 / 16) * t ^ 2 + (329 / 23040) * t ^ 4 + (-3373 / 7680) * t ^ 6 + (47 / 9216) * t ^ 10 + (9 / 16) * alpha * t ^ 2 + (-8011 / 23040) * alpha * t ^ 4 + (-673 / 7680) * alpha * t ^ 6 + (47 / 9216) * alpha * t ^ 10) * d_sq
theorem v37_32 (t : ℂ) : (momentPoly 37 z37 3 2).eval t = ((23655 / 8) * t + (-159253 / 32) * t ^ 3 + (66297377 / 24000) * t ^ 5 + (-12202799 / 12800) * t ^ 7 + (14531923 / 64000) * t ^ 9 + (34053559 / 576000) * t ^ 11 + (-11699959 / 576000) * t ^ 13 + (-7885 / 24) * d * t + (103447 / 160) * d * t ^ 3 + (-75257 / 192) * d * t ^ 5 + (3542647 / 38400) * d * t ^ 7 + (-50633 / 2560) * d * t ^ 9 + (-214753 / 115200) * d * t ^ 11 + (117257 / 115200) * d * t ^ 13 + (-102505 / 24) * alpha * t + (834747 / 160) * alpha * t ^ 3 + (1509159 / 4000) * alpha * t ^ 5 + (-51459869 / 38400) * alpha * t ^ 7 + (-8329247 / 192000) * alpha * t ^ 9 + (41613703 / 576000) * alpha * t ^ 11 + (-42702023 / 576000) * alpha * t ^ 13 + (7885 / 24) * alpha * d * t + (-213071 / 480) * alpha * d * t ^ 3 + (17611 / 2400) * alpha * d * t ^ 5 + (10343617 / 115200) * alpha * d * t ^ 7 + (51283 / 2560) * alpha * d * t ^ 9 + (327001 / 345600) * alpha * d * t ^ 11 + (-48721 / 345600) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_01, v36_02, v36_10, v36_11, v36_12, v36_20, v36_21, v36_22, v36_30, v36_31, v36_32]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_10, phase36_11, phase36_12, phase36_20, phase36_21, phase36_22, phase36_30, phase36_31, phase36_32]
  try simp only [star_one, star_neg]
  linear_combination ((123043 / 3840) * t ^ 3 + (-438773 / 4608) * t ^ 5 + (6907313 / 184320) * t ^ 7 + (54929 / 5120) * t ^ 9 + (-78143 / 138240) * t ^ 11 + (-1352221 / 552960) * t ^ 13 + (-20803 / 640) * d * t ^ 3 + (67273 / 1600) * d * t ^ 5 + (-590561 / 55296) * d * t ^ 7 + (-12653 / 25600) * d * t ^ 9 + (-459809 / 1382400) * d * t ^ 11 + (-24817 / 2764800) * d * t ^ 13 + (355 / 768) * d ^ 2 * t ^ 3 + (-7777 / 38400) * d ^ 2 * t ^ 5 + (-152603 / 921600) * d ^ 2 * t ^ 7 + (-43 / 23040) * d ^ 2 * t ^ 9 + (6673 / 460800) * d ^ 2 * t ^ 11) * alpha_sq + ((-355 / 128) * t ^ 3 + (178651 / 115200) * t ^ 5 + (378709 / 460800) * t ^ 7 + (-263 / 6144) * t ^ 9 + (-43663 / 460800) * t ^ 11 + (47 / 36864) * t ^ 13 + (1349 / 384) * alpha * t ^ 3 + (-238643 / 115200) * alpha * t ^ 5 + (-1213571 / 1382400) * alpha * t ^ 7 + (793 / 18432) * alpha * t ^ 9 + (-34463 / 1382400) * alpha * t ^ 11 + (47 / 110592) * alpha * t ^ 13) * d_sq
theorem v37_33 (t : ℂ) : (momentPoly 37 z37 3 3).eval t = (291745 + (-736320) * t ^ 2 + (214661643 / 320) * t ^ 4 + (-795393697 / 2500) * t ^ 6 + (20299098009 / 160000) * t ^ 8 + (-695223651 / 20000) * t ^ 10 + (135849407 / 160000) * t ^ 12 + (-356541679 / 480000) * t ^ 14 + (30792379 / 480000) * t ^ 18 + (-3835) * d * t ^ 2 + (360717 / 64) * d * t ^ 4 + (-110481 / 200) * d * t ^ 6 + (-4640261 / 3840) * d * t ^ 8 + (-282977 / 6400) * d * t ^ 10 + (2014603 / 57600) * d * t ^ 12 + (-892289 / 19200) * d * t ^ 14 + (47 / 288) * d * t ^ 18) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_01, v36_02, v36_03, v36_10, v36_11, v36_12, v36_13, v36_20, v36_21, v36_22, v36_23, v36_30, v36_31, v36_32, v36_33]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_10, phase36_11, phase36_12, phase36_13, phase36_20, phase36_21, phase36_22, phase36_23, phase36_30, phase36_31, phase36_32, phase36_33]
  try simp only [star_one, star_neg]
  linear_combination ((34515 / 64) * t ^ 2 + (-54397 / 128) * t ^ 4 + (-473372629 / 192000) * t ^ 6 + (134236887 / 51200) * t ^ 8 + (-13205221 / 32000) * t ^ 10 + (-189712343 / 27648000) * t ^ 12 + (-8950759 / 576000) * t ^ 14 + (-7608887 / 5529600) * t ^ 18 + (-19175 / 32) * d * t ^ 2 + (63203 / 128) * d * t ^ 4 + (86658263 / 384000) * d * t ^ 6 + (-2892233 / 23040) * d * t ^ 8 + (-1875283 / 64000) * d * t ^ 10 + (45342703 / 4608000) * d * t ^ 12 + (-127941 / 16000) * d * t ^ 14 + (3835 / 64) * d ^ 2 * t ^ 2 + (-4403 / 64) * d ^ 2 * t ^ 4 + (-1745083 / 230400) * d ^ 2 * t ^ 6 + (6329281 / 460800) * d ^ 2 * t ^ 8 + (637 / 150) * d ^ 2 * t ^ 10 + (424507 / 1843200) * d ^ 2 * t ^ 12 + (-49 / 1600) * d ^ 2 * t ^ 14) * alpha_sq + ((-3835 / 16) * t ^ 2 + (40089 / 128) * t ^ 4 + (-194961 / 5120) * t ^ 6 + (-184843 / 7680) * t ^ 8 + (-439261 / 25600) * t ^ 10 + (-1063411 / 691200) * t ^ 12 + (17287 / 28800) * t ^ 14 + (-2209 / 221184) * t ^ 18) * d_sq
theorem v37_34 (t : ℂ) : (momentPoly 37 z37 3 4).eval t = ((3360315 / 8) * t + (-8364147 / 8) * t ^ 3 + (265893993 / 250) * t ^ 5 + (-3544430840267 / 4800000) * t ^ 7 + (14785105962811 / 38400000) * t ^ 9 + (-1302054774323 / 19200000) * t ^ 11 + (-1126317487001 / 46080000) * t ^ 13 + (75781298161 / 7200000) * t ^ 15 + (-505397510369 / 230400000) * t ^ 17 + (-108197696177 / 172800000) * t ^ 19 + (23655127667 / 76800000) * t ^ 21 + (27664545449 / 691200000) * t ^ 25 + (-1120105 / 24) * d * t + (5433153 / 40) * d * t ^ 3 + (-12062797 / 80) * d * t ^ 5 + (10432134229 / 120000) * d * t ^ 7 + (-82398917081 / 2560000) * d * t ^ 9 + (24161681227 / 3840000) * d * t ^ 11 + (30314851141 / 46080000) * d * t ^ 13 + (-18577393 / 160000) * d * t ^ 15 + (20272027 / 614400) * d * t ^ 17 + (1071483013 / 34560000) * d * t ^ 19 + (-1836251953 / 46080000) * d * t ^ 21 + (26165251 / 27648000) * d * t ^ 25 + (14561365 / 24) * alpha * t + (-43841853 / 40) * alpha * t ^ 3 + (827211899 / 4000) * alpha * t ^ 5 + (1142111931877 / 2400000) * alpha * t ^ 7 + (-2332185887949 / 12800000) * alpha * t ^ 9 + (-803346262669 / 19200000) * alpha * t ^ 11 + (2560097532241 / 46080000) * alpha * t ^ 13 + (-35075643281 / 1600000) * alpha * t ^ 15 + (-192501712309 / 76800000) * alpha * t ^ 17 + (60880026569 / 172800000) * alpha * t ^ 19 + (-4372143353 / 25600000) * alpha * t ^ 21 + (-47537993633 / 691200000) * alpha * t ^ 25 + (-1120105 / 24) * alpha * d * t + (3730243 / 40) * alpha * d * t ^ 3 + (-75965339 / 2400) * alpha * d * t ^ 5 + (-68097709219 / 2880000) * alpha * d * t ^ 7 + (48659277601 / 23040000) * alpha * d * t ^ 9 + (63416177311 / 11520000) * alpha * d * t ^ 11 + (153628550293 / 138240000) * alpha * d * t ^ 13 + (-158774197 / 8640000) * alpha * d * t ^ 15 + (-59768903 / 5529600) * alpha * d * t ^ 17 + (-2120907551 / 103680000) * alpha * d * t ^ 19 + (52821373 / 5120000) * alpha * d * t ^ 21 + (4012003 / 82944000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_01, v36_02, v36_03, v36_04, v36_10, v36_11, v36_12, v36_13, v36_14, v36_20, v36_21, v36_22, v36_23, v36_24, v36_30, v36_31, v36_32, v36_33, v36_34]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_04, phase36_10, phase36_11, phase36_12, phase36_13, phase36_14, phase36_20, phase36_21, phase36_22, phase36_23, phase36_24, phase36_30, phase36_31, phase36_32, phase36_33, phase36_34]
  try simp only [star_one, star_neg]
  linear_combination ((2154119 / 320) * t ^ 3 + (-193323017 / 7680) * t ^ 5 + (456011227321 / 23040000) * t ^ 7 + (12359943739 / 20480000) * t ^ 9 + (-17151681601 / 6144000) * t ^ 11 + (-578484361997 / 1105920000) * t ^ 13 + (465588747479 / 552960000) * t ^ 15 + (-11117882963 / 55296000) * t ^ 17 + (-60485619079 / 3317760000) * t ^ 19 + (256917853 / 11520000) * t ^ 21 + (1591569707 / 663552000) * t ^ 25 + (-1092597 / 160) * d * t ^ 3 + (44630199 / 3200) * d * t ^ 5 + (-595686978133 / 69120000) * d * t ^ 7 + (82710473161 / 46080000) * d * t ^ 9 + (-329324579 / 614400) * d * t ^ 11 + (6600300073 / 46080000) * d * t ^ 13 + (122037431 / 2560000) * d * t ^ 15 + (-175252271 / 110592000) * d * t ^ 17 + (8872542761 / 829440000) * d * t ^ 19 + (-1580560067 / 276480000) * d * t ^ 21 + (-471523 / 26542080) * d * t ^ 25 + (6215 / 64) * d ^ 2 * t ^ 3 + (-3581503 / 38400) * d ^ 2 * t ^ 5 + (-99253921 / 2304000) * d ^ 2 * t ^ 7 + (3752340091 / 110592000) * d ^ 2 * t ^ 9 + (683183923 / 55296000) * d ^ 2 * t ^ 11 + (-309956321 / 73728000) * d ^ 2 * t ^ 13 + (50931269 / 110592000) * d ^ 2 * t ^ 15 + (-63121 / 22118400) * d ^ 2 * t ^ 17 + (-34567267 / 221184000) * d ^ 2 * t ^ 19 + (291931 / 55296000) * d ^ 2 * t ^ 21) * alpha_sq + ((-18645 / 32) * t ^ 3 + (2235399 / 3200) * t ^ 5 + (6737591 / 76800) * t ^ 7 + (-1854830239 / 9216000) * t ^ 9 + (-51117559 / 1152000) * t ^ 11 + (3051757 / 108000) * t ^ 13 + (-38413421 / 18432000) * t ^ 15 + (299999 / 2457600) * t ^ 17 + (23306683 / 36864000) * t ^ 19 + (97103 / 4096000) * t ^ 21 + (-4465 / 1769472) * t ^ 25 + (-23617 / 32) * alpha * t ^ 3 + (8052271 / 9600) * alpha * t ^ 5 + (532005851 / 3456000) * alpha * t ^ 7 + (-2243200349 / 9216000) * alpha * t ^ 9 + (-19937311 / 1152000) * alpha * t ^ 11 + (-653631 / 1024000) * alpha * t ^ 13 + (-525745079 / 55296000) * alpha * t ^ 15 + (321803 / 22118400) * alpha * t ^ 17 + (1193191 / 66355200) * alpha * t ^ 19 + (-4118927 / 110592000) * alpha * t ^ 21 + (4465 / 5308416) * alpha * t ^ 25) * d_sq
theorem v37_40 (t : ℂ) : (momentPoly 37 z37 4 0).eval t = ((20225597 / 48000) * t ^ 4 + (-6228579 / 8000) * t ^ 6 + (27106983 / 64000) * t ^ 8 + (-1475079 / 16000) * t ^ 10 + (7065521 / 576000) * t ^ 16 + (-2097 / 3200) * d * t ^ 4 + (-2693 / 4800) * d * t ^ 6 + (-7537 / 7680) * d * t ^ 8 + (77951 / 28800) * d * t ^ 10 + (95 / 4608) * d * t ^ 16 + (18653683 / 48000) * alpha * t ^ 4 + (-12454523 / 24000) * alpha * t ^ 6 + (28914451 / 192000) * alpha * t ^ 8 + (168877 / 48000) * alpha * t ^ 10 + (-920521 / 576000) * alpha * t ^ 16 + (-175471 / 28800) * alpha * d * t ^ 4 + (19849 / 4800) * alpha * d * t ^ 6 + (327 / 2560) * alpha * d * t ^ 8 + (26117 / 28800) * alpha * d * t ^ 10 + (95 / 13824) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_10, v36_20, v36_30, v36_40]
  try simp only [phase36_00, phase36_10, phase36_20, phase36_30, phase36_40]
  try simp only [star_one, star_neg]
  linear_combination ((72461 / 57600) * t ^ 4 + (804529 / 38400) * t ^ 6 + (-43643 / 6144) * t ^ 8 + (-10517 / 57600) * t ^ 10 + (-41443 / 28800) * d * t ^ 4 + (1529 / 3600) * d * t ^ 6 + (-1861 / 46080) * d * t ^ 8 + (24817 / 57600) * d * t ^ 10 + (139 / 768) * d ^ 2 * t ^ 4 + (-803 / 4608) * d ^ 2 * t ^ 6 + (-1 / 18432) * d ^ 2 * t ^ 8) * alpha_sq + ((-463 / 5760) * t ^ 4 + (229 / 1280) * t ^ 6 + (-1 / 3072) * t ^ 8 + (47 / 2304) * t ^ 10 + (-3707 / 5760) * alpha * t ^ 4 + (671 / 1280) * alpha * t ^ 6 + (1 / 3072) * alpha * t ^ 8 + (-47 / 2304) * alpha * t ^ 10) * d_sq
theorem v37_41 (t : ℂ) : (momentPoly 37 z37 4 1).eval t = ((-392417 / 80) * t ^ 3 + (216519401 / 32000) * t ^ 5 + (-87622703 / 48000) * t ^ 7 + (9667823 / 192000) * t ^ 9 + (-30458317 / 144000) * t ^ 11 + (3569417 / 576000) * t ^ 17 + (103873 / 240) * d * t ^ 3 + (-71019769 / 96000) * d * t ^ 5 + (14390069 / 48000) * d * t ^ 7 + (10102463 / 576000) * d * t ^ 9 + (-651359 / 144000) * d * t ^ 11 + (-458441 / 576000) * d * t ^ 17 + (1634633 / 1200) * alpha * t ^ 3 + (-110797051 / 96000) * alpha * t ^ 5 + (-18411929 / 48000) * alpha * t ^ 7 + (-293780203 / 576000) * alpha * t ^ 9 + (98596459 / 144000) * alpha * t ^ 11 + (6367981 / 576000) * alpha * t ^ 17 + (-9727 / 48) * alpha * d * t ^ 3 + (20521187 / 57600) * alpha * d * t ^ 5 + (-3746479 / 28800) * alpha * d * t ^ 7 + (-626161 / 23040) * alpha * d * t ^ 9 + (315679 / 86400) * alpha * d * t ^ 11 + (-1985 / 4608) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_01, v36_10, v36_11, v36_20, v36_21, v36_30, v36_31, v36_40, v36_41]
  try simp only [phase36_00, phase36_01, phase36_10, phase36_11, phase36_20, phase36_21, phase36_30, phase36_31, phase36_40, phase36_41]
  try simp only [star_one, star_neg]
  linear_combination ((-123043 / 1920) * t ^ 3 + (44710923 / 256000) * t ^ 5 + (-95235439 / 2304000) * t ^ 7 + (-144357163 / 4608000) * t ^ 9 + (-3488173 / 3456000) * t ^ 11 + (8650271 / 27648000) * t ^ 17 + (20803 / 320) * d * t ^ 3 + (-39205333 / 576000) * d * t ^ 5 + (168469 / 384000) * d * t ^ 7 + (342053 / 48000) * d * t ^ 9 + (1746649 / 1728000) * d * t ^ 11 + (-1042073 / 13824000) * d * t ^ 17 + (-355 / 384) * d ^ 2 * t ^ 3 + (5107 / 30720) * d ^ 2 * t ^ 5 + (43549 / 92160) * d ^ 2 * t ^ 7 + (527 / 36864) * d ^ 2 * t ^ 9 + (-41 / 27648) * d ^ 2 * t ^ 11 + (95 / 221184) * d ^ 2 * t ^ 17) * alpha_sq + ((71 / 16) * t ^ 3 + (-16931 / 11520) * t ^ 5 + (-13691 / 7680) * t ^ 7 + (-11 / 128) * t ^ 9 + (23 / 576) * t ^ 11 + (-71 / 96) * alpha * t ^ 3 + (3031 / 12800) * alpha * t ^ 5 + (15347 / 57600) * alpha * t ^ 7 + (-2701 / 46080) * alpha * t ^ 9 + (39013 / 172800) * alpha * t ^ 11 + (95 / 55296) * alpha * t ^ 17) * d_sq
theorem v37_42 (t : ℂ) : (momentPoly 37 z37 4 2).eval t = ((-1907529 / 8) * t ^ 2 + (288108847 / 480) * t ^ 4 + (-158994918023 / 320000) * t ^ 6 + (134576362357 / 960000) * t ^ 8 + (-246695911 / 24000) * t ^ 10 + (4369793107 / 720000) * t ^ 12 + (-130707113 / 120000) * t ^ 14 + (-50402717 / 320000) * t ^ 18 + (129786731 / 960000) * t ^ 20 + (42185 / 24) * d * t ^ 2 + (-291743 / 160) * d * t ^ 4 + (-251410073 / 288000) * d * t ^ 6 + (81713657 / 96000) * d * t ^ 8 + (-1350183 / 16000) * d * t ^ 10 + (25957201 / 192000) * d * t ^ 12 + (18672037 / 432000) * d * t ^ 14 + (14273 / 6912) * d * t ^ 18 + (97523 / 576000) * d * t ^ 20 + (-526929 / 8) * alpha * t ^ 2 + (67595543 / 480) * alpha * t ^ 4 + (-32991711439 / 360000) * alpha * t ^ 6 + (7087948847 / 360000) * alpha * t ^ 8 + (-583127897 / 115200) * alpha * t ^ 10 + (1150195657 / 720000) * alpha * t ^ 12 + (268005893 / 1080000) * alpha * t ^ 14 + (759965191 / 8640000) * alpha * t ^ 18 + (-24699671 / 540000) * alpha * t ^ 20 + (26845 / 24) * alpha * d * t ^ 2 + (-2139811 / 1440) * alpha * d * t ^ 4 + (-1370327 / 12800) * alpha * d * t ^ 6 + (48698323 / 115200) * alpha * d * t ^ 8 + (713599 / 6400) * alpha * d * t ^ 10 + (-1358471 / 24000) * alpha * d * t ^ 12 + (1195543 / 216000) * alpha * d * t ^ 14 + (-2706389 / 1728000) * alpha * d * t ^ 18 + (33727 / 1728000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_01, v36_02, v36_10, v36_11, v36_12, v36_20, v36_21, v36_22, v36_30, v36_31, v36_32, v36_40, v36_41, v36_42]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_10, phase36_11, phase36_12, phase36_20, phase36_21, phase36_22, phase36_30, phase36_31, phase36_32, phase36_40, phase36_41, phase36_42]
  try simp only [star_one, star_neg]
  linear_combination ((-11505 / 32) * t ^ 2 + (1124683 / 5760) * t ^ 4 + (942711217 / 4608000) * t ^ 6 + (985025461 / 3072000) * t ^ 8 + (-418994281 / 921600) * t ^ 10 + (4977784093 / 55296000) * t ^ 12 + (29805463 / 4608000) * t ^ 14 + (55658573 / 18432000) * t ^ 18 + (-48099709 / 22118400) * t ^ 20 + (19175 / 48) * d * t ^ 2 + (-82243 / 360) * d * t ^ 4 + (-398230297 / 1728000) * d * t ^ 6 + (100821733 / 1536000) * d * t ^ 8 + (706367 / 13824000) * d * t ^ 10 + (80482673 / 5529600) * d * t ^ 12 + (33526037 / 5184000) * d * t ^ 14 + (32620459 / 82944000) * d * t ^ 18 + (24949 / 3456000) * d * t ^ 20 + (-3835 / 96) * d ^ 2 * t ^ 2 + (4249 / 128) * d ^ 2 * t ^ 4 + (14308349 / 552960) * d ^ 2 * t ^ 6 + (-86843927 / 5529600) * d ^ 2 * t ^ 8 + (-6518177 / 1382400) * d ^ 2 * t ^ 10 + (85921 / 1228800) * d ^ 2 * t ^ 12 + (208357 / 8294400) * d ^ 2 * t ^ 14 + (-35255 / 1327104) * d ^ 2 * t ^ 18 + (95 / 2654208) * d ^ 2 * t ^ 20) * alpha_sq + ((3835 / 48) * t ^ 2 + (2303 / 576) * t ^ 4 + (-195249263 / 1152000) * t ^ 6 + (117690323 / 1536000) * t ^ 8 + (21111143 / 1536000) * t ^ 10 + (-11751971 / 9216000) * t ^ 12 + (182683 / 1382400) * t ^ 14 + (633677 / 27648000) * t ^ 18 + (95 / 442368) * t ^ 20 + (3835 / 48) * alpha * t ^ 2 + (-56077 / 576) * alpha * t ^ 4 + (6162289 / 864000) * alpha * t ^ 6 + (110263387 / 13824000) * alpha * t ^ 8 + (27295429 / 4608000) * alpha * t ^ 10 + (96521 / 1024000) * alpha * t ^ 12 + (-432817 / 1382400) * alpha * t ^ 14 + (-2248823 / 27648000) * alpha * t ^ 18 + (95 / 442368) * alpha * t ^ 20) * d_sq
theorem v37_43 (t : ℂ) : (momentPoly 37 z37 4 3).eval t = ((3360315 / 8) * t + (-8364147 / 8) * t ^ 3 + (265893993 / 250) * t ^ 5 + (-3544430840267 / 4800000) * t ^ 7 + (14785105962811 / 38400000) * t ^ 9 + (-1302054774323 / 19200000) * t ^ 11 + (-1126317487001 / 46080000) * t ^ 13 + (75781298161 / 7200000) * t ^ 15 + (-505397510369 / 230400000) * t ^ 17 + (-108197696177 / 172800000) * t ^ 19 + (23655127667 / 76800000) * t ^ 21 + (27664545449 / 691200000) * t ^ 25 + (-1120105 / 24) * d * t + (5433153 / 40) * d * t ^ 3 + (-12062797 / 80) * d * t ^ 5 + (10432134229 / 120000) * d * t ^ 7 + (-82398917081 / 2560000) * d * t ^ 9 + (24161681227 / 3840000) * d * t ^ 11 + (30314851141 / 46080000) * d * t ^ 13 + (-18577393 / 160000) * d * t ^ 15 + (20272027 / 614400) * d * t ^ 17 + (1071483013 / 34560000) * d * t ^ 19 + (-1836251953 / 46080000) * d * t ^ 21 + (26165251 / 27648000) * d * t ^ 25 + (-14561365 / 24) * alpha * t + (43841853 / 40) * alpha * t ^ 3 + (-827211899 / 4000) * alpha * t ^ 5 + (-1142111931877 / 2400000) * alpha * t ^ 7 + (2332185887949 / 12800000) * alpha * t ^ 9 + (803346262669 / 19200000) * alpha * t ^ 11 + (-2560097532241 / 46080000) * alpha * t ^ 13 + (35075643281 / 1600000) * alpha * t ^ 15 + (192501712309 / 76800000) * alpha * t ^ 17 + (-60880026569 / 172800000) * alpha * t ^ 19 + (4372143353 / 25600000) * alpha * t ^ 21 + (47537993633 / 691200000) * alpha * t ^ 25 + (1120105 / 24) * alpha * d * t + (-3730243 / 40) * alpha * d * t ^ 3 + (75965339 / 2400) * alpha * d * t ^ 5 + (68097709219 / 2880000) * alpha * d * t ^ 7 + (-48659277601 / 23040000) * alpha * d * t ^ 9 + (-63416177311 / 11520000) * alpha * d * t ^ 11 + (-153628550293 / 138240000) * alpha * d * t ^ 13 + (158774197 / 8640000) * alpha * d * t ^ 15 + (59768903 / 5529600) * alpha * d * t ^ 17 + (2120907551 / 103680000) * alpha * d * t ^ 19 + (-52821373 / 5120000) * alpha * d * t ^ 21 + (-4012003 / 82944000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_01, v36_02, v36_03, v36_10, v36_11, v36_12, v36_13, v36_20, v36_21, v36_22, v36_23, v36_30, v36_31, v36_32, v36_33, v36_40, v36_41, v36_42, v36_43]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_10, phase36_11, phase36_12, phase36_13, phase36_20, phase36_21, phase36_22, phase36_23, phase36_30, phase36_31, phase36_32, phase36_33, phase36_40, phase36_41, phase36_42, phase36_43]
  try simp only [star_one, star_neg]
  linear_combination ((2154119 / 320) * t ^ 3 + (-193323017 / 7680) * t ^ 5 + (456011227321 / 23040000) * t ^ 7 + (12359943739 / 20480000) * t ^ 9 + (-17151681601 / 6144000) * t ^ 11 + (-578484361997 / 1105920000) * t ^ 13 + (465588747479 / 552960000) * t ^ 15 + (-11117882963 / 55296000) * t ^ 17 + (-60485619079 / 3317760000) * t ^ 19 + (256917853 / 11520000) * t ^ 21 + (1591569707 / 663552000) * t ^ 25 + (-1092597 / 160) * d * t ^ 3 + (44630199 / 3200) * d * t ^ 5 + (-595686978133 / 69120000) * d * t ^ 7 + (82710473161 / 46080000) * d * t ^ 9 + (-329324579 / 614400) * d * t ^ 11 + (6600300073 / 46080000) * d * t ^ 13 + (122037431 / 2560000) * d * t ^ 15 + (-175252271 / 110592000) * d * t ^ 17 + (8872542761 / 829440000) * d * t ^ 19 + (-1580560067 / 276480000) * d * t ^ 21 + (-471523 / 26542080) * d * t ^ 25 + (6215 / 64) * d ^ 2 * t ^ 3 + (-3581503 / 38400) * d ^ 2 * t ^ 5 + (-99253921 / 2304000) * d ^ 2 * t ^ 7 + (3752340091 / 110592000) * d ^ 2 * t ^ 9 + (683183923 / 55296000) * d ^ 2 * t ^ 11 + (-309956321 / 73728000) * d ^ 2 * t ^ 13 + (50931269 / 110592000) * d ^ 2 * t ^ 15 + (-63121 / 22118400) * d ^ 2 * t ^ 17 + (-34567267 / 221184000) * d ^ 2 * t ^ 19 + (291931 / 55296000) * d ^ 2 * t ^ 21) * alpha_sq + ((-18645 / 32) * t ^ 3 + (2235399 / 3200) * t ^ 5 + (6737591 / 76800) * t ^ 7 + (-1854830239 / 9216000) * t ^ 9 + (-51117559 / 1152000) * t ^ 11 + (3051757 / 108000) * t ^ 13 + (-38413421 / 18432000) * t ^ 15 + (299999 / 2457600) * t ^ 17 + (23306683 / 36864000) * t ^ 19 + (97103 / 4096000) * t ^ 21 + (-4465 / 1769472) * t ^ 25 + (23617 / 32) * alpha * t ^ 3 + (-8052271 / 9600) * alpha * t ^ 5 + (-532005851 / 3456000) * alpha * t ^ 7 + (2243200349 / 9216000) * alpha * t ^ 9 + (19937311 / 1152000) * alpha * t ^ 11 + (653631 / 1024000) * alpha * t ^ 13 + (525745079 / 55296000) * alpha * t ^ 15 + (-321803 / 22118400) * alpha * t ^ 17 + (-1193191 / 66355200) * alpha * t ^ 19 + (4118927 / 110592000) * alpha * t ^ 21 + (-4465 / 5308416) * alpha * t ^ 25) * d_sq
theorem v37_44 (t : ℂ) : (momentPoly 37 z37 4 4).eval t = (41443885 + (-137537792) * t ^ 2 + (74099154767 / 400) * t ^ 4 + (-730539892761 / 5000) * t ^ 6 + (2769910593296233 / 32000000) * t ^ 8 + (-438512853110617 / 12000000) * t ^ 10 + (113137183856611 / 15360000) * t ^ 12 + (-168909500089997 / 192000000) * t ^ 14 + (1163269462337893 / 2304000000) * t ^ 16 + (-7479929482277 / 288000000) * t ^ 18 + (-70368318872639 / 3456000000) * t ^ 20 + (-5270725719719 / 576000000) * t ^ 22 + (697868453941 / 96000000) * t ^ 24 + (-532943646677 / 216000000) * t ^ 26 + (839493493193 / 6912000000) * t ^ 32 + (-2149028 / 3) * d * t ^ 2 + (124516073 / 80) * d * t ^ 4 + (-416532877 / 600) * d * t ^ 6 + (-1462408270807 / 3840000) * d * t ^ 8 + (278914370321 / 1440000) * d * t ^ 10 + (2831312720569 / 46080000) * d * t ^ 12 + (-2880372435941 / 69120000) * d * t ^ 14 + (1647654787897 / 92160000) * d * t ^ 16 + (561602381 / 153600) * d * t ^ 18 + (-40177752823 / 138240000) * d * t ^ 20 + (3523034123 / 69120000) * d * t ^ 22 + (951707 / 864000) * d * t ^ 24 + (140170163 / 2592000) * d * t ^ 26 + (583775 / 1327104) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z37, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v36_00, v36_01, v36_02, v36_03, v36_04, v36_10, v36_11, v36_12, v36_13, v36_14, v36_20, v36_21, v36_22, v36_23, v36_24, v36_30, v36_31, v36_32, v36_33, v36_34, v36_40, v36_41, v36_42, v36_43, v36_44]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_04, phase36_10, phase36_11, phase36_12, phase36_13, phase36_14, phase36_20, phase36_21, phase36_22, phase36_23, phase36_24, phase36_30, phase36_31, phase36_32, phase36_33, phase36_34, phase36_40, phase36_41, phase36_42, phase36_43, phase36_44]
  try simp only [star_one, star_neg]
  linear_combination ((1611771 / 16) * t ^ 2 + (-56331979 / 480) * t ^ 4 + (-64713311663 / 96000) * t ^ 6 + (142871805114551 / 115200000) * t ^ 8 + (-72708237852791 / 115200000) * t ^ 10 + (40281810143903 / 345600000) * t ^ 12 + (-2833742984641 / 55296000) * t ^ 14 + (5061626205103 / 691200000) * t ^ 16 + (6023185679071 / 2764800000) * t ^ 18 + (-2129310501911 / 16588800000) * t ^ 20 + (9386789374487 / 5529600000) * t ^ 22 + (-48607619633 / 88473600) * t ^ 24 + (-15762317249 / 921600000) * t ^ 26 + (10570618639 / 5308416000) * t ^ 32 + (-2686285 / 24) * d * t ^ 2 + (65451221 / 480) * d * t ^ 4 + (399143597 / 9000) * d * t ^ 6 + (-6176399090287 / 86400000) * d * t ^ 8 + (-1173120070397 / 345600000) * d * t ^ 10 + (13482489832403 / 1382400000) * d * t ^ 12 + (-23251001663 / 3240000) * d * t ^ 14 + (6515527716413 / 2764800000) * d * t ^ 16 + (150480939383 / 345600000) * d * t ^ 18 + (-2474320283 / 57600000) * d * t ^ 20 + (51034651417 / 8294400000) * d * t ^ 22 + (504151 / 6480000) * d * t ^ 24 + (122838011299 / 12441600000) * d * t ^ 26 + (-38470649 / 1592524800) * d * t ^ 32 + (537257 / 48) * d ^ 2 * t ^ 2 + (-4559621 / 240) * d ^ 2 * t ^ 4 + (186416977 / 57600) * d ^ 2 * t ^ 6 + (366929629099 / 69120000) * d ^ 2 * t ^ 8 + (1579258759 / 2160000) * d ^ 2 * t ^ 10 + (-304068482441 / 276480000) * d ^ 2 * t ^ 12 + (-269390462917 / 829440000) * d ^ 2 * t ^ 14 + (-5258404783 / 552960000) * d ^ 2 * t ^ 16 + (139687271 / 36864000) * d ^ 2 * t ^ 18 + (14756658323 / 3317760000) * d ^ 2 * t ^ 20 + (-7406312671 / 3317760000) * d ^ 2 * t ^ 22 + (2130823 / 1327104000) * d ^ 2 * t ^ 24 + (-13381859 / 995328000) * d ^ 2 * t ^ 26 + (9025 / 127401984) * d ^ 2 * t ^ 32) * alpha_sq + ((-537257 / 12) * t ^ 2 + (13838341 / 160) * t ^ 4 + (-9743857 / 240) * t ^ 6 + (9121558771 / 2880000) * t ^ 8 + (-120989752247 / 11520000) * t ^ 10 + (1288463575679 / 276480000) * t ^ 12 + (23036338597 / 15360000) * t ^ 14 + (-17714150081 / 184320000) * t ^ 16 + (-134524681 / 13824000) * t ^ 18 + (-457133461 / 276480000) * t ^ 20 + (-82186103 / 17280000) * t ^ 22 + (612319 / 13824000) * t ^ 24 + (26368003 / 41472000) * t ^ 26 + (-9025 / 10616832) * t ^ 32) * d_sq
#print axioms v37_00
#print axioms v37_11
#print axioms v37_22
#print axioms v37_33
#print axioms v37_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
noncomputable def z38 : Fin 38 → ℂ := Fin.snoc z37 (r ^ 2 * phiMinus)
theorem v38_00 (t : ℂ) : (momentPoly 38 z38 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00]
  try simp only [phase36_00]
  try simp only [star_one, star_neg]
  ring
theorem v38_01 (t : ℂ) : (momentPoly 38 z38 0 1).eval t = ((7 / 16) * t + (-1 / 48) * d * t + (25 / 48) * alpha * t + (-1 / 48) * alpha * d * t) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_01]
  try simp only [phase36_00, phase36_01]
  try simp only [star_one, star_neg]
  ring
theorem v38_02 (t : ℂ) : (momentPoly 38 z38 0 2).eval t = ((-6451 / 480) * t ^ 2 + (11827 / 960) * t ^ 4 + (5 / 96) * d * t ^ 2 + (-1 / 192) * d * t ^ 4 + (377 / 160) * alpha * t ^ 2 + (-449 / 320) * alpha * t ^ 4 + (-11 / 288) * alpha * d * t ^ 2 + (-1 / 576) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_01, v37_02]
  try simp only [phase36_00, phase36_01, phase36_02]
  try simp only [star_one, star_neg]
  linear_combination ((-13 / 576) * t ^ 2 + (7 / 288) * d * t ^ 2 + (-1 / 576) * d ^ 2 * t ^ 2) * alpha_sq + ((1 / 288) * t ^ 2 + (-1 / 288) * alpha * t ^ 2) * d_sq
theorem v38_03 (t : ℂ) : (momentPoly 38 z38 0 3).eval t = ((-7909 / 320) * t ^ 3 + (6319 / 320) * t ^ 5 + 1 * t ^ 9 + (307 / 240) * d * t ^ 3 + (-277 / 240) * d * t ^ 5 + (47 / 1152) * d * t ^ 9 + (-7589 / 1200) * alpha * t ^ 3 + (341 / 1200) * alpha * t ^ 5 + (166777 / 28800) * alpha * t ^ 9 + (45 / 64) * alpha * d * t ^ 3 + (-133 / 192) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_01, v37_02, v37_03]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03]
  try simp only [star_one, star_neg]
  linear_combination ((-687 / 2560) * t ^ 3 + (1181 / 1280) * t ^ 5 + (131 / 480) * d * t ^ 3 + (-511 / 2880) * d * t ^ 5 + (-7 / 1536) * d ^ 2 * t ^ 3 + (-1 / 2304) * d ^ 2 * t ^ 5) * alpha_sq + ((1 / 48) * t ^ 3 + (1 / 384) * alpha * t ^ 3 + (-1 / 576) * alpha * t ^ 5) * d_sq
theorem v38_04 (t : ℂ) : (momentPoly 38 z38 0 4).eval t = ((16869157 / 48000) * t ^ 4 + (-21917551 / 32000) * t ^ 6 + (77238199 / 192000) * t ^ 8 + (-12029771 / 144000) * t ^ 10 + (13578917 / 1152000) * t ^ 16 + (-163 / 9600) * d * t ^ 4 + (-15451 / 19200) * d * t ^ 6 + (-1177 / 2560) * d * t ^ 8 + (40163 / 28800) * d * t ^ 10 + (95 / 9216) * d * t ^ 16 + (-8373923 / 48000) * alpha * t ^ 4 + (8649829 / 32000) * alpha * t ^ 6 + (-20552201 / 192000) * alpha * t ^ 8 + (92701 / 16000) * alpha * t ^ 10 + (143213 / 128000) * alpha * t ^ 16 + (72503 / 28800) * alpha * d * t ^ 4 + (-11481 / 6400) * alpha * d * t ^ 6 + (-1709 / 23040) * alpha * d * t ^ 8 + (-40363 / 86400) * alpha * d * t ^ 10 + (-95 / 27648) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_01, v37_02, v37_03, v37_04]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_04]
  try simp only [star_one, star_neg]
  linear_combination ((23023 / 28800) * t ^ 4 + (320601 / 25600) * t ^ 6 + (-17309 / 3072) * t ^ 8 + (-17563 / 86400) * t ^ 10 + (-551 / 600) * d * t ^ 4 + (19273 / 115200) * d * t ^ 6 + (-77 / 2560) * d * t ^ 8 + (39013 / 86400) * d * t ^ 10 + (137 / 1152) * d ^ 2 * t ^ 4 + (-119 / 1024) * d ^ 2 * t ^ 6 + (-1 / 27648) * d ^ 2 * t ^ 8) * alpha_sq + ((-37 / 360) * t ^ 4 + (357 / 2560) * t ^ 6 + (-1 / 4608) * t ^ 8 + (47 / 3456) * t ^ 10 + (179 / 480) * alpha * t ^ 4 + (-843 / 2560) * alpha * t ^ 6 + (-1 / 4608) * alpha * t ^ 8 + (47 / 3456) * alpha * t ^ 10) * d_sq
theorem v38_10 (t : ℂ) : (momentPoly 38 z38 1 0).eval t = ((7 / 16) * t + (-1 / 48) * d * t + (-25 / 48) * alpha * t + (1 / 48) * alpha * d * t) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_10]
  try simp only [phase36_00, phase36_10]
  try simp only [star_one, star_neg]
  ring
theorem v38_11 (t : ℂ) : (momentPoly 38 z38 1 1).eval t = (38 + (-36) * t ^ 2 + (-1 / 12) * d * t ^ 2) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_01, v37_10, v37_11]
  try simp only [phase36_00, phase36_01, phase36_10, phase36_11]
  try simp only [star_one, star_neg]
  linear_combination ((13 / 576) * t ^ 2 + (-7 / 288) * d * t ^ 2 + (1 / 576) * d ^ 2 * t ^ 2) * alpha_sq + ((-1 / 144) * t ^ 2) * d_sq
theorem v38_12 (t : ℂ) : (momentPoly 38 z38 1 2).eval t = ((525 / 16) * t + (-16237 / 480) * t ^ 3 + (923 / 320) * t ^ 5 + (-25 / 16) * d * t + (131 / 80) * d * t ^ 3 + (-49 / 320) * d * t ^ 5 + (625 / 16) * alpha * t + (-883 / 30) * alpha * t ^ 3 + (-7289 / 960) * alpha * t ^ 5 + (-25 / 16) * alpha * d * t + (187 / 160) * alpha * d * t ^ 3 + (889 / 2880) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_01, v37_02, v37_10, v37_11, v37_12]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_10, phase36_11, phase36_12]
  try simp only [star_one, star_neg]
  linear_combination ((229 / 2560) * t ^ 3 + (-1181 / 3840) * t ^ 5 + (-131 / 1440) * d * t ^ 3 + (511 / 8640) * d * t ^ 5 + (7 / 4608) * d ^ 2 * t ^ 3 + (1 / 6912) * d ^ 2 * t ^ 5) * alpha_sq + ((-7 / 768) * t ^ 3 + (-1 / 1152) * t ^ 5 + (-25 / 2304) * alpha * t ^ 3 + (1 / 3456) * alpha * t ^ 5) * d_sq
theorem v38_13 (t : ℂ) : (momentPoly 38 z38 1 3).eval t = ((-238687 / 160) * t ^ 2 + (5318681 / 1920) * t ^ 4 + (-409443 / 320) * t ^ 6 + (-4251 / 1280) * t ^ 10 + (185 / 32) * d * t ^ 2 + (-34943 / 9600) * d * t ^ 4 + (-3827 / 2400) * d * t ^ 6 + (-20719 / 57600) * d * t ^ 10 + (41847 / 160) * alpha * t ^ 2 + (-3788569 / 9600) * alpha * t ^ 4 + (638443 / 4800) * alpha * t ^ 6 + (224803 / 57600) * alpha * t ^ 10 + (-407 / 96) * alpha * d * t ^ 2 + (91837 / 28800) * alpha * d * t ^ 4 + (1213 / 1200) * alpha * d * t ^ 6 + (-2291 / 19200) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_01, v37_02, v37_03, v37_10, v37_11, v37_12, v37_13]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_10, phase36_11, phase36_12, phase36_13]
  try simp only [star_one, star_neg]
  linear_combination ((-481 / 192) * t ^ 2 + (38333 / 28800) * t ^ 4 + (44423 / 76800) * t ^ 6 + (17563 / 345600) * t ^ 10 + (259 / 96) * d * t ^ 2 + (-10307 / 7200) * d * t ^ 4 + (-16601 / 25600) * d * t ^ 6 + (-39013 / 345600) * d * t ^ 10 + (-37 / 192) * d ^ 2 * t ^ 2 + (193 / 1920) * d ^ 2 * t ^ 4 + (269 / 3840) * d ^ 2 * t ^ 6) * alpha_sq + ((37 / 96) * t ^ 2 + (-557 / 11520) * t ^ 4 + (-4339 / 15360) * t ^ 6 + (47 / 13824) * t ^ 10 + (-37 / 96) * alpha * t ^ 2 + (1099 / 3840) * alpha * t ^ 4 + (739 / 15360) * alpha * t ^ 6 + (-47 / 13824) * alpha * t ^ 10) * d_sq
theorem v38_14 (t : ℂ) : (momentPoly 38 z38 1 4).eval t = ((-577357 / 160) * t ^ 3 + (394289477 / 64000) * t ^ 5 + (-239875631 / 96000) * t ^ 7 + (16178607 / 128000) * t ^ 9 + (-6455751 / 32000) * t ^ 11 + (6802709 / 1152000) * t ^ 17 + (22411 / 120) * d * t ^ 3 + (-196774607 / 576000) * d * t ^ 5 + (14663519 / 96000) * d * t ^ 7 + (7349263 / 1152000) * d * t ^ 9 + (-933359 / 288000) * d * t ^ 11 + (-137147 / 384000) * d * t ^ 17 + (-553997 / 600) * alpha * t ^ 3 + (367274153 / 576000) * alpha * t ^ 5 + (15482353 / 32000) * alpha * t ^ 7 + (692714663 / 1152000) * alpha * t ^ 9 + (-227277479 / 288000) * alpha * t ^ 11 + (-12990521 / 1152000) * alpha * t ^ 17 + (3285 / 32) * alpha * d * t ^ 3 + (-21707147 / 115200) * alpha * d * t ^ 5 + (4335259 / 57600) * alpha * d * t ^ 7 + (562331 / 46080) * alpha * d * t ^ 9 + (-322829 / 172800) * alpha * d * t ^ 11 + (1985 / 9216) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_01, v37_02, v37_03, v37_04, v37_10, v37_11, v37_12, v37_13, v37_14]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_04, phase36_10, phase36_11, phase36_12, phase36_13, phase36_14]
  try simp only [star_one, star_neg]
  linear_combination ((-50151 / 1280) * t ^ 3 + (370777757 / 2304000) * t ^ 5 + (-21525133 / 288000) * t ^ 7 + (-257655451 / 9216000) * t ^ 9 + (-3633971 / 6912000) * t ^ 11 + (449897 / 1536000) * t ^ 17 + (9563 / 240) * d * t ^ 3 + (-29642533 / 576000) * d * t ^ 5 + (4427141 / 576000) * d * t ^ 7 + (23059163 / 4608000) * d * t ^ 9 + (1819423 / 3456000) * d * t ^ 11 + (-1146047 / 20736000) * d * t ^ 17 + (-511 / 768) * d ^ 2 * t ^ 3 + (4931 / 18432) * d ^ 2 * t ^ 5 + (4033 / 13824) * d ^ 2 * t ^ 7 + (2107 / 221184) * d ^ 2 * t ^ 9 + (-13 / 18432) * d ^ 2 * t ^ 11 + (95 / 331776) * d ^ 2 * t ^ 17) * alpha_sq + ((73 / 24) * t ^ 3 + (-34613 / 23040) * t ^ 5 + (-25207 / 23040) * t ^ 7 + (-11 / 192) * t ^ 9 + (23 / 864) * t ^ 11 + (73 / 192) * alpha * t ^ 3 + (-26099 / 172800) * alpha * t ^ 5 + (-11041 / 115200) * alpha * t ^ 7 + (3283 / 92160) * alpha * t ^ 9 + (-53209 / 345600) * alpha * t ^ 11 + (-95 / 82944) * alpha * t ^ 17) * d_sq
theorem v38_20 (t : ℂ) : (momentPoly 38 z38 2 0).eval t = ((-6451 / 480) * t ^ 2 + (11827 / 960) * t ^ 4 + (5 / 96) * d * t ^ 2 + (-1 / 192) * d * t ^ 4 + (-377 / 160) * alpha * t ^ 2 + (449 / 320) * alpha * t ^ 4 + (11 / 288) * alpha * d * t ^ 2 + (1 / 576) * alpha * d * t ^ 4) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_10, v37_20]
  try simp only [phase36_00, phase36_10, phase36_20]
  try simp only [star_one, star_neg]
  linear_combination ((-13 / 576) * t ^ 2 + (7 / 288) * d * t ^ 2 + (-1 / 576) * d ^ 2 * t ^ 2) * alpha_sq + ((1 / 288) * t ^ 2 + (1 / 288) * alpha * t ^ 2) * d_sq
theorem v38_21 (t : ℂ) : (momentPoly 38 z38 2 1).eval t = ((525 / 16) * t + (-16237 / 480) * t ^ 3 + (923 / 320) * t ^ 5 + (-25 / 16) * d * t + (131 / 80) * d * t ^ 3 + (-49 / 320) * d * t ^ 5 + (-625 / 16) * alpha * t + (883 / 30) * alpha * t ^ 3 + (7289 / 960) * alpha * t ^ 5 + (25 / 16) * alpha * d * t + (-187 / 160) * alpha * d * t ^ 3 + (-889 / 2880) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_01, v37_10, v37_11, v37_20, v37_21]
  try simp only [phase36_00, phase36_01, phase36_10, phase36_11, phase36_20, phase36_21]
  try simp only [star_one, star_neg]
  linear_combination ((229 / 2560) * t ^ 3 + (-1181 / 3840) * t ^ 5 + (-131 / 1440) * d * t ^ 3 + (511 / 8640) * d * t ^ 5 + (7 / 4608) * d ^ 2 * t ^ 3 + (1 / 6912) * d ^ 2 * t ^ 5) * alpha_sq + ((-7 / 768) * t ^ 3 + (-1 / 1152) * t ^ 5 + (25 / 2304) * alpha * t ^ 3 + (-1 / 3456) * alpha * t ^ 5) * d_sq
theorem v38_22 (t : ℂ) : (momentPoly 38 z38 2 2).eval t = (2850 + (-5328) * t ^ 2 + (12352033 / 4800) * t ^ 4 + (-662609 / 3200) * t ^ 6 + (1149161 / 9600) * t ^ 8 + (-37 / 3) * d * t ^ 2 + (28973 / 2880) * d * t ^ 4 + (3943 / 1920) * d * t ^ 6 + (-131 / 1152) * d * t ^ 8) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_01, v37_02, v37_10, v37_11, v37_12, v37_20, v37_21, v37_22]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_10, phase36_11, phase36_12, phase36_20, phase36_21, phase36_22]
  try simp only [star_one, star_neg]
  linear_combination ((481 / 144) * t ^ 2 + (-3919 / 1920) * t ^ 4 + (-227899 / 46080) * t ^ 6 + (17309 / 9216) * t ^ 8 + (-259 / 72) * d * t ^ 2 + (299 / 135) * d * t ^ 4 + (55909 / 69120) * d * t ^ 6 + (77 / 7680) * d * t ^ 8 + (37 / 144) * d ^ 2 * t ^ 2 + (-3001 / 17280) * d ^ 2 * t ^ 4 + (-2519 / 46080) * d ^ 2 * t ^ 6 + (1 / 82944) * d ^ 2 * t ^ 8) * alpha_sq + ((-37 / 36) * t ^ 2 + (743 / 960) * t ^ 4 + (1649 / 11520) * t ^ 6 + (-1 / 6912) * t ^ 8) * d_sq
theorem v38_23 (t : ℂ) : (momentPoly 38 z38 2 3).eval t = ((29141 / 8) * t + (-1185301 / 160) * t ^ 3 + (289542957 / 64000) * t ^ 5 + (-3045881 / 3200) * t ^ 7 + (18276227 / 96000) * t ^ 9 + (26430853 / 1152000) * t ^ 11 + (-14532943 / 1152000) * t ^ 13 + (-4163 / 24) * d * t + (28689 / 80) * d * t ^ 3 + (-8601581 / 38400) * d * t ^ 5 + (15211 / 320) * d * t ^ 7 + (-33161 / 3840) * d * t ^ 9 + (-196651 / 230400) * d * t ^ 11 + (112457 / 230400) * d * t ^ 13 + (104075 / 24) * alpha * t + (-64459 / 10) * alpha * t ^ 3 + (34094131 / 64000) * alpha * t ^ 5 + (631841 / 400) * alpha * t ^ 7 + (-139537 / 48000) * alpha * t ^ 9 + (-73848721 / 1152000) * alpha * t ^ 11 + (83249471 / 1152000) * alpha * t ^ 13 + (-4163 / 24) * alpha * d * t + (40953 / 160) * alpha * d * t ^ 3 + (-939119 / 38400) * alpha * d * t ^ 5 + (-1420511 / 28800) * alpha * d * t ^ 7 + (-50309 / 5760) * alpha * d * t ^ 9 + (-51659 / 138240) * alpha * d * t ^ 11 + (34321 / 691200) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_01, v37_02, v37_03, v37_10, v37_11, v37_12, v37_13, v37_20, v37_21, v37_22, v37_23]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_10, phase36_11, phase36_12, phase36_13, phase36_20, phase36_21, phase36_22, phase36_23]
  try simp only [star_one, star_neg]
  linear_combination ((50151 / 2560) * t ^ 3 + (-540877 / 6400) * t ^ 5 + (5474549 / 115200) * t ^ 7 + (680903 / 61440) * t ^ 9 + (-848147 / 2764800) * t ^ 11 + (-26299 / 10240) * t ^ 13 + (-9563 / 480) * d * t ^ 3 + (257843 / 8640) * d * t ^ 5 + (-3449483 / 345600) * d * t ^ 7 + (-233963 / 921600) * d * t ^ 9 + (-125507 / 552960) * d * t ^ 11 + (-39013 / 4147200) * d * t ^ 13 + (511 / 1536) * d ^ 2 * t ^ 3 + (-34081 / 172800) * d ^ 2 * t ^ 5 + (-18191 / 172800) * d ^ 2 * t ^ 7 + (-71 / 69120) * d ^ 2 * t ^ 9 + (6773 / 691200) * d ^ 2 * t ^ 11) * alpha_sq + ((-511 / 256) * t ^ 3 + (104981 / 76800) * t ^ 5 + (19963 / 38400) * t ^ 7 + (-117 / 4096) * t ^ 9 + (-175877 / 2764800) * t ^ 11 + (47 / 55296) * t ^ 13 + (-1825 / 768) * alpha * t ^ 3 + (1146397 / 691200) * alpha * t ^ 5 + (179741 / 345600) * alpha * t ^ 7 + (-1057 / 36864) * alpha * t ^ 9 + (1717 / 102400) * alpha * t ^ 11 + (-47 / 165888) * alpha * t ^ 13) * d_sq
theorem v38_24 (t : ℂ) : (momentPoly 38 z38 2 4).eval t = ((-10457071 / 48) * t ^ 2 + (193193111 / 320) * t ^ 4 + (-530876258479 / 960000) * t ^ 6 + (106864481883 / 640000) * t ^ 8 + (-111902013 / 32000) * t ^ 10 + (17783224049 / 3840000) * t ^ 12 + (-2849211707 / 2880000) * t ^ 14 + (-1651178707 / 11520000) * t ^ 18 + (92279917 / 720000) * t ^ 20 + (40525 / 48) * d * t ^ 2 + (-1545989 / 1600) * d * t ^ 4 + (-11625269 / 32000) * d * t ^ 6 + (261157999 / 576000) * d * t ^ 8 + (-18976423 / 288000) * d * t ^ 10 + (22059679 / 288000) * d * t ^ 12 + (8978011 / 432000) * d * t ^ 14 + (1801097 / 1728000) * d * t ^ 18 + (91523 / 1152000) * d * t ^ 20 + (611117 / 16) * alpha * t ^ 2 + (-146485827 / 1600) * alpha * t ^ 4 + (24920662079 / 360000) * alpha * t ^ 6 + (-16132488407 / 960000) * alpha * t ^ 8 + (1389528899 / 576000) * alpha * t ^ 10 + (-11844240649 / 8640000) * alpha * t ^ 12 + (-24513641 / 360000) * alpha * t ^ 14 + (-24236747 / 480000) * alpha * t ^ 18 + (548581997 / 17280000) * alpha * t ^ 20 + (-89155 / 144) * alpha * d * t ^ 2 + (4539451 / 4800) * alpha * d * t ^ 4 + (-45146683 / 576000) * alpha * d * t ^ 6 + (-264938873 / 1152000) * alpha * d * t ^ 8 + (-7004891 / 144000) * alpha * d * t ^ 10 + (14915783 / 460800) * alpha * d * t ^ 12 + (-1926019 / 576000) * alpha * d * t ^ 14 + (5315449 / 6912000) * alpha * d * t ^ 18 + (-39727 / 3456000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_01, v37_02, v37_03, v37_04, v37_10, v37_11, v37_12, v37_13, v37_14, v37_20, v37_21, v37_22, v37_23, v37_24]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_04, phase36_10, phase36_11, phase36_12, phase36_13, phase36_14, phase36_20, phase36_21, phase36_22, phase36_23, phase36_24]
  try simp only [star_one, star_neg]
  linear_combination ((-105365 / 288) * t ^ 2 + (38333 / 100) * t ^ 4 + (188567443 / 2304000) * t ^ 6 + (890197937 / 9216000) * t ^ 8 + (-595413209 / 2304000) * t ^ 10 + (1419270379 / 22118400) * t ^ 12 + (-878483 / 3072000) * t ^ 14 + (176642077 / 110592000) * t ^ 18 + (-18804667 / 11059200) * t ^ 20 + (56735 / 144) * d * t ^ 2 + (-10307 / 25) * d * t ^ 4 + (-83252303 / 864000) * d * t ^ 6 + (489623717 / 4608000) * d * t ^ 8 + (-43687531 / 3456000) * d * t ^ 10 + (600654299 / 27648000) * d * t ^ 12 + (43502651 / 6912000) * d * t ^ 14 + (11858087 / 27648000) * d * t ^ 18 + (18949 / 3456000) * d * t ^ 20 + (-8105 / 288) * d ^ 2 * t ^ 2 + (579 / 20) * d ^ 2 * t ^ 4 + (20063219 / 1382400) * d ^ 2 * t ^ 6 + (-214214371 / 16588800) * d ^ 2 * t ^ 8 + (-3863213 / 1382400) * d ^ 2 * t ^ 10 + (4884427 / 66355200) * d ^ 2 * t ^ 12 + (73667 / 5529600) * d ^ 2 * t ^ 14 + (-46975 / 2654208) * d ^ 2 * t ^ 18 + (95 / 3981312) * d ^ 2 * t ^ 20) * alpha_sq + ((8105 / 144) * t ^ 2 + (-557 / 40) * t ^ 4 + (-31122433 / 288000) * t ^ 6 + (822178633 / 13824000) * t ^ 8 + (519413 / 64000) * t ^ 10 + (-59290169 / 55296000) * t ^ 12 + (94123 / 921600) * t ^ 14 + (1036861 / 55296000) * t ^ 18 + (95 / 663552) * t ^ 20 + (-8105 / 144) * alpha * t ^ 2 + (3297 / 40) * alpha * t ^ 4 + (-29983517 / 1728000) * alpha * t ^ 6 + (-91877053 / 13824000) * alpha * t ^ 8 + (-11731427 / 3456000) * alpha * t ^ 10 + (23358587 / 165888000) * alpha * t ^ 12 + (1614893 / 8294400) * alpha * t ^ 14 + (8419417 / 165888000) * alpha * t ^ 18 + (-95 / 663552) * alpha * t ^ 20) * d_sq
theorem v38_30 (t : ℂ) : (momentPoly 38 z38 3 0).eval t = ((-7909 / 320) * t ^ 3 + (6319 / 320) * t ^ 5 + 1 * t ^ 9 + (307 / 240) * d * t ^ 3 + (-277 / 240) * d * t ^ 5 + (47 / 1152) * d * t ^ 9 + (7589 / 1200) * alpha * t ^ 3 + (-341 / 1200) * alpha * t ^ 5 + (-166777 / 28800) * alpha * t ^ 9 + (-45 / 64) * alpha * d * t ^ 3 + (133 / 192) * alpha * d * t ^ 5) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_10, v37_20, v37_30]
  try simp only [phase36_00, phase36_10, phase36_20, phase36_30]
  try simp only [star_one, star_neg]
  linear_combination ((-687 / 2560) * t ^ 3 + (1181 / 1280) * t ^ 5 + (131 / 480) * d * t ^ 3 + (-511 / 2880) * d * t ^ 5 + (-7 / 1536) * d ^ 2 * t ^ 3 + (-1 / 2304) * d ^ 2 * t ^ 5) * alpha_sq + ((1 / 48) * t ^ 3 + (-1 / 384) * alpha * t ^ 3 + (1 / 576) * alpha * t ^ 5) * d_sq
theorem v38_31 (t : ℂ) : (momentPoly 38 z38 3 1).eval t = ((-238687 / 160) * t ^ 2 + (5318681 / 1920) * t ^ 4 + (-409443 / 320) * t ^ 6 + (-4251 / 1280) * t ^ 10 + (185 / 32) * d * t ^ 2 + (-34943 / 9600) * d * t ^ 4 + (-3827 / 2400) * d * t ^ 6 + (-20719 / 57600) * d * t ^ 10 + (-41847 / 160) * alpha * t ^ 2 + (3788569 / 9600) * alpha * t ^ 4 + (-638443 / 4800) * alpha * t ^ 6 + (-224803 / 57600) * alpha * t ^ 10 + (407 / 96) * alpha * d * t ^ 2 + (-91837 / 28800) * alpha * d * t ^ 4 + (-1213 / 1200) * alpha * d * t ^ 6 + (2291 / 19200) * alpha * d * t ^ 10) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_01, v37_10, v37_11, v37_20, v37_21, v37_30, v37_31]
  try simp only [phase36_00, phase36_01, phase36_10, phase36_11, phase36_20, phase36_21, phase36_30, phase36_31]
  try simp only [star_one, star_neg]
  linear_combination ((-481 / 192) * t ^ 2 + (38333 / 28800) * t ^ 4 + (44423 / 76800) * t ^ 6 + (17563 / 345600) * t ^ 10 + (259 / 96) * d * t ^ 2 + (-10307 / 7200) * d * t ^ 4 + (-16601 / 25600) * d * t ^ 6 + (-39013 / 345600) * d * t ^ 10 + (-37 / 192) * d ^ 2 * t ^ 2 + (193 / 1920) * d ^ 2 * t ^ 4 + (269 / 3840) * d ^ 2 * t ^ 6) * alpha_sq + ((37 / 96) * t ^ 2 + (-557 / 11520) * t ^ 4 + (-4339 / 15360) * t ^ 6 + (47 / 13824) * t ^ 10 + (37 / 96) * alpha * t ^ 2 + (-1099 / 3840) * alpha * t ^ 4 + (-739 / 15360) * alpha * t ^ 6 + (47 / 13824) * alpha * t ^ 10) * d_sq
theorem v38_32 (t : ℂ) : (momentPoly 38 z38 3 2).eval t = ((29141 / 8) * t + (-1185301 / 160) * t ^ 3 + (289542957 / 64000) * t ^ 5 + (-3045881 / 3200) * t ^ 7 + (18276227 / 96000) * t ^ 9 + (26430853 / 1152000) * t ^ 11 + (-14532943 / 1152000) * t ^ 13 + (-4163 / 24) * d * t + (28689 / 80) * d * t ^ 3 + (-8601581 / 38400) * d * t ^ 5 + (15211 / 320) * d * t ^ 7 + (-33161 / 3840) * d * t ^ 9 + (-196651 / 230400) * d * t ^ 11 + (112457 / 230400) * d * t ^ 13 + (-104075 / 24) * alpha * t + (64459 / 10) * alpha * t ^ 3 + (-34094131 / 64000) * alpha * t ^ 5 + (-631841 / 400) * alpha * t ^ 7 + (139537 / 48000) * alpha * t ^ 9 + (73848721 / 1152000) * alpha * t ^ 11 + (-83249471 / 1152000) * alpha * t ^ 13 + (4163 / 24) * alpha * d * t + (-40953 / 160) * alpha * d * t ^ 3 + (939119 / 38400) * alpha * d * t ^ 5 + (1420511 / 28800) * alpha * d * t ^ 7 + (50309 / 5760) * alpha * d * t ^ 9 + (51659 / 138240) * alpha * d * t ^ 11 + (-34321 / 691200) * alpha * d * t ^ 13) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_01, v37_02, v37_10, v37_11, v37_12, v37_20, v37_21, v37_22, v37_30, v37_31, v37_32]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_10, phase36_11, phase36_12, phase36_20, phase36_21, phase36_22, phase36_30, phase36_31, phase36_32]
  try simp only [star_one, star_neg]
  linear_combination ((50151 / 2560) * t ^ 3 + (-540877 / 6400) * t ^ 5 + (5474549 / 115200) * t ^ 7 + (680903 / 61440) * t ^ 9 + (-848147 / 2764800) * t ^ 11 + (-26299 / 10240) * t ^ 13 + (-9563 / 480) * d * t ^ 3 + (257843 / 8640) * d * t ^ 5 + (-3449483 / 345600) * d * t ^ 7 + (-233963 / 921600) * d * t ^ 9 + (-125507 / 552960) * d * t ^ 11 + (-39013 / 4147200) * d * t ^ 13 + (511 / 1536) * d ^ 2 * t ^ 3 + (-34081 / 172800) * d ^ 2 * t ^ 5 + (-18191 / 172800) * d ^ 2 * t ^ 7 + (-71 / 69120) * d ^ 2 * t ^ 9 + (6773 / 691200) * d ^ 2 * t ^ 11) * alpha_sq + ((-511 / 256) * t ^ 3 + (104981 / 76800) * t ^ 5 + (19963 / 38400) * t ^ 7 + (-117 / 4096) * t ^ 9 + (-175877 / 2764800) * t ^ 11 + (47 / 55296) * t ^ 13 + (1825 / 768) * alpha * t ^ 3 + (-1146397 / 691200) * alpha * t ^ 5 + (-179741 / 345600) * alpha * t ^ 7 + (1057 / 36864) * alpha * t ^ 9 + (-1717 / 102400) * alpha * t ^ 11 + (47 / 165888) * alpha * t ^ 13) * d_sq
theorem v38_33 (t : ℂ) : (momentPoly 38 z38 3 3).eval t = (316388 + (-875340) * t ^ 2 + (333504891 / 400) * t ^ 4 + (-54376029593 / 160000) * t ^ 6 + (8056842217 / 80000) * t ^ 8 + (-5697322823 / 160000) * t ^ 10 + (131788129 / 320000) * t ^ 12 + (-243274439 / 480000) * t ^ 14 + (61973983 / 960000) * t ^ 18 + (-8105 / 4) * d * t ^ 2 + (260757 / 80) * d * t ^ 4 + (-11649599 / 19200) * d * t ^ 6 + (-3983687 / 6400) * d * t ^ 8 + (-261 / 400) * d * t ^ 10 + (433403 / 23040) * d * t ^ 12 + (-301863 / 12800) * d * t ^ 14 + (47 / 576) * d * t ^ 18) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_01, v37_02, v37_03, v37_10, v37_11, v37_12, v37_13, v37_20, v37_21, v37_22, v37_23, v37_30, v37_31, v37_32, v37_33]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_10, phase36_11, phase36_12, phase36_13, phase36_20, phase36_21, phase36_22, phase36_23, phase36_30, phase36_31, phase36_32, phase36_33]
  try simp only [star_one, star_neg]
  linear_combination ((105365 / 192) * t ^ 2 + (-105813 / 160) * t ^ 4 + (-184285061 / 128000) * t ^ 6 + (201317503 / 102400) * t ^ 8 + (-347013089 / 768000) * t ^ 10 + (-91918219 / 13824000) * t ^ 12 + (-34641797 / 4608000) * t ^ 14 + (-11668943 / 8294400) * t ^ 18 + (-56735 / 96) * d * t ^ 2 + (3588 / 5) * d * t ^ 4 + (4374173 / 64000) * d * t ^ 6 + (-21614099 / 115200) * d * t ^ 8 + (-4116967 / 256000) * d * t ^ 10 + (19718059 / 2304000) * d * t ^ 12 + (-14279753 / 1728000) * d * t ^ 14 + (8105 / 192) * d ^ 2 * t ^ 2 + (-9003 / 160) * d ^ 2 * t ^ 4 + (173467 / 230400) * d ^ 2 * t ^ 6 + (30883427 / 2764800) * d ^ 2 * t ^ 8 + (95273 / 38400) * d ^ 2 * t ^ 10 + (327001 / 2764800) * d ^ 2 * t ^ 12 + (-10487 / 691200) * d ^ 2 * t ^ 14) * alpha_sq + ((-8105 / 48) * t ^ 2 + (20061 / 80) * t ^ 4 + (-652327 / 12800) * t ^ 6 + (-10229647 / 460800) * t ^ 8 + (-513473 / 51200) * t ^ 10 + (-289109 / 345600) * t ^ 12 + (330781 / 921600) * t ^ 14 + (-2209 / 331776) * t ^ 18) * d_sq
theorem v38_34 (t : ℂ) : (momentPoly 38 z38 3 4).eval t = ((8512301 / 16) * t + (-128061219 / 80) * t ^ 3 + (57430818741 / 32000) * t ^ 5 + (-12686232920767 / 12800000) * t ^ 7 + (13181658065581 / 38400000) * t ^ 9 + (-5636291102227 / 76800000) * t ^ 11 + (-105803382481 / 11520000) * t ^ 13 + (76966924009 / 12800000) * t ^ 15 + (-684464428163 / 460800000) * t ^ 17 + (-236776320613 / 691200000) * t ^ 19 + (29973047183 / 115200000) * t ^ 21 + (42893245073 / 1382400000) * t ^ 25 + (-1216043 / 48) * d * t + (3099591 / 40) * d * t ^ 3 + (-565674391 / 6400) * d * t ^ 5 + (375831640393 / 7680000) * d * t ^ 7 + (-122691360089 / 7680000) * d * t ^ 9 + (45932718719 / 15360000) * d * t ^ 11 + (1055939533 / 2880000) * d * t ^ 13 + (-2265098881 / 23040000) * d * t ^ 15 + (19148297 / 1228800) * d * t ^ 17 + (1494407741 / 138240000) * d * t ^ 19 + (-385547987 / 23040000) * d * t ^ 21 + (25013251 / 55296000) * d * t ^ 25 + (30401075 / 48) * alpha * t + (-6964221 / 5) * alpha * t ^ 3 + (18428069003 / 32000) * alpha * t ^ 5 + (18829386333437 / 38400000) * alpha * t ^ 7 + (-3821977577279 / 12800000) * alpha * t ^ 9 + (-2947585760381 / 76800000) * alpha * t ^ 11 + (73462665277 / 1280000) * alpha * t ^ 13 + (-953897277539 / 38400000) * alpha * t ^ 15 + (-367531645043 / 153600000) * alpha * t ^ 17 + (238486433761 / 691200000) * alpha * t ^ 19 + (-608073013 / 3600000) * alpha * t ^ 21 + (-93644803241 / 1382400000) * alpha * t ^ 25 + (-1216043 / 48) * alpha * d * t + (4424607 / 80) * alpha * d * t ^ 3 + (-472404167 / 19200) * alpha * d * t ^ 5 + (-271911406391 / 23040000) * alpha * d * t ^ 7 + (70364025143 / 23040000) * alpha * d * t ^ 9 + (135966961007 / 46080000) * alpha * d * t ^ 11 + (2640880621 / 5760000) * alpha * d * t ^ 13 + (-526861531 / 23040000) * alpha * d * t ^ 15 + (-40156073 / 11059200) * alpha * d * t ^ 17 + (-4564924327 / 414720000) * alpha * d * t ^ 19 + (12372487 / 2160000) * alpha * d * t ^ 21 + (556003 / 165888000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_01, v37_02, v37_03, v37_04, v37_10, v37_11, v37_12, v37_13, v37_14, v37_20, v37_21, v37_22, v37_23, v37_24, v37_30, v37_31, v37_32, v37_33, v37_34]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_04, phase36_10, phase36_11, phase36_12, phase36_13, phase36_14, phase36_20, phase36_21, phase36_22, phase36_23, phase36_24, phase36_30, phase36_31, phase36_32, phase36_33, phase36_34]
  try simp only [star_one, star_neg]
  linear_combination ((5418369 / 1280) * t ^ 3 + (-139954907 / 6400) * t ^ 5 + (135020899139 / 5760000) * t ^ 7 + (-163981085627 / 92160000) * t ^ 9 + (-1827606637 / 409600) * t ^ 11 + (-358389061771 / 552960000) * t ^ 13 + (99018925949 / 92160000) * t ^ 15 + (-44545539727 / 221184000) * t ^ 17 + (-20494140487 / 1658880000) * t ^ 19 + (22732467313 / 1105920000) * t ^ 21 + (278420597 / 110592000) * t ^ 25 + (-344399 / 80) * d * t ^ 3 + (28785697 / 2880) * d * t ^ 5 + (-1013409355811 / 138240000) * d * t ^ 7 + (6726348593 / 3840000) * d * t ^ 9 + (-1213329217 / 4608000) * d * t ^ 11 + (96269104289 / 829440000) * d * t ^ 13 + (1875397507 / 69120000) * d * t ^ 15 + (-86623639 / 73728000) * d * t ^ 17 + (1808617747 / 276480000) * d * t ^ 19 + (-1516968511 / 368640000) * d * t ^ 21 + (-741247 / 39813120) * d * t ^ 25 + (18403 / 256) * d ^ 2 * t ^ 3 + (-5222477 / 57600) * d ^ 2 * t ^ 5 + (-71748781 / 5529600) * d ^ 2 * t ^ 7 + (11611519 / 409600) * d ^ 2 * t ^ 9 + (80569559 / 11059200) * d ^ 2 * t ^ 11 + (-383816323 / 110592000) * d ^ 2 * t ^ 13 + (6908651 / 18432000) * d ^ 2 * t ^ 15 + (-48721 / 33177600) * d ^ 2 * t ^ 17 + (-34103543 / 331776000) * d ^ 2 * t ^ 19 + (309931 / 82944000) * d ^ 2 * t ^ 21) * alpha_sq + ((-55209 / 128) * t ^ 3 + (23892853 / 38400) * t ^ 5 + (-103226107 / 3072000) * t ^ 7 + (-180298943 / 1152000) * t ^ 9 + (-58655609 / 2304000) * t ^ 11 + (416835829 / 18432000) * t ^ 13 + (-5561729 / 3072000) * t ^ 15 + (3373163 / 44236800) * t ^ 17 + (17621063 / 41472000) * t ^ 19 + (2931583 / 221184000) * t ^ 21 + (-4465 / 2654208) * t ^ 25 + (-65725 / 128) * alpha * t ^ 3 + (79862287 / 115200) * alpha * t ^ 5 + (335693143 / 27648000) * alpha * t ^ 7 + (-9524739 / 51200) * alpha * t ^ 9 + (-10675573 / 4608000) * alpha * t ^ 11 + (-4040447 / 6144000) * alpha * t ^ 13 + (-177353063 / 27648000) * alpha * t ^ 15 + (504679 / 44236800) * alpha * t ^ 17 + (516667 / 82944000) * alpha * t ^ 19 + (-5303861 / 221184000) * alpha * t ^ 21 + (4465 / 7962624) * alpha * t ^ 25) * d_sq
theorem v38_40 (t : ℂ) : (momentPoly 38 z38 4 0).eval t = ((16869157 / 48000) * t ^ 4 + (-21917551 / 32000) * t ^ 6 + (77238199 / 192000) * t ^ 8 + (-12029771 / 144000) * t ^ 10 + (13578917 / 1152000) * t ^ 16 + (-163 / 9600) * d * t ^ 4 + (-15451 / 19200) * d * t ^ 6 + (-1177 / 2560) * d * t ^ 8 + (40163 / 28800) * d * t ^ 10 + (95 / 9216) * d * t ^ 16 + (8373923 / 48000) * alpha * t ^ 4 + (-8649829 / 32000) * alpha * t ^ 6 + (20552201 / 192000) * alpha * t ^ 8 + (-92701 / 16000) * alpha * t ^ 10 + (-143213 / 128000) * alpha * t ^ 16 + (-72503 / 28800) * alpha * d * t ^ 4 + (11481 / 6400) * alpha * d * t ^ 6 + (1709 / 23040) * alpha * d * t ^ 8 + (40363 / 86400) * alpha * d * t ^ 10 + (95 / 27648) * alpha * d * t ^ 16) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_10, v37_20, v37_30, v37_40]
  try simp only [phase36_00, phase36_10, phase36_20, phase36_30, phase36_40]
  try simp only [star_one, star_neg]
  linear_combination ((23023 / 28800) * t ^ 4 + (320601 / 25600) * t ^ 6 + (-17309 / 3072) * t ^ 8 + (-17563 / 86400) * t ^ 10 + (-551 / 600) * d * t ^ 4 + (19273 / 115200) * d * t ^ 6 + (-77 / 2560) * d * t ^ 8 + (39013 / 86400) * d * t ^ 10 + (137 / 1152) * d ^ 2 * t ^ 4 + (-119 / 1024) * d ^ 2 * t ^ 6 + (-1 / 27648) * d ^ 2 * t ^ 8) * alpha_sq + ((-37 / 360) * t ^ 4 + (357 / 2560) * t ^ 6 + (-1 / 4608) * t ^ 8 + (47 / 3456) * t ^ 10 + (-179 / 480) * alpha * t ^ 4 + (843 / 2560) * alpha * t ^ 6 + (1 / 4608) * alpha * t ^ 8 + (-47 / 3456) * alpha * t ^ 10) * d_sq
theorem v38_41 (t : ℂ) : (momentPoly 38 z38 4 1).eval t = ((-577357 / 160) * t ^ 3 + (394289477 / 64000) * t ^ 5 + (-239875631 / 96000) * t ^ 7 + (16178607 / 128000) * t ^ 9 + (-6455751 / 32000) * t ^ 11 + (6802709 / 1152000) * t ^ 17 + (22411 / 120) * d * t ^ 3 + (-196774607 / 576000) * d * t ^ 5 + (14663519 / 96000) * d * t ^ 7 + (7349263 / 1152000) * d * t ^ 9 + (-933359 / 288000) * d * t ^ 11 + (-137147 / 384000) * d * t ^ 17 + (553997 / 600) * alpha * t ^ 3 + (-367274153 / 576000) * alpha * t ^ 5 + (-15482353 / 32000) * alpha * t ^ 7 + (-692714663 / 1152000) * alpha * t ^ 9 + (227277479 / 288000) * alpha * t ^ 11 + (12990521 / 1152000) * alpha * t ^ 17 + (-3285 / 32) * alpha * d * t ^ 3 + (21707147 / 115200) * alpha * d * t ^ 5 + (-4335259 / 57600) * alpha * d * t ^ 7 + (-562331 / 46080) * alpha * d * t ^ 9 + (322829 / 172800) * alpha * d * t ^ 11 + (-1985 / 9216) * alpha * d * t ^ 17) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_01, v37_10, v37_11, v37_20, v37_21, v37_30, v37_31, v37_40, v37_41]
  try simp only [phase36_00, phase36_01, phase36_10, phase36_11, phase36_20, phase36_21, phase36_30, phase36_31, phase36_40, phase36_41]
  try simp only [star_one, star_neg]
  linear_combination ((-50151 / 1280) * t ^ 3 + (370777757 / 2304000) * t ^ 5 + (-21525133 / 288000) * t ^ 7 + (-257655451 / 9216000) * t ^ 9 + (-3633971 / 6912000) * t ^ 11 + (449897 / 1536000) * t ^ 17 + (9563 / 240) * d * t ^ 3 + (-29642533 / 576000) * d * t ^ 5 + (4427141 / 576000) * d * t ^ 7 + (23059163 / 4608000) * d * t ^ 9 + (1819423 / 3456000) * d * t ^ 11 + (-1146047 / 20736000) * d * t ^ 17 + (-511 / 768) * d ^ 2 * t ^ 3 + (4931 / 18432) * d ^ 2 * t ^ 5 + (4033 / 13824) * d ^ 2 * t ^ 7 + (2107 / 221184) * d ^ 2 * t ^ 9 + (-13 / 18432) * d ^ 2 * t ^ 11 + (95 / 331776) * d ^ 2 * t ^ 17) * alpha_sq + ((73 / 24) * t ^ 3 + (-34613 / 23040) * t ^ 5 + (-25207 / 23040) * t ^ 7 + (-11 / 192) * t ^ 9 + (23 / 864) * t ^ 11 + (-73 / 192) * alpha * t ^ 3 + (26099 / 172800) * alpha * t ^ 5 + (11041 / 115200) * alpha * t ^ 7 + (-3283 / 92160) * alpha * t ^ 9 + (53209 / 345600) * alpha * t ^ 11 + (95 / 82944) * alpha * t ^ 17) * d_sq
theorem v38_42 (t : ℂ) : (momentPoly 38 z38 4 2).eval t = ((-10457071 / 48) * t ^ 2 + (193193111 / 320) * t ^ 4 + (-530876258479 / 960000) * t ^ 6 + (106864481883 / 640000) * t ^ 8 + (-111902013 / 32000) * t ^ 10 + (17783224049 / 3840000) * t ^ 12 + (-2849211707 / 2880000) * t ^ 14 + (-1651178707 / 11520000) * t ^ 18 + (92279917 / 720000) * t ^ 20 + (40525 / 48) * d * t ^ 2 + (-1545989 / 1600) * d * t ^ 4 + (-11625269 / 32000) * d * t ^ 6 + (261157999 / 576000) * d * t ^ 8 + (-18976423 / 288000) * d * t ^ 10 + (22059679 / 288000) * d * t ^ 12 + (8978011 / 432000) * d * t ^ 14 + (1801097 / 1728000) * d * t ^ 18 + (91523 / 1152000) * d * t ^ 20 + (-611117 / 16) * alpha * t ^ 2 + (146485827 / 1600) * alpha * t ^ 4 + (-24920662079 / 360000) * alpha * t ^ 6 + (16132488407 / 960000) * alpha * t ^ 8 + (-1389528899 / 576000) * alpha * t ^ 10 + (11844240649 / 8640000) * alpha * t ^ 12 + (24513641 / 360000) * alpha * t ^ 14 + (24236747 / 480000) * alpha * t ^ 18 + (-548581997 / 17280000) * alpha * t ^ 20 + (89155 / 144) * alpha * d * t ^ 2 + (-4539451 / 4800) * alpha * d * t ^ 4 + (45146683 / 576000) * alpha * d * t ^ 6 + (264938873 / 1152000) * alpha * d * t ^ 8 + (7004891 / 144000) * alpha * d * t ^ 10 + (-14915783 / 460800) * alpha * d * t ^ 12 + (1926019 / 576000) * alpha * d * t ^ 14 + (-5315449 / 6912000) * alpha * d * t ^ 18 + (39727 / 3456000) * alpha * d * t ^ 20) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_01, v37_02, v37_10, v37_11, v37_12, v37_20, v37_21, v37_22, v37_30, v37_31, v37_32, v37_40, v37_41, v37_42]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_10, phase36_11, phase36_12, phase36_20, phase36_21, phase36_22, phase36_30, phase36_31, phase36_32, phase36_40, phase36_41, phase36_42]
  try simp only [star_one, star_neg]
  linear_combination ((-105365 / 288) * t ^ 2 + (38333 / 100) * t ^ 4 + (188567443 / 2304000) * t ^ 6 + (890197937 / 9216000) * t ^ 8 + (-595413209 / 2304000) * t ^ 10 + (1419270379 / 22118400) * t ^ 12 + (-878483 / 3072000) * t ^ 14 + (176642077 / 110592000) * t ^ 18 + (-18804667 / 11059200) * t ^ 20 + (56735 / 144) * d * t ^ 2 + (-10307 / 25) * d * t ^ 4 + (-83252303 / 864000) * d * t ^ 6 + (489623717 / 4608000) * d * t ^ 8 + (-43687531 / 3456000) * d * t ^ 10 + (600654299 / 27648000) * d * t ^ 12 + (43502651 / 6912000) * d * t ^ 14 + (11858087 / 27648000) * d * t ^ 18 + (18949 / 3456000) * d * t ^ 20 + (-8105 / 288) * d ^ 2 * t ^ 2 + (579 / 20) * d ^ 2 * t ^ 4 + (20063219 / 1382400) * d ^ 2 * t ^ 6 + (-214214371 / 16588800) * d ^ 2 * t ^ 8 + (-3863213 / 1382400) * d ^ 2 * t ^ 10 + (4884427 / 66355200) * d ^ 2 * t ^ 12 + (73667 / 5529600) * d ^ 2 * t ^ 14 + (-46975 / 2654208) * d ^ 2 * t ^ 18 + (95 / 3981312) * d ^ 2 * t ^ 20) * alpha_sq + ((8105 / 144) * t ^ 2 + (-557 / 40) * t ^ 4 + (-31122433 / 288000) * t ^ 6 + (822178633 / 13824000) * t ^ 8 + (519413 / 64000) * t ^ 10 + (-59290169 / 55296000) * t ^ 12 + (94123 / 921600) * t ^ 14 + (1036861 / 55296000) * t ^ 18 + (95 / 663552) * t ^ 20 + (8105 / 144) * alpha * t ^ 2 + (-3297 / 40) * alpha * t ^ 4 + (29983517 / 1728000) * alpha * t ^ 6 + (91877053 / 13824000) * alpha * t ^ 8 + (11731427 / 3456000) * alpha * t ^ 10 + (-23358587 / 165888000) * alpha * t ^ 12 + (-1614893 / 8294400) * alpha * t ^ 14 + (-8419417 / 165888000) * alpha * t ^ 18 + (95 / 663552) * alpha * t ^ 20) * d_sq
theorem v38_43 (t : ℂ) : (momentPoly 38 z38 4 3).eval t = ((8512301 / 16) * t + (-128061219 / 80) * t ^ 3 + (57430818741 / 32000) * t ^ 5 + (-12686232920767 / 12800000) * t ^ 7 + (13181658065581 / 38400000) * t ^ 9 + (-5636291102227 / 76800000) * t ^ 11 + (-105803382481 / 11520000) * t ^ 13 + (76966924009 / 12800000) * t ^ 15 + (-684464428163 / 460800000) * t ^ 17 + (-236776320613 / 691200000) * t ^ 19 + (29973047183 / 115200000) * t ^ 21 + (42893245073 / 1382400000) * t ^ 25 + (-1216043 / 48) * d * t + (3099591 / 40) * d * t ^ 3 + (-565674391 / 6400) * d * t ^ 5 + (375831640393 / 7680000) * d * t ^ 7 + (-122691360089 / 7680000) * d * t ^ 9 + (45932718719 / 15360000) * d * t ^ 11 + (1055939533 / 2880000) * d * t ^ 13 + (-2265098881 / 23040000) * d * t ^ 15 + (19148297 / 1228800) * d * t ^ 17 + (1494407741 / 138240000) * d * t ^ 19 + (-385547987 / 23040000) * d * t ^ 21 + (25013251 / 55296000) * d * t ^ 25 + (-30401075 / 48) * alpha * t + (6964221 / 5) * alpha * t ^ 3 + (-18428069003 / 32000) * alpha * t ^ 5 + (-18829386333437 / 38400000) * alpha * t ^ 7 + (3821977577279 / 12800000) * alpha * t ^ 9 + (2947585760381 / 76800000) * alpha * t ^ 11 + (-73462665277 / 1280000) * alpha * t ^ 13 + (953897277539 / 38400000) * alpha * t ^ 15 + (367531645043 / 153600000) * alpha * t ^ 17 + (-238486433761 / 691200000) * alpha * t ^ 19 + (608073013 / 3600000) * alpha * t ^ 21 + (93644803241 / 1382400000) * alpha * t ^ 25 + (1216043 / 48) * alpha * d * t + (-4424607 / 80) * alpha * d * t ^ 3 + (472404167 / 19200) * alpha * d * t ^ 5 + (271911406391 / 23040000) * alpha * d * t ^ 7 + (-70364025143 / 23040000) * alpha * d * t ^ 9 + (-135966961007 / 46080000) * alpha * d * t ^ 11 + (-2640880621 / 5760000) * alpha * d * t ^ 13 + (526861531 / 23040000) * alpha * d * t ^ 15 + (40156073 / 11059200) * alpha * d * t ^ 17 + (4564924327 / 414720000) * alpha * d * t ^ 19 + (-12372487 / 2160000) * alpha * d * t ^ 21 + (-556003 / 165888000) * alpha * d * t ^ 25) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_01, v37_02, v37_03, v37_10, v37_11, v37_12, v37_13, v37_20, v37_21, v37_22, v37_23, v37_30, v37_31, v37_32, v37_33, v37_40, v37_41, v37_42, v37_43]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_10, phase36_11, phase36_12, phase36_13, phase36_20, phase36_21, phase36_22, phase36_23, phase36_30, phase36_31, phase36_32, phase36_33, phase36_40, phase36_41, phase36_42, phase36_43]
  try simp only [star_one, star_neg]
  linear_combination ((5418369 / 1280) * t ^ 3 + (-139954907 / 6400) * t ^ 5 + (135020899139 / 5760000) * t ^ 7 + (-163981085627 / 92160000) * t ^ 9 + (-1827606637 / 409600) * t ^ 11 + (-358389061771 / 552960000) * t ^ 13 + (99018925949 / 92160000) * t ^ 15 + (-44545539727 / 221184000) * t ^ 17 + (-20494140487 / 1658880000) * t ^ 19 + (22732467313 / 1105920000) * t ^ 21 + (278420597 / 110592000) * t ^ 25 + (-344399 / 80) * d * t ^ 3 + (28785697 / 2880) * d * t ^ 5 + (-1013409355811 / 138240000) * d * t ^ 7 + (6726348593 / 3840000) * d * t ^ 9 + (-1213329217 / 4608000) * d * t ^ 11 + (96269104289 / 829440000) * d * t ^ 13 + (1875397507 / 69120000) * d * t ^ 15 + (-86623639 / 73728000) * d * t ^ 17 + (1808617747 / 276480000) * d * t ^ 19 + (-1516968511 / 368640000) * d * t ^ 21 + (-741247 / 39813120) * d * t ^ 25 + (18403 / 256) * d ^ 2 * t ^ 3 + (-5222477 / 57600) * d ^ 2 * t ^ 5 + (-71748781 / 5529600) * d ^ 2 * t ^ 7 + (11611519 / 409600) * d ^ 2 * t ^ 9 + (80569559 / 11059200) * d ^ 2 * t ^ 11 + (-383816323 / 110592000) * d ^ 2 * t ^ 13 + (6908651 / 18432000) * d ^ 2 * t ^ 15 + (-48721 / 33177600) * d ^ 2 * t ^ 17 + (-34103543 / 331776000) * d ^ 2 * t ^ 19 + (309931 / 82944000) * d ^ 2 * t ^ 21) * alpha_sq + ((-55209 / 128) * t ^ 3 + (23892853 / 38400) * t ^ 5 + (-103226107 / 3072000) * t ^ 7 + (-180298943 / 1152000) * t ^ 9 + (-58655609 / 2304000) * t ^ 11 + (416835829 / 18432000) * t ^ 13 + (-5561729 / 3072000) * t ^ 15 + (3373163 / 44236800) * t ^ 17 + (17621063 / 41472000) * t ^ 19 + (2931583 / 221184000) * t ^ 21 + (-4465 / 2654208) * t ^ 25 + (65725 / 128) * alpha * t ^ 3 + (-79862287 / 115200) * alpha * t ^ 5 + (-335693143 / 27648000) * alpha * t ^ 7 + (9524739 / 51200) * alpha * t ^ 9 + (10675573 / 4608000) * alpha * t ^ 11 + (4040447 / 6144000) * alpha * t ^ 13 + (177353063 / 27648000) * alpha * t ^ 15 + (-504679 / 44236800) * alpha * t ^ 17 + (-516667 / 82944000) * alpha * t ^ 19 + (5303861 / 221184000) * alpha * t ^ 21 + (-4465 / 7962624) * alpha * t ^ 25) * d_sq
theorem v38_44 (t : ℂ) : (momentPoly 38 z38 4 4).eval t = (46209634 + (-168170976) * t ^ 2 + (11845599647 / 50) * t ^ 4 + (-1374525169319 / 8000) * t ^ 6 + (7991897709989039 / 96000000) * t ^ 8 + (-2223911017970409 / 64000000) * t ^ 10 + (636575202935137 / 76800000) * t ^ 12 + (-303148289842057 / 1152000000) * t ^ 14 + (903662519081323 / 2304000000) * t ^ 16 + (-831497725609 / 36000000) * t ^ 18 + (-166930640054873 / 6912000000) * t ^ 20 + (-353624598813 / 32000000) * t ^ 22 + (33749045103293 / 4608000000) * t ^ 24 + (-7385399150627 / 3456000000) * t ^ 26 + (160935986029 / 1536000000) * t ^ 32 + (-1167854 / 3) * d * t ^ 2 + (27785107 / 30) * d * t ^ 4 + (-502334411 / 960) * d * t ^ 6 + (-1839416624993 / 11520000) * d * t ^ 8 + (3018696759763 / 23040000) * d * t ^ 10 + (1252485126047 / 46080000) * d * t ^ 12 + (-1097822422717 / 46080000) * d * t ^ 14 + (2789893112533 / 276480000) * d * t ^ 16 + (583135187 / 345600) * d * t ^ 18 + (-139799986819 / 829440000) * d * t ^ 20 + (270457433 / 8640000) * d * t ^ 22 + (19475041 / 36864000) * d * t ^ 24 + (85745129 / 3072000) * d * t ^ 26 + (583775 / 2654208) * d * t ^ 32) := by
  rw [momentPoly]
  simp only [z38, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v37_00, v37_01, v37_02, v37_03, v37_04, v37_10, v37_11, v37_12, v37_13, v37_14, v37_20, v37_21, v37_22, v37_23, v37_24, v37_30, v37_31, v37_32, v37_33, v37_34, v37_40, v37_41, v37_42, v37_43, v37_44]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_04, phase36_10, phase36_11, phase36_12, phase36_13, phase36_14, phase36_20, phase36_21, phase36_22, phase36_23, phase36_24, phase36_30, phase36_31, phase36_32, phase36_33, phase36_34, phase36_40, phase36_41, phase36_42, phase36_43, phase36_44]
  try simp only [star_one, star_neg]
  linear_combination ((7591051 / 72) * t ^ 2 + (-3758321 / 20) * t ^ 4 + (-13991670203 / 38400) * t ^ 6 + (2223286364417 / 2400000) * t ^ 8 + (-132916950375647 / 230400000) * t ^ 10 + (38437098745093 / 345600000) * t ^ 12 + (-6070362057629 / 276480000) * t ^ 14 + (117730573249 / 21600000) * t ^ 16 + (2254152612169 / 4147200000) * t ^ 18 + (2024672166293 / 5529600000) * t ^ 20 + (913508661607 / 921600000) * t ^ 22 + (-73598705911 / 176947200) * t ^ 24 + (-63972446107 / 16588800000) * t ^ 26 + (4065941257 / 2654208000) * t ^ 32 + (-4087489 / 36) * d * t ^ 2 + (9175712 / 45) * d * t ^ 4 + (-1958121403 / 57600) * d * t ^ 6 + (-7829630384357 / 86400000) * d * t ^ 8 + (19400044936411 / 691200000) * d * t ^ 10 + (2460613950493 / 230400000) * d * t ^ 12 + (-68289603683 / 8294400) * d * t ^ 14 + (208569714023 / 64800000) * d * t ^ 16 + (442712598149 / 1036800000) * d * t ^ 18 + (-310974027799 / 6220800000) * d * t ^ 20 + (15745981199 / 1036800000) * d * t ^ 22 + (55621111 / 737280000) * d * t ^ 24 + (253755850823 / 24883200000) * d * t ^ 26 + (-4663379 / 265420800) * d * t ^ 32 + (583927 / 72) * d ^ 2 * t ^ 2 + (-2877959 / 180) * d ^ 2 * t ^ 4 + (122245439 / 23040) * d ^ 2 * t ^ 6 + (207328148407 / 51840000) * d ^ 2 * t ^ 8 + (-5776908197 / 17280000) * d ^ 2 * t ^ 10 + (-41828032049 / 46080000) * d ^ 2 * t ^ 12 + (-151807926593 / 829440000) * d ^ 2 * t ^ 14 + (48821501 / 25920000) * d ^ 2 * t ^ 16 + (317973203 / 165888000) * d ^ 2 * t ^ 18 + (11172592397 / 3317760000) * d ^ 2 * t ^ 20 + (-2859340547 / 1658880000) * d ^ 2 * t ^ 22 + (3409139 / 2654208000) * d ^ 2 * t ^ 24 + (-3642437 / 1990656000) * d ^ 2 * t ^ 26 + (9025 / 191102976) * d ^ 2 * t ^ 32) * alpha_sq + ((-583927 / 18) * t ^ 2 + (712537 / 10) * t ^ 4 + (-79350727 / 1920) * t ^ 6 + (42647636939 / 17280000) * t ^ 8 + (-204434813197 / 46080000) * t ^ 10 + (508853255333 / 138240000) * t ^ 12 + (41317050559 / 46080000) * t ^ 14 + (-15814879423 / 138240000) * t ^ 16 + (-136899757 / 41472000) * t ^ 18 + (-1428875741 / 414720000) * t ^ 20 + (-183850621 / 138240000) * t ^ 22 + (1987787 / 73728000) * t ^ 24 + (20304211 / 55296000) * t ^ 26 + (-9025 / 15925248) * t ^ 32) * d_sq
#print axioms v38_00
#print axioms v38_11
#print axioms v38_22
#print axioms v38_33
#print axioms v38_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
noncomputable def z39 : Fin 39 → ℂ := Fin.snoc z38 (r ^ 2 * phiMinus)
theorem v39_00 (t : ℂ) : (momentPoly 39 z39 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00]
  try simp only [phase36_00]
  try simp only [star_one, star_neg]
  ring
theorem v39_01 (t : ℂ) : (momentPoly 39 z39 0 1).eval t = ((1 / 2) * t + (1 / 2) * alpha * t) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_01]
  try simp only [phase36_00, phase36_01]
  try simp only [star_one, star_neg]
  ring
theorem v39_02 (t : ℂ) : (momentPoly 39 z39 0 2).eval t = ((-493 / 40) * t ^ 2 + (473 / 40) * t ^ 4 + (169 / 120) * alpha * t ^ 2 + (-109 / 120) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_01, v38_02]
  try simp only [phase36_00, phase36_01, phase36_02]
  try simp only [star_one, star_neg]
  linear_combination ((-25 / 1152) * t ^ 2 + (13 / 576) * d * t ^ 2 + (-1 / 1152) * d ^ 2 * t ^ 2) * alpha_sq + ((1 / 576) * t ^ 2 + (-1 / 576) * alpha * t ^ 2) * d_sq
theorem v39_03 (t : ℂ) : (momentPoly 39 z39 0 3).eval t = ((-833 / 40) * t ^ 3 + (753 / 40) * t ^ 5 + 1 * t ^ 9 + (-909 / 200) * alpha * t ^ 3 + (-137 / 100) * alpha * t ^ 5 + (1183 / 200) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_01, v38_02, v38_03]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03]
  try simp only [star_one, star_neg]
  linear_combination ((-377 / 2560) * t ^ 3 + (6611 / 7680) * t ^ 5 + (431 / 2880) * d * t ^ 3 + (-667 / 5760) * d * t ^ 5 + (-11 / 4608) * d ^ 2 * t ^ 3 + (-1 / 4608) * d ^ 2 * t ^ 5) * alpha_sq + ((1 / 96) * t ^ 3 + (1 / 1152) * alpha * t ^ 3 + (-1 / 1152) * alpha * t ^ 5) * d_sq
theorem v39_04 (t : ℂ) : (momentPoly 39 z39 0 4).eval t = ((2432307 / 8000) * t ^ 4 + (-2461067 / 4000) * t ^ 6 + (6050277 / 16000) * t ^ 8 + (-944663 / 12000) * t ^ 10 + (542783 / 48000) * t ^ 16 + (-1903769 / 24000) * alpha * t ^ 4 + (1599329 / 12000) * alpha * t ^ 6 + (-3185519 / 48000) * alpha * t ^ 8 + (405781 / 36000) * alpha * t ^ 10 + (92099 / 144000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_01, v38_02, v38_03, v38_04]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_04]
  try simp only [star_one, star_neg]
  linear_combination ((7589 / 14400) * t ^ 4 + (1606219 / 230400) * t ^ 6 + (-8531 / 2048) * t ^ 8 + (-38701 / 172800) * t ^ 10 + (-33731 / 57600) * d * t ^ 4 + (-857 / 115200) * d * t ^ 6 + (-911 / 46080) * d * t ^ 8 + (81601 / 172800) * d * t ^ 10 + (15 / 256) * d ^ 2 * t ^ 4 + (-1607 / 27648) * d ^ 2 * t ^ 6 + (-1 / 55296) * d ^ 2 * t ^ 8) * alpha_sq + ((-797 / 11520) * t ^ 4 + (613 / 7680) * t ^ 6 + (-1 / 9216) * t ^ 8 + (47 / 6912) * t ^ 10 + (1903 / 11520) * alpha * t ^ 4 + (-1187 / 7680) * alpha * t ^ 6 + (-1 / 9216) * alpha * t ^ 8 + (47 / 6912) * alpha * t ^ 10) * d_sq
theorem v39_10 (t : ℂ) : (momentPoly 39 z39 1 0).eval t = ((1 / 2) * t + (-1 / 2) * alpha * t) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_10]
  try simp only [phase36_00, phase36_10]
  try simp only [star_one, star_neg]
  ring
theorem v39_11 (t : ℂ) : (momentPoly 39 z39 1 1).eval t = (39 + (-38) * t ^ 2) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_01, v38_10, v38_11]
  try simp only [phase36_00, phase36_01, phase36_10, phase36_11]
  try simp only [star_one, star_neg]
  linear_combination ((25 / 1152) * t ^ 2 + (-13 / 576) * d * t ^ 2 + (1 / 1152) * d ^ 2 * t ^ 2) * alpha_sq + ((-1 / 288) * t ^ 2) * d_sq
theorem v39_12 (t : ℂ) : (momentPoly 39 z39 1 2).eval t = ((77 / 2) * t + (-841 / 20) * t ^ 3 + (81 / 20) * t ^ 5 + (77 / 2) * alpha * t + (-467 / 15) * alpha * t ^ 3 + (-103 / 15) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_01, v38_02, v38_10, v38_11, v38_12]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_10, phase36_11, phase36_12]
  try simp only [star_one, star_neg]
  linear_combination ((377 / 7680) * t ^ 3 + (-6611 / 23040) * t ^ 5 + (-431 / 8640) * d * t ^ 3 + (667 / 17280) * d * t ^ 5 + (11 / 13824) * d ^ 2 * t ^ 3 + (1 / 13824) * d ^ 2 * t ^ 5) * alpha_sq + ((-11 / 2304) * t ^ 3 + (-1 / 2304) * t ^ 5 + (-37 / 6912) * alpha * t ^ 3 + (1 / 6912) * alpha * t ^ 5) * d_sq
theorem v39_13 (t : ℂ) : (momentPoly 39 z39 1 3).eval t = ((-28101 / 20) * t ^ 2 + (67768 / 25) * t ^ 4 + (-521487 / 400) * t ^ 6 + (-981 / 400) * t ^ 10 + (3211 / 20) * alpha * t ^ 2 + (-75793 / 300) * alpha * t ^ 4 + (35691 / 400) * alpha * t ^ 6 + (4039 / 1200) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_01, v38_02, v38_03, v38_10, v38_11, v38_12, v38_13]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_10, phase36_11, phase36_12, phase36_13]
  try simp only [star_one, star_neg]
  linear_combination ((-475 / 192) * t ^ 2 + (98371 / 57600) * t ^ 4 + (110699 / 230400) * t ^ 6 + (38701 / 691200) * t ^ 10 + (247 / 96) * d * t ^ 2 + (-406939 / 230400) * d * t ^ 4 + (-118469 / 230400) * d * t ^ 6 + (-81601 / 691200) * d * t ^ 10 + (-19 / 192) * d ^ 2 * t ^ 2 + (299 / 5120) * d ^ 2 * t ^ 4 + (259 / 7680) * d ^ 2 * t ^ 6) * alpha_sq + ((19 / 96) * t ^ 2 + (-2129 / 46080) * t ^ 4 + (-6271 / 46080) * t ^ 6 + (47 / 27648) * t ^ 10 + (-19 / 96) * alpha * t ^ 2 + (7529 / 46080) * alpha * t ^ 4 + (871 / 46080) * alpha * t ^ 6 + (-47 / 27648) * alpha * t ^ 10) * d_sq
theorem v39_14 (t : ℂ) : (momentPoly 39 z39 1 4).eval t = ((-12495 / 4) * t ^ 3 + (47045469 / 8000) * t ^ 5 + (-11075469 / 4000) * t ^ 7 + (3277979 / 16000) * t ^ 9 + (-2394641 / 12000) * t ^ 11 + (269441 / 48000) * t ^ 17 + (-2727 / 4) * alpha * t ^ 3 + (1226267 / 4800) * alpha * t ^ 5 + (58013 / 96) * alpha * t ^ 7 + (6580621 / 9600) * alpha * t ^ 9 + (-6136247 / 7200) * alpha * t ^ 11 + (-323977 / 28800) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_01, v38_02, v38_03, v38_04, v38_10, v38_11, v38_12, v38_13, v38_14]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_04, phase36_10, phase36_11, phase36_12, phase36_13, phase36_14]
  try simp only [star_one, star_neg]
  linear_combination ((-5655 / 256) * t ^ 3 + (337364057 / 2304000) * t ^ 5 + (-427773953 / 4608000) * t ^ 7 + (-228288701 / 9216000) * t ^ 9 + (-1413721 / 6912000) * t ^ 11 + (7546021 / 27648000) * t ^ 17 + (2155 / 96) * d * t ^ 3 + (-6510761 / 192000) * d * t ^ 5 + (19570639 / 2304000) * d * t ^ 7 + (42381839 / 13824000) * d * t ^ 9 + (2122769 / 10368000) * d * t ^ 11 + (-1457969 / 41472000) * d * t ^ 17 + (-275 / 768) * d ^ 2 * t ^ 3 + (6041 / 30720) * d ^ 2 * t ^ 5 + (24659 / 184320) * d ^ 2 * t ^ 7 + (39 / 8192) * d ^ 2 * t ^ 9 + (-35 / 165888) * d ^ 2 * t ^ 11 + (95 / 663552) * d ^ 2 * t ^ 17) * alpha_sq + ((25 / 16) * t ^ 3 + (-21739 / 23040) * t ^ 5 + (-2879 / 5760) * t ^ 7 + (-11 / 384) * t ^ 9 + (23 / 1728) * t ^ 11 + (25 / 192) * alpha * t ^ 3 + (-1109 / 21600) * alpha * t ^ 5 + (-3611 / 230400) * alpha * t ^ 7 + (4447 / 276480) * alpha * t ^ 9 + (-81601 / 1036800) * alpha * t ^ 11 + (-95 / 165888) * alpha * t ^ 17) * d_sq
theorem v39_20 (t : ℂ) : (momentPoly 39 z39 2 0).eval t = ((-493 / 40) * t ^ 2 + (473 / 40) * t ^ 4 + (-169 / 120) * alpha * t ^ 2 + (109 / 120) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_10, v38_20]
  try simp only [phase36_00, phase36_10, phase36_20]
  try simp only [star_one, star_neg]
  linear_combination ((-25 / 1152) * t ^ 2 + (13 / 576) * d * t ^ 2 + (-1 / 1152) * d ^ 2 * t ^ 2) * alpha_sq + ((1 / 576) * t ^ 2 + (1 / 576) * alpha * t ^ 2) * d_sq
theorem v39_21 (t : ℂ) : (momentPoly 39 z39 2 1).eval t = ((77 / 2) * t + (-841 / 20) * t ^ 3 + (81 / 20) * t ^ 5 + (-77 / 2) * alpha * t + (467 / 15) * alpha * t ^ 3 + (103 / 15) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_01, v38_10, v38_11, v38_20, v38_21]
  try simp only [phase36_00, phase36_01, phase36_10, phase36_11, phase36_20, phase36_21]
  try simp only [star_one, star_neg]
  linear_combination ((377 / 7680) * t ^ 3 + (-6611 / 23040) * t ^ 5 + (-431 / 8640) * d * t ^ 3 + (667 / 17280) * d * t ^ 5 + (11 / 13824) * d ^ 2 * t ^ 3 + (1 / 13824) * d ^ 2 * t ^ 5) * alpha_sq + ((-11 / 2304) * t ^ 3 + (-1 / 2304) * t ^ 5 + (37 / 6912) * alpha * t ^ 3 + (-1 / 6912) * alpha * t ^ 5) * d_sq
theorem v39_22 (t : ℂ) : (momentPoly 39 z39 2 2).eval t = (3003 + (-5776) * t ^ 2 + (3381427 / 1200) * t ^ 4 + (-88297 / 600) * t ^ 6 + (123967 / 1200) * t ^ 8) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_01, v38_02, v38_10, v38_11, v38_12, v38_20, v38_21, v38_22]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_10, phase36_11, phase36_12, phase36_20, phase36_21, phase36_22]
  try simp only [star_one, star_neg]
  linear_combination ((475 / 144) * t ^ 2 + (-883 / 360) * t ^ 4 + (-136601 / 46080) * t ^ 6 + (8531 / 6144) * t ^ 8 + (-247 / 72) * d * t ^ 2 + (14689 / 5760) * d * t ^ 4 + (15853 / 23040) * d * t ^ 6 + (911 / 138240) * d * t ^ 8 + (19 / 144) * d ^ 2 * t ^ 2 + (-187 / 1920) * d ^ 2 * t ^ 4 + (-10613 / 414720) * d ^ 2 * t ^ 6 + (1 / 165888) * d ^ 2 * t ^ 8) * alpha_sq + ((-19 / 36) * t ^ 2 + (823 / 1920) * t ^ 4 + (2231 / 34560) * t ^ 6 + (-1 / 13824) * t ^ 8) * d_sq
theorem v39_23 (t : ℂ) : (momentPoly 39 z39 2 3).eval t = ((8779 / 2) * t + (-37845 / 4) * t ^ 3 + (12043231 / 2000) * t ^ 5 + (-1770123 / 1600) * t ^ 7 + (1257511 / 8000) * t ^ 9 + (36527 / 8000) * t ^ 11 + (-38347 / 8000) * t ^ 13 + (8779 / 2) * alpha * t + (-7005) * alpha * t ^ 3 + (3100237 / 3000) * alpha * t ^ 5 + (7719901 / 4800) * alpha * t ^ 7 + (-284007 / 8000) * alpha * t ^ 9 + (-484619 / 8000) * alpha * t ^ 11 + (1688477 / 24000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_01, v38_02, v38_03, v38_10, v38_11, v38_12, v38_13, v38_20, v38_21, v38_22, v38_23]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_10, phase36_11, phase36_12, phase36_13, phase36_20, phase36_21, phase36_22, phase36_23]
  try simp only [star_one, star_neg]
  linear_combination ((5655 / 512) * t ^ 3 + (-17286899 / 230400) * t ^ 5 + (1340449 / 25600) * t ^ 7 + (2051449 / 184320) * t ^ 9 + (-359059 / 2764800) * t ^ 11 + (-1488071 / 552960) * t ^ 13 + (-2155 / 192) * d * t ^ 3 + (812099 / 43200) * d * t ^ 5 + (-20510413 / 2764800) * d * t ^ 7 + (-211229 / 2764800) * d * t ^ 9 + (-1350731 / 8294400) * d * t ^ 11 + (-81601 / 8294400) * d * t ^ 13 + (275 / 1536) * d ^ 2 * t ^ 3 + (-86087 / 691200) * d ^ 2 * t ^ 5 + (-45551 / 921600) * d ^ 2 * t ^ 7 + (-7 / 17280) * d ^ 2 * t ^ 9 + (2291 / 460800) * d ^ 2 * t ^ 11) * alpha_sq + ((-275 / 256) * t ^ 3 + (190259 / 230400) * t ^ 5 + (74477 / 307200) * t ^ 7 + (-527 / 36864) * t ^ 9 + (-9839 / 307200) * t ^ 11 + (47 / 110592) * t ^ 13 + (-925 / 768) * alpha * t ^ 3 + (642761 / 691200) * alpha * t ^ 5 + (632089 / 2764800) * alpha * t ^ 7 + (-1585 / 110592) * alpha * t ^ 9 + (70151 / 8294400) * alpha * t ^ 11 + (-47 / 331776) * alpha * t ^ 13) * d_sq
theorem v39_24 (t : ℂ) : (momentPoly 39 z39 2 4).eval t = ((-1054034 / 5) * t ^ 2 + (121132849 / 200) * t ^ 4 + (-275852724307 / 480000) * t ^ 6 + (28359678507 / 160000) * t ^ 8 + (-15460093 / 192000) * t ^ 10 + (10315779683 / 2880000) * t ^ 12 + (-649794263 / 720000) * t ^ 14 + (-379479263 / 2880000) * t ^ 18 + (346029143 / 2880000) * t ^ 20 + (361322 / 15) * alpha * t ^ 2 + (-35803381 / 600) * alpha * t ^ 4 + (22166283517 / 480000) * alpha * t ^ 6 + (-5131074311 / 480000) * alpha * t ^ 8 + (82182257 / 64000) * alpha * t ^ 10 + (-3514570213 / 2880000) * alpha * t ^ 12 + (10244491 / 240000) * alpha * t ^ 14 + (-87954767 / 2880000) * alpha * t ^ 18 + (17993029 / 960000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_01, v38_02, v38_03, v38_04, v38_10, v38_11, v38_12, v38_13, v38_14, v38_20, v38_21, v38_22, v38_23, v38_24]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_04, phase36_10, phase36_11, phase36_12, phase36_13, phase36_14, phase36_20, phase36_21, phase36_22, phase36_23, phase36_24]
  try simp only [star_one, star_neg]
  linear_combination ((-26725 / 72) * t ^ 2 + (3639727 / 7200) * t ^ 4 + (-43970489 / 2764800) * t ^ 6 + (-231823799 / 9216000) * t ^ 8 + (-7049744597 / 55296000) * t ^ 10 + (4427970589 / 110592000) * t ^ 12 + (-47175199 / 9216000) * t ^ 14 + (72928591 / 110592000) * t ^ 18 + (-9039653 / 7372800) * t ^ 20 + (13897 / 36) * d * t ^ 2 + (-15056743 / 28800) * d * t ^ 4 + (127431 / 12800) * d * t ^ 6 + (36181339 / 307200) * d * t ^ 8 + (-64541383 / 2764800) * d * t ^ 10 + (750229433 / 27648000) * d * t ^ 12 + (63097379 / 10368000) * d * t ^ 14 + (37526063 / 82944000) * d * t ^ 18 + (12949 / 3456000) * d * t ^ 20 + (-1069 / 72) * d ^ 2 * t ^ 2 + (11063 / 640) * d ^ 2 * t ^ 4 + (16445393 / 2764800) * d ^ 2 * t ^ 6 + (-120280139 / 16588800) * d ^ 2 * t ^ 8 + (-13638307 / 11059200) * d ^ 2 * t ^ 10 + (3107449 / 66355200) * d ^ 2 * t ^ 12 + (246289 / 49766400) * d ^ 2 * t ^ 14 + (-70415 / 7962624) * d ^ 2 * t ^ 18 + (95 / 7962624) * d ^ 2 * t ^ 20) * alpha_sq + ((1069 / 36) * t ^ 2 + (-78773 / 5760) * t ^ 4 + (-177184433 / 3456000) * t ^ 6 + (447785789 / 13824000) * t ^ 8 + (98589433 / 27648000) * t ^ 10 + (-34274227 / 55296000) * t ^ 12 + (481741 / 8294400) * t ^ 14 + (1843229 / 165888000) * t ^ 18 + (95 / 1327104) * t ^ 20 + (-1069 / 36) * alpha * t ^ 2 + (278573 / 5760) * alpha * t ^ 4 + (-2069843 / 144000) * alpha * t ^ 6 + (-5006561 / 1536000) * alpha * t ^ 8 + (-4458937 / 3072000) * alpha * t ^ 10 + (24034721 / 165888000) * alpha * t ^ 12 + (83251 / 921600) * alpha * t ^ 14 + (1307257 / 55296000) * alpha * t ^ 18 + (-95 / 1327104) * alpha * t ^ 20) * d_sq
theorem v39_30 (t : ℂ) : (momentPoly 39 z39 3 0).eval t = ((-833 / 40) * t ^ 3 + (753 / 40) * t ^ 5 + 1 * t ^ 9 + (909 / 200) * alpha * t ^ 3 + (137 / 100) * alpha * t ^ 5 + (-1183 / 200) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_10, v38_20, v38_30]
  try simp only [phase36_00, phase36_10, phase36_20, phase36_30]
  try simp only [star_one, star_neg]
  linear_combination ((-377 / 2560) * t ^ 3 + (6611 / 7680) * t ^ 5 + (431 / 2880) * d * t ^ 3 + (-667 / 5760) * d * t ^ 5 + (-11 / 4608) * d ^ 2 * t ^ 3 + (-1 / 4608) * d ^ 2 * t ^ 5) * alpha_sq + ((1 / 96) * t ^ 3 + (-1 / 1152) * alpha * t ^ 3 + (1 / 1152) * alpha * t ^ 5) * d_sq
theorem v39_31 (t : ℂ) : (momentPoly 39 z39 3 1).eval t = ((-28101 / 20) * t ^ 2 + (67768 / 25) * t ^ 4 + (-521487 / 400) * t ^ 6 + (-981 / 400) * t ^ 10 + (-3211 / 20) * alpha * t ^ 2 + (75793 / 300) * alpha * t ^ 4 + (-35691 / 400) * alpha * t ^ 6 + (-4039 / 1200) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_01, v38_10, v38_11, v38_20, v38_21, v38_30, v38_31]
  try simp only [phase36_00, phase36_01, phase36_10, phase36_11, phase36_20, phase36_21, phase36_30, phase36_31]
  try simp only [star_one, star_neg]
  linear_combination ((-475 / 192) * t ^ 2 + (98371 / 57600) * t ^ 4 + (110699 / 230400) * t ^ 6 + (38701 / 691200) * t ^ 10 + (247 / 96) * d * t ^ 2 + (-406939 / 230400) * d * t ^ 4 + (-118469 / 230400) * d * t ^ 6 + (-81601 / 691200) * d * t ^ 10 + (-19 / 192) * d ^ 2 * t ^ 2 + (299 / 5120) * d ^ 2 * t ^ 4 + (259 / 7680) * d ^ 2 * t ^ 6) * alpha_sq + ((19 / 96) * t ^ 2 + (-2129 / 46080) * t ^ 4 + (-6271 / 46080) * t ^ 6 + (47 / 27648) * t ^ 10 + (19 / 96) * alpha * t ^ 2 + (-7529 / 46080) * alpha * t ^ 4 + (-871 / 46080) * alpha * t ^ 6 + (47 / 27648) * alpha * t ^ 10) * d_sq
theorem v39_32 (t : ℂ) : (momentPoly 39 z39 3 2).eval t = ((8779 / 2) * t + (-37845 / 4) * t ^ 3 + (12043231 / 2000) * t ^ 5 + (-1770123 / 1600) * t ^ 7 + (1257511 / 8000) * t ^ 9 + (36527 / 8000) * t ^ 11 + (-38347 / 8000) * t ^ 13 + (-8779 / 2) * alpha * t + 7005 * alpha * t ^ 3 + (-3100237 / 3000) * alpha * t ^ 5 + (-7719901 / 4800) * alpha * t ^ 7 + (284007 / 8000) * alpha * t ^ 9 + (484619 / 8000) * alpha * t ^ 11 + (-1688477 / 24000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_01, v38_02, v38_10, v38_11, v38_12, v38_20, v38_21, v38_22, v38_30, v38_31, v38_32]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_10, phase36_11, phase36_12, phase36_20, phase36_21, phase36_22, phase36_30, phase36_31, phase36_32]
  try simp only [star_one, star_neg]
  linear_combination ((5655 / 512) * t ^ 3 + (-17286899 / 230400) * t ^ 5 + (1340449 / 25600) * t ^ 7 + (2051449 / 184320) * t ^ 9 + (-359059 / 2764800) * t ^ 11 + (-1488071 / 552960) * t ^ 13 + (-2155 / 192) * d * t ^ 3 + (812099 / 43200) * d * t ^ 5 + (-20510413 / 2764800) * d * t ^ 7 + (-211229 / 2764800) * d * t ^ 9 + (-1350731 / 8294400) * d * t ^ 11 + (-81601 / 8294400) * d * t ^ 13 + (275 / 1536) * d ^ 2 * t ^ 3 + (-86087 / 691200) * d ^ 2 * t ^ 5 + (-45551 / 921600) * d ^ 2 * t ^ 7 + (-7 / 17280) * d ^ 2 * t ^ 9 + (2291 / 460800) * d ^ 2 * t ^ 11) * alpha_sq + ((-275 / 256) * t ^ 3 + (190259 / 230400) * t ^ 5 + (74477 / 307200) * t ^ 7 + (-527 / 36864) * t ^ 9 + (-9839 / 307200) * t ^ 11 + (47 / 110592) * t ^ 13 + (925 / 768) * alpha * t ^ 3 + (-642761 / 691200) * alpha * t ^ 5 + (-632089 / 2764800) * alpha * t ^ 7 + (1585 / 110592) * alpha * t ^ 9 + (-70151 / 8294400) * alpha * t ^ 11 + (47 / 331776) * alpha * t ^ 13) * d_sq
theorem v39_33 (t : ℂ) : (momentPoly 39 z39 3 3).eval t = (342381 + (-974928) * t ^ 2 + (375338397 / 400) * t ^ 4 + (-1772456279 / 5000) * t ^ 6 + (1636979023 / 20000) * t ^ 8 + (-1322335047 / 40000) * t ^ 10 + (4770659 / 20000) * t ^ 12 + (-4028063 / 10000) * t ^ 14 + (2678467 / 40000) * t ^ 18) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_01, v38_02, v38_03, v38_10, v38_11, v38_12, v38_13, v38_20, v38_21, v38_22, v38_23, v38_30, v38_31, v38_32, v38_33]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_10, phase36_11, phase36_12, phase36_13, phase36_20, phase36_21, phase36_22, phase36_23, phase36_30, phase36_31, phase36_32, phase36_33]
  try simp only [star_one, star_neg]
  linear_combination ((26725 / 48) * t ^ 2 + (-32671 / 40) * t ^ 4 + (-368491669 / 512000) * t ^ 6 + (421850441 / 307200) * t ^ 8 + (-101179833 / 256000) * t ^ 10 + (-178137083 / 27648000) * t ^ 12 + (-36273191 / 13824000) * t ^ 14 + (-23849111 / 16588800) * t ^ 18 + (-13897 / 24) * d * t ^ 2 + (543493 / 640) * d * t ^ 4 + (-65356891 / 1152000) * d * t ^ 6 + (-96284989 / 460800) * d * t ^ 8 + (-3928181 / 768000) * d * t ^ 10 + (107714219 / 13824000) * d * t ^ 12 + (-14759503 / 1728000) * d * t ^ 14 + (1069 / 48) * d ^ 2 * t ^ 2 + (-20757 / 640) * d ^ 2 * t ^ 4 + (8255231 / 2764800) * d ^ 2 * t ^ 6 + (3390869 / 552960) * d ^ 2 * t ^ 8 + (249119 / 230400) * d ^ 2 * t ^ 10 + (51659 / 1105920) * d ^ 2 * t ^ 12 + (-3431 / 691200) * d ^ 2 * t ^ 14) * alpha_sq + ((-1069 / 12) * t ^ 2 + (91353 / 640) * t ^ 4 + (-16972447 / 460800) * t ^ 6 + (-2895841 / 230400) * t ^ 8 + (-223899 / 51200) * t ^ 10 + (-970999 / 2764800) * t ^ 12 + (439159 / 2764800) * t ^ 14 + (-2209 / 663552) * t ^ 18) * d_sq
theorem v39_34 (t : ℂ) : (momentPoly 39 z39 3 4).eval t = ((1317309 / 2) * t + (-10505772 / 5) * t ^ 3 + (2440771239 / 1000) * t ^ 5 + (-1020779858517 / 800000) * t ^ 7 + (548348153749 / 1600000) * t ^ 9 + (-105974972869 / 1600000) * t ^ 11 + (932403367 / 1920000) * t ^ 13 + (455319379 / 300000) * t ^ 15 + (-2636173577 / 3200000) * t ^ 17 + (-928507747 / 4800000) * t ^ 19 + (2039752069 / 9600000) * t ^ 21 + (70903239 / 3200000) * t ^ 25 + (1317309 / 2) * alpha * t + (-7778352 / 5) * alpha * t ^ 3 + (393064001 / 500) * alpha * t ^ 5 + (368902844579 / 800000) * alpha * t ^ 7 + (-1683498833119 / 4800000) * alpha * t ^ 9 + (-145106870171 / 4800000) * alpha * t ^ 11 + (338721274171 / 5760000) * alpha * t ^ 13 + (-5186833627 / 200000) * alpha * t ^ 15 + (-21714016873 / 9600000) * alpha * t ^ 17 + (1628672209 / 4800000) * alpha * t ^ 19 + (-1564105613 / 9600000) * alpha * t ^ 21 + (-1922317067 / 28800000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_01, v38_02, v38_03, v38_04, v38_10, v38_11, v38_12, v38_13, v38_14, v38_20, v38_21, v38_22, v38_23, v38_24, v38_30, v38_31, v38_32, v38_33, v38_34]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_04, phase36_10, phase36_11, phase36_12, phase36_13, phase36_14, phase36_20, phase36_21, phase36_22, phase36_23, phase36_24, phase36_30, phase36_31, phase36_32, phase36_33, phase36_34]
  try simp only [star_one, star_neg]
  linear_combination ((392457 / 160) * t ^ 3 + (-90852029 / 4800) * t ^ 5 + (16034473081 / 640000) * t ^ 7 + (-651344107609 / 184320000) * t ^ 9 + (-11031782253 / 2048000) * t ^ 11 + (-843769611587 / 1105920000) * t ^ 13 + (347774555117 / 276480000) * t ^ 15 + (-44513233727 / 221184000) * t ^ 17 + (-1833871759 / 207360000) * t ^ 19 + (20856440113 / 1105920000) * t ^ 21 + (1749477457 / 663552000) * t ^ 25 + (-149557 / 60) * d * t ^ 3 + (20349177 / 3200) * d * t ^ 5 + (-720558406241 / 138240000) * d * t ^ 7 + (190639587583 / 138240000) * d * t ^ 9 + (-757372811 / 5529600) * d * t ^ 11 + (37523967887 / 414720000) * d * t ^ 13 + (2290751497 / 184320000) * d * t ^ 15 + (-591202001 / 663552000) * d * t ^ 17 + (36626554697 / 9953280000) * d * t ^ 19 + (-8555973019 / 3317760000) * d * t ^ 21 + (-1550419 / 79626240) * d * t ^ 25 + (3817 / 96) * d ^ 2 * t ^ 3 + (-557423 / 9600) * d ^ 2 * t ^ 5 + (13049023 / 9216000) * d ^ 2 * t ^ 7 + (191795927 / 12288000) * d ^ 2 * t ^ 9 + (176500829 / 55296000) * d ^ 2 * t ^ 11 + (-29427211 / 14745600) * d ^ 2 * t ^ 13 + (73856449 / 331776000) * d ^ 2 * t ^ 15 + (-34321 / 66355200) * d ^ 2 * t ^ 17 + (-11165273 / 221184000) * d ^ 2 * t ^ 19 + (327931 / 165888000) * d ^ 2 * t ^ 21) * alpha_sq + ((-3817 / 16) * t ^ 3 + (14698357 / 38400) * t ^ 5 + (-64399999 / 1024000) * t ^ 7 + (-127138931 / 1536000) * t ^ 9 + (-698623 / 64000) * t ^ 11 + (919283 / 72000) * t ^ 13 + (-123689527 / 110592000) * t ^ 15 + (1573169 / 44236800) * t ^ 17 + (9378319 / 44236800) * t ^ 19 + (1183729 / 221184000) * t ^ 21 + (-4465 / 5308416) * t ^ 25 + (-12839 / 48) * alpha * t ^ 3 + (5123567 / 12800) * alpha * t ^ 5 + (-967655063 / 27648000) * alpha * t ^ 7 + (-168286091 / 1728000) * alpha * t ^ 9 + (1550483 / 552960) * alpha * t ^ 11 + (-1213673 / 2764800) * alpha * t ^ 13 + (-358817491 / 110592000) * alpha * t ^ 15 + (870431 / 132710400) * alpha * t ^ 17 + (1890223 / 1990656000) * alpha * t ^ 19 + (-7673729 / 663552000) * alpha * t ^ 21 + (4465 / 15925248) * alpha * t ^ 25) * d_sq
theorem v39_40 (t : ℂ) : (momentPoly 39 z39 4 0).eval t = ((2432307 / 8000) * t ^ 4 + (-2461067 / 4000) * t ^ 6 + (6050277 / 16000) * t ^ 8 + (-944663 / 12000) * t ^ 10 + (542783 / 48000) * t ^ 16 + (1903769 / 24000) * alpha * t ^ 4 + (-1599329 / 12000) * alpha * t ^ 6 + (3185519 / 48000) * alpha * t ^ 8 + (-405781 / 36000) * alpha * t ^ 10 + (-92099 / 144000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_10, v38_20, v38_30, v38_40]
  try simp only [phase36_00, phase36_10, phase36_20, phase36_30, phase36_40]
  try simp only [star_one, star_neg]
  linear_combination ((7589 / 14400) * t ^ 4 + (1606219 / 230400) * t ^ 6 + (-8531 / 2048) * t ^ 8 + (-38701 / 172800) * t ^ 10 + (-33731 / 57600) * d * t ^ 4 + (-857 / 115200) * d * t ^ 6 + (-911 / 46080) * d * t ^ 8 + (81601 / 172800) * d * t ^ 10 + (15 / 256) * d ^ 2 * t ^ 4 + (-1607 / 27648) * d ^ 2 * t ^ 6 + (-1 / 55296) * d ^ 2 * t ^ 8) * alpha_sq + ((-797 / 11520) * t ^ 4 + (613 / 7680) * t ^ 6 + (-1 / 9216) * t ^ 8 + (47 / 6912) * t ^ 10 + (-1903 / 11520) * alpha * t ^ 4 + (1187 / 7680) * alpha * t ^ 6 + (1 / 9216) * alpha * t ^ 8 + (-47 / 6912) * alpha * t ^ 10) * d_sq
theorem v39_41 (t : ℂ) : (momentPoly 39 z39 4 1).eval t = ((-12495 / 4) * t ^ 3 + (47045469 / 8000) * t ^ 5 + (-11075469 / 4000) * t ^ 7 + (3277979 / 16000) * t ^ 9 + (-2394641 / 12000) * t ^ 11 + (269441 / 48000) * t ^ 17 + (2727 / 4) * alpha * t ^ 3 + (-1226267 / 4800) * alpha * t ^ 5 + (-58013 / 96) * alpha * t ^ 7 + (-6580621 / 9600) * alpha * t ^ 9 + (6136247 / 7200) * alpha * t ^ 11 + (323977 / 28800) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_01, v38_10, v38_11, v38_20, v38_21, v38_30, v38_31, v38_40, v38_41]
  try simp only [phase36_00, phase36_01, phase36_10, phase36_11, phase36_20, phase36_21, phase36_30, phase36_31, phase36_40, phase36_41]
  try simp only [star_one, star_neg]
  linear_combination ((-5655 / 256) * t ^ 3 + (337364057 / 2304000) * t ^ 5 + (-427773953 / 4608000) * t ^ 7 + (-228288701 / 9216000) * t ^ 9 + (-1413721 / 6912000) * t ^ 11 + (7546021 / 27648000) * t ^ 17 + (2155 / 96) * d * t ^ 3 + (-6510761 / 192000) * d * t ^ 5 + (19570639 / 2304000) * d * t ^ 7 + (42381839 / 13824000) * d * t ^ 9 + (2122769 / 10368000) * d * t ^ 11 + (-1457969 / 41472000) * d * t ^ 17 + (-275 / 768) * d ^ 2 * t ^ 3 + (6041 / 30720) * d ^ 2 * t ^ 5 + (24659 / 184320) * d ^ 2 * t ^ 7 + (39 / 8192) * d ^ 2 * t ^ 9 + (-35 / 165888) * d ^ 2 * t ^ 11 + (95 / 663552) * d ^ 2 * t ^ 17) * alpha_sq + ((25 / 16) * t ^ 3 + (-21739 / 23040) * t ^ 5 + (-2879 / 5760) * t ^ 7 + (-11 / 384) * t ^ 9 + (23 / 1728) * t ^ 11 + (-25 / 192) * alpha * t ^ 3 + (1109 / 21600) * alpha * t ^ 5 + (3611 / 230400) * alpha * t ^ 7 + (-4447 / 276480) * alpha * t ^ 9 + (81601 / 1036800) * alpha * t ^ 11 + (95 / 165888) * alpha * t ^ 17) * d_sq
theorem v39_42 (t : ℂ) : (momentPoly 39 z39 4 2).eval t = ((-1054034 / 5) * t ^ 2 + (121132849 / 200) * t ^ 4 + (-275852724307 / 480000) * t ^ 6 + (28359678507 / 160000) * t ^ 8 + (-15460093 / 192000) * t ^ 10 + (10315779683 / 2880000) * t ^ 12 + (-649794263 / 720000) * t ^ 14 + (-379479263 / 2880000) * t ^ 18 + (346029143 / 2880000) * t ^ 20 + (-361322 / 15) * alpha * t ^ 2 + (35803381 / 600) * alpha * t ^ 4 + (-22166283517 / 480000) * alpha * t ^ 6 + (5131074311 / 480000) * alpha * t ^ 8 + (-82182257 / 64000) * alpha * t ^ 10 + (3514570213 / 2880000) * alpha * t ^ 12 + (-10244491 / 240000) * alpha * t ^ 14 + (87954767 / 2880000) * alpha * t ^ 18 + (-17993029 / 960000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_01, v38_02, v38_10, v38_11, v38_12, v38_20, v38_21, v38_22, v38_30, v38_31, v38_32, v38_40, v38_41, v38_42]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_10, phase36_11, phase36_12, phase36_20, phase36_21, phase36_22, phase36_30, phase36_31, phase36_32, phase36_40, phase36_41, phase36_42]
  try simp only [star_one, star_neg]
  linear_combination ((-26725 / 72) * t ^ 2 + (3639727 / 7200) * t ^ 4 + (-43970489 / 2764800) * t ^ 6 + (-231823799 / 9216000) * t ^ 8 + (-7049744597 / 55296000) * t ^ 10 + (4427970589 / 110592000) * t ^ 12 + (-47175199 / 9216000) * t ^ 14 + (72928591 / 110592000) * t ^ 18 + (-9039653 / 7372800) * t ^ 20 + (13897 / 36) * d * t ^ 2 + (-15056743 / 28800) * d * t ^ 4 + (127431 / 12800) * d * t ^ 6 + (36181339 / 307200) * d * t ^ 8 + (-64541383 / 2764800) * d * t ^ 10 + (750229433 / 27648000) * d * t ^ 12 + (63097379 / 10368000) * d * t ^ 14 + (37526063 / 82944000) * d * t ^ 18 + (12949 / 3456000) * d * t ^ 20 + (-1069 / 72) * d ^ 2 * t ^ 2 + (11063 / 640) * d ^ 2 * t ^ 4 + (16445393 / 2764800) * d ^ 2 * t ^ 6 + (-120280139 / 16588800) * d ^ 2 * t ^ 8 + (-13638307 / 11059200) * d ^ 2 * t ^ 10 + (3107449 / 66355200) * d ^ 2 * t ^ 12 + (246289 / 49766400) * d ^ 2 * t ^ 14 + (-70415 / 7962624) * d ^ 2 * t ^ 18 + (95 / 7962624) * d ^ 2 * t ^ 20) * alpha_sq + ((1069 / 36) * t ^ 2 + (-78773 / 5760) * t ^ 4 + (-177184433 / 3456000) * t ^ 6 + (447785789 / 13824000) * t ^ 8 + (98589433 / 27648000) * t ^ 10 + (-34274227 / 55296000) * t ^ 12 + (481741 / 8294400) * t ^ 14 + (1843229 / 165888000) * t ^ 18 + (95 / 1327104) * t ^ 20 + (1069 / 36) * alpha * t ^ 2 + (-278573 / 5760) * alpha * t ^ 4 + (2069843 / 144000) * alpha * t ^ 6 + (5006561 / 1536000) * alpha * t ^ 8 + (4458937 / 3072000) * alpha * t ^ 10 + (-24034721 / 165888000) * alpha * t ^ 12 + (-83251 / 921600) * alpha * t ^ 14 + (-1307257 / 55296000) * alpha * t ^ 18 + (95 / 1327104) * alpha * t ^ 20) * d_sq
theorem v39_43 (t : ℂ) : (momentPoly 39 z39 4 3).eval t = ((1317309 / 2) * t + (-10505772 / 5) * t ^ 3 + (2440771239 / 1000) * t ^ 5 + (-1020779858517 / 800000) * t ^ 7 + (548348153749 / 1600000) * t ^ 9 + (-105974972869 / 1600000) * t ^ 11 + (932403367 / 1920000) * t ^ 13 + (455319379 / 300000) * t ^ 15 + (-2636173577 / 3200000) * t ^ 17 + (-928507747 / 4800000) * t ^ 19 + (2039752069 / 9600000) * t ^ 21 + (70903239 / 3200000) * t ^ 25 + (-1317309 / 2) * alpha * t + (7778352 / 5) * alpha * t ^ 3 + (-393064001 / 500) * alpha * t ^ 5 + (-368902844579 / 800000) * alpha * t ^ 7 + (1683498833119 / 4800000) * alpha * t ^ 9 + (145106870171 / 4800000) * alpha * t ^ 11 + (-338721274171 / 5760000) * alpha * t ^ 13 + (5186833627 / 200000) * alpha * t ^ 15 + (21714016873 / 9600000) * alpha * t ^ 17 + (-1628672209 / 4800000) * alpha * t ^ 19 + (1564105613 / 9600000) * alpha * t ^ 21 + (1922317067 / 28800000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_01, v38_02, v38_03, v38_10, v38_11, v38_12, v38_13, v38_20, v38_21, v38_22, v38_23, v38_30, v38_31, v38_32, v38_33, v38_40, v38_41, v38_42, v38_43]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_10, phase36_11, phase36_12, phase36_13, phase36_20, phase36_21, phase36_22, phase36_23, phase36_30, phase36_31, phase36_32, phase36_33, phase36_40, phase36_41, phase36_42, phase36_43]
  try simp only [star_one, star_neg]
  linear_combination ((392457 / 160) * t ^ 3 + (-90852029 / 4800) * t ^ 5 + (16034473081 / 640000) * t ^ 7 + (-651344107609 / 184320000) * t ^ 9 + (-11031782253 / 2048000) * t ^ 11 + (-843769611587 / 1105920000) * t ^ 13 + (347774555117 / 276480000) * t ^ 15 + (-44513233727 / 221184000) * t ^ 17 + (-1833871759 / 207360000) * t ^ 19 + (20856440113 / 1105920000) * t ^ 21 + (1749477457 / 663552000) * t ^ 25 + (-149557 / 60) * d * t ^ 3 + (20349177 / 3200) * d * t ^ 5 + (-720558406241 / 138240000) * d * t ^ 7 + (190639587583 / 138240000) * d * t ^ 9 + (-757372811 / 5529600) * d * t ^ 11 + (37523967887 / 414720000) * d * t ^ 13 + (2290751497 / 184320000) * d * t ^ 15 + (-591202001 / 663552000) * d * t ^ 17 + (36626554697 / 9953280000) * d * t ^ 19 + (-8555973019 / 3317760000) * d * t ^ 21 + (-1550419 / 79626240) * d * t ^ 25 + (3817 / 96) * d ^ 2 * t ^ 3 + (-557423 / 9600) * d ^ 2 * t ^ 5 + (13049023 / 9216000) * d ^ 2 * t ^ 7 + (191795927 / 12288000) * d ^ 2 * t ^ 9 + (176500829 / 55296000) * d ^ 2 * t ^ 11 + (-29427211 / 14745600) * d ^ 2 * t ^ 13 + (73856449 / 331776000) * d ^ 2 * t ^ 15 + (-34321 / 66355200) * d ^ 2 * t ^ 17 + (-11165273 / 221184000) * d ^ 2 * t ^ 19 + (327931 / 165888000) * d ^ 2 * t ^ 21) * alpha_sq + ((-3817 / 16) * t ^ 3 + (14698357 / 38400) * t ^ 5 + (-64399999 / 1024000) * t ^ 7 + (-127138931 / 1536000) * t ^ 9 + (-698623 / 64000) * t ^ 11 + (919283 / 72000) * t ^ 13 + (-123689527 / 110592000) * t ^ 15 + (1573169 / 44236800) * t ^ 17 + (9378319 / 44236800) * t ^ 19 + (1183729 / 221184000) * t ^ 21 + (-4465 / 5308416) * t ^ 25 + (12839 / 48) * alpha * t ^ 3 + (-5123567 / 12800) * alpha * t ^ 5 + (967655063 / 27648000) * alpha * t ^ 7 + (168286091 / 1728000) * alpha * t ^ 9 + (-1550483 / 552960) * alpha * t ^ 11 + (1213673 / 2764800) * alpha * t ^ 13 + (358817491 / 110592000) * alpha * t ^ 15 + (-870431 / 132710400) * alpha * t ^ 17 + (-1890223 / 1990656000) * alpha * t ^ 19 + (7673729 / 663552000) * alpha * t ^ 21 + (-4465 / 15925248) * alpha * t ^ 25) * d_sq
theorem v39_44 (t : ℂ) : (momentPoly 39 z39 4 4).eval t = (51375051 + (-192500400) * t ^ 2 + (27413228689 / 100) * t ^ 4 + (-475702672027 / 2500) * t ^ 6 + (3843458673432827 / 48000000) * t ^ 8 + (-373683665549827 / 12000000) * t ^ 10 + (77637299853733 / 9600000) * t ^ 12 + (-880925378677 / 72000000) * t ^ 14 + (182340504937057 / 576000000) * t ^ 16 + (-1099376238773 / 72000000) * t ^ 18 + (-12167722895423 / 432000000) * t ^ 20 + (-785462792303 / 72000000) * t ^ 22 + (2032619887073 / 288000000) * t ^ 24 + (-425263031167 / 216000000) * t ^ 26 + (155688595267 / 1728000000) * t ^ 32) := by
  rw [momentPoly]
  simp only [z39, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v38_00, v38_01, v38_02, v38_03, v38_04, v38_10, v38_11, v38_12, v38_13, v38_14, v38_20, v38_21, v38_22, v38_23, v38_24, v38_30, v38_31, v38_32, v38_33, v38_34, v38_40, v38_41, v38_42, v38_43, v38_44]
  try simp only [phase36_00, phase36_01, phase36_02, phase36_03, phase36_04, phase36_10, phase36_11, phase36_12, phase36_13, phase36_14, phase36_20, phase36_21, phase36_22, phase36_23, phase36_24, phase36_30, phase36_31, phase36_32, phase36_33, phase36_34, phase36_40, phase36_41, phase36_42, phase36_43, phase36_44]
  try simp only [star_one, star_neg]
  linear_combination ((5276875 / 48) * t ^ 2 + (-7158481 / 30) * t ^ 4 + (-25810971779 / 192000) * t ^ 6 + (145880284529437 / 230400000) * t ^ 8 + (-106650335089637 / 230400000) * t ^ 10 + (43425875695169 / 460800000) * t ^ 12 + (-1115813950651 / 207360000) * t ^ 14 + (76007062619 / 21600000) * t ^ 16 + (-183515806631 / 307200000) * t ^ 18 + (11180146192019 / 16588800000) * t ^ 20 + (5869725708919 / 11059200000) * t ^ 22 + (-51509599781 / 176947200) * t ^ 24 + (10067046127 / 1843200000) * t ^ 26 + (632571821 / 589824000) * t ^ 32 + (-2743975 / 24) * d * t ^ 2 + (119083723 / 480) * d * t ^ 4 + (-9378853193 / 96000) * d * t ^ 6 + (-30778102080133 / 345600000) * d * t ^ 8 + (11351421367747 / 230400000) * d * t ^ 10 + (11840466333713 / 1382400000) * d * t ^ 12 + (-70142961769 / 7680000) * d * t ^ 14 + (10777169589133 / 2764800000) * d * t ^ 16 + (70389370879 / 172800000) * d * t ^ 18 + (-111710426653 / 2073600000) * d * t ^ 20 + (365201889059 / 16588800000) * d * t ^ 22 + (473588749 / 6635520000) * d * t ^ 24 + (87830858641 / 8294400000) * d * t ^ 26 + (-17489899 / 1592524800) * d * t ^ 32 + (211075 / 48) * d ^ 2 * t ^ 2 + (-1516009 / 160) * d ^ 2 * t ^ 4 + (1430097317 / 345600) * d ^ 2 * t ^ 6 + (827945111173 / 414720000) * d ^ 2 * t ^ 8 + (-4308664933 / 8640000) * d ^ 2 * t ^ 10 + (-22423158107 / 46080000) * d ^ 2 * t ^ 12 + (-217278593 / 2880000) * d ^ 2 * t ^ 14 + (1734551549 / 552960000) * d ^ 2 * t ^ 16 + (223892593 / 331776000) * d ^ 2 * t ^ 18 + (6029167561 / 3317760000) * d ^ 2 * t ^ 20 + (-6359220199 / 6635520000) * d ^ 2 * t ^ 22 + (5965771 / 7962624000) * d ^ 2 * t ^ 24 + (15836407 / 5971968000) * d ^ 2 * t ^ 26 + (9025 / 382205952) * d ^ 2 * t ^ 32) * alpha_sq + ((-211075 / 12) * t ^ 2 + (6672061 / 160) * t ^ 4 + (-786688187 / 28800) * t ^ 6 + (148844356603 / 69120000) * t ^ 8 + (-55209173771 / 46080000) * t ^ 10 + (177348418951 / 92160000) * t ^ 12 + (164074843343 / 414720000) * t ^ 14 + (-39184304411 / 552960000) * t ^ 16 + (-8063 / 36000) * t ^ 18 + (-1074910063 / 414720000) * t ^ 20 + (92809073 / 552960000) * t ^ 22 + (8092979 / 663552000) * t ^ 24 + (77265887 / 497664000) * t ^ 26 + (-9025 / 31850496) * t ^ 32) * d_sq
#print axioms v39_00
#print axioms v39_11
#print axioms v39_22
#print axioms v39_33
#print axioms v39_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
theorem site40 : ((r ^ 2 * 1) : ℂ) = ((-1 / 2) + (1 / 2) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 4)) * alpha_sq
theorem phase40_00 : ((r ^ 2 * 1) : ℂ) ^ 0 * star ((r ^ 2 * 1) : ℂ) ^ 0 = (1) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase40_01 : ((r ^ 2 * 1) : ℂ) ^ 0 * star ((r ^ 2 * 1) : ℂ) ^ 1 = ((-1 / 2) + (-1 / 2) * alpha) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase40_02 : ((r ^ 2 * 1) : ℂ) ^ 0 * star ((r ^ 2 * 1) : ℂ) ^ 2 = ((-1 / 2) + (1 / 2) * alpha) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 4)) * alpha_sq
theorem phase40_03 : ((r ^ 2 * 1) : ℂ) ^ 0 * star ((r ^ 2 * 1) : ℂ) ^ 3 = (1) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-3 / 8) + (-1 / 8) * alpha) * alpha_sq
theorem phase40_04 : ((r ^ 2 * 1) : ℂ) ^ 0 * star ((r ^ 2 * 1) : ℂ) ^ 4 = ((-1 / 2) + (-1 / 2) * alpha) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((3 / 16) + (1 / 4) * alpha + (1 / 16) * alpha ^ 2) * alpha_sq
theorem phase40_10 : ((r ^ 2 * 1) : ℂ) ^ 1 * star ((r ^ 2 * 1) : ℂ) ^ 0 = ((-1 / 2) + (1 / 2) * alpha) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase40_11 : ((r ^ 2 * 1) : ℂ) ^ 1 * star ((r ^ 2 * 1) : ℂ) ^ 1 = (1) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 4)) * alpha_sq
theorem phase40_12 : ((r ^ 2 * 1) : ℂ) ^ 1 * star ((r ^ 2 * 1) : ℂ) ^ 2 = ((-1 / 2) + (-1 / 2) * alpha) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 8) + (1 / 8) * alpha) * alpha_sq
theorem phase40_13 : ((r ^ 2 * 1) : ℂ) ^ 1 * star ((r ^ 2 * 1) : ℂ) ^ 3 = ((-1 / 2) + (1 / 2) * alpha) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((3 / 16) + (-1 / 8) * alpha + (-1 / 16) * alpha ^ 2) * alpha_sq
theorem phase40_14 : ((r ^ 2 * 1) : ℂ) ^ 1 * star ((r ^ 2 * 1) : ℂ) ^ 4 = (1) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-11 / 32) + (-1 / 32) * alpha + (3 / 32) * alpha ^ 2 + (1 / 32) * alpha ^ 3) * alpha_sq
theorem phase40_20 : ((r ^ 2 * 1) : ℂ) ^ 2 * star ((r ^ 2 * 1) : ℂ) ^ 0 = ((-1 / 2) + (-1 / 2) * alpha) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 4)) * alpha_sq
theorem phase40_21 : ((r ^ 2 * 1) : ℂ) ^ 2 * star ((r ^ 2 * 1) : ℂ) ^ 1 = ((-1 / 2) + (1 / 2) * alpha) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 8) + (-1 / 8) * alpha) * alpha_sq
theorem phase40_22 : ((r ^ 2 * 1) : ℂ) ^ 2 * star ((r ^ 2 * 1) : ℂ) ^ 2 = (1) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-5 / 16) + (1 / 16) * alpha ^ 2) * alpha_sq
theorem phase40_23 : ((r ^ 2 * 1) : ℂ) ^ 2 * star ((r ^ 2 * 1) : ℂ) ^ 3 = ((-1 / 2) + (-1 / 2) * alpha) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((5 / 32) + (5 / 32) * alpha + (-1 / 32) * alpha ^ 2 + (-1 / 32) * alpha ^ 3) * alpha_sq
theorem phase40_24 : ((r ^ 2 * 1) : ℂ) ^ 2 * star ((r ^ 2 * 1) : ℂ) ^ 4 = ((-1 / 2) + (1 / 2) * alpha) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((11 / 64) + (-5 / 32) * alpha + (-1 / 16) * alpha ^ 2 + (1 / 32) * alpha ^ 3 + (1 / 64) * alpha ^ 4) * alpha_sq
theorem phase40_30 : ((r ^ 2 * 1) : ℂ) ^ 3 * star ((r ^ 2 * 1) : ℂ) ^ 0 = (1) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-3 / 8) + (1 / 8) * alpha) * alpha_sq
theorem phase40_31 : ((r ^ 2 * 1) : ℂ) ^ 3 * star ((r ^ 2 * 1) : ℂ) ^ 1 = ((-1 / 2) + (-1 / 2) * alpha) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((3 / 16) + (1 / 8) * alpha + (-1 / 16) * alpha ^ 2) * alpha_sq
theorem phase40_32 : ((r ^ 2 * 1) : ℂ) ^ 3 * star ((r ^ 2 * 1) : ℂ) ^ 2 = ((-1 / 2) + (1 / 2) * alpha) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((5 / 32) + (-5 / 32) * alpha + (-1 / 32) * alpha ^ 2 + (1 / 32) * alpha ^ 3) * alpha_sq
theorem phase40_33 : ((r ^ 2 * 1) : ℂ) ^ 3 * star ((r ^ 2 * 1) : ℂ) ^ 3 = (1) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-21 / 64) + (3 / 32) * alpha ^ 2 + (-1 / 64) * alpha ^ 4) * alpha_sq
theorem phase40_34 : ((r ^ 2 * 1) : ℂ) ^ 3 * star ((r ^ 2 * 1) : ℂ) ^ 4 = ((-1 / 2) + (-1 / 2) * alpha) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((21 / 128) + (21 / 128) * alpha + (-3 / 64) * alpha ^ 2 + (-3 / 64) * alpha ^ 3 + (1 / 128) * alpha ^ 4 + (1 / 128) * alpha ^ 5) * alpha_sq
theorem phase40_40 : ((r ^ 2 * 1) : ℂ) ^ 4 * star ((r ^ 2 * 1) : ℂ) ^ 0 = ((-1 / 2) + (1 / 2) * alpha) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((3 / 16) + (-1 / 4) * alpha + (1 / 16) * alpha ^ 2) * alpha_sq
theorem phase40_41 : ((r ^ 2 * 1) : ℂ) ^ 4 * star ((r ^ 2 * 1) : ℂ) ^ 1 = (1) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-11 / 32) + (1 / 32) * alpha + (3 / 32) * alpha ^ 2 + (-1 / 32) * alpha ^ 3) * alpha_sq
theorem phase40_42 : ((r ^ 2 * 1) : ℂ) ^ 4 * star ((r ^ 2 * 1) : ℂ) ^ 2 = ((-1 / 2) + (-1 / 2) * alpha) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((11 / 64) + (5 / 32) * alpha + (-1 / 16) * alpha ^ 2 + (-1 / 32) * alpha ^ 3 + (1 / 64) * alpha ^ 4) * alpha_sq
theorem phase40_43 : ((r ^ 2 * 1) : ℂ) ^ 4 * star ((r ^ 2 * 1) : ℂ) ^ 3 = ((-1 / 2) + (1 / 2) * alpha) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((21 / 128) + (-21 / 128) * alpha + (-3 / 64) * alpha ^ 2 + (3 / 64) * alpha ^ 3 + (1 / 128) * alpha ^ 4 + (-1 / 128) * alpha ^ 5) * alpha_sq
theorem phase40_44 : ((r ^ 2 * 1) : ℂ) ^ 4 * star ((r ^ 2 * 1) : ℂ) ^ 4 = (1) := by
  rw [site40]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-85 / 256) + (27 / 256) * alpha ^ 2 + (-7 / 256) * alpha ^ 4 + (1 / 256) * alpha ^ 6) * alpha_sq
noncomputable def z40 : Fin 40 → ℂ := Fin.snoc z39 (r ^ 2 * 1)
theorem v40_00 (t : ℂ) : (momentPoly 40 z40 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00]
  try simp only [phase40_00]
  try simp only [star_one, star_neg]
  ring
theorem v40_01 (t : ℂ) : (momentPoly 40 z40 0 1).eval t = 0 := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_01]
  try simp only [phase40_00, phase40_01]
  try simp only [star_one, star_neg]
  ring
theorem v40_02 (t : ℂ) : (momentPoly 40 z40 0 2).eval t = ((-453 / 40) * t ^ 2 + (453 / 40) * t ^ 4 + (49 / 120) * alpha * t ^ 2 + (-49 / 120) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_01, v39_02]
  try simp only [phase40_00, phase40_01, phase40_02]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 2) * t ^ 2) * alpha_sq
theorem v40_03 (t : ℂ) : (momentPoly 40 z40 0 3).eval t = (4 * t ^ 3 + (-6) * t ^ 5 + 2 * t ^ 9 + (1183 / 100) * alpha * t ^ 3 + (-3549 / 200) * alpha * t ^ 5 + (1183 / 200) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_01, v39_02, v39_03]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_03]
  try simp only [star_one, star_neg]
  linear_combination ((-169 / 80) * t ^ 3 + (169 / 80) * t ^ 5) * alpha_sq
theorem v40_04 (t : ℂ) : (momentPoly 40 z40 0 4).eval t = ((2547347 / 8000) * t ^ 4 + (-2547347 / 4000) * t ^ 6 + (5613477 / 16000) * t ^ 8 + (-518783 / 12000) * t ^ 10 + (518783 / 48000) * t ^ 16 + (-686009 / 24000) * alpha * t ^ 4 + (686009 / 12000) * alpha * t ^ 6 + (-1351919 / 48000) * alpha * t ^ 8 + (-20099 / 36000) * alpha * t ^ 10 + (20099 / 144000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_01, v39_02, v39_03, v39_04]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_03, phase40_04]
  try simp only [star_one, star_neg]
  linear_combination ((909 / 100) * t ^ 4 + (1393 / 200) * t ^ 6 + (-109 / 40) * t ^ 8 + (-1183 / 100) * t ^ 10) * alpha_sq
theorem v40_10 (t : ℂ) : (momentPoly 40 z40 1 0).eval t = 0 := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_10]
  try simp only [phase40_00, phase40_10]
  try simp only [star_one, star_neg]
  ring
theorem v40_11 (t : ℂ) : (momentPoly 40 z40 1 1).eval t = (40 + (-40) * t ^ 2) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_01, v39_10, v39_11]
  try simp only [phase40_00, phase40_01, phase40_10, phase40_11]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 2) * t ^ 2) * alpha_sq
theorem v40_12 (t : ℂ) : (momentPoly 40 z40 1 2).eval t = 0 := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_01, v39_02, v39_10, v39_11, v39_12]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_10, phase40_11, phase40_12]
  try simp only [star_one, star_neg]
  linear_combination ((169 / 240) * t ^ 3 + (-169 / 240) * t ^ 5) * alpha_sq
theorem v40_13 (t : ℂ) : (momentPoly 40 z40 1 3).eval t = ((-53001 / 40) * t ^ 2 + (13137 / 5) * t ^ 4 + (-25821 / 20) * t ^ 6 + (-453 / 40) * t ^ 10 + (1911 / 40) * alpha * t ^ 2 + (-1421 / 15) * alpha * t ^ 4 + (931 / 20) * alpha * t ^ 6 + (49 / 120) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_01, v39_02, v39_03, v39_10, v39_11, v39_12, v39_13]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_03, phase40_10, phase40_11, phase40_12, phase40_13]
  try simp only [star_one, star_neg]
  linear_combination ((-117 / 2) * t ^ 2 + (17771 / 400) * t ^ 4 + (1923 / 200) * t ^ 6 + (1183 / 400) * t ^ 10) * alpha_sq
theorem v40_14 (t : ℂ) : (momentPoly 40 z40 1 4).eval t = (616 * t ^ 3 + (-1524) * t ^ 5 + 888 * t ^ 7 + 326 * t ^ 9 + (-304) * t ^ 11 + (-2) * t ^ 17 + (91091 / 50) * alpha * t ^ 3 + (-450723 / 100) * alpha * t ^ 5 + (131313 / 50) * alpha * t ^ 7 + (192829 / 200) * alpha * t ^ 9 + (-22477 / 25) * alpha * t ^ 11 + (-1183 / 200) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_01, v39_02, v39_03, v39_04, v39_10, v39_11, v39_12, v39_13, v39_14]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_03, phase40_04, phase40_10, phase40_11, phase40_12, phase40_13, phase40_14]
  try simp only [star_one, star_neg]
  linear_combination ((-13013 / 40) * t ^ 3 + (9357597 / 16000) * t ^ 5 + (-4925191 / 24000) * t ^ 7 + (-5163119 / 96000) * t ^ 9 + (-78899 / 72000) * t ^ 11 + (164099 / 288000) * t ^ 17) * alpha_sq
theorem v40_20 (t : ℂ) : (momentPoly 40 z40 2 0).eval t = ((-453 / 40) * t ^ 2 + (453 / 40) * t ^ 4 + (-49 / 120) * alpha * t ^ 2 + (49 / 120) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_10, v39_20]
  try simp only [phase40_00, phase40_10, phase40_20]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 2) * t ^ 2) * alpha_sq
theorem v40_21 (t : ℂ) : (momentPoly 40 z40 2 1).eval t = 0 := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_01, v39_10, v39_11, v39_20, v39_21]
  try simp only [phase40_00, phase40_01, phase40_10, phase40_11, phase40_20, phase40_21]
  try simp only [star_one, star_neg]
  linear_combination ((169 / 240) * t ^ 3 + (-169 / 240) * t ^ 5) * alpha_sq
theorem v40_22 (t : ℂ) : (momentPoly 40 z40 2 2).eval t = (3160 + (-6240) * t ^ 2 + (3706507 / 1200) * t ^ 4 + (-58507 / 600) * t ^ 6 + (106507 / 1200) * t ^ 8) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_01, v39_02, v39_10, v39_11, v39_12, v39_20, v39_21, v39_22]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_10, phase40_11, phase40_12, phase40_20, phase40_21, phase40_22]
  try simp only [star_one, star_neg]
  linear_combination (78 * t ^ 2 + (-934 / 15) * t ^ 4 + (-1817 / 120) * t ^ 6 + (109 / 120) * t ^ 8) * alpha_sq
theorem v40_23 (t : ℂ) : (momentPoly 40 z40 2 3).eval t = ((-123233 / 4000) * t ^ 5 + (123233 / 1600) * t ^ 7 + (-369699 / 8000) * t ^ 9 + (-123233 / 8000) * t ^ 11 + (123233 / 8000) * t ^ 13 + (-1627297 / 12000) * alpha * t ^ 5 + (1627297 / 4800) * alpha * t ^ 7 + (-1627297 / 8000) * alpha * t ^ 9 + (-1627297 / 24000) * alpha * t ^ 11 + (1627297 / 24000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_01, v39_02, v39_03, v39_10, v39_11, v39_12, v39_13, v39_20, v39_21, v39_22, v39_23]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_03, phase40_10, phase40_11, phase40_12, phase40_13, phase40_20, phase40_21, phase40_22, phase40_23]
  try simp only [star_one, star_neg]
  linear_combination ((13013 / 80) * t ^ 3 + (-374707 / 1200) * t ^ 5 + (691 / 5) * t ^ 7 + (2197 / 200) * t ^ 9 + (4039 / 1200) * t ^ 11 + (-1183 / 400) * t ^ 13) * alpha_sq
theorem v40_24 (t : ℂ) : (momentPoly 40 z40 2 4).eval t = ((-4081983 / 20) * t ^ 2 + (24003111 / 40) * t ^ 4 + (-278548849507 / 480000) * t ^ 6 + (29014705507 / 160000) * t ^ 8 + (-349881133 / 192000) * t ^ 10 + (14972713403 / 2880000) * t ^ 12 + (-286788623 / 720000) * t ^ 14 + (-286788623 / 2880000) * t ^ 18 + (319404623 / 2880000) * t ^ 20 + (441539 / 60) * alpha * t ^ 2 + (-2596363 / 120) * alpha * t ^ 4 + (3357763679 / 160000) * alpha * t ^ 6 + (-1076107037 / 160000) * alpha * t ^ 8 + (42570323 / 192000) * alpha * t ^ 10 + (-509899973 / 2880000) * alpha * t ^ 12 + (-19614607 / 720000) * alpha * t ^ 14 + (-19614607 / 2880000) * alpha * t ^ 18 + (18438607 / 2880000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_01, v39_02, v39_03, v39_04, v39_10, v39_11, v39_12, v39_13, v39_14, v39_20, v39_21, v39_22, v39_23, v39_24]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_03, phase40_04, phase40_10, phase40_11, phase40_12, phase40_13, phase40_14, phase40_20, phase40_21, phase40_22, phase40_23, phase40_24]
  try simp only [star_one, star_neg]
  linear_combination ((-9011) * t ^ 2 + (337649 / 25) * t ^ 4 + (-14183139 / 8000) * t ^ 6 + (-123487751 / 48000) * t ^ 8 + (33680371 / 48000) * t ^ 10 + (-40200151 / 57600) * t ^ 12 + (-10536643 / 72000) * t ^ 14 + (-303697 / 28800) * t ^ 18 + (-222899 / 288000) * t ^ 20) * alpha_sq
theorem v40_30 (t : ℂ) : (momentPoly 40 z40 3 0).eval t = (4 * t ^ 3 + (-6) * t ^ 5 + 2 * t ^ 9 + (-1183 / 100) * alpha * t ^ 3 + (3549 / 200) * alpha * t ^ 5 + (-1183 / 200) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_10, v39_20, v39_30]
  try simp only [phase40_00, phase40_10, phase40_20, phase40_30]
  try simp only [star_one, star_neg]
  linear_combination ((-169 / 80) * t ^ 3 + (169 / 80) * t ^ 5) * alpha_sq
theorem v40_31 (t : ℂ) : (momentPoly 40 z40 3 1).eval t = ((-53001 / 40) * t ^ 2 + (13137 / 5) * t ^ 4 + (-25821 / 20) * t ^ 6 + (-453 / 40) * t ^ 10 + (-1911 / 40) * alpha * t ^ 2 + (1421 / 15) * alpha * t ^ 4 + (-931 / 20) * alpha * t ^ 6 + (-49 / 120) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_01, v39_10, v39_11, v39_20, v39_21, v39_30, v39_31]
  try simp only [phase40_00, phase40_01, phase40_10, phase40_11, phase40_20, phase40_21, phase40_30, phase40_31]
  try simp only [star_one, star_neg]
  linear_combination ((-117 / 2) * t ^ 2 + (17771 / 400) * t ^ 4 + (1923 / 200) * t ^ 6 + (1183 / 400) * t ^ 10) * alpha_sq
theorem v40_32 (t : ℂ) : (momentPoly 40 z40 3 2).eval t = ((-123233 / 4000) * t ^ 5 + (123233 / 1600) * t ^ 7 + (-369699 / 8000) * t ^ 9 + (-123233 / 8000) * t ^ 11 + (123233 / 8000) * t ^ 13 + (1627297 / 12000) * alpha * t ^ 5 + (-1627297 / 4800) * alpha * t ^ 7 + (1627297 / 8000) * alpha * t ^ 9 + (1627297 / 24000) * alpha * t ^ 11 + (-1627297 / 24000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_01, v39_02, v39_10, v39_11, v39_12, v39_20, v39_21, v39_22, v39_30, v39_31, v39_32]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_10, phase40_11, phase40_12, phase40_20, phase40_21, phase40_22, phase40_30, phase40_31, phase40_32]
  try simp only [star_one, star_neg]
  linear_combination ((13013 / 80) * t ^ 3 + (-374707 / 1200) * t ^ 5 + (691 / 5) * t ^ 7 + (2197 / 200) * t ^ 9 + (4039 / 1200) * t ^ 11 + (-1183 / 400) * t ^ 13) * alpha_sq
theorem v40_33 (t : ℂ) : (momentPoly 40 z40 3 3).eval t = (369760 + (-1081320) * t ^ 2 + (211270899 / 200) * t ^ 4 + (-3773225683 / 10000) * t ^ 6 + (611732699 / 10000) * t ^ 8 + (-1139849397 / 40000) * t ^ 10 + (7283817 / 10000) * t ^ 12 + (-18926101 / 20000) * t ^ 14 + (2758467 / 40000) * t ^ 18) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_01, v39_02, v39_03, v39_10, v39_11, v39_12, v39_13, v39_20, v39_21, v39_22, v39_23, v39_30, v39_31, v39_32, v39_33]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_03, phase40_10, phase40_11, phase40_12, phase40_13, phase40_20, phase40_21, phase40_22, phase40_23, phase40_30, phase40_31, phase40_32, phase40_33]
  try simp only [star_one, star_neg]
  linear_combination ((27033 / 2) * t ^ 2 + (-106476 / 5) * t ^ 4 + (1276281 / 500) * t ^ 6 + (8936949 / 1600) * t ^ 8 + (-2993481 / 8000) * t ^ 10 + (-1453857 / 8000) * t ^ 12 + (1607697 / 8000) * t ^ 14) * alpha_sq
theorem v40_34 (t : ℂ) : (momentPoly 40 z40 3 4).eval t = ((-1109097 / 80) * t ^ 5 + (38532853153 / 800000) * t ^ 7 + (-87074019471 / 1600000) * t ^ 9 + (21188699341 / 1600000) * t ^ 11 + (5096416831 / 384000) * t ^ 13 + (-1287971459 / 200000) * t ^ 15 + (646070623 / 3200000) * t ^ 17 + (-305230117 / 4800000) * t ^ 19 + (-379169917 / 3200000) * t ^ 21 + (231290317 / 9600000) * t ^ 25 + (-4881891 / 80) * alpha * t ^ 5 + (165591476299 / 800000) * alpha * t ^ 7 + (-1065441388879 / 4800000) * alpha * t ^ 9 + (178482084109 / 4800000) * alpha * t ^ 11 + (76407474431 / 1152000) * alpha * t ^ 13 + (-15216164291 / 600000) * alpha * t ^ 15 + (-20462997473 / 9600000) * alpha * t ^ 17 + (856743067 / 14400000) * alpha * t ^ 19 + (-119635133 / 9600000) * alpha * t ^ 21 + (-1833121267 / 28800000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_01, v39_02, v39_03, v39_04, v39_10, v39_11, v39_12, v39_13, v39_14, v39_20, v39_21, v39_22, v39_23, v39_24, v39_30, v39_31, v39_32, v39_33, v39_34]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_03, phase40_04, phase40_10, phase40_11, phase40_12, phase40_13, phase40_14, phase40_20, phase40_21, phase40_22, phase40_23, phase40_24, phase40_30, phase40_31, phase40_32, phase40_33, phase40_34]
  try simp only [star_one, star_neg]
  linear_combination ((1483989 / 40) * t ^ 3 + (-8354183 / 80) * t ^ 5 + (29452325117 / 320000) * t ^ 7 + (-6231716051 / 320000) * t ^ 9 + (-484486349 / 128000) * t ^ 11 + (-5306985073 / 1920000) * t ^ 13 + (731589593 / 480000) * t ^ 15 + (-1688477 / 8000) * t ^ 17 + (-92317967 / 1920000) * t ^ 19 + (85061587 / 1920000) * t ^ 21 + (1183 / 400) * t ^ 25) * alpha_sq
theorem v40_40 (t : ℂ) : (momentPoly 40 z40 4 0).eval t = ((2547347 / 8000) * t ^ 4 + (-2547347 / 4000) * t ^ 6 + (5613477 / 16000) * t ^ 8 + (-518783 / 12000) * t ^ 10 + (518783 / 48000) * t ^ 16 + (686009 / 24000) * alpha * t ^ 4 + (-686009 / 12000) * alpha * t ^ 6 + (1351919 / 48000) * alpha * t ^ 8 + (20099 / 36000) * alpha * t ^ 10 + (-20099 / 144000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_10, v39_20, v39_30, v39_40]
  try simp only [phase40_00, phase40_10, phase40_20, phase40_30, phase40_40]
  try simp only [star_one, star_neg]
  linear_combination ((909 / 100) * t ^ 4 + (1393 / 200) * t ^ 6 + (-109 / 40) * t ^ 8 + (-1183 / 100) * t ^ 10) * alpha_sq
theorem v40_41 (t : ℂ) : (momentPoly 40 z40 4 1).eval t = (616 * t ^ 3 + (-1524) * t ^ 5 + 888 * t ^ 7 + 326 * t ^ 9 + (-304) * t ^ 11 + (-2) * t ^ 17 + (-91091 / 50) * alpha * t ^ 3 + (450723 / 100) * alpha * t ^ 5 + (-131313 / 50) * alpha * t ^ 7 + (-192829 / 200) * alpha * t ^ 9 + (22477 / 25) * alpha * t ^ 11 + (1183 / 200) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_01, v39_10, v39_11, v39_20, v39_21, v39_30, v39_31, v39_40, v39_41]
  try simp only [phase40_00, phase40_01, phase40_10, phase40_11, phase40_20, phase40_21, phase40_30, phase40_31, phase40_40, phase40_41]
  try simp only [star_one, star_neg]
  linear_combination ((-13013 / 40) * t ^ 3 + (9357597 / 16000) * t ^ 5 + (-4925191 / 24000) * t ^ 7 + (-5163119 / 96000) * t ^ 9 + (-78899 / 72000) * t ^ 11 + (164099 / 288000) * t ^ 17) * alpha_sq
theorem v40_42 (t : ℂ) : (momentPoly 40 z40 4 2).eval t = ((-4081983 / 20) * t ^ 2 + (24003111 / 40) * t ^ 4 + (-278548849507 / 480000) * t ^ 6 + (29014705507 / 160000) * t ^ 8 + (-349881133 / 192000) * t ^ 10 + (14972713403 / 2880000) * t ^ 12 + (-286788623 / 720000) * t ^ 14 + (-286788623 / 2880000) * t ^ 18 + (319404623 / 2880000) * t ^ 20 + (-441539 / 60) * alpha * t ^ 2 + (2596363 / 120) * alpha * t ^ 4 + (-3357763679 / 160000) * alpha * t ^ 6 + (1076107037 / 160000) * alpha * t ^ 8 + (-42570323 / 192000) * alpha * t ^ 10 + (509899973 / 2880000) * alpha * t ^ 12 + (19614607 / 720000) * alpha * t ^ 14 + (19614607 / 2880000) * alpha * t ^ 18 + (-18438607 / 2880000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_01, v39_02, v39_10, v39_11, v39_12, v39_20, v39_21, v39_22, v39_30, v39_31, v39_32, v39_40, v39_41, v39_42]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_10, phase40_11, phase40_12, phase40_20, phase40_21, phase40_22, phase40_30, phase40_31, phase40_32, phase40_40, phase40_41, phase40_42]
  try simp only [star_one, star_neg]
  linear_combination ((-9011) * t ^ 2 + (337649 / 25) * t ^ 4 + (-14183139 / 8000) * t ^ 6 + (-123487751 / 48000) * t ^ 8 + (33680371 / 48000) * t ^ 10 + (-40200151 / 57600) * t ^ 12 + (-10536643 / 72000) * t ^ 14 + (-303697 / 28800) * t ^ 18 + (-222899 / 288000) * t ^ 20) * alpha_sq
theorem v40_43 (t : ℂ) : (momentPoly 40 z40 4 3).eval t = ((-1109097 / 80) * t ^ 5 + (38532853153 / 800000) * t ^ 7 + (-87074019471 / 1600000) * t ^ 9 + (21188699341 / 1600000) * t ^ 11 + (5096416831 / 384000) * t ^ 13 + (-1287971459 / 200000) * t ^ 15 + (646070623 / 3200000) * t ^ 17 + (-305230117 / 4800000) * t ^ 19 + (-379169917 / 3200000) * t ^ 21 + (231290317 / 9600000) * t ^ 25 + (4881891 / 80) * alpha * t ^ 5 + (-165591476299 / 800000) * alpha * t ^ 7 + (1065441388879 / 4800000) * alpha * t ^ 9 + (-178482084109 / 4800000) * alpha * t ^ 11 + (-76407474431 / 1152000) * alpha * t ^ 13 + (15216164291 / 600000) * alpha * t ^ 15 + (20462997473 / 9600000) * alpha * t ^ 17 + (-856743067 / 14400000) * alpha * t ^ 19 + (119635133 / 9600000) * alpha * t ^ 21 + (1833121267 / 28800000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_01, v39_02, v39_03, v39_10, v39_11, v39_12, v39_13, v39_20, v39_21, v39_22, v39_23, v39_30, v39_31, v39_32, v39_33, v39_40, v39_41, v39_42, v39_43]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_03, phase40_10, phase40_11, phase40_12, phase40_13, phase40_20, phase40_21, phase40_22, phase40_23, phase40_30, phase40_31, phase40_32, phase40_33, phase40_40, phase40_41, phase40_42, phase40_43]
  try simp only [star_one, star_neg]
  linear_combination ((1483989 / 40) * t ^ 3 + (-8354183 / 80) * t ^ 5 + (29452325117 / 320000) * t ^ 7 + (-6231716051 / 320000) * t ^ 9 + (-484486349 / 128000) * t ^ 11 + (-5306985073 / 1920000) * t ^ 13 + (731589593 / 480000) * t ^ 15 + (-1688477 / 8000) * t ^ 17 + (-92317967 / 1920000) * t ^ 19 + (85061587 / 1920000) * t ^ 21 + (1183 / 400) * t ^ 25) * alpha_sq
theorem v40_44 (t : ℂ) : (momentPoly 40 z40 4 4).eval t = (56961880 + (-219271360) * t ^ 2 + (15852730439 / 50) * t ^ 4 + (-534111653159 / 2500) * t ^ 6 + (3652934173383227 / 48000000) * t ^ 8 + (-294336506005627 / 12000000) * t ^ 10 + (71442547477333 / 9600000) * t ^ 12 + (-47537887465477 / 72000000) * t ^ 14 + (320310293581057 / 576000000) * t ^ 16 + (1733060804527 / 72000000) * t ^ 18 + (-14310623752223 / 432000000) * t ^ 20 + (-673032320903 / 72000000) * t ^ 22 + (1870599113873 / 288000000) * t ^ 24 + (-251998617667 / 216000000) * t ^ 26 + (132832843267 / 1728000000) * t ^ 32) := by
  rw [momentPoly]
  simp only [z40, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v39_00, v39_01, v39_02, v39_03, v39_04, v39_10, v39_11, v39_12, v39_13, v39_14, v39_20, v39_21, v39_22, v39_23, v39_24, v39_30, v39_31, v39_32, v39_33, v39_34, v39_40, v39_41, v39_42, v39_43, v39_44]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_03, phase40_04, phase40_10, phase40_11, phase40_12, phase40_13, phase40_14, phase40_20, phase40_21, phase40_22, phase40_23, phase40_24, phase40_30, phase40_31, phase40_32, phase40_33, phase40_34, phase40_40, phase40_41, phase40_42, phase40_43, phase40_44]
  try simp only [star_one, star_neg]
  linear_combination (2740892 * t ^ 2 + (-31957744 / 5) * t ^ 4 + (1511021527 / 500) * t ^ 6 + (1347117168737 / 600000) * t ^ 8 + (-1009364339537 / 600000) * t ^ 10 + (-34942691953 / 600000) * t ^ 12 + (82495131889 / 360000) * t ^ 14 + (-231395163031 / 2400000) * t ^ 16 + (-22328686333 / 2400000) * t ^ 18 + (511161253 / 400000) * t ^ 20 + (-134077663 / 400000) * t ^ 22 + (-85834277 / 480000) * t ^ 24 + (-613720289 / 2400000) * t ^ 26 + (92099 / 144000) * t ^ 32) * alpha_sq
#print axioms v40_00
#print axioms v40_11
#print axioms v40_22
#print axioms v40_33
#print axioms v40_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
noncomputable def z41 : Fin 41 → ℂ := Fin.snoc z40 (r ^ 2 * 1)
theorem v41_00 (t : ℂ) : (momentPoly 41 z41 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00]
  try simp only [phase40_00]
  try simp only [star_one, star_neg]
  ring
theorem v41_01 (t : ℂ) : (momentPoly 41 z41 0 1).eval t = ((-1 / 2) * t + (-1 / 2) * alpha * t) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_01]
  try simp only [phase40_00, phase40_01]
  try simp only [star_one, star_neg]
  ring
theorem v41_02 (t : ℂ) : (momentPoly 41 z41 0 2).eval t = ((-453 / 40) * t ^ 2 + (433 / 40) * t ^ 4 + (49 / 120) * alpha * t ^ 2 + (11 / 120) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_01, v40_02]
  try simp only [phase40_00, phase40_01, phase40_02]
  try simp only [star_one, star_neg]
  ring
theorem v41_03 (t : ℂ) : (momentPoly 41 z41 0 3).eval t = ((913 / 40) * t ^ 3 + (-993 / 40) * t ^ 5 + 3 * t ^ 9 + (5641 / 200) * alpha * t ^ 3 + (-853 / 25) * alpha * t ^ 5 + (1183 / 200) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_01, v40_02, v40_03]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_03]
  try simp only [star_one, star_neg]
  linear_combination ((-49 / 80) * t ^ 3 + (49 / 80) * t ^ 5) * alpha_sq
theorem v41_04 (t : ℂ) : (momentPoly 41 z41 0 4).eval t = ((3051187 / 8000) * t ^ 4 + (-2804027 / 4000) * t ^ 6 + (5128677 / 16000) * t ^ 8 + (-140903 / 12000) * t ^ 10 + (494783 / 48000) * t ^ 16 + (-1445849 / 24000) * alpha * t ^ 4 + (833489 / 12000) * alpha * t ^ 6 + (337681 / 48000) * alpha * t ^ 8 + (-589979 / 36000) * alpha * t ^ 10 + (-51901 / 144000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_01, v40_02, v40_03, v40_04]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_03, phase40_04]
  try simp only [star_one, star_neg]
  linear_combination ((-1183 / 50) * t ^ 4 + (7343 / 200) * t ^ 6 + (-49 / 40) * t ^ 8 + (-1183 / 100) * t ^ 10) * alpha_sq
theorem v41_10 (t : ℂ) : (momentPoly 41 z41 1 0).eval t = ((-1 / 2) * t + (1 / 2) * alpha * t) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_10]
  try simp only [phase40_00, phase40_10]
  try simp only [star_one, star_neg]
  ring
theorem v41_11 (t : ℂ) : (momentPoly 41 z41 1 1).eval t = (41 + (-40) * t ^ 2) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_01, v40_10, v40_11]
  try simp only [phase40_00, phase40_01, phase40_10, phase40_11]
  try simp only [star_one, star_neg]
  ring
theorem v41_12 (t : ℂ) : (momentPoly 41 z41 1 2).eval t = ((-81 / 2) * t + (901 / 20) * t ^ 3 + (-101 / 20) * t ^ 5 + (-81 / 2) * alpha * t + (512 / 15) * alpha * t ^ 3 + (88 / 15) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_01, v40_02, v40_10, v40_11, v40_12]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_10, phase40_11, phase40_12]
  try simp only [star_one, star_neg]
  linear_combination ((49 / 240) * t ^ 3 + (-49 / 240) * t ^ 5) * alpha_sq
theorem v41_13 (t : ℂ) : (momentPoly 41 z41 1 3).eval t = ((-1359) * t ^ 2 + (258113 / 100) * t ^ 4 + (-480573 / 400) * t ^ 6 + (-8479 / 400) * t ^ 10 + 49 * alpha * t ^ 2 + (-2953 / 75) * alpha * t ^ 4 + (-3031 / 400) * alpha * t ^ 6 + (-1859 / 1200) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_01, v40_02, v40_03, v40_10, v40_11, v40_12, v40_13]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_03, phase40_10, phase40_11, phase40_12, phase40_13]
  try simp only [star_one, star_neg]
  linear_combination ((1183 / 200) * t ^ 4 + (-3549 / 400) * t ^ 6 + (1183 / 400) * t ^ 10) * alpha_sq
theorem v41_14 (t : ℂ) : (momentPoly 41 z41 1 4).eval t = ((72127 / 20) * t ^ 3 + (-60201469 / 8000) * t ^ 5 + (15928269 / 4000) * t ^ 7 + (5789221 / 16000) * t ^ 9 + (-4997359 / 12000) * t ^ 11 + (-365441 / 48000) * t ^ 17 + (445639 / 100) * alpha * t ^ 3 + (-45613403 / 4800) * alpha * t ^ 5 + (11443819 / 2400) * alpha * t ^ 7 + (11302163 / 9600) * alpha * t ^ 9 + (-6469801 / 7200) * alpha * t ^ 11 + (-16727 / 28800) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_01, v40_02, v40_03, v40_04, v40_10, v40_11, v40_12, v40_13, v40_14]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_03, phase40_04, phase40_10, phase40_11, phase40_12, phase40_13, phase40_14]
  try simp only [star_one, star_neg]
  linear_combination ((-3871 / 40) * t ^ 3 + (2822397 / 16000) * t ^ 5 + (-1548391 / 24000) * t ^ 7 + (-1351919 / 96000) * t ^ 9 + (-78899 / 72000) * t ^ 11 + (20099 / 288000) * t ^ 17) * alpha_sq
theorem v41_20 (t : ℂ) : (momentPoly 41 z41 2 0).eval t = ((-453 / 40) * t ^ 2 + (433 / 40) * t ^ 4 + (-49 / 120) * alpha * t ^ 2 + (-11 / 120) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_10, v40_20]
  try simp only [phase40_00, phase40_10, phase40_20]
  try simp only [star_one, star_neg]
  ring
theorem v41_21 (t : ℂ) : (momentPoly 41 z41 2 1).eval t = ((-81 / 2) * t + (901 / 20) * t ^ 3 + (-101 / 20) * t ^ 5 + (81 / 2) * alpha * t + (-512 / 15) * alpha * t ^ 3 + (-88 / 15) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_01, v40_10, v40_11, v40_20, v40_21]
  try simp only [phase40_00, phase40_01, phase40_10, phase40_11, phase40_20, phase40_21]
  try simp only [star_one, star_neg]
  linear_combination ((49 / 240) * t ^ 3 + (-49 / 240) * t ^ 5) * alpha_sq
theorem v41_22 (t : ℂ) : (momentPoly 41 z41 2 2).eval t = (3321 + (-6400) * t ^ 2 + (3706507 / 1200) * t ^ 4 + (-50977 / 600) * t ^ 6 + (91447 / 1200) * t ^ 8) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_01, v40_02, v40_10, v40_11, v40_12, v40_20, v40_21, v40_22]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_10, phase40_11, phase40_12, phase40_20, phase40_21, phase40_22]
  try simp only [star_one, star_neg]
  linear_combination ((-49 / 120) * t ^ 6 + (49 / 120) * t ^ 8) * alpha_sq
theorem v41_23 (t : ℂ) : (momentPoly 41 z41 2 3).eval t = ((-9721 / 2) * t + (213537 / 20) * t ^ 3 + (-1755573 / 250) * t ^ 5 + (2224693 / 1600) * t ^ 7 + (-1623709 / 8000) * t ^ 9 + (-133033 / 8000) * t ^ 11 + (276813 / 8000) * t ^ 13 + (-9721 / 2) * alpha * t + (40448 / 5) * alpha * t ^ 3 + (-4058017 / 2000) * alpha * t ^ 5 + (-4129091 / 4800) * alpha * t ^ 7 + (-2597387 / 8000) * alpha * t ^ 9 + (-1918697 / 24000) * alpha * t ^ 11 + (514039 / 8000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_01, v40_02, v40_03, v40_10, v40_11, v40_12, v40_13, v40_20, v40_21, v40_22, v40_23]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_03, phase40_10, phase40_11, phase40_12, phase40_13, phase40_20, phase40_21, phase40_22, phase40_23]
  try simp only [star_one, star_neg]
  linear_combination ((3871 / 80) * t ^ 3 + (-22883 / 240) * t ^ 5 + (8127 / 200) * t ^ 7 + (3549 / 400) * t ^ 9 + (49 / 120) * t ^ 11 + (-1183 / 400) * t ^ 13) * alpha_sq
theorem v41_24 (t : ℂ) : (momentPoly 41 z41 2 4).eval t = ((-2147673 / 10) * t ^ 2 + (121072797 / 200) * t ^ 4 + (-267526260067 / 480000) * t ^ 6 + (26397897147 / 160000) * t ^ 8 + (-215123177 / 38400) * t ^ 10 + (21139622483 / 2880000) * t ^ 12 + (-1096583 / 720000) * t ^ 14 + (-215379023 / 2880000) * t ^ 18 + (289900103 / 2880000) * t ^ 20 + (232309 / 30) * alpha * t ^ 2 + (-2795531 / 200) * alpha * t ^ 4 + (2792628317 / 480000) * alpha * t ^ 6 + (-27945677 / 160000) * alpha * t ^ 8 + (4835889 / 64000) * alpha * t ^ 10 + (1985404507 / 2880000) * alpha * t ^ 12 + (-123669887 / 720000) * alpha * t ^ 14 + (8556593 / 2880000) * alpha * t ^ 18 + (-14221873 / 2880000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_01, v40_02, v40_03, v40_04, v40_10, v40_11, v40_12, v40_13, v40_14, v40_20, v40_21, v40_22, v40_23, v40_24]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_03, phase40_04, phase40_10, phase40_11, phase40_12, phase40_13, phase40_14, phase40_20, phase40_21, phase40_22, phase40_23, phase40_24]
  try simp only [star_one, star_neg]
  linear_combination ((46137 / 25) * t ^ 4 + (-25629023 / 6000) * t ^ 6 + (31400183 / 16000) * t ^ 8 + (32501173 / 24000) * t ^ 10 + (-14388277 / 19200) * t ^ 12 + (-9743683 / 72000) * t ^ 14 + (-6853 / 1200) * t ^ 18 + (-78899 / 288000) * t ^ 20) * alpha_sq
theorem v41_30 (t : ℂ) : (momentPoly 41 z41 3 0).eval t = ((913 / 40) * t ^ 3 + (-993 / 40) * t ^ 5 + 3 * t ^ 9 + (-5641 / 200) * alpha * t ^ 3 + (853 / 25) * alpha * t ^ 5 + (-1183 / 200) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_10, v40_20, v40_30]
  try simp only [phase40_00, phase40_10, phase40_20, phase40_30]
  try simp only [star_one, star_neg]
  linear_combination ((-49 / 80) * t ^ 3 + (49 / 80) * t ^ 5) * alpha_sq
theorem v41_31 (t : ℂ) : (momentPoly 41 z41 3 1).eval t = ((-1359) * t ^ 2 + (258113 / 100) * t ^ 4 + (-480573 / 400) * t ^ 6 + (-8479 / 400) * t ^ 10 + (-49) * alpha * t ^ 2 + (2953 / 75) * alpha * t ^ 4 + (3031 / 400) * alpha * t ^ 6 + (1859 / 1200) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_01, v40_10, v40_11, v40_20, v40_21, v40_30, v40_31]
  try simp only [phase40_00, phase40_01, phase40_10, phase40_11, phase40_20, phase40_21, phase40_30, phase40_31]
  try simp only [star_one, star_neg]
  linear_combination ((1183 / 200) * t ^ 4 + (-3549 / 400) * t ^ 6 + (1183 / 400) * t ^ 10) * alpha_sq
theorem v41_32 (t : ℂ) : (momentPoly 41 z41 3 2).eval t = ((-9721 / 2) * t + (213537 / 20) * t ^ 3 + (-1755573 / 250) * t ^ 5 + (2224693 / 1600) * t ^ 7 + (-1623709 / 8000) * t ^ 9 + (-133033 / 8000) * t ^ 11 + (276813 / 8000) * t ^ 13 + (9721 / 2) * alpha * t + (-40448 / 5) * alpha * t ^ 3 + (4058017 / 2000) * alpha * t ^ 5 + (4129091 / 4800) * alpha * t ^ 7 + (2597387 / 8000) * alpha * t ^ 9 + (1918697 / 24000) * alpha * t ^ 11 + (-514039 / 8000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_01, v40_02, v40_10, v40_11, v40_12, v40_20, v40_21, v40_22, v40_30, v40_31, v40_32]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_10, phase40_11, phase40_12, phase40_20, phase40_21, phase40_22, phase40_30, phase40_31, phase40_32]
  try simp only [star_one, star_neg]
  linear_combination ((3871 / 80) * t ^ 3 + (-22883 / 240) * t ^ 5 + (8127 / 200) * t ^ 7 + (3549 / 400) * t ^ 9 + (49 / 120) * t ^ 11 + (-1183 / 400) * t ^ 13) * alpha_sq
theorem v41_33 (t : ℂ) : (momentPoly 41 z41 3 3).eval t = (398561 + (-1137840) * t ^ 2 + (433661319 / 400) * t ^ 4 + (-1862222879 / 5000) * t ^ 6 + (998347573 / 20000) * t ^ 8 + (-889391547 / 40000) * t ^ 10 + (27856609 / 20000) * t ^ 12 + (-7885519 / 5000) * t ^ 14 + (2918467 / 40000) * t ^ 18) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_01, v40_02, v40_03, v40_10, v40_11, v40_12, v40_13, v40_20, v40_21, v40_22, v40_23, v40_30, v40_31, v40_32, v40_33]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_03, phase40_10, phase40_11, phase40_12, phase40_13, phase40_20, phase40_21, phase40_22, phase40_23, phase40_30, phase40_31, phase40_32, phase40_33]
  try simp only [star_one, star_neg]
  linear_combination ((-2205497 / 4000) * t ^ 6 + (2083977 / 1600) * t ^ 8 + (-5999091 / 8000) * t ^ 10 + (-1627297 / 8000) * t ^ 12 + (1617497 / 8000) * t ^ 14) * alpha_sq
theorem v41_34 (t : ℂ) : (momentPoly 41 z41 3 4).eval t = ((-1536401 / 2) * t + (12495969 / 5) * t ^ 3 + (-1485791877 / 500) * t ^ 5 + (1275909341423 / 800000) * t ^ 7 + (-702540095491 / 1600000) * t ^ 9 + (127710522951 / 1600000) * t ^ 11 + (11551679541 / 640000) * t ^ 13 + (-2067315053 / 150000) * t ^ 15 + (3573642823 / 3200000) * t ^ 17 + (-622910287 / 4800000) * t ^ 19 + (-2953511971 / 9600000) * t ^ 21 + (240270917 / 9600000) * t ^ 25 + (-1536401 / 2) * alpha * t + (9467904 / 5) * alpha * t ^ 3 + (-1254219527 / 1000) * alpha * t ^ 5 + (42337720219 / 800000) * alpha * t ^ 7 + (-272912593039 / 4800000) * alpha * t ^ 9 + (412850732989 / 4800000) * alpha * t ^ 11 + (411254395339 / 5760000) * alpha * t ^ 13 + (-4519662667 / 200000) * alpha * t ^ 15 + (-6112328691 / 3200000) * alpha * t ^ 17 + (-3108341893 / 14400000) * alpha * t ^ 19 + (480931649 / 3200000) * alpha * t ^ 21 + (-590908489 / 9600000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_01, v40_02, v40_03, v40_04, v40_10, v40_11, v40_12, v40_13, v40_14, v40_20, v40_21, v40_22, v40_23, v40_24, v40_30, v40_31, v40_32, v40_33, v40_34]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_03, phase40_04, phase40_10, phase40_11, phase40_12, phase40_13, phase40_14, phase40_20, phase40_21, phase40_22, phase40_23, phase40_24, phase40_30, phase40_31, phase40_32, phase40_33, phase40_34]
  try simp only [star_one, star_neg]
  linear_combination ((226527 / 20) * t ^ 3 + (-2641933 / 80) * t ^ 5 + (9280622237 / 320000) * t ^ 7 + (-923310151 / 320000) * t ^ 9 + (-591541757 / 128000) * t ^ 11 + (-2137697333 / 1920000) * t ^ 13 + (725360813 / 480000) * t ^ 15 + (-1627297 / 8000) * t ^ 17 + (-8257807 / 1920000) * t ^ 19 + (18438607 / 1920000) * t ^ 21 + (1183 / 400) * t ^ 25) * alpha_sq
theorem v41_40 (t : ℂ) : (momentPoly 41 z41 4 0).eval t = ((3051187 / 8000) * t ^ 4 + (-2804027 / 4000) * t ^ 6 + (5128677 / 16000) * t ^ 8 + (-140903 / 12000) * t ^ 10 + (494783 / 48000) * t ^ 16 + (1445849 / 24000) * alpha * t ^ 4 + (-833489 / 12000) * alpha * t ^ 6 + (-337681 / 48000) * alpha * t ^ 8 + (589979 / 36000) * alpha * t ^ 10 + (51901 / 144000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_10, v40_20, v40_30, v40_40]
  try simp only [phase40_00, phase40_10, phase40_20, phase40_30, phase40_40]
  try simp only [star_one, star_neg]
  linear_combination ((-1183 / 50) * t ^ 4 + (7343 / 200) * t ^ 6 + (-49 / 40) * t ^ 8 + (-1183 / 100) * t ^ 10) * alpha_sq
theorem v41_41 (t : ℂ) : (momentPoly 41 z41 4 1).eval t = ((72127 / 20) * t ^ 3 + (-60201469 / 8000) * t ^ 5 + (15928269 / 4000) * t ^ 7 + (5789221 / 16000) * t ^ 9 + (-4997359 / 12000) * t ^ 11 + (-365441 / 48000) * t ^ 17 + (-445639 / 100) * alpha * t ^ 3 + (45613403 / 4800) * alpha * t ^ 5 + (-11443819 / 2400) * alpha * t ^ 7 + (-11302163 / 9600) * alpha * t ^ 9 + (6469801 / 7200) * alpha * t ^ 11 + (16727 / 28800) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_01, v40_10, v40_11, v40_20, v40_21, v40_30, v40_31, v40_40, v40_41]
  try simp only [phase40_00, phase40_01, phase40_10, phase40_11, phase40_20, phase40_21, phase40_30, phase40_31, phase40_40, phase40_41]
  try simp only [star_one, star_neg]
  linear_combination ((-3871 / 40) * t ^ 3 + (2822397 / 16000) * t ^ 5 + (-1548391 / 24000) * t ^ 7 + (-1351919 / 96000) * t ^ 9 + (-78899 / 72000) * t ^ 11 + (20099 / 288000) * t ^ 17) * alpha_sq
theorem v41_42 (t : ℂ) : (momentPoly 41 z41 4 2).eval t = ((-2147673 / 10) * t ^ 2 + (121072797 / 200) * t ^ 4 + (-267526260067 / 480000) * t ^ 6 + (26397897147 / 160000) * t ^ 8 + (-215123177 / 38400) * t ^ 10 + (21139622483 / 2880000) * t ^ 12 + (-1096583 / 720000) * t ^ 14 + (-215379023 / 2880000) * t ^ 18 + (289900103 / 2880000) * t ^ 20 + (-232309 / 30) * alpha * t ^ 2 + (2795531 / 200) * alpha * t ^ 4 + (-2792628317 / 480000) * alpha * t ^ 6 + (27945677 / 160000) * alpha * t ^ 8 + (-4835889 / 64000) * alpha * t ^ 10 + (-1985404507 / 2880000) * alpha * t ^ 12 + (123669887 / 720000) * alpha * t ^ 14 + (-8556593 / 2880000) * alpha * t ^ 18 + (14221873 / 2880000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_01, v40_02, v40_10, v40_11, v40_12, v40_20, v40_21, v40_22, v40_30, v40_31, v40_32, v40_40, v40_41, v40_42]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_10, phase40_11, phase40_12, phase40_20, phase40_21, phase40_22, phase40_30, phase40_31, phase40_32, phase40_40, phase40_41, phase40_42]
  try simp only [star_one, star_neg]
  linear_combination ((46137 / 25) * t ^ 4 + (-25629023 / 6000) * t ^ 6 + (31400183 / 16000) * t ^ 8 + (32501173 / 24000) * t ^ 10 + (-14388277 / 19200) * t ^ 12 + (-9743683 / 72000) * t ^ 14 + (-6853 / 1200) * t ^ 18 + (-78899 / 288000) * t ^ 20) * alpha_sq
theorem v41_43 (t : ℂ) : (momentPoly 41 z41 4 3).eval t = ((-1536401 / 2) * t + (12495969 / 5) * t ^ 3 + (-1485791877 / 500) * t ^ 5 + (1275909341423 / 800000) * t ^ 7 + (-702540095491 / 1600000) * t ^ 9 + (127710522951 / 1600000) * t ^ 11 + (11551679541 / 640000) * t ^ 13 + (-2067315053 / 150000) * t ^ 15 + (3573642823 / 3200000) * t ^ 17 + (-622910287 / 4800000) * t ^ 19 + (-2953511971 / 9600000) * t ^ 21 + (240270917 / 9600000) * t ^ 25 + (1536401 / 2) * alpha * t + (-9467904 / 5) * alpha * t ^ 3 + (1254219527 / 1000) * alpha * t ^ 5 + (-42337720219 / 800000) * alpha * t ^ 7 + (272912593039 / 4800000) * alpha * t ^ 9 + (-412850732989 / 4800000) * alpha * t ^ 11 + (-411254395339 / 5760000) * alpha * t ^ 13 + (4519662667 / 200000) * alpha * t ^ 15 + (6112328691 / 3200000) * alpha * t ^ 17 + (3108341893 / 14400000) * alpha * t ^ 19 + (-480931649 / 3200000) * alpha * t ^ 21 + (590908489 / 9600000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_01, v40_02, v40_03, v40_10, v40_11, v40_12, v40_13, v40_20, v40_21, v40_22, v40_23, v40_30, v40_31, v40_32, v40_33, v40_40, v40_41, v40_42, v40_43]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_03, phase40_10, phase40_11, phase40_12, phase40_13, phase40_20, phase40_21, phase40_22, phase40_23, phase40_30, phase40_31, phase40_32, phase40_33, phase40_40, phase40_41, phase40_42, phase40_43]
  try simp only [star_one, star_neg]
  linear_combination ((226527 / 20) * t ^ 3 + (-2641933 / 80) * t ^ 5 + (9280622237 / 320000) * t ^ 7 + (-923310151 / 320000) * t ^ 9 + (-591541757 / 128000) * t ^ 11 + (-2137697333 / 1920000) * t ^ 13 + (725360813 / 480000) * t ^ 15 + (-1627297 / 8000) * t ^ 17 + (-8257807 / 1920000) * t ^ 19 + (18438607 / 1920000) * t ^ 21 + (1183 / 400) * t ^ 25) * alpha_sq
theorem v41_44 (t : ℂ) : (momentPoly 41 z41 4 4).eval t = (62992441 + (-236797760) * t ^ 2 + (33406747591 / 100) * t ^ 4 + (-543766163991 / 2500) * t ^ 6 + (3376578549454427 / 48000000) * t ^ 8 + (-218453260828027 / 12000000) * t ^ 10 + (55252869785173 / 9600000) * t ^ 12 + (-109926303980077 / 72000000) * t ^ 14 + (494726945434657 / 576000000) * t ^ 16 + (3921722951827 / 72000000) * t ^ 18 + (-15660304666223 / 432000000) * t ^ 20 + (-560444062103 / 72000000) * t ^ 22 + (1635437788673 / 288000000) * t ^ 24 + (-101589956167 / 216000000) * t ^ 26 + (113433091267 / 1728000000) * t ^ 32) := by
  rw [momentPoly]
  simp only [z41, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v40_00, v40_01, v40_02, v40_03, v40_04, v40_10, v40_11, v40_12, v40_13, v40_14, v40_20, v40_21, v40_22, v40_23, v40_24, v40_30, v40_31, v40_32, v40_33, v40_34, v40_40, v40_41, v40_42, v40_43, v40_44]
  try simp only [phase40_00, phase40_01, phase40_02, phase40_03, phase40_04, phase40_10, phase40_11, phase40_12, phase40_13, phase40_14, phase40_20, phase40_21, phase40_22, phase40_23, phase40_24, phase40_30, phase40_31, phase40_32, phase40_33, phase40_34, phase40_40, phase40_41, phase40_42, phase40_43, phase40_44]
  try simp only [star_one, star_neg]
  linear_combination ((-146134947 / 500) * t ^ 6 + (580458119897 / 600000) * t ^ 8 + (-611646391817 / 600000) * t ^ 10 + (112477072187 / 600000) * t ^ 12 + (3824556073 / 14400) * t ^ 14 + (-240909128791 / 2400000) * t ^ 16 + (-6690235111 / 800000) * t ^ 18 + (753841717 / 3600000) * t ^ 20 + (57819851 / 1200000) * t ^ 22 + (-10652599 / 160000) * t ^ 24 + (-1837141067 / 7200000) * t ^ 26 + (20099 / 144000) * t ^ 32) * alpha_sq
#print axioms v41_00
#print axioms v41_11
#print axioms v41_22
#print axioms v41_33
#print axioms v41_44
end PhotonCertB
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertB
theorem site42 : ((r ^ 2 * (-1)) : ℂ) = ((1 / 2) + (-1 / 2) * alpha) := by
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 4)) * alpha_sq
theorem phase42_00 : ((r ^ 2 * (-1)) : ℂ) ^ 0 * star ((r ^ 2 * (-1)) : ℂ) ^ 0 = (1) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase42_01 : ((r ^ 2 * (-1)) : ℂ) ^ 0 * star ((r ^ 2 * (-1)) : ℂ) ^ 1 = ((1 / 2) + (1 / 2) * alpha) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase42_02 : ((r ^ 2 * (-1)) : ℂ) ^ 0 * star ((r ^ 2 * (-1)) : ℂ) ^ 2 = ((-1 / 2) + (1 / 2) * alpha) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 4)) * alpha_sq
theorem phase42_03 : ((r ^ 2 * (-1)) : ℂ) ^ 0 * star ((r ^ 2 * (-1)) : ℂ) ^ 3 = ((-1)) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((3 / 8) + (1 / 8) * alpha) * alpha_sq
theorem phase42_04 : ((r ^ 2 * (-1)) : ℂ) ^ 0 * star ((r ^ 2 * (-1)) : ℂ) ^ 4 = ((-1 / 2) + (-1 / 2) * alpha) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((3 / 16) + (1 / 4) * alpha + (1 / 16) * alpha ^ 2) * alpha_sq
theorem phase42_10 : ((r ^ 2 * (-1)) : ℂ) ^ 1 * star ((r ^ 2 * (-1)) : ℂ) ^ 0 = ((1 / 2) + (-1 / 2) * alpha) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  ring
theorem phase42_11 : ((r ^ 2 * (-1)) : ℂ) ^ 1 * star ((r ^ 2 * (-1)) : ℂ) ^ 1 = (1) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 4)) * alpha_sq
theorem phase42_12 : ((r ^ 2 * (-1)) : ℂ) ^ 1 * star ((r ^ 2 * (-1)) : ℂ) ^ 2 = ((1 / 2) + (1 / 2) * alpha) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 8) + (-1 / 8) * alpha) * alpha_sq
theorem phase42_13 : ((r ^ 2 * (-1)) : ℂ) ^ 1 * star ((r ^ 2 * (-1)) : ℂ) ^ 3 = ((-1 / 2) + (1 / 2) * alpha) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((3 / 16) + (-1 / 8) * alpha + (-1 / 16) * alpha ^ 2) * alpha_sq
theorem phase42_14 : ((r ^ 2 * (-1)) : ℂ) ^ 1 * star ((r ^ 2 * (-1)) : ℂ) ^ 4 = ((-1)) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((11 / 32) + (1 / 32) * alpha + (-3 / 32) * alpha ^ 2 + (-1 / 32) * alpha ^ 3) * alpha_sq
theorem phase42_20 : ((r ^ 2 * (-1)) : ℂ) ^ 2 * star ((r ^ 2 * (-1)) : ℂ) ^ 0 = ((-1 / 2) + (-1 / 2) * alpha) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((1 / 4)) * alpha_sq
theorem phase42_21 : ((r ^ 2 * (-1)) : ℂ) ^ 2 * star ((r ^ 2 * (-1)) : ℂ) ^ 1 = ((1 / 2) + (-1 / 2) * alpha) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-1 / 8) + (1 / 8) * alpha) * alpha_sq
theorem phase42_22 : ((r ^ 2 * (-1)) : ℂ) ^ 2 * star ((r ^ 2 * (-1)) : ℂ) ^ 2 = (1) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-5 / 16) + (1 / 16) * alpha ^ 2) * alpha_sq
theorem phase42_23 : ((r ^ 2 * (-1)) : ℂ) ^ 2 * star ((r ^ 2 * (-1)) : ℂ) ^ 3 = ((1 / 2) + (1 / 2) * alpha) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-5 / 32) + (-5 / 32) * alpha + (1 / 32) * alpha ^ 2 + (1 / 32) * alpha ^ 3) * alpha_sq
theorem phase42_24 : ((r ^ 2 * (-1)) : ℂ) ^ 2 * star ((r ^ 2 * (-1)) : ℂ) ^ 4 = ((-1 / 2) + (1 / 2) * alpha) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((11 / 64) + (-5 / 32) * alpha + (-1 / 16) * alpha ^ 2 + (1 / 32) * alpha ^ 3 + (1 / 64) * alpha ^ 4) * alpha_sq
theorem phase42_30 : ((r ^ 2 * (-1)) : ℂ) ^ 3 * star ((r ^ 2 * (-1)) : ℂ) ^ 0 = ((-1)) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((3 / 8) + (-1 / 8) * alpha) * alpha_sq
theorem phase42_31 : ((r ^ 2 * (-1)) : ℂ) ^ 3 * star ((r ^ 2 * (-1)) : ℂ) ^ 1 = ((-1 / 2) + (-1 / 2) * alpha) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((3 / 16) + (1 / 8) * alpha + (-1 / 16) * alpha ^ 2) * alpha_sq
theorem phase42_32 : ((r ^ 2 * (-1)) : ℂ) ^ 3 * star ((r ^ 2 * (-1)) : ℂ) ^ 2 = ((1 / 2) + (-1 / 2) * alpha) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-5 / 32) + (5 / 32) * alpha + (1 / 32) * alpha ^ 2 + (-1 / 32) * alpha ^ 3) * alpha_sq
theorem phase42_33 : ((r ^ 2 * (-1)) : ℂ) ^ 3 * star ((r ^ 2 * (-1)) : ℂ) ^ 3 = (1) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-21 / 64) + (3 / 32) * alpha ^ 2 + (-1 / 64) * alpha ^ 4) * alpha_sq
theorem phase42_34 : ((r ^ 2 * (-1)) : ℂ) ^ 3 * star ((r ^ 2 * (-1)) : ℂ) ^ 4 = ((1 / 2) + (1 / 2) * alpha) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-21 / 128) + (-21 / 128) * alpha + (3 / 64) * alpha ^ 2 + (3 / 64) * alpha ^ 3 + (-1 / 128) * alpha ^ 4 + (-1 / 128) * alpha ^ 5) * alpha_sq
theorem phase42_40 : ((r ^ 2 * (-1)) : ℂ) ^ 4 * star ((r ^ 2 * (-1)) : ℂ) ^ 0 = ((-1 / 2) + (1 / 2) * alpha) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((3 / 16) + (-1 / 4) * alpha + (1 / 16) * alpha ^ 2) * alpha_sq
theorem phase42_41 : ((r ^ 2 * (-1)) : ℂ) ^ 4 * star ((r ^ 2 * (-1)) : ℂ) ^ 1 = ((-1)) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((11 / 32) + (-1 / 32) * alpha + (-3 / 32) * alpha ^ 2 + (1 / 32) * alpha ^ 3) * alpha_sq
theorem phase42_42 : ((r ^ 2 * (-1)) : ℂ) ^ 4 * star ((r ^ 2 * (-1)) : ℂ) ^ 2 = ((-1 / 2) + (-1 / 2) * alpha) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((11 / 64) + (5 / 32) * alpha + (-1 / 16) * alpha ^ 2 + (-1 / 32) * alpha ^ 3 + (1 / 64) * alpha ^ 4) * alpha_sq
theorem phase42_43 : ((r ^ 2 * (-1)) : ℂ) ^ 4 * star ((r ^ 2 * (-1)) : ℂ) ^ 3 = ((1 / 2) + (-1 / 2) * alpha) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-21 / 128) + (21 / 128) * alpha + (3 / 64) * alpha ^ 2 + (-3 / 64) * alpha ^ 3 + (-1 / 128) * alpha ^ 4 + (1 / 128) * alpha ^ 5) * alpha_sq
theorem phase42_44 : ((r ^ 2 * (-1)) : ℂ) ^ 4 * star ((r ^ 2 * (-1)) : ℂ) ^ 4 = (1) := by
  rw [site42]
  simp only [thetaPlus, thetaMinus, phiPlus, phiMinus, r, star_mul, star_div₀, star_add, star_sub, star_neg, star_pow, star_ofNat, star_one, star_alpha, star_c, star_d]
  linear_combination ((-85 / 256) + (27 / 256) * alpha ^ 2 + (-7 / 256) * alpha ^ 4 + (1 / 256) * alpha ^ 6) * alpha_sq
noncomputable def z42 : Fin 42 → ℂ := Fin.snoc z41 (r ^ 2 * (-1))
theorem v42_00 (t : ℂ) : (momentPoly 42 z42 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00]
  try simp only [phase42_00]
  try simp only [star_one, star_neg]
  ring
theorem v42_01 (t : ℂ) : (momentPoly 42 z42 0 1).eval t = 0 := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_01]
  try simp only [phase42_00, phase42_01]
  try simp only [star_one, star_neg]
  ring
theorem v42_02 (t : ℂ) : (momentPoly 42 z42 0 2).eval t = ((-413 / 40) * t ^ 2 + (413 / 40) * t ^ 4 + (-71 / 120) * alpha * t ^ 2 + (71 / 120) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_01, v41_02]
  try simp only [phase42_00, phase42_01, phase42_02]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 2) * t ^ 2) * alpha_sq
theorem v42_03 (t : ℂ) : (momentPoly 42 z42 0 3).eval t = (4 * t ^ 3 + (-6) * t ^ 5 + 2 * t ^ 9 + (1183 / 100) * alpha * t ^ 3 + (-3549 / 200) * alpha * t ^ 5 + (1183 / 200) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_01, v41_02, v41_03]
  try simp only [phase42_00, phase42_01, phase42_02, phase42_03]
  try simp only [star_one, star_neg]
  linear_combination ((49 / 80) * t ^ 3 + (-49 / 80) * t ^ 5) * alpha_sq
theorem v42_04 (t : ℂ) : (momentPoly 42 z42 0 4).eval t = ((2062547 / 8000) * t ^ 4 + (-2062547 / 4000) * t ^ 6 + (4595877 / 16000) * t ^ 8 + (-470783 / 12000) * t ^ 10 + (470783 / 48000) * t ^ 16 + (1003591 / 24000) * alpha * t ^ 4 + (-1003591 / 12000) * alpha * t ^ 6 + (1883281 / 48000) * alpha * t ^ 8 + (123901 / 36000) * alpha * t ^ 10 + (-123901 / 144000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_01, v41_02, v41_03, v41_04]
  try simp only [phase42_00, phase42_01, phase42_02, phase42_03, phase42_04]
  try simp only [star_one, star_neg]
  linear_combination ((5641 / 100) * t ^ 4 + (-13403 / 200) * t ^ 6 + (11 / 40) * t ^ 8 + (1183 / 100) * t ^ 10) * alpha_sq
theorem v42_10 (t : ℂ) : (momentPoly 42 z42 1 0).eval t = 0 := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_10]
  try simp only [phase42_00, phase42_10]
  try simp only [star_one, star_neg]
  ring
theorem v42_11 (t : ℂ) : (momentPoly 42 z42 1 1).eval t = (42 + (-42) * t ^ 2) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_01, v41_10, v41_11]
  try simp only [phase42_00, phase42_01, phase42_10, phase42_11]
  try simp only [star_one, star_neg]
  linear_combination ((1 / 2) * t ^ 2) * alpha_sq
theorem v42_12 (t : ℂ) : (momentPoly 42 z42 1 2).eval t = 0 := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_01, v41_02, v41_10, v41_11, v41_12]
  try simp only [phase42_00, phase42_01, phase42_02, phase42_10, phase42_11, phase42_12]
  try simp only [star_one, star_neg]
  linear_combination ((-49 / 240) * t ^ 3 + (49 / 240) * t ^ 5) * alpha_sq
theorem v42_13 (t : ℂ) : (momentPoly 42 z42 1 3).eval t = ((-50799 / 40) * t ^ 2 + (25193 / 10) * t ^ 4 + (-1239) * t ^ 6 + (-413 / 40) * t ^ 10 + (-2911 / 40) * alpha * t ^ 2 + (4331 / 30) * alpha * t ^ 4 + (-71) * alpha * t ^ 6 + (-71 / 120) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_01, v41_02, v41_03, v41_10, v41_11, v41_12, v41_13]
  try simp only [phase42_00, phase42_01, phase42_02, phase42_03, phase42_10, phase42_11, phase42_12, phase42_13]
  try simp only [star_one, star_neg]
  linear_combination ((-123 / 2) * t ^ 2 + (14839 / 400) * t ^ 4 + (1293 / 50) * t ^ 6 + (-1183 / 400) * t ^ 10) * alpha_sq
theorem v42_14 (t : ℂ) : (momentPoly 42 z42 1 4).eval t = (648 * t ^ 3 + (-1604) * t ^ 5 + 936 * t ^ 7 + 342 * t ^ 9 + (-320) * t ^ 11 + (-2) * t ^ 17 + (95823 / 50) * alpha * t ^ 3 + (-474383 / 100) * alpha * t ^ 5 + (138411 / 50) * alpha * t ^ 7 + (202293 / 200) * alpha * t ^ 9 + (-4732 / 5) * alpha * t ^ 11 + (-1183 / 200) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_01, v41_02, v41_03, v41_04, v41_10, v41_11, v41_12, v41_13, v41_14]
  try simp only [phase42_00, phase42_01, phase42_02, phase42_03, phase42_04, phase42_10, phase42_11, phase42_12, phase42_13, phase42_14]
  try simp only [star_one, star_neg]
  linear_combination ((3969 / 40) * t ^ 3 + (-2733597 / 16000) * t ^ 5 + (1260391 / 24000) * t ^ 7 + (1351919 / 96000) * t ^ 9 + (366899 / 72000) * t ^ 11 + (-20099 / 288000) * t ^ 17) * alpha_sq
theorem v42_20 (t : ℂ) : (momentPoly 42 z42 2 0).eval t = ((-413 / 40) * t ^ 2 + (413 / 40) * t ^ 4 + (71 / 120) * alpha * t ^ 2 + (-71 / 120) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_10, v41_20]
  try simp only [phase42_00, phase42_10, phase42_20]
  try simp only [star_one, star_neg]
  linear_combination ((-1 / 2) * t ^ 2) * alpha_sq
theorem v42_21 (t : ℂ) : (momentPoly 42 z42 2 1).eval t = 0 := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_01, v41_10, v41_11, v41_20, v41_21]
  try simp only [phase42_00, phase42_01, phase42_10, phase42_11, phase42_20, phase42_21]
  try simp only [star_one, star_neg]
  linear_combination ((-49 / 240) * t ^ 3 + (49 / 240) * t ^ 5) * alpha_sq
theorem v42_22 (t : ℂ) : (momentPoly 42 z42 2 2).eval t = (3486 + (-6888) * t ^ 2 + (4060387 / 1200) * t ^ 4 + (-28387 / 600) * t ^ 6 + (78787 / 1200) * t ^ 8) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_01, v41_02, v41_10, v41_11, v41_12, v41_20, v41_21, v41_22]
  try simp only [phase42_00, phase42_01, phase42_02, phase42_10, phase42_11, phase42_12, phase42_20, phase42_21, phase42_22]
  try simp only [star_one, star_neg]
  linear_combination (82 * t ^ 2 + (-1024 / 15) * t ^ 4 + (-1457 / 120) * t ^ 6 + (-11 / 120) * t ^ 8) * alpha_sq
theorem v42_23 (t : ℂ) : (momentPoly 42 z42 2 3).eval t = ((-249193 / 4000) * t ^ 5 + (249193 / 1600) * t ^ 7 + (-747579 / 8000) * t ^ 9 + (-249193 / 8000) * t ^ 11 + (249193 / 8000) * t ^ 13 + (-1437337 / 12000) * alpha * t ^ 5 + (1437337 / 4800) * alpha * t ^ 7 + (-1437337 / 8000) * alpha * t ^ 9 + (-1437337 / 24000) * alpha * t ^ 11 + (1437337 / 24000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_01, v41_02, v41_03, v41_10, v41_11, v41_12, v41_13, v41_20, v41_21, v41_22, v41_23]
  try simp only [phase42_00, phase42_01, phase42_02, phase42_03, phase42_10, phase42_11, phase42_12, phase42_13, phase42_20, phase42_21, phase42_22, phase42_23]
  try simp only [star_one, star_neg]
  linear_combination ((-3969 / 80) * t ^ 3 + (120583 / 1200) * t ^ 5 + (-2309 / 40) * t ^ 7 + (413 / 50) * t ^ 9 + (1859 / 1200) * t ^ 11 + (-1183 / 400) * t ^ 13) * alpha_sq
theorem v42_24 (t : ℂ) : (momentPoly 42 z42 2 4).eval t = ((-823109 / 4) * t ^ 2 + (4844903 / 8) * t ^ 4 + (-281228255347 / 480000) * t ^ 6 + (29066975347 / 160000) * t ^ 8 + (111011267 / 192000) * t ^ 10 + (11853589163 / 2880000) * t ^ 12 + (-227779583 / 720000) * t ^ 14 + (-227779583 / 2880000) * t ^ 18 + (257515583 / 2880000) * t ^ 20 + (-141503 / 12) * alpha * t ^ 2 + (832901 / 24) * alpha * t ^ 4 + (-5391447041 / 160000) * alpha * t ^ 6 + (1724421123 / 160000) * alpha * t ^ 8 + (-52397677 / 192000) * alpha * t ^ 10 + (206834089 / 960000) * alpha * t ^ 12 + (15235451 / 240000) * alpha * t ^ 14 + (15235451 / 960000) * alpha * t ^ 18 + (-14667451 / 960000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_01, v41_02, v41_03, v41_04, v41_10, v41_11, v41_12, v41_13, v41_14, v41_20, v41_21, v41_22, v41_23, v41_24]
  try simp only [phase42_00, phase42_01, phase42_02, phase42_03, phase42_04, phase42_10, phase42_11, phase42_12, phase42_13, phase42_14, phase42_20, phase42_21, phase42_22, phase42_23, phase42_24]
  try simp only [star_one, star_neg]
  linear_combination ((-9965) * t ^ 2 + (59356 / 5) * t ^ 4 + (133157167 / 24000) * t ^ 6 + (-310012351 / 48000) * t ^ 8 + (-89914277 / 48000) * t ^ 10 + (211730269 / 288000) * t ^ 12 + (9842681 / 72000) * t ^ 14 + (22607 / 28800) * t ^ 18 + (65101 / 288000) * t ^ 20) * alpha_sq
theorem v42_30 (t : ℂ) : (momentPoly 42 z42 3 0).eval t = (4 * t ^ 3 + (-6) * t ^ 5 + 2 * t ^ 9 + (-1183 / 100) * alpha * t ^ 3 + (3549 / 200) * alpha * t ^ 5 + (-1183 / 200) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_10, v41_20, v41_30]
  try simp only [phase42_00, phase42_10, phase42_20, phase42_30]
  try simp only [star_one, star_neg]
  linear_combination ((49 / 80) * t ^ 3 + (-49 / 80) * t ^ 5) * alpha_sq
theorem v42_31 (t : ℂ) : (momentPoly 42 z42 3 1).eval t = ((-50799 / 40) * t ^ 2 + (25193 / 10) * t ^ 4 + (-1239) * t ^ 6 + (-413 / 40) * t ^ 10 + (2911 / 40) * alpha * t ^ 2 + (-4331 / 30) * alpha * t ^ 4 + 71 * alpha * t ^ 6 + (71 / 120) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_01, v41_10, v41_11, v41_20, v41_21, v41_30, v41_31]
  try simp only [phase42_00, phase42_01, phase42_10, phase42_11, phase42_20, phase42_21, phase42_30, phase42_31]
  try simp only [star_one, star_neg]
  linear_combination ((-123 / 2) * t ^ 2 + (14839 / 400) * t ^ 4 + (1293 / 50) * t ^ 6 + (-1183 / 400) * t ^ 10) * alpha_sq
theorem v42_32 (t : ℂ) : (momentPoly 42 z42 3 2).eval t = ((-249193 / 4000) * t ^ 5 + (249193 / 1600) * t ^ 7 + (-747579 / 8000) * t ^ 9 + (-249193 / 8000) * t ^ 11 + (249193 / 8000) * t ^ 13 + (1437337 / 12000) * alpha * t ^ 5 + (-1437337 / 4800) * alpha * t ^ 7 + (1437337 / 8000) * alpha * t ^ 9 + (1437337 / 24000) * alpha * t ^ 11 + (-1437337 / 24000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_01, v41_02, v41_10, v41_11, v41_12, v41_20, v41_21, v41_22, v41_30, v41_31, v41_32]
  try simp only [phase42_00, phase42_01, phase42_02, phase42_10, phase42_11, phase42_12, phase42_20, phase42_21, phase42_22, phase42_30, phase42_31, phase42_32]
  try simp only [star_one, star_neg]
  linear_combination ((-3969 / 80) * t ^ 3 + (120583 / 1200) * t ^ 5 + (-2309 / 40) * t ^ 7 + (413 / 50) * t ^ 9 + (1859 / 1200) * t ^ 11 + (-1183 / 400) * t ^ 13) * alpha_sq
theorem v42_33 (t : ℂ) : (momentPoly 42 z42 3 3).eval t = (428820 + (-1255590) * t ^ 2 + (12181161 / 10) * t ^ 4 + (-4078685833 / 10000) * t ^ 6 + (389030849 / 10000) * t ^ 8 + (-889185597 / 40000) * t ^ 10 + (5777817 / 10000) * t ^ 12 + (-15914101 / 20000) * t ^ 14 + (2678467 / 40000) * t ^ 18) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_01, v41_02, v41_03, v41_10, v41_11, v41_12, v41_13, v41_20, v41_21, v41_22, v41_23, v41_30, v41_31, v41_32, v41_33]
  try simp only [phase42_00, phase42_01, phase42_02, phase42_03, phase42_10, phase42_11, phase42_12, phase42_13, phase42_20, phase42_21, phase42_22, phase42_23, phase42_30, phase42_31, phase42_32, phase42_33]
  try simp only [star_one, star_neg]
  linear_combination ((29895 / 2) * t ^ 2 + (-24576) * t ^ 4 + (11772001 / 2000) * t ^ 6 + (4317643 / 1600) * t ^ 8 + (7974021 / 8000) * t ^ 10 + (1918697 / 8000) * t ^ 12 + (-1504937 / 8000) * t ^ 14) * alpha_sq
theorem v42_34 (t : ℂ) : (momentPoly 42 z42 3 4).eval t = ((-59058741 / 2000) * t ^ 5 + (83697732353 / 800000) * t ^ 7 + (-196794176271 / 1600000) * t ^ 9 + (57555750541 / 1600000) * t ^ 11 + (10404814399 / 384000) * t ^ 13 + (-3258674459 / 200000) * t ^ 15 + (4066272223 / 3200000) * t ^ 17 + (-191254117 / 4800000) * t ^ 19 + (-340769917 / 3200000) * t ^ 21 + (41738317 / 9600000) * t ^ 25 + (-113549623 / 2000) * alpha * t ^ 5 + (154746841899 / 800000) * alpha * t ^ 7 + (-1005425688079 / 4800000) * alpha * t ^ 9 + (181816696909 / 4800000) * alpha * t ^ 11 + (70240295423 / 1152000) * alpha * t ^ 13 + (-14654897291 / 600000) * alpha * t ^ 15 + (-15557455073 / 9600000) * alpha * t ^ 17 + (857967067 / 14400000) * alpha * t ^ 19 + (-4435133 / 9600000) * alpha * t ^ 21 + (-1720369267 / 28800000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_01, v41_02, v41_03, v41_04, v41_10, v41_11, v41_12, v41_13, v41_14, v41_20, v41_21, v41_22, v41_23, v41_24, v41_30, v41_31, v41_32, v41_33, v41_34]
  try simp only [phase42_00, phase42_01, phase42_02, phase42_03, phase42_04, phase42_10, phase42_11, phase42_12, phase42_13, phase42_14, phase42_20, phase42_21, phase42_22, phase42_23, phase42_24, phase42_30, phase42_31, phase42_32, phase42_33, phase42_34]
  try simp only [star_one, star_neg]
  linear_combination ((-476427 / 40) * t ^ 3 + (14411079 / 400) * t ^ 5 + (-12766749917 / 320000) * t ^ 7 + (6603598291 / 320000) * t ^ 9 + (-598496147 / 128000) * t ^ 11 + (-3528648367 / 1920000) * t ^ 13 + (295257269 / 160000) * t ^ 15 + (-1542117 / 8000) * t ^ 17 + (18520207 / 1920000) * t ^ 19 + (-5620209 / 640000) * t ^ 21 + (1183 / 400) * t ^ 25) * alpha_sq
theorem v42_40 (t : ℂ) : (momentPoly 42 z42 4 0).eval t = ((2062547 / 8000) * t ^ 4 + (-2062547 / 4000) * t ^ 6 + (4595877 / 16000) * t ^ 8 + (-470783 / 12000) * t ^ 10 + (470783 / 48000) * t ^ 16 + (-1003591 / 24000) * alpha * t ^ 4 + (1003591 / 12000) * alpha * t ^ 6 + (-1883281 / 48000) * alpha * t ^ 8 + (-123901 / 36000) * alpha * t ^ 10 + (123901 / 144000) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_10, v41_20, v41_30, v41_40]
  try simp only [phase42_00, phase42_10, phase42_20, phase42_30, phase42_40]
  try simp only [star_one, star_neg]
  linear_combination ((5641 / 100) * t ^ 4 + (-13403 / 200) * t ^ 6 + (11 / 40) * t ^ 8 + (1183 / 100) * t ^ 10) * alpha_sq
theorem v42_41 (t : ℂ) : (momentPoly 42 z42 4 1).eval t = (648 * t ^ 3 + (-1604) * t ^ 5 + 936 * t ^ 7 + 342 * t ^ 9 + (-320) * t ^ 11 + (-2) * t ^ 17 + (-95823 / 50) * alpha * t ^ 3 + (474383 / 100) * alpha * t ^ 5 + (-138411 / 50) * alpha * t ^ 7 + (-202293 / 200) * alpha * t ^ 9 + (4732 / 5) * alpha * t ^ 11 + (1183 / 200) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_01, v41_10, v41_11, v41_20, v41_21, v41_30, v41_31, v41_40, v41_41]
  try simp only [phase42_00, phase42_01, phase42_10, phase42_11, phase42_20, phase42_21, phase42_30, phase42_31, phase42_40, phase42_41]
  try simp only [star_one, star_neg]
  linear_combination ((3969 / 40) * t ^ 3 + (-2733597 / 16000) * t ^ 5 + (1260391 / 24000) * t ^ 7 + (1351919 / 96000) * t ^ 9 + (366899 / 72000) * t ^ 11 + (-20099 / 288000) * t ^ 17) * alpha_sq
theorem v42_42 (t : ℂ) : (momentPoly 42 z42 4 2).eval t = ((-823109 / 4) * t ^ 2 + (4844903 / 8) * t ^ 4 + (-281228255347 / 480000) * t ^ 6 + (29066975347 / 160000) * t ^ 8 + (111011267 / 192000) * t ^ 10 + (11853589163 / 2880000) * t ^ 12 + (-227779583 / 720000) * t ^ 14 + (-227779583 / 2880000) * t ^ 18 + (257515583 / 2880000) * t ^ 20 + (141503 / 12) * alpha * t ^ 2 + (-832901 / 24) * alpha * t ^ 4 + (5391447041 / 160000) * alpha * t ^ 6 + (-1724421123 / 160000) * alpha * t ^ 8 + (52397677 / 192000) * alpha * t ^ 10 + (-206834089 / 960000) * alpha * t ^ 12 + (-15235451 / 240000) * alpha * t ^ 14 + (-15235451 / 960000) * alpha * t ^ 18 + (14667451 / 960000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_01, v41_02, v41_10, v41_11, v41_12, v41_20, v41_21, v41_22, v41_30, v41_31, v41_32, v41_40, v41_41, v41_42]
  try simp only [phase42_00, phase42_01, phase42_02, phase42_10, phase42_11, phase42_12, phase42_20, phase42_21, phase42_22, phase42_30, phase42_31, phase42_32, phase42_40, phase42_41, phase42_42]
  try simp only [star_one, star_neg]
  linear_combination ((-9965) * t ^ 2 + (59356 / 5) * t ^ 4 + (133157167 / 24000) * t ^ 6 + (-310012351 / 48000) * t ^ 8 + (-89914277 / 48000) * t ^ 10 + (211730269 / 288000) * t ^ 12 + (9842681 / 72000) * t ^ 14 + (22607 / 28800) * t ^ 18 + (65101 / 288000) * t ^ 20) * alpha_sq
theorem v42_43 (t : ℂ) : (momentPoly 42 z42 4 3).eval t = ((-59058741 / 2000) * t ^ 5 + (83697732353 / 800000) * t ^ 7 + (-196794176271 / 1600000) * t ^ 9 + (57555750541 / 1600000) * t ^ 11 + (10404814399 / 384000) * t ^ 13 + (-3258674459 / 200000) * t ^ 15 + (4066272223 / 3200000) * t ^ 17 + (-191254117 / 4800000) * t ^ 19 + (-340769917 / 3200000) * t ^ 21 + (41738317 / 9600000) * t ^ 25 + (113549623 / 2000) * alpha * t ^ 5 + (-154746841899 / 800000) * alpha * t ^ 7 + (1005425688079 / 4800000) * alpha * t ^ 9 + (-181816696909 / 4800000) * alpha * t ^ 11 + (-70240295423 / 1152000) * alpha * t ^ 13 + (14654897291 / 600000) * alpha * t ^ 15 + (15557455073 / 9600000) * alpha * t ^ 17 + (-857967067 / 14400000) * alpha * t ^ 19 + (4435133 / 9600000) * alpha * t ^ 21 + (1720369267 / 28800000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_01, v41_02, v41_03, v41_10, v41_11, v41_12, v41_13, v41_20, v41_21, v41_22, v41_23, v41_30, v41_31, v41_32, v41_33, v41_40, v41_41, v41_42, v41_43]
  try simp only [phase42_00, phase42_01, phase42_02, phase42_03, phase42_10, phase42_11, phase42_12, phase42_13, phase42_20, phase42_21, phase42_22, phase42_23, phase42_30, phase42_31, phase42_32, phase42_33, phase42_40, phase42_41, phase42_42, phase42_43]
  try simp only [star_one, star_neg]
  linear_combination ((-476427 / 40) * t ^ 3 + (14411079 / 400) * t ^ 5 + (-12766749917 / 320000) * t ^ 7 + (6603598291 / 320000) * t ^ 9 + (-598496147 / 128000) * t ^ 11 + (-3528648367 / 1920000) * t ^ 13 + (295257269 / 160000) * t ^ 15 + (-1542117 / 8000) * t ^ 17 + (18520207 / 1920000) * t ^ 19 + (-5620209 / 640000) * t ^ 21 + (1183 / 400) * t ^ 25) * alpha_sq
theorem v42_44 (t : ℂ) : (momentPoly 42 z42 4 4).eval t = (69489630 + (-267995952) * t ^ 2 + (9627177577 / 25) * t ^ 4 + (-623169421723 / 2500) * t ^ 6 + (3561879429876827 / 48000000) * t ^ 8 + (-210712960076827 / 12000000) * t ^ 10 + (58569043916773 / 9600000) * t ^ 12 + (-37577890521877 / 72000000) * t ^ 14 + (270203987806657 / 576000000) * t ^ 16 + (2244986106127 / 72000000) * t ^ 18 + (-15651004311023 / 432000000) * t ^ 20 + (-447570871703 / 72000000) * t ^ 22 + (1337503911473 / 288000000) * t ^ 24 + (-213199113667 / 216000000) * t ^ 26 + (97489339267 / 1728000000) * t ^ 32) := by
  rw [momentPoly]
  simp only [z42, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v41_00, v41_01, v41_02, v41_03, v41_04, v41_10, v41_11, v41_12, v41_13, v41_14, v41_20, v41_21, v41_22, v41_23, v41_24, v41_30, v41_31, v41_32, v41_33, v41_34, v41_40, v41_41, v41_42, v41_43, v41_44]
  try simp only [phase42_00, phase42_01, phase42_02, phase42_03, phase42_04, phase42_10, phase42_11, phase42_12, phase42_13, phase42_14, phase42_20, phase42_21, phase42_22, phase42_23, phase42_24, phase42_30, phase42_31, phase42_32, phase42_33, phase42_34, phase42_40, phase42_41, phase42_42, phase42_43, phase42_44]
  try simp only [star_one, star_neg]
  linear_combination (3190428 * t ^ 2 + (-38846464 / 5) * t ^ 4 + (2509092631 / 500) * t ^ 6 + (-63928675657 / 600000) * t ^ 8 + (60129812371 / 300000) * t ^ 10 + (-102322685281 / 300000) * t ^ 12 + (-207046098017 / 720000) * t ^ 14 + (207016785481 / 2400000) * t ^ 16 + (20810383813 / 2400000) * t ^ 18 + (2891464543 / 3600000) * t ^ 20 + (-27476669 / 50000) * t ^ 22 + (17598683 / 480000) * t ^ 24 + (1654729667 / 7200000) * t ^ 26 + (-51901 / 144000) * t ^ 32) * alpha_sq
#print axioms v42_00
#print axioms v42_11
#print axioms v42_22
#print axioms v42_33
#print axioms v42_44
end PhotonCertB
