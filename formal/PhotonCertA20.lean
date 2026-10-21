import PhotonCertA19
open scoped BigOperators NNReal Polynomial
open PhotonMomentPolynomial PhotonGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace PhotonCertA
noncomputable def z20 : Fin 20 → ℂ := Fin.snoc z19 1
theorem v20_00 (t : ℂ) : (momentPoly 20 z20 0 0).eval t = (1) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00]
  try simp only [phase19_00]
  try simp only [star_one, star_neg]
  ring
theorem v20_01 (t : ℂ) : (momentPoly 20 z20 0 1).eval t = (1 * t) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_01]
  try simp only [phase19_00, phase19_01]
  try simp only [star_one, star_neg]
  ring
theorem v20_02 (t : ℂ) : (momentPoly 20 z20 0 2).eval t = ((-81 / 20) * t ^ 2 + (101 / 20) * t ^ 4 + (73 / 15) * alpha * t ^ 2 + (-73 / 15) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_01, v19_02]
  try simp only [phase19_00, phase19_01, phase19_02]
  try simp only [star_one, star_neg]
  ring
theorem v20_03 (t : ℂ) : (momentPoly 20 z20 0 3).eval t = ((-203 / 20) * t ^ 3 + (183 / 20) * t ^ 5 + 2 * t ^ 9 + (4103 / 200) * alpha * t ^ 3 + (-9389 / 400) * alpha * t ^ 5 + (1183 / 400) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_01, v19_02, v19_03]
  try simp only [phase19_00, phase19_01, phase19_02, phase19_03]
  try simp only [star_one, star_neg]
  ring
theorem v20_04 (t : ℂ) : (momentPoly 20 z20 0 4).eval t = ((-724481 / 4000) * t ^ 4 + (683881 / 2000) * t ^ 6 + (-1217891 / 8000) * t ^ 8 + (-25557 / 2000) * t ^ 10 + (41557 / 8000) * t ^ 16 + (-45541 / 375) * alpha * t ^ 4 + (425873 / 1500) * alpha * t ^ 6 + (-120661 / 750) * alpha * t ^ 8 + (-27293 / 4500) * alpha * t ^ 10 + (5033 / 1125) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_01, v19_02, v19_03, v19_04]
  try simp only [phase19_00, phase19_01, phase19_02, phase19_03, phase19_04]
  try simp only [star_one, star_neg]
  ring
theorem v20_10 (t : ℂ) : (momentPoly 20 z20 1 0).eval t = (1 * t) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_10]
  try simp only [phase19_00, phase19_10]
  try simp only [star_one, star_neg]
  ring
theorem v20_11 (t : ℂ) : (momentPoly 20 z20 1 1).eval t = (20 + (-19) * t ^ 2) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_01, v19_10, v19_11]
  try simp only [phase19_00, phase19_01, phase19_10, phase19_11]
  try simp only [star_one, star_neg]
  ring
theorem v20_12 (t : ℂ) : (momentPoly 20 z20 1 2).eval t = (39 * t + (-841 / 20) * t ^ 3 + (81 / 20) * t ^ 5 + (73 / 15) * alpha * t ^ 3 + (-73 / 15) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_01, v19_02, v19_10, v19_11, v19_12]
  try simp only [phase19_00, phase19_01, phase19_02, phase19_10, phase19_11, phase19_12]
  try simp only [star_one, star_neg]
  ring
theorem v20_13 (t : ℂ) : (momentPoly 20 z20 1 3).eval t = ((-4617 / 20) * t ^ 2 + (10029 / 20) * t ^ 4 + (-5331 / 20) * t ^ 6 + (-61 / 20) * t ^ 10 + (1387 / 5) * alpha * t ^ 2 + (-314731 / 600) * alpha * t ^ 4 + (95731 / 400) * alpha * t ^ 6 + (9389 / 1200) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_01, v19_02, v19_03, v19_10, v19_11, v19_12, v19_13]
  try simp only [phase19_00, phase19_01, phase19_02, phase19_03, phase19_10, phase19_11, phase19_12, phase19_13]
  try simp only [star_one, star_neg]
  ring
theorem v20_14 (t : ℂ) : (momentPoly 20 z20 1 4).eval t = ((-7511 / 10) * t ^ 3 + (4793519 / 4000) * t ^ 5 + (-511919 / 2000) * t ^ 7 + (-132291 / 8000) * t ^ 9 + (-353957 / 2000) * t ^ 11 + (25557 / 8000) * t ^ 17 + (151811 / 100) * alpha * t ^ 3 + (-9854173 / 3000) * alpha * t ^ 5 + (694067 / 375) * alpha * t ^ 7 + (682747 / 6000) * alpha * t ^ 9 + (-897923 / 4500) * alpha * t ^ 11 + (27293 / 18000) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_01, v19_02, v19_03, v19_04, v19_10, v19_11, v19_12, v19_13, v19_14]
  try simp only [phase19_00, phase19_01, phase19_02, phase19_03, phase19_04, phase19_10, phase19_11, phase19_12, phase19_13, phase19_14]
  try simp only [star_one, star_neg]
  ring
theorem v20_20 (t : ℂ) : (momentPoly 20 z20 2 0).eval t = ((-81 / 20) * t ^ 2 + (101 / 20) * t ^ 4 + (-73 / 15) * alpha * t ^ 2 + (73 / 15) * alpha * t ^ 4) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_10, v19_20]
  try simp only [phase19_00, phase19_10, phase19_20]
  try simp only [star_one, star_neg]
  ring
theorem v20_21 (t : ℂ) : (momentPoly 20 z20 2 1).eval t = (39 * t + (-841 / 20) * t ^ 3 + (81 / 20) * t ^ 5 + (-73 / 15) * alpha * t ^ 3 + (73 / 15) * alpha * t ^ 5) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_01, v19_10, v19_11, v19_20, v19_21]
  try simp only [phase19_00, phase19_01, phase19_10, phase19_11, phase19_20, phase19_21]
  try simp only [star_one, star_neg]
  ring
theorem v20_22 (t : ℂ) : (momentPoly 20 z20 2 2).eval t = (780 + (-1444) * t ^ 2 + (834547 / 1200) * t ^ 4 + (-64207 / 600) * t ^ 6 + (91867 / 1200) * t ^ 8) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_01, v19_02, v19_10, v19_11, v19_12, v19_20, v19_21, v19_22]
  try simp only [phase19_00, phase19_01, phase19_02, phase19_10, phase19_11, phase19_12, phase19_20, phase19_21, phase19_22]
  try simp only [star_one, star_neg]
  ring
theorem v20_23 (t : ℂ) : (momentPoly 20 z20 2 3).eval t = (2224 * t + (-93351 / 20) * t ^ 3 + (6070753 / 2000) * t ^ 5 + (-361393 / 400) * t ^ 7 + (79939 / 250) * t ^ 9 + (53959 / 2000) * t ^ 11 + (-68159 / 2000) * t ^ 13 + (2701 / 5) * alpha * t ^ 3 + (-12960269 / 12000) * alpha * t ^ 5 + (2815381 / 4800) * alpha * t ^ 7 + (-475249 / 8000) * alpha * t ^ 9 + (-95823 / 8000) * alpha * t ^ 11 + (592049 / 24000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_01, v19_02, v19_03, v19_10, v19_11, v19_12, v19_13, v19_20, v19_21, v19_22, v19_23]
  try simp only [phase19_00, phase19_01, phase19_02, phase19_03, phase19_10, phase19_11, phase19_12, phase19_13, phase19_20, phase19_21, phase19_22, phase19_23]
  try simp only [star_one, star_neg]
  ring
theorem v20_24 (t : ℂ) : (momentPoly 20 z20 2 4).eval t = ((-170991 / 10) * t ^ 2 + (208419 / 4) * t ^ 4 + (-12469518221 / 240000) * t ^ 6 + (1404568841 / 80000) * t ^ 8 + (-193351151 / 96000) * t ^ 10 + (1943965549 / 1440000) * t ^ 12 + (18870911 / 360000) * t ^ 14 + (72545651 / 1440000) * t ^ 18 + (-63553391 / 1440000) * t ^ 20 + (308206 / 15) * alpha * t ^ 2 + (-1404031 / 25) * alpha * t ^ 4 + (992334827 / 20000) * alpha * t ^ 6 + (-906617093 / 60000) * alpha * t ^ 8 + (76668983 / 24000) * alpha * t ^ 10 + (-232432243 / 120000) * alpha * t ^ 12 + (-3230569 / 22500) * alpha * t ^ 14 + (-7085717 / 120000) * alpha * t ^ 18 + (18986311 / 360000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_01, v19_02, v19_03, v19_04, v19_10, v19_11, v19_12, v19_13, v19_14, v19_20, v19_21, v19_22, v19_23, v19_24]
  try simp only [phase19_00, phase19_01, phase19_02, phase19_03, phase19_04, phase19_10, phase19_11, phase19_12, phase19_13, phase19_14, phase19_20, phase19_21, phase19_22, phase19_23, phase19_24]
  try simp only [star_one, star_neg]
  ring
theorem v20_30 (t : ℂ) : (momentPoly 20 z20 3 0).eval t = ((-203 / 20) * t ^ 3 + (183 / 20) * t ^ 5 + 2 * t ^ 9 + (-4103 / 200) * alpha * t ^ 3 + (9389 / 400) * alpha * t ^ 5 + (-1183 / 400) * alpha * t ^ 9) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_10, v19_20, v19_30]
  try simp only [phase19_00, phase19_10, phase19_20, phase19_30]
  try simp only [star_one, star_neg]
  ring
theorem v20_31 (t : ℂ) : (momentPoly 20 z20 3 1).eval t = ((-4617 / 20) * t ^ 2 + (10029 / 20) * t ^ 4 + (-5331 / 20) * t ^ 6 + (-61 / 20) * t ^ 10 + (-1387 / 5) * alpha * t ^ 2 + (314731 / 600) * alpha * t ^ 4 + (-95731 / 400) * alpha * t ^ 6 + (-9389 / 1200) * alpha * t ^ 10) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_01, v19_10, v19_11, v19_20, v19_21, v19_30, v19_31]
  try simp only [phase19_00, phase19_01, phase19_10, phase19_11, phase19_20, phase19_21, phase19_30, phase19_31]
  try simp only [star_one, star_neg]
  ring
theorem v20_32 (t : ℂ) : (momentPoly 20 z20 3 2).eval t = (2224 * t + (-93351 / 20) * t ^ 3 + (6070753 / 2000) * t ^ 5 + (-361393 / 400) * t ^ 7 + (79939 / 250) * t ^ 9 + (53959 / 2000) * t ^ 11 + (-68159 / 2000) * t ^ 13 + (-2701 / 5) * alpha * t ^ 3 + (12960269 / 12000) * alpha * t ^ 5 + (-2815381 / 4800) * alpha * t ^ 7 + (475249 / 8000) * alpha * t ^ 9 + (95823 / 8000) * alpha * t ^ 11 + (-592049 / 24000) * alpha * t ^ 13) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_01, v19_02, v19_10, v19_11, v19_12, v19_20, v19_21, v19_22, v19_30, v19_31, v19_32]
  try simp only [phase19_00, phase19_01, phase19_02, phase19_10, phase19_11, phase19_12, phase19_20, phase19_21, phase19_22, phase19_30, phase19_31, phase19_32]
  try simp only [star_one, star_neg]
  ring
theorem v20_33 (t : ℂ) : (momentPoly 20 z20 3 3).eval t = (44480 + (-120327) * t ^ 2 + (22532769 / 200) * t ^ 4 + (-2112997873 / 40000) * t ^ 6 + (1038119399 / 40000) * t ^ 8 + (-1579734837 / 160000) * t ^ 10 + (25778947 / 40000) * t ^ 12 + (-58020361 / 80000) * t ^ 14 + (1638467 / 160000) * t ^ 18) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_01, v19_02, v19_03, v19_10, v19_11, v19_12, v19_13, v19_20, v19_21, v19_22, v19_23, v19_30, v19_31, v19_32, v19_33]
  try simp only [phase19_00, phase19_01, phase19_02, phase19_03, phase19_10, phase19_11, phase19_12, phase19_13, phase19_20, phase19_21, phase19_22, phase19_23, phase19_30, phase19_31, phase19_32, phase19_33]
  try simp only [star_one, star_neg]
  ring
theorem v20_34 (t : ℂ) : (momentPoly 20 z20 3 4).eval t = (164807 * t + (-5048523 / 10) * t ^ 3 + (118341723 / 200) * t ^ 5 + (-156301697353 / 400000) * t ^ 7 + (82807185923 / 400000) * t ^ 9 + (-54462018691 / 800000) * t ^ 11 + (-3148497643 / 480000) * t ^ 13 + (5083653889 / 600000) * t ^ 15 + (-87809619 / 50000) * t ^ 17 + (98098409 / 800000) * t ^ 19 + (-425791027 / 2400000) * t ^ 21 + (14724853 / 300000) * t ^ 25 + (292146 / 5) * alpha * t ^ 3 + (-68745963 / 400) * alpha * t ^ 5 + (142583223663 / 800000) * alpha * t ^ 7 + (-385182231403 / 4800000) * alpha * t ^ 9 + (75454629973 / 4800000) * alpha * t ^ 11 + (29981672491 / 5760000) * alpha * t ^ 13 + (-553755497 / 100000) * alpha * t ^ 15 + (1513693559 / 9600000) * alpha * t ^ 17 + (-302488949 / 1600000) * alpha * t ^ 19 + (993213859 / 9600000) * alpha * t ^ 21 + (-184767779 / 28800000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_01, v19_02, v19_03, v19_04, v19_10, v19_11, v19_12, v19_13, v19_14, v19_20, v19_21, v19_22, v19_23, v19_24, v19_30, v19_31, v19_32, v19_33, v19_34]
  try simp only [phase19_00, phase19_01, phase19_02, phase19_03, phase19_04, phase19_10, phase19_11, phase19_12, phase19_13, phase19_14, phase19_20, phase19_21, phase19_22, phase19_23, phase19_24, phase19_30, phase19_31, phase19_32, phase19_33, phase19_34]
  try simp only [star_one, star_neg]
  ring
theorem v20_40 (t : ℂ) : (momentPoly 20 z20 4 0).eval t = ((-724481 / 4000) * t ^ 4 + (683881 / 2000) * t ^ 6 + (-1217891 / 8000) * t ^ 8 + (-25557 / 2000) * t ^ 10 + (41557 / 8000) * t ^ 16 + (45541 / 375) * alpha * t ^ 4 + (-425873 / 1500) * alpha * t ^ 6 + (120661 / 750) * alpha * t ^ 8 + (27293 / 4500) * alpha * t ^ 10 + (-5033 / 1125) * alpha * t ^ 16) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_10, v19_20, v19_30, v19_40]
  try simp only [phase19_00, phase19_10, phase19_20, phase19_30, phase19_40]
  try simp only [star_one, star_neg]
  ring
theorem v20_41 (t : ℂ) : (momentPoly 20 z20 4 1).eval t = ((-7511 / 10) * t ^ 3 + (4793519 / 4000) * t ^ 5 + (-511919 / 2000) * t ^ 7 + (-132291 / 8000) * t ^ 9 + (-353957 / 2000) * t ^ 11 + (25557 / 8000) * t ^ 17 + (-151811 / 100) * alpha * t ^ 3 + (9854173 / 3000) * alpha * t ^ 5 + (-694067 / 375) * alpha * t ^ 7 + (-682747 / 6000) * alpha * t ^ 9 + (897923 / 4500) * alpha * t ^ 11 + (-27293 / 18000) * alpha * t ^ 17) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_01, v19_10, v19_11, v19_20, v19_21, v19_30, v19_31, v19_40, v19_41]
  try simp only [phase19_00, phase19_01, phase19_10, phase19_11, phase19_20, phase19_21, phase19_30, phase19_31, phase19_40, phase19_41]
  try simp only [star_one, star_neg]
  ring
theorem v20_42 (t : ℂ) : (momentPoly 20 z20 4 2).eval t = ((-170991 / 10) * t ^ 2 + (208419 / 4) * t ^ 4 + (-12469518221 / 240000) * t ^ 6 + (1404568841 / 80000) * t ^ 8 + (-193351151 / 96000) * t ^ 10 + (1943965549 / 1440000) * t ^ 12 + (18870911 / 360000) * t ^ 14 + (72545651 / 1440000) * t ^ 18 + (-63553391 / 1440000) * t ^ 20 + (-308206 / 15) * alpha * t ^ 2 + (1404031 / 25) * alpha * t ^ 4 + (-992334827 / 20000) * alpha * t ^ 6 + (906617093 / 60000) * alpha * t ^ 8 + (-76668983 / 24000) * alpha * t ^ 10 + (232432243 / 120000) * alpha * t ^ 12 + (3230569 / 22500) * alpha * t ^ 14 + (7085717 / 120000) * alpha * t ^ 18 + (-18986311 / 360000) * alpha * t ^ 20) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_01, v19_02, v19_10, v19_11, v19_12, v19_20, v19_21, v19_22, v19_30, v19_31, v19_32, v19_40, v19_41, v19_42]
  try simp only [phase19_00, phase19_01, phase19_02, phase19_10, phase19_11, phase19_12, phase19_20, phase19_21, phase19_22, phase19_30, phase19_31, phase19_32, phase19_40, phase19_41, phase19_42]
  try simp only [star_one, star_neg]
  ring
theorem v20_43 (t : ℂ) : (momentPoly 20 z20 4 3).eval t = (164807 * t + (-5048523 / 10) * t ^ 3 + (118341723 / 200) * t ^ 5 + (-156301697353 / 400000) * t ^ 7 + (82807185923 / 400000) * t ^ 9 + (-54462018691 / 800000) * t ^ 11 + (-3148497643 / 480000) * t ^ 13 + (5083653889 / 600000) * t ^ 15 + (-87809619 / 50000) * t ^ 17 + (98098409 / 800000) * t ^ 19 + (-425791027 / 2400000) * t ^ 21 + (14724853 / 300000) * t ^ 25 + (-292146 / 5) * alpha * t ^ 3 + (68745963 / 400) * alpha * t ^ 5 + (-142583223663 / 800000) * alpha * t ^ 7 + (385182231403 / 4800000) * alpha * t ^ 9 + (-75454629973 / 4800000) * alpha * t ^ 11 + (-29981672491 / 5760000) * alpha * t ^ 13 + (553755497 / 100000) * alpha * t ^ 15 + (-1513693559 / 9600000) * alpha * t ^ 17 + (302488949 / 1600000) * alpha * t ^ 19 + (-993213859 / 9600000) * alpha * t ^ 21 + (184767779 / 28800000) * alpha * t ^ 25) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_01, v19_02, v19_03, v19_10, v19_11, v19_12, v19_13, v19_20, v19_21, v19_22, v19_23, v19_30, v19_31, v19_32, v19_33, v19_40, v19_41, v19_42, v19_43]
  try simp only [phase19_00, phase19_01, phase19_02, phase19_03, phase19_10, phase19_11, phase19_12, phase19_13, phase19_20, phase19_21, phase19_22, phase19_23, phase19_30, phase19_31, phase19_32, phase19_33, phase19_40, phase19_41, phase19_42, phase19_43]
  try simp only [star_one, star_neg]
  ring
theorem v20_44 (t : ℂ) : (momentPoly 20 z20 4 4).eval t = (3296140 + (-11579816) * t ^ 2 + (790316009 / 50) * t ^ 4 + (-7555246854 / 625) * t ^ 6 + (363756018593027 / 48000000) * t ^ 8 + (-48120460006987 / 12000000) * t ^ 10 + (2383228239677 / 1920000) * t ^ 12 + (-32391666341257 / 72000000) * t ^ 14 + (106399306081777 / 576000000) * t ^ 16 + (1588231012327 / 72000000) * t ^ 18 + (-3611479549163 / 432000000) * t ^ 20 + (1059597939157 / 72000000) * t ^ 22 + (-1963807419607 / 288000000) * t ^ 24 + (-48705005587 / 216000000) * t ^ 26 + (115824715267 / 1728000000) * t ^ 32) := by
  rw [momentPoly]
  simp only [z20, Fin.init_snoc, Fin.snoc_last, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, chargeSq]
  simp only [v19_00, v19_01, v19_02, v19_03, v19_04, v19_10, v19_11, v19_12, v19_13, v19_14, v19_20, v19_21, v19_22, v19_23, v19_24, v19_30, v19_31, v19_32, v19_33, v19_34, v19_40, v19_41, v19_42, v19_43, v19_44]
  try simp only [phase19_00, phase19_01, phase19_02, phase19_03, phase19_04, phase19_10, phase19_11, phase19_12, phase19_13, phase19_14, phase19_20, phase19_21, phase19_22, phase19_23, phase19_24, phase19_30, phase19_31, phase19_32, phase19_33, phase19_34, phase19_40, phase19_41, phase19_42, phase19_43, phase19_44]
  try simp only [star_one, star_neg]
  ring
#print axioms v20_00
#print axioms v20_11
#print axioms v20_22
#print axioms v20_33
#print axioms v20_44
end PhotonCertA
