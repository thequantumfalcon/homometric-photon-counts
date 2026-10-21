import PhotonPoissonMixture
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Concrete phase geometry. These are finite complex-algebra theorems,
not a Gaussian expectation or an experimental validation. -/
namespace PhotonGeometry

set_option maxHeartbeats 2000000

noncomputable def alpha : ℂ := Complex.I * (Real.sqrt 3 : ℂ)
noncomputable def c : ℂ := (Real.sqrt 222 : ℂ)
noncomputable def d : ℂ := (Real.sqrt 573 : ℂ)
noncomputable def r : ℂ := (1 + alpha) / 2
noncomputable def thetaPlus : ℂ := r * (c + alpha) / 15
noncomputable def thetaMinus : ℂ := r * (-c + alpha) / 15
noncomputable def phiPlus : ℂ := (d - alpha) / 24
noncomputable def phiMinus : ℂ := (-d - alpha) / 24

noncomputable def base : List ℂ :=
  List.replicate 5 thetaPlus ++ List.replicate 5 thetaMinus ++
  List.replicate 4 phiPlus ++ List.replicate 4 phiMinus ++ [1, 1, -1]
noncomputable def rotate (z : ℂ) (zs : List ℂ) := zs.map (z * ·)
noncomputable def geometryA := base ++ rotate r base ++ rotate (r ^ 3) base
noncomputable def geometryB := base ++ rotate (r ^ 2) base ++ rotate (r ^ 3) base
noncomputable def harmonic (zs : List ℂ) (k : ℕ) : ℂ := (zs.map (· ^ k)).sum

theorem alpha_sq : alpha ^ 2 = -3 := by
  norm_num [alpha, mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt]
theorem c_sq : c ^ 2 = 222 := by
  norm_num [c, ← Complex.ofReal_pow, Real.sq_sqrt]
theorem d_sq : d ^ 2 = 573 := by
  norm_num [d, ← Complex.ofReal_pow, Real.sq_sqrt]

theorem geometry_sizes : base.length = 21 ∧ geometryA.length = 63 ∧
    geometryB.length = 63 := by
  norm_num [base, geometryA, geometryB, rotate]

theorem harmonic_append (xs ys : List ℂ) (k : ℕ) :
    harmonic (xs ++ ys) k = harmonic xs k + harmonic ys k := by
  simp [harmonic]
theorem harmonic_rotate (z : ℂ) (zs : List ℂ) (k : ℕ) :
    harmonic (rotate z zs) k = z ^ k * harmonic zs k := by
  simp [harmonic, rotate, List.map_map, Function.comp_def, mul_pow, List.sum_map_mul_left]
theorem harmonic_base (k : ℕ) : harmonic base k =
    5 * thetaPlus ^ k + 5 * thetaMinus ^ k + 4 * phiPlus ^ k +
      4 * phiMinus ^ k + 2 + (-1) ^ k := by
  simp [harmonic, base]
  ring

theorem base_h1 : harmonic base 1 = 0 := by
  rw [harmonic_base]
  unfold thetaPlus thetaMinus phiPlus phiMinus r
  linear_combination (1 / 3) * alpha_sq

theorem base_h2 : harmonic base 2 = ((121 / 20) + ((73 / 15) * alpha)) := by
  rw [harmonic_base]
  unfold thetaPlus thetaMinus phiPlus phiMinus r
  linear_combination ((-1 / 120) + ((1 / 45) * alpha) + ((1 / 90) * (alpha ^ 2)) + ((1 / 90) * (c ^ 2))) * alpha_sq + ((-1 / 45) + ((1 / 45) * alpha)) * c_sq + (1 / 72) * d_sq

theorem base_h3 : harmonic base 3 = (1 + ((-1183 / 400) * alpha)) := by
  rw [harmonic_base]
  unfold thetaPlus thetaMinus phiPlus phiMinus r
  linear_combination (((-17 / 4800) * alpha) + ((1 / 900) * (alpha ^ 3)) + ((1 / 2700) * (alpha ^ 4)) + ((1 / 300) * alpha * (c ^ 2)) + ((1 / 900) * (alpha ^ 2) * (c ^ 2))) * alpha_sq + ((-2 / 225) * alpha) * c_sq + ((-1 / 576) * alpha) * d_sq

theorem base_h4 : harmonic base 4 = ((49557 / 8000) + ((-5033 / 1125) * alpha)) := by
  rw [harmonic_base]
  unfold thetaPlus thetaMinus phiPlus phiMinus r
  linear_combination ((43 / 192000) + ((-43 / 576000) * (alpha ^ 2)) + ((-2 / 3375) * (c ^ 2)) + ((-1 / 10125) * (alpha ^ 3)) + ((1 / 3375) * alpha) + ((1 / 6912) * (d ^ 2)) + ((1 / 20250) * (alpha ^ 5)) + ((1 / 27000) * (alpha ^ 4)) + ((1 / 27000) * (c ^ 4)) + ((1 / 81000) * (alpha ^ 6)) + ((-2 / 3375) * alpha * (c ^ 2)) + ((1 / 3375) * (alpha ^ 3) * (c ^ 2)) + ((1 / 4500) * (alpha ^ 2) * (c ^ 2)) + ((1 / 13500) * (alpha ^ 4) * (c ^ 2)) + ((1 / 20250) * alpha * (c ^ 4)) + ((1 / 81000) * (alpha ^ 2) * (c ^ 4))) * alpha_sq + ((-68 / 3375) + ((-68 / 3375) * alpha) + ((-1 / 10125) * (c ^ 2)) + ((-1 / 10125) * alpha * (c ^ 2))) * c_sq + ((185 / 13824) + ((1 / 41472) * (d ^ 2))) * d_sq

theorem base_h5 : harmonic base 5 = ((32266 / 5625) + ((-76843 / 1440000) * alpha)) := by
  rw [harmonic_base]
  unfold thetaPlus thetaMinus phiPlus phiMinus r
  linear_combination ((-1 / 16875) + ((-1157 / 69120000) * alpha) + ((-1 / 30375) * (c ^ 4)) + ((-1 / 151875) * (alpha ^ 4)) + ((-1 / 486000) * (alpha ^ 5)) + ((1 / 50625) * (alpha ^ 2)) + ((1 / 486000) * (alpha ^ 7)) + ((1 / 2430000) * (alpha ^ 8)) + ((2 / 10125) * (c ^ 2)) + ((7 / 2430000) * (alpha ^ 6)) + ((1157 / 207360000) * (alpha ^ 3)) + ((-5 / 497664) * alpha * (d ^ 2)) + ((-2 / 30375) * (alpha ^ 2) * (c ^ 2)) + ((-1 / 48600) * (alpha ^ 3) * (c ^ 2)) + ((-1 / 97200) * alpha * (c ^ 4)) + ((1 / 48600) * (alpha ^ 5) * (c ^ 2)) + ((1 / 97200) * (alpha ^ 3) * (c ^ 4)) + ((1 / 243000) * (alpha ^ 6) * (c ^ 2)) + ((1 / 486000) * (alpha ^ 4) * (c ^ 4)) + ((2 / 30375) * alpha * (c ^ 2)) + ((7 / 243000) * (alpha ^ 4) * (c ^ 2)) + ((7 / 486000) * (alpha ^ 2) * (c ^ 4))) * alpha_sq + ((8 / 375) + ((1 / 10125) * (c ^ 2)) + ((8 / 1125) * alpha) + ((1 / 30375) * alpha * (c ^ 2))) * c_sq + (((-35 / 12288) * alpha) + ((-5 / 995328) * alpha * (d ^ 2))) * d_sq

theorem A_h1 : harmonic geometryA 1 = 0 := by
  simp only [geometryA, harmonic_append, harmonic_rotate, base_h1]
  unfold r
  ring

theorem A_h2 : harmonic geometryA 2 = ((71 / 40) + ((413 / 40) * alpha)) := by
  simp only [geometryA, harmonic_append, harmonic_rotate, base_h2]
  unfold r
  linear_combination ((7529 / 3840) + ((-367 / 1920) * alpha) + ((73 / 960) * (alpha ^ 5)) + ((141 / 256) * (alpha ^ 4)) + ((247 / 192) * (alpha ^ 2)) + ((947 / 640) * (alpha ^ 3))) * alpha_sq

theorem A_h3 : harmonic geometryA 3 = ((-1) + ((1183 / 400) * alpha)) := by
  simp only [geometryA, harmonic_append, harmonic_rotate, base_h3]
  unfold r
  linear_combination ((363 / 512) + ((-402629 / 204800) * alpha) + ((-97261 / 204800) * (alpha ^ 2)) + ((-54231 / 204800) * (alpha ^ 5)) + ((-35439 / 204800) * (alpha ^ 6)) + ((-10247 / 204800) * (alpha ^ 7)) + ((-9141 / 204800) * (alpha ^ 4)) + ((-1183 / 204800) * (alpha ^ 8)) + ((12807 / 40960) * (alpha ^ 3))) * alpha_sq

theorem A_h4 : harmonic geometryA 4 = ((123901 / 48000) + ((-470783 / 48000) * alpha)) := by
  simp only [geometryA, harmonic_append, harmonic_rotate, base_h4]
  unfold r
  linear_combination ((78683123 / 58982400) + ((-31169789 / 294912000) * (alpha ^ 8)) + ((-5099879 / 7372800) * (alpha ^ 3)) + ((-4203607 / 294912000) * (alpha ^ 2)) + ((-1139777 / 16384000) * (alpha ^ 4)) + ((-1139777 / 98304000) * (alpha ^ 10)) + ((-45833 / 819200) * (alpha ^ 7)) + ((-16601 / 327680) * (alpha ^ 9)) + ((-5033 / 4608000) * (alpha ^ 11)) + ((2189801 / 6144000) * (alpha ^ 5)) + ((9862183 / 49152000) * (alpha ^ 6)) + ((54233519 / 24576000) * alpha)) * alpha_sq

theorem A_h5 : harmonic geometryA 5 = ((8029567 / 2880000) + ((-8336939 / 2880000) * alpha)) := by
  simp only [geometryA, harmonic_append, harmonic_rotate, base_h5]
  unfold r
  linear_combination ((3843151 / 3686400) + ((-76843 / 47185920000) * (alpha ^ 14)) + ((7107451 / 47185920000) * (alpha ^ 13)) + ((19343909 / 7864320000) * (alpha ^ 12)) + ((114815987 / 629145600) * (alpha ^ 9)) + ((150136987 / 471859200) * (alpha ^ 7)) + ((151075171 / 524288000) * (alpha ^ 4)) + ((405512081 / 23592960000) * (alpha ^ 11)) + ((1545604489 / 9437184000) * (alpha ^ 5)) + ((2390918101 / 9437184000) * (alpha ^ 2)) + ((3048396481 / 15728640000) * (alpha ^ 6)) + ((3305262623 / 47185920000) * (alpha ^ 10)) + ((3626170301 / 11796480000) * (alpha ^ 8)) + ((4790506201 / 23592960000) * (alpha ^ 3)) + ((58803748679 / 47185920000) * alpha)) * alpha_sq

theorem B_h1 : harmonic geometryB 1 = 0 := by
  simp only [geometryB, harmonic_append, harmonic_rotate, base_h1]
  unfold r
  ring

theorem B_h2 : harmonic geometryB 2 = ((131 / 8) + ((171 / 40) * alpha)) := by
  simp only [geometryB, harmonic_append, harmonic_rotate, base_h2]
  unfold r
  linear_combination ((-12611 / 3840) + ((73 / 960) * (alpha ^ 5)) + ((141 / 256) * (alpha ^ 4)) + ((461 / 160) * (alpha ^ 2)) + ((651 / 640) * alpha) + ((685 / 384) * (alpha ^ 3))) * alpha_sq

theorem B_h3 : harmonic geometryB 3 = (1 + ((-1183 / 400) * alpha)) := by
  simp only [geometryB, harmonic_append, harmonic_rotate, base_h3]
  unfold r
  linear_combination ((3 / 512) + ((-35439 / 204800) * (alpha ^ 6)) + ((-30333 / 204800) * (alpha ^ 3)) + ((-12739 / 40960) * (alpha ^ 5)) + ((-10247 / 204800) * (alpha ^ 7)) + ((-2509 / 8192) * (alpha ^ 4)) + ((-2077 / 204800) * (alpha ^ 2)) + ((-1183 / 204800) * (alpha ^ 8)) + ((4051 / 204800) * alpha)) * alpha_sq

theorem B_h4 : harmonic geometryB 4 = ((6145 / 384) + ((-173441 / 48000) * alpha)) := by
  simp only [geometryB, harmonic_append, harmonic_rotate, base_h4]
  unfold r
  linear_combination ((-961636177 / 294912000) + ((-31169789 / 294912000) * (alpha ^ 8)) + ((-16398611 / 73728000) * alpha) + ((-2706709 / 36864000) * (alpha ^ 7)) + ((-1139777 / 98304000) * (alpha ^ 10)) + ((-703213 / 29491200) * (alpha ^ 4)) + ((-16601 / 327680) * (alpha ^ 9)) + ((-5033 / 4608000) * (alpha ^ 11)) + ((2084707 / 18432000) * (alpha ^ 5)) + ((2507897 / 29491200) * (alpha ^ 6)) + ((16574141 / 36864000) * (alpha ^ 3)) + ((127310131 / 98304000) * (alpha ^ 2))) * alpha_sq

theorem B_h5 : harmonic geometryB 5 = ((-13585 / 4608) + ((-2727751 / 960000) * alpha)) := by
  simp only [geometryB, harmonic_append, harmonic_rotate, base_h5]
  unfold r
  linear_combination ((266959511 / 92160000) + ((-41315721239 / 47185920000) * (alpha ^ 2)) + ((-523071341 / 7864320000) * (alpha ^ 3)) + ((-76843 / 47185920000) * (alpha ^ 14)) + ((7107451 / 47185920000) * (alpha ^ 13)) + ((19343909 / 7864320000) * (alpha ^ 12)) + ((405512081 / 23592960000) * (alpha ^ 11)) + ((1462804369 / 3932160000) * (alpha ^ 7)) + ((3305262623 / 47185920000) * (alpha ^ 10)) + ((3686103629 / 11796480000) * (alpha ^ 8)) + ((6675150209 / 15728640000) * (alpha ^ 6)) + ((8608740049 / 47185920000) * (alpha ^ 9)) + ((17961426119 / 23592960000) * (alpha ^ 4)) + ((31310544941 / 47185920000) * (alpha ^ 5)) + ((44773674023 / 47185920000) * alpha)) * alpha_sq

theorem star_alpha : star alpha = -alpha := by
  simp [alpha]
theorem star_c : star c = c := by simp [c]
theorem star_d : star d = d := by simp [d]

theorem r_unit : r * star r = 1 := by
  simp only [r, star_div₀, star_add, star_alpha, star_one, star_ofNat]
  linear_combination (-1 / 4) * alpha_sq

theorem thetaPlus_unit : thetaPlus * star thetaPlus = 1 := by
  simp only [thetaPlus, r, star_div₀, star_add, star_mul, star_alpha, star_c, star_one, star_ofNat]
  linear_combination ((-1 / 225) + ((-1 / 900) * (c ^ 2)) + ((1 / 900) * (alpha ^ 2))) * alpha_sq + (1 / 225) * c_sq

theorem thetaMinus_unit : thetaMinus * star thetaMinus = 1 := by
  simp only [thetaMinus, r, star_div₀, star_add, star_neg, star_mul, star_alpha, star_c, star_one, star_ofNat]
  linear_combination ((-1 / 225) + ((-1 / 900) * (c ^ 2)) + ((1 / 900) * (alpha ^ 2))) * alpha_sq + (1 / 225) * c_sq

theorem phiPlus_unit : phiPlus * star phiPlus = 1 := by
  simp only [phiPlus, star_div₀, star_sub, star_alpha, star_d, star_ofNat]
  linear_combination (-1 / 576) * alpha_sq + (1 / 576) * d_sq

theorem phiMinus_unit : phiMinus * star phiMinus = 1 := by
  simp only [phiMinus, star_div₀, star_sub, star_neg, star_alpha, star_d, star_ofNat]
  linear_combination (-1 / 576) * alpha_sq + (1 / 576) * d_sq

theorem base_unit : ∀ z ∈ base, z * star z = 1 := by
  intro z hz
  simp only [base, List.mem_append, List.mem_replicate, List.mem_cons,
    List.not_mem_nil, or_false] at hz
  rcases hz with (((⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | rfl | rfl | rfl
  · exact thetaPlus_unit
  · exact thetaMinus_unit
  · exact phiPlus_unit
  · exact phiMinus_unit
  · simp
  · simp
  · simp

theorem unit_mul (z w : ℂ) (hz : z * star z = 1) (hw : w * star w = 1) :
    (z * w) * star (z * w) = 1 := by
  calc
    _ = (z * star z) * (w * star w) := by rw [star_mul]; ring
    _ = 1 := by rw [hz, hw]; norm_num

theorem unit_pow (z : ℂ) (hz : z * star z = 1) (k : ℕ) :
    z ^ k * star (z ^ k) = 1 := by
  rw [star_pow, ← mul_pow, hz, one_pow]

theorem rotate_unit (z : ℂ) (zs : List ℂ) (hz : z * star z = 1)
    (hs : ∀ w ∈ zs, w * star w = 1) : ∀ w ∈ rotate z zs, w * star w = 1 := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
  exact unit_mul z v hz (hs v hv)

theorem geometry_unit : (∀ z ∈ geometryA, z * star z = 1) ∧
    (∀ z ∈ geometryB, z * star z = 1) := by
  constructor <;> intro z hz
  · simp only [geometryA, List.mem_append] at hz
    rcases hz with (h | h) | h
    · exact base_unit z h
    · exact rotate_unit r base r_unit base_unit z h
    · exact rotate_unit (r ^ 3) base (unit_pow r r_unit 3) base_unit z h
  · simp only [geometryB, List.mem_append] at hz
    rcases hz with (h | h) | h
    · exact base_unit z h
    · exact rotate_unit (r ^ 2) base (unit_pow r r_unit 2) base_unit z h
    · exact rotate_unit (r ^ 3) base (unit_pow r r_unit 3) base_unit z h

theorem harmonic_norm_match_1 :
    harmonic geometryA 1 * star (harmonic geometryA 1) =
      harmonic geometryB 1 * star (harmonic geometryB 1) := by
  rw [A_h1, B_h1]

theorem harmonic_norm_match_2 :
    harmonic geometryA 2 * star (harmonic geometryA 2) =
      harmonic geometryB 2 * star (harmonic geometryB 2) := by
  rw [A_h2, B_h2]
  simp only [star_add, star_mul, star_div₀, star_ofNat, star_alpha]
  linear_combination (-8833 / 100) * alpha_sq

theorem harmonic_norm_match_3 :
    harmonic geometryA 3 * star (harmonic geometryA 3) =
      harmonic geometryB 3 * star (harmonic geometryB 3) := by
  rw [A_h3, B_h3]
  simp only [star_add, star_mul, star_div₀, star_neg, star_ofNat, star_alpha]
  ring

theorem harmonic_norm_match_4 :
    harmonic geometryA 4 * star (harmonic geometryA 4) =
      harmonic geometryB 4 * star (harmonic geometryB 4) := by
  rw [A_h4, B_h4]
  simp only [star_add, star_mul, star_div₀, star_neg, star_ofNat, star_alpha]
  linear_combination (-83140127 / 1000000) * alpha_sq

theorem harmonic_norm_match_5 :
    harmonic geometryA 5 * star (harmonic geometryA 5) =
      harmonic geometryB 5 * star (harmonic geometryB 5) := by
  rw [A_h5, B_h5]
  simp only [star_add, star_mul, star_div₀, star_neg, star_ofNat, star_alpha]
  linear_combination (-1239708119 / 4050000000) * alpha_sq

theorem A_invariant : harmonic geometryA 4 * (star (harmonic geometryA 2)) ^ 2 =
    ((-455015761 / 240000) + ((28907930179 / 9600000) * alpha)) := by
  rw [A_h4, A_h2]
  simp only [star_add, star_mul, star_div₀, star_ofNat, star_alpha]
  linear_combination ((48743209487 / 76800000) + ((-80300985527 / 76800000) * alpha)) * alpha_sq

theorem B_invariant : harmonic geometryB 4 * (star (harmonic geometryB 2)) ^ 2 =
    ((455015761 / 240000) + ((-28907930179 / 9600000) * alpha)) := by
  rw [B_h4, B_h2]
  simp only [star_add, star_mul, star_div₀, star_ofNat, star_alpha]
  linear_combination ((4087550769 / 5120000) + ((-1690529427 / 25600000) * alpha)) * alpha_sq

theorem invariant_real_gap :
    (harmonic geometryA 4 * (star (harmonic geometryA 2)) ^ 2).re -
    (harmonic geometryB 4 * (star (harmonic geometryB 2)) ^ 2).re =
      -(455015761 / 120000 : ℝ) := by
  rw [A_invariant, B_invariant]
  norm_num [alpha, Complex.mul_re, Complex.mul_im]

theorem gaussian_parameter_square (s : ℝ) :
    (Real.exp (-s / 2)) ^ 2 = Real.exp (-s) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem gap_parameter_substitution (s : ℝ) :
    let t := Real.exp (-s / 2)
    PhotonAlgebra.delta4 (Real.exp (-s)) =
      (455015761 / 20000 : ℝ) * t ^ 8 * (1 - t ^ 2) ^ 5 *
        (t ^ 6 + 3 * t ^ 4 + 6 * t ^ 2 + 6) := by
  dsimp
  rw [← gaussian_parameter_square s]
  unfold PhotonAlgebra.delta4
  ring

#print axioms geometry_sizes
#print axioms geometry_unit
#print axioms invariant_real_gap
#print axioms gaussian_parameter_square
#print axioms gap_parameter_substitution
#print axioms A_h1
#print axioms A_h2
#print axioms A_h3
#print axioms A_h4
#print axioms A_h5
#print axioms B_h1
#print axioms B_h2
#print axioms B_h3
#print axioms B_h4
#print axioms B_h5
#print axioms harmonic_norm_match_1
#print axioms harmonic_norm_match_2
#print axioms harmonic_norm_match_3
#print axioms harmonic_norm_match_4
#print axioms harmonic_norm_match_5

end PhotonGeometry
