import PhotonGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Exact symbolic coordinates and their complex phases. Decimal display
coordinates are not substituted for these real-valued expressions. -/
namespace PhotonCoordinates

open PhotonGeometry

set_option maxHeartbeats 4000000

noncomputable def theta : ℝ := Real.arcsin (1 / (5 * Real.sqrt 3))
noncomputable def phi : ℝ := -Real.arcsin (1 / (8 * Real.sqrt 3))
noncomputable def coordinate (base : ℕ) (angle : ℝ) : ℝ :=
  (base : ℝ) + 3 * angle / Real.pi
noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (((Real.pi * x / 3 : ℝ) : ℂ) * Complex.I)

theorem sqrt3_pos : 0 < Real.sqrt 3 := by positivity
theorem sqrt3_sq : (Real.sqrt 3) ^ 2 = 3 := by norm_num [Real.sq_sqrt]

theorem theta_argument : 1 / (5 * Real.sqrt 3) = Real.sqrt 3 / 15 := by
  field_simp
  nlinarith [sqrt3_sq]

theorem phi_argument : 1 / (8 * Real.sqrt 3) = Real.sqrt 3 / 24 := by
  field_simp
  nlinarith [sqrt3_sq]

theorem theta_sin : Real.sin theta = Real.sqrt 3 / 15 := by
  unfold theta
  rw [theta_argument]
  apply Real.sin_arcsin <;> nlinarith [sqrt3_pos, sqrt3_sq]

theorem theta_cos : Real.cos theta = Real.sqrt 222 / 15 := by
  have hpos : 0 ≤ Real.cos theta := Real.cos_arcsin_nonneg _
  have hsq := Real.sin_sq_add_cos_sq theta
  rw [theta_sin] at hsq
  have hc : (Real.sqrt 222) ^ 2 = 222 := by norm_num [Real.sq_sqrt]
  have hcpos : 0 ≤ Real.sqrt 222 := Real.sqrt_nonneg _
  nlinarith [sqrt3_sq]

theorem phi_sin : Real.sin phi = -Real.sqrt 3 / 24 := by
  unfold phi
  rw [Real.sin_neg, phi_argument, Real.sin_arcsin]
  · ring
  · nlinarith [sqrt3_pos, sqrt3_sq]
  · nlinarith [sqrt3_pos, sqrt3_sq]

theorem phi_cos : Real.cos phi = Real.sqrt 573 / 24 := by
  have hpos : 0 ≤ Real.cos phi := by
    simpa [phi, Real.cos_neg] using Real.cos_arcsin_nonneg (1 / (8 * Real.sqrt 3))
  have hsq := Real.sin_sq_add_cos_sq phi
  rw [phi_sin] at hsq
  have hd : (Real.sqrt 573) ^ 2 = 573 := by norm_num [Real.sq_sqrt]
  have hdpos : 0 ≤ Real.sqrt 573 := Real.sqrt_nonneg _
  nlinarith [sqrt3_sq]

theorem theta_exp : Complex.exp ((theta : ℂ) * Complex.I) = (c + alpha) / 15 := by
  rw [Complex.exp_ofReal_mul_I, theta_cos, theta_sin]
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
  unfold c alpha
  ring

theorem neg_theta_exp : Complex.exp (((-theta : ℝ) : ℂ) * Complex.I) =
    (c - alpha) / 15 := by
  rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, theta_cos, theta_sin]
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg]
  unfold c alpha
  ring

theorem phi_exp : Complex.exp ((phi : ℂ) * Complex.I) = (d - alpha) / 24 := by
  rw [Complex.exp_ofReal_mul_I, phi_cos, phi_sin]
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg]
  unfold d alpha
  ring

theorem neg_phi_exp : Complex.exp (((-phi : ℝ) : ℂ) * Complex.I) =
    (d + alpha) / 24 := by
  rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, phi_cos, phi_sin]
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg]
  unfold d alpha
  ring

theorem sixth_root_exp : Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I) = r := by
  rw [Complex.exp_ofReal_mul_I, Real.cos_pi_div_three, Real.sin_pi_div_three]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  unfold r alpha
  ring

theorem r_six : r ^ 6 = 1 := by
  have h3 : r ^ 3 = -1 := by
    unfold r
    linear_combination ((alpha + 3) / 8) * alpha_sq
  calc r ^ 6 = (r ^ 3) ^ 2 := by ring
       _ = 1 := by rw [h3]; norm_num

theorem coordinate_phase (base : ℕ) (angle : ℝ) :
    phase (coordinate base angle) =
      r ^ (base % 6) * Complex.exp ((angle : ℂ) * Complex.I) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have harg : Real.pi * coordinate base angle / 3 =
      (base : ℝ) * (Real.pi / 3) + angle := by
    unfold coordinate
    field_simp
  unfold phase
  rw [harg]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_natCast, add_mul]
  rw [mul_assoc, Complex.exp_add, Complex.exp_nat_mul, sixth_root_exp,
    pow_eq_pow_mod base r_six]

#print axioms theta_exp
#print axioms neg_theta_exp
#print axioms phi_exp
#print axioms neg_phi_exp
#print axioms coordinate_phase

end PhotonCoordinates
