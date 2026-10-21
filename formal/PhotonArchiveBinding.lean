import PhotonGeometry

import Mathlib.Data.List.Perm.Basic

open PhotonGeometry

namespace PhotonArchiveBinding

set_option maxHeartbeats 4000000

set_option maxRecDepth 20000

set_option linter.unusedSimpArgs false

set_option linter.unusedTactic false

set_option linter.unreachableTactic false

set_option linter.unnecessarySeqFocus false

abbrev Coeff := ℚ × ℚ × ℚ × ℚ × ℚ × ℚ × ℚ × ℚ

abbrev Phase := Coeff × Coeff

noncomputable def s3 : ℂ := (Real.sqrt 3 : ℂ)

noncomputable def s74 : ℂ := (Real.sqrt 74 : ℂ)

noncomputable def s191 : ℂ := (Real.sqrt 191 : ℂ)

noncomputable def evalReal (a : Coeff) : ℂ := (a.1 : ℂ) + a.2.1 * s3 + a.2.2.1 * s74 + a.2.2.2.1 * (s3 * s74) + a.2.2.2.2.1 * s191 + a.2.2.2.2.2.1 * (s3 * s191) + a.2.2.2.2.2.2.1 * (s74 * s191) + a.2.2.2.2.2.2.2 * (s3 * s74 * s191)

noncomputable def evalPhase (a : Phase) : ℂ := evalReal a.1 + Complex.I * evalReal a.2

theorem alpha_field : alpha = Complex.I * s3 := rfl

theorem r_sq_field : r ^ 2 = (-1 + alpha) / 2 := by
  unfold r
  linear_combination (1 / 4) * alpha_sq

theorem r_cube_field : r ^ 3 = -1 := by
  unfold r
  linear_combination ((alpha + 3) / 8) * alpha_sq

theorem s3_sq : s3 ^ 2 = 3 := by norm_num [s3, ← Complex.ofReal_pow, Real.sq_sqrt]

theorem c_field : c = s3 * s74 := by
  unfold c s3 s74
  rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem d_field : d = s3 * s191 := by
  unfold d s3 s191
  rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

def p0 : Phase := ((1, 0, 0, 0, 0, 0, 0, 0), (0, 0, 0, 0, 0, 0, 0, 0))

def p1 : Phase := (((-1 / 10), 0, 0, (1 / 30), 0, 0, 0, 0), (0, (1 / 30), (1 / 10), 0, 0, 0, 0, 0))

def p2 : Phase := ((-1, 0, 0, 0, 0, 0, 0, 0), (0, 0, 0, 0, 0, 0, 0, 0))

def p3 : Phase := (((-1 / 10), 0, 0, (-1 / 30), 0, 0, 0, 0), (0, (1 / 30), (-1 / 10), 0, 0, 0, 0, 0))

def p4 : Phase := ((0, 0, 0, 0, 0, (1 / 24), 0, 0), (0, (-1 / 24), 0, 0, 0, 0, 0, 0))

def p5 : Phase := ((0, 0, 0, 0, 0, (-1 / 24), 0, 0), (0, (-1 / 24), 0, 0, 0, 0, 0, 0))

def p6 : Phase := (((1 / 2), 0, 0, 0, 0, 0, 0, 0), (0, (1 / 2), 0, 0, 0, 0, 0, 0))

def p7 : Phase := (((-1 / 10), 0, 0, (-1 / 30), 0, 0, 0, 0), (0, (-1 / 30), (1 / 10), 0, 0, 0, 0, 0))

def p8 : Phase := (((-1 / 2), 0, 0, 0, 0, 0, 0, 0), (0, (-1 / 2), 0, 0, 0, 0, 0, 0))

def p9 : Phase := (((-1 / 10), 0, 0, (1 / 30), 0, 0, 0, 0), (0, (-1 / 30), (-1 / 10), 0, 0, 0, 0, 0))

def p10 : Phase := (((1 / 16), 0, 0, 0, 0, (1 / 48), 0, 0), (0, (-1 / 48), 0, 0, (1 / 16), 0, 0, 0))

def p11 : Phase := (((1 / 16), 0, 0, 0, 0, (-1 / 48), 0, 0), (0, (-1 / 48), 0, 0, (-1 / 16), 0, 0, 0))

def p12 : Phase := (((1 / 10), 0, 0, (-1 / 30), 0, 0, 0, 0), (0, (-1 / 30), (-1 / 10), 0, 0, 0, 0, 0))

def p13 : Phase := (((1 / 10), 0, 0, (1 / 30), 0, 0, 0, 0), (0, (-1 / 30), (1 / 10), 0, 0, 0, 0, 0))

def p14 : Phase := ((0, 0, 0, 0, 0, (-1 / 24), 0, 0), (0, (1 / 24), 0, 0, 0, 0, 0, 0))

def p15 : Phase := ((0, 0, 0, 0, 0, (1 / 24), 0, 0), (0, (1 / 24), 0, 0, 0, 0, 0, 0))

def p16 : Phase := (((-1 / 2), 0, 0, 0, 0, 0, 0, 0), (0, (1 / 2), 0, 0, 0, 0, 0, 0))

def p17 : Phase := ((0, 0, 0, (-1 / 15), 0, 0, 0, 0), (0, (-1 / 15), 0, 0, 0, 0, 0, 0))

def p18 : Phase := (((1 / 2), 0, 0, 0, 0, 0, 0, 0), (0, (-1 / 2), 0, 0, 0, 0, 0, 0))

def p19 : Phase := ((0, 0, 0, (1 / 15), 0, 0, 0, 0), (0, (-1 / 15), 0, 0, 0, 0, 0, 0))

def p20 : Phase := (((1 / 16), 0, 0, 0, 0, (-1 / 48), 0, 0), (0, (1 / 48), 0, 0, (1 / 16), 0, 0, 0))

def p21 : Phase := (((1 / 16), 0, 0, 0, 0, (1 / 48), 0, 0), (0, (1 / 48), 0, 0, (-1 / 16), 0, 0, 0))

def lookup : Nat → Phase
  | 0 => p0
  | 1 => p1
  | 2 => p2
  | 3 => p3
  | 4 => p4
  | 5 => p5
  | 6 => p6
  | 7 => p7
  | 8 => p8
  | 9 => p9
  | 10 => p10
  | 11 => p11
  | 12 => p12
  | 13 => p13
  | 14 => p14
  | 15 => p15
  | 16 => p16
  | 17 => p17
  | 18 => p18
  | 19 => p19
  | 20 => p20
  | 21 => p21
  | _ => p0

theorem value_0_0 : evalPhase p1 = thetaPlus := by
  norm_num [evalPhase, evalReal, p1, p1, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_0_1 : evalPhase p3 = thetaMinus := by
  norm_num [evalPhase, evalReal, p3, p3, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_0_2 : evalPhase p4 = phiPlus := by
  norm_num [evalPhase, evalReal, p4, p4, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_0_3 : evalPhase p5 = phiMinus := by
  norm_num [evalPhase, evalReal, p5, p5, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_0_4 : evalPhase p0 = 1 := by
  norm_num [evalPhase, evalReal, p0, p0, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_0_5 : evalPhase p2 = (-1) := by
  norm_num [evalPhase, evalReal, p2, p2, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_1_0 : evalPhase p7 = (r * thetaPlus) := by
  rw [← value_0_0]
  norm_num [evalPhase, evalReal, p7, p1, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_1_1 : evalPhase p9 = (r * thetaMinus) := by
  rw [← value_0_1]
  norm_num [evalPhase, evalReal, p9, p3, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_1_2 : evalPhase p10 = (r * phiPlus) := by
  rw [← value_0_2]
  norm_num [evalPhase, evalReal, p10, p4, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_1_3 : evalPhase p11 = (r * phiMinus) := by
  rw [← value_0_3]
  norm_num [evalPhase, evalReal, p11, p5, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_1_4 : evalPhase p6 = (r * 1) := by
  rw [← value_0_4]
  norm_num [evalPhase, evalReal, p6, p0, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_1_5 : evalPhase p8 = (r * (-1)) := by
  rw [← value_0_5]
  norm_num [evalPhase, evalReal, p8, p2, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_2_0 : evalPhase p17 = (r ^ 2 * thetaPlus) := by
  rw [← value_0_0]
  simp only [r_sq_field, r_cube_field]
  norm_num [evalPhase, evalReal, p17, p1, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_2_1 : evalPhase p19 = (r ^ 2 * thetaMinus) := by
  rw [← value_0_1]
  simp only [r_sq_field, r_cube_field]
  norm_num [evalPhase, evalReal, p19, p3, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_2_2 : evalPhase p20 = (r ^ 2 * phiPlus) := by
  rw [← value_0_2]
  simp only [r_sq_field, r_cube_field]
  norm_num [evalPhase, evalReal, p20, p4, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_2_3 : evalPhase p21 = (r ^ 2 * phiMinus) := by
  rw [← value_0_3]
  simp only [r_sq_field, r_cube_field]
  norm_num [evalPhase, evalReal, p21, p5, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_2_4 : evalPhase p16 = (r ^ 2 * 1) := by
  rw [← value_0_4]
  simp only [r_sq_field, r_cube_field]
  norm_num [evalPhase, evalReal, p16, p0, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_2_5 : evalPhase p18 = (r ^ 2 * (-1)) := by
  rw [← value_0_5]
  simp only [r_sq_field, r_cube_field]
  norm_num [evalPhase, evalReal, p18, p2, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_3_0 : evalPhase p12 = (r ^ 3 * thetaPlus) := by
  rw [← value_0_0]
  simp only [r_sq_field, r_cube_field]
  norm_num [evalPhase, evalReal, p12, p1, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_3_1 : evalPhase p13 = (r ^ 3 * thetaMinus) := by
  rw [← value_0_1]
  simp only [r_sq_field, r_cube_field]
  norm_num [evalPhase, evalReal, p13, p3, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_3_2 : evalPhase p14 = (r ^ 3 * phiPlus) := by
  rw [← value_0_2]
  simp only [r_sq_field, r_cube_field]
  norm_num [evalPhase, evalReal, p14, p4, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_3_3 : evalPhase p15 = (r ^ 3 * phiMinus) := by
  rw [← value_0_3]
  simp only [r_sq_field, r_cube_field]
  norm_num [evalPhase, evalReal, p15, p5, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_3_4 : evalPhase p2 = (r ^ 3 * 1) := by
  rw [← value_0_4]
  simp only [r_sq_field, r_cube_field]
  norm_num [evalPhase, evalReal, p2, p0, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

theorem value_3_5 : evalPhase p0 = (r ^ 3 * (-1)) := by
  rw [← value_0_5]
  simp only [r_sq_field, r_cube_field]
  norm_num [evalPhase, evalReal, p0, p2, thetaPlus, thetaMinus, phiPlus, phiMinus, r, alpha_field, c_field, d_field] <;>
    ring_nf <;> (try simp only [s3_sq, Complex.I_sq]) <;> ring

def archiveA : List Phase := ([0, 1, 2, 3, 4, 1, 5, 3, 4, 1, 5, 3, 4, 1, 5, 3, 4, 1, 5, 3, 0, 6, 7, 8, 9, 10, 7, 11, 9, 10, 7, 11, 9, 10, 7, 11, 9, 10, 7, 11, 9, 6, 2, 12, 0, 13, 14, 12, 15, 13, 14, 12, 15, 13, 14, 12, 15, 13, 14, 12, 15, 13, 2] : List Nat).map lookup

def reconstructedA : List Phase := ([1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0, 0, 2, 7, 7, 7, 7, 7, 9, 9, 9, 9, 9, 10, 10, 10, 10, 11, 11, 11, 11, 6, 6, 8, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 14, 14, 14, 14, 15, 15, 15, 15, 2, 2, 0] : List Nat).map lookup

theorem records_perm_A : archiveA.Perm reconstructedA := by
  exact (show ([0, 1, 2, 3, 4, 1, 5, 3, 4, 1, 5, 3, 4, 1, 5, 3, 4, 1, 5, 3, 0, 6, 7, 8, 9, 10, 7, 11, 9, 10, 7, 11, 9, 10, 7, 11, 9, 10, 7, 11, 9, 6, 2, 12, 0, 13, 14, 12, 15, 13, 14, 12, 15, 13, 14, 12, 15, 13, 14, 12, 15, 13, 2] : List Nat).Perm [1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0, 0, 2, 7, 7, 7, 7, 7, 9, 9, 9, 9, 9, 10, 10, 10, 10, 11, 11, 11, 11, 6, 6, 8, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 14, 14, 14, 14, 15, 15, 15, 15, 2, 2, 0] from by decide).map lookup

theorem reconstructedA_eval : reconstructedA.map evalPhase = geometryA := by
  change [evalPhase p1, evalPhase p1, evalPhase p1, evalPhase p1, evalPhase p1, evalPhase p3, evalPhase p3, evalPhase p3, evalPhase p3, evalPhase p3, evalPhase p4, evalPhase p4, evalPhase p4, evalPhase p4, evalPhase p5, evalPhase p5, evalPhase p5, evalPhase p5, evalPhase p0, evalPhase p0, evalPhase p2, evalPhase p7, evalPhase p7, evalPhase p7, evalPhase p7, evalPhase p7, evalPhase p9, evalPhase p9, evalPhase p9, evalPhase p9, evalPhase p9, evalPhase p10, evalPhase p10, evalPhase p10, evalPhase p10, evalPhase p11, evalPhase p11, evalPhase p11, evalPhase p11, evalPhase p6, evalPhase p6, evalPhase p8, evalPhase p12, evalPhase p12, evalPhase p12, evalPhase p12, evalPhase p12, evalPhase p13, evalPhase p13, evalPhase p13, evalPhase p13, evalPhase p13, evalPhase p14, evalPhase p14, evalPhase p14, evalPhase p14, evalPhase p15, evalPhase p15, evalPhase p15, evalPhase p15, evalPhase p2, evalPhase p2, evalPhase p0] = [thetaPlus, thetaPlus, thetaPlus, thetaPlus, thetaPlus, thetaMinus, thetaMinus, thetaMinus, thetaMinus, thetaMinus, phiPlus, phiPlus, phiPlus, phiPlus, phiMinus, phiMinus, phiMinus, phiMinus, 1, 1, (-1), (r * thetaPlus), (r * thetaPlus), (r * thetaPlus), (r * thetaPlus), (r * thetaPlus), (r * thetaMinus), (r * thetaMinus), (r * thetaMinus), (r * thetaMinus), (r * thetaMinus), (r * phiPlus), (r * phiPlus), (r * phiPlus), (r * phiPlus), (r * phiMinus), (r * phiMinus), (r * phiMinus), (r * phiMinus), (r * 1), (r * 1), (r * (-1)), (r ^ 3 * thetaPlus), (r ^ 3 * thetaPlus), (r ^ 3 * thetaPlus), (r ^ 3 * thetaPlus), (r ^ 3 * thetaPlus), (r ^ 3 * thetaMinus), (r ^ 3 * thetaMinus), (r ^ 3 * thetaMinus), (r ^ 3 * thetaMinus), (r ^ 3 * thetaMinus), (r ^ 3 * phiPlus), (r ^ 3 * phiPlus), (r ^ 3 * phiPlus), (r ^ 3 * phiPlus), (r ^ 3 * phiMinus), (r ^ 3 * phiMinus), (r ^ 3 * phiMinus), (r ^ 3 * phiMinus), (r ^ 3 * 1), (r ^ 3 * 1), (r ^ 3 * (-1))]
  simp only [List.cons.injEq, and_true]
  exact ⟨value_0_0, value_0_0, value_0_0, value_0_0, value_0_0, value_0_1, value_0_1, value_0_1, value_0_1, value_0_1, value_0_2, value_0_2, value_0_2, value_0_2, value_0_3, value_0_3, value_0_3, value_0_3, value_0_4, value_0_4, value_0_5, value_1_0, value_1_0, value_1_0, value_1_0, value_1_0, value_1_1, value_1_1, value_1_1, value_1_1, value_1_1, value_1_2, value_1_2, value_1_2, value_1_2, value_1_3, value_1_3, value_1_3, value_1_3, value_1_4, value_1_4, value_1_5, value_3_0, value_3_0, value_3_0, value_3_0, value_3_0, value_3_1, value_3_1, value_3_1, value_3_1, value_3_1, value_3_2, value_3_2, value_3_2, value_3_2, value_3_3, value_3_3, value_3_3, value_3_3, value_3_4, value_3_4, value_3_5⟩

theorem archiveA_geometry : (archiveA.map evalPhase).Perm geometryA := by
  rw [← reconstructedA_eval]
  exact (records_perm_A).map evalPhase

#print axioms archiveA_geometry

def archiveB : List Phase := ([0, 1, 2, 3, 4, 1, 5, 3, 4, 1, 5, 3, 4, 1, 5, 3, 4, 1, 5, 3, 0, 16, 17, 18, 19, 20, 17, 21, 19, 20, 17, 21, 19, 20, 17, 21, 19, 20, 17, 21, 19, 16, 2, 12, 0, 13, 14, 12, 15, 13, 14, 12, 15, 13, 14, 12, 15, 13, 14, 12, 15, 13, 2] : List Nat).map lookup

def reconstructedB : List Phase := ([1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0, 0, 2, 17, 17, 17, 17, 17, 19, 19, 19, 19, 19, 20, 20, 20, 20, 21, 21, 21, 21, 16, 16, 18, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 14, 14, 14, 14, 15, 15, 15, 15, 2, 2, 0] : List Nat).map lookup

theorem records_perm_B : archiveB.Perm reconstructedB := by
  exact (show ([0, 1, 2, 3, 4, 1, 5, 3, 4, 1, 5, 3, 4, 1, 5, 3, 4, 1, 5, 3, 0, 16, 17, 18, 19, 20, 17, 21, 19, 20, 17, 21, 19, 20, 17, 21, 19, 20, 17, 21, 19, 16, 2, 12, 0, 13, 14, 12, 15, 13, 14, 12, 15, 13, 14, 12, 15, 13, 14, 12, 15, 13, 2] : List Nat).Perm [1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0, 0, 2, 17, 17, 17, 17, 17, 19, 19, 19, 19, 19, 20, 20, 20, 20, 21, 21, 21, 21, 16, 16, 18, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 14, 14, 14, 14, 15, 15, 15, 15, 2, 2, 0] from by decide).map lookup

theorem reconstructedB_eval : reconstructedB.map evalPhase = geometryB := by
  change [evalPhase p1, evalPhase p1, evalPhase p1, evalPhase p1, evalPhase p1, evalPhase p3, evalPhase p3, evalPhase p3, evalPhase p3, evalPhase p3, evalPhase p4, evalPhase p4, evalPhase p4, evalPhase p4, evalPhase p5, evalPhase p5, evalPhase p5, evalPhase p5, evalPhase p0, evalPhase p0, evalPhase p2, evalPhase p17, evalPhase p17, evalPhase p17, evalPhase p17, evalPhase p17, evalPhase p19, evalPhase p19, evalPhase p19, evalPhase p19, evalPhase p19, evalPhase p20, evalPhase p20, evalPhase p20, evalPhase p20, evalPhase p21, evalPhase p21, evalPhase p21, evalPhase p21, evalPhase p16, evalPhase p16, evalPhase p18, evalPhase p12, evalPhase p12, evalPhase p12, evalPhase p12, evalPhase p12, evalPhase p13, evalPhase p13, evalPhase p13, evalPhase p13, evalPhase p13, evalPhase p14, evalPhase p14, evalPhase p14, evalPhase p14, evalPhase p15, evalPhase p15, evalPhase p15, evalPhase p15, evalPhase p2, evalPhase p2, evalPhase p0] = [thetaPlus, thetaPlus, thetaPlus, thetaPlus, thetaPlus, thetaMinus, thetaMinus, thetaMinus, thetaMinus, thetaMinus, phiPlus, phiPlus, phiPlus, phiPlus, phiMinus, phiMinus, phiMinus, phiMinus, 1, 1, (-1), (r ^ 2 * thetaPlus), (r ^ 2 * thetaPlus), (r ^ 2 * thetaPlus), (r ^ 2 * thetaPlus), (r ^ 2 * thetaPlus), (r ^ 2 * thetaMinus), (r ^ 2 * thetaMinus), (r ^ 2 * thetaMinus), (r ^ 2 * thetaMinus), (r ^ 2 * thetaMinus), (r ^ 2 * phiPlus), (r ^ 2 * phiPlus), (r ^ 2 * phiPlus), (r ^ 2 * phiPlus), (r ^ 2 * phiMinus), (r ^ 2 * phiMinus), (r ^ 2 * phiMinus), (r ^ 2 * phiMinus), (r ^ 2 * 1), (r ^ 2 * 1), (r ^ 2 * (-1)), (r ^ 3 * thetaPlus), (r ^ 3 * thetaPlus), (r ^ 3 * thetaPlus), (r ^ 3 * thetaPlus), (r ^ 3 * thetaPlus), (r ^ 3 * thetaMinus), (r ^ 3 * thetaMinus), (r ^ 3 * thetaMinus), (r ^ 3 * thetaMinus), (r ^ 3 * thetaMinus), (r ^ 3 * phiPlus), (r ^ 3 * phiPlus), (r ^ 3 * phiPlus), (r ^ 3 * phiPlus), (r ^ 3 * phiMinus), (r ^ 3 * phiMinus), (r ^ 3 * phiMinus), (r ^ 3 * phiMinus), (r ^ 3 * 1), (r ^ 3 * 1), (r ^ 3 * (-1))]
  simp only [List.cons.injEq, and_true]
  exact ⟨value_0_0, value_0_0, value_0_0, value_0_0, value_0_0, value_0_1, value_0_1, value_0_1, value_0_1, value_0_1, value_0_2, value_0_2, value_0_2, value_0_2, value_0_3, value_0_3, value_0_3, value_0_3, value_0_4, value_0_4, value_0_5, value_2_0, value_2_0, value_2_0, value_2_0, value_2_0, value_2_1, value_2_1, value_2_1, value_2_1, value_2_1, value_2_2, value_2_2, value_2_2, value_2_2, value_2_3, value_2_3, value_2_3, value_2_3, value_2_4, value_2_4, value_2_5, value_3_0, value_3_0, value_3_0, value_3_0, value_3_0, value_3_1, value_3_1, value_3_1, value_3_1, value_3_1, value_3_2, value_3_2, value_3_2, value_3_2, value_3_3, value_3_3, value_3_3, value_3_3, value_3_4, value_3_4, value_3_5⟩

theorem archiveB_geometry : (archiveB.map evalPhase).Perm geometryB := by
  rw [← reconstructedB_eval]
  exact (records_perm_B).map evalPhase

#print axioms archiveB_geometry

end PhotonArchiveBinding
