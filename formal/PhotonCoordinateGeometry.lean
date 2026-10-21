import PhotonCoordinateData
import PhotonCoordinates
import PhotonArchiveBinding

namespace PhotonCoordinateGeometry

open PhotonCoordinateInput PhotonCoordinates PhotonGeometry PhotonArchiveBinding

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

noncomputable def angle (p : Record) : ℝ :=
  (p.2.2 : ℝ) * (if p.2.1 = 1 then theta else if p.2.1 = 2 then phi else 0)

noncomputable def position (p : Record) : ℝ := coordinate p.1 (angle p)

noncomputable def recordPhase (p : Record) : ℂ := phase (position p)

noncomputable def coordinatePhasesA : List ℂ := recordsA.map recordPhase
noncomputable def coordinatePhasesB : List ℂ := recordsB.map recordPhase

def residue (p : Record) : Record := (p.1 % 6, p.2.1, p.2.2)

theorem recordPhase_residue (p : Record) : recordPhase p = recordPhase (residue p) := by
  simp only [recordPhase, position, coordinate_phase, residue, angle, Nat.mod_mod]
  rfl

theorem map_recordPhase_residue (ps : List Record) :
    ps.map recordPhase = (ps.map residue).map recordPhase := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro p _
  exact recordPhase_residue p

theorem r_four : r ^ 4 = -r := by
  calc r ^ 4 = r ^ 3 * r := by ring
       _ = -r := by rw [r_cube_field]; ring

theorem r_five : r ^ 5 = -(r ^ 2) := by
  calc r ^ 5 = r ^ 3 * r ^ 2 := by ring
       _ = -(r ^ 2) := by rw [r_cube_field]; ring

theorem theta_exp_neg : Complex.exp (-((theta : ℂ) * Complex.I)) =
    (c - alpha) / 15 := by simpa using neg_theta_exp

theorem phi_exp_neg : Complex.exp (-((phi : ℂ) * Complex.I)) =
    (d + alpha) / 24 := by simpa using neg_phi_exp

theorem key_0 : recordPhase (0, 0, (0)) = evalPhase p0 := by
  rw [recordPhase, position, coordinate_phase, value_0_4]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_1 : recordPhase (1, 1, (1)) = evalPhase p1 := by
  rw [recordPhase, position, coordinate_phase, value_0_0]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_2 : recordPhase (3, 0, (0)) = evalPhase p2 := by
  rw [recordPhase, position, coordinate_phase, value_0_5]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_3 : recordPhase (4, 1, (-1)) = evalPhase p3 := by
  rw [recordPhase, position, coordinate_phase, value_0_1]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_4 : recordPhase (0, 2, (1)) = evalPhase p4 := by
  rw [recordPhase, position, coordinate_phase, value_0_2]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_5 : recordPhase (3, 2, (-1)) = evalPhase p5 := by
  rw [recordPhase, position, coordinate_phase, value_0_3]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_6 : recordPhase (1, 0, (0)) = evalPhase p6 := by
  rw [recordPhase, position, coordinate_phase, value_1_4]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_7 : recordPhase (2, 1, (1)) = evalPhase p7 := by
  rw [recordPhase, position, coordinate_phase, value_1_0]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_8 : recordPhase (4, 0, (0)) = evalPhase p8 := by
  rw [recordPhase, position, coordinate_phase, value_1_5]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_9 : recordPhase (5, 1, (-1)) = evalPhase p9 := by
  rw [recordPhase, position, coordinate_phase, value_1_1]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_10 : recordPhase (1, 2, (1)) = evalPhase p10 := by
  rw [recordPhase, position, coordinate_phase, value_1_2]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_11 : recordPhase (4, 2, (-1)) = evalPhase p11 := by
  rw [recordPhase, position, coordinate_phase, value_1_3]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_12 : recordPhase (4, 1, (1)) = evalPhase p12 := by
  rw [recordPhase, position, coordinate_phase, value_3_0]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_13 : recordPhase (1, 1, (-1)) = evalPhase p13 := by
  rw [recordPhase, position, coordinate_phase, value_3_1]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_14 : recordPhase (3, 2, (1)) = evalPhase p14 := by
  rw [recordPhase, position, coordinate_phase, value_3_2]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_15 : recordPhase (0, 2, (-1)) = evalPhase p15 := by
  rw [recordPhase, position, coordinate_phase, value_3_3]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_16 : recordPhase (2, 0, (0)) = evalPhase p16 := by
  rw [recordPhase, position, coordinate_phase, value_2_4]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_17 : recordPhase (3, 1, (1)) = evalPhase p17 := by
  rw [recordPhase, position, coordinate_phase, value_2_0]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_18 : recordPhase (5, 0, (0)) = evalPhase p18 := by
  rw [recordPhase, position, coordinate_phase, value_2_5]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_19 : recordPhase (0, 1, (-1)) = evalPhase p19 := by
  rw [recordPhase, position, coordinate_phase, value_2_1]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_20 : recordPhase (2, 2, (1)) = evalPhase p20 := by
  rw [recordPhase, position, coordinate_phase, value_2_2]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

theorem key_21 : recordPhase (5, 2, (-1)) = evalPhase p21 := by
  rw [recordPhase, position, coordinate_phase, value_2_3]
  norm_num [angle, theta_exp, theta_exp_neg, phi_exp, phi_exp_neg,
    thetaPlus, thetaMinus, phiPlus, phiMinus]
  <;> ring_nf
  <;> simp only [r_cube_field, r_four, r_five]
  <;> ring

/-- Exact equality in original archived order, before any permutation. -/
theorem coordinatesA_archive : coordinatePhasesA = archiveA.map evalPhase := by
  unfold coordinatePhasesA
  rw [map_recordPhase_residue]
  change [recordPhase (0, 0, (0)), recordPhase (1, 1, (1)), recordPhase (3, 0, (0)), recordPhase (4, 1, (-1)), recordPhase (0, 2, (1)), recordPhase (1, 1, (1)), recordPhase (3, 2, (-1)), recordPhase (4, 1, (-1)), recordPhase (0, 2, (1)), recordPhase (1, 1, (1)), recordPhase (3, 2, (-1)), recordPhase (4, 1, (-1)), recordPhase (0, 2, (1)), recordPhase (1, 1, (1)), recordPhase (3, 2, (-1)), recordPhase (4, 1, (-1)), recordPhase (0, 2, (1)), recordPhase (1, 1, (1)), recordPhase (3, 2, (-1)), recordPhase (4, 1, (-1)), recordPhase (0, 0, (0)), recordPhase (1, 0, (0)), recordPhase (2, 1, (1)), recordPhase (4, 0, (0)), recordPhase (5, 1, (-1)), recordPhase (1, 2, (1)), recordPhase (2, 1, (1)), recordPhase (4, 2, (-1)), recordPhase (5, 1, (-1)), recordPhase (1, 2, (1)), recordPhase (2, 1, (1)), recordPhase (4, 2, (-1)), recordPhase (5, 1, (-1)), recordPhase (1, 2, (1)), recordPhase (2, 1, (1)), recordPhase (4, 2, (-1)), recordPhase (5, 1, (-1)), recordPhase (1, 2, (1)), recordPhase (2, 1, (1)), recordPhase (4, 2, (-1)), recordPhase (5, 1, (-1)), recordPhase (1, 0, (0)), recordPhase (3, 0, (0)), recordPhase (4, 1, (1)), recordPhase (0, 0, (0)), recordPhase (1, 1, (-1)), recordPhase (3, 2, (1)), recordPhase (4, 1, (1)), recordPhase (0, 2, (-1)), recordPhase (1, 1, (-1)), recordPhase (3, 2, (1)), recordPhase (4, 1, (1)), recordPhase (0, 2, (-1)), recordPhase (1, 1, (-1)), recordPhase (3, 2, (1)), recordPhase (4, 1, (1)), recordPhase (0, 2, (-1)), recordPhase (1, 1, (-1)), recordPhase (3, 2, (1)), recordPhase (4, 1, (1)), recordPhase (0, 2, (-1)), recordPhase (1, 1, (-1)), recordPhase (3, 0, (0))] = [evalPhase p0, evalPhase p1, evalPhase p2, evalPhase p3, evalPhase p4, evalPhase p1, evalPhase p5, evalPhase p3, evalPhase p4, evalPhase p1, evalPhase p5, evalPhase p3, evalPhase p4, evalPhase p1, evalPhase p5, evalPhase p3, evalPhase p4, evalPhase p1, evalPhase p5, evalPhase p3, evalPhase p0, evalPhase p6, evalPhase p7, evalPhase p8, evalPhase p9, evalPhase p10, evalPhase p7, evalPhase p11, evalPhase p9, evalPhase p10, evalPhase p7, evalPhase p11, evalPhase p9, evalPhase p10, evalPhase p7, evalPhase p11, evalPhase p9, evalPhase p10, evalPhase p7, evalPhase p11, evalPhase p9, evalPhase p6, evalPhase p2, evalPhase p12, evalPhase p0, evalPhase p13, evalPhase p14, evalPhase p12, evalPhase p15, evalPhase p13, evalPhase p14, evalPhase p12, evalPhase p15, evalPhase p13, evalPhase p14, evalPhase p12, evalPhase p15, evalPhase p13, evalPhase p14, evalPhase p12, evalPhase p15, evalPhase p13, evalPhase p2]
  simp only [key_0, key_1, key_2, key_3, key_4, key_5, key_6, key_7, key_8, key_9, key_10, key_11, key_12, key_13, key_14, key_15]

theorem coordinatesA_geometry : coordinatePhasesA.Perm PhotonGeometry.geometryA := by
  rw [coordinatesA_archive]
  exact archiveA_geometry

/-- Exact equality in original archived order, before any permutation. -/
theorem coordinatesB_archive : coordinatePhasesB = archiveB.map evalPhase := by
  unfold coordinatePhasesB
  rw [map_recordPhase_residue]
  change [recordPhase (0, 0, (0)), recordPhase (1, 1, (1)), recordPhase (3, 0, (0)), recordPhase (4, 1, (-1)), recordPhase (0, 2, (1)), recordPhase (1, 1, (1)), recordPhase (3, 2, (-1)), recordPhase (4, 1, (-1)), recordPhase (0, 2, (1)), recordPhase (1, 1, (1)), recordPhase (3, 2, (-1)), recordPhase (4, 1, (-1)), recordPhase (0, 2, (1)), recordPhase (1, 1, (1)), recordPhase (3, 2, (-1)), recordPhase (4, 1, (-1)), recordPhase (0, 2, (1)), recordPhase (1, 1, (1)), recordPhase (3, 2, (-1)), recordPhase (4, 1, (-1)), recordPhase (0, 0, (0)), recordPhase (2, 0, (0)), recordPhase (3, 1, (1)), recordPhase (5, 0, (0)), recordPhase (0, 1, (-1)), recordPhase (2, 2, (1)), recordPhase (3, 1, (1)), recordPhase (5, 2, (-1)), recordPhase (0, 1, (-1)), recordPhase (2, 2, (1)), recordPhase (3, 1, (1)), recordPhase (5, 2, (-1)), recordPhase (0, 1, (-1)), recordPhase (2, 2, (1)), recordPhase (3, 1, (1)), recordPhase (5, 2, (-1)), recordPhase (0, 1, (-1)), recordPhase (2, 2, (1)), recordPhase (3, 1, (1)), recordPhase (5, 2, (-1)), recordPhase (0, 1, (-1)), recordPhase (2, 0, (0)), recordPhase (3, 0, (0)), recordPhase (4, 1, (1)), recordPhase (0, 0, (0)), recordPhase (1, 1, (-1)), recordPhase (3, 2, (1)), recordPhase (4, 1, (1)), recordPhase (0, 2, (-1)), recordPhase (1, 1, (-1)), recordPhase (3, 2, (1)), recordPhase (4, 1, (1)), recordPhase (0, 2, (-1)), recordPhase (1, 1, (-1)), recordPhase (3, 2, (1)), recordPhase (4, 1, (1)), recordPhase (0, 2, (-1)), recordPhase (1, 1, (-1)), recordPhase (3, 2, (1)), recordPhase (4, 1, (1)), recordPhase (0, 2, (-1)), recordPhase (1, 1, (-1)), recordPhase (3, 0, (0))] = [evalPhase p0, evalPhase p1, evalPhase p2, evalPhase p3, evalPhase p4, evalPhase p1, evalPhase p5, evalPhase p3, evalPhase p4, evalPhase p1, evalPhase p5, evalPhase p3, evalPhase p4, evalPhase p1, evalPhase p5, evalPhase p3, evalPhase p4, evalPhase p1, evalPhase p5, evalPhase p3, evalPhase p0, evalPhase p16, evalPhase p17, evalPhase p18, evalPhase p19, evalPhase p20, evalPhase p17, evalPhase p21, evalPhase p19, evalPhase p20, evalPhase p17, evalPhase p21, evalPhase p19, evalPhase p20, evalPhase p17, evalPhase p21, evalPhase p19, evalPhase p20, evalPhase p17, evalPhase p21, evalPhase p19, evalPhase p16, evalPhase p2, evalPhase p12, evalPhase p0, evalPhase p13, evalPhase p14, evalPhase p12, evalPhase p15, evalPhase p13, evalPhase p14, evalPhase p12, evalPhase p15, evalPhase p13, evalPhase p14, evalPhase p12, evalPhase p15, evalPhase p13, evalPhase p14, evalPhase p12, evalPhase p15, evalPhase p13, evalPhase p2]
  simp only [key_0, key_1, key_2, key_3, key_4, key_5, key_12, key_13, key_14, key_15, key_16, key_17, key_18, key_19, key_20, key_21]

theorem coordinatesB_geometry : coordinatePhasesB.Perm PhotonGeometry.geometryB := by
  rw [coordinatesB_archive]
  exact archiveB_geometry

#print axioms coordinatesA_archive
#print axioms coordinatesB_archive
#print axioms coordinatesA_geometry
#print axioms coordinatesB_geometry

end PhotonCoordinateGeometry
