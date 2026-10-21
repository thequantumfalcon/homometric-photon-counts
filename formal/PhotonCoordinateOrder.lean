import PhotonCoordinateGeometry
import Mathlib.Data.List.Nodup

/-! Strict order and distinctness of the exact real symbolic coordinates.
The finite decimal display fields are not used as exact positions. -/
namespace PhotonCoordinateOrder

open PhotonCoordinates PhotonCoordinateInput PhotonCoordinateGeometry

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem theta_angle_small : |theta| < Real.pi / 6 := by
  have hnonneg : 0 ≤ theta := by
    apply Real.arcsin_nonneg.mpr
    positivity
  rw [abs_of_nonneg hnonneg]
  unfold theta
  apply (Real.arcsin_lt_iff_lt_sin' (by
    constructor <;> linarith [Real.pi_pos])).mpr
  rw [Real.sin_pi_div_six, theta_argument]
  nlinarith [sqrt3_pos, sqrt3_sq]

theorem phi_angle_small : |phi| < Real.pi / 6 := by
  have hnonneg : 0 ≤ Real.arcsin (1 / (8 * Real.sqrt 3)) := by
    apply Real.arcsin_nonneg.mpr
    positivity
  rw [phi, abs_neg, abs_of_nonneg hnonneg]
  apply (Real.arcsin_lt_iff_lt_sin' (by
    constructor <;> linarith [Real.pi_pos])).mpr
  rw [Real.sin_pi_div_six, phi_argument]
  nlinarith [sqrt3_pos, sqrt3_sq]

theorem scaled_angle_small {a : ℝ} (ha : |a| < Real.pi / 6) :
    |3 * a / Real.pi| < 1 / 2 := by
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3),
    abs_of_pos Real.pi_pos]
  apply (div_lt_iff₀ Real.pi_pos).mpr
  linarith

theorem theta_offset_small : |3 * theta / Real.pi| < 1 / 2 :=
  scaled_angle_small theta_angle_small

theorem phi_offset_small : |3 * phi / Real.pi| < 1 / 2 :=
  scaled_angle_small phi_angle_small

def validSign (p : Record) : Prop := p.2.2 = 0 ∨ p.2.2 = 1 ∨ p.2.2 = -1

instance (p : Record) : Decidable (validSign p) := inferInstanceAs
  (Decidable (p.2.2 = 0 ∨ p.2.2 = 1 ∨ p.2.2 = -1))

theorem angle_small {p : Record} (hp : validSign p) : |angle p| < Real.pi / 6 := by
  rcases hp with hp | hp | hp
  · simp [angle, hp, Real.pi_pos]
  · simp only [angle, hp, Int.cast_one, one_mul]
    split_ifs
    · exact theta_angle_small
    · exact phi_angle_small
    · simpa using (show (0 : ℝ) < Real.pi / 6 by positivity)
  · simp only [angle, hp, Int.cast_neg, Int.cast_one, neg_one_mul, abs_neg]
    split_ifs
    · exact theta_angle_small
    · exact phi_angle_small
    · simpa using (show (0 : ℝ) < Real.pi / 6 by positivity)

theorem position_bounds {p : Record} (hp : validSign p) :
    (p.1 : ℝ) - 1 / 2 < position p ∧ position p < (p.1 : ℝ) + 1 / 2 := by
  have h := abs_lt.mp (scaled_angle_small (angle_small hp))
  unfold position coordinate
  constructor <;> linarith

theorem position_lt_of_base_lt {p q : Record}
    (hp : validSign p) (hq : validSign q) (hpq : p.1 < q.1) :
    position p < position q := by
  have hbase : (p.1 : ℝ) + 1 ≤ (q.1 : ℝ) := by exact_mod_cast hpq
  have hp' := position_bounds hp
  have hq' := position_bounds hq
  linarith

theorem recordsA_signs : ∀ p ∈ recordsA, validSign p := by decide +kernel
theorem recordsB_signs : ∀ p ∈ recordsB, validSign p := by decide +kernel

theorem recordsA_bases_sorted : recordsA.Pairwise (fun p q => p.1 < q.1) := by decide +kernel
theorem recordsB_bases_sorted : recordsB.Pairwise (fun p q => p.1 < q.1) := by decide +kernel

theorem positions_sorted_of_bases {ps : List Record}
    (hs : ∀ p ∈ ps, validSign p) (ho : ps.Pairwise (fun p q => p.1 < q.1)) :
    (ps.map position).Pairwise (· < ·) := by
  rw [List.pairwise_map]
  apply ho.imp_of_mem
  intro p q hp hq hpq
  exact position_lt_of_base_lt (hs p hp) (hs q hq) hpq

theorem recordsA_positions_sorted : (recordsA.map position).Pairwise (· < ·) :=
  positions_sorted_of_bases recordsA_signs recordsA_bases_sorted

theorem recordsB_positions_sorted : (recordsB.map position).Pairwise (· < ·) :=
  positions_sorted_of_bases recordsB_signs recordsB_bases_sorted

theorem recordsA_positions_nodup : (recordsA.map position).Nodup :=
  recordsA_positions_sorted.nodup

theorem recordsB_positions_nodup : (recordsB.map position).Nodup :=
  recordsB_positions_sorted.nodup

theorem records_positions_lengths :
    (recordsA.map position).length = 63 ∧ (recordsB.map position).length = 63 := by
  simp only [List.length_map]
  decide

#print axioms theta_offset_small
#print axioms phi_offset_small
#print axioms position_bounds
#print axioms position_lt_of_base_lt
#print axioms recordsA_positions_sorted
#print axioms recordsB_positions_sorted
#print axioms recordsA_positions_nodup
#print axioms recordsB_positions_nodup
#print axioms records_positions_lengths

end PhotonCoordinateOrder
