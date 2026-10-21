import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Ineq

/-! Algebraic part only. The interpretation of `moment` as a count-law
factorial moment, and the assumed identity, are external obligations. -/
namespace PhotonAlgebra

noncomputable def delta4 (x : ℝ) : ℝ :=
  (455015761 / 20000 : ℝ) * x ^ 4 * (1 - x) ^ 5 *
    (x ^ 3 + 3 * x ^ 2 + 6 * x + 6)

theorem delta4_pos {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    0 < delta4 x := by
  have hc : (0 : ℝ) < 455015761 / 20000 := by norm_num
  have h3 : (0 : ℝ) < 3 := by norm_num
  have h6 : (0 : ℝ) < 6 := by norm_num
  exact mul_pos
    (mul_pos (mul_pos hc (pow_pos hx 4)) (pow_pos (sub_pos.mpr hx1) 5))
    (add_pos (add_pos (add_pos (pow_pos hx 3) (mul_pos h3 (pow_pos hx 2)))
      (mul_pos h6 hx)) h6)

theorem reference_delta4 : delta4 (1 / 4) = (54510433152039 / 335544320000 : ℝ) := by
  norm_num [delta4, pow_succ]

theorem endpoint_delta4_zero : delta4 0 = 0 ∧ delta4 1 = 0 := by
  constructor <;> norm_num [delta4]

noncomputable def selectedD : ℝ :=
  2929691026982676683576014631598600390325842740183259345033812474797 /
  100000000000000000000000000000000000000000000000000000000000000000000000000000000

def selectedM : ℕ := 102399876723169

/-- Exact arithmetic for the selected cutoff-12, gain-1/20 certificate.
This does not establish that the certificate bounds the true single-count MGF. -/
theorem selected_budget : 0 < selectedD ∧ selectedD ≤ 1 ∧
    (3 : ℝ) ≤ (selectedM : ℝ) * selectedD := by
  norm_num [selectedD, selectedM]

/-- Any law functional with the stated positive difference separates laws. -/
theorem laws_distinct_of_moment_identity
    {Laws : Type*} (moment : Laws → ℝ) (μ ν : Laws) {η x : ℝ}
    (hη : 0 < η) (hx : 0 < x) (hx1 : x < 1)
    (identity : moment μ - moment ν = η ^ 4 * delta4 x) : μ ≠ ν := by
  have hpos : 0 < η ^ 4 * delta4 x :=
    mul_pos (pow_pos hη 4) (delta4_pos hx hx1)
  intro heq
  have hz : (0 : ℝ) = η ^ 4 * delta4 x := by
    simpa only [heq, sub_self] using identity
  exact (ne_of_gt hpos) hz.symm

end PhotonAlgebra

#print axioms PhotonAlgebra.delta4_pos
#print axioms PhotonAlgebra.reference_delta4
#print axioms PhotonAlgebra.endpoint_delta4_zero
#print axioms PhotonAlgebra.selected_budget
#print axioms PhotonAlgebra.laws_distinct_of_moment_identity
