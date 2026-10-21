import PhotonMixedRecurrence
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots

open MeasureTheory
open scoped BigOperators NNReal Polynomial

namespace PhotonMomentPolynomial

open PhotonMixedRecurrence PhotonIntensityBounds PhotonGaussian

def chargeSq (a b : ℕ) : ℕ := (a - b + (b - a)) ^ 2

theorem chargeSq_cast (a b : ℕ) :
    (chargeSq a b : ℝ) = ((a : ℝ) - b) ^ 2 := by
  unfold chargeSq
  push_cast
  rcases le_total a b with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, zero_add, Nat.cast_sub h]
    ring
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, add_zero, Nat.cast_sub h]

theorem gaussian_weight_power (s : ℝ≥0) (a b : ℕ) :
    (Real.exp (-(s : ℝ) / 2) : ℂ) ^ chargeSq a b =
      (Real.exp (-(s : ℝ) * ((a : ℝ) - b) ^ 2 / 2) : ℂ) := by
  rw [← Complex.ofReal_pow]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  rw [chargeSq_cast]
  ring

noncomputable def momentPoly : (n : ℕ) → (Fin n → ℂ) → ℕ → ℕ → ℂ[X]
  | 0, _, a, b => Polynomial.C (0 ^ a * 0 ^ b)
  | n+1, z, a, b =>
      ∑ i ∈ Finset.range (a+1), ∑ j ∈ Finset.range (b+1),
        Polynomial.C ((a.choose i : ℂ) * (b.choose j : ℂ)) *
          momentPoly n (Fin.init z) (a-i) (b-j) *
          Polynomial.C (z (Fin.last n) ^ i * star (z (Fin.last n)) ^ j) *
          Polynomial.X ^ chargeSq i j

theorem eval_momentPoly (n : ℕ) (z : Fin n → ℂ) (s : ℝ≥0) (a b : ℕ) :
    (momentPoly n z a b).eval (Real.exp (-(s : ℝ) / 2) : ℂ) =
      recurrence n z s a b := by
  induction n generalizing a b with
  | zero => simp [momentPoly, recurrence]
  | succ n ih =>
    simp only [momentPoly, recurrence, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih, gaussian_weight_power]

theorem eval_momentPoly_intensity (n : ℕ) (z : Fin n → ℂ) (s : ℝ≥0) (k : ℕ) :
    (momentPoly n z k k).eval (Real.exp (-(s : ℝ) / 2) : ℂ) =
      ((∫ θ, intensity z θ ^ k ∂phaseLaw s : ℝ) : ℂ) := by
  rw [eval_momentPoly, recurrence_eq_real_intensity]

theorem chargeSq_le (a b : ℕ) : chargeSq a b ≤ a ^ 2 + b ^ 2 := by
  have h : (chargeSq a b : ℝ) ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
    rw [chargeSq_cast]
    nlinarith [mul_nonneg (Nat.cast_nonneg a : (0 : ℝ) ≤ a) (Nat.cast_nonneg b)]
  exact_mod_cast h

theorem transition_degree_le {a b i j : ℕ} (hi : i ≤ a) (hj : j ≤ b) :
    (a-i)^2 + (b-j)^2 + chargeSq i j ≤ a^2 + b^2 := by
  have hc := chargeSq_le i j
  have ha := Nat.sub_add_cancel hi
  have hb := Nat.sub_add_cancel hj
  nlinarith [Nat.zero_le ((a-i)*i), Nat.zero_le ((b-j)*j)]

theorem momentPoly_degree (n : ℕ) (z : Fin n → ℂ) (a b : ℕ) :
    (momentPoly n z a b).natDegree ≤ a^2 + b^2 := by
  induction n generalizing a b with
  | zero => simp only [momentPoly, Polynomial.natDegree_C]; exact Nat.zero_le _
  | succ n ih =>
    simp only [momentPoly]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    have hp := (Polynomial.natDegree_mul_C_le
      (Polynomial.C ((a.choose i : ℂ) * (b.choose j : ℂ)) *
        momentPoly n (Fin.init z) (a-i) (b-j))
      (z (Fin.last n) ^ i * star (z (Fin.last n)) ^ j)).trans
      ((Polynomial.natDegree_C_mul_le ((a.choose i : ℂ) * (b.choose j : ℂ)) _).trans
        (ih (Fin.init z) (a-i) (b-j)))
    exact (Polynomial.natDegree_mul_le_of_le hp (Polynomial.natDegree_X_pow_le _)).trans
      (transition_degree_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))

theorem difference_degree {n m : ℕ} (z : Fin n → ℂ) (w : Fin m → ℂ) (k : ℕ) :
    (momentPoly n z k k - momentPoly m w k k).natDegree ≤ 2*k^2 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simpa only [two_mul] using momentPoly_degree n z k k
  · simpa only [two_mul] using momentPoly_degree m w k k

theorem eq_of_33_nodes (p q : ℂ[X]) (hp : p.natDegree ≤ 32) (hq : q.natDegree ≤ 32)
    (h : ∀ i : Fin 33, p.eval ((i.val : ℂ) + 1) = q.eval ((i.val : ℂ) + 1)) :
    p = q := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq p q
    (f := fun i : Fin 33 => (i.val : ℂ) + 1)
  · intro i j hij
    apply Fin.ext
    exact_mod_cast add_right_cancel hij
  · exact h
  · simpa only [Fintype.card_fin] using lt_of_le_of_lt (max_le hp hq) (by decide : 32 < 33)

theorem difference_eq_of_33_nodes {n m : ℕ} (z : Fin n → ℂ) (w : Fin m → ℂ)
    (k : ℕ) (hk : k ≤ 4) (q : ℂ[X]) (hq : q.natDegree ≤ 32)
    (h : ∀ i : Fin 33,
      (momentPoly n z k k - momentPoly m w k k).eval ((i.val : ℂ) + 1) =
        q.eval ((i.val : ℂ) + 1)) :
    momentPoly n z k k - momentPoly m w k k = q := by
  apply eq_of_33_nodes _ q _ hq h
  exact (difference_degree z w k).trans (by nlinarith)

#print axioms chargeSq_cast
#print axioms gaussian_weight_power
#print axioms eval_momentPoly
#print axioms eval_momentPoly_intensity
#print axioms chargeSq_le
#print axioms transition_degree_le
#print axioms momentPoly_degree
#print axioms difference_degree
#print axioms eq_of_33_nodes
#print axioms difference_eq_of_33_nodes

end PhotonMomentPolynomial
