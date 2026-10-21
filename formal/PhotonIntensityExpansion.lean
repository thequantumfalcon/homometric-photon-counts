import PhotonIntensityBounds

open MeasureTheory
open scoped BigOperators

namespace PhotonIntensityExpansion

def occupancy {n k : ℕ} (f : Fin k → Fin n) (j : Fin n) : ℕ :=
  (Finset.univ.filter (fun i => f i = j)).card

theorem product_occupancy {n k : ℕ} (f : Fin k → Fin n) (w : Fin n → ℂ) :
    (∏ i, w (f i)) = ∏ j, w j ^ occupancy f j := by
  rw [← Finset.prod_fiberwise' Finset.univ f w]
  simp [occupancy]

noncomputable def coefficient {n k : ℕ} (z : Fin n → ℂ)
    (f g : Fin k → Fin n) : ℂ :=
  (∏ i, z (f i)) * star (∏ i, z (g i))

theorem field_power_expansion {n : ℕ} (z w : Fin n → ℂ) (k : ℕ) :
    (∑ j, z j * w j) ^ k = ∑ f : Fin k → Fin n,
      (∏ i, z (f i)) * (∏ j, w j ^ occupancy f j) := by
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro f hf
  rw [Finset.prod_mul_distrib, product_occupancy f w]

theorem phasor_power_expansion {n : ℕ} (z w : Fin n → ℂ) (k : ℕ) :
    ((∑ j, z j * w j) * star (∑ j, z j * w j)) ^ k =
      ∑ f : Fin k → Fin n, ∑ g : Fin k → Fin n,
        coefficient z f g * ∏ j, w j ^ occupancy f j * star (w j) ^ occupancy g j := by
  rw [mul_pow, ← star_pow, field_power_expansion]
  simp only [star_sum, star_mul, star_prod, star_pow, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro g hg
  rw [Finset.prod_mul_distrib]
  unfold coefficient
  rw [star_prod]
  ring

theorem intensity_power_expansion {n : ℕ} (z : Fin n → ℂ) (θ : Fin n → ℝ) (k : ℕ) :
    (PhotonIntensityBounds.intensity z θ : ℂ) ^ k =
      ∑ f : Fin k → Fin n, ∑ g : Fin k → Fin n,
        coefficient z f g * ∏ j,
          Complex.exp (Complex.I * (θ j : ℂ)) ^ occupancy f j *
            star (Complex.exp (Complex.I * (θ j : ℂ))) ^ occupancy g j := by
  rw [PhotonIntensityBounds.intensity_complex]
  exact phasor_power_expansion z (fun j => Complex.exp (Complex.I * (θ j : ℂ))) k

#print axioms product_occupancy
#print axioms field_power_expansion
#print axioms phasor_power_expansion
#print axioms intensity_power_expansion

end PhotonIntensityExpansion
