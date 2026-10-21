import PhotonGeometry

open MeasureTheory
open scoped BigOperators

namespace PhotonIntensityBounds

noncomputable def field {n : ℕ} (z : Fin n → ℂ) (θ : Fin n → ℝ) : ℂ :=
  ∑ j, z j * Complex.exp (Complex.I * (θ j : ℂ))

noncomputable def intensity {n : ℕ} (z : Fin n → ℂ) (θ : Fin n → ℝ) : ℝ :=
  ‖field z θ‖ ^ 2

theorem intensity_complex {n : ℕ} (z : Fin n → ℂ) (θ : Fin n → ℝ) :
    (intensity z θ : ℂ) = field z θ * star (field z θ) := by
  rw [intensity, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  exact mul_comm _ _

theorem phase_conjugate (x : ℝ) :
    star (Complex.exp (Complex.I * (x : ℂ))) =
      Complex.exp (-(Complex.I * (x : ℂ))) := by
  rw [show star (Complex.exp (Complex.I * (x : ℂ))) =
    starRingEnd ℂ (Complex.exp (Complex.I * (x : ℂ))) from rfl]
  rw [← Complex.exp_conj]
  simp

theorem phase_product (x y : ℝ) :
    Complex.exp (Complex.I * (x : ℂ)) * star (Complex.exp (Complex.I * (y : ℂ))) =
      Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) := by
  rw [phase_conjugate, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem intensity_expansion {n : ℕ} (z : Fin n → ℂ) (θ : Fin n → ℝ) :
    (intensity z θ : ℂ) = ∑ j, ∑ k,
      z j * star (z k) * Complex.exp (Complex.I * ((θ j - θ k : ℝ) : ℂ)) := by
  rw [intensity_complex]
  unfold field
  rw [star_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [star_mul]
  calc
    _ = z j * star (z k) *
      (Complex.exp (Complex.I * (θ j : ℂ)) *
        star (Complex.exp (Complex.I * (θ k : ℂ)))) := by ring
    _ = _ := by rw [phase_product]

theorem norm_unit {z : ℂ} (hz : z * star z = 1) : ‖z‖ = 1 := by
  have hn := congrArg norm hz
  simp only [norm_mul, norm_star, norm_one] at hn
  have hp := norm_nonneg z
  nlinarith

theorem phase_norm (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem field_norm_le {n : ℕ} (z : Fin n → ℂ) (θ : Fin n → ℝ)
    (hz : ∀ j, z j * star (z j) = 1) : ‖field z θ‖ ≤ n := by
  calc
    ‖field z θ‖ ≤ ∑ j, ‖z j * Complex.exp (Complex.I * (θ j : ℂ))‖ :=
      norm_sum_le _ _
    _ = n := by simp [norm_unit (hz _)]

theorem intensity_bounds {n : ℕ} (z : Fin n → ℂ) (θ : Fin n → ℝ)
    (hz : ∀ j, z j * star (z j) = 1) :
    0 ≤ intensity z θ ∧ intensity z θ ≤ (n : ℝ) ^ 2 := by
  constructor
  · exact sq_nonneg _
  · exact pow_le_pow_left₀ (norm_nonneg _) (field_norm_le z θ hz) 2

theorem intensity_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (z : Fin n → ℂ) (θ : Fin n → Ω → ℝ) (hθ : ∀ j, Measurable (θ j)) :
    Measurable (fun ω => intensity z (fun j => θ j ω)) := by
  unfold intensity field
  fun_prop

theorem intensity_power_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {n : ℕ} (z : Fin n → ℂ)
    (θ : Fin n → Ω → ℝ) (hθ : ∀ j, Measurable (θ j))
    (hz : ∀ j, z j * star (z j) = 1) (k : ℕ) :
    Integrable (fun ω => intensity z (fun j => θ j ω) ^ k) μ := by
  apply (integrable_const (((n : ℝ) ^ 2) ^ k)).mono'
    ((intensity_measurable z θ hθ).pow_const k).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  have hb := intensity_bounds z (fun j => θ j ω) hz
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hb.1 k)]
  exact pow_le_pow_left₀ hb.1 hb.2 k

noncomputable def listIntensity (zs : List ℂ) (θ : Fin zs.length → ℝ) : ℝ :=
  intensity zs.get θ

theorem listIntensity_bounds (zs : List ℂ) (θ : Fin zs.length → ℝ)
    (hz : ∀ z ∈ zs, z * star z = 1) :
    0 ≤ listIntensity zs θ ∧ listIntensity zs θ ≤ (zs.length : ℝ) ^ 2 := by
  exact intensity_bounds zs.get θ (fun j => hz _ (List.get_mem zs j))

theorem geometryA_bounds (θ : Fin PhotonGeometry.geometryA.length → ℝ) :
    0 ≤ listIntensity PhotonGeometry.geometryA θ ∧
      listIntensity PhotonGeometry.geometryA θ ≤ 3969 := by
  have h := listIntensity_bounds PhotonGeometry.geometryA θ PhotonGeometry.geometry_unit.1
  norm_num [PhotonGeometry.geometry_sizes.2.1] at h ⊢
  exact h

theorem geometryB_bounds (θ : Fin PhotonGeometry.geometryB.length → ℝ) :
    0 ≤ listIntensity PhotonGeometry.geometryB θ ∧
      listIntensity PhotonGeometry.geometryB θ ≤ 3969 := by
  have h := listIntensity_bounds PhotonGeometry.geometryB θ PhotonGeometry.geometry_unit.2
  norm_num [PhotonGeometry.geometry_sizes.2.2] at h ⊢
  exact h

theorem geometryA_power_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (θ : Fin PhotonGeometry.geometryA.length → Ω → ℝ)
    (hθ : ∀ j, Measurable (θ j)) (k : ℕ) :
    Integrable (fun ω => listIntensity PhotonGeometry.geometryA (fun j => θ j ω) ^ k) μ := by
  exact intensity_power_integrable μ _ θ hθ
    (fun j => PhotonGeometry.geometry_unit.1 _ (List.get_mem _ j)) k

theorem geometryB_power_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (θ : Fin PhotonGeometry.geometryB.length → Ω → ℝ)
    (hθ : ∀ j, Measurable (θ j)) (k : ℕ) :
    Integrable (fun ω => listIntensity PhotonGeometry.geometryB (fun j => θ j ω) ^ k) μ := by
  exact intensity_power_integrable μ _ θ hθ
    (fun j => PhotonGeometry.geometry_unit.2 _ (List.get_mem _ j)) k

#print axioms field_norm_le
#print axioms intensity_complex
#print axioms intensity_expansion
#print axioms intensity_bounds
#print axioms intensity_measurable
#print axioms intensity_power_integrable
#print axioms geometryA_bounds
#print axioms geometryB_bounds
#print axioms geometryA_power_integrable
#print axioms geometryB_power_integrable

end PhotonIntensityBounds
