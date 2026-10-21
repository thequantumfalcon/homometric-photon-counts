import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring

open MeasureTheory

namespace PhotonMomentTransfer

/-- Fourth moment after affine gain and common background, with all required
integrability hypotheses explicit. -/
theorem affine_fourth_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : Ω → ℝ) (η b : ℝ)
    (h1 : Integrable I μ)
    (h2 : Integrable (fun ω => I ω ^ 2) μ)
    (h3 : Integrable (fun ω => I ω ^ 3) μ)
    (h4 : Integrable (fun ω => I ω ^ 4) μ) :
    (∫ ω, (η * I ω + b) ^ 4 ∂μ) =
      η ^ 4 * (∫ ω, I ω ^ 4 ∂μ) +
      (4 * η ^ 3 * b) * (∫ ω, I ω ^ 3 ∂μ) +
      (6 * η ^ 2 * b ^ 2) * (∫ ω, I ω ^ 2 ∂μ) +
      (4 * η * b ^ 3) * (∫ ω, I ω ∂μ) + b ^ 4 := by
  have hexpand : (fun ω => (η * I ω + b) ^ 4) =
      (fun ω => η ^ 4 * I ω ^ 4 + (4 * η ^ 3 * b) * I ω ^ 3 +
        (6 * η ^ 2 * b ^ 2) * I ω ^ 2 + (4 * η * b ^ 3) * I ω + b ^ 4) := by
    funext ω
    ring
  rw [hexpand]
  have ha := h4.const_mul (η ^ 4)
  have hb := h3.const_mul (4 * η ^ 3 * b)
  have hc := h2.const_mul (6 * η ^ 2 * b ^ 2)
  have hd := h1.const_mul (4 * η * b ^ 3)
  have hs4 := integral_add (((ha.add hb).add hc).add hd) (integrable_const (b ^ 4))
  have hs3 := integral_add ((ha.add hb).add hc) hd
  have hs2 := integral_add (ha.add hb) hc
  have hs1 := integral_add ha hb
  simp only [Pi.add_apply] at hs4 hs3 hs2 hs1
  rw [hs4, hs3, hs2, hs1]
  simp [integral_const_mul]

/-- Equality of intensity moments one through three eliminates all common
background terms in the fourth affine-moment difference. -/
theorem common_background_cancellation
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (I : Ω → ℝ) (J : Ξ → ℝ) (η b : ℝ)
    (hI1 : Integrable I μ) (hI2 : Integrable (fun ω => I ω ^ 2) μ)
    (hI3 : Integrable (fun ω => I ω ^ 3) μ)
    (hI4 : Integrable (fun ω => I ω ^ 4) μ)
    (hJ1 : Integrable J ν) (hJ2 : Integrable (fun ω => J ω ^ 2) ν)
    (hJ3 : Integrable (fun ω => J ω ^ 3) ν)
    (hJ4 : Integrable (fun ω => J ω ^ 4) ν)
    (match1 : (∫ ω, I ω ∂μ) = ∫ ω, J ω ∂ν)
    (match2 : (∫ ω, I ω ^ 2 ∂μ) = ∫ ω, J ω ^ 2 ∂ν)
    (match3 : (∫ ω, I ω ^ 3 ∂μ) = ∫ ω, J ω ^ 3 ∂ν) :
    (∫ ω, (η * I ω + b) ^ 4 ∂μ) - (∫ ω, (η * J ω + b) ^ 4 ∂ν) =
      η ^ 4 * ((∫ ω, I ω ^ 4 ∂μ) - (∫ ω, J ω ^ 4 ∂ν)) := by
  rw [affine_fourth_moment μ I η b hI1 hI2 hI3 hI4,
    affine_fourth_moment ν J η b hJ1 hJ2 hJ3 hJ4, match1, match2, match3]
  ring

#print axioms affine_fourth_moment
#print axioms common_background_cancellation

end PhotonMomentTransfer
