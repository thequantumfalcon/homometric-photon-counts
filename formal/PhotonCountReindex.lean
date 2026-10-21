import PhotonGaussianModel
import Mathlib.Logic.Equiv.Fin.Basic

open MeasureTheory
open scoped BigOperators NNReal

namespace PhotonCountReindex

set_option maxHeartbeats 2000000

/-- A list permutation transports every indexed occurrence, including repeated values. -/
theorem perm_index_equiv {α : Type*} {zs ws : List α} (h : zs.Perm ws) :
    ∃ e : Fin zs.length ≃ Fin ws.length, ∀ i, ws.get (e i) = zs.get i := by
  classical
  induction h with
  | nil => exact ⟨Equiv.refl _, fun _ => rfl⟩
  | @cons x zs ws h ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨(finSuccEquiv zs.length).trans
      ((Equiv.optionCongr e).trans (finSuccEquiv ws.length).symm), ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simpa using he j
  | swap x y zs =>
    refine ⟨Equiv.swap 0 1, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · have h0 : k.succ.succ ≠ (0 : Fin (zs.length + 2)) := Fin.succ_ne_zero _
        have h1 : k.succ.succ ≠ (1 : Fin (zs.length + 2)) := by
          change k.succ.succ ≠ (0 : Fin (zs.length + 1)).succ
          exact fun h => Fin.succ_ne_zero k (Fin.succ_inj.mp h)
        simp [Equiv.swap_apply_of_ne_of_ne h0 h1]
  | trans h₁ h₂ ih₁ ih₂ =>
    obtain ⟨e, he⟩ := ih₁
    obtain ⟨f, hf⟩ := ih₂
    exact ⟨e.trans f, fun i => (hf (e i)).trans (he i)⟩

theorem field_reindex {n m : ℕ} (e : Fin n ≃ Fin m)
    (z : Fin n → ℂ) (w : Fin m → ℂ) (hw : ∀ i, w (e i) = z i)
    (θ : Fin n → ℝ) :
    PhotonIntensityBounds.field w (fun j => θ (e.symm j)) =
      PhotonIntensityBounds.field z θ := by
  unfold PhotonIntensityBounds.field
  rw [← e.sum_comp]
  simp only [e.symm_apply_apply, hw]

theorem listIntensity_reindex {zs ws : List ℂ}
    (e : Fin zs.length ≃ Fin ws.length) (he : ∀ i, ws.get (e i) = zs.get i)
    (θ : Fin zs.length → ℝ) :
    PhotonIntensityBounds.listIntensity ws (fun j => θ (e.symm j)) =
      PhotonIntensityBounds.listIntensity zs θ := by
  unfold PhotonIntensityBounds.listIntensity PhotonIntensityBounds.intensity
  rw [field_reindex e zs.get ws.get he]

theorem rate_reindex {zs ws : List ℂ}
    (e : Fin zs.length ≃ Fin ws.length) (he : ∀ i, ws.get (e i) = zs.get i)
    (η b : ℝ≥0) (θ : Fin zs.length → ℝ) :
    PhotonGaussianModel.rate ws η b (fun j => θ (e.symm j)) =
      PhotonGaussianModel.rate zs η b θ := by
  apply Subtype.ext
  simp only [PhotonGaussianModel.rate]
  rw [listIntensity_reindex e he]

theorem phaseLaw_reindex {n m : ℕ} (e : Fin n ≃ Fin m) (s : ℝ≥0) :
    MeasurePreserving (fun θ : Fin n → ℝ => fun j => θ (e.symm j))
      (PhotonGaussian.phaseLaw s) (PhotonGaussian.phaseLaw s) := by
  have hf : (fun θ : Fin n → ℝ => fun j => θ (e.symm j)) =
      MeasurableEquiv.piCongrLeft (fun _ : Fin m => ℝ) e := by
    funext θ j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp [MeasurableEquiv.piCongrLeft_apply_apply]
  rw [hf]
  exact measurePreserving_piCongrLeft (fun _ => ProbabilityTheory.gaussianReal 0 s) e

/-- The full Gaussian/Poisson count measure is invariant under any permutation of sites. -/
theorem countLaw_perm {zs ws : List ℂ} (h : zs.Perm ws) (s η b : ℝ≥0) :
    PhotonGaussianModel.countLaw zs s η b =
      PhotonGaussianModel.countLaw ws s η b := by
  obtain ⟨e, he⟩ := perm_index_equiv h
  have hm := phaseLaw_reindex e s
  unfold PhotonGaussianModel.countLaw PhotonPoissonMixture.countLaw
  rw [← hm.map_eq, Measure.bind_map hm.measurable.aemeasurable
    (PhotonPoissonMixture.poissonLaw_measurable.comp
      (PhotonGaussianModel.rate_measurable ws η b)).aemeasurable]
  congr 1
  funext θ
  simp only [Function.comp_apply, rate_reindex e he]

#print axioms perm_index_equiv
#print axioms field_reindex
#print axioms listIntensity_reindex
#print axioms rate_reindex
#print axioms phaseLaw_reindex
#print axioms countLaw_perm

end PhotonCountReindex
