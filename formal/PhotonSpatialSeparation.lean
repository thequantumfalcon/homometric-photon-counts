import PhotonCoordinateNoncongruence
import PhotonCoordinateCountLaw

open MeasureTheory
open scoped NNReal

namespace PhotonSpatialSeparation

open PhotonHomometry PhotonCoordinateInput PhotonCoordinateGeometry
open PhotonCoordinateHomometry PhotonCoordinateOrder PhotonCoordinateNoncongruence

/-- Two distinct 63-site lists with the same pair-separation multiset, not related
by any translation or reflection on the real line. -/
def GeometricPair (xs ys : List ℝ) : Prop :=
  xs.length = 63 ∧ ys.length = 63 ∧ xs.Nodup ∧ ys.Nodup ∧
  (differences xs).Perm (differences ys) ∧
  (∀ c : ℝ, ¬ xs.Perm (ys.map (fun x => x + c))) ∧
  (∀ c : ℝ, ¬ xs.Perm (ys.map (fun x => c - x)))

/-- The exact factorial-count moment gap and distinction for coordinate phasors. -/
def CountGap (xs ys : List ℝ) (s η b : ℝ≥0) : Prop :=
  ((∫ n, (n.descFactorial 4 : ℝ) ∂PhotonGaussianModel.countLaw
      (xs.map PhotonCoordinates.phase) s η b) -
    (∫ n, (n.descFactorial 4 : ℝ) ∂PhotonGaussianModel.countLaw
      (ys.map PhotonCoordinates.phase) s η b) =
    (η : ℝ) ^ 4 * PhotonAlgebra.delta4 (Real.exp (-(s : ℝ)))) ∧
  PhotonGaussianModel.countLaw (xs.map PhotonCoordinates.phase) s η b ≠
    PhotonGaussianModel.countLaw (ys.map PhotonCoordinates.phase) s η b

theorem exact_geometric_pair : GeometricPair positionsA positionsB :=
  ⟨records_positions_lengths.1, records_positions_lengths.2,
    recordsA_positions_nodup, recordsB_positions_nodup, coordinates_homometric,
    no_translation, no_reflection⟩

theorem positionsA_phases : positionsA.map PhotonCoordinates.phase = coordinatePhasesA := by
  simp only [positionsA, coordinatePhasesA, List.map_map, Function.comp_def]
  rfl

theorem positionsB_phases : positionsB.map PhotonCoordinates.phase = coordinatePhasesB := by
  simp only [positionsB, coordinatePhasesB, List.map_map, Function.comp_def]
  rfl

theorem spatial_count_laws_distinct (s η b : ℝ≥0) (hs : 0 < s) (hη : 0 < η) :
    GeometricPair positionsA positionsB ∧ CountGap positionsA positionsB s η b := by
  refine ⟨exact_geometric_pair, ?_⟩
  unfold CountGap
  rw [positionsA_phases, positionsB_phases]
  exact PhotonCoordinateCountLaw.coordinate_count_laws_distinct s η b hs hη

/-- The exact archived coordinate literals decode to a noncongruent homometric
pair with distinct count laws in the specified iid Gaussian/Poisson model. -/
theorem decoded_spatial_separation (s η b : ℝ≥0) (hs : 0 < s) (hη : 0 < η) :
    ∃ ps qs : List Record,
      parseCoordinates rawCoordinatesA = some ps ∧
      parseCoordinates rawCoordinatesB = some qs ∧
      GeometricPair (ps.map position) (qs.map position) ∧
      CountGap (ps.map position) (qs.map position) s η b :=
  ⟨recordsA, recordsB, parsed_coordinatesA, parsed_coordinatesB,
    spatial_count_laws_distinct s η b hs hη⟩

#print axioms exact_geometric_pair
#print axioms positionsA_phases
#print axioms positionsB_phases
#print axioms spatial_count_laws_distinct
#print axioms decoded_spatial_separation

end PhotonSpatialSeparation
