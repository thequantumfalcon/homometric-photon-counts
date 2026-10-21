import PhotonHomometry
import PhotonCoordinateGeometry

namespace PhotonCoordinateHomometry

open PhotonHomometry PhotonCoordinateInput PhotonCoordinateGeometry

noncomputable def positionsA : List ℝ := recordsA.map position
noncomputable def positionsB : List ℝ := recordsB.map position
noncomputable def basePositions : List ℝ := baseRecords.map position

theorem position_translate (p : Record) (n : Nat) :
    position (p.1 + n, p.2.1, p.2.2) = position p + n := by
  simp only [position, PhotonCoordinates.coordinate, angle, Nat.cast_add]
  ring

theorem translated_positions (ns : List Nat) :
    (translatedRecords ns).map position =
      translates basePositions (ns.map (fun n : Nat => (n : ℝ))) := by
  simp only [translatedRecords, translates, basePositions, List.map_flatMap,
    List.flatMap_map, List.map_map, Function.comp_def]
  congr 1
  funext n
  apply List.map_congr_left
  intro p _
  exact position_translate p n

theorem positionsA_construction :
    positionsA.Perm (translates basePositions [0,31,63]) := by
  have h := recordsA_construction.map position
  rw [translated_positions] at h
  simpa [positionsA] using h

theorem positionsB_construction :
    positionsB.Perm (translates basePositions [0,32,63]) := by
  have h := recordsB_construction.map position
  rw [translated_positions] at h
  simpa [positionsB] using h

theorem real_shifts_homometric :
    (differences ([0,31,63] : List ℝ)).Perm (differences [0,32,63]) := by
  have h := integer_shifts_homometric.map (fun n : Int => (n : ℝ))
  convert h using 1 <;> norm_num [differences]

/-- Every directed pair separation, including multiplicity, agrees exactly. -/
theorem coordinates_homometric :
    (differences positionsA).Perm (differences positionsB) := by
  exact (differences_perm positionsA_construction).trans
    ((translates_homometric basePositions [0,31,63] [0,32,63] real_shifts_homometric).trans
      (differences_perm positionsB_construction).symm)

/-- The same conclusion holds after applying any observable to each separation. -/
theorem separation_observables {α : Type*} (f : ℝ → α) :
    ((differences positionsA).map f).Perm ((differences positionsB).map f) :=
  coordinates_homometric.map f

#print axioms position_translate
#print axioms positionsA_construction
#print axioms positionsB_construction
#print axioms coordinates_homometric
#print axioms separation_observables

end PhotonCoordinateHomometry
