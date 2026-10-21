import PhotonCoordinateGeometry
import PhotonArchiveCountLaw

open MeasureTheory
open scoped NNReal

namespace PhotonCoordinateCountLaw

open PhotonCoordinateInput PhotonCoordinateGeometry

/-- Symbolic coordinates in original archive order induce the canonical A count law. -/
theorem coordinateA_countLaw (s η b : ℝ≥0) :
    PhotonGaussianModel.countLaw coordinatePhasesA s η b =
      PhotonGaussianModel.countLaw PhotonGeometry.geometryA s η b := by
  rw [coordinatesA_archive]
  exact PhotonArchiveCountLaw.archiveA_countLaw s η b

/-- Symbolic coordinates in original archive order induce the canonical B count law. -/
theorem coordinateB_countLaw (s η b : ℝ≥0) :
    PhotonGaussianModel.countLaw coordinatePhasesB s η b =
      PhotonGaussianModel.countLaw PhotonGeometry.geometryB s η b := by
  rw [coordinatesB_archive]
  exact PhotonArchiveCountLaw.archiveB_countLaw s η b

/-- The coordinate construction has the concrete fourth factorial-moment gap
and distinct count laws for positive Gaussian variance and signal gain. -/
theorem coordinate_count_laws_distinct (s η b : ℝ≥0) (hs : 0 < s) (hη : 0 < η) :
    ((∫ n, (n.descFactorial 4 : ℝ)
        ∂PhotonGaussianModel.countLaw coordinatePhasesA s η b) -
      (∫ n, (n.descFactorial 4 : ℝ)
        ∂PhotonGaussianModel.countLaw coordinatePhasesB s η b) =
      (η : ℝ) ^ 4 * PhotonAlgebra.delta4 (Real.exp (-(s : ℝ)))) ∧
      PhotonGaussianModel.countLaw coordinatePhasesA s η b ≠
        PhotonGaussianModel.countLaw coordinatePhasesB s η b := by
  rw [coordinateA_countLaw, coordinateB_countLaw]
  exact PhotonConcreteSeparation.count_laws_distinct s η b hs hη

/-- The stated translated symbolic construction has the same count laws.
The construction ordering need not equal the sorted archive ordering. -/
theorem translatedA_countLaw (s η b : ℝ≥0) :
    PhotonGaussianModel.countLaw
      ((translatedRecords [0,31,63]).map recordPhase) s η b =
      PhotonGaussianModel.countLaw coordinatePhasesA s η b := by
  exact PhotonCountReindex.countLaw_perm
    (recordsA_construction.map recordPhase).symm s η b

theorem translatedB_countLaw (s η b : ℝ≥0) :
    PhotonGaussianModel.countLaw
      ((translatedRecords [0,32,63]).map recordPhase) s η b =
      PhotonGaussianModel.countLaw coordinatePhasesB s η b := by
  exact PhotonCountReindex.countLaw_perm
    (recordsB_construction.map recordPhase).symm s η b

theorem translated_coordinate_count_laws_distinct
    (s η b : ℝ≥0) (hs : 0 < s) (hη : 0 < η) :
    ((∫ n, (n.descFactorial 4 : ℝ) ∂PhotonGaussianModel.countLaw
        ((translatedRecords [0,31,63]).map recordPhase) s η b) -
      (∫ n, (n.descFactorial 4 : ℝ) ∂PhotonGaussianModel.countLaw
        ((translatedRecords [0,32,63]).map recordPhase) s η b) =
      (η : ℝ) ^ 4 * PhotonAlgebra.delta4 (Real.exp (-(s : ℝ)))) ∧
      PhotonGaussianModel.countLaw
        ((translatedRecords [0,31,63]).map recordPhase) s η b ≠
      PhotonGaussianModel.countLaw
        ((translatedRecords [0,32,63]).map recordPhase) s η b := by
  rw [translatedA_countLaw, translatedB_countLaw]
  exact coordinate_count_laws_distinct s η b hs hη

/-- Parsing the literal coordinate arrays yields the stated symbolic construction
and the proved separation. Decimal display strings are consumed, not treated as
exact positions. External source-file byte binding remains a separate check. -/
theorem decoded_coordinate_count_laws_distinct
    (s η b : ℝ≥0) (hs : 0 < s) (hη : 0 < η) :
    ∃ ps qs : List Record,
      parseCoordinates rawCoordinatesA = some ps ∧
      parseCoordinates rawCoordinatesB = some qs ∧
      ps.Perm (translatedRecords [0,31,63]) ∧
      qs.Perm (translatedRecords [0,32,63]) ∧
      ((∫ n, (n.descFactorial 4 : ℝ)
          ∂PhotonGaussianModel.countLaw (ps.map recordPhase) s η b) -
        (∫ n, (n.descFactorial 4 : ℝ)
          ∂PhotonGaussianModel.countLaw (qs.map recordPhase) s η b) =
        (η : ℝ) ^ 4 * PhotonAlgebra.delta4 (Real.exp (-(s : ℝ)))) ∧
      PhotonGaussianModel.countLaw (ps.map recordPhase) s η b ≠
        PhotonGaussianModel.countLaw (qs.map recordPhase) s η b :=
  ⟨recordsA, recordsB, parsed_coordinatesA, parsed_coordinatesB,
    recordsA_construction, recordsB_construction,
    coordinate_count_laws_distinct s η b hs hη⟩

#print axioms coordinateA_countLaw
#print axioms coordinateB_countLaw
#print axioms coordinate_count_laws_distinct
#print axioms translatedA_countLaw
#print axioms translatedB_countLaw
#print axioms translated_coordinate_count_laws_distinct
#print axioms decoded_coordinate_count_laws_distinct

end PhotonCoordinateCountLaw
