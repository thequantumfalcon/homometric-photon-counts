import PhotonCountReindex
import PhotonArchiveBridge
import PhotonConcreteSeparation

open MeasureTheory
open scoped NNReal

namespace PhotonArchiveCountLaw

noncomputable def geometryA : List ℂ :=
  PhotonArchiveBinding.archiveA.map PhotonArchiveBinding.evalPhase

noncomputable def geometryB : List ℂ :=
  PhotonArchiveBinding.archiveB.map PhotonArchiveBinding.evalPhase

/-- Original archived A ordering has exactly the canonical count measure. -/
theorem archiveA_countLaw (s η b : ℝ≥0) :
    PhotonGaussianModel.countLaw geometryA s η b =
      PhotonGaussianModel.countLaw PhotonGeometry.geometryA s η b :=
  PhotonCountReindex.countLaw_perm PhotonArchiveBinding.archiveA_geometry s η b

/-- Original archived B ordering has exactly the canonical count measure. -/
theorem archiveB_countLaw (s η b : ℝ≥0) :
    PhotonGaussianModel.countLaw geometryB s η b =
      PhotonGaussianModel.countLaw PhotonGeometry.geometryB s η b :=
  PhotonCountReindex.countLaw_perm PhotonArchiveBinding.archiveB_geometry s η b

/-- The checked concrete factorial-moment gap and count-law distinction hold in
the original archived phase ordering, without an additional exchangeability premise. -/
theorem archived_count_laws_distinct (s η b : ℝ≥0) (hs : 0 < s) (hη : 0 < η) :
    ((∫ n, (n.descFactorial 4 : ℝ)
        ∂PhotonGaussianModel.countLaw geometryA s η b) -
      (∫ n, (n.descFactorial 4 : ℝ)
        ∂PhotonGaussianModel.countLaw geometryB s η b) =
      (η : ℝ) ^ 4 * PhotonAlgebra.delta4 (Real.exp (-(s : ℝ)))) ∧
      PhotonGaussianModel.countLaw geometryA s η b ≠
        PhotonGaussianModel.countLaw geometryB s η b := by
  rw [archiveA_countLaw, archiveB_countLaw]
  exact PhotonConcreteSeparation.count_laws_distinct s η b hs hη

/-- The literal phase arrays parse to models with the proved fourth count-moment
gap and different count laws. External file/byte binding remains a separate check. -/
theorem decoded_count_laws_distinct (s η b : ℝ≥0) (hs : 0 < s) (hη : 0 < η) :
    ∃ ps qs : List PhotonArchiveParser.Phase,
      PhotonArchiveParser.parse PhotonArchiveParser.rawA = some ps ∧
      PhotonArchiveParser.parse PhotonArchiveParser.rawB = some qs ∧
      ((∫ n, (n.descFactorial 4 : ℝ) ∂PhotonGaussianModel.countLaw
          (ps.map PhotonArchiveBinding.evalPhase) s η b) -
        (∫ n, (n.descFactorial 4 : ℝ) ∂PhotonGaussianModel.countLaw
          (qs.map PhotonArchiveBinding.evalPhase) s η b) =
        (η : ℝ) ^ 4 * PhotonAlgebra.delta4 (Real.exp (-(s : ℝ)))) ∧
      PhotonGaussianModel.countLaw (ps.map PhotonArchiveBinding.evalPhase) s η b ≠
        PhotonGaussianModel.countLaw (qs.map PhotonArchiveBinding.evalPhase) s η b :=
  ⟨PhotonArchiveBinding.archiveA, PhotonArchiveBinding.archiveB,
    PhotonArchiveParser.parsedA, PhotonArchiveParser.parsedB,
    archived_count_laws_distinct s η b hs hη⟩

#print axioms archiveA_countLaw
#print axioms archiveB_countLaw
#print axioms archived_count_laws_distinct
#print axioms decoded_count_laws_distinct

end PhotonArchiveCountLaw
