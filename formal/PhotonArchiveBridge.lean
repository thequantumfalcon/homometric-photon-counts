import PhotonArchiveParsed

namespace PhotonArchiveParser

/-- The archived A phase-array text decodes to a permutation of the formal geometry. -/
theorem decodedA_geometry :
    ∃ ps : List Phase, parse rawA = some ps ∧
      (ps.map PhotonArchiveBinding.evalPhase).Perm PhotonGeometry.geometryA :=
  ⟨PhotonArchiveBinding.archiveA, parsedA, PhotonArchiveBinding.archiveA_geometry⟩

/-- The archived B phase-array text decodes to a permutation of the formal geometry. -/
theorem decodedB_geometry :
    ∃ ps : List Phase, parse rawB = some ps ∧
      (ps.map PhotonArchiveBinding.evalPhase).Perm PhotonGeometry.geometryB :=
  ⟨PhotonArchiveBinding.archiveB, parsedB, PhotonArchiveBinding.archiveB_geometry⟩

#print axioms decodedA_geometry
#print axioms decodedB_geometry

end PhotonArchiveParser
