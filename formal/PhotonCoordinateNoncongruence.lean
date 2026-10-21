import PhotonCoordinateHomometry
import PhotonCoordinateOrder

namespace PhotonCoordinateNoncongruence

open PhotonCoordinateInput PhotonCoordinateGeometry PhotonCoordinateHomometry
open PhotonCoordinateOrder

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem sorted_perm_eq {xs ys : List ℝ} (hx : xs.Pairwise (· < ·))
    (hy : ys.Pairwise (· < ·)) (h : xs.Perm ys) : xs = ys :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ ha hb => le_antisymm ha hb)
    (hx.imp fun h => le_of_lt h) (hy.imp fun h => le_of_lt h) h

theorem no_translation (c : ℝ) :
    ¬ positionsA.Perm (positionsB.map (fun x => x + c)) := by
  intro h
  have hs : (positionsB.map (fun x => x + c)).Pairwise (· < ·) :=
    recordsB_positions_sorted.map _ (fun _ _ h => by linarith)
  have he := sorted_perm_eq recordsA_positions_sorted hs h
  have h0 := congrArg (fun xs : List ℝ => xs[0]?) he
  have h21 := congrArg (fun xs : List ℝ => xs[21]?) he
  norm_num [positionsA, positionsB, recordsA, recordsB, position,
    PhotonCoordinates.coordinate, angle] at h0 h21
  linarith

theorem no_reflection (c : ℝ) :
    ¬ positionsA.Perm (positionsB.map (fun x => c - x)) := by
  intro h
  have hr : positionsB.reverse.Pairwise (fun a b => b < a) :=
    List.pairwise_reverse.mpr recordsB_positions_sorted
  have hs : (positionsB.reverse.map (fun x => c - x)).Pairwise (· < ·) :=
    hr.map _ (fun _ _ h => by linarith)
  have hp := h.trans ((List.reverse_perm positionsB).symm.map (fun x => c - x))
  have he := sorted_perm_eq recordsA_positions_sorted hs hp
  have h0 := congrArg (fun xs : List ℝ => xs[0]?) he
  have h1 := congrArg (fun xs : List ℝ => xs[1]?) he
  norm_num [positionsA, positionsB, recordsA, recordsB, position,
    PhotonCoordinates.coordinate, angle] at h0 h1
  ring_nf at h1
  linarith

theorem positions_not_permutation : ¬ positionsA.Perm positionsB := by
  simpa using no_translation 0

#print axioms no_translation
#print axioms no_reflection
#print axioms positions_not_permutation

end PhotonCoordinateNoncongruence
