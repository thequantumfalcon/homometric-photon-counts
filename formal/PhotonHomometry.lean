import Mathlib.Data.List.Perm.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Abel

namespace PhotonHomometry

/-- All ordered pair differences, including diagonal zeros and multiplicity. -/
def differences {G : Type*} [Sub G] (xs : List G) : List G :=
  xs.flatMap (fun x => xs.map (fun y => x - y))

/-- A list of translated copies; every indexed occurrence is preserved. -/
def translates {G : Type*} [Add G] (us vs : List G) : List G :=
  vs.flatMap (fun v => us.map (fun u => u + v))

theorem flatMap_swap {α β γ : Type*} (xs : List α) (ys : List β)
    (f : α → β → List γ) :
    (xs.flatMap fun x => ys.flatMap (f x)).Perm
      (ys.flatMap fun y => xs.flatMap (fun x => f x y)) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.flatMap_cons]
    exact (ih.append_left _).trans (List.flatMap_append_perm ys (f a) _)

theorem differences_perm {G : Type*} [Sub G] {xs ys : List G} (h : xs.Perm ys) :
    (differences xs).Perm (differences ys) :=
  h.flatMap (fun x _ => h.map (fun y => x - y))

theorem differences_translates {G : Type*} [AddCommGroup G] (us vs : List G) :
    (differences (translates us vs)).Perm
      (translates (differences us) (differences vs)) := by
  unfold differences translates
  simp only [List.flatMap_map, List.map_flatMap, List.map_map, List.flatMap_assoc,
    Function.comp_def]
  apply List.Perm.flatMap_left vs
  intro v _
  have h := flatMap_swap us vs (fun u w => us.map (fun z => u + v - (z + w)))
  apply h.trans
  apply List.Perm.flatMap_left vs
  intro w _
  apply List.Perm.flatMap_left us
  intro u _
  apply List.Perm.of_eq
  apply List.map_congr_left
  intro z _
  abel

theorem translates_homometric {G : Type*} [AddCommGroup G] (us vs ws : List G)
    (h : (differences vs).Perm (differences ws)) :
    (differences (translates us vs)).Perm (differences (translates us ws)) := by
  exact (differences_translates us vs).trans
    ((h.flatMap_right _).trans (differences_translates us ws).symm)

theorem integer_shifts_homometric :
    (differences ([0,31,63] : List Int)).Perm (differences [0,32,63]) := by decide +kernel

#print axioms differences_perm
#print axioms differences_translates
#print axioms translates_homometric
#print axioms integer_shifts_homometric

end PhotonHomometry
