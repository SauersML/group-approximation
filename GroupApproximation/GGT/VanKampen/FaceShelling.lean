import GroupApproximation.GGT.VanKampen.FaceSetMoveAlgebra

/-!
# Shellings of a selected face set

A shelling builds a region one face at a time, each new face attaching to the
union of its predecessors along a single arc.  The arc is allowed to be empty,
so the first face of a shelling attaches to nothing, and a region pinched at a
vertex, two squares meeting at a point, is shellable: the face across the pinch
attaches along the empty arc and its insertion cancels nothing.

The step is a single move of the existing algebra.  If the current walk reads
`before ++ arc ++ after` and the new face's boundary, read from a suitable base
dart, is `exposed ++ invDarts arc`, then the new walk is `before ++ exposed ++
after`, because the face word is trivial and so `exposed` and `arc` are
connected by moves.  No planarity, no single boundary cycle, no unpinched face
and no ear enter here.

What remains is `RegionShellingStatement`: that the boundary cycle of a
selected face set is the last walk of some shelling.  That is the planar
content, and a shelling read backwards is an ear decomposition, so this is the
same combinatorial core as the ear, reached from the other end.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u w v

namespace Embedded

open GroupApproximation.HullSC

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-! ## Reverse orientation is an involution -/

/-- Reverse orientation turns concatenation around. -/
theorem invDarts_append (first second : List Delta.toCombMap.Dart) :
    invDarts Delta (first ++ second) =
      invDarts Delta second ++ invDarts Delta first := by
  simp [invDarts]

/-- Reverse orientation is an involution on dart lists. -/
theorem invDarts_invDarts (darts : List Delta.toCombMap.Dart) :
    invDarts Delta (invDarts Delta darts) = darts := by
  induction darts with
  | nil => simp [invDarts]
  | cons dart darts ih =>
      rw [invDarts_cons, invDarts_append, ih]
      simp [invDarts, Delta.toCombMap.alpha_involutive]

/-! ## The shelling step -/

/-- Attaching one face along an arc is a move of the face-set algebra.  The
face boundary read from a suitable base dart is the exposed part followed by
the reverse of the arc it covers, and the exposed part then replaces the arc. -/
theorem FaceSetMoveSequence.shellStep
    {faces : Finset Delta.toCombMap.Face}
    {face : Delta.toCombMap.Face} (hface : face ∈ faces)
    (before arc after exposed : List Delta.toCombMap.Dart) (k : ℕ)
    (hrot : (Delta.faceBoundary face).darts.rotate k =
      exposed ++ invDarts Delta arc) :
    FaceSetMoveSequence (faces := faces)
      (before ++ arc ++ after) (before ++ exposed ++ after) := by
  have hface_nil : FaceSetMoveSequence (faces := faces)
      (exposed ++ invDarts Delta arc) [] := by
    have hrotnil := FaceSetMoveSequence.faceBoundary_rotate_nil hface k
    rw [hrot] at hrotnil
    exact hrotnil
  have hexposed : FaceSetMoveSequence (faces := faces) exposed
      (invDarts Delta (invDarts Delta arc)) :=
    FaceSetMoveSequence.to_invDarts exposed (invDarts Delta arc) hface_nil
  rw [invDarts_invDarts] at hexposed
  exact (hexposed.append_context before after).symm

/-! ## Shellings -/

/-- A shelling of a selected face set: an ordering of faces in which each new
face attaches to the current walk along one arc, which may be empty. -/
inductive FaceShelling {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (faces : Finset Delta.toCombMap.Face) :
    List Delta.toCombMap.Face → List Delta.toCombMap.Dart → Prop
  | empty : FaceShelling Delta faces [] []
  | step {l : List Delta.toCombMap.Face}
      {before arc after exposed : List Delta.toCombMap.Dart}
      (face : Delta.toCombMap.Face) (hface : face ∈ faces) (k : ℕ)
      (hrot : (Delta.faceBoundary face).darts.rotate k =
        exposed ++ invDarts Delta arc)
      (rest : FaceShelling Delta faces l (before ++ arc ++ after)) :
      FaceShelling Delta faces (face :: l) (before ++ exposed ++ after)

/-- The last walk of a shelling is trivial in the face-set algebra. -/
theorem faceSetMoveSequence_of_shelling
    {faces : Finset Delta.toCombMap.Face}
    {l : List Delta.toCombMap.Face} {walk : List Delta.toCombMap.Dart}
    (shelling : FaceShelling Delta faces l walk) :
    FaceSetMoveSequence (faces := faces) walk [] := by
  induction shelling with
  | empty => exact FaceSetMoveSequence.refl []
  | @step l before arc after exposed face hface k hrot _rest ih =>
      exact ((FaceSetMoveSequence.shellStep hface before arc after exposed k
        hrot).symm).trans ih

/-- The last walk of a shelling pastes to the empty word. -/
theorem faceSetWordHomotopy_of_shelling
    {faces : Finset Delta.toCombMap.Face}
    {l : List Delta.toCombMap.Face} {walk : List Delta.toCombMap.Dart}
    (shelling : FaceShelling Delta faces l walk) :
    FaceSetWordHomotopy Delta faces walk [] :=
  (faceSetMoveSequence_of_shelling shelling).to_homotopy

/-- A shelling of a boundary cycle gives the boundary value identity. -/
theorem cycle_value_eq_one_of_shelling
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    {l : List Delta.toCombMap.Face}
    (shelling : FaceShelling Delta faces l boundary.cycle) :
    GGT.RelLetter.listVal (dartWord Delta boundary.cycle) = 1 :=
  boundary.cycle_value_eq_one_of_pasting (faceSetWordHomotopy_of_shelling shelling)

end Embedded

/-! ## The remaining planar statement -/

/-- The one planar fact still missing: the boundary cycle of a selected face
set is the last walk of a shelling.  A shelling read backwards is an ear
decomposition, so this is the ear statement reached from the other end, minus
its unpinchedness and single-cycle-remainder conditions. -/
def RegionShellingStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (boundary : Embedded.FaceSetBoundary Delta faces),
    ∃ l : List Delta.toCombMap.Face,
      Embedded.FaceShelling Delta faces l boundary.cycle

/-- A shelling for every selected face set gives the face-pasting homotopy with
no further hypothesis. -/
theorem faceSetWordHomotopy_of_regionShelling
    (hshelling : RegionShellingStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (boundary : Embedded.FaceSetBoundary Delta faces) :
    Embedded.FaceSetWordHomotopy Delta faces boundary.cycle [] := by
  obtain ⟨l, shelling⟩ := hshelling boundary
  exact Embedded.faceSetWordHomotopy_of_shelling shelling

end VanKampen
end GGT
end GroupApproximation
