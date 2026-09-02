import GroupApproximation.GGT.VanKampen.FaceSetMoveAlgebra
import GroupApproximation.GGT.VanKampen.FaceSetWordHomotopyCore

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
      have hinv : Delta.toCombMap.alpha (Delta.toCombMap.alpha dart) = dart :=
        Delta.toCombMap.alpha_involutive dart
      simp [invDarts, hinv]

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

/-! ## Model checks -/

/-- One face is shellable from any base dart. -/
theorem shelling_oneFace
    {faces : Finset Delta.toCombMap.Face}
    {face : Delta.toCombMap.Face} (hface : face ∈ faces) (k : ℕ) :
    FaceShelling Delta faces [face]
      ((Delta.faceBoundary face).darts.rotate k) := by
  have hrot : (Delta.faceBoundary face).darts.rotate k =
      (Delta.faceBoundary face).darts.rotate k ++
        invDarts Delta ([] : List Delta.toCombMap.Dart) := by
    rw [invDarts_nil]
    simp
  have hempty : FaceShelling Delta faces []
      (([] : List Delta.toCombMap.Dart) ++ ([] : List Delta.toCombMap.Dart) ++
        ([] : List Delta.toCombMap.Dart)) := by
    simpa using FaceShelling.empty
  have hstep := FaceShelling.step (l := [])
    (before := ([] : List Delta.toCombMap.Dart))
    (arc := ([] : List Delta.toCombMap.Dart))
    (after := ([] : List Delta.toCombMap.Dart))
    (exposed := (Delta.faceBoundary face).darts.rotate k)
    face hface k hrot hempty
  simpa using hstep

/-- Two faces meeting along an arc are shellable. -/
theorem shelling_twoFace
    {faces : Finset Delta.toCombMap.Face}
    {first second : Delta.toCombMap.Face}
    (hfirst : first ∈ faces) (hsecond : second ∈ faces)
    (kfirst ksecond : ℕ)
    (before arc after exposed : List Delta.toCombMap.Dart)
    (hrotFirst : (Delta.faceBoundary first).darts.rotate kfirst =
      before ++ arc ++ after)
    (hrotSecond : (Delta.faceBoundary second).darts.rotate ksecond =
      exposed ++ invDarts Delta arc) :
    FaceShelling Delta faces [second, first] (before ++ exposed ++ after) := by
  have hfirstShell : FaceShelling Delta faces [first]
      (before ++ arc ++ after) := by
    have hone := shelling_oneFace hfirst kfirst
    rw [hrotFirst] at hone
    exact hone
  exact FaceShelling.step second hsecond ksecond hrotSecond hfirstShell

/-- Two faces meeting only at a vertex are shellable: the second attaches along
the empty arc, and its insertion cancels nothing. -/
theorem shelling_pinch
    {faces : Finset Delta.toCombMap.Face}
    {first second : Delta.toCombMap.Face}
    (hfirst : first ∈ faces) (hsecond : second ∈ faces)
    (kfirst ksecond : ℕ) :
    FaceShelling Delta faces [second, first]
      ((Delta.faceBoundary first).darts.rotate kfirst ++
        (Delta.faceBoundary second).darts.rotate ksecond) := by
  have hrot : (Delta.faceBoundary second).darts.rotate ksecond =
      (Delta.faceBoundary second).darts.rotate ksecond ++
        invDarts Delta ([] : List Delta.toCombMap.Dart) := by
    rw [invDarts_nil]
    simp
  have hfirstShell : FaceShelling Delta faces [first]
      ((Delta.faceBoundary first).darts.rotate kfirst ++
        ([] : List Delta.toCombMap.Dart) ++
        ([] : List Delta.toCombMap.Dart)) := by
    simpa using shelling_oneFace hfirst kfirst
  have hstep := FaceShelling.step (l := [first])
    (before := (Delta.faceBoundary first).darts.rotate kfirst)
    (arc := ([] : List Delta.toCombMap.Dart))
    (after := ([] : List Delta.toCombMap.Dart))
    (exposed := (Delta.faceBoundary second).darts.rotate ksecond)
    second hsecond ksecond hrot hfirstShell
  simpa using hstep

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
