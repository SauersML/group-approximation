import GroupApproximation.GGT.VanKampen.GRegionBoundaryValue
import GroupApproximation.GGT.VanKampen.SurgeryMap

/-!
# Face-set deletion schedules

This module gives the finite induction that turns a cellular peel of a
single-cycle `G`-region into the face-set insertion/erasure relation used by
Osin's Appendix.  A `FaceSetDeletionSchedule` names one boundary face at a
time.  Its constructor is exactly the `eraseFace` generator, while the
induction transports the tail relation from the erased face set to the
original set.  The topological peel lemma which constructs such a schedule
from a particular `Embedded.FaceSetBoundary` is kept as an explicit input;
`Surgery.MapCollapse.IsDiscRegion` supplies the map-level disc interface for
that construction.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.HullSC

universe u w v

namespace Embedded

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

noncomputable local instance faceDecidableEq :
    DecidableEq Delta.toCombMap.Face := Classical.decEq _

/-! ## Monotonicity in the selected face set -/

/-- A face-set word homotopy remains valid after enlarging the selected face
set.  This transports the recursive tail of a deletion schedule back to the
original region, so each erased face is still an allowed generator. -/
theorem FaceSetWordHomotopy.mono
    {faces₁ faces₂ : Finset Delta.toCombMap.Face}
    (hfaces : faces₁ ⊆ faces₂)
    {first second : List Delta.toCombMap.Dart}
    (homotopy : FaceSetWordHomotopy Delta faces₁ first second) :
    FaceSetWordHomotopy Delta faces₂ first second := by
  induction homotopy with
  | refl word => exact .refl word
  | eraseFace face hface before after =>
      exact .eraseFace face (hfaces hface) before after
  | eraseAlphaPair dart before after =>
      exact .eraseAlphaPair dart before after
  | symm _ ih => exact .symm ih
  | trans _ _ ihFirst ihSecond => exact .trans ihFirst ihSecond

/-! ## The explicit peel schedule -/

/-- A schedule deletes every face of a finite set by exposing one complete
face boundary at each step.  The empty schedule is the empty word.  A step
does not assert that a face is geometrically peelable; that assertion is the
topological input supplied by a planar region deletion lemma. -/
inductive FaceSetDeletionSchedule :
    Finset Delta.toCombMap.Face → List Delta.toCombMap.Dart → Prop
  | empty : FaceSetDeletionSchedule ∅ []
  | step {faces : Finset Delta.toCombMap.Face}
      (face : Delta.toCombMap.Face) (hface : face ∈ faces)
      (hne : face ≠ Delta.outerFace)
      (before after : List Delta.toCombMap.Dart)
      (tail : FaceSetDeletionSchedule (faces.erase face) (before ++ after)) :
      FaceSetDeletionSchedule faces
        (before ++ (Delta.faceBoundary face).darts ++ after)

namespace FaceSetDeletionSchedule

/-- A deletion schedule proves that the selected boundary cycle is homotopic
to the empty word.  The selected faces need only be non-outer; their `G`-cell
value hypotheses are consumed separately by the value theorem in
`GRegionBoundaryValue`. -/
theorem to_homotopy
    {faces : Finset Delta.toCombMap.Face} {cycle : List Delta.toCombMap.Dart}
    (schedule : FaceSetDeletionSchedule (Delta := Delta) faces cycle) :
    FaceSetWordHomotopy Delta faces cycle [] := by
  induction schedule with
  | empty => exact .refl []
  | @step faces face hface hne before after tail ih =>
      have htail : FaceSetWordHomotopy Delta faces (before ++ after) [] := by
        exact FaceSetWordHomotopy.mono
          (Finset.erase_subset _ _) ih
      exact .trans (.eraseFace face hface before after) htail

/-- The one-face schedule is the base model for the deletion induction. -/
theorem oneFace
    (face : Delta.toCombMap.Face) (hne : face ≠ Delta.outerFace) :
    FaceSetDeletionSchedule (Delta := Delta) {face}
      (Delta.faceBoundary face).darts := by
  have hface : face ∈ ({face} : Finset Delta.toCombMap.Face) := by simp
  have htail : FaceSetDeletionSchedule (Delta := Delta)
      (({face} : Finset Delta.toCombMap.Face).erase face) ([] ++ []) := by
    rw [Finset.erase_singleton]
    exact FaceSetDeletionSchedule.empty
  simpa only [List.nil_append, List.append_nil] using
    (FaceSetDeletionSchedule.step face hface hne [] [] htail)

/-- A singleton `SurgeryMap` disc whose boundary is the face boundary gives the
one-face schedule.  This is the map-level bridge used by a planar peel
producer. -/
theorem oneFace_of_discRegion
    {face : Delta.toCombMap.Face}
    (region : Surgery.MapCollapse.IsDiscRegion
      Delta.toCombMap ({face} : Finset Delta.toCombMap.Face))
    (boundary_eq : region.toBoundaryCycle.cycle =
      (Delta.faceBoundary face).darts)
    (hne : face ≠ Delta.outerFace) :
    FaceSetDeletionSchedule (Delta := Delta) {face}
      region.toBoundaryCycle.cycle := by
  rw [boundary_eq]
  exact oneFace face hne

/-- The zero-face schedule is the empty-word model. -/
theorem emptyModel :
    FaceSetDeletionSchedule (Delta := Delta) (∅ : Finset Delta.toCombMap.Face) [] :=
  FaceSetDeletionSchedule.empty

end FaceSetDeletionSchedule

/-! ## Boundary packaging and the Hull49 handoff -/

/-- A boundary together with the local planar peel data needed to run the
deletion induction.  The boundary field is est's `FaceSetBoundary`; the
schedule field is the output of the corresponding `SurgeryMap` face deletion
lemma. -/
structure FaceSetBoundaryPeeling
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces) where
  schedule : FaceSetDeletionSchedule (Delta := Delta) faces boundary.cycle

/-- A peeled single-cycle `G`-region has the required face-set homotopy. -/
theorem FaceSetBoundaryPeeling.to_homotopy
    {faces : Finset Delta.toCombMap.Face}
    {boundary : FaceSetBoundary Delta faces}
    (peeling : FaceSetBoundaryPeeling boundary) :
    FaceSetWordHomotopy Delta faces boundary.cycle [] :=
  FaceSetDeletionSchedule.to_homotopy peeling.schedule

/-- The value-one theorem consumes the homotopy produced by a planar peel. -/
theorem FaceSetBoundaryPeeling.cycle_value_eq_one
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    (peeling : FaceSetBoundaryPeeling boundary) :
    GGT.RelLetter.listVal (dartWord Delta boundary.cycle) = 1 :=
  boundary.cycle_value_eq_one_of_pasting peeling.to_homotopy

end Embedded

end VanKampen
end GGT
end GroupApproximation
