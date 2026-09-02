import GroupApproximation.GGT.VanKampen.GRegionBoundaryValue
import GroupApproximation.GGT.VanKampen.SurgeryMap

/-!
# Face-set deletion schedules

This module gives the finite induction that turns a cellular peel of a
single-cycle `G`-region into the face-set insertion/erasure relation used by
Osin's Appendix.  A `FaceSetDeletionSchedule` names one boundary face at a
time.  A step carries the finite word-move factorisation which exposes that
face: in the non-adjacent case it is the single `eraseFace` generator, while
for adjacent selected faces it may first insert the complete face boundary
and then erase internal `alpha`-pairs.  The induction transports the tail
relation from the erased face set to the original set.  The topological
producer of these local factorisations is deliberately a separate datum; the
finite word induction itself is independent of a particular planar surgery.
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
      {cycle next : List Delta.toCombMap.Dart}
      (expose : FaceSetWordHomotopy Delta faces cycle next)
      (tail : FaceSetDeletionSchedule (faces.erase face) next) :
      FaceSetDeletionSchedule faces cycle

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
  | @step faces face hface hne cycle next expose tail ih =>
      have htail : FaceSetWordHomotopy Delta faces next [] := by
        exact FaceSetWordHomotopy.mono
          (Finset.erase_subset _ _) ih
      exact expose.trans htail

end FaceSetDeletionSchedule

/-! A local peel step records the geometric arc which is exposed.  The
`expose` field is intentionally a word-level factorisation: its proof may be
the direct face insertion/erasure, or a sequence of such moves together with
internal `alpha`-pair cancellations.  In particular, the face boundary need
not occur as one contiguous block in the current outer cycle. -/

structure FaceSetPeelStep
    {faces : Finset Delta.toCombMap.Face}
    (cycle : List Delta.toCombMap.Dart) where
  face : Delta.toCombMap.Face
  face_mem : face ∈ faces
  face_ne_outer : face ≠ Delta.outerFace
  next : List Delta.toCombMap.Dart
  arc : List Delta.toCombMap.Dart
  arc_nonempty : arc ≠ []
  arc_factor : ∃ before after : List Delta.toCombMap.Dart,
    cycle = before ++ arc ++ after
  expose : FaceSetWordHomotopy Delta faces cycle
    next
  tail : FaceSetDeletionSchedule (faces.erase face) next

/-! ## Explicit finite move factorisations -/

/-- One elementary move in a boundary peel.  The two insertion constructors
are the symmetric forms of the deletion generators; naming them explicitly
makes the ``insert the remaining face boundary, then cancel internal
`alpha`-pairs'' factorisation available to geometric producers. -/
inductive FaceSetElementaryMove
    {faces : Finset Delta.toCombMap.Face} :
    List Delta.toCombMap.Dart → List Delta.toCombMap.Dart → Prop
  | eraseFace (face : Delta.toCombMap.Face) (hface : face ∈ faces)
      (before after : List Delta.toCombMap.Dart) :
      FaceSetElementaryMove
        (before ++ (Delta.faceBoundary face).darts ++ after)
        (before ++ after)
  | insertFace (face : Delta.toCombMap.Face) (hface : face ∈ faces)
      (before after : List Delta.toCombMap.Dart) :
      FaceSetElementaryMove
        (before ++ after)
        (before ++ (Delta.faceBoundary face).darts ++ after)
  | eraseAlphaPair (dart : Delta.toCombMap.Dart)
      (before after : List Delta.toCombMap.Dart) :
      FaceSetElementaryMove
        (before ++ dart :: Delta.toCombMap.alpha dart :: after)
        (before ++ after)
  | insertAlphaPair (dart : Delta.toCombMap.Dart)
      (before after : List Delta.toCombMap.Dart) :
      FaceSetElementaryMove
        (before ++ after)
        (before ++ dart :: Delta.toCombMap.alpha dart :: after)

/-- A finite sequence of elementary peel moves. -/
inductive FaceSetMoveSequence
    {faces : Finset Delta.toCombMap.Face} :
    List Delta.toCombMap.Dart → List Delta.toCombMap.Dart → Prop
  | refl (word : List Delta.toCombMap.Dart) :
      FaceSetMoveSequence word word
  | cons {first second third : List Delta.toCombMap.Dart}
      (head : FaceSetElementaryMove (faces := faces) first second)
      (tail : FaceSetMoveSequence (faces := faces) second third) :
      FaceSetMoveSequence first third

namespace FaceSetMoveSequence

/-- Elementary moves are exactly the generators of the existing homotopy. -/
theorem to_elementary_homotopy
    {faces : Finset Delta.toCombMap.Face}
    {first second : List Delta.toCombMap.Dart}
    (move : FaceSetElementaryMove (faces := faces) first second) :
    FaceSetWordHomotopy Delta faces first second := by
  cases move with
  | eraseFace face hface before after =>
      exact FaceSetWordHomotopy.eraseFace face hface before after
  | insertFace face hface before after =>
      exact (FaceSetWordHomotopy.eraseFace face hface before after).symm
  | eraseAlphaPair dart before after =>
      exact FaceSetWordHomotopy.eraseAlphaPair dart before after
  | insertAlphaPair dart before after =>
      exact (FaceSetWordHomotopy.eraseAlphaPair dart before after).symm

/-- A finite factorisation gives a `FaceSetWordHomotopy`. -/
theorem to_homotopy
    {faces : Finset Delta.toCombMap.Face}
    {first second : List Delta.toCombMap.Dart}
    (moves : FaceSetMoveSequence (faces := faces) first second) :
    FaceSetWordHomotopy Delta faces first second := by
  induction moves with
  | refl word => exact .refl word
  | cons head tail ih =>
      exact (head.to_elementary_homotopy).trans ih

end FaceSetMoveSequence

/-- Build a peel step from an explicit factorisation.  Geometric lemmas only
have to provide the nonempty exposed arc and the finite list of elementary
insertions/cancellations; the face-count induction is then automatic. -/
def FaceSetPeelStep.of_moves
    {faces : Finset Delta.toCombMap.Face}
    {cycle next arc : List Delta.toCombMap.Dart}
    (face : Delta.toCombMap.Face) (hface : face ∈ faces)
    (hne : face ≠ Delta.outerFace)
    (hfactor : ∃ before after : List Delta.toCombMap.Dart,
      cycle = before ++ arc ++ after)
    (harc : arc ≠ [])
    (moves : FaceSetMoveSequence (faces := faces) cycle
      next)
    (tail : FaceSetDeletionSchedule (Delta := Delta) (faces.erase face) next) :
    FaceSetPeelStep (faces := faces) cycle where
  face := face
  face_mem := hface
  face_ne_outer := hne
  next := next
  arc := arc
  arc_nonempty := harc
  arc_factor := hfactor
  expose := moves.to_homotopy
  tail := tail

/-- A geometric peel step is exactly one constructor of the finite schedule. -/
theorem FaceSetPeelStep.to_schedule
    {faces : Finset Delta.toCombMap.Face}
    {cycle : List Delta.toCombMap.Dart}
    (step : FaceSetPeelStep (faces := faces) cycle) :
    FaceSetDeletionSchedule (Delta := Delta) faces cycle :=
  .step step.face step.face_mem step.face_ne_outer step.expose step.tail

/-- The direct contiguous-block step is the old cactus/one-face model. -/
def FaceSetPeelStep.direct
    {faces : Finset Delta.toCombMap.Face}
    {before after : List Delta.toCombMap.Dart}
    (face : Delta.toCombMap.Face) (hface : face ∈ faces)
    (hne : face ≠ Delta.outerFace)
    (tail : FaceSetDeletionSchedule (Delta := Delta) (faces.erase face)
      (before ++ after)) :
    FaceSetPeelStep (faces := faces)
      (before ++ (Delta.faceBoundary face).darts ++ after) where
  face := face
  face_mem := hface
  face_ne_outer := hne
  next := before ++ after
  arc := (Delta.faceBoundary face).darts
  arc_nonempty := (Delta.faceBoundary face).nonempty
  arc_factor := ⟨before, after, rfl⟩
  expose := .eraseFace face hface before after
  tail := tail

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
    (FaceSetDeletionSchedule.step face hface hne
      (.eraseFace face hface [] []) htail)

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

/-- Named boundary-level form of the face-set homotopy conclusion. -/
theorem faceSetWordHomotopy_of_faceSetBoundary
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    (peeling : FaceSetBoundaryPeeling boundary) :
    FaceSetWordHomotopy Delta faces boundary.cycle [] :=
  peeling.to_homotopy

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
