import GroupApproximation.GGT.VanKampen.FaceSetPeelWitness
import GroupApproximation.GGT.VanKampen.FaceSetMoveAlgebra
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryDeterminism

/-!
# Reducing the planar face-peel certificate to an ear

`PlanarFacePeelCertificate` mixes two very different things: a purely
word-combinatorial factorisation, and the planar topology which says that
some selected face can be removed leaving a single boundary cycle.  This file
separates them.

A `FaceSetEar` records only the planar data: a selected face, the contiguous
arc of the current boundary cycle it occupies, the rest of that face's
boundary read from the same base dart, and the boundary record of the erased
face set.  Every word move is then supplied by `FaceSetMoveAlgebra`:
`FaceSetMoveSequence.faceBoundary_rotate_nil` makes the base dart of the face
boundary free, and `FaceSetMoveSequence.to_invDarts` replaces the exposed arc
by the reverse orientation of the rest of the face.  So the arc need not be a
contiguous block of the face boundary in the stored orientation, and the
boundary cycle need not begin where the face boundary begins.

What is left open is exactly the planar statement `FaceSetEarStatement`: the
existence of the ear.  Nothing else in the peel is still missing; the finite
face-count induction is `faceSetBoundaryPeeling_of_faceSetBoundary_of_oracle`
and the word algebra is proved.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

open GroupApproximation.HullSC

universe u w v

section Producer

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

noncomputable local instance faceDecidableEqPeelProducer :
    DecidableEq Delta.toCombMap.Face := Classical.decEq _

/-! ## The planar ear datum -/

/-- The planar content of one peel step.  `arc` is the contiguous piece of the
current boundary cycle carried by `face`, and `interior` is the rest of that
face's boundary read from the same base dart, so that `arc ++ interior` is a
rotation of the stored face boundary.  After the face is removed the arc is
replaced by the reverse orientation of `interior`; `remainder` asserts that
the resulting word is the boundary cycle of the erased face set. -/
structure FaceSetEar
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces) where
  /-- The peeled face. -/
  face : Delta.toCombMap.Face
  /-- The peeled face is selected. -/
  face_mem : face ∈ faces
  /-- The part of the boundary cycle before the exposed arc. -/
  before : List Delta.toCombMap.Dart
  /-- The exposed arc of the boundary cycle. -/
  arc : List Delta.toCombMap.Dart
  /-- The part of the boundary cycle after the exposed arc. -/
  after : List Delta.toCombMap.Dart
  /-- The rest of the peeled face's boundary. -/
  interior : List Delta.toCombMap.Dart
  /-- The base shift identifying the face boundary with `arc ++ interior`. -/
  faceRotation : ℕ
  /-- The exposed arc is nonempty. -/
  arc_nonempty : arc ≠ []
  /-- The exposed arc is a contiguous block of the boundary cycle. -/
  cycle_eq : boundary.cycle = before ++ arc ++ after
  /-- The exposed arc is an initial segment of the face boundary based
  suitably. -/
  face_eq : (Delta.faceBoundary face).darts.rotate faceRotation =
    arc ++ interior
  /-- Removing the face leaves either nothing or a single boundary cycle. -/
  remainder :
    (faces.erase face = ∅ ∧
        before ++ invDarts Delta interior ++ after = []) ∨
      ∃ boundary' : FaceSetBoundary Delta (faces.erase face),
        boundary'.cycle = before ++ invDarts Delta interior ++ after

/-- A planar ear is a planar face-peel certificate.  All word bookkeeping is
discharged by the move algebra; the exposed face need not be `≠ outerFace` by
assumption because every selected face of a `FaceSetBoundary` is a `G`-cell. -/
def FaceSetEar.toCertificate
    {faces : Finset Delta.toCombMap.Face}
    {boundary : FaceSetBoundary Delta faces}
    (ear : FaceSetEar boundary) :
    PlanarFacePeelCertificate boundary where
  face := ear.face
  face_mem := ear.face_mem
  face_ne_outer := (boundary.all_gCells ear.face ear.face_mem).1
  next := ear.before ++ invDarts Delta ear.interior ++ ear.after
  arc := ear.arc
  arc_nonempty := ear.arc_nonempty
  arc_factor := ⟨ear.before, ear.after, ear.cycle_eq⟩
  moves := by
    have hfaceMoves : FaceSetMoveSequence (faces := faces)
        (ear.arc ++ ear.interior) [] := by
      have hrot := FaceSetMoveSequence.faceBoundary_rotate_nil
        (faces := faces) ear.face_mem ear.faceRotation
      rw [ear.face_eq] at hrot
      exact hrot
    have harc : FaceSetMoveSequence (faces := faces)
        ear.arc (invDarts Delta ear.interior) :=
      FaceSetMoveSequence.to_invDarts ear.arc ear.interior hfaceMoves
    have hstep := harc.append_context ear.before ear.after
    rw [ear.cycle_eq]
    exact hstep
  remainder := ear.remainder

/-- A family of planar ears is a family of planar face-peel certificates. -/
def planarFacePeelCertificate_of_ears
    (ears : ∀ {faces : Finset Delta.toCombMap.Face}
      (boundary : FaceSetBoundary Delta faces), FaceSetEar boundary)
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces) :
    PlanarFacePeelCertificate boundary :=
  (ears boundary).toCertificate

/-- A family of planar ears gives the complete face-deletion schedule of any
single-cycle `G`-region. -/
theorem faceSetBoundaryPeeling_of_ears
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    (ears : ∀ {faces : Finset Delta.toCombMap.Face}
      (boundary : FaceSetBoundary Delta faces), FaceSetEar boundary) :
    FaceSetBoundaryPeeling boundary := by
  apply faceSetBoundaryPeeling_of_faceSetBoundary_of_oracle boundary
  intro faces boundary
  exact (ears boundary).toCertificate.to_witness

/-! ## The one-face model at an arbitrary base dart -/

/-- The one-face certificate with a free base dart.  The earlier one-face
model required the boundary cycle to begin exactly where `Delta.faceBoundary`
begins; the rotation algebra removes that restriction. -/
def oneFace_planarCertificate_of_rotate
    {face : Delta.toCombMap.Face}
    {boundary : FaceSetBoundary Delta ({face} : Finset Delta.toCombMap.Face)}
    (k : ℕ)
    (hcycle : boundary.cycle = (Delta.faceBoundary face).darts.rotate k) :
    PlanarFacePeelCertificate boundary where
  face := face
  face_mem := by simp
  face_ne_outer := (boundary.all_gCells face (by simp)).1
  next := []
  arc := boundary.cycle
  arc_nonempty := boundary.cycle_nonempty
  arc_factor := ⟨[], [], by simp⟩
  moves := by
    rw [hcycle]
    exact FaceSetMoveSequence.faceBoundary_rotate_nil
      (faces := ({face} : Finset Delta.toCombMap.Face)) (by simp) k
  remainder := by
    left
    exact ⟨by simp, rfl⟩

end Producer

/-! ## The remaining planar statement -/

/-- The one planar fact still missing from the face-peel producer: every
selected face set with a single boundary cycle has an ear.  Everything else in
`PlanarFacePeelCertificate` is proved. -/
def FaceSetEarStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces),
    Nonempty (FaceSetEar boundary)

/-- The ear statement supplies the planar face-peel certificate in the exact
shape consumed by `hullLemma49SourceFacePastingStatement_of_planar`. -/
noncomputable def planarFacePeelCertificate_of_earStatement
    (hear : FaceSetEarStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces) :
    PlanarFacePeelCertificate boundary :=
  (hear boundary).some.toCertificate

/-- The ear statement makes `faceSetBoundaryPeeling_of_faceSetBoundary` free
of its local peel oracle. -/
theorem faceSetBoundaryPeeling_of_earStatement
    (hear : FaceSetEarStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces) :
    FaceSetBoundaryPeeling boundary := by
  apply faceSetBoundaryPeeling_of_faceSetBoundary_of_oracle boundary
  intro faces boundary
  exact ((hear boundary).some.toCertificate).to_witness

end Embedded
end VanKampen
end GGT
end GroupApproximation
