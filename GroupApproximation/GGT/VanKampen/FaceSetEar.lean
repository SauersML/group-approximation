import GroupApproximation.GGT.VanKampen.FaceSetPeeledCycle
import GroupApproximation.GGT.VanKampen.FaceSetArcRotation
import GroupApproximation.GGT.VanKampen.FaceSetPeelProducer

/-!
# Assembling a planar ear from local peel data

`FaceSetEarData` is the planar ear written out in full: a selected face, the
contiguous arc of the boundary cycle it carries, the rest of its boundary, and
the three facts that make the peel work — the face is unpinched, the arc is the
face's only contact with the cycle, and the peeled word is a `BoundaryStep`
cycle of the erased face set.  `FaceSetEarData.toEar` builds the `FaceSetEar`
consumed by `FaceSetEar.toCertificate`, so it closes `FaceSetEarStatement` and
therefore the whole face-peel producer.

Everything set-theoretic in the erased boundary record is discharged here from
`mem_peeled_iff` and `nodup_peeled`; the empty branch, when the peeled face was
the last one, is proved rather than assumed.

## Why the walk fields are still hypotheses

The natural expectation is that the chain and closing of the peeled word follow
from `boundaryStep_right_unique` together with the face-boundary chain.  They do
not.  A `BoundaryStep` advances once around the current face and then rotates
around the vertex at its head, crossing every selected face there.  So erasing
the face `f` can create new boundary darts at any vertex where `f` sits with
both its edges internal, and those darts are the reverses of darts of
`interior`, but they belong at that vertex, not at the position the arc
occupied.  The word `before ++ invDarts interior ++ after` then holds exactly
the right darts, which is what `mem_peeled_iff` and `nodup_peeled` say, in the
wrong cyclic order.

So a producer of `FaceSetEarData` has to choose an ear that meets the boundary
walk only along its arc, not merely a face with one arc.  That locality is part
of the remaining planar content, alongside the existence of the ear itself.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

open GroupApproximation.HullSC

universe u w v

section Ear

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

noncomputable local instance faceDecidableEqEar :
    DecidableEq Delta.toCombMap.Face := Classical.decEq _

/-- The local data of one planar peel step. -/
structure FaceSetEarData
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces) where
  /-- The peeled face. -/
  face : Delta.toCombMap.Face
  /-- The peeled face is selected. -/
  face_mem : face ∈ faces
  /-- The cycle before the exposed arc. -/
  before : List Delta.toCombMap.Dart
  /-- The exposed arc. -/
  arc : List Delta.toCombMap.Dart
  /-- The cycle after the exposed arc. -/
  after : List Delta.toCombMap.Dart
  /-- The rest of the peeled face's boundary. -/
  interior : List Delta.toCombMap.Dart
  /-- The base shift identifying the face boundary with `arc ++ interior`. -/
  faceRotation : ℕ
  /-- The exposed arc is nonempty. -/
  arc_nonempty : arc ≠ []
  /-- The exposed arc is a contiguous block of the cycle. -/
  cycle_eq : boundary.cycle = before ++ arc ++ after
  /-- The arc opens the face boundary. -/
  face_eq : (Delta.faceBoundary face).darts.rotate faceRotation =
    arc ++ interior
  /-- No edge carries the peeled face on both sides. -/
  unpinched : ∀ y : Delta.toCombMap.Dart,
    Delta.toCombMap.faceOf y = face →
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha y) ≠ face
  /-- The arc is the face's only contact with the cycle. -/
  single_arc : ∀ d ∈ boundary.cycle,
    Delta.toCombMap.faceOf d = face → d ∈ arc
  /-- While faces remain, the peeled word is nonempty. -/
  peeled_nonempty : (faces.erase face).Nonempty →
    before ++ invDarts Delta interior ++ after ≠ []
  /-- The peeled word is a boundary walk of the erased face set. -/
  peeled_chain : (before ++ invDarts Delta interior ++ after).IsChain
    (BoundaryStep Delta (faces.erase face))
  /-- The peeled word closes up. -/
  peeled_closes : ∀ hne : before ++ invDarts Delta interior ++ after ≠ [],
    BoundaryStep Delta (faces.erase face)
      ((before ++ invDarts Delta interior ++ after).getLast hne)
      ((before ++ invDarts Delta interior ++ after).head hne)

namespace FaceSetEarData

variable {faces : Finset Delta.toCombMap.Face}
  {boundary : FaceSetBoundary Delta faces}

/-- When the peeled face was the last selected one, the cycle before the arc
is empty. -/
theorem before_eq_nil_of_erase_eq_empty
    (data : FaceSetEarData boundary)
    (hempty : faces.erase data.face = ∅) : data.before = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  obtain ⟨hb, hnef⟩ := isBoundaryDart_of_mem_before_after boundary
    data.cycle_eq data.single_arc (Or.inl hx)
  have hmem : Delta.toCombMap.faceOf x ∈ faces.erase data.face :=
    Finset.mem_erase.mpr ⟨hnef, hb.1⟩
  rw [hempty] at hmem
  simp at hmem

/-- When the peeled face was the last selected one, the cycle after the arc
is empty. -/
theorem after_eq_nil_of_erase_eq_empty
    (data : FaceSetEarData boundary)
    (hempty : faces.erase data.face = ∅) : data.after = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  obtain ⟨hb, hnef⟩ := isBoundaryDart_of_mem_before_after boundary
    data.cycle_eq data.single_arc (Or.inr hx)
  have hmem : Delta.toCombMap.faceOf x ∈ faces.erase data.face :=
    Finset.mem_erase.mpr ⟨hnef, hb.1⟩
  rw [hempty] at hmem
  simp at hmem

/-- When the peeled face was the last selected one it has no interior: every
one of its darts faced outside. -/
theorem interior_eq_nil_of_erase_eq_empty
    (data : FaceSetEarData boundary)
    (hempty : faces.erase data.face = ∅) : data.interior = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro y hy
  obtain ⟨_, hmem, hneq⟩ := faceOf_alpha_of_mem_interior boundary
    data.face_mem data.face_eq data.unpinched data.single_arc hy
  have hmem' : Delta.toCombMap.faceOf (Delta.toCombMap.alpha y) ∈
      faces.erase data.face := Finset.mem_erase.mpr ⟨hneq, hmem⟩
  rw [hempty] at hmem'
  simp at hmem'

/-- The peeled word of the last selected face is empty. -/
theorem peeled_eq_nil_of_erase_eq_empty
    (data : FaceSetEarData boundary)
    (hempty : faces.erase data.face = ∅) :
    data.before ++ invDarts Delta data.interior ++ data.after = [] := by
  rw [data.before_eq_nil_of_erase_eq_empty hempty,
    data.after_eq_nil_of_erase_eq_empty hempty,
    data.interior_eq_nil_of_erase_eq_empty hempty]
  simp [invDarts]

/-- The boundary record of the erased face set, when faces remain. -/
def erasedBoundary
    (data : FaceSetEarData boundary)
    (hne : (faces.erase data.face).Nonempty) :
    FaceSetBoundary Delta (faces.erase data.face) where
  faces_nonempty := hne
  all_gCells := fun g hg => boundary.all_gCells g (Finset.mem_of_mem_erase hg)
  cycle := data.before ++ invDarts Delta data.interior ++ data.after
  cycle_nonempty := data.peeled_nonempty hne
  cycle_nodup := nodup_peeled boundary data.face_mem data.cycle_eq
    data.face_eq data.unpinched data.single_arc
  cycle_mem_iff := fun d =>
    mem_peeled_iff boundary data.face_mem data.cycle_eq data.face_eq
      data.unpinched data.single_arc d
  cycle_chain := data.peeled_chain
  cycle_closes := data.peeled_closes (data.peeled_nonempty hne)

@[simp] theorem erasedBoundary_cycle
    (data : FaceSetEarData boundary)
    (hne : (faces.erase data.face).Nonempty) :
    (data.erasedBoundary hne).cycle =
      data.before ++ invDarts Delta data.interior ++ data.after := rfl

/-- Local peel data is exactly a planar ear. -/
def toEar (data : FaceSetEarData boundary) : FaceSetEar boundary where
  face := data.face
  face_mem := data.face_mem
  before := data.before
  arc := data.arc
  after := data.after
  interior := data.interior
  faceRotation := data.faceRotation
  arc_nonempty := data.arc_nonempty
  cycle_eq := data.cycle_eq
  face_eq := data.face_eq
  remainder := by
    by_cases hne : (faces.erase data.face).Nonempty
    · exact Or.inr ⟨data.erasedBoundary hne, rfl⟩
    · have hempty : faces.erase data.face = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      exact Or.inl ⟨hempty, data.peeled_eq_nil_of_erase_eq_empty hempty⟩

/-- Local peel data is a planar face-peel certificate. -/
def toCertificate (data : FaceSetEarData boundary) :
    PlanarFacePeelCertificate boundary :=
  data.toEar.toCertificate

end FaceSetEarData

end Ear

/-! ## The remaining planar statement -/

/-- The one planar fact the face-peel producer still needs: every selected face
set with a single boundary cycle has a peelable ear. -/
def FaceSetEarDataStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces),
    Nonempty (FaceSetEarData boundary)

/-- A peelable ear for every selected face set closes `FaceSetEarStatement`. -/
theorem faceSetEarStatement_of_earData
    (hdata : FaceSetEarDataStatement.{u, w, v}) :
    FaceSetEarStatement.{u, w, v} := by
  intro G _ Lambda W Delta faces boundary
  exact ⟨(hdata boundary).some.toEar⟩

/-- A peelable ear for every selected face set makes the whole face-deletion
schedule oracle free. -/
theorem faceSetBoundaryPeeling_of_earData
    (hdata : FaceSetEarDataStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces) :
    FaceSetBoundaryPeeling boundary :=
  faceSetBoundaryPeeling_of_earStatement
    (faceSetEarStatement_of_earData hdata) boundary

end Embedded
end VanKampen
end GGT
end GroupApproximation
