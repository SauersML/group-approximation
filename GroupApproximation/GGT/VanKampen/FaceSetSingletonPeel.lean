import GroupApproximation.GGT.VanKampen.FaceSetPeelProducer

/-!
# The unconditional one-face peel

For a single selected face the planar ear is the face itself, so the peel
should need no hypothesis at all.  The only obstruction is pinching: if some
edge has the chosen face on both sides then the boundary walk of the singleton
face set skips the pinched darts and is not a rotation of the stored face
boundary.

This file proves the one-face certificate for an unpinched face with no
further assumption.  The stored `Delta.faceBoundary` is exhibited as a
`FaceSetBoundary` of the singleton face set, the determinism theorem
`FaceSetBoundary.exists_cycle_eq_rotate` identifies any other singleton
boundary record with a rotation of it, and the rotation algebra of
`FaceSetMoveAlgebra` then supplies the move sequence.  In particular the base
dart of the given boundary record is free.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

open GroupApproximation.HullSC

universe u w v

/-- A face is unpinched when no edge carries it on both sides. -/
def FaceNotSelfAdjacent {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (face : Delta.toCombMap.Face) : Prop :=
  ∀ d : Delta.toCombMap.Dart, Delta.toCombMap.faceOf d = face →
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ≠ face

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

noncomputable local instance faceDecidableEqSingletonPeel :
    DecidableEq Delta.toCombMap.Face := Classical.decEq _

/-- For an unpinched face the boundary darts of the singleton face set are
exactly the darts of that face. -/
theorem isBoundaryDart_singleton_iff
    {face : Delta.toCombMap.Face}
    (hself : FaceNotSelfAdjacent Delta face)
    (d : Delta.toCombMap.Dart) :
    IsBoundaryDart Delta ({face} : Finset Delta.toCombMap.Face) d ↔
      Delta.toCombMap.faceOf d = face := by
  constructor
  · intro hd
    simpa using hd.1
  · intro hd
    refine ⟨by simpa using hd, ?_⟩
    intro hmem
    exact hself d hd (by simpa using hmem)

/-- For an unpinched face the boundary walk of the singleton face set never
crosses an internal edge. -/
theorem not_internalBoundaryMove_singleton
    {face : Delta.toCombMap.Face}
    (hself : FaceNotSelfAdjacent Delta face)
    (d e : Delta.toCombMap.Dart) :
    ¬ InternalBoundaryMove Delta ({face} : Finset Delta.toCombMap.Face) d e := by
  intro hmove
  have hd : Delta.toCombMap.faceOf d = face := by
    simpa using hmove.1
  have hda : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = face := by
    simpa using hmove.2.1
  exact hself d hd hda

/-- For an unpinched face one boundary step of the singleton face set is one
turn of the face rotation. -/
theorem boundaryStep_singleton_facePerm
    {face : Delta.toCombMap.Face}
    (hself : FaceNotSelfAdjacent Delta face)
    {d : Delta.toCombMap.Dart}
    (hd : Delta.toCombMap.faceOf d = face) :
    BoundaryStep Delta ({face} : Finset Delta.toCombMap.Face) d
      (Delta.toCombMap.facePerm d) := by
  refine ⟨(isBoundaryDart_singleton_iff hself d).2 hd, ?_,
    Relation.ReflTransGen.refl⟩
  refine (isBoundaryDart_singleton_iff hself
    (Delta.toCombMap.facePerm d)).2 ?_
  rw [Delta.toCombMap.faceOf_facePerm]
  exact hd

/-- The stored boundary of an unpinched `G`-cell is a `FaceSetBoundary` of the
singleton face set. -/
def singletonFaceSetBoundary
    {face : Delta.toCombMap.Face}
    (hself : FaceNotSelfAdjacent Delta face)
    (hne : face ≠ Delta.outerFace)
    (hone : GGT.RelLetter.listVal (Delta.faceWord face) = 1) :
    FaceSetBoundary Delta ({face} : Finset Delta.toCombMap.Face) where
  faces_nonempty := Finset.singleton_nonempty face
  all_gCells := by
    intro f hf
    rw [Finset.mem_singleton] at hf
    subst hf
    exact ⟨hne, hone⟩
  cycle := (Delta.faceBoundary face).darts
  cycle_nonempty := (Delta.faceBoundary face).nonempty
  cycle_nodup := (Delta.faceBoundary face).nodup
  cycle_mem_iff := by
    intro d
    rw [isBoundaryDart_singleton_iff hself d]
    exact (Delta.faceBoundary face).mem_iff d
  cycle_chain := by
    refine List.IsChain.imp_of_mem_imp ?_ (Delta.faceBoundary face).chain
    intro a b ha _ hab
    have haface : Delta.toCombMap.faceOf a = face :=
      ((Delta.faceBoundary face).mem_iff a).1 ha
    have hstep := boundaryStep_singleton_facePerm hself haface
    rw [hab] at hstep
    exact hstep
  cycle_closes := by
    have hlast : Delta.toCombMap.faceOf
        ((Delta.faceBoundary face).darts.getLast
          (Delta.faceBoundary face).nonempty) = face :=
      ((Delta.faceBoundary face).mem_iff _).1
        (List.getLast_mem (Delta.faceBoundary face).nonempty)
    have hstep := boundaryStep_singleton_facePerm hself hlast
    rw [(Delta.faceBoundary face).closes] at hstep
    exact hstep

/-- The cycle of the singleton boundary record is the stored face boundary. -/
theorem singletonFaceSetBoundary_cycle
    {face : Delta.toCombMap.Face}
    (hself : FaceNotSelfAdjacent Delta face)
    (hne : face ≠ Delta.outerFace)
    (hone : GGT.RelLetter.listVal (Delta.faceWord face) = 1) :
    (singletonFaceSetBoundary hself hne hone).cycle =
      (Delta.faceBoundary face).darts := rfl

/-- Any boundary record of an unpinched singleton face set is a rotation of
the stored face boundary. -/
theorem exists_singleton_cycle_eq_rotate
    {face : Delta.toCombMap.Face}
    (hself : FaceNotSelfAdjacent Delta face)
    (boundary : FaceSetBoundary Delta ({face} : Finset Delta.toCombMap.Face)) :
    ∃ k : ℕ, boundary.cycle = (Delta.faceBoundary face).darts.rotate k := by
  have hne : face ≠ Delta.outerFace :=
    (boundary.all_gCells face (by simp)).1
  have hone : GGT.RelLetter.listVal (Delta.faceWord face) = 1 :=
    (boundary.all_gCells face (by simp)).2
  obtain ⟨k, hk⟩ := FaceSetBoundary.exists_cycle_eq_rotate boundary
    (singletonFaceSetBoundary hself hne hone)
  rw [singletonFaceSetBoundary_cycle] at hk
  exact ⟨k, hk⟩

/-- The unconditional one-face peel certificate: every boundary record of an
unpinched selected face has a planar face-peel certificate, with no
assumption on its base dart. -/
theorem nonempty_oneFace_planarCertificate_of_notSelfAdjacent
    {face : Delta.toCombMap.Face}
    (hself : FaceNotSelfAdjacent Delta face)
    (boundary : FaceSetBoundary Delta ({face} : Finset Delta.toCombMap.Face)) :
    Nonempty (PlanarFacePeelCertificate boundary) := by
  obtain ⟨k, hk⟩ := exists_singleton_cycle_eq_rotate hself boundary
  exact ⟨oneFace_planarCertificate_of_rotate k hk⟩

/-- The unconditional one-face peel schedule. -/
theorem faceSetBoundaryPeeling_singleton_of_notSelfAdjacent
    {face : Delta.toCombMap.Face}
    (hself : FaceNotSelfAdjacent Delta face)
    (boundary : FaceSetBoundary Delta ({face} : Finset Delta.toCombMap.Face)) :
    FaceSetBoundaryPeeling boundary := by
  have hne : face ≠ Delta.outerFace :=
    (boundary.all_gCells face (by simp)).1
  obtain ⟨k, hk⟩ := exists_singleton_cycle_eq_rotate hself boundary
  have hmoves : FaceSetMoveSequence
      (faces := ({face} : Finset Delta.toCombMap.Face)) boundary.cycle [] := by
    rw [hk]
    exact FaceSetMoveSequence.faceBoundary_rotate_nil
      (faces := ({face} : Finset Delta.toCombMap.Face)) (by simp) k
  have htail : FaceSetDeletionSchedule (Delta := Delta)
      (({face} : Finset Delta.toCombMap.Face).erase face) [] := by
    rw [Finset.erase_singleton]
    exact FaceSetDeletionSchedule.empty
  exact ⟨FaceSetDeletionSchedule.step face (by simp) hne
    hmoves.to_homotopy htail⟩

end Embedded
end VanKampen
end GGT
end GroupApproximation
