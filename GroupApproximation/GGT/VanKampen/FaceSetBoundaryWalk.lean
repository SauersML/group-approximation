import GroupApproximation.GGT.VanKampen.FaceSetBoundaryDeterminism
import GroupApproximation.GGT.VanKampen.FaceSetMoveAlgebra

/-!
# How the boundary walk moves, and what erasing a face does to it

Two independent ingredients of the planar ear argument are isolated here, both
proved with no hypothesis.

The first is the local shape of a `BoundaryStep`.  Determinism says the walk
has at most one successor; here we identify it.  While the next dart around
the current face is still a boundary dart the walk takes exactly that dart, so
consecutive boundary darts on one face are consecutive around that face and a
face meets the cycle in runs of the face rotation.  When the walk does leave
the current face, the next dart around that face faces a selected face, which
is the entry point for the dual-graph argument.

The second is the effect of erasing one selected face on the boundary-dart
predicate.  This is pure finite-set algebra: after erasing `face`, the boundary
darts are the old boundary darts off `face`, together with the reverses of the
darts of `face` that used to face another selected face.  That is the set the
peeled cycle `before ++ invDarts interior ++ after` has to enumerate.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

open GroupApproximation.HullSC

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

noncomputable local instance faceDecidableEqBoundaryWalk :
    DecidableEq Delta.toCombMap.Face := Classical.decEq _

/-! ## The boundary walk follows a face for as long as it can -/

/-- While the next dart around the current face is itself a boundary dart, the
boundary walk takes exactly that dart.  A boundary dart admits no internal
move, so the reflexive transitive closure in `BoundaryStep` stops at once. -/
theorem boundaryStep_eq_facePerm
    {faces : Finset Delta.toCombMap.Face}
    {d e : Delta.toCombMap.Dart}
    (hstep : BoundaryStep Delta faces d e)
    (hnext : IsBoundaryDart Delta faces (Delta.toCombMap.facePerm d)) :
    e = Delta.toCombMap.facePerm d := by
  rcases Relation.ReflTransGen.cases_head hstep.2.2 with heq | ⟨_, hmove, _⟩
  · exact heq.symm
  · exact absurd hmove (not_internalBoundaryMove_of_isBoundaryDart hnext)

/-- Consecutive boundary darts stay on the same face for as long as the face
rotation stays on the boundary. -/
theorem faceOf_eq_of_boundaryStep
    {faces : Finset Delta.toCombMap.Face}
    {d e : Delta.toCombMap.Dart}
    (hstep : BoundaryStep Delta faces d e)
    (hnext : IsBoundaryDart Delta faces (Delta.toCombMap.facePerm d)) :
    Delta.toCombMap.faceOf e = Delta.toCombMap.faceOf d := by
  rw [boundaryStep_eq_facePerm hstep hnext]
  exact Delta.toCombMap.faceOf_facePerm d

/-- When the boundary walk does leave the current face, the next dart around
that face is internal: the face across it is selected.  This is the dual-graph
edge that a run change produces. -/
theorem faceOf_alpha_facePerm_mem_of_ne
    {faces : Finset Delta.toCombMap.Face}
    {d e : Delta.toCombMap.Dart}
    (hstep : BoundaryStep Delta faces d e)
    (hne : e ≠ Delta.toCombMap.facePerm d) :
    Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (Delta.toCombMap.facePerm d)) ∈ faces := by
  rcases Relation.ReflTransGen.cases_head hstep.2.2 with heq | ⟨_, hmove, _⟩
  · exact absurd heq.symm hne
  · exact hmove.2.1

/-- The face rotation of a boundary dart stays on the same face, so it is a
boundary dart exactly when the face across it is unselected. -/
theorem isBoundaryDart_facePerm_iff
    {faces : Finset Delta.toCombMap.Face}
    {d : Delta.toCombMap.Dart}
    (hd : IsBoundaryDart Delta faces d) :
    IsBoundaryDart Delta faces (Delta.toCombMap.facePerm d) ↔
      Delta.toCombMap.faceOf
        (Delta.toCombMap.alpha (Delta.toCombMap.facePerm d)) ∉ faces := by
  constructor
  · intro hnext
    exact hnext.2
  · intro hnext
    refine ⟨?_, hnext⟩
    rw [Delta.toCombMap.faceOf_facePerm]
    exact hd.1

/-! ## Erasing one selected face -/

/-- The boundary darts of a face set with one face erased.  Pure finite-set
algebra: a dart is a boundary dart of `faces.erase face` exactly when it is
based in a selected face other than `face` and its reverse is either
unselected or based in `face`. -/
theorem isBoundaryDart_erase_iff
    {faces : Finset Delta.toCombMap.Face}
    (face : Delta.toCombMap.Face) (d : Delta.toCombMap.Dart) :
    IsBoundaryDart Delta (faces.erase face) d ↔
      (Delta.toCombMap.faceOf d ∈ faces ∧ Delta.toCombMap.faceOf d ≠ face ∧
        (Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∉ faces ∨
          Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = face)) := by
  constructor
  · intro hd
    obtain ⟨hmem, hnot⟩ := hd
    rw [Finset.mem_erase] at hmem
    refine ⟨hmem.2, hmem.1, ?_⟩
    by_cases hface :
        Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = face
    · exact Or.inr hface
    · left
      intro hin
      exact hnot (Finset.mem_erase.mpr ⟨hface, hin⟩)
  · rintro ⟨hmem, hne, hcase⟩
    refine ⟨Finset.mem_erase.mpr ⟨hne, hmem⟩, ?_⟩
    intro hin
    rw [Finset.mem_erase] at hin
    rcases hcase with hcase | hcase
    · exact hcase hin.2
    · exact hin.1 hcase

/-- A boundary dart off the erased face is still a boundary dart. -/
theorem isBoundaryDart_erase_of_isBoundaryDart
    {faces : Finset Delta.toCombMap.Face}
    {face : Delta.toCombMap.Face} {d : Delta.toCombMap.Dart}
    (hd : IsBoundaryDart Delta faces d)
    (hne : Delta.toCombMap.faceOf d ≠ face) :
    IsBoundaryDart Delta (faces.erase face) d := by
  rw [isBoundaryDart_erase_iff]
  exact ⟨hd.1, hne, Or.inl hd.2⟩

/-- The reverse of an interior dart of the erased face becomes a boundary
dart, provided the face across it is another selected face. -/
theorem isBoundaryDart_erase_alpha
    {faces : Finset Delta.toCombMap.Face}
    {face : Delta.toCombMap.Face} {y : Delta.toCombMap.Dart}
    (hy : Delta.toCombMap.faceOf y = face)
    (hmem : Delta.toCombMap.faceOf (Delta.toCombMap.alpha y) ∈ faces)
    (hne : Delta.toCombMap.faceOf (Delta.toCombMap.alpha y) ≠ face) :
    IsBoundaryDart Delta (faces.erase face) (Delta.toCombMap.alpha y) := by
  rw [isBoundaryDart_erase_iff]
  refine ⟨hmem, hne, Or.inr ?_⟩
  rw [Delta.toCombMap.alpha_involutive]
  exact hy

/-- A boundary dart of the erased set is either an old boundary dart off the
erased face, or the reverse of a dart of the erased face. -/
theorem isBoundaryDart_erase_cases
    {faces : Finset Delta.toCombMap.Face}
    {face : Delta.toCombMap.Face} {d : Delta.toCombMap.Dart}
    (hd : IsBoundaryDart Delta (faces.erase face) d) :
    IsBoundaryDart Delta faces d ∨
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = face := by
  rw [isBoundaryDart_erase_iff] at hd
  rcases hd.2.2 with hcase | hcase
  · exact Or.inl ⟨hd.1, hcase⟩
  · exact Or.inr hcase

/-! ## The reverse-orientation dart list -/

/-- Membership in the reverse-orientation dart list. -/
theorem mem_invDarts_iff
    (darts : List Delta.toCombMap.Dart) (d : Delta.toCombMap.Dart) :
    d ∈ invDarts Delta darts ↔ Delta.toCombMap.alpha d ∈ darts := by
  constructor
  · intro hd
    simp only [invDarts, List.mem_map, List.mem_reverse] at hd
    obtain ⟨y, hy, hyd⟩ := hd
    rw [← hyd, Delta.toCombMap.alpha_involutive]
    exact hy
  · intro hd
    simp only [invDarts, List.mem_map, List.mem_reverse]
    exact ⟨Delta.toCombMap.alpha d, hd, Delta.toCombMap.alpha_involutive d⟩

/-- The reverse-orientation list of a duplicate-free dart list is duplicate
free. -/
theorem invDarts_nodup
    {darts : List Delta.toCombMap.Dart} (h : darts.Nodup) :
    (invDarts Delta darts).Nodup := by
  have hrev : darts.reverse.Nodup := by simpa using h
  exact hrev.map Delta.toCombMap.alpha.injective

/-- The reverse-orientation list has the same length. -/
theorem invDarts_length (darts : List Delta.toCombMap.Dart) :
    (invDarts Delta darts).length = darts.length := by
  simp [invDarts]

end Embedded
end VanKampen
end GGT
end GroupApproximation
