import GroupApproximation.GGT.VanKampen.ClosedWalkFaceColouring
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketClosedWalkNoncrossing
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketSectionFaceSet
import GroupApproximation.Meta.AxiomGuard

/-!
# A pocket walk oriented by every colouring bounds a pocket face set

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b):

> "Let us consider the subdiagram `Γ_1` of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where
> `s_1, s_2` are side arcs of some of `Γ_{i,1}`'s and `t_1, t_2` are subpaths of `∂Π` and the
> section `q_1` of `∂Δ`, respectively; (ii) `Γ_1` contains all `Γ_{i,1}`'s."

This is step (D) of the parity route to `SectionPocketFaceSetInput`.  Let a closed walk in a planar
map use distinct darts and no edge in both directions, and let every two-colouring of the faces
changing colour exactly across the walk give the faces of all walk darts one colour.  Then the
walk is the boundary cycle of that colour class
(`ClosedWalkFaceColouring.exists_boundaryCycle_of_orient`), and a boundary cycle in walk order is a
noncrossing closed walk (`Surgery.MapCollapse.BoundaryCycle.isNoncrossingClosedWalk`).

* `ClosedWalkFaceColouring.isNoncrossingClosedWalk_of_orient`: the walk is a noncrossing closed
  walk.
* `PocketWalk.exists_pocketFaceSet_closedWalk_of_orient`: a pocket walk `s_1 t_1 s_2 t_2` with
  these properties and a relator cell on its side is the boundary cycle of a pocket face set in
  walk order, the conclusion of `SectionPocketFaceSetInput`.

Not proved here, for the pocket walk of two exterior regions: the four walk facts (distinct darts,
no edge in both directions, `chain`, `closes`), the orientation of every colouring (step (C)), and
the relator cell on the side.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

namespace ClosedWalkFaceColouring

/-- **A closed walk oriented by every colouring is noncrossing.**  In a planar map, let `w` be a
closed walk of distinct darts using no edge in both directions.  If every two-colouring of the
faces changing colour exactly across `w` gives the faces of all walk darts one colour, then `w` is
a noncrossing closed walk. -/
theorem isNoncrossingClosedWalk_of_orient {M : CombMap.{u}} (hM : M.IsPlanar) {w : List M.Dart}
    (hne : w ≠ []) (hnodup : w.Nodup) (halpha : ∀ d ∈ w, M.alpha d ∉ w)
    (hchain : w.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hcloses : M.vertexOf (M.alpha (w.getLast hne)) = M.vertexOf (w.head hne))
    (horient : ∀ faces : Finset M.Face,
      (∀ d, ¬ (M.faceOf (M.alpha d) ∈ faces ↔ M.faceOf d ∈ faces) ↔ walkKeep M w d) →
        ∀ d ∈ w, ∀ e ∈ w, (M.faceOf d ∈ faces ↔ M.faceOf e ∈ faces)) :
    IsNoncrossingClosedWalk M w := by
  obtain ⟨faces, B, hB⟩ :=
    exists_boundaryCycle_of_orient hM hne hnodup halpha hchain hcloses horient
  have hcloses' : ∀ v : List M.Dart, v = w → ∀ hv : v ≠ [],
      M.vertexOf (M.alpha (v.getLast hv)) = M.vertexOf (v.head hv) := by
    rintro v rfl hv
    exact hcloses
  have hw := B.isNoncrossingClosedWalk (by rw [hB]; exact hchain)
    (hcloses' B.cycle hB B.cycle_nonempty)
  rw [hB] at hw
  exact hw

end ClosedWalkFaceColouring

namespace PocketWalk

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A pocket walk oriented by every colouring bounds a pocket face set in walk order.**  Let the
pocket walk `s_1 t_1 s_2 t_2` be a closed walk of distinct darts using no edge in both directions.
Let every two-colouring of the faces changing colour exactly across the walk give the faces of all
walk darts one colour, and let a relator cell lie on the side of the walk.  Then the walk is the
boundary cycle of a pocket face set in walk order. -/
theorem exists_pocketFaceSet_closedWalk_of_orient (K : PocketWalk D eps X lo hi)
    (hne : K.walk ≠ []) (hnodup : K.walk.Nodup)
    (halpha : ∀ d ∈ K.walk, X.toCombMap.alpha d ∉ K.walk)
    (hchain : K.walk.IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e)
    (hcloses : X.toCombMap.vertexOf (X.toCombMap.alpha (K.walk.getLast hne)) =
      X.toCombMap.vertexOf (K.walk.head hne))
    (horient : ∀ faces : Finset X.toCombMap.Face,
      (∀ d, ¬ (X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ faces ↔
        X.toCombMap.faceOf d ∈ faces) ↔ walkKeep X.toCombMap K.walk d) →
        ∀ d ∈ K.walk, ∀ e ∈ K.walk,
          (X.toCombMap.faceOf d ∈ faces ↔ X.toCombMap.faceOf e ∈ faces))
    (hkept : ∃ kept : Fin X.rCellCount, (cell X kept).face ∈ sideFaces X.toCombMap K.walk) :
    ∃ P : PocketFaceSet D eps X lo hi, P.boundary.cycle = K.walk ∧ P.ClosedWalk := by
  obtain ⟨kept, hkept⟩ := hkept
  have hw := ClosedWalkFaceColouring.isNoncrossingClosedWalk_of_orient X.planar hne hnodup
    halpha hchain hcloses horient
  exact ⟨K.toPocketFaceSetOfNoncrossing kept hw hkept,
    K.toPocketFaceSetOfNoncrossing_cycle kept hw hkept,
    K.toPocketFaceSetOfNoncrossing_closedWalk kept hw hkept⟩

end PocketWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.ClosedWalkFaceColouring.isNoncrossingClosedWalk_of_orient
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.exists_pocketFaceSet_closedWalk_of_orient
