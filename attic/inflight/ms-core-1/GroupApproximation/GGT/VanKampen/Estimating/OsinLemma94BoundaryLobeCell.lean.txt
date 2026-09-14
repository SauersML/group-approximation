import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFirstTurnWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMergeRegion
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: a boundary lobe that does not read `1` encloses a relator cell

Osin (math/0411039v3, §9), proof of Lemma 9.4.  A value failure at a boundary junction is a lobe of `∂Δ` at a
pinch vertex whose word does not have value one (`OsinLemma94RealizedPolygons.valueFailureJunctions`,
`Estimating/OsinLemma94BoundaryJunctionBudget`).  Counting value failures charges each one to a relator cell inside
its lobe.  This module proves the charging step for every closed walk presented through first turns.

Let `c` be a list of distinct darts, no dart together with its reverse, each dart reaching the next and the last
reaching the first by a first turn along `c` (`FirstTurn`), with the exterior face on the side of `c`.  Then
`PocketRegion.ofFirstTurnWalk` is a pocket region whose inner cycle is the reversed walk `c.reverse.map alpha`.  A
pocket region with no relator cell reads the identity along its inner cycle (`PocketRegion.listVal_inner_eq_one`, by
the pocket as a van Kampen diagram, with no shelling and no face assembly).  So if the reversed walk reads an element
other than `1`, a relator cell lies on its side.

* `exists_relatorCell_of_firstTurnWalk_listVal_ne_one`.

For a lobe of `∂Δ` the complement spelling `c` is the stretch of exterior face darts behind the gap: consecutive darts
follow the face permutation (`FirstTurn.of_facePerm`), and the closing turn at the pinch vertex passes the reversal
of the last polygon dart and the first dart of the next side.  That instance, and the no-hair clause, are the next
steps.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4 inside the proof of
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open SimpleClosedWalkSides

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-- **A first-turn walk that does not read `1` encloses a relator cell.**  With the exterior face on the side of `c`,
if the reversed walk `c.reverse.map alpha` reads an element other than `1`, some relator cell lies on its side. -/
theorem exists_relatorCell_of_firstTurnWalk_listVal_ne_one {c : List Delta.toCombMap.Dart}
    (hne : c ≠ []) (hnodup : c.Nodup) (halpha : ∀ x ∈ c, Delta.toCombMap.alpha x ∉ c)
    (hchain : c.IsChain (FirstTurn Delta.toCombMap c))
    (hclose : FirstTurn Delta.toCombMap c (c.getLast hne) (c.head hne))
    (hout : Delta.outerFace ∈ sideFaces Delta.toCombMap c)
    (hval : RelLetter.listVal (dartWord Delta (c.reverse.map Delta.toCombMap.alpha)) ≠ 1) :
    ∃ C ∈ Delta.relatorCells,
      C.face ∈ sideFaces Delta.toCombMap (c.reverse.map Delta.toCombMap.alpha) := by
  by_contra hno
  refine hval ?_
  have h := (PocketRegion.ofFirstTurnWalk hne hnodup halpha hchain hclose hout).listVal_inner_eq_one
    fun C hC hmem => hno ⟨C, hC, by rwa [PocketRegion.ofFirstTurnWalk_faces] at hmem⟩
  rwa [PocketRegion.ofFirstTurnWalk_inner_cycle] at h

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.exists_relatorCell_of_firstTurnWalk_listVal_ne_one
