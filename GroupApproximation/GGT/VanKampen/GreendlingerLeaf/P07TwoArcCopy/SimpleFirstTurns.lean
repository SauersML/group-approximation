import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFirstTurnsOfOuterFollows
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellFaceSet
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# A simple cell pocket is in first-turn order

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), lane `gl-p07-91`.  This is the first step
of the plan for `P07TwoArcLong.CellPocketInnerTwoArcFirstTurnsStatement`.

## Proof plan

* `twoArcCopy_firstTurns_of_simple`.  A simple closed walk is noncrossing
  (`IsSimpleClosedWalk.isNoncrossingClosedWalk`), and its outer cycle follows its boundary
  (`IsSimpleClosedWalk.outerCycle_follows`).  The outer cycles of the simple and of the noncrossing
  walk carry the same cycle `w.reverse.map alpha` on the same face set `sideOutside`, so they agree
  up to proof fields, and `CellPocketFaceSet.firstTurns_of_outerFollows` gives first-turn order.
* `twoArcCopy_walkPocket_firstTurns`.  The walk-order cell pocket of a noncrossing pocket walk
  (`CellPocketWalk.toCellPocketFaceSetOfNoncrossing`) has the walk as its boundary cycle (by `rfl`).
  When that walk is simple, the pocket is in first-turn order.

Why it is true, on paper: at each vertex `v` of a simple closed walk the darts kept by the walk are
the one walk dart `e` leaving `v` and the reversal `alpha d` of the one walk dart `d` arriving at
`v`.  These two darts are distinct, since `alpha d ∉ w`.  So rotating from `e` meets `alpha d`
before any other kept dart.  Model check: `gl-p07-91/check.py`, part (1), finds no counterexample
on 32847 sampled simple walks in random maps.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07TwoArcCopy

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **A simple cell pocket is in first-turn order.**  Its boundary cycle is a simple closed walk, so
it is noncrossing and its outer cycle follows its boundary. -/
theorem twoArcCopy_firstTurns_of_simple {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ}
    {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}
    (K : CellPocketFaceSet D eps X i j) (hK : K.Simple) : K.FirstTurns := by
  have hs : IsSimpleClosedWalk X.toCombMap K.boundary.cycle := hK
  have hfol : (hs.isNoncrossingClosedWalk.outerCycle X.planar).FollowsBoundary :=
    hs.outerCycle_follows X.planar
  exact K.firstTurns_of_outerFollows hs.isNoncrossingClosedWalk hfol

/-- **The walk pocket of a simple pocket walk is in first-turn order.**  Its boundary cycle is the
walk itself. -/
theorem twoArcCopy_walkPocket_firstTurns {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ}
    {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}
    (K : CellPocketWalk D eps X i j) (kept : Fin X.rCellCount)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hkept : (cell X kept).face ∈ sideFaces X.toCombMap K.walk)
    (hs : IsSimpleClosedWalk X.toCombMap K.walk) :
    (K.toCellPocketFaceSetOfNoncrossing kept hw hout hkept).FirstTurns := by
  apply twoArcCopy_firstTurns_of_simple
  show IsSimpleClosedWalk X.toCombMap
    (K.toCellPocketFaceSetOfNoncrossing kept hw hout hkept).boundary.cycle
  rw [CellPocketWalk.toCellPocketFaceSetOfNoncrossing_cycle]
  exact hs

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07TwoArcCopy

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07TwoArcCopy.twoArcCopy_firstTurns_of_simple
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07TwoArcCopy.twoArcCopy_walkPocket_firstTurns
