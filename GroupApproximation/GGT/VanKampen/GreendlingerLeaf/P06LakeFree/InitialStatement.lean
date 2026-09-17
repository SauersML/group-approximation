import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Def
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, lane gl-p06-06: the lane's reach statement is FALSE

Lane gl-p06-06 of `carto-gl-p06`, "LakeFree from a noncrossing walk with the outer Euler
equality".  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` "contains all `Γ_{i,1}`'s".

## Truth check: `SideOutsideReachStatement` is FALSE

The lane asks: for a noncrossing closed walk `w` in a disc diagram, with the exterior face off
`sideFaces M w` and the outer Euler equality
`χ (reclosedMap M (sideOutside M w) (outerCycle)) = χ M`, every face of `sideOutside M w` lies in
the exterior piece `ExteriorComponent.component M (sideFaces M w) outerFace`.

**Counterexample (pinched annulus).**  Four edges `1, 2, 3, 4`, darts `k±` with `α (k±) = k∓`, and
`σ = (1+ 3+ 4- 2-)(1- 2+)(3- 4+)`.  Three vertices, four edges and three faces
`E = (1+ 2+)`, `R = (1- 3+ 4+ 2-)`, `L = (3- 4-)`, so `χ = 2`: a planar map (checked by script).
Geometrically: an outer circle `1 2` and an inner circle `3 4` touching at the vertex `v` of
`(1+ 3+ 4- 2-)`; `R` is the annulus, `E` the exterior and `L` the hole.  The walk
`w = [1-, 3+, 4+, 2-]` (the boundary of `R`, passing twice through `v`) is a noncrossing closed walk,
`sideFaces M w = {R}`, `sideOutside M w = {E, L}`, and `w.reverse.map α` is a valid boundary cycle
of `{E, L}`.  Reclosing `{E, L}` along it keeps all edges and splits `v` into two vertices with one
new face in place of `E` and `L`: `V - E + F = 4 - 4 + 2 = 2 = χ M`, so the outer Euler equality
holds (so does the inner one).  With `outerFace = E ∉ {R}`, the face `L ∈ sideOutside M w` is not
in the exterior piece: `E` and `L` share no edge, and every edge out of `E` or `L` is a walk edge.

The same shape arises for a cell pocket walk `s₁ t̄₁ s₂ t̄₂` whose two sides meet at a vertex,
with `Π_j` in the hole, so `lakeFree_toCellPocketFaceSetOfNoncrossing` below is only a formal
reduction from a false hypothesis.  No lemma "Euler equality ⇒ edge-connected outside" exists in
the corpus (the `KeepUnion` files of gl-p07-01 give only connectivity of walk unions), and none can.

## Correction

`InitialReach.lean` proves the corrected statement `SideOutsideReachFollowsStatement`, with
`FollowsBoundary` of the outer cycle in place of the Euler equality, and the endpoint
`lakeFree_toCellPocketFaceSetOfNoncrossing_of_followsBoundary`.  In the pinched annulus the outer
cycle `[2+, 4-, 3-, 1+]` does not follow the boundary: from `2+`, the face rotation gives `1+`, a
dart on `E` that is not internal, while the cycle successor of `2+` is `4-`, on `L`.

## Manuscript status

Infrastructure for `thm:hull` (through Osin's Lemma 9.7(b)); certifies no printed sentence.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Initial

universe u w v

open Embedded HullSC WordMetric Surgery.MapCollapse SimpleClosedWalkSides

/-- **The lane's reach statement: FALSE** (pinched-annulus counterexample in the module
docstring).  For a noncrossing closed walk with the exterior face off its side and the outer
Euler equality, every face of the walk's outside lies in the exterior piece.  Stated as the lane
asks, for the formal reduction `lakeFree_toCellPocketFaceSetOfNoncrossing`; the true replacement is
`SideOutsideReachFollowsStatement` (`InitialReach.lean`). -/
def SideOutsideReachStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (X : DiscDiagram.{u, w, v} W) (walk : List X.toCombMap.Dart)
    (hw : IsNoncrossingClosedWalk X.toCombMap walk),
    X.outerFace ∉ sideFaces X.toCombMap walk →
    (reclosedMap X.toCombMap (sideOutside X.toCombMap walk)
        (hw.outerCycle X.planar)).eulerCharacteristic =
      X.toCombMap.eulerCharacteristic →
    ∀ f ∈ sideOutside X.toCombMap walk,
      f ∈ ExteriorComponent.component X.toCombMap (sideFaces X.toCombMap walk) X.outerFace

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The lane's reduction**: from `SideOutsideReachStatement` (false), the cell pocket face set
of a noncrossing walk with the outer Euler equality is lake free. -/
theorem lakeFree_toCellPocketFaceSetOfNoncrossing (h : SideOutsideReachStatement.{u, w, v})
    (K : CellPocketWalk D eps X i j) (kept : Fin X.rCellCount)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hoff : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hkept : (cell X kept).face ∈ sideFaces X.toCombMap K.walk)
    (heuler : (reclosedMap X.toCombMap (sideOutside X.toCombMap K.walk)
        (hw.outerCycle X.planar)).eulerCharacteristic =
      X.toCombMap.eulerCharacteristic) :
    CellPocketLakeFree (K.toCellPocketFaceSetOfNoncrossing kept hw hoff hkept) := by
  intro f hf
  exact h X K.walk hw hoff heuler f ((mem_sideOutside_iff X.toCombMap K.walk f).mpr hf)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Initial

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Initial.SideOutsideReachStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Initial.lakeFree_toCellPocketFaceSetOfNoncrossing
