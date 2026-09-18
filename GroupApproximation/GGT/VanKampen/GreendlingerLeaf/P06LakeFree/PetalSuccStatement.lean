import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSuccEnclosed
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.OrderCactusStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.EnclosedOfOrder
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, cactus petal: the petal walk as a turning walk on `∂K` (lane gl-p06-17)

Lane gl-p06-17.  Target: `P06LakeFree.CellPocketLakeFreePetalSuccStatement`
(`P06LakeFree/PetalStatement.lean`), the residual of lane gl-p06-16.  Osin, arXiv:math/0411039v3,
§9, proof of Lemma 9.7(b).

## Truth check

The target is TRUE with the cactus witness `U` of `EnclosedOrder.lean`.  Nothing false was found.
The whole face set `K.faces` with its outer walk is NOT a witness in general: at a pinch vertex of
`∂K` the order of `∂K` (following the inside of `K`) and the successor order of the outside walk
(following the outside) differ, so no rotation of the inverse outside walk is a sublist of `∂K`.
The petal `U` has no pinch vertices on its own boundary, which is why it is used.

## What is proved

`cellPocketLakeFreePetalSucc_of_petalTurn`: the target follows from
`CellPocketLakeFreePetalTurnStatement`, which supplies only a nonempty walk `W₀` turning to its
successors (`PetalSucc.SuccTurn`), `C` on the side of `L = invDarts X W₀`, and a rotation of `L`
that is a sublist of `∂K` and convex in both arcs.  The face set is `F = sideFaces L`, and
`PetalSucc.petalSucc_enclosedFaceSetSucc` (`PetalSuccEnclosed.lean`) proves
`EnclosedFaceSetSucc X F W₀` and `F ⊆ K.faces`: no repeats and no bridges from the sublist of the
duplicate-free `∂K`, noncrossing of `L` from the turning (`PetalSuccInv.lean`), the membership
field from the boundary darts of the side, and the outer face off `F` and `F ⊆ K` by lake freeness
(`PetalSuccReach.lean`).

Chained with the reductions on disk, the same residual gives
`CellPocketLakeFreeCactusPetalStatement`, `CellPocketLakeFreeCactusOrderStatement`,
`CellPocketLakeFreeEnclosedOrderStatement` and `CellPocketFaceSetLakeFreeEnclosedStatement`.

## Why the remaining statement is smaller and true

* *Smaller in proof content.*  Compared with the target it drops the face set and all fields of
  `EnclosedFaceSetSucc` but `ne_nil` and `turn_next` (outer face, no repeats, chain, closing,
  membership, turning), and it drops `sideFaces L ⊆ K.faces`.  All of these are proved here.
* *True.*  `cellPocketLakeFreePetalTurn_of_petalSucc` derives it from the target, true with the
  cactus witness.
* What remains is the planar content only: a walk around the petal of `C` turning to its
  successors, whose inverse is, up to rotation, a filter of `∂K = s₁ t̄₁ s₂ t̄₂` with the arc parts
  infixes.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121) through Osin's Lemma 9.7(b); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The cactus petal as a turning walk on `∂K`** (remaining gap of lane gl-p06-17).  Under the
hypotheses of `CellPocketLakeFreePetalSuccStatement`, there is a nonempty walk `W₀` turning to its
successors such that the side of `L = invDarts X W₀` holds `C`, and a rotation of `L` is a sublist
of `∂K`, convex in both backwards arcs.
* **Why it is true.**  `W₀` the successor walk of the cactus `U` of `EnclosedOrder.lean`
  (`cellPocketLakeFreePetalTurn_of_petalSucc`).
* **Why it is smaller.**  The face set, the enclosing fields and `sideFaces L ⊆ K.faces` are proved
  in `cellPocketLakeFreePetalSucc_of_petalTurn`. -/
def CellPocketLakeFreePetalTurnStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (K : CellPocketFaceSet D eps X i j),
    i ≠ j →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    IsNoncrossingClosedWalk X.toCombMap K.boundary.cycle →
    CellPocketLakeFree K →
    ∀ C ∈ X.relatorCells, C.face ∈ K.faces →
      ∃ W₀ : List X.toCombMap.Dart, W₀ ≠ [] ∧ PetalSucc.SuccTurn X W₀ ∧
        C.face ∈ sideFaces X.toCombMap (invDarts X W₀) ∧
        ∃ m : ℕ, ((invDarts X W₀).rotate m).Sublist K.boundary.cycle ∧
          OrderCactus.RunConvex ((invDarts X W₀).rotate m) (invDarts X K.firstArc.darts) ∧
          OrderCactus.RunConvex ((invDarts X W₀).rotate m) (invDarts X K.secondArc.darts)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.CellPocketLakeFreePetalTurnStatement

/-- **The petal successor walk from a turning walk on `∂K`.** -/
theorem cellPocketLakeFreePetalSucc_of_petalTurn
    (h : CellPocketLakeFreePetalTurnStatement.{u, w, v}) :
    CellPocketLakeFreePetalSuccStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j K hij hlabel hW hw hfree C hC hCK
  obtain ⟨W₀, hne, hT, hCside, m, hsl, hr1, hr2⟩ :=
    h D eps X K hij hlabel hW hw hfree C hC hCK
  obtain ⟨E₀, hsub⟩ := PetalSucc.petalSucc_enclosedFaceSetSucc hfree hne hT hsl
  exact ⟨sideFaces X.toCombMap (invDarts X W₀), W₀, E₀, hCside, hsub, m, hsl, hr1, hr2⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.cellPocketLakeFreePetalSucc_of_petalTurn

/-- **The residual is no stronger than the target**: a successor walk turns to its successors. -/
theorem cellPocketLakeFreePetalTurn_of_petalSucc
    (h : CellPocketLakeFreePetalSuccStatement.{u, w, v}) :
    CellPocketLakeFreePetalTurnStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j K hij hlabel hW hw hfree C hC hCK
  obtain ⟨_, W₀, E₀, hCside, _, m, hsl, hr1, hr2⟩ :=
    h D eps X K hij hlabel hW hw hfree C hC hCK
  exact ⟨W₀, E₀.ne_nil, E₀.turn_next, hCside, m, hsl, hr1, hr2⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.cellPocketLakeFreePetalTurn_of_petalSucc

/-- **The cactus petal walk from a turning walk on `∂K`.** -/
theorem cellPocketLakeFreeCactusPetal_of_petalTurn
    (h : CellPocketLakeFreePetalTurnStatement.{u, w, v}) :
    CellPocketLakeFreeCactusPetalStatement.{u, w, v} :=
  cellPocketLakeFreeCactusPetal_of_petalSucc (cellPocketLakeFreePetalSucc_of_petalTurn h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.cellPocketLakeFreeCactusPetal_of_petalTurn

/-- **The cactus order from a turning walk on `∂K`.** -/
theorem cellPocketLakeFreeCactusOrder_of_petalTurn
    (h : CellPocketLakeFreePetalTurnStatement.{u, w, v}) :
    CellPocketLakeFreeCactusOrderStatement.{u, w, v} :=
  cellPocketLakeFreeCactusOrder_of_cactusPetal (cellPocketLakeFreeCactusPetal_of_petalTurn h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.cellPocketLakeFreeCactusOrder_of_petalTurn

/-- **The enclosed order from a turning walk on `∂K`.** -/
theorem cellPocketLakeFreeEnclosedOrder_of_petalTurn
    (h : CellPocketLakeFreePetalTurnStatement.{u, w, v}) :
    CellPocketLakeFreeEnclosedOrderStatement.{u, w, v} :=
  cellPocketLakeFreeEnclosedOrder_of_cactusOrder (cellPocketLakeFreeCactusOrder_of_petalTurn h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.cellPocketLakeFreeEnclosedOrder_of_petalTurn

/-- **The lake-free enclosed face set from a turning walk on `∂K`.** -/
theorem cellPocketFaceSetLakeFreeEnclosed_of_petalTurn
    (h : CellPocketLakeFreePetalTurnStatement.{u, w, v}) :
    CellPocketFaceSetLakeFreeEnclosedStatement.{u, w, v} :=
  cellPocketFaceSetLakeFreeEnclosed_of_order (cellPocketLakeFreeEnclosedOrder_of_petalTurn h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.cellPocketFaceSetLakeFreeEnclosed_of_petalTurn

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree
