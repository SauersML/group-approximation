import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.EnclosedOrder
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.OrderCactusList
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.OrderCactusUnique
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, cactus order: the planar filter statement (lane gl-p06-14)

Lane gl-p06-14.  Target: `P06LakeFree.CellPocketLakeFreeEnclosedOrderStatement`
(`P06LakeFree/EnclosedOrder.lean:106`), the residual of lane gl-p06-08.  Osin,
arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## Truth check

The target is TRUE with the corrected cactus witness of `EnclosedOrder.lean` (items 1-5 of its
truth check): `L` the boundary walk of the petal of `C` together with the petals cut off by loops
of `∂Π_i`, `∂Π_j` at its vertices.  The bare edge class and the whole face set are FALSE witnesses
(same module).  The target is not closed here: items 1, 2, 4 and 5 (the cactus construction and its
planar order) need a Jordan-type argument on the combinatorial map that no corpus lemma provides
(`P07InnerPocket/FourPieceOrder.lean` of lane gl-p07-10 ends in its own residual
`PocketLabelNoninterleavingStatement`, not an order lemma).

## What is proved

`cellPocketLakeFreeEnclosedOrder_of_cactusOrder`: the target follows from
`CellPocketLakeFreeCactusOrderStatement`.  Given a walk `W` of the target and the walk `W₀` of the
residual:
1. `W` and `W₀` have the same darts (both clauses characterise them), so `W₀ = W.rotate k`
   (`OrderCactus.exists_rotate_eq_of_mem_iff`, `OrderCactusUnique.lean`).
2. `invDarts (W₀.rotate n)` is a sublist of `∂K = s₁ ++ t̄₁ ++ s₂ ++ t̄₂` (`K.decomposition`),
   convex in `t̄₁` and in `t̄₂`; `∂K` has no repeats (`K.boundary.cycle_nodup`).  So it reads
   `s₁' ++ q₁ ++ s₂' ++ q₂` with `s_t' <+ s_t` and `q₁`, `q₂` infixes
   (`OrderCactus.exists_four_of_sublist`, `OrderCactusList.lean`).
3. `W₀.rotate n = W.rotate (k + n)` (`List.rotate_rotate`).

## Why the remaining statement is strictly weaker and true

* *Strictly weaker.*  It asks for ONE lake-filled successor walk, not every one (the target's
  universal clause is item 1 above, proved), and it asks for a sublist of `∂K` whose entries on the
  arcs are convex, not for an explicit four-piece decomposition with infix arc parts (item 2,
  proved).  It names no pieces `p_t`, `q_t`, `r_t`, `s_t`.
* *True.*  With the cactus witness `L`, `sideFaces L ⊆ K.faces` and `K.outerFace_not_mem` keep the
  outer face off the side, so `P07InnerPocket.exists_lakeFill_of_noncrossing` gives a walk `W₀`
  with both clauses.  Item 4 of the truth check of `EnclosedOrder.lean` makes `invDarts (W₀.rotate
  n)` the filter `s₁' t₁' s₂' t₂'` of `∂K`, hence a sublist; item 5 makes `t₁'`, `t₂'` infixes of
  `t̄₁`, `t̄₂`.  An infix `q` of a list without repeats is convex, and the entries of the filter on
  `t̄₁` are exactly those of `t₁'` (no repeats in `∂K`), so both convexity clauses hold.
* What remains is only the planar content: the cactus witness, its noncrossing boundary, and the
  cyclic filter order with contiguous arc parts.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121) through Osin's Lemma 9.7(b); certifies no printed sentence
on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The cactus filter order of a lake-free pocket petal** (remaining gap of lane gl-p06-14).
Under the hypotheses of `CellPocketLakeFreeEnclosedOrderStatement`, there is a noncrossing closed
walk `L` whose side holds `C` and lies in `K.faces`, and SOME lake-filled successor walk `W` of its
side, such that a rotation of the inverse of `W` is a sublist of `∂K` whose entries on each arc
`Ā(Π_i)`, `Ā(Π_j)` of `K` are convex.
* **Why it is true.**  Take the cactus witness `L` (the petal of `C` with the petals cut off by
  loops of `∂Π_i`, `∂Π_j` at its vertices) and the walk of
  `P07InnerPocket.exists_lakeFill_of_noncrossing`; see the module docstring.
* **Why it is strictly weaker.**  Uniqueness of successor walks up to rotation and the four-piece
  list decomposition are proved in `cellPocketLakeFreeEnclosedOrder_of_cactusOrder`. -/
def CellPocketLakeFreeCactusOrderStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (K : CellPocketFaceSet D eps X i j),
    i ≠ j →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    IsNoncrossingClosedWalk X.toCombMap K.boundary.cycle →
    CellPocketLakeFree K →
    ∀ C ∈ X.relatorCells, C.face ∈ K.faces →
      ∃ L : List X.toCombMap.Dart,
        IsNoncrossingClosedWalk X.toCombMap L ∧
          C.face ∈ sideFaces X.toCombMap L ∧
          sideFaces X.toCombMap L ⊆ K.faces ∧
          ∃ outerWalk : List X.toCombMap.Dart,
            EnclosedFaceSetSucc X
                (ExteriorComponent.absorbed X.toCombMap (sideFaces X.toCombMap L) X.outerFace)
                outerWalk ∧
              (∀ d : X.toCombMap.Dart, d ∈ outerWalk ↔ X.toCombMap.alpha d ∈ L ∧
                X.toCombMap.faceOf d ∈
                  ExteriorComponent.component X.toCombMap (sideFaces X.toCombMap L)
                    X.outerFace) ∧
              ∃ n : ℕ, (invDarts X (outerWalk.rotate n)).Sublist K.boundary.cycle ∧
                OrderCactus.RunConvex (invDarts X (outerWalk.rotate n))
                  (invDarts X K.firstArc.darts) ∧
                OrderCactus.RunConvex (invDarts X (outerWalk.rotate n))
                  (invDarts X K.secondArc.darts)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.CellPocketLakeFreeCactusOrderStatement

/-- **The planar order from the cactus filter order.**  Every lake-filled successor walk is a
rotation of the one of the residual (`OrderCactus.exists_rotate_eq_of_mem_iff`), and a convex
sublist of `∂K = s₁ t̄₁ s₂ t̄₂` reads four pieces (`OrderCactus.exists_four_of_sublist`). -/
theorem cellPocketLakeFreeEnclosedOrder_of_cactusOrder
    (h : CellPocketLakeFreeCactusOrderStatement.{u, w, v}) :
    CellPocketLakeFreeEnclosedOrderStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j K hij hlabel hW hw hfree C hC hCK
  obtain ⟨L, hL, hCL, hsub, ow₀, E₀, hmem₀, n, hsl, hA, hB⟩ :=
    h D eps X K hij hlabel hW hw hfree C hC hCK
  refine ⟨L, hL, hCL, hsub, fun ow E hmem => ?_⟩
  obtain ⟨k, hk⟩ :=
    OrderCactus.exists_rotate_eq_of_mem_iff E E₀ fun d => (hmem d).trans (hmem₀ d).symm
  have hnd : K.boundary.cycle.Nodup := K.boundary.cycle_nodup
  rw [K.decomposition] at hsl hnd
  obtain ⟨p₁, q₁, r₁, p₂, q₂, r₂, s₁, s₂, h₁, h₂, h₃, h₄, h₅⟩ :=
    OrderCactus.exists_four_of_sublist hnd hsl hA hB
  refine ⟨k + n, p₁, q₁, r₁, p₂, q₂, r₂, s₁, s₂, h₁, h₂, h₃, h₄, ?_⟩
  rw [← List.rotate_rotate, ← hk]
  exact h₅

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.cellPocketLakeFreeEnclosedOrder_of_cactusOrder

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree
