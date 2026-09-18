import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.CactusBuildArc
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLakeFill
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, cactus build: the petal walk in pocket order (lane gl-p06-15)

Lane gl-p06-15.  Target: `P06LakeFree.CellPocketLakeFreeCactusOrderStatement`
(`P06LakeFree/OrderCactusStatement.lean`), the residual of lane gl-p06-14.  Osin,
arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## Truth check

The target is TRUE with the cactus witness of `EnclosedOrder.lean` (items 1-5 of its truth
check): `U` the petal of `C` with the petals cut off by loops of `∂Π_i`, `∂Π_j` at its vertices.
The bare edge class and the whole face set are FALSE witnesses (same module).

## Route: merging with the P07 residual does not apply

`P07InnerPocket.PocketLabelNoninterleavingStatement` (`P07InnerPocket/FourPieceOrder.lean`) is
stated for a region candidate `a ≠ b`, a cell pocket walk, Euler equalities and a pocket orbit of
`pocketKeep`, and concludes four `CyclicNoInterleave` facts.  None of these objects exists under
the hypotheses here (no region candidates, no Euler data), and the cactus `U` is no face class of
one dart (petals meeting at a vertex are not joined by `FaceClassStep`), so no pocket orbit gives
`U`.  So this lane takes route 3: one smaller residual.

## What is proved

`cellPocketLakeFreeCactusOrder_of_cactusPetal`: the target follows from
`CellPocketLakeFreeCactusPetalStatement`.  Given the residual walk `L` with a rotation
`L' = L.rotate m <+ ∂K`, convex in both arcs `invDarts A(Π_i)`, `invDarts A(Π_j)`:
1. `X.outerFace ∉ sideFaces L`, since `sideFaces L ⊆ K.faces` and `K.outerFace_not_mem`.
2. Fill the lakes (`P07InnerPocket.exists_lakeFill_of_noncrossing`, with `C.face` on the side): an
   outer walk `W` with `EnclosedFaceSetSucc` and both membership clauses.  This is the witness.
3. The residual clause for `W` gives `n` with `invDarts (W.rotate n) <+ L'`, so
   `invDarts (W.rotate n) <+ ∂K` (`List.Sublist.trans`).
4. Convexity in each arc passes from `L'` to `invDarts (W.rotate n)`
   (`CactusBuild.runConvex_lakeWalk`, `CactusBuildArc.lean`): an arc entry on `L` faces `Π_i`
   (or `Π_j`), which by lake freeness lies in the exterior piece of `K.faces`, hence in that of
   `sideFaces L`, so it survives the filling.

## Why the remaining statement is smaller and true

* *Smaller in proof content.*  The residual asks nothing about lake filling: it never builds the
  successor walk of the filled side, and the four clauses of the target on that walk (its
  existence, membership, sublist of `∂K`, convexity in the arcs) are proved from order facts on
  `L` itself.  Items 1-4 above (exterior face, lake filling, transitivity, arc entries surviving
  the filling via lake freeness) are the content removed.  Its last clause is universal in `W`,
  but `W` is determined up to rotation by its dart set (`OrderCactus.exists_rotate_eq_of_mem_iff`)
  and a sublist of a rotation of `L` is invariant under rotating `W` suitably, so this costs
  nothing.  It is not the target restated: the target makes no claim about the order of `L`.
* *True.*  Take `W₀` the successor walk of the cactus `U` (no lakes by item 3 of the truth check
  of `EnclosedOrder.lean`, so `absorbed U = U` and every face off `U` is exterior) and `L` the
  inverse of `W₀`, so `sideFaces L = U` (item 1), `L` is noncrossing (item 2), and the membership
  clauses of `W₀` hold.  Item 4 gives a rotation of `L` that is a filter of
  `∂K = s₁ t̄₁ s₂ t̄₂`, hence a sublist, and item 5 makes its arc parts infixes, hence convex (no
  repeats in `∂K`).  Every `W` of the last clause has the darts of `W₀`, so `W₀ = W.rotate k`,
  and `invDarts (W.rotate (k + n₀))` is that rotation of `L` for a suitable `n₀`.
* What remains is the planar content only: the cactus walk `L` in the cyclic order of `∂K` with
  contiguous arc parts, and the lake-filled walk read along `L`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121) through Osin's Lemma 9.7(b); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The cactus petal walk in pocket order** (remaining gap of lane gl-p06-15).  Under the
hypotheses of `CellPocketLakeFreeCactusOrderStatement`, there is a noncrossing closed walk `L`
whose side holds `C` and lies in `K.faces`, with a rotation `L'` that is a sublist of `∂K`, convex
in each arc `Ā(Π_i)`, `Ā(Π_j)` of `K`, such that the inverse of every lake-filled successor walk
of its side is, after a rotation, a sublist of `L'`.
* **Why it is true.**  Take `L` the inverse successor walk of the cactus `U` (the petal of `C` with
  the petals cut off by loops of `∂Π_i`, `∂Π_j`); see the module docstring.
* **Why it is smaller.**  Lake filling, the exterior face, transitivity and the survival of arc
  entries are proved in `cellPocketLakeFreeCactusOrder_of_cactusPetal`. -/
def CellPocketLakeFreeCactusPetalStatement : Prop :=
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
          ∃ m : ℕ, (L.rotate m).Sublist K.boundary.cycle ∧
            OrderCactus.RunConvex (L.rotate m) (invDarts X K.firstArc.darts) ∧
            OrderCactus.RunConvex (L.rotate m) (invDarts X K.secondArc.darts) ∧
            ∀ outerWalk : List X.toCombMap.Dart,
              EnclosedFaceSetSucc X
                  (ExteriorComponent.absorbed X.toCombMap (sideFaces X.toCombMap L)
                    X.outerFace)
                  outerWalk →
              (∀ d : X.toCombMap.Dart, d ∈ outerWalk ↔ X.toCombMap.alpha d ∈ L ∧
                X.toCombMap.faceOf d ∈
                  ExteriorComponent.component X.toCombMap (sideFaces X.toCombMap L)
                    X.outerFace) →
              ∃ n : ℕ, (invDarts X (outerWalk.rotate n)).Sublist (L.rotate m)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.CellPocketLakeFreeCactusPetalStatement

/-- **The cactus filter order from the petal walk order.**  Fill the lakes of the side of `L`
(`P07InnerPocket.exists_lakeFill_of_noncrossing`); its inverse outer walk is a sublist of a
rotation of `L`, hence of `∂K`, and keeps the arc entries of `L` (`CactusBuild.runConvex_lakeWalk`).
-/
theorem cellPocketLakeFreeCactusOrder_of_cactusPetal
    (h : CellPocketLakeFreeCactusPetalStatement.{u, w, v}) :
    CellPocketLakeFreeCactusOrderStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j K hij hlabel hW hw hfree C hC hCK
  obtain ⟨L, hL, hCL, hsub, m, hsl, hA, hB, hord⟩ :=
    h D eps X K hij hlabel hW hw hfree C hC hCK
  have hout : X.outerFace ∉ sideFaces X.toCombMap L := fun ho => K.outerFace_not_mem (hsub ho)
  obtain ⟨ow, E, -, hmem⟩ := P07InnerPocket.exists_lakeFill_of_noncrossing X hL hout hCL
  obtain ⟨n, hn⟩ := hord ow E hmem
  exact ⟨L, hL, hCL, hsub, ow, E, hmem, n, hn.trans hsl,
    CactusBuild.runConvex_lakeWalk hfree hsub hmem K.first_not_mem K.firstArc hn hA,
    CactusBuild.runConvex_lakeWalk hfree hsub hmem K.second_not_mem K.secondArc hn hB⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.cellPocketLakeFreeCactusOrder_of_cactusPetal

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree
