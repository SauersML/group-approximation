import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.CactusBuildStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.OrderCactusUnique
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.DefComponent
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalInvWalk
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.EnclosedRotate
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, cactus petal: the petal as a successor walk (lane gl-p06-16)

Lane gl-p06-16.  Target: `P06LakeFree.CellPocketLakeFreeCactusPetalStatement`
(`P06LakeFree/CactusBuildStatement.lean`), the residual of lane gl-p06-15.  Osin,
arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## Truth check

The target is TRUE with the cactus witness `U` of `EnclosedOrder.lean` (items 1-5 of its truth
check): `U` the petal of `C` with the petals cut off by loops of `∂Π_i`, `∂Π_j` at its vertices,
`W₀` the successor walk around `U` (`EnclosedFaceSetSucc X U W₀`), `L = invDarts X W₀`.

## What is proved

`cellPocketLakeFreeCactusPetal_of_petalSucc`: the target follows from
`CellPocketLakeFreePetalSuccStatement`, which supplies `F`, `W₀` with `EnclosedFaceSetSucc X F W₀`,
`C` on the side of `L = invDarts X W₀`, that side inside `K.faces`, and a rotation `L.rotate m`
that is a sublist of `∂K` and convex in both arcs.  The proof, with `L` as the witness:

1. *No bridges.*  Every dart `e ∈ L` is a dart of `∂K`, so `faceOf e ∈ K` and
   `faceOf (α e) ∉ K`.  If `d, α d ∈ W₀` then `α d, d ∈ L`, so `faceOf d ∈ K` and `faceOf d ∉ K`.
2. *Noncrossing.*  `Petal.isNoncrossingClosedWalk_invDarts` (`PetalInvWalk.lean`): the inverse of
   a successor walk without bridges is noncrossing (first returns are injective).
3. *The universal clause.*  Let `W` be an outer walk with `EnclosedFaceSetSucc` over the absorbed
   side and `d ∈ W ↔ α d ∈ L ∧ faceOf d ∈ component (sideFaces L)`.  Then `d ∈ W ↔ d ∈ W₀`:
   `α d ∈ L ↔ d ∈ W₀`, and for `d ∈ W₀` the dart `α d ∈ L ⊆ ∂K` gives `faceOf d ∉ K`, so `faceOf d`
   is in the exterior piece of `K` (lake freeness), which lies in the exterior piece of
   `sideFaces L ⊆ K` (`component_subset_of_subset`).  By `OrderCactus.exists_rotate_eq_of_mem_iff`,
   `W₀ = W.rotate k`.  With `t = |L| - m % |L|`,
   `invDarts (L.rotate m) = (invDarts L).rotate t = W₀.rotate t = W.rotate (k + t)`
   (`P07InnerPocket.invDarts_rotate`, `invDarts ∘ invDarts = id`, `List.rotate_rotate`), so
   `invDarts (W.rotate (k + t)) = L.rotate m`, a sublist of itself.

## Why the remaining statement is smaller and true

* *Smaller in proof content.*  Compared with the target, the residual drops two clauses, both
  proved here: that `L` is noncrossing (the turning argument of `PetalInvWalk.lean`) and the
  universal clause over lake-filled outer walks (the uniqueness of successor walks and the lake
  freeness argument of item 3).  In exchange it asks for the walk around the side in successor
  form, which is how the cactus is naturally produced.  It is not the target restated: it says
  nothing about noncrossing walks or lake filling.
* *True.*  Take `F = U`, `W₀` the successor walk of `U`.  `U` has no bridges and no lakes (item 3
  of `EnclosedOrder.lean`), so `W₀` goes once around `U` and `EnclosedFaceSetSucc X U W₀` holds.
  `sideFaces (invDarts W₀) = U` (item 1), and items 4 and 5 give the rotation: a filter of
  `∂K = s₁ t̄₁ s₂ t̄₂`, hence a sublist, with arc parts infixes, hence convex.
* What remains is the planar content only: build the cactus `U`, its successor walk, and its
  cyclic order along `∂K`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121) through Osin's Lemma 9.7(b); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The cactus petal as a successor walk** (remaining gap of lane gl-p06-16).  Under the
hypotheses of `CellPocketLakeFreeCactusPetalStatement`, there are a face set `F` and a successor
walk `W₀` around it such that the side of `L = invDarts X W₀` holds `C` and lies in `K.faces`, and
a rotation of `L` is a sublist of `∂K`, convex in both backwards arcs.
* **Why it is true.**  `F` the cactus `U` of `EnclosedOrder.lean`, `W₀` its successor walk.
* **Why it is smaller.**  Noncrossing of `L` and the universal clause over lake-filled outer walks
  are proved in `cellPocketLakeFreeCactusPetal_of_petalSucc`. -/
def CellPocketLakeFreePetalSuccStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (K : CellPocketFaceSet D eps X i j),
    i ≠ j →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    IsNoncrossingClosedWalk X.toCombMap K.boundary.cycle →
    CellPocketLakeFree K →
    ∀ C ∈ X.relatorCells, C.face ∈ K.faces →
      ∃ (F : Finset X.toCombMap.Face) (W₀ : List X.toCombMap.Dart),
        EnclosedFaceSetSucc X F W₀ ∧
          C.face ∈ sideFaces X.toCombMap (invDarts X W₀) ∧
          sideFaces X.toCombMap (invDarts X W₀) ⊆ K.faces ∧
          ∃ m : ℕ, ((invDarts X W₀).rotate m).Sublist K.boundary.cycle ∧
            OrderCactus.RunConvex ((invDarts X W₀).rotate m) (invDarts X K.firstArc.darts) ∧
            OrderCactus.RunConvex ((invDarts X W₀).rotate m) (invDarts X K.secondArc.darts)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.CellPocketLakeFreePetalSuccStatement

/-- **The cactus petal walk from the successor walk around the petal.** -/
theorem cellPocketLakeFreeCactusPetal_of_petalSucc
    (h : CellPocketLakeFreePetalSuccStatement.{u, w, v}) :
    CellPocketLakeFreeCactusPetalStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j K hij hlabel hW hw hfree C hC hCK
  obtain ⟨F, W₀, E₀, hCside, hsub, m, hsl, hr1, hr2⟩ :=
    h D eps X K hij hlabel hW hw hfree C hC hCK
  have hbd : ∀ d ∈ invDarts X W₀, X.toCombMap.faceOf d ∈ K.faces ∧
      X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ K.faces := fun d hd =>
    (K.boundary.cycle_mem_iff d).mp (hsl.subset (List.mem_rotate.mpr hd))
  have hα : ∀ d ∈ W₀, X.toCombMap.alpha d ∉ W₀ := by
    intro d hd had
    have h1 : d ∈ invDarts X W₀ := (Petal.petal_mem_invDarts_iff X).mpr had
    have h2 : X.toCombMap.alpha d ∈ invDarts X W₀ := by
      rw [Petal.petal_mem_invDarts_iff X, X.toCombMap.alpha_involutive d]
      exact hd
    exact (hbd d h1).2 (hbd _ h2).1
  refine ⟨invDarts X W₀, Petal.isNoncrossingClosedWalk_invDarts E₀ hα, hCside, hsub, m, hsl,
    hr1, hr2, ?_⟩
  intro ow E hmem
  have hmem' : ∀ d, d ∈ ow ↔ d ∈ W₀ := by
    intro d
    rw [hmem d, Petal.petal_mem_invDarts_iff X, X.toCombMap.alpha_involutive d]
    constructor
    · exact fun hd => hd.1
    · intro hd
      refine ⟨hd, ?_⟩
      have hαd : X.toCombMap.alpha d ∈ invDarts X W₀ := by
        rw [Petal.petal_mem_invDarts_iff X, X.toCombMap.alpha_involutive d]
        exact hd
      have hout : X.toCombMap.faceOf d ∉ K.faces := by
        have hb := (hbd _ hαd).2
        rwa [X.toCombMap.alpha_involutive d] at hb
      exact component_subset_of_subset hsub K.outerFace_not_mem (hfree _ hout)
  obtain ⟨k, hk⟩ := OrderCactus.exists_rotate_eq_of_mem_iff E E₀ hmem'
  have hV : invDarts X ((invDarts X W₀).rotate m) =
      ow.rotate (k + ((invDarts X W₀).length - m % (invDarts X W₀).length)) := by
    rw [P07InnerPocket.invDarts_rotate, Petal.petal_invDarts_invDarts, hk, List.rotate_rotate]
  have hinv : invDarts X (ow.rotate (k + ((invDarts X W₀).length -
      m % (invDarts X W₀).length))) = (invDarts X W₀).rotate m := by
    rw [← hV, Petal.petal_invDarts_invDarts]
  refine ⟨k + ((invDarts X W₀).length - m % (invDarts X W₀).length), ?_⟩
  simp only [hinv, List.Sublist.refl]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.cellPocketLakeFreeCactusPetal_of_petalSucc

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree
