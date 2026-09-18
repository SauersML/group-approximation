import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07TwoArcLong.FirstTurns
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07TwoArcCopy.SimpleFirstTurns
import GroupApproximation.Meta.AxiomGuard

/-!
# The first-turn cell pocket in a copy: only the pinched walk is left

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), lane `gl-p07-91`.  The target is
`P07TwoArcLong.CellPocketInnerTwoArcFirstTurnsStatement`.

## Proof plan

* **The residual** `TwoArcCopyPinchedStatement`: the target, with one more hypothesis.  The pocket
  walk `K.walk` passes twice through some vertex, `¬ (K.walk.map vertexOf).Nodup`.
* **The reduction** `twoArcCopy_firstTurns_of_pinched`.  Split on whether the walk visits each
  vertex once.
  - If it does, the noncrossing walk is a simple closed walk: the noncrossing fields give every
    other field.  The relator cell `C` on the side of the walk gets an index `k` with
    `cell X k = C`.  The walk pocket `K.toCellPocketFaceSetOfNoncrossing k` of `X` itself is in
    first-turn order (`twoArcCopy_walkPocket_firstTurns`).  The copy is `X`, by
    `OEquivalentDiscDiagram.refl`.
  - Otherwise the residual applies.

## Why the residual is strictly weaker, and how much

It is the target with an added hypothesis, so the target implies it outright.  It drops the case of
a simple pocket walk, which the reduction closes in `X` itself.  The drop is SMALL.  What is left is
the whole of the copy construction: unpinching, by an O-equivalent redraw, a walk that is pinched
at a vertex (a lake touching the rest of the complement at one vertex).  The residual is not a
restatement of `CellPocketInnerTwoArcLongStatement`, of `LakeFillTwoArcExit` or of anything on
the lane's avoid list.  Its conclusion is still first-turn order in a copy.

## Why the residual is true

It is the target restricted to pinched walks, so it is true whenever the target is.  The target's
own module docstring argues that it is true.  Model check: `gl-p07-91/check.py`, part (2), on the
48-dart model of `gl-p07-88`.  All the target's hypotheses hold there, and the walk is noncrossing
with repeated vertices `p₀`, `q₀`.  So the model lies in the residual's domain, and the residual is
not vacuous there.  Its walk pocket is not in first-turn order, and the copy of the target docstring
(`{C}` glued to `Π_i` and `Π_j`) witnesses the conclusion.

Part (1) of the check also shows that "noncrossing and in first-turn order" does NOT force a simple
walk.  So the residual cannot be cut further by asking the walk pocket of `X` to fail first-turn
order, beyond the simple case.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07TwoArcCopy

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **A first-turn cell pocket in a copy, for a pinched inner two-arc walk.**  These are the
hypotheses of `P07TwoArcLong.CellPocketInnerTwoArcFirstTurnsStatement`, and also the pocket walk
visits some vertex twice.  The conclusion is the same: some O-equivalent copy with letter labels
carries a cell pocket face set in first-turn order.
* **Why it is true.**  It is the target restricted to pinched walks.  See the module docstring.
* **Why it is strictly weaker.**  It has one more hypothesis.  The simple case it drops is closed in
  `X` itself by `twoArcCopy_firstTurns_of_pinched`. -/
def TwoArcCopyPinchedStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
    (∃ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
    (∃ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
    ∀ hw : IsNoncrossingClosedWalk X.toCombMap K.walk,
      ¬ (K.walk.map X.toCombMap.vertexOf).Nodup →
      X.outerFace ∉ sideFaces X.toCombMap K.walk →
      (reclosedMap X.toCombMap (sideFaces X.toCombMap K.walk)
          (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      (reclosedMap X.toCombMap (sideOutside X.toCombMap K.walk)
          (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 → C.face ∉ b.1 →
        ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
          (K' : CellPocketFaceSet D eps X' i' j'),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ K'.FirstTurns

/-- **The first-turn cell pocket in a copy, from the pinched case.**  A walk visiting each vertex
once is simple, and its walk pocket in `X` is in first-turn order.  Otherwise the residual
applies. -/
theorem twoArcCopy_firstTurns_of_pinched (h : TwoArcCopyPinchedStatement.{u, w, v}) :
    P07TwoArcLong.CellPocketInnerTwoArcFirstTurnsStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb
  by_cases hnd : (K.walk.map X.toCombMap.vertexOf).Nodup
  · obtain ⟨k, hk⟩ := List.get_of_mem hC
    have hkept : (cell X k).face ∈ sideFaces X.toCombMap K.walk := by
      rw [show cell X k = C from hk]
      exact hCf
    have hs : IsSimpleClosedWalk X.toCombMap K.walk :=
      ⟨hw.ne_nil, hw.chain, hw.closes, hnd, hw.alpha_not_mem⟩
    exact ⟨X, i, j, K.toCellPocketFaceSetOfNoncrossing k hw hoff hkept,
      ⟨OEquivalentDiscDiagram.refl X⟩, hlabel,
      twoArcCopy_walkPocket_firstTurns K k hw hoff hkept hs⟩
  · exact h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hnd hoff hinner
      houter C hC hCf hCa hCb

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07TwoArcCopy

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07TwoArcCopy.TwoArcCopyPinchedStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07TwoArcCopy.twoArcCopy_firstTurns_of_pinched
