import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.InnerTwoArcLongUnpinch
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.InnerTwoArc
import GroupApproximation.Meta.AxiomGuard

/-!
# The inner two-arc pocket for long relator words, reduced to the enclosed inner pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), lane `P07InnerTwoArcLong`.  The target is
`CellPocketInnerTwoArcLongStatement` (`InnerTwoArc.lean`).  The previous lane named two missing
ingredients:
(i) the boundary walk of the inner pocket, as an `EnclosedFaceSetSucc`;
(ii) a two-arc doubling and unpinching.

## Ingredient (ii) is closed

* `InnerTwoArcLongDoubling.lean` doubles the bridges and keeps two sides and two arcs.
* `InnerTwoArcLongUnpinch.lean` does the rest (`lakeFillTwoArcExit_of_enclosed`).  It turns the
  bridge-free walk into a cell pocket on its boundary cycle, in first-turn order.
  `copyRegion_of_firstTurns` unpinches that pocket.  A walk whose first arc is empty goes through
  the closed one-arc pieces.

So a separate two-arc unpinch statement is not needed.  What remains is (i), which is purely
combinatorial and involves no O-equivalent copy.  It is `InnerPocketEnclosedTwoArcStatement`.

## Proof route

`innerTwoArcLong_of_innerPocketEnclosed`: introduce the hypotheses, take the enclosed face set from
the residual, and apply `lakeFillTwoArcExit_of_enclosed` with the length hypothesis.
`proof_of_innerPocketEnclosed` composes this with `proof_of_innerTwoArcLong`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The enclosed inner pocket of a cell pocket walk.**  It has the hypotheses of
`CellPocketInnerTwoArcLongStatement`.  The conclusion is an enclosed face set of `X` itself,
turning to its successors and holding a relator cell.  Its inverse outside walk reads
`s_1 Ā_1 s_2 Ā_2`, with arcs `A_1`, `A_2` of cells outside, `|s_1|, |s_2| ≤ ε`, and `A_1` empty or
`A_2` nonempty.
* **Why it is true.**  Take the inner pocket `sideFaces K \ (a ∪ b)` and fill its lakes.
  * The pocket meets the walk only along the gaps `G_1`, `G_2`, and it meets `a`, `b` only across
    their far sides.  So its outside walk, which turns to its successors, reads the far side of `b`,
    then `Ḡ_1`, then the far side of `a`, then `Ḡ_2`.
  * Each far side is a side of a region candidate, so its length is `≤ ε`.  `Π_i` and `Π_j` lie in
    `sideOutside K`, so they are outside, and the kept cell `C` is inside.
  * If `G_2` is empty but `G_1` is not, rotate the walk to `s_2 ∅ s_1 Ḡ_1`, with `∅` an empty arc
    of `Π_j`.  This gives the last disjunct.
* **Why it is strictly weaker.**  It implies the target (`innerTwoArcLong_of_innerPocketEnclosed`).
  It asks only for a face set and a walk in the given diagram `X`: no O-equivalent copy, no
  unpinched region, no `FollowsBoundary`, and no bound on word norms.  Its walk may pinch and may
  have bridges.  All of that surgery is proved in `InnerTwoArcLongUnpinch.lean`. -/
def InnerPocketEnclosedTwoArcStatement : Prop :=
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
      X.outerFace ∉ sideFaces X.toCombMap K.walk →
      (reclosedMap X.toCombMap (sideFaces X.toCombMap K.walk)
          (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      (reclosedMap X.toCombMap (sideOutside X.toCombMap K.walk)
          (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 → C.face ∉ b.1 →
        ∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart)
          (k₁ k₂ : Fin X.rCellCount) (A₁ : CyclicArc (cellDarts X k₁))
          (A₂ : CyclicArc (cellDarts X k₂)) (s₁ s₂ : List X.toCombMap.Dart),
          EnclosedFaceSetSucc X faces outerWalk ∧
            (∃ C' ∈ X.relatorCells, C'.face ∈ faces) ∧
            (cell X k₁).face ∉ faces ∧ (cell X k₂).face ∉ faces ∧
            invDarts X outerWalk = s₁ ++ invDarts X A₁.darts ++ s₂ ++ invDarts X A₂.darts ∧
            s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ (A₁.length = 0 ∨ 0 < A₂.length)

/-- **The long-word inner two-arc pocket from the enclosed inner pocket**, by
`lakeFillTwoArcExit_of_enclosed`. -/
theorem innerTwoArcLong_of_innerPocketEnclosed
    (h : InnerPocketEnclosedTwoArcStatement.{u, w, v}) :
    CellPocketInnerTwoArcLongStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb
  obtain ⟨faces, outerWalk, k₁, k₂, A₁, A₂, s₁, s₂, E, ⟨C', hC', hCf'⟩, hk₁, hk₂, hdec, hs₁, hs₂,
      hpos⟩ :=
    h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff hinner houter C hC hCf
      hCa hCb
  exact lakeFillTwoArcExit_of_enclosed hW hlabel E hC' hCf' hk₁ hk₂ A₁ A₂ hdec hs₁ hs₂ hpos

/-- **The lake exclusion from the enclosed inner pocket.** -/
theorem proof_of_innerPocketEnclosed (h : InnerPocketEnclosedTwoArcStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} :=
  proof_of_innerTwoArcLong (innerTwoArcLong_of_innerPocketEnclosed h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.InnerPocketEnclosedTwoArcStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.innerTwoArcLong_of_innerPocketEnclosed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.proof_of_innerPocketEnclosed
