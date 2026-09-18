import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessRead
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-44: clause 4 for the witness under block-local conditions

## LOUD: `PocketFourPieceWitnessArcsStatement` (`FourPieceWitnessRead.lean`) is FALSE

This lane rechecked the refutation, on paper.  It is model M2 of lane gl-p07-21c, as recorded in
`FourPieceWitnessArcsStatement.lean`.
* The outside walk of `F = {C}` is the inner loop `λ = λ₁ ⋯ λ_k` of `Π_i`, in `facePerm` order.
  Here `x = λ_k` is the only pinched dart, and `facePerm x = μ₁ ≠ λ₁`.
* The whole walk lies on `G₁`.  The rotation-prefix `U = [α λ₁, α x]` of `invDarts outerWalk`
  crosses the seam `x → λ₁`.
* `U = invDarts [x, λ₁]`.  That is a cell arc only if `facePerm x = λ₁`.  So clause 4 fails.

The corrected `FourPieceWitness.ArcsAuditStatement` is also FALSE on paper (model M11, lane
gl-p07-29).  Its pinch-bounded form `FourPieceWitness.ArcsAuditPinchStatement` is PROVED
(`FourPieceWitness.arcsAuditPinch`).  So no open residual of clause 4 at the witness level remains
unproved.  This lane proves the sharpest local form that the corpus step lemmas (lane gl-p07-26)
support.

## The statement (`WitnessArcsBlocksStatement`)

It keeps the premise block and the walk hypotheses of the target.  Write `M = X.toCombMap`, and
say that a walk dart `x` is **good** if `walkKeep M outerWalk (facePerm x)` or
`PocketRun.PinchFreeAt M x` holds.
* **4a (local).**  Take a rotation-prefix block `U ⊆ invDarts G₁` of `invDarts outerWalk`.  Suppose
  every entry of `(invDarts U).dropLast` is good.  These are the walk-order entries of the block
  except the last one.  Then `U = invDarts A.darts` for a cell arc `A` of `Π_i`.
* **4b (local).**  Suppose the whole walk lies on `G₁` and at most one walk dart is not good.  Then
  some rotation of the walk is one cell arc of `Π_i`.
* The same two clauses hold for `G₂` and `Π_j`.

## Strength

* **Weaker than the target.**  Each clause only gains a hypothesis
  (`witnessArcsBlocks_of_arcs`).  The target is false and this statement is proved, so it is
  strictly weaker.
* **Not equivalent to the target.**  In M2, the block `[α λ₁, α x]` has `(invDarts U).dropLast =
  [x]`, and `x` is not good.  So the local hypothesis is exactly what excludes the counterexample.
* **Stronger than the proved `ArcsAuditPinchStatement`.**  That statement is recovered from this
  one (`witnessArcsBlocks_arcsAuditPinch`, `WitnessArcsBlocksProof.lean`).
  - Its 4a needs every dart of `G₁` pinch-free, together with an off-`G₁` complement entry.  Here
    only the block's non-final darts must be good, and there is no complement condition.
  - Its 4b bounds the pinched darts of all of `G₁`.  Here only walk darts count, and a kept
    `facePerm` also counts as good.
* **Sharp in M2.**  The good blocks of M2 are exactly the blocks that end at `x` in walk order,
  and they are genuine sub-arcs of `λ`.

## Proof

The proof is in `WitnessArcsBlocksLocal.lean` and `WitnessArcsBlocksProof.lean`.  It follows
`ArcClose.arc_of_block` with the hypothesis made block-local.
* The block, read in walk order, is a rotation prefix of `outerWalk`.
* At each non-final block position, the good dart steps by `facePerm`
  (`ArcClose.exists_cellArc_of_rotate`).
* 4b is `ArcClose.arc_of_all`.  Two bad positions carry equal darts, and `E.nodup` makes the
  positions equal.

**Remaining gap.**  None for this statement.  The corpus gap is that consumers must discharge the
goodness hypothesis.  It fails exactly at pinch vertices whose `facePerm` successor is cut, as in
M2 and M11.  `SoundRoute.PinchCaseStatement` already case-splits on that.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Clause 4 for the cut-down witness, under block-local goodness.**  See the module
docstring. -/
def WitnessArcsBlocksStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
    ∀ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i →
    ∀ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j →
    ∀ hw : IsNoncrossingClosedWalk X.toCombMap K.walk,
      X.outerFace ∉ sideFaces X.toCombMap K.walk →
      (reclosedMap X.toCombMap (sideFaces X.toCombMap K.walk)
          (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      (reclosedMap X.toCombMap (sideOutside X.toCombMap K.walk)
          (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 → C.face ∉ b.1 →
      ∀ outerWalk : List X.toCombMap.Dart,
        EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K C.face) outerWalk →
        (∀ d ∈ outerWalk,
          X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ FourPieceWitness.witnessFaces a b K C.face) →
        (∀ (m : ℕ) (U V : List X.toCombMap.Dart),
          (invDarts X outerWalk).rotate m = U ++ V →
          (∀ e ∈ U, e ∈ invDarts X G₁.darts) →
          (∀ x ∈ (invDarts X U).dropLast,
            walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm x) ∨
              PocketRun.PinchFreeAt X.toCombMap x) →
          ∃ A : CyclicArc (cellDarts X i), U = invDarts X A.darts) ∧
        ((∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₁.darts) →
          (∀ x ∈ outerWalk, ∀ y ∈ outerWalk,
            ¬ (walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm x) ∨
              PocketRun.PinchFreeAt X.toCombMap x) →
            ¬ (walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm y) ∨
              PocketRun.PinchFreeAt X.toCombMap y) → x = y) →
          ∃ (n : ℕ) (A : CyclicArc (cellDarts X i)),
            invDarts X (outerWalk.rotate n) = invDarts X A.darts) ∧
        (∀ (m : ℕ) (U V : List X.toCombMap.Dart),
          (invDarts X outerWalk).rotate m = U ++ V →
          (∀ e ∈ U, e ∈ invDarts X G₂.darts) →
          (∀ x ∈ (invDarts X U).dropLast,
            walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm x) ∨
              PocketRun.PinchFreeAt X.toCombMap x) →
          ∃ A : CyclicArc (cellDarts X j), U = invDarts X A.darts) ∧
        ((∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₂.darts) →
          (∀ x ∈ outerWalk, ∀ y ∈ outerWalk,
            ¬ (walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm x) ∨
              PocketRun.PinchFreeAt X.toCombMap x) →
            ¬ (walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm y) ∨
              PocketRun.PinchFreeAt X.toCombMap y) → x = y) →
          ∃ (n : ℕ) (A : CyclicArc (cellDarts X j)),
            invDarts X (outerWalk.rotate n) = invDarts X A.darts)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessArcsBlocksStatement

/-- **The block-local statement follows from the (false) target.**  Every clause only gains a
hypothesis.  4b is the target's clause for the whole list, as the prefix of rotation `0`. -/
theorem witnessArcsBlocks_of_arcs (h : PocketFourPieceWitnessArcsStatement.{u, w, v}) :
    WitnessArcsBlocksStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw
    hout hinner houter C hC hCf hCa hCb outerWalk E hnb
  obtain ⟨harc₁, harc₂⟩ := h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
  refine ⟨fun m U V hm hU _ => harc₁ m U V hm hU, fun hall _ => ?_,
    fun m U V hm hU _ => harc₂ m U V hm hU, fun hall _ => ?_⟩
  · obtain ⟨A, hA⟩ := harc₁ 0 (invDarts X outerWalk) []
      (by rw [List.rotate_zero, List.append_nil]) hall
    exact ⟨0, A, by rw [List.rotate_zero, hA]⟩
  · obtain ⟨A, hA⟩ := harc₂ 0 (invDarts X outerWalk) []
      (by rw [List.rotate_zero, List.append_nil]) hall
    exact ⟨0, A, by rw [List.rotate_zero, hA]⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessArcsBlocks_of_arcs

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
