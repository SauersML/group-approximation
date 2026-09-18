import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBridgeModel
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepGenusProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-61: the Bridge residual from one reclosing boundary cycle

Lane gl-p07-61.  States the residual `FourPieceWitness.witnessStepBridge_ReclosedStatement` and
proves `WitnessStepGenusBridgeStatement` and `WitnessStepSkipStatement` from it.  Certifies no
printed sentence on its own.  NOT COMPILED: authored without running Lean.

## The residual

The premise block is that of `WitnessStepGenusBridgeStatement`.  Write
`w = witnessSublistCurve a b G₁ G₂` and `l = invDarts X outerWalk`.  The residual asks for one
face set `O` and one boundary cycle `B` of `O` such that
* `B` follows its boundary (`FollowsBoundary`);
* every dart of `outerWalk` lies on `B.cycle`;
* on entries of `l`, the order of `w` is the order of `invDarts X B.cycle`.

## What is discharged (`WitnessStepBridgeModel.lean`)

From `O` and `B`, `witnessStepBridge_model` builds the whole Bridge witness:
`N = mirror (reclosedMap X O B)`, `ι = Subtype.val`, and `l'`, `Γ` the kept-dart lifts of `l` and of
`invDarts X B.cycle`.  Proved there:
* planarity of `N`: the mirror (`WitnessStepBridgeMirror.lean`) and `reclosedMap_planar`;
* `Γ` a face cycle of `N`: `newFaceDarts`, reversed through `α`;
* every cyclic step of `l'` a `WitnessStepGenusSucc` step of `N`.  `turn_next` read backwards,
  transported through the first return `reclosed_sigma_firstReturn`
  (`WitnessStepBridgeFirstReturn.lean`);
* the order transfer through the injective `Subtype.val`.

## Status (LOUD)

* **Smaller in proof content.**  The residual has no map, no planarity, no face cycle and no
  successor clause.  It asks only for a face set with a following boundary cycle that carries the
  walk and reads `w` in order.
* **Not claimed strictly weaker as a formula.**  It may well be logically equivalent to the
  Bridge.  On paper both follow from, and give, the forward-sublist order of `w` along a reclosed
  boundary.  The converse `Bridge → residual` is not proved.
* **Not an equivalent restatement of the forbidden kinds.**  It mentions no `gapSum`, no descent,
  no crossing count and no local pick surgery.
* **The gl-p07-60 intended witness is wrong as stated.**  That witness is
  `O = sideFaces X K.walk` (the pocket middle), but the curve `w` is not carried by `K.walk`.  The
  face set here is instead the **collapsed** set: the complement of the pocket middle, whose
  boundary cycle is the curve.

## Truth check (LOUD)

`SP/gl-p07-61/reclose_check.py` (scratchpad) extends `SP/gl-p07-60/bridge_check.py` to multi-face
pockets with pinch vertices.  `O` is the complement of the middle, `B` its `FollowsBoundary`
cycle, the curve is `B` read inversely, and the walk is an `EnclosedFaceSetSucc` walk inside the
boundary.  Checked:
* (P) `N` planar;
* (R) first return;
* (F) `Γ` a face cycle;
* (S) successor steps;
* (K) the order clause.

It checked **47492 configurations with 0 failures in P, R, F, S and K**.  Of these, 10846 have a
pinch vertex, 3712 a multi-face `O` and 24561 a multi-face middle.  A further 20848 were skipped
because the boundary is not one cycle.

**NOT checked:** that the real `witnessSublistCurve a b G₁ G₂` is, on the walk, in the order of
the inverse boundary reading of the collapsed set.  In the models the curve is that reading by
construction.  This identification is the content of the residual.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Residual of lane gl-p07-61: one reclosing boundary cycle carrying the curve.**  The premises
of `WitnessStepGenusBridgeStatement`.  The conclusion: a face set `O` and a boundary cycle `B` of
`O` that follows its boundary, carries `outerWalk`, and on whose inverse reading
`witnessSublistCurve a b G₁ G₂` has its order on `invDarts X outerWalk`.  LOUD: smaller in proof
content; not claimed strictly weaker as a formula (possibly equivalent). -/
def witnessStepBridge_ReclosedStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    0 < (a.cellArcList i).length → 0 < (a.cellArcList j).length →
    0 < (b.cellArcList i).length → 0 < (b.cellArcList j).length →
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
      ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 →
      C.face ∉ b.1 →
      ∀ outerWalk : List X.toCombMap.Dart,
        EnclosedFaceSetSucc X (witnessFaces a b K C.face) outerWalk →
        (∀ d ∈ outerWalk,
          X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K C.face) →
        (∀ e ∈ invDarts X outerWalk,
          e ∈ invDarts X G₁.darts ∨ e ∈ invDarts X G₂.darts ∨
          X.toCombMap.alpha e ∈ a.sideFrom j ∨ X.toCombMap.alpha e ∈ b.sideFrom i) →
        (∃ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
          (invDarts X outerWalk).rotate n = s ++ x :: y :: t ∧
          ¬ WitnessStepCellTurn G₁ G₂ outerWalk y ∧
          ¬ WitnessStepSideTurn a b G₁ G₂ outerWalk y ∧
          ¬ WitnessStepBlockTurn a b G₁ G₂ x y ∧
          ¬ WitnessStepCornerTurn a b G₁ G₂ outerWalk y ∧
          WitnessStepPinchOffAt a b K C.face G₁ G₂ outerWalk x y) →
        ∃ (O : Finset X.toCombMap.Face) (B : BoundaryCycle X.toCombMap O),
          B.FollowsBoundary ∧ (∀ d ∈ outerWalk, d ∈ B.cycle) ∧
          ∀ c ∈ invDarts X outerWalk, ∀ d ∈ invDarts X outerWalk,
            (WitnessStepGenusBefore (witnessSublistCurve a b G₁ G₂) c d ↔
              WitnessStepGenusBefore (invDarts X B.cycle) c d)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_ReclosedStatement

/-- **Lane gl-p07-61: the Bridge residual from one reclosing boundary cycle.** -/
theorem witnessStepBridge_of_reclosed (h : witnessStepBridge_ReclosedStatement.{u, w, v}) :
    WitnessStepGenusBridgeStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab hpinch
  obtain ⟨O, B, hwalk, hsub, hcompat⟩ :=
    h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab hpinch
  exact witnessStepBridge_model E O B hwalk hsub _ hcompat

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_of_reclosed

/-- **Lane gl-p07-61: the skip residual from one reclosing boundary cycle.** -/
theorem witnessStepBridge_skip_of_reclosed (h : witnessStepBridge_ReclosedStatement.{u, w, v}) :
    WitnessStepSkipStatement.{u, w, v} :=
  witnessStepGenus_skip_of_bridge (witnessStepBridge_of_reclosed h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_skip_of_reclosed

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
