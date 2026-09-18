import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepOrderGenus
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-63: the Order statement from a curve-side boundary cycle

Lane gl-p07-63.  States the residual `FourPieceWitness.witnessStepOrder_CycleStatement` and
proves `FourPieceWitness.witnessStepReclose_OrderStatement` (`WitnessStepRecloseProof.lean`)
from it, then the Reclosed, Bridge, skip and corner residuals.  Certifies no printed sentence on
its own.  NOT COMPILED: authored without running Lean.

## The residual

Premise block of the Order statement.  With `w = witnessSublistCurve a b G₁ G₂` and
`F = witnessFaces a b K C.face`: a face set `O` and a boundary cycle `B` of `O` such that
* `B` follows its boundary (`FollowsBoundary`);
* every entry `e` of `w` with `faceOf e ∈ F` has `alpha e` on `B.cycle`;
* some rotation of `invDarts X B.cycle` is a sublist of `w`.

## The reduction (`witnessStepOrder_order_of_cycle`)

From `hnb` and `hlab`, every inverse walk dart `alpha d` lies on `w` and has its face in `F`, so
`d` lies on `B.cycle`.  The genus lemma `witnessStepOrder_rotate_sublist` makes a rotation of
`invDarts X outerWalk` a sublist of `invDarts X B.cycle`.  Cyclic-sublist transitivity then puts
a rotation of it inside `w`, and `witnessStepOrder_before_sublist_iff` gives the order.

## Status (LOUD)

* **NOT weaker than the target as a formula.**  The residual implies the Order statement.  The
  converse is **not proved**.  With the gl-p07-62 witness (`O` the complement of `F`, `B` a
  rotation of `outerWalk`), the second clause asks for more than Order gives: every `F`-faced
  entry of `w` must lie on `invDarts X outerWalk`.  So this is a **different** statement, not an
  equivalent restatement, and not a strictly weaker one.
* **What it removes.**  It has no walk, no walk order and no genus content.  The planarity
  argument (that the walk is read in order along any following boundary cycle carrying it) is
  proved here (`WitnessStepOrderGenus.lean`).  It is a statement about the curve `w` alone: `w`
  contains, in cyclic order, the inverse boundary reading of one face set, and that reading
  covers the `F`-faced part of `w`.
* **Why not the plain `∃ O B` form.**  Replacing the second clause by `∀ d ∈ outerWalk,
  d ∈ B.cycle` gives a statement **equivalent** to Order: take `O` the complement of `F`
  (gl-p07-62).  Such forms were rejected as restatements.
* **Order ⇔ Reclosed ⇔ Bridge** (`witnessStepOrder_order_of_reclosed`,
  `witnessStepOrder_order_of_bridge`).  The gl-p07-60/61/62 chain is circular for the order.
* **Intended witness.**  `O` is the complement of the lobe that `w` bounds (the part of the
  pocket middle on the `F` side of the four pieces), and `B` its boundary cycle read forwards.
  Then `invDarts X B.cycle` is a rotation of `w`, and the second clause holds for every entry of
  `w`.
* **Truth.**  The genus lemma is checked (`SP/gl-p07-63/order_check.py`, 55719 planar cases,
  0 failures).  The residual itself is **NOT checked** for the real `witnessSublistCurve`.  This
  is the four-piece Jordan-type fact.  Risks:
  - an `F`-faced cell dart of `invDarts X G₁.darts` off the lobe boundary;
  - `a` and `b` sharing a path, so `w` pinches and the lobe boundary is not one cycle;
  - `w` not closing up as a face-set boundary at the four corners.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Residual of lane gl-p07-63: a boundary cycle read inside the curve.**  The premises of
`witnessStepReclose_OrderStatement`.  The conclusion: a face set `O` and a following boundary
cycle `B` of `O`; `alpha e ∈ B.cycle` for every entry `e` of the curve with its face in
`witnessFaces a b K C.face`; and a rotation of `invDarts X B.cycle` is a sublist of the curve.
LOUD: implies the Order statement; not weaker as a formula; converse not proved. -/
def witnessStepOrder_CycleStatement : Prop :=
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
          B.FollowsBoundary ∧
          (∀ e ∈ witnessSublistCurve a b G₁ G₂,
            X.toCombMap.faceOf e ∈ witnessFaces a b K C.face →
            X.toCombMap.alpha e ∈ B.cycle) ∧
          ∃ k : ℕ, (invDarts X B.cycle).rotate k <+ witnessSublistCurve a b G₁ G₂

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepOrder_CycleStatement

/-- **Lane gl-p07-63: the Order statement from the curve-side boundary cycle.** -/
theorem witnessStepOrder_order_of_cycle (h : witnessStepOrder_CycleStatement.{u, w, v}) :
    witnessStepReclose_OrderStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab hpinch
  obtain ⟨O, B, hwalk, hcurve, k, hk⟩ :=
    h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab hpinch
  have hsub : ∀ d ∈ outerWalk, d ∈ B.cycle := by
    intro d hd
    have hmem : X.toCombMap.alpha d ∈ invDarts X outerWalk := by
      simp only [invDarts, List.mem_map, List.mem_reverse]
      exact ⟨d, hd, rfl⟩
    have h1 := hcurve _ (witnessSublist_mem_curve (hlab _ hmem)) (hnb d hd)
    rw [X.toCombMap.alpha_involutive d] at h1
    exact h1
  obtain ⟨n, hn⟩ := witnessStepOrder_rotate_sublist E O B hwalk hsub
  obtain ⟨m, hm⟩ := witnessStepOrder_rotate_sublist_trans hn hk
  refine ⟨outerWalk.length - m % outerWalk.length, fun c hc d hd => ?_⟩
  rw [← witnessStepOrder_invDarts_rotate X outerWalk m]
  exact witnessStepOrder_before_sublist_iff (witnessSublist_curve_nodup a b G₁ G₂) hm
    (List.mem_rotate.mpr hc) (List.mem_rotate.mpr hd)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepOrder_order_of_cycle

/-- **Lane gl-p07-63: the Reclosed residual from the curve-side boundary cycle.** -/
theorem witnessStepOrder_reclosed_of_cycle (h : witnessStepOrder_CycleStatement.{u, w, v}) :
    witnessStepBridge_ReclosedStatement.{u, w, v} :=
  witnessStepReclose_reclosed_of_order (witnessStepOrder_order_of_cycle h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepOrder_reclosed_of_cycle

/-- **Lane gl-p07-63: the Bridge from the curve-side boundary cycle.** -/
theorem witnessStepOrder_bridge_of_cycle (h : witnessStepOrder_CycleStatement.{u, w, v}) :
    WitnessStepGenusBridgeStatement.{u, w, v} :=
  witnessStepReclose_bridge_of_order (witnessStepOrder_order_of_cycle h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepOrder_bridge_of_cycle

/-- **Lane gl-p07-63: the skip residual from the curve-side boundary cycle.** -/
theorem witnessStepOrder_skip_of_cycle (h : witnessStepOrder_CycleStatement.{u, w, v}) :
    WitnessStepSkipStatement.{u, w, v} :=
  witnessStepReclose_skip_of_order (witnessStepOrder_order_of_cycle h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepOrder_skip_of_cycle

/-- **Lane gl-p07-63: the corner residual from the curve-side boundary cycle.** -/
theorem witnessStepOrder_corner_of_cycle (h : witnessStepOrder_CycleStatement.{u, w, v}) :
    WitnessStepCornerResidualStatement.{u, w, v} :=
  witnessStepReclose_corner_of_order (witnessStepOrder_order_of_cycle h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepOrder_corner_of_cycle

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
