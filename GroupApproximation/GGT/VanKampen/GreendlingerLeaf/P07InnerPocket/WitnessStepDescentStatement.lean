import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchParityStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepDescentList
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-58: the enclosing walk winds once around the curve

Lane gl-p07-58.  States the residual `FourPieceWitness.WitnessStepDescentStatement`.  Certifies
no printed sentence on its own.  NOT COMPILED.

Write `w = witnessSublistCurve a b G₁ G₂` (duplicate free) and `l = invDarts X outerWalk`
(`l ⊆ w`).  Index `w` by first occurrence (`witnessStepDescent_pos`).  The forward disjunct
says: **one cycle of `l` advances along `w` by at most one full turn.**  In symbols, the sum
over the cyclic steps `(x, y)` of `l` of the forward cyclic gap from `x` to `y` modulo `|w|` is
at most `|w|`.  Premises and backward disjunct are those of `WitnessStepPinchParityStatement`.

By telescoping (`witnessStepDescent_gapSum_steps`, proved), the gap sum is `#descents * |w|`,
where a descent is a step `(x, y)` with `y` not after `x` in `w`.  So the forward disjunct says
exactly that `l` has at most one descent against `w`.  This is the genuine planar input (winding
number one), and it is the only thing left.

Truth check.  Model `SP/gl-p07-58/descent_model.py` (planar flowers with 1-3 petals, types
T/D/S, every cut set, every linearisation of `Γ`): in 26488 cases the gap sum equals `|w|`
exactly (one descent), so the bound holds and is tight.  For `l = []` the sum is `0`.  For
`l = [e]` the sum is `|w|`.  On random lists the telescoping identity holds, and so does the
two-descent count used by the reduction.

LOUD: **logically equivalent** to `WitnessStepPinchParityStatement`,
`WitnessStepPinchArcStatement` and `WitnessCurveSublistStepStatement`.
`WitnessStepDescentProof.lean` proves the direction from this statement to each of them.
`WitnessStepDescentConverse.lean` proves `WitnessCurveSublistStepStatement → this`.  So this is
not strictly weaker.  It is strictly smaller in proof content: the telescoping identity and the
two-descent count are proved, and no pinch, lobe, fan or face data remain.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Residual of lane gl-p07-58: the inverted enclosing walk winds at most once around the
witness curve.**  The total forward cyclic gap of the steps of `invDarts X outerWalk`, measured
in the first-occurrence index of `witnessSublistCurve a b G₁ G₂`, is at most the curve length.
Same premises and the same backward disjunct as `WitnessStepPinchParityStatement`.  LOUD:
logically equivalent to it, strictly smaller only in proof content. -/
def WitnessStepDescentStatement : Prop :=
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
      ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 → C.face ∉ b.1 →
      ∀ outerWalk : List X.toCombMap.Dart,
        EnclosedFaceSetSucc X (witnessFaces a b K C.face) outerWalk →
        (∀ d ∈ outerWalk,
          X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K C.face) →
        (∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₁.darts ∨ e ∈ invDarts X G₂.darts ∨
          X.toCombMap.alpha e ∈ a.sideFrom j ∨ X.toCombMap.alpha e ∈ b.sideFrom i) →
        witnessStepDescent_gapSum
            (fun e => witnessStepDescent_pos e (witnessSublistCurve a b G₁ G₂))
            (witnessSublistCurve a b G₁ G₂).length
            (witnessStepDescent_steps (invDarts X outerWalk)) ≤
          (witnessSublistCurve a b G₁ G₂).length ∨
          ∀ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
            (invDarts X outerWalk).rotate n = s ++ x :: y :: t →
            WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
              (invDarts X outerWalk) y x

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepDescentStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
