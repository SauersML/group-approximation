import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchParityStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-57: the entry step into the prefix lands at the curve-first dart

Lane gl-p07-57.  States the residual `FourPieceWitness.WitnessStepPinchArcStatement`.  Certifies
no printed sentence on its own.  NOT COMPILED.

Same premise block and same backward disjunct as `WitnessStepPinchParityStatement`.  The forward
disjunct is the forward disjunct of `WitnessStepPinchParityStatement` with **one extra hypothesis**:
the second dart `y'` of the entry step is the **curve-first dart of the walk**, i.e.
`w = u ++ y' :: z` with no dart of `u` on `l = invDarts X ow`.

Why it is smaller in proof content: `WitnessStepPinchArcProof.lean` discharges every entry step
whose second dart is not curve-first, by the per-step classification
(`witnessStepPinchArc_classify`) and an induction on the length of the prefix.  A forward
`StepNext` step `x' → y'` of the first kind puts `x'` before `y'`, hence in the prefix.  One of the
second kind has `y'` curve-first.  An entry step that is itself an off-lobe pinch has a shorter
prefix, and the induction shows that prefix is off `l`, so again `y'` is curve-first.

What is left (truth: winding one, see `SP/gl-p07-57/arc_model.py`): the walk `l` has exactly one
descent relative to the curve `w`, and that descent lands at the curve-first dart `m`.  So the
configuration "an off-lobe pinch `(x, y)` with `y` before `x`, and a second step `(x', m)` with
`m` before `y` and `x'` not before `y`" is two descents, and it never occurs.  This is a planar
Jordan fact.  It is not a local turn fact: in truth the prefix before `y` is off `l`, `l` is often
not a contiguous arc of `w`, and the step into `m` at the list end (`x' = w.getLast`,
`m = w.head`) is an ordinary curve step.

LOUD: logically **equivalent** to `WitnessStepPinchParityStatement` (both directions are proved in
`WitnessStepPinchArcProof.lean`).  It is strictly smaller only in proof content: the entries at a
dart that is not curve-first are proved, not assumed.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Residual of lane gl-p07-57: no entry step into the curve prefix at the curve-first dart.**
The same statement as `WitnessStepPinchParityStatement`, with the extra hypothesis that the
second dart `y'` of the entry step is the first dart of the curve on the walk.  LOUD: logically
equivalent to `WitnessStepPinchParityStatement`, strictly smaller only in proof content. -/
def WitnessStepPinchArcStatement : Prop :=
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
        (∀ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
            (invDarts X outerWalk).rotate n = s ++ x :: y :: t →
            ¬ WitnessStepCellTurn G₁ G₂ outerWalk y →
            ¬ WitnessStepSideTurn a b G₁ G₂ outerWalk y →
            ¬ WitnessStepBlockTurn a b G₁ G₂ x y →
            ¬ WitnessStepCornerTurn a b G₁ G₂ outerWalk y →
            WitnessStepPinchOffAt a b K C.face G₁ G₂ outerWalk x y →
            ∀ pre mid post : List X.toCombMap.Dart,
              witnessSublistCurve a b G₁ G₂ = pre ++ y :: (mid ++ x :: post) →
              ∀ (n' : ℕ) (s' t' : List X.toCombMap.Dart) (x' y' : X.toCombMap.Dart),
                (invDarts X outerWalk).rotate n' = s' ++ x' :: y' :: t' →
                x' ∉ pre → y' ∈ pre →
                X.toCombMap.faceOf y' ∈ witnessFaces a b K C.face →
                WitnessStepPinchFan X.toCombMap (witnessFaces a b K C.face) y'
                  (X.toCombMap.alpha x') →
                (∃ u z : List X.toCombMap.Dart, witnessSublistCurve a b G₁ G₂ = u ++ y' :: z ∧
                  ∀ e ∈ u, e ∉ invDarts X outerWalk) →
                False) ∨
          ∀ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
            (invDarts X outerWalk).rotate n = s ++ x :: y :: t →
            WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
              (invDarts X outerWalk) y x

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepPinchArcStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
