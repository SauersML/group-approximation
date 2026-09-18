import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchParityWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-56: no entry step of the walk into the prefix before `y`

Lane gl-p07-56.  States the residual `FourPieceWitness.WitnessStepPinchParityStatement`.
Same premise block and same backward disjunct as `WitnessStepPinchLobeStatement`.  At an
off-lobe pinch `(x, y)` with `w = pre ++ y :: (mid ++ x :: post)`, the forward disjunct asks
only: **no entry step** `(x', y')` of `invDarts X ow` has `x' ∉ pre`, `y' ∈ pre`, where the
entry step comes with the local data the reduction supplies (`faceOf y' ∈ F`, and the sector
from `y'` to `α x'` is a fan off `F`).  Certifies no printed sentence on its own.  NOT COMPILED.

See `WitnessStepPinchParityWalk.lean` for the full proof, the truth check and the LOUD notes.
LOUD: logically **equivalent** to `WitnessStepPinchLobeStatement` (both directions are proved in
`WitnessStepPinchParityProof.lean`), strictly smaller only in proof content.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Residual of lane gl-p07-56: at an off-lobe pinch with `y` before `x` on the curve, the
inverted enclosing walk has no entry step into the curve prefix before `y`.**  Same premises and
the same backward disjunct as `WitnessStepPinchLobeStatement`.  LOUD: logically equivalent to
that statement, strictly smaller only in proof content. -/
def WitnessStepPinchParityStatement : Prop :=
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
                False) ∨
          ∀ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
            (invDarts X outerWalk).rotate n = s ++ x :: y :: t →
            WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
              (invDarts X outerWalk) y x

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepPinchParityStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
