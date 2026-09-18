import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsTouchNIParts
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsTouchTail
import GroupApproximation.GGT.VanKampen.SurgeryReclosedVertices
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-76: the arc interface (lane gl-p07-77's clauses)

`pinchAbsTouchNI_ArcStatement` states clauses 5–8 of the touch tail, `pinchAbsTouchNI_ArcPart`,
for `w' = pinchLobe_walk (pinchAbs_set a b K G₁ G₂ C.face) comp`.  The premises are the same as
those of `pinchAbsTouchNI_NIStatement` (`PinchAbsTouchNIStatement.lean`).

Lane gl-p07-76 does NOT prove it.  It is lane gl-p07-77's target, and is stated here only as the
interface that `PinchAbsTouchNIFollow.lean` consumes.  Lane gl-p07-77 may discharge it with its
own clauses.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Interface: the arc clauses of the touch tail** (lane gl-p07-77's target).  The premises are
those of `pinchAbsTouchNI_NIStatement`.  The conclusion is `pinchAbsTouchNI_ArcPart`, which is
clauses 5–8 of `pinchCut_Tail b G₁ G₂ (invDarts X w')`, verbatim. -/
def pinchAbsTouchNI_ArcStatement : Prop :=
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
      (hw.outerCycle X.planar).FollowsBoundary →
      X.outerFace ∉ sideFaces X.toCombMap K.walk →
      (reclosedMap X.toCombMap (sideFaces X.toCombMap K.walk)
          (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      (reclosedMap X.toCombMap (sideOutside X.toCombMap K.walk)
          (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 → C.face ∉ b.1 →
        ¬ (0 < (a.cellArcList i).length ∧ 0 < (a.cellArcList j).length ∧
            0 < (b.cellArcList i).length ∧ 0 < (b.cellArcList j).length ∧
            (∀ d ∈ G₁.darts, PocketRun.PinchFreeAt X.toCombMap d) ∧
            (∀ d ∈ G₂.darts, PocketRun.PinchFreeAt X.toCombMap d) ∧
            ∃ outerWalk : List X.toCombMap.Dart,
              EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K C.face) outerWalk ∧
                ∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈
                  FourPieceWitness.witnessFaces a b K C.face) →
        (∀ outerWalk : List X.toCombMap.Dart,
          EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K C.face) outerWalk →
          (∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈
            FourPieceWitness.witnessFaces a b K C.face) →
          ((0 < (a.cellArcList i).length ∧ 0 < (a.cellArcList j).length ∧
              0 < (b.cellArcList i).length ∧ 0 < (b.cellArcList j).length) ∨
            PinchCase.WalkDegenCaseNoninterleave b G₁ G₂ outerWalk) →
          ¬ FourPieceWitness.AbsorbFaceSetStepGood G₁ G₂ outerWalk ∧
            ∃ (p : ℕ) (hp : p < outerWalk.length),
              (outerWalk[p] ∈ G₁.darts ∨ outerWalk[p] ∈ G₂.darts) ∧
              ¬ PocketRun.PinchFreeAt X.toCombMap outerWalk[p]) →
        ∀ comp : FaceSetCircuits.Component X.toCombMap
            (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ C.face)),
          C.face ∈ sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ C.face) comp) →
          EnclosedFaceSetSucc X
              (sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ C.face) comp))
              (invDarts X (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ C.face) comp)) →
          pinchAbsTouchNI_ArcPart G₁ G₂
            (invDarts X (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ C.face) comp))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchNI_ArcStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
