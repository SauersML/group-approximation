import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.RegionStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Pointwise conclusions of the rose lobe chain, part 1

Lane gl-p10-74.  The residuals of the rose lobe chain (`roseLobeRegion_Statement`,
`roseLobeCore_Statement`, `roseLobeBlk_BlockStatement`, ...) all quantify over every pocket
`K` with the same hypotheses, and every reduction between them is pointwise: the proof calls the
stronger statement at the same `K` only.  To add the premises of `P10ChordLift.RoseStepStatement`
(hyperbolicity, `OsinCCondition`, the thresholds) to the top residual, the chain is restated
pointwise.  For a fixed pocket `K`, `roseLobeOsin_RegionAt K`, `roseLobeOsin_CoreAt K` and
`roseLobeOsin_BlkAt K` are the conclusions, verbatim, of `roseLobeRegion_Statement`,
`roseLobeCore_Statement` (equal to that of `roseLobeNoBub_Statement`) and
`roseLobeBlk_BlockStatement`.  They are `abbrev`s, so anonymous constructors and `obtain`
unfold them.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- The conclusion of `roseLobeRegion_Statement` at the pocket `K` (a lobe or a lake). -/
abbrev roseLobeOsin_RegionAt (K : PocketFaceSet D eps X lo hi) : Prop :=
  (∃ rs : List X.toCombMap.Dart, rs ≠ [] ∧ (∀ r ∈ rs, r ∈ K.boundary.cycle) ∧
    (∃ x, X.toCombMap.faceOf x = (cell X K.kept).face ∧ ∀ r ∈ rs, ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
    ∃ A B C : List X.toCombMap.Dart,
      roseLobeRegion_Block K.boundary.cycle (fun d => ∀ r ∈ rs, ¬Relation.EqvGen
        (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r d)
        A B C ∧
      roseLobeRegion_Place (fun d => ∀ r ∈ rs, ¬Relation.EqvGen
        (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r d)
        (invDarts X K.sourceArc.darts) K.targetArc.darts A B C) ∨
  (∃ y ∈ K.boundary.cycle,
    (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen (CombMap.FaceClassStep
      X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) (X.toCombMap.alpha y) x) ∧
    (∀ x, X.toCombMap.faceOf x = (cell X K.source).face → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle))
        (X.toCombMap.alpha y) x) ∧
    ∃ A B C : List X.toCombMap.Dart,
      roseLobeRegion_Block K.boundary.cycle (fun d => ¬Relation.EqvGen
        (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle))
          (X.toCombMap.alpha y) (X.toCombMap.alpha d)) A B C)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsin_RegionAt

/-- The conclusion of `roseLobeCore_Statement` (and of `roseLobeNoBub_Statement`) at `K`. -/
abbrev roseLobeOsin_CoreAt (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∃ rs : List X.toCombMap.Dart,
    ((rs ≠ [] ∧ ∀ r ∈ rs, r ∈ K.boundary.cycle) ∨
      ∃ r, rs = [r] ∧
        (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
          (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
        ∃ y ∈ K.boundary.cycle, Relation.EqvGen
          (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r y ∨
          Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
            (walkKeep X.toCombMap K.boundary.cycle)) r (X.toCombMap.alpha y)) ∧
    ((∀ r ∈ rs, X.toCombMap.faceOf r ∈ K.faces) ∨
      (cell X K.source).face ∉ flipFaces X.toCombMap K.faces (roseJunctionCore_lobeColour
        X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs)) ∧
    ((∃ r, rs = [r] ∧ X.toCombMap.faceOf r ∉ K.faces) ∨
      (cell X K.kept).face ∈ flipFaces X.toCombMap K.faces (roseJunctionCore_lobeColour
        X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs)) ∧
    ∃ A B C : List X.toCombMap.Dart, K.boundary.cycle = A ++ B ++ C ∧
      ((B.filter (movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
            (walkKeep X.toCombMap K.boundary.cycle) rs)) = [] ∧
          (A ++ C).filter (movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
            (walkKeep X.toCombMap K.boundary.cycle) rs)) = A ++ C ∧
          A ++ C ≠ []) ∨
        (B.filter (movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
            (walkKeep X.toCombMap K.boundary.cycle) rs)) = B ∧
          (A ++ C).filter (movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
            (walkKeep X.toCombMap K.boundary.cycle) rs)) = [] ∧
          B ≠ [])) ∧
      ((∃ r, rs = [r] ∧ X.toCombMap.faceOf r ∉ K.faces) ∨
        (((A ++ C).filter (movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
              (walkKeep X.toCombMap K.boundary.cycle) rs)) = [] ∨
            (∃ d ∈ B, d ∉ invDarts X K.sourceArc.darts) ∨
            B <+: invDarts X K.sourceArc.darts ∨ B <:+ invDarts X K.sourceArc.darts) ∧
          ((∀ d ∈ B, d ∉ K.targetArc.darts) ∨
            (C = [] ∧ B.filter (movePred X.toCombMap (roseJunctionCore_lobeColour
              X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs)) = []) ∨
            ((A ++ C).filter (movePred X.toCombMap (roseJunctionCore_lobeColour
                X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs)) = [] ∧
              ∀ d ∈ A, d ∉ K.targetArc.darts))))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsin_CoreAt

/-- The conclusion of `roseLobeBlk_BlockStatement` at `K`. -/
abbrev roseLobeOsin_BlkAt (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∃ rs : List X.toCombMap.Dart,
    ((rs ≠ [] ∧ ∀ r ∈ rs, r ∈ K.boundary.cycle) ∨
      ∃ r, rs = [r] ∧
        (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
          (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
        ∃ y ∈ K.boundary.cycle, Relation.EqvGen
          (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r y ∨
          Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
            (walkKeep X.toCombMap K.boundary.cycle)) r (X.toCombMap.alpha y)) ∧
    (cell X K.source).face ∉ flipFaces X.toCombMap K.faces (roseJunctionCore_lobeColour
      X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs) ∧
    (cell X K.kept).face ∈ flipFaces X.toCombMap K.faces (roseJunctionCore_lobeColour
      X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs) ∧
    (invDarts X K.sourceArc.darts).filter (movePred X.toCombMap
        (roseJunctionCore_lobeColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)
          rs)) <:+: invDarts X K.sourceArc.darts ∧
    (∃ k, K.targetArc.start.1 + k ≤ (outerDarts X).length ∧
      K.targetArc.darts.filter (movePred X.toCombMap
        (roseJunctionCore_lobeColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)
          rs)) <+: K.targetArc.darts.drop k) ∧
    ∃ A B C : List X.toCombMap.Dart, K.boundary.cycle = A ++ B ++ C ∧
      ((B.filter (movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
            (walkKeep X.toCombMap K.boundary.cycle) rs)) = [] ∧
          (A ++ C).filter (movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
            (walkKeep X.toCombMap K.boundary.cycle) rs)) = A ++ C ∧
          A ++ C ≠ []) ∨
        (B.filter (movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
            (walkKeep X.toCombMap K.boundary.cycle) rs)) = B ∧
          (A ++ C).filter (movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
            (walkKeep X.toCombMap K.boundary.cycle) rs)) = [] ∧
          B ≠ []))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsin_BlkAt

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
