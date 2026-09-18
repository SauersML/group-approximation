import GroupApproximation.Manuscript.NonMF.Full.GL05c.EndBlockModelClasses
import GroupApproximation.Manuscript.NonMF.Full.GL05c.EndBlockRefutation
import GroupApproximation.Meta.AxiomGuard

/-!
# `ExtremalEndBlockStatement` is refuted by the 16-dart model

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane nm-gl05c-02.

**Verdict: `ExtremalEndBlockStatement.{0, 0, 0}` is false** (`endBlockModel_not_statement`).  The
diagram `Model.diagram` over `Perm (Fin 3)` with the pocket `Model.pocketK` meets every
hypothesis of the statement (`GL05c/Diagram`, `GL05c/Pocket`).  Every one of its six face classes
fails in one of the four ways of `endBlock_not_statement_of_classes`:

* `O ∪ S` (index `5`) meets the exterior at the dart `15`;
* `P` (index `0`) is the face of the kept cell;
* `R1` (index `1`) moves `t₂ = [2,6,4]` as `false, true, false`, and `Q1` (index `2`) as
  `true, false, true`;
* `R2` (index `3`) moves `t₁⁻¹ = [8,12,10]` as `false, true, false`, and `Q2` (index `4`) as
  `true, false, true`.

The universes are those of the model: `G`, `Lambda = Empty` and the darts `Fin 16` all live in
`Type`.

## Manuscript status

Infrastructure for `thm:hull` (`non_mf_groups_exist.tex`, tex 2121, through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL05c

open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

/-- The target arc of the pocket is `t₂ = [2,6,4]`. -/
theorem endBlockModel_targetArc :
    Model.pocketK.targetArc.darts = ([2, 6, 4] : List Model.diagram.toCombMap.Dart) :=
  Model.tgtArc_darts

/-- The reversed source arc of the pocket is `t₁⁻¹ = [8,12,10]`. -/
theorem endBlockModel_invSourceArc :
    Embedded.invDarts Model.diagram Model.pocketK.sourceArc.darts =
      ([8, 12, 10] : List Model.diagram.toCombMap.Dart) := by
  have h : Model.pocketK.sourceArc.darts = ([11, 13, 9] : List Model.diagram.toCombMap.Dart) :=
    Model.srcArc_darts
  rw [h]
  decide

/-- The dart `0` lies on the kept cell `P`. -/
theorem endBlockModel_faceOf_kept :
    Model.diagram.toCombMap.faceOf 0 = (Embedded.cell Model.diagram Model.pocketK.kept).face := by
  change Model.M.faceOf (0 : Fin 16) = Model.face 0
  exact (Model.faceOf_eq_face 0 0).mpr (by decide)

/-- The dart `15` lies on the exterior `O`. -/
theorem endBlockModel_faceOf_outer :
    Model.diagram.toCombMap.faceOf 15 = Model.diagram.outerFace := by
  change Model.M.faceOf (15 : Fin 16) = Model.face 6
  exact (Model.faceOf_eq_face 15 6).mpr (by decide)

/-- The class `R1` moves `t₂` as `false, true, false`. -/
theorem endBlockModel_target_of_one {r : Model.diagram.toCombMap.Dart}
    (hr : endBlockModel_cls r = 1) :
    ¬GL05b.IsEndBlock (GL05b.movePred Model.diagram.toCombMap
      (GL05b.regionColour Model.diagram.toCombMap
        (walkKeep Model.diagram.toCombMap Model.pocketK.boundary.cycle) r))
      Model.pocketK.targetArc.darts := by
  rw [endBlockModel_targetArc]
  refine endBlock_not_isEndBlock_middle (by decide) (by decide) ?_ ?_ ?_ <;>
    (rw [endBlockModel_movePred, hr] <;> decide)

/-- The class `Q1` moves `t₂` as `true, false, true`. -/
theorem endBlockModel_target_of_two {r : Model.diagram.toCombMap.Dart}
    (hr : endBlockModel_cls r = 2) :
    ¬GL05b.IsEndBlock (GL05b.movePred Model.diagram.toCombMap
      (GL05b.regionColour Model.diagram.toCombMap
        (walkKeep Model.diagram.toCombMap Model.pocketK.boundary.cycle) r))
      Model.pocketK.targetArc.darts := by
  rw [endBlockModel_targetArc]
  refine endBlock_not_isEndBlock_ends (by decide) (by decide) ?_ ?_ ?_ <;>
    (rw [endBlockModel_movePred, hr] <;> decide)

/-- The class `R2` moves `t₁⁻¹` as `false, true, false`. -/
theorem endBlockModel_source_of_three {r : Model.diagram.toCombMap.Dart}
    (hr : endBlockModel_cls r = 3) :
    ¬GL05b.IsEndBlock (GL05b.movePred Model.diagram.toCombMap
      (GL05b.regionColour Model.diagram.toCombMap
        (walkKeep Model.diagram.toCombMap Model.pocketK.boundary.cycle) r))
      (Embedded.invDarts Model.diagram Model.pocketK.sourceArc.darts) := by
  rw [endBlockModel_invSourceArc]
  refine endBlock_not_isEndBlock_middle (by decide) (by decide) ?_ ?_ ?_ <;>
    (rw [endBlockModel_movePred, hr] <;> decide)

/-- The class `Q2` moves `t₁⁻¹` as `true, false, true`. -/
theorem endBlockModel_source_of_four {r : Model.diagram.toCombMap.Dart}
    (hr : endBlockModel_cls r = 4) :
    ¬GL05b.IsEndBlock (GL05b.movePred Model.diagram.toCombMap
      (GL05b.regionColour Model.diagram.toCombMap
        (walkKeep Model.diagram.toCombMap Model.pocketK.boundary.cycle) r))
      (Embedded.invDarts Model.diagram Model.pocketK.sourceArc.darts) := by
  rw [endBlockModel_invSourceArc]
  refine endBlock_not_isEndBlock_ends (by decide) (by decide) ?_ ?_ ?_ <;>
    (rw [endBlockModel_movePred, hr] <;> decide)

/-- The six class indices. -/
theorem endBlockModel_fin6 :
    ∀ i : Fin 6, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
  decide

/-- **Every dart of the model fails in one of the four ways**: its face class meets the exterior,
or meets the kept cell, or leaves no end block on `t₂` or on `t₁⁻¹`. -/
theorem endBlockModel_classes : ∀ r : Model.diagram.toCombMap.Dart,
    (∃ x, Model.diagram.toCombMap.faceOf x = Model.diagram.outerFace ∧
      Relation.EqvGen (CombMap.FaceClassStep Model.diagram.toCombMap
        (walkKeep Model.diagram.toCombMap Model.pocketK.boundary.cycle)) r x) ∨
    (∃ x, Model.diagram.toCombMap.faceOf x =
        (Embedded.cell Model.diagram Model.pocketK.kept).face ∧
      Relation.EqvGen (CombMap.FaceClassStep Model.diagram.toCombMap
        (walkKeep Model.diagram.toCombMap Model.pocketK.boundary.cycle)) r x) ∨
    ¬GL05b.IsEndBlock (GL05b.movePred Model.diagram.toCombMap
      (GL05b.regionColour Model.diagram.toCombMap
        (walkKeep Model.diagram.toCombMap Model.pocketK.boundary.cycle) r))
      Model.pocketK.targetArc.darts ∨
    ¬GL05b.IsEndBlock (GL05b.movePred Model.diagram.toCombMap
      (GL05b.regionColour Model.diagram.toCombMap
        (walkKeep Model.diagram.toCombMap Model.pocketK.boundary.cycle) r))
      (Embedded.invDarts Model.diagram Model.pocketK.sourceArc.darts) := by
  intro r
  rcases endBlockModel_fin6 (endBlockModel_cls r) with h | h | h | h | h | h
  · exact Or.inr (Or.inl
      ⟨0, endBlockModel_faceOf_kept, endBlockModel_eqvGen_of_cls (h.trans (by decide))⟩)
  · exact Or.inr (Or.inr (Or.inl (endBlockModel_target_of_one h)))
  · exact Or.inr (Or.inr (Or.inl (endBlockModel_target_of_two h)))
  · exact Or.inr (Or.inr (Or.inr (endBlockModel_source_of_three h)))
  · exact Or.inr (Or.inr (Or.inr (endBlockModel_source_of_four h)))
  · exact Or.inl
      ⟨15, endBlockModel_faceOf_outer, endBlockModel_eqvGen_of_cls (h.trans (by decide))⟩

/-- **`ExtremalEndBlockStatement` is false**, at the universes of the 16-dart model: the pocket
`Model.pocketK` of `Model.diagram` meets every hypothesis, and no face class meets the
conclusion. -/
theorem endBlockModel_not_statement : ¬ExtremalEndBlockStatement.{0, 0, 0} :=
  endBlock_not_statement_of_classes OsinPocketPinchedTwoGonModel.D 1 Model.diagram 0 4
    Model.leastArea Model.label_isLetter Model.pocketK Model.closedWalk Model.not_firstTurns
    Model.srcArc_length Model.tgtArc_length Model.not_unpinched Model.allNonFirstTurnsCrossed
    endBlockModel_classes

end GroupApproximation.Full.GL05c

#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_targetArc
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_invSourceArc
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_faceOf_kept
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_faceOf_outer
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_target_of_one
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_target_of_two
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_source_of_three
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_source_of_four
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_fin6
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_classes
#audit_axioms GroupApproximation.Full.GL05c.endBlockModel_not_statement
