import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalWrapInPlace
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.Cases
import GroupApproximation.Meta.AxiomGuard

/-!
# The outer-pinch step without wrap

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-12a.

`PocketOuterPinchStepSectionStatement` (`Estimating/OsinPocketPinchOuterDispatch`) with the extra
premise `hi ≤ |outerDarts X|` (no wrap of the target arc), and its reduction to the no-wrap in-place
rose step, by the case split of `Piece10.proof_of_cases` (the non-rose case is closed
unconditionally by `P10ChordLift.proof`; the rose case is in place, in the same diagram).

* `PocketOuterPinchStepSectionNoWrapStatement`: the step with the premise `hi ≤ |outerDarts X|`.
* `stepNoWrap_of_step` (proved): implied by the original step.
* `stepNoWrap_of_inPlaceStepNoWrap` (proved): from `RoseInPlaceStepNoWrapStatement`.
* `stepNoWrap_of_extremalCoreNoWrap`, `stepNoWrap_of_contigResidualNoWrap` (proved): from the
  no-wrap core and the no-wrap residual.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

universe u w v

open Embedded Surgery.MapCollapse

/-- **One step of the section pinch at an outer pinch, without wrap**:
`PocketOuterPinchStepSectionStatement` with the premise `hi ≤ |outerDarts X|`. -/
def PocketOuterPinchStepSectionNoWrapStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              ∀ (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), hi ≤ (outerDarts X).length →
                X.LeastArea →
                (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
                ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
                  K.sourceArc.length < (cellDarts X K.source).length →
                  K.targetArc.length < (outerDarts X).length →
                  ¬Unpinched X.toCombMap K.faces →
                    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
                      Nonempty (OEquivalentDiscDiagram X X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
                        K'.ClosedWalk ∧ K'.sourceArc.length < (cellDarts X' K'.source).length ∧
                        K'.targetArc.length < (outerDarts X').length ∧
                        K'.repeatedVisits < K.repeatedVisits

/-- **The no-wrap step is implied by the original step.** -/
theorem stepNoWrap_of_step (h : PocketOuterPinchStepSectionStatement.{u, w, v}) :
    PocketOuterPinchStepSectionNoWrapStatement.{u, w, v} := by
  intro _ _ _ D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  refine ⟨rho0, hrho0, fun rho hrho' W hcondition => ?_⟩
  intro X lo hi _ hlea hlabel K hK hturns hprop htgt hpinch
  exact hrho rho hrho' W hcondition X lo hi hlea hlabel K hK hturns hprop htgt hpinch

/-- **The no-wrap step from the no-wrap in-place rose step**: split on the rose configuration; the
non-rose case is `P10ChordLift.proof`, the rose case stays in the same diagram. -/
theorem stepNoWrap_of_inPlaceStepNoWrap (h : RoseInPlaceStepNoWrapStatement.{u, w, v}) :
    PocketOuterPinchStepSectionNoWrapStatement.{u, w, v} := by
  intro _ _ _ D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ :=
    P10ChordLift.proof.{u, w, v} D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  refine ⟨rho0, hrho0, fun rho hrho' W hcondition => ?_⟩
  intro X lo hi hwrap hlea hlabel K hK hturns hprop htgt hpinch
  by_cases hall : P10ChordLift.AllNonFirstTurnsCrossed K
  · obtain ⟨K', hK', hprop', htgt', hlt⟩ :=
      h D eps X lo hi hwrap hlea hlabel K hK hturns hprop htgt hpinch hall
    exact ⟨X, K', ⟨OEquivalentDiscDiagram.refl X⟩, hlabel, hK', hprop', htgt', hlt⟩
  · exact hrho rho hrho' W hcondition X lo hi hlea hlabel K hK hturns hprop htgt hpinch hall

/-- **The no-wrap step from the no-wrap extremal core.** -/
theorem stepNoWrap_of_extremalCoreNoWrap (h : RoseExtremalCoreNoWrapStatement.{u, w, v}) :
    PocketOuterPinchStepSectionNoWrapStatement.{u, w, v} :=
  stepNoWrap_of_inPlaceStepNoWrap (inPlaceStepNoWrap_of_extremalCoreNoWrap h)

/-- **The no-wrap step from the no-wrap residual contiguity clauses.** -/
theorem stepNoWrap_of_contigResidualNoWrap
    (h : RoseExtremalContigResidualNoWrapStatement.{u, w, v}) :
    PocketOuterPinchStepSectionNoWrapStatement.{u, w, v} :=
  stepNoWrap_of_extremalCoreNoWrap (extremalCoreNoWrap_of_contigResidualNoWrap h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.PocketOuterPinchStepSectionNoWrapStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.stepNoWrap_of_step
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.stepNoWrap_of_inPlaceStepNoWrap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.stepNoWrap_of_extremalCoreNoWrap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.stepNoWrap_of_contigResidualNoWrap
