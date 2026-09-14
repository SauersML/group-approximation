import GroupApproximation.GGT.VanKampen.Estimating.OsinGreendlingerWaistV5
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassEndLoopsSide
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellPocketAssembly
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellRCellEnclosed
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketNoSpurSucc
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellSpurEnclosure
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonEulerAssembly
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkEulerNoninterleaving
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellPinchOuterDispatch
import GroupApproximation.Meta.AxiomGuard

/-!
# The Greendlinger waist at leaf level

Osin, arXiv:math/0411039v3, §9 and Appendix, Lemmas 9.3, 9.4, 9.7 and 4.4.  An additive waist that
pushes each residual of `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV5`
(`OsinGreendlingerWaistV5`) down through the reductions on origin:

* the class end loops from the budget, `osinLemma94ClassEndLoopsInput_of_budget`;
* the same-cell pocket values from the cell-free value and the loop cut,
  `osinLemma94SameCellPocketInput_of_loopCut`;
* the relator-cell branch of Case 1 from the no-spur pockets and the spur branch,
  `osinLemma94CaseOneRCell_of_noSpurPockets`, over the successor-form enclosed loop cut
  (`osinLemma94CaseOneNoSpurXPocket_of_enclosedLoopCutSucc`, its `Y` form, and
  `osinLemma94CaseOneRCellSpur_of_enclosure` with the successor-form enclosed subdiagram and the spur
  enclosure);
* C6′ at section level from the Euler walk and the gap inputs of two-gon pockets, through
  `twoGonHoldsInput_of_eulerWalk` (`osinTwoGonHoldsSection_of_eulerWalk` below);
* the Euler equalities of the cell pocket walk from non-interleaving, `cellPocketWalkEuler_of_noninterleaving`;
* the section cell pinch from the outer pinch step, `cellPocketPinchSectionStatement_of_outerPinchStep`;
* the two-arc section pinch from the outer pinch step,
  `pocketPinchLabelledSectionTwoArcStatement_of_outerPinchStep`.

The spanning shape of class-word pairs, the proper arcs of the cell walk and the two-arc face set
producer have no reduction on origin and stay as they are.

* `OsinTwoGonEulerWalkSectionStatement`, `OsinTwoGonEulerGapSectionStatement`: the inputs of
  `twoGonHoldsInput_of_eulerWalk`, uniformly in the parameters, with the prefix of
  `OsinTwoGonHoldsSectionStatement`.  `osinTwoGonHoldsSection_of_eulerWalk` combines them at the larger
  thresholds.
* `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV6`: fifteen named leaf residual Props.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemmas 9.7 and 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **The Euler walk of two-gon pockets, uniformly in the parameters**: `TwoGonEulerWalkInput` beyond
thresholds under Osin's condition, with the prefix of `OsinTwoGonHoldsSectionStatement`. -/
def OsinTwoGonEulerWalkSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              TwoGonEulerWalkInput.{u, w, v} D lambda c eps W

/-- **The gap input of two-gon pockets, uniformly in the parameters**: `TwoGonEulerGapInput` beyond
thresholds under Osin's condition, with the prefix of `OsinTwoGonHoldsSectionStatement`. -/
def OsinTwoGonEulerGapSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              TwoGonEulerGapInput.{u, w, v} D lambda c eps W

/-- **C6′ at section level from the Euler walk and the gap inputs**, at the larger of the two
thresholds for `ε` and for `ρ`. -/
theorem osinTwoGonHoldsSection_of_eulerWalk
    (hwalk : OsinTwoGonEulerWalkSectionStatement.{u, w, v})
    (hgap : OsinTwoGonEulerGapSectionStatement.{u, w, v}) :
    OsinTwoGonHoldsSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := hwalk D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps1, heps1⟩ := hgap D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max eps0 eps1, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps ((le_max_left eps0 eps1).trans heps)
  obtain ⟨rho1, -, hrho1⟩ := heps1 eps ((le_max_right eps0 eps1).trans heps)
  refine ⟨max rho0 rho1, lt_of_lt_of_le hrho0 (le_max_left rho0 rho1),
    fun rho hrho' W hcondition => ?_⟩
  exact twoGonHoldsInput_of_eulerWalk (hrho rho ((le_max_left rho0 rho1).trans hrho') W hcondition)
    (hrho1 rho ((le_max_right rho0 rho1).trans hrho') W hcondition)

/-- **Osin's Lemma 4.4 at least-area diagrams from leaf residuals**: the live waist
`relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV5` with each of its residuals produced by the
reductions on origin, leaving fifteen named leaves. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV6
    (hbudget : OsinLemma94ClassEndLoopsBudgetInput.{u, w, v})
    (hvalue : SameCellPocketCellFreeValueStatement.{u, w, v})
    (hcut : SameCellPocketLoopCutStatement.{u, w, v})
    (hloop : EnclosedSubdiagramLoopCutSuccStatement.{u, w, v})
    (hsub : ClosedWalkEnclosedSubdiagramSuccStatement.{u, w, v})
    (hencl : OsinLemma94CaseOneSpurEnclosureStatement.{u, w, v})
    (hspan : OsinLemma94ClassCaseGapSpanStatement.{u, w, v})
    (htwowalk : OsinTwoGonEulerWalkSectionStatement.{u, w, v})
    (htwogap : OsinTwoGonEulerGapSectionStatement.{u, w, v})
    (hcount : NoninterleavingVertexCountStatement.{v})
    (hni : CellPocketWalkNoninterleavingStatement.{u, w, v})
    (hcellStep : CellPocketOuterPinchStepSectionStatement.{u, w, v})
    (hproper : CellPocketWalkProperArcsSectionStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetTwoArcSectionStatement.{u, w, v})
    (hstep : PocketOuterPinchStepSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV5
    (osinLemma94ClassEndLoopsInput_of_budget hbudget)
    (osinLemma94SameCellPocketInput_of_loopCut hvalue hcut)
    (osinLemma94CaseOneRCell_of_noSpurPockets
      (osinLemma94CaseOneNoSpurXPocket_of_enclosedLoopCutSucc hloop)
      (osinLemma94CaseOneNoSpurYPocket_of_enclosedLoopCutSucc hloop)
      (osinLemma94CaseOneRCellSpur_of_enclosure hloop hsub hencl))
    hspan
    (osinTwoGonHoldsSection_of_eulerWalk htwowalk htwogap)
    (cellPocketWalkEuler_of_noninterleaving hcount hni)
    (cellPocketPinchSectionStatement_of_outerPinchStep hcellStep)
    hproper hfaces
    (pocketPinchLabelledSectionTwoArcStatement_of_outerPinchStep hstep)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OsinTwoGonEulerWalkSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.OsinTwoGonEulerGapSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.osinTwoGonHoldsSection_of_eulerWalk
#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV6
