import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauHopF2
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauDeepReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauD2Residual
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauLevelReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauEqLvlD2
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauClassifyMain
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauBridgeReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# The τ half of the Higman transfer, unconditionally (lane bh-met-93b)

This is pure wiring.  Lane bh-met-92n proved `higmanVCTauHop_deep`, and lane bh-met-77v proved
`higmanVCTauD2_all`.  Together they close the whole τ chain:
* the equal-level part: `higmanVCTauDeep_eq_of_deep higmanVCTauHop_deep`;
* the lower-level part: every lower-level tight instance is contradictory, because its
  hypothesis `hC` rules out the chain that `higmanVCTauD2_all` builds.  This is the same
  argument as `higmanVCTauTightEq_tight_of_eq_of_all`;
* `higmanVCTauLevel_tight_of_split` then gives the tight residual, and
  `higmanVCTauTight_tau_of_tight` gives `HigmanVCTauStatement` with no hypotheses.

The intermediate residuals of the chain are also recorded as proved: tight-eq, the d = 2
residual, the comm residual, the level residual and the uniform classification.

No new Statements are introduced.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Lower-level part, proved.**  Every instance is vacuous: the chain from
`higmanVCTauD2_all` contradicts the hypothesis `hC`. -/
theorem higmanVCTauDone_levelLt : HigmanVCTauLevelLtStatement := by
  intro d hd n _ p q x y x' y' hpq hqp hp hq hA _ _ hs _ _ _ _ hC hlt hmx hmy hxy hyx _ _
  exact (hC hlt (higmanVCTauD2_all d hd p q x y x' y' hpq hqp hp hq
    (higmanVCTauBridge_long hd hpq hqp hmx hmy (by omega) hs) hxy hyx hmx hmy
    (by omega))).elim

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_levelLt

/-- **Equal-level hop residual, proved** (from lane 92n's deep residual). -/
theorem higmanVCTauDone_levelResidual : HigmanVCTauLevelResidualStatement :=
  higmanVCTauDeep_level_of_deep higmanVCTauHop_deep

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_levelResidual

/-- **Equal-level part, proved.** -/
theorem higmanVCTauDone_levelEq : HigmanVCTauLevelEqStatement :=
  higmanVCTauDeep_eq_of_deep higmanVCTauHop_deep

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_levelEq

/-- **Tight residual, proved.** -/
theorem higmanVCTauDone_tight : HigmanVCTauTightStatement :=
  higmanVCTauLevel_tight_of_split higmanVCTauDone_levelEq higmanVCTauDone_levelLt

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_tight

/-- **Tight-eq residual, proved.** -/
theorem higmanVCTauDone_tightEq : HigmanVCTauTightEqStatement :=
  higmanVCTauTightEq_eq_of_tight higmanVCTauDone_tight

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_tightEq

/-- **The d = 2 equal-level residual, proved.** -/
theorem higmanVCTauDone_d2Residual : higmanVCTauEqLvl_D2Residual :=
  higmanVCTauEqLvl_d2_of_tightEq higmanVCTauDone_tightEq

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_d2Residual

/-- **Comm residual, proved.** -/
theorem higmanVCTauDone_commResidual : HigmanVCTauCommResidualStatement :=
  higmanVCTauTight_commResidual_of_tight higmanVCTauDone_tight

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_commResidual

/-- **Uniform classification, proved** (from lane 92n's two-letter classification). -/
theorem higmanVCTauDone_unifClassify : HigmanVCTauUnifClassifyStatement :=
  higmanVCTauClassify_of_two higmanVCTauHop_classifyTwo

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_unifClassify

/-- **The τ half of the Higman transfer, with no hypotheses.** -/
theorem higmanVCTauDone_tau : HigmanVCTauStatement :=
  higmanVCTauTight_tau_of_tight higmanVCTauDone_tight

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDone_tau

end GroupApproximation.BooneHigman.Metabelian.Envelope
