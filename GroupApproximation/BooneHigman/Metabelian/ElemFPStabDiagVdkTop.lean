import GroupApproximation.BooneHigman.Metabelian.ElemFPStabDiagVdkWire
import GroupApproximation.BooneHigman.Metabelian.ElemFPBhNagaoWireUncondTop
import GroupApproximation.Meta.AxiomGuard

/-!
# Route A with the `k = 1` instance of StabRangeDiag discharged

Lane `bh-met-96`, part 3 of 3 (wiring).  `bhNagaoUncond_fpMetabelian_routeA` takes
`P1 = ∀ p prime, PolyK2NilGapStatementOver (ZMod p) 4`.  Here `P1` is split into its two
conjuncts, and the second is replaced by the `k ≥ 2` residual `stabDiagVdk_GeTwoStatement`
(its `k = 1` instance is Nagao, `stabDiagVdk_diag_one`).

LOUD: this removes no open statement from route A.  `stabDiagVdk_GeTwoStatement` is equivalent
to `PolyK2StabRangeDiagStatement` (`stabDiagVdk_geTwo_iff`); only the base instance is proved.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

/-- **Route A, with `P1` split**: `S1`, the OneVarNil conjunct, the `k ≥ 2` StabRangeDiag
residual, `Z1` and `H1` give `FinitelyPresentedMetabelianStatement`. -/
theorem stabDiagVdk_fpMetabelian_routeA
    (hS1 : Absorption.suslinZLocal_BadStatement)
    (hone : PolyK2OneVarNilStatement) (hge : stabDiagVdk_GeTwoStatement)
    (hZ1 : ElemFPCharZero.CharZeroK2SplitGapStatement)
    (hH1 : Envelope.HigmanVCStepBCoreStatement) : FinitelyPresentedMetabelianStatement :=
  bhNagaoUncond_fpMetabelian_routeA hS1 (stabDiagVdk_nilGapOver_of_geTwo hone hge) hZ1 hH1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagVdk_fpMetabelian_routeA

end GroupApproximation.BooneHigman.Metabelian.ElemFP
