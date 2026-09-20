import GroupApproximation.BooneHigmanLinear.CharZero.RouteNoSuslin
import GroupApproximation.BooneHigmanLinear.CharZero.BTri.StepWire
import GroupApproximation.Meta.AxiomGuard

/-!
# T1–T3 with the Z1 base part replaced by the building inputs

`Z1 = CharZeroK2SplitGapStatement` is the base part (`K₂(N, ℤ[1/m])` finitely generated) together
with the nil part (`CharZeroK2NilFGPosStatement`). The base part follows from
`BTri.BuildingInputsStatement` (`BTri.baseFG_of_inputs`). So route A's owed inputs for T1–T3 become:
* `P1`;
* the building inputs (the triangle action and simple connectivity); the standard-vertex
  stabilizer is proved in `BTri.DomainStabilizer` and supplied by `BTri.buildingInputs_of`;
* the Z1 nil part;
* `H1`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace NoSuslin

open GroupApproximation.BooneHigman
open GroupApproximation.BooneHigman.Metabelian

/-- `Z1` from the building inputs and the nil part. -/
theorem splitGap_of_inputs (hI : BTri.BuildingInputsStatement)
    (hnil : ElemFPCharZero.CharZeroK2NilFGPosStatement) :
    ElemFPCharZero.CharZeroK2SplitGapStatement :=
  ⟨BTri.baseFG_of_inputs hI, hnil⟩

#audit_axioms splitGap_of_inputs

/-- **T3** from `P1`, the building inputs, the `Z1` nil part and `H1`. -/
theorem finitelyGeneratedLinearStatement_of_inputs
    (hP1 : ∀ p : ℕ, p.Prime → ElemFP.PolyK2NilGapStatementOver (ZMod p) 4)
    (hI : BTri.BuildingInputsStatement) (hnil : ElemFPCharZero.CharZeroK2NilFGPosStatement)
    (hH1 : Envelope.HigmanVCStepBCoreStatement) : FinitelyGeneratedLinearStatement :=
  finitelyGeneratedLinearStatement_noSuslin hP1 (splitGap_of_inputs hI hnil) hH1

#audit_axioms finitelyGeneratedLinearStatement_of_inputs

/-- **T2** from `P1`, the building inputs, the `Z1` nil part and `H1`. -/
theorem finitelyGeneratedMetabelianStatement_of_inputs
    (hP1 : ∀ p : ℕ, p.Prime → ElemFP.PolyK2NilGapStatementOver (ZMod p) 4)
    (hI : BTri.BuildingInputsStatement) (hnil : ElemFPCharZero.CharZeroK2NilFGPosStatement)
    (hH1 : Envelope.HigmanVCStepBCoreStatement) : FinitelyGeneratedMetabelianStatement :=
  finitelyGeneratedMetabelianStatement_noSuslin hP1 (splitGap_of_inputs hI hnil) hH1

#audit_axioms finitelyGeneratedMetabelianStatement_of_inputs

/-- **T1** from `P1`, the building inputs, the `Z1` nil part and `H1`. -/
theorem finitelyPresentedMetabelianStatement_of_inputs
    (hP1 : ∀ p : ℕ, p.Prime → ElemFP.PolyK2NilGapStatementOver (ZMod p) 4)
    (hI : BTri.BuildingInputsStatement) (hnil : ElemFPCharZero.CharZeroK2NilFGPosStatement)
    (hH1 : Envelope.HigmanVCStepBCoreStatement) : FinitelyPresentedMetabelianStatement :=
  finitelyPresentedMetabelianStatement_noSuslin hP1 (splitGap_of_inputs hI hnil) hH1

#audit_axioms finitelyPresentedMetabelianStatement_of_inputs

end NoSuslin
end BooneHigmanLinear
end GroupApproximation
