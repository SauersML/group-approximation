import GroupApproximation.Monsters.CyclicBaseLEFObstruction
import GroupApproximation.Monsters.ExplicitIntegralLinearModel
import GroupApproximation.Sofic.LiteralMarkedCylinder
import GroupApproximation.Sofic.LiteralSixGenerator
import GroupApproximation.Sofic.LiteralWitnessConsequences
import GroupApproximation.Sofic.OperatorMFQuotientNonclosure
import GroupApproximation.Sofic.ScalingFamilyEndpoint

/-!
# Closed high-impact non-MF endpoints

Every declaration in this file is premise-free.  It collects the strongest
concrete consequences that have been discharged entirely inside Lean; no
property `(T)`, soficity, MF permanence, literature theorem, or construction
datum is accepted from a caller.
-/

namespace GroupApproximation
namespace NonMFImpact

open LiteralNonMFPresentation

/-- The literal group is finitely presented, six-generated, and non-MF. -/
theorem literal_sixGenerated_finitelyPresented_nonMF :
    Group.rank MarkedGroup ≤ 6 ∧
      Group.IsFinitelyPresented MarkedGroup ∧
      ¬ IsOperatorMF MarkedGroup :=
  LiteralSixGenerator.literal_sixGenerated_finitelyPresented_nonMF

/-- The literal forty-one-relator condition cuts out a nonempty clopen set
consisting entirely of non-MF marked groups. -/
theorem literal_nonempty_clopen_nonMF_cylinder :
    LiteralMarkedCylinder.literalCylinder.Nonempty ∧
      IsClopen LiteralMarkedCylinder.literalCylinder ∧
      LiteralMarkedCylinder.literalCylinder ⊆
        {N : MarkedGroupSpace 8 | ¬ IsOperatorMF N.Quotient} :=
  LiteralMarkedCylinder.literal_nonempty_clopen_nonMF_cylinder

/-- The concrete affine--Clifford witness is finitely generated and non-MF,
while its canonical lamp kernel is locally finite, LEF, sofic, and MF. -/
theorem witness_locallyFinite_MF_kernel_nonMF_total :
    IsLocallyFiniteGroup LiteralWitnessConsequences.WitnessLampGroup ∧
      IsLEF LiteralWitnessConsequences.WitnessLampGroup ∧
      IsSofic LiteralWitnessConsequences.WitnessLampGroup ∧
      IsOperatorMF LiteralWitnessConsequences.WitnessLampGroup ∧
      Group.FG LiteralNonMFLinearWitness.WitnessGroup ∧
      ¬ IsOperatorMF LiteralNonMFLinearWitness.WitnessGroup :=
  LiteralWitnessConsequences.literalWitness_locallyFiniteKernel_nonMF

/-- The concrete affine base is residually finite, sofic, and operator-MF;
all three facts are proved through its explicit integral matrix model. -/
theorem affineBase_residuallyFinite_sofic_MF :
    Group.ResiduallyFinite ExplicitLinearModel.gammaBar ∧
      IsSofic ExplicitLinearModel.gammaBar ∧
      IsOperatorMF ExplicitLinearModel.gammaBar :=
  ⟨ExplicitIntegralLinearModel.gammaBar_residuallyFinite,
    ExplicitIntegralLinearModel.gammaBar_isSofic,
    ExplicitIntegralLinearModel.gammaBar_isOperatorMF⟩

/-- The scaling construction is an unconditional infinite family: every
factor `m ≥ 2` produces a finitely presented non-MF group. -/
theorem scalingFamily_finitelyPresented_nonMF :
    ∀ m : ℕ, 2 ≤ m →
      Group.IsFinitelyPresented (ScalingFamilyEndpoint.MarkedGroup m) ∧
        ¬ IsOperatorMF (ScalingFamilyEndpoint.MarkedGroup m) := by
  intro m hm
  exact ⟨inferInstance,
    ScalingFamilyEndpoint.scalingFamily_not_isOperatorMF m hm⟩

/-- The cyclic-base sign survives but blocks every exact finite local model;
in particular its realized quotient is not residually finite. -/
theorem cyclicBase_exactModel_obstruction :
    LiteralCyclicCalibration.quotientMap LiteralCyclicCalibration.mark ≠ 1 ∧
      (∀ {H : Type} [Group H] [Finite H]
        (pi : LiteralCyclicCalibration.LiteralGroup →* H),
        pi LiteralCyclicCalibration.mark = 1) ∧
      ¬ IsLEF LiteralCyclicCalibration.LiteralGroup ∧
      ¬ IsLEF LiteralCyclicCalibration.RealizedQuotient ∧
      ¬ Group.ResiduallyFinite LiteralCyclicCalibration.RealizedQuotient :=
  CyclicBaseLEFObstruction.cyclicBase_exactModel_package

/-- A concrete operator-MF group has a non-operator-MF quotient. -/
theorem operatorMF_not_closed_under_quotients :=
  OperatorMFQuotientNonclosure.operatorMF_not_closed_under_this_quotient

end NonMFImpact
end GroupApproximation
