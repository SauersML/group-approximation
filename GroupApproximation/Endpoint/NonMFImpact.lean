import GroupApproximation.Monsters.CyclicBaseLEFObstruction
import GroupApproximation.Monsters.ExplicitIntegralLinearModel
import GroupApproximation.Sofic.LiteralMarkedCylinder
import GroupApproximation.Sofic.LiteralSixGenerator
import GroupApproximation.Sofic.LiteralWitnessConsequences
import GroupApproximation.Sofic.LiteralUniformObstruction
import GroupApproximation.Sofic.Hyperlinear
import GroupApproximation.Sofic.OperatorMFQuotientNonclosure
import GroupApproximation.Sofic.ScalingFamilyEndpoint
import GroupApproximation.Sofic.TorsionFreeFiniteNormalLimit

/-!
# Closed high-impact non-MF endpoints

Every declaration in this file is premise-free.  It collects the strongest
concrete consequences that have been discharged entirely inside Lean; no
property `(T)`, soficity, MF permanence, literature theorem, or construction
datum is accepted from a caller.
-/

namespace GroupApproximation
namespace NonMFImpact

open Matrix
open LiteralNonMFPresentation
open ReducedGroupCStarTrace
open scoped Matrix.Norms.L2Operator

/-!
The universally quantified conclusions below are routed through named closed
propositions.  Every theorem exported from this endpoint module therefore has
an empty declaration telescope: callers receive a proof of a closed sentence,
never a headline API that accepts hypotheses.
-/

/-- Closed proposition asserting the whole scaling family at once. -/
def ScalingFamilyFinitelyPresentedNonMF : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    Group.IsFinitelyPresented (ScalingFamilyPresentation.MarkedGroup m) ∧
      ¬ IsOperatorMF (ScalingFamilyPresentation.MarkedGroup m)

/-- Closed proposition recording the torsion-free limit of the finite-normal
obstruction. -/
def FiniteNormalObstructionTrivialInTorsionFreeGroups : Prop :=
  ∀ (G : Type) [Group G] [IsMulTorsionFree G]
    (F : Subgroup G) [Finite F], F = ⊥

/-- Closed universal separation statement: sofic non-MF groups are
hyperlinear non-MF. -/
def SoficNonMFIsHyperlinearNonMF : Prop :=
  ∀ (G : Type) [Group G], IsSofic G → ¬ IsOperatorMF G →
    IsHyperlinear G ∧ ¬ IsOperatorMF G

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

/-- The concrete witness also gives a separable, faithfully tracial, stably
finite reduced group C-star algebra that is not MF. -/
theorem witness_reducedGroupCStar_stablyFinite_nonMF :
    TopologicalSpace.SeparableSpace
        (ReducedGroupCStar LiteralNonMFLinearWitness.WitnessGroup) ∧
      Nonempty (FaithfulTracialState
        (ReducedGroupCStar LiteralNonMFLinearWitness.WitnessGroup)) ∧
      (∀ (I : Type) [Fintype I] [DecidableEq I], Nonempty I →
        ∀ v : CStarMatrix I I
          (ReducedGroupCStar LiteralNonMFLinearWitness.WitnessGroup),
          star v * v = 1 → v * star v = 1) ∧
      ¬ IsMFAlgebra
        (ReducedGroupCStar LiteralNonMFLinearWitness.WitnessGroup) :=
  LiteralWitnessConsequences.literalWitness_reducedGroupCStar_stablyFinite_nonMF

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
    ScalingFamilyFinitelyPresentedNonMF := by
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
theorem operatorMF_not_closed_under_quotients :
    IsOperatorMF (FreeGroup ChosenMarkedPresentation.Generator) ∧
      Function.Surjective
        (PresentedGroup.mk
          (ChosenMarkedPresentation.relators :
            Set (FreeGroup ChosenMarkedPresentation.Generator))) ∧
      ¬ IsOperatorMF ChosenMarkedPresentation.MarkedGroup :=
  OperatorMFQuotientNonclosure.operatorMF_not_closed_under_this_quotient

/-- A single positive defect threshold and finite test set force the literal
mark uniformly close to the identity in every matrix dimension. -/
theorem literal_uniform_operatorNorm_obstruction :
    ∃ (δ : ℝ) (F₀ : Finset MarkedGroup), 0 < δ ∧
      ∀ (Y : FiniteModel)
        (φ : MarkedGroup → Matrix.unitaryGroup Y ℂ),
        (∀ g ∈ F₀, ∀ h ∈ F₀,
          ‖(φ (g * h) : Matrix Y Y ℂ) -
            (φ g : Matrix Y Y ℂ) * φ h‖ ≤ δ) →
        ‖(φ mark : Matrix Y Y ℂ) - 1‖ < 1 :=
  LiteralUniformObstruction.literal_uniform_operatorNorm_obstruction

/-- The finite-normal obstruction cannot directly produce a nontrivial
marked element in a torsion-free group. -/
theorem finiteNormal_obstruction_is_trivial_in_torsionFree_groups :
    FiniteNormalObstructionTrivialInTorsionFreeGroups :=
  finiteSubgroup_eq_bot_of_isMulTorsionFree

/-- The formal "free win": any sofic non-MF group is at once a hyperlinear
non-MF group.  Applying this closed implication to the concrete witness only
awaits the closed Lean proof of that witness's soficity. -/
theorem sofic_nonMF_is_hyperlinear_nonMF :
    SoficNonMFIsHyperlinearNonMF := by
  intro G _ hsofic hnonMF
  exact ⟨isHyperlinear_of_isSofic hsofic, hnonMF⟩

end NonMFImpact
end GroupApproximation
