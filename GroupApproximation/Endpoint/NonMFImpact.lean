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

/-- The same concrete witness is hyperlinear but not operator-MF. -/
theorem witness_hyperlinear_nonMF :
    Group.FG LiteralNonMFLinearWitness.WitnessGroup ∧
      IsHyperlinear LiteralNonMFLinearWitness.WitnessGroup ∧
      ¬ IsOperatorMF LiteralNonMFLinearWitness.WitnessGroup :=
  ⟨LiteralNonMFLinearWitness.witnessGroup_finitelyGenerated,
    isHyperlinear_of_isSofic LiteralWitnessConsequences.witnessGroup_isSofic,
    LiteralWitnessConsequences.witnessGroup_not_isOperatorMF⟩

/-- One closed package for both concrete approximation separations. -/
theorem witness_sofic_hyperlinear_nonMF :
    Group.FG LiteralNonMFLinearWitness.WitnessGroup ∧
      IsSofic LiteralNonMFLinearWitness.WitnessGroup ∧
      IsHyperlinear LiteralNonMFLinearWitness.WitnessGroup ∧
      ¬ IsOperatorMF LiteralNonMFLinearWitness.WitnessGroup :=
  ⟨LiteralWitnessConsequences.literalWitness_sofic_nonMF.1,
    LiteralWitnessConsequences.literalWitness_sofic_nonMF.2.1,
    witness_hyperlinear_nonMF.2.1, witness_hyperlinear_nonMF.2.2⟩

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

/-- The finite-normal obstruction cannot directly produce a nontrivial
marked element in a torsion-free group. -/
theorem finiteNormal_obstruction_is_trivial_in_torsionFree_groups :
    FiniteNormalObstructionTrivialInTorsionFreeGroups :=
  finiteSubgroup_eq_bot_of_isMulTorsionFree

/-- The formal "free win": any sofic non-MF group is at once a hyperlinear
non-MF group.  `LiteralWitnessConsequences.literalWitness_sofic_nonMF`
supplies the concrete closed input. -/
theorem sofic_nonMF_is_hyperlinear_nonMF :
    SoficNonMFIsHyperlinearNonMF := by
  intro G _ hsofic hnonMF
  exact ⟨isHyperlinear_of_isSofic hsofic, hnonMF⟩

end NonMFImpact
end GroupApproximation
