import GroupApproximation.Sofic.LiteralNonMFEndpoint
import GroupApproximation.Sofic.NormMFCoronaRadical
import GroupApproximation.Sofic.CliffordLampPermanence
import GroupApproximation.Sofic.LiteralBaseDoublingIndex
import GroupApproximation.Sofic.SoficMarkedCompression
import GroupApproximation.Sofic.CommutingLampCollapse
import GroupApproximation.Sofic.CliffordWitnessDirectDefect
import GroupApproximation.Monsters.ExplicitIntegralLinearModel
import GroupApproximation.Sofic.WitnessVerticalResiduallyFinite
import GroupApproximation.Meta.AxiomGuard

/-!
# Consequences for the explicit affine--Clifford witness

The general direct Clifford obstruction applies to the affine self-embedding.
The literal presentation supplies the independent MF-radical certificate used
by the sharper consequences below.
-/

namespace GroupApproximation
namespace LiteralWitnessConsequences

open CliffordLamp ExplicitLinearModel LiteralNonMFPresentation
  LiteralNonMFLinearWitness MarkedCompression
open ReducedGroupCStarTrace

noncomputable section

/-- The concrete lamp kernel in the affine--Clifford witness. -/
abbrev WitnessLampGroup : Type :=
  CliffordLamp (Cosets alpha conjD_injective)

/-- The concrete witness's lamp kernel is locally finite. -/
theorem witnessLamp_isLocallyFiniteGroup :
    IsLocallyFiniteGroup WitnessLampGroup :=
  CliffordLamp.isLocallyFiniteGroup_cliffordLamp _

/-- The concrete witness's lamp kernel is LEF. -/
theorem witnessLamp_isLEF : IsLEF WitnessLampGroup :=
  CliffordLamp.isLEF_cliffordLamp _

/-- The concrete witness's lamp kernel is sofic. -/
theorem witnessLamp_isSofic : IsSofic WitnessLampGroup :=
  CliffordLamp.isSofic_cliffordLamp _

/-- The concrete witness's lamp kernel is operator-MF. -/
theorem witnessLamp_isOperatorMF : IsOperatorMF WitnessLampGroup :=
  CliffordLamp.isOperatorMF_cliffordLamp _

/-- The full concrete affine--Clifford witness is sofic.  The base is
residually finite, the compressing range has finite index, and the generic
marked-compression permanence theorem supplies the remaining layers. -/
theorem witnessGroup_isSofic : IsSofic WitnessGroup :=
  SoficMarkedCompression.isSofic_ambient alpha conjD_injective
    ExplicitIntegralLinearModel.gammaBar_isSofic

/-- The lamp kernel is exactly the kernel of the canonical projection from
the witness semidirect product onto its vertical factor. -/
theorem witnessLamp_range_eq_projection_ker :
    (SemidirectProduct.inl : WitnessLampGroup →* WitnessGroup).range =
      (SemidirectProduct.rightHom : WitnessGroup →*
        Vertical alpha conjD_injective).ker :=
  SemidirectProduct.range_inl_eq_ker_rightHom

/-- The canonical projection from the witness onto its vertical factor is
surjective. -/
theorem witnessProjection_surjective :
    Function.Surjective
      (SemidirectProduct.rightHom : WitnessGroup →*
        Vertical alpha conjD_injective) :=
  SemidirectProduct.rightHom_surjective

/-- The surviving Clifford sign is MF-invisible in the witness group. -/
theorem witness_sign_normMFInvisible :
    NormMFInvisible (signAmbient alpha conjD_injective) := by
  rw [← witnessHom_mark]
  exact LiteralNonMFEndpoint.literal_mark_normMFInvisible.map witnessHom

/-- The actual affine--Clifford witness is non-MF by the general direct
obstruction for a proper self-embedding. -/
theorem witnessGroup_not_isOperatorMF_direct : ¬ IsOperatorMF WitnessGroup :=
  CliffordWitnessDirectDefect.not_isOperatorMF alpha conjD_injective
    v1G_not_mem_range CommutingLampCollapse.gammaBar_hasKazhdanPropertyT

/-- The explicit witness has nontrivial MF radical. -/
theorem witness_normMFResidual_ne_bot :
    normMFResidual WitnessGroup ≠ ⊥ := by
  intro hbot
  have hmem : signAmbient alpha conjD_injective ∈
      normMFResidual WitnessGroup :=
    witness_sign_normMFInvisible
  rw [hbot] at hmem
  exact signAmbient_ne_one alpha conjD_injective (Subgroup.mem_bot.mp hmem)

/-- The explicit affine--Clifford witness is not operator-MF. -/
theorem witnessGroup_not_isOperatorMF : ¬ IsOperatorMF WitnessGroup := by
  exact witnessGroup_not_isOperatorMF_direct

/-- The concrete witness's reduced group C-star algebra admits no faithful
embedding into a norm-matrix C-star corona. -/
theorem witness_reducedGroupCStar_not_hasMFEmbedding :
    ¬ HasMFEmbedding (ReducedGroupCStar WitnessGroup) :=
  not_hasMFEmbedding_reducedGroupCStar_of_not_isGroupTheoreticMF
    witnessGroup_not_isOperatorMF

/-- The concrete witness's reduced group C-star algebra is not MF. -/
theorem witness_reducedGroupCStar_not_isMFAlgebra :
    ¬ IsMFAlgebra (ReducedGroupCStar WitnessGroup) := by
  intro hMF
  exact witness_reducedGroupCStar_not_hasMFEmbedding hMF.2

/-- **Exact witness endpoint.**  The concrete quotient target is finitely
generated, its central Clifford sign is nontrivial and MF-invisible, and the
target is not operator-MF. -/
theorem literalWitness_finitelyGenerated_nonMF :
    Group.FG WitnessGroup ∧
      signAmbient alpha conjD_injective ≠ 1 ∧
      NormMFInvisible (signAmbient alpha conjD_injective) ∧
      ¬ IsOperatorMF WitnessGroup :=
  ⟨witnessGroup_finitelyGenerated,
    signAmbient_ne_one alpha conjD_injective,
    witness_sign_normMFInvisible,
    witnessGroup_not_isOperatorMF⟩

/-- **Closed kernel-and-quotient package for the explicit witness.**  With no
hypotheses, the kernel of its canonical vertical projection is locally finite,
LEF, sofic, and operator-MF, the quotient by that kernel is operator-MF as
well, and yet the whole witness is finitely generated and not operator-MF.
Operator MF is therefore not closed under extensions, even when the kernel is
locally finite and the quotient is residually finite. -/
theorem literalWitness_locallyFiniteKernel_nonMF :
    IsLocallyFiniteGroup WitnessLampGroup ∧
      IsLEF WitnessLampGroup ∧
      IsSofic WitnessLampGroup ∧
      IsOperatorMF WitnessLampGroup ∧
      IsOperatorMF (MarkedCompression.Vertical
        LiteralNonMFLinearWitness.alpha ExplicitLinearModel.conjD_injective) ∧
      Group.FG WitnessGroup ∧
      ¬ IsOperatorMF WitnessGroup :=
  ⟨witnessLamp_isLocallyFiniteGroup,
    witnessLamp_isLEF,
    witnessLamp_isSofic,
    witnessLamp_isOperatorMF,
    WitnessVertical.vertical_isOperatorMF,
    witnessGroup_finitelyGenerated,
    witnessGroup_not_isOperatorMF⟩

/-- **Closed sofic non-MF endpoint.**  The same concrete, finitely generated
witness is simultaneously sofic and non-operator-MF. -/
theorem literalWitness_sofic_nonMF :
    Group.FG WitnessGroup ∧ IsSofic WitnessGroup ∧
      ¬ IsOperatorMF WitnessGroup :=
  ⟨witnessGroup_finitelyGenerated, witnessGroup_isSofic,
    witnessGroup_not_isOperatorMF⟩

/-- **Closed reduced-C-star endpoint for the explicit witness.**  Its reduced
group C-star algebra is separable, carries its canonical faithful trace, is
stably finite in every nonempty finite matrix amplification, and is not MF. -/
theorem literalWitness_reducedGroupCStar_stablyFinite_nonMF :
    TopologicalSpace.SeparableSpace (ReducedGroupCStar WitnessGroup) ∧
      Nonempty (FaithfulTracialState (ReducedGroupCStar WitnessGroup)) ∧
      (∀ (I : Type) [Fintype I] [DecidableEq I], Nonempty I →
        ∀ v : CStarMatrix I I (ReducedGroupCStar WitnessGroup),
          star v * v = 1 → v * star v = 1) ∧
      ¬ IsMFAlgebra (ReducedGroupCStar WitnessGroup) := by
  refine ⟨reducedGroupCStar_separableSpace WitnessGroup,
    ⟨canonicalFaithfulTracialState WitnessGroup⟩, ?_,
    witness_reducedGroupCStar_not_isMFAlgebra⟩
  intro I _ _ hI v hv
  exact (canonicalFaithfulTracialState WitnessGroup).matrix_mul_star_eq_one_of_star_mul_eq_one
    I hI hv

end
end LiteralWitnessConsequences
end GroupApproximation

#audit_closed_axioms GroupApproximation.LiteralWitnessConsequences.witnessGroup_not_isOperatorMF_direct
