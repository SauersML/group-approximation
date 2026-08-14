import GroupApproximation.Sofic.LiteralNonMFEndpoint
import GroupApproximation.Sofic.NormMFCoronaRadical
import GroupApproximation.Sofic.CliffordLampPermanence

/-!
# Operator-MF consequences for the explicit Clifford witness

The literal presentation maps surjectively onto its affine--Clifford witness.
The marked central sign survives there, while functoriality carries the
literal MF-radical certificate to that sign.  Thus the witness itself is a
finitely generated non-MF group, independently of its separate soficity
analysis.
-/

namespace GroupApproximation
namespace LiteralWitnessConsequences

open LiteralNonMFPresentation LiteralNonMFLinearWitness MarkedCompression

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
  intro hMF
  exact witness_normMFResidual_ne_bot
    (normMFResidual_eq_bot_of_isOperatorMF hMF)

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

/-- **Closed kernel package for the explicit witness.**  With no hypotheses,
the kernel of its canonical vertical projection is locally finite, LEF,
sofic, and operator-MF, whereas the whole witness is finitely generated and
not operator-MF. -/
theorem literalWitness_locallyFiniteKernel_nonMF :
    IsLocallyFiniteGroup WitnessLampGroup ∧
      IsLEF WitnessLampGroup ∧
      IsSofic WitnessLampGroup ∧
      IsOperatorMF WitnessLampGroup ∧
      Group.FG WitnessGroup ∧
      ¬ IsOperatorMF WitnessGroup :=
  ⟨witnessLamp_isLocallyFiniteGroup,
    witnessLamp_isLEF,
    witnessLamp_isSofic,
    witnessLamp_isOperatorMF,
    witnessGroup_finitelyGenerated,
    witnessGroup_not_isOperatorMF⟩

end
end LiteralWitnessConsequences
end GroupApproximation
