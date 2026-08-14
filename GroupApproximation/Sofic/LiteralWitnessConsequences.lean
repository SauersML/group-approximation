import GroupApproximation.Sofic.LiteralNonMFEndpoint
import GroupApproximation.Sofic.NormMFCoronaRadical

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

end
end LiteralWitnessConsequences
end GroupApproximation
