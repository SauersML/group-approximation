import GroupApproximation.Sofic.NormMFUniversalCorona
import GroupApproximation.Sofic.WeakMFTransfer

/-!
# Positive permanence results for operator-MF groups

This file records the standard cofinite-corona versions of two positive
facts used in the manuscript's consequences section: countable residually
finite groups are MF, and subgroups of MF groups are MF.
-/

namespace GroupApproximation

universe u v

variable {G : Type u} [Group G]

/-- For countable groups, a weak-MF approximation gives the standard
cofinite-corona MF property. -/
theorem IsWeakMF.isOperatorMF [Countable G] (hG : IsWeakMF G) :
    IsOperatorMF G :=
  isOperatorMF_of_normMFResidual_eq_bot
    (normMFResidual_eq_bot_of_isWeakMF hG)

/-- Every countable residually finite group is operator-MF in the literal
cofinite norm-matrix-corona sense (manuscript Lemma `lem:rfmf`). -/
theorem isOperatorMF_of_residuallyFinite [Countable G]
    [Group.ResiduallyFinite G] : IsOperatorMF G :=
  (isWeakMF_of_residuallyFinite (H := G)).isOperatorMF

/-- Operator-MF pulls back along an injective homomorphism by restricting a
faithful corona representation. -/
theorem IsOperatorMF.comap {H : Type v} [Group H] (hG : IsOperatorMF G)
    (ι : H →* G) (hι : Function.Injective ι) : IsOperatorMF H := by
  obtain ⟨X, hX, rho, hrho⟩ := hG
  exact ⟨X, hX, rho.comp ι, hrho.comp hι⟩

/-- Every subgroup of an operator-MF group is operator-MF (manuscript Lemma
`lem:subgroupMF`). -/
theorem IsOperatorMF.subgroup (hG : IsOperatorMF G) (H : Subgroup G) :
    IsOperatorMF H :=
  hG.comap H.subtype (fun _ _ h ↦ Subtype.ext h)

end GroupApproximation
