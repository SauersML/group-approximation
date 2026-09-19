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
theorem isOperatorMF_of_residuallyFinite :
    ∀ {K : Type u} [Group K] [Countable K] [Group.ResiduallyFinite K],
      IsOperatorMF K := by
  intro K _ _ _
  exact (isWeakMF_of_residuallyFinite (H := K)).isOperatorMF

/-- Every finite group is operator-MF. -/
theorem isOperatorMF_of_finite_standard (K : Type) [Group K] [Finite K] :
    IsOperatorMF K :=
  (isWeakMF_of_finite K).isOperatorMF

/-- Operator-MF pulls back along an injective homomorphism by restricting a
faithful corona representation. -/
theorem IsOperatorMF.comap {H : Type v} [Group H] (hG : IsOperatorMF G)
    (ι : H →* G) (hι : Function.Injective ι) : IsOperatorMF H := by
  obtain ⟨X, hX, rho, hrho⟩ := hG
  exact ⟨X, hX, rho.comp ι, hrho.comp hι⟩

/-- Every subgroup of an operator-MF group is operator-MF (manuscript Lemma
`lem:subgroupMF`). -/
theorem IsOperatorMF.subgroup :
    ∀ {K : Type u} [Group K] (_hG : IsOperatorMF K) (H : Subgroup K),
      IsOperatorMF H := by
  intro K _ hG H
  exact hG.comap H.subtype (fun _ _ h ↦ Subtype.ext h)

/-- Contrapositive subgroup permanence: an ambient group containing a
non-operator-MF subgroup is not operator-MF. -/
theorem not_isOperatorMF_of_subgroup {H : Subgroup G}
    (hH : ¬ IsOperatorMF H) : ¬ IsOperatorMF G :=
  fun hG ↦ hH (hG.subgroup H)

end GroupApproximation
