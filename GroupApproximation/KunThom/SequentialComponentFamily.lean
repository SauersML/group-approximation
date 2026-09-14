import GroupApproximation.KunThom.SequentialComponentFamilyObjects
import GroupApproximation.KunThom.CentralizerNormalizationImprove

/-!
# The sequential component family of an expander decomposition

`componentFamily D hsymm hgen hT enum henum` is the
`CentralizerNormalizationImprove.ComponentFamily K T` of an expander decomposition
`D` of a sofic approximation of an infinite group `K`, on a finite symmetric
generating set `T`, for a surjective enumeration `enum : ℕ → K`.  Its objects
are the components that are good at the diagonal level, pruned and with
completed labels (`SequentialComponentFamilyObjects`).  Its Cheeger constant is
`cheeger D / (8 |T|)`.

The components that are not objects, together with the pruned points of the
objects, carry negligible mass (`uncoveredMass_negligible`).  The object sizes
and the uncovered mass add up to the model size
(`sum_card_objectModel_add_uncoveredMass`).
-/

namespace GroupApproximation
namespace SequentialComponentFamily

open scoped BigOperators

variable {K : Type} [Group K] {S : SoficApproximation K} {T : Finset K}
variable (D : ExpanderDecomposition S T)

/-- **The sequential component family.** -/
noncomputable def componentFamily [Infinite K] (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (hT : T.Nonempty) (enum : ℕ → K)
    (henum : Function.Surjective enum) :
    CentralizerNormalizationImprove.ComponentFamily K T where
  index := objectIndex D enum
  model := objectModel D hT enum
  act := objectAction D hT enum
  cheeger := D.cheeger / (8 * T.card)
  cheeger_pos := div_pos D.cheeger_pos
    (mul_pos (by norm_num) (by exact_mod_cast Finset.card_pos.mpr hT))
  expands := objectAction_expands D hT enum
  size_tendsTo := objectModel_size D hsymm hgen hT enum
  locallyMultiplicative := objectAction_locallyMultiplicative D hsymm hgen hT enum henum
  labelsInjective := objectAction_injOn D hsymm hgen hT enum

theorem componentFamily_model [Infinite K] (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (hT : T.Nonempty) (enum : ℕ → K)
    (henum : Function.Surjective enum) (n : ℕ) (i : objectIndex D enum n) :
    (componentFamily D hsymm hgen hT enum henum).model n i = objectModel D hT enum n i :=
  rfl

theorem componentFamily_act [Infinite K] (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (hT : T.Nonempty) (enum : ℕ → K)
    (henum : Function.Surjective enum) (n : ℕ) (i : objectIndex D enum n) :
    (componentFamily D hsymm hgen hT enum henum).act n i = objectAction D hT enum n i :=
  rfl

theorem componentFamily_cheeger [Infinite K] (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (hT : T.Nonempty) (enum : ℕ → K)
    (henum : Function.Surjective enum) :
    (componentFamily D hsymm hgen hT enum henum).cheeger = D.cheeger / (8 * T.card) :=
  rfl

/-! ### Uncovered mass -/

/-- Mass not covered by the objects: the components that are not good at the
diagonal level, and the pruned points of those that are. -/
noncomputable def uncoveredMass (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ) : ℝ :=
  badMass D enum n + prunedMass D hT enum n

theorem uncoveredMass_negligible [Infinite K] (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (hT : T.Nonempty) (enum : ℕ → K) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) (uncoveredMass D hT enum) :=
  (badMass_negligible D hsymm hgen enum).add (prunedMass_negligible D hT enum)

open Classical in
/-- The object sizes and the uncovered mass add up to the model size. -/
theorem sum_card_objectModel_add_uncoveredMass (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ) :
    (∑ C : D.componentIndex n,
      if hC : IsGoodAt D enum (level D enum n) n C then
        (Fintype.card (objectModel D hT enum n ⟨C, hC⟩) : ℝ) else 0) +
      uncoveredMass D hT enum n = Fintype.card (S.model n) := by
  have htotal : (∑ C : D.componentIndex n, (C.block.card : ℝ)) = Fintype.card (S.model n) := by
    exact_mod_cast BlockIndex.sum_card (D.blocks n)
  rw [← htotal]
  unfold uncoveredMass badMass prunedMass
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  by_cases hC : IsGoodAt D enum (level D enum n) n C
  · have h5 : 5 * (prunedSet D hT n C).card ≤ C.block.card :=
      five_mul_card_prunedSet_le D hT enum n ⟨C, hC⟩
    have hle : (prunedSet D hT n C).card ≤ C.block.card := by omega
    have hcard : Fintype.card (objectModel D hT enum n ⟨C, hC⟩) =
        C.block.card - (prunedSet D hT n C).card :=
      card_objectModel D hT enum n ⟨C, hC⟩
    rw [dif_pos hC, if_pos hC, if_pos hC, hcard, Nat.cast_sub hle]
    ring
  · rw [dif_neg hC, if_neg hC, if_neg hC]
    ring

end SequentialComponentFamily
end GroupApproximation
